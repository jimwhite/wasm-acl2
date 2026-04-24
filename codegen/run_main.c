/*
 * Driver for the spec-generated pipeline:
 *
 *   fread -> wasm_buf[65536]
 *         -> parse_module(&m)               (ATC-emitted from wasm-vm1.lisp)
 *         -> run_wasm_gen(&st, &m, a, b)    (ATC-emitted from integration-demo.lisp)
 *         -> unsigned int result
 *
 * Usage: run_demo FILE.wasm EXPORT_NAME ARG1 ARG2
 *
 * Companion to ../atc/main.c (which calls the hand-written invoke()).  Same CLI,
 * same fixtures, so the two can be diffed against each other.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#include "run.h"

static int load_wasm(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "run_demo: cannot open %s: %s\n", path, strerror(errno));
        return -1;
    }
    size_t n = fread(wasm_buf, 1, sizeof(wasm_buf), f);
    int err = ferror(f);
    fclose(f);
    if (err) {
        fprintf(stderr, "run_demo: read error on %s\n", path);
        return -1;
    }
    if (n < sizeof(wasm_buf)) {
        memset(wasm_buf + n, 0, sizeof(wasm_buf) - n);
    }
    return (int) n;
}

static int export_name_matches(const struct wmod *m, const char *query) {
    size_t qlen = strlen(query);
    if ((unsigned) qlen != (unsigned) m->export_len) return 0;
    return memcmp(wasm_buf + m->export_off, query, qlen) == 0;
}

int main(int argc, char **argv) {
    if (argc != 5) {
        fprintf(stderr, "usage: %s FILE.wasm EXPORT_NAME ARG1 ARG2\n", argv[0]);
        return 2;
    }
    const char *wasm_path = argv[1];
    const char *export_query = argv[2];

    if (load_wasm(wasm_path) < 0) return 1;

    struct wmod m = { 0 };
    parse_module(&m);
    if (m.err) {
        fprintf(stderr, "run_demo: parse error (err=%d)\n", m.err);
        return 1;
    }

    if (!export_name_matches(&m, export_query)) {
        fprintf(stderr, "run_demo: export %s not found\n", export_query);
        return 1;
    }

    unsigned int a = (unsigned int) strtoul(argv[3], NULL, 0);
    unsigned int b = (unsigned int) strtoul(argv[4], NULL, 0);
    struct wst st = { 0 };
    unsigned int r = run_wasm_gen(&st, &m, a, b);
    printf("%u\n", r);
    return 0;
}
