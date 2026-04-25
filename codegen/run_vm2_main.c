/*
 * Driver for the wasm-vm2 ATC pipeline.
 *
 *   fread -> wasm_buf[65536]
 *         -> parse_module(&m)
 *         -> [v2 default] extract_cfg(&w, &m); invoke_v2(&st, &m, a, b, &w)
 *         -> [v1 ref]     invoke(&st, &m, a, b)
 *         -> unsigned int result
 *
 * Usage: run_vm2 [--vm v1|v2] FILE.wasm EXPORT_NAME ARG1 ARG2
 *   --vm v2 (default): block-structured path with precomputed CFG.
 *   --vm v1          : flat dispatcher (kept only for reference).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#include "wasm-vm2.h"

static int load_wasm(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "run_vm2: cannot open %s: %s\n", path, strerror(errno));
        return -1;
    }
    size_t n = fread(wasm_buf, 1, sizeof(wasm_buf), f);
    int err = ferror(f);
    fclose(f);
    if (err) {
        fprintf(stderr, "run_vm2: read error on %s\n", path);
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
    int use_v2 = 1;
    int argi = 1;
    if (argi < argc && strcmp(argv[argi], "--vm") == 0) {
        if (argi + 1 >= argc) {
            fprintf(stderr, "run_vm2: --vm requires v1 or v2\n");
            return 2;
        }
        if (strcmp(argv[argi + 1], "v1") == 0) use_v2 = 0;
        else if (strcmp(argv[argi + 1], "v2") == 0) use_v2 = 1;
        else {
            fprintf(stderr, "run_vm2: unknown --vm value '%s' (want v1 or v2)\n",
                    argv[argi + 1]);
            return 2;
        }
        argi += 2;
    }

    if (argc - argi != 4) {
        fprintf(stderr,
                "usage: %s [--vm v1|v2] FILE.wasm EXPORT_NAME ARG1 ARG2\n",
                argv[0]);
        return 2;
    }

    const char *wasm_path = argv[argi];
    const char *export_query = argv[argi + 1];
    unsigned int a = (unsigned int) strtoul(argv[argi + 2], NULL, 0);
    unsigned int b = (unsigned int) strtoul(argv[argi + 3], NULL, 0);

    if (load_wasm(wasm_path) < 0) return 1;

    struct wmod m = { 0 };
    parse_module(&m);
    if (m.err) {
        fprintf(stderr, "run_vm2: parse error (err=%d)\n", m.err);
        return 1;
    }
    if (!export_name_matches(&m, export_query)) {
        fprintf(stderr, "run_vm2: export %s not found\n", export_query);
        return 1;
    }

    struct wst st = { 0 };
    unsigned int r;
    if (use_v2) {
        struct wcfg w = { 0 };
        extract_cfg(&w, &m);
        r = invoke_v2(&st, &m, a, b, &w);
    } else {
        r = invoke(&st, &m, a, b);
    }
    printf("%u\n", r);
    return 0;
}
