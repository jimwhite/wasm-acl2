/*
 * wasm-vm1 driver.
 *
 * Usage: wasm-vm1 FILE.wasm EXPORT_NAME ARG1 ARG2
 *
 * Reads FILE.wasm into the global buffer `wasm_buf`, asks the ATC-generated
 * parser to populate the module struct, verifies that EXPORT_NAME matches the
 * single exported function's name (bytes at m->export_off), and invokes it.
 *
 * The invoked function is interpreted by the ATC-generated `invoke()`.
 * All algorithmic work lives in wasm-vm1.c; this file is pure plumbing.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#include "wasm-vm1.h"

static int load_wasm(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "wasm-vm1: cannot open %s: %s\n", path, strerror(errno));
        return -1;
    }
    size_t n = fread(wasm_buf, 1, sizeof(wasm_buf), f);
    int err = ferror(f);
    fclose(f);
    if (err) {
        fprintf(stderr, "wasm-vm1: read error on %s\n", path);
        return -1;
    }
    /* zero the tail so out-of-bounds reads are deterministic */
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
    parse_header(&m);
    if (m.err) {
        fprintf(stderr, "wasm-vm1: not a WebAssembly binary (bad magic)\n");
        return 1;
    }

    /*
     * When the real parser lands, export_name_matches() below will find the
     * exported function and confirm it matches argv[2].  Until then, the
     * module struct is mostly zero and we can't do the match, so we skip it
     * during stub bring-up.  Uncomment once parse_module is wired in.
     */
    if (m.export_len != 0) {
        if (!export_name_matches(&m, export_query)) {
            fprintf(stderr, "wasm-vm1: export %s not found\n", export_query);
            return 1;
        }
    }

    unsigned int a = (unsigned int) strtoul(argv[3], NULL, 0);
    unsigned int b = (unsigned int) strtoul(argv[4], NULL, 0);
    unsigned int r = invoke(&m, a, b);
    printf("%u\n", r);
    return 0;
}
