/*
 * dump_cfg: load a .wasm and print the wcfg produced by extract_cfg
 * (the Phase 1.x bracket matcher emitted from codegen/wasm-vm2.lisp).
 *
 * Usage:  dump_cfg FILE.wasm
 *
 * Output (one line each):
 *   parse: err=<n> body_off=<o> body_len=<l>
 *   cfg:   err=<n> nbr=<n> pend_top=<n>
 *   br <i>: opener_pc=<pc> opcode=0x<xx> end_pc=<pc> else_pc=<pc>
 *   pend <j>: <bracket-index>
 *
 * Companion to run_demo (which exercises the vm1 execution path).
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#include "wasm-vm2.h"

static int load_wasm(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "dump_cfg: cannot open %s: %s\n", path, strerror(errno));
        return -1;
    }
    size_t n = fread(wasm_buf, 1, sizeof(wasm_buf), f);
    int err = ferror(f);
    fclose(f);
    if (err) {
        fprintf(stderr, "dump_cfg: read error on %s\n", path);
        return -1;
    }
    if (n < sizeof(wasm_buf)) {
        memset(wasm_buf + n, 0, sizeof(wasm_buf) - n);
    }
    return (int) n;
}

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: %s FILE.wasm\n", argv[0]);
        return 2;
    }
    if (load_wasm(argv[1]) < 0) return 1;

    struct wmod m = { 0 };
    parse_module(&m);
    printf("parse: err=%u body_off=%d body_len=%d\n",
           (unsigned) m.err, m.body_off, m.body_len);
    if (m.err) return 1;

    struct wcfg w = { 0 };
    extract_cfg(&w, &m);
    printf("cfg:   err=%u nbr=%d pend_top=%d\n",
           (unsigned) w.err, w.nbr, w.pend_top);

    for (int i = 0; i < w.nbr && i < 64; i++) {
        printf("  br %2d: opener_pc=%5d opcode=0x%02x end_pc=%5d else_pc=%5d\n",
               i, w.opener_pc[i], (unsigned) w.opener[i],
               w.end_pc[i], w.else_pc[i]);
    }
    for (int j = 0; j < w.pend_top && j < 16; j++) {
        printf("  pend %2d: br %d\n", j, w.pend[j]);
    }
    return 0;
}
