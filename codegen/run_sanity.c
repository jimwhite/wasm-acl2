/*
 * Sanity driver: bypass parse_module, inject a hand-crafted bytecode body
 * that uses only the 8 opcodes the generated loop supports, and run it.
 *
 * Body: local.get 0 ; local.get 1 ; i32.add ; end
 *       0x20 0x00    0x20 0x01     0x6a     0x0b
 *
 * Expected output: a + b.
 *
 * Usage: run_sanity OP A B
 *   OP is one of: add, rem_u, drop_then_a, const42
 *
 * This isolates the generated execution loop from module parsing so we can
 * exercise it end-to-end even before control-flow ops are generated.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "run.h"

static int lay_add(void) {
    int pc = 100;
    wasm_buf[pc++] = 0x20; wasm_buf[pc++] = 0x00;   /* local.get 0 */
    wasm_buf[pc++] = 0x20; wasm_buf[pc++] = 0x01;   /* local.get 1 */
    wasm_buf[pc++] = 0x6a;                          /* i32.add     */
    wasm_buf[pc++] = 0x0b;                          /* end         */
    return 100;
}

static int lay_rem_u(void) {
    int pc = 100;
    wasm_buf[pc++] = 0x20; wasm_buf[pc++] = 0x00;   /* local.get 0 */
    wasm_buf[pc++] = 0x20; wasm_buf[pc++] = 0x01;   /* local.get 1 */
    wasm_buf[pc++] = 0x70;                          /* i32.rem_u   */
    wasm_buf[pc++] = 0x0b;                          /* end         */
    return 100;
}

static int lay_drop_then_a(void) {
    /* push a, push b, drop (so top is a), end. */
    int pc = 100;
    wasm_buf[pc++] = 0x20; wasm_buf[pc++] = 0x00;   /* local.get 0 */
    wasm_buf[pc++] = 0x20; wasm_buf[pc++] = 0x01;   /* local.get 1 */
    wasm_buf[pc++] = 0x1a;                          /* drop        */
    wasm_buf[pc++] = 0x0b;                          /* end         */
    return 100;
}

static int lay_const42(void) {
    int pc = 100;
    wasm_buf[pc++] = 0x41; wasm_buf[pc++] = 42;     /* i32.const 42 (u8 imm) */
    wasm_buf[pc++] = 0x0b;                          /* end         */
    return 100;
}

int main(int argc, char **argv) {
    if (argc != 4) {
        fprintf(stderr, "usage: %s {add|rem_u|drop_then_a|const42} A B\n", argv[0]);
        return 2;
    }
    memset(wasm_buf, 0, sizeof(wasm_buf));
    int body_off;
    if (!strcmp(argv[1], "add"))              body_off = lay_add();
    else if (!strcmp(argv[1], "rem_u"))       body_off = lay_rem_u();
    else if (!strcmp(argv[1], "drop_then_a")) body_off = lay_drop_then_a();
    else if (!strcmp(argv[1], "const42"))     body_off = lay_const42();
    else { fprintf(stderr, "unknown op: %s\n", argv[1]); return 2; }

    unsigned int a = (unsigned int) strtoul(argv[2], NULL, 0);
    unsigned int b = (unsigned int) strtoul(argv[3], NULL, 0);

    struct wmod m = { 0 };
    m.body_off = body_off;
    m.num_locals = 2;

    struct wst st = { 0 };
    unsigned int r = run_wasm_gen(&st, &m, a, b);
    printf("%u\n", r);
    return 0;
}
