# atc/codegen — spec-driven ATC step-function generator

A small code generator that takes the operational WASM semantics in
[../execution.lisp](../execution.lisp) as-is and, for each
operation it understands, emits two artifacts:

1. A standalone per-op **step function** in C.
2. An opcode-dispatched **execution loop** in C that inlines all
   arms around a shared set of scalar registers.

Both come from one source of truth: a *template family* indexed by
structural shape. There is one emitter per shape, and the per-op
work is one line regardless of which artifact is being produced.

No new DSL. No edits to `execution.lisp`.

## Status

Today: **eighteen opcodes** generated end-to-end through a shared template
family of thirteen shapes, wired to the hand-written `.wasm` parser, driven
by real `wat2wasm`-compiled WebAssembly. Straight-line, branching, *and*
if/else-with-scan programs (gcd, factorial, is_prime, collatz) all run
through the same dispatch loop.

**Running examples** (see [End-to-end](#end-to-end-running-a-real-wasm-through-the-generated-loop) below):

```
$ wat2wasm addmod.wat -o addmod.wasm
$ ./run_demo addmod.wasm addmod 30 10         → 40    (= (30+10) %% 50)
$ ./run_demo addmod.wasm addmod 49 49         → 48    (= 98 %% 50)

$ ./run_demo ../tests/oracle/gcd.wasm        gcd       48 18        → 6
$ ./run_demo ../tests/oracle/gcd.wasm        gcd       1000000 999983 → 1
$ ./run_demo ../tests/oracle/factorial.wasm  factorial 5  0          → 120
$ ./run_demo ../tests/oracle/factorial.wasm  factorial 10 0          → 3628800
$ ./run_demo ../tests/oracle/is_prime.wasm   is_prime  7  0          → 1
$ ./run_demo ../tests/oracle/is_prime.wasm   is_prime  9  0          → 0
$ ./run_demo ../tests/oracle/collatz.wasm    collatz   27 0          → 111
$ ./run_demo ../tests/oracle/collatz.wasm    collatz   97 0          → 118
```

All results match the published oracle / hand-written reference.

### Template shapes and opcodes covered

| Spec / opcode                         | Shape                         | Notes                                            |
|---------------------------------------|-------------------------------|--------------------------------------------------|
| `wasm::execute-local.get` `0x20`      | `:local-idx-pusher`           | `|exec_local_get|`                               |
| `wasm::execute-local.set` `0x21`      | `:local-idx-popper`           | `|exec_local_set|`                               |
| `wasm::execute-local.tee` `0x22`      | `:local-idx-teer`             | `|exec_local_tee|`                               |
| `wasm::execute-drop` `0x1a`           | `:drop`                       |                                                  |
| `wasm::execute-i32.const` `0x41`      | `:i32-const`                  | one-byte immediate (not full LEB128)             |
| `wasm::execute-i32.add` `0x6a`        | `:i32-binop-total` + uint-op  | shared with sub/mul/and/or/xor                   |
| `wasm::execute-i32.rem_u` `0x70`      | `:i32-binop-nz` + uint-op     | shared with div_u; traps-to-halt on zero         |
| `wasm::execute-i32.eqz` `0x45`        | `:i32-unop-eqz`               | peek-and-replace                                 |
| `wasm::execute-block` `0x02`          | `:block`                      | pushes label w/ target = `scan_end(pc+2)`        |
| `wasm::execute-loop` `0x03`           | `:loop-begin`                 | pushes label w/ target = loop start              |
| `wasm::execute-end` `0x0b`            | `:end` or `:end-toplevel`     | `:end` pops a label (non-toplevel); toplevel halts |
| `wasm::execute-br` `0x0c`             | `:br`                         | unconditional branch by depth                    |
| `wasm::execute-br_if` `0x0d`          | `:br-if`                      | conditional branch (shares emitter w/ `:br`)     |
| `wasm::execute-if` `0x04`             | `:if`                         | calls `scan_end` + `scan_else`; pushes label iff cond-true or else-present |
| `wasm::execute-else` `0x05`           | `:else`                       | pops the label pushed by `:if` and jumps to `scan_end(pc+1)` |
| `wasm::execute-return` `0x0f`         | `:return`                     | halts the loop                                   |
| `wasm::execute-i32.{eq,ne,lt_u,gt_u,le_u,ge_u}` `0x46..0x4f` | `:i32-relop` + uint-relop | parameterized over `c::lt-uint-uint` etc.; pushes `uint-from-sint` |
| `wasm::execute-i32.div_u` `0x6d`      | `:i32-binop-nz` + uint-op     | second `0x6d` client of the div/rem shape        |
| `wasm::execute-i32.{sub,mul}` `0x6b,0x6c` | `:i32-binop-total` + uint-op | additional clients of the binop-total shape      |

The `:i32-binop-total` shape is parameterized by the ATC uint operator and
covers `add`/`sub`/`mul`/`and`/`or`/`xor` at one line each. `:i32-binop-nz`
hoists the divisor-nonzero trap into the ACL2 guard and covers `div_u`/
`rem_u` similarly. `:i32-relop` is parameterized by the signed-sint
relop and wraps the sint result in `uint-from-sint` to push WASM's 0/1 `i32`.
`:br` and `:br-if` share one emitter (`emit-arm-br`) parameterized by an
`is-conditional` flag — the only difference is three extra bindings for
the stack-top check, spliced in conditionally so the translated C for `:br`
has no dead code (ATC's ignore-formal rule). `:if` is the most complex
arm: it calls both `scan_end(pc+2)` and `scan_else(pc+2)`; if
`scan_else` reports no else (sentinel `0`), `end_pc` is used for the
 false-arm target and no label is pushed; otherwise a label is pushed
 with its target at `scan_end` so the matching `:else` can pop it and
 jump to the end.

### `:end` vs `:end-toplevel`

`:end-toplevel` (used by [loop-demo.lisp](loop-demo.lisp) / [demo.lisp](demo.lisp))
treats every `0x0b` as the function end and halts. That is fine for
straight-line programs whose label stack is always empty.

`:end` (used by [integration-demo.lisp](integration-demo.lisp)) is the
real semantics: if the label stack is non-empty, pop a label and fall
through; otherwise halt. Programs that use `block` / `loop` / `br` must
use `:end`, because every one of those constructs closes with a `0x0b`
that does *not* mean "function return".

### Guard-hint conditioning

The loop generator detects whether the opcode table includes any of
`:block` / `:loop-begin` / `:br` / `:br-if` / `:if` / `:else`
(via `entries-have-control-flow-p`) and only then splices the
`STRUCT-wst-lpc/lsp/lkind-INDEX-OKP`, `scan_end`, and `scan_else` rules
into the generated guard hints. That way the control-flow-free
`loop-demo.lisp` still certifies against a `|wst|` defstruct that has no
`lpc`/`lsp`/`lkind` slots, while `integration-demo.lisp` picks up the
richer struct from `wasm-vm1.lisp` and gets the extra enables it needs.

### Execution loop

The same shape-tag vocabulary drives a dispatcher generator
([loop.lisp](loop.lisp), [loop-demo.lisp](loop-demo.lisp)) that
emits an opcode-dispatched step-until-halt loop as a single C
function. Each arm is inlined (ATC passes structs by value, so
calling the per-op step functions from the loop would not mutate
the caller's state) but every arm body is emitted from the same
per-shape template that drives the standalone generator — one
source of truth per shape.

The 8-op straight-line demo (end, drop, local.get/set/tee, i32.const,
i32.add, i32.rem_u) is driven by this table:

```lisp
(gen-exec-loop
  |exec_loop|
  (:end-toplevel    #x0b)
  (:drop            #x1a)
  (:local-idx-pusher #x20)
  (:local-idx-popper #x21)
  (:local-idx-teer   #x22)
  (:i32-const        #x41)
  (:i32-binop-total  #x6a c::add-uint-uint)   ; i32.add
  (:i32-binop-nz     #x70 c::rem-uint-uint))  ; i32.rem_u
```

The full 18-op control-flow table, used by
[integration-demo.lisp](integration-demo.lisp) for gcd / factorial /
is_prime / collatz, adds:

```lisp
  (:end              #x0b)                         ; pops a label if any, else halts
  (:i32-unop-eqz     #x45)
  (:i32-binop-total  #x6b c::sub-uint-uint)        ; i32.sub
  (:i32-binop-total  #x6c c::mul-uint-uint)        ; i32.mul
  (:i32-binop-nz     #x6d c::div-uint-uint)        ; i32.div_u
  (:i32-relop        #x46 c::eq-sint-sint)         ; i32.eq   (any sint relop works)
  (:i32-relop        #x47 c::ne-sint-sint)         ; i32.ne
  (:i32-relop        #x49 c::lt-uint-uint)         ; i32.lt_u
  (:i32-relop        #x4b c::gt-uint-uint)         ; i32.gt_u
  (:i32-relop        #x4d c::le-uint-uint)         ; i32.le_u
  (:i32-relop        #x4f c::ge-uint-uint)         ; i32.ge_u
  (:block            #x02)
  (:loop-begin       #x03)
  (:br               #x0c)
  (:br-if            #x0d)
  (:if               #x04)                         ; if BT (with optional else)
  (:else             #x05)                         ; else
  (:return           #x0f)                         ; return (halts loop)
```

and produces [loop-demo.c](loop-demo.c) (8-op) or [run.c](run.c) (18-op)
each containing a single dispatch C function. Compare to the ~1100
hand-written lines covering this same set in
[`wasm-vm1.lisp`](wasm-vm1.lisp) `|exec$loop|`.

Shape of the generated dispatcher (excerpt):

```c
void exec_run(struct wst *st, int pc) {
    int sp = 0;
    int nl = 0;
    int halted = 0;
    int fuel = 100000;
    while (halted == 0 && fuel > 0 && pc < 59998) {
        int b = (int) wasm_buf[pc];
        if (b == 11) {                // end: halt
            halted = 1;
            fuel = fuel - 1;
        } else { if (b == 26) {       // drop
            int ok = sp > 0;
            sp = ok ? sp - 1 : sp;
            pc = pc + 1;
            halted = ok ? halted : 1;
            fuel = fuel - 1;
        } else { ... } }
    }
}
```

ATC emits only `if`/`else` — it does not generate `switch`
statements. The resulting else-cascade is deeply nested in source
form; `clang-format` or a trivial post-pass can flatten `else { if
… }` into `else if …` for readability.

The generated C, as emitted by ATC into [demo.c](demo.c):

```c
int exec_local_get(struct wst st, int sp, int x) {
    unsigned int val = st.loc[x];
    st.op[sp] = val;
    sp = sp + 1;
    return sp;
}

int exec_local_set(struct wst st, int sp, int x) {
    int idx = sp - 1;
    unsigned int val = st.op[idx];
    st.loc[x] = val;
    sp = idx;
    return sp;
}

int exec_local_tee(struct wst st, int sp, int x) {
    int idx = sp - 1;
    unsigned int val = st.op[idx];
    st.loc[x] = val;
    return sp;
}

int exec_drop(struct wst st, int sp) {
    return sp - 1;
}

int exec_i32_const(struct wst st, int sp, unsigned int n) {
    st.op[sp] = n;
    sp = sp + 1;
    return sp;
}

int exec_i32_add(struct wst st, int sp) {
    int i1 = sp - 2;
    int i2 = sp - 1;
    unsigned int v1 = st.op[i1];
    unsigned int v2 = st.op[i2];
    unsigned int r = v1 + v2;
    st.op[i1] = r;
    sp = i2;
    return sp;
}

int exec_i32_rem_u(struct wst st, int sp) {
    int i1 = sp - 2;
    int i2 = sp - 1;
    unsigned int v1 = st.op[i1];
    unsigned int v2 = st.op[i2];
    unsigned int r = v1 % v2;
    st.op[i1] = r;
    sp = i2;
    return sp;
}
```

Compare to the hand-written opcode arms inside
[`wasm-vm1.lisp`](wasm-vm1.lisp) `|exec$loop|`, which are
~40 ACL2 lines each of `ok` / `x_safe` / `sp_safe` / `halted`
gating, fuel decrement, pc arithmetic, and the recursive tail. The
generated versions are the "shape-pure" form: trap conditions live
in the ACL2 guard, not in the body.

Build: `make -j$(nproc) demo` (from this directory — uses
`/home/acl2/books/build/cert.pl`).

## End-to-end: running a real `.wasm` through the generated loop

[integration-demo.lisp](integration-demo.lisp) wires the generated
`|exec_loop_gen|` to the hand-written `.wasm` reader in
[wasm-vm1.lisp](wasm-vm1.lisp). The pipeline is:

```
    main.c → fread → wasm_buf[65536]
                │
                ▼
          parse_module         (hand-written, emitted by ATC from wasm-vm1.lisp)
                │  fills |wmod|: body_off, body_len, num_locals,
                │                export_off, export_len, ...
                ▼
          run_wasm_gen         (GENERATED; defined in integration-demo.lisp)
                │  seeds st->loc[0..1] with the two u32 arguments,
                │  then drives exec_loop_gen (8-opcode dispatch),
                │  then returns st->op[0].
                ▼
             uint result
```

`c::atc` emits these three C functions plus the loop body (inlined into
`run_wasm_gen` as a `while`) into [run.c](run.c) / [run.h](run.h).
[run_main.c](run_main.c) is the CLI driver (same arg convention as
`../atc/main.c`):

```
$ cd atc/codegen
$ gcc -O2 -o run_demo run.c run_main.c
$ wat2wasm addmod.wat -o addmod.wasm
$ ./run_demo addmod.wasm addmod 30 10    # (30+10) %% 50 = 40
40
$ ./run_demo addmod.wasm addmod 100 50   # (100+50) %% 50 = 0
0
$ ./run_demo addmod.wasm addmod 49 49    # (98) %% 50 = 48
48

$ ./run_demo ../tests/oracle/gcd.wasm gcd 48 18
6
$ ./run_demo ../tests/oracle/gcd.wasm gcd 1000000 999983
1
```

[addmod.wat](addmod.wat) is a straight-line example using only the 8
straight-line opcodes. The `gcd.wasm` / `factorial.wasm` / `is_prime.wasm` /
`collatz.wasm` fixtures exercise the full 18-op vocabulary — `block` /
`loop` / `br` / `br_if` / `if` / `else` / `return` / `i32.eqz` / the
full unsigned relop family / sub / mul / div_u — through the same
generated dispatch loop. `wat2wasm` is available at
`tools/node_modules/.bin/wat2wasm`.

Two additional drivers exist for regression / isolation work:

- [run_sanity.c](run_sanity.c) — bypasses `parse_module` and injects a
  hand-crafted bytecode body directly into `wasm_buf`. Useful for
  exercising the generated loop without going through the parser
  (`./run_sanity add 3 4 → 7`, `./run_sanity rem_u 17 0 → 0` demonstrating
  the trap-to-halt path, etc.).
- The hand-written `../atc/wasm-vm1` binary takes the same CLI and implements
  a different opcode subset (block / br_if / eqz for gcd), so the two
  can be diffed on fixtures that fall inside both vocabularies.

Known caveat exercised by the demo: the generated `:i32-const` arm reads
a **one-byte** immediate, not LEB128. For constants that fit in a signed
single LEB byte (<= 63) the encoding coincides; larger constants need
either (a) a multi-byte LEB reader template (straightforward follow-up)
or (b) modelling the immediate as two separate spec ops. Same simplification
applies to `:local-idx-*` which currently read the index as a single
byte (fine for the 16-local state we've fixed).

## Files

| File                                     | Role                                                                                     |
|------------------------------------------|------------------------------------------------------------------------------------------|
| [state-model.lisp](state-model.lisp)     | The one concrete state struct `|wst|` (op[64], loc[16]). Shared by every generated op.   |
| [standalone-state.lisp](standalone-state.lisp) | Non-local re-export of the `sint-max` linear rule + standalone `|wasm_buf|` defobject. Used by demos that don't include `wasm-vm1`. |
| [templates.lisp](templates.lisp)         | Per-shape emitters for standalone C step functions (`gen-local-idx-pusher`, …).          |
| [demo.lisp](demo.lisp)                   | Uses step-function emitters for 7 ops, then `c::atc` → [demo.c](demo.c).                 |
| [loop.lisp](loop.lisp)                   | Per-shape emitters for **arms** spliced into a generated opcode-dispatch loop.           |
| [loop-demo.lisp](loop-demo.lisp)         | Uses loop emitters for 8 opcodes plus `|exec_run|` entry, then `c::atc` → [loop-demo.c](loop-demo.c). |
| [integration-demo.lisp](integration-demo.lisp) | Wires generated loop to hand-written parser from `wasm-vm1.lisp`; emits [run.c](run.c) / [run.h](run.h). |
| [run_main.c](run_main.c)                 | CLI driver: fread → parse_module → run_wasm_gen → print.                                 |
| [run_sanity.c](run_sanity.c)             | Hand-crafted bytecode injector; exercises the generated loop without `parse_module`.      |
| [addmod.wat](addmod.wat)                 | Smallest end-to-end WAT using only the 8 supported opcodes.                              |
| [cert.acl2](cert.acl2)                   | Portcullis: ACL2 package + ATC ttags.                                                    |

## Gotchas (lessons from building this)

These are ATC/ACL2 rules that cost time to rediscover. All are
addressed in the current code; they're listed here so the next
person — or the next shape — doesn't re-trip them.

1. **ATC C identifier rule.** Generated function names must be
   portable ASCII C identifiers — no dots, no dashes. Use
   underscores: `|exec_local_get|`, not `|exec-local.get|` or
   `|exec.local.get|`.

2. **`mv-return` rule for scalars.** If a function returns `(mv st
   sp)` and the second value is a `sintp` scalar, ATC rejects it:
   non-first `mv` values must be pointer/array formals. The
   standalone step functions return just the new `sp` and "mutate"
   the struct by shadowing the `let*`-bound variable.

3. **Recursive targets need a non-recursive caller.** ATC will
   refuse a `c::atc` form whose only recursive target function is
   not called from another target. [loop-demo.lisp](loop-demo.lisp)
   introduces a trivial non-recursive `|exec_run|` that
   initializes scalar registers and calls `|exec_loop|`; ATC
   translates `|exec_loop|` into a `while` inlined inside
   `exec_run`.

4. **Scalar mutation in a recursive loop requires mv-return.** The
   loop's scalar formals (`sp`, `pc`, `halted`, `fuel`) are only
   treated as assignable OUT parameters by ATC when the function
   returns `(mv st sp nl pc halted fuel)`. Returning just `st` and
   writing `(|halted| (c::assign …))` produces "attempt to modify a
   non-assignable variable." The arms still look like in-place
   assignments in ACL2 source; ATC handles the mv packaging.

5. **Local rules don't survive `include-book`.** A linear rule
   `(>= (c::sint-max) 65600)` declared with `defrulel` in
   [state-model.lisp](state-model.lisp) is not visible inside a
   book that `include-book`s it. Use `defrule` (non-local) in any
   book whose guard proofs depend on the concrete `sint-max`
   bound. [loop.lisp](loop.lisp) re-declares it non-locally.

6. **`declare ignore` on program-mode helpers.** `xargs :mode
   :program` still enforces the "every formal must be used or
   declared ignored" rule at defun time. In [loop.lisp](loop.lisp),
   `emit-pc-halted-fuel` takes `loop-name` only for interface
   symmetry with other arm emitters and needs `(declare (ignore
   loop-name))`.

7. **No `switch`-statement generation.** ATC emits only nested
   `if`/`else` (its underlying C AST supports `switch`, but the
   ACL2-to-C translator does not). The dispatcher C is a deeply
   nested else-cascade; `clang-format` or a trivial post-pass can
   flatten `else { if … }` into `else if …` if you need it for
   reading.

8. **Caller guard proofs need a struct-preservation lemma for the
   loop.** When `|run_wasm_gen|` (or any caller) uses `mv-let` to
   destructure the loop's return and then writes through the
   returned `|st|`, ATC's guard generator has to know that
   `(mv-nth 0 (|exec_loop_gen| ...))` is still a `struct-|wst|-p`.
   The inductive proof doesn't come for free from the loop's defun.
   [integration-demo.lisp](integration-demo.lisp) adds:

   ```lisp
   (defrulel struct-wst-p-of-mv-nth-0-exec_loop_gen
     (implies (struct-|wst|-p |st|)
              (struct-|wst|-p
               (mv-nth 0 (|exec_loop_gen| |st| |sp| |nl| |pc| |halted|
                                          |fuel| |wasm_buf|))))
     :induct (|exec_loop_gen| |st| |sp| |nl| |pc| |halted| |fuel|
                              |wasm_buf|)
     :enable (|exec_loop_gen|))
   ```

   This mirrors `struct-wst-p-of-mv-nth-0-exec$loop` in
   [wasm-vm1.lisp](wasm-vm1.lisp). Without it, guard
   verification for the caller fails with checkpoints like
   `(STRUCT-wst-P (MV-NTH 0 (|exec_loop_gen| ...)))`. A future
   enhancement is for `gen-exec-loop` to emit this lemma
   automatically alongside the defun.

9. **`:i32-const` and `:local-idx-*` read one-byte immediates, not
   LEB128.** The current arms do `byte-at(pc+1)` and advance `pc`
   by a fixed 2. For constants/indices that fit in a signed single
   LEB byte (≤ 63 for `i32.const`, ≤ 15 for `local.*`) the encoding
   coincides with raw bytes, and `wat2wasm` produces the expected
   bytecode. For larger constants, a multi-byte LEB reader template
   is a straightforward follow-up. The 16-local bound is already
   enforced by `|wst|` (`loc[16]`), so the 1-byte index is not a
   footgun there.

10. **`c::atc` target lists must cover the full call graph.** If
    `|run_wasm_gen|` calls both `|exec_loop_gen|` and (indirectly,
    via the caller) `parse_module`, all three — plus every
    recursively-tail-called helper like `|parse$loop|` — must be
    listed as targets in the `c::atc` form. ATC accepts a target
    function that is already declared elsewhere as long as its
    body matches; listing it twice (here and in the upstream
    wasm-vm1 `c::atc`) is fine.

11. **`sint-from-boolean` must wrap an AND or OR, not a single
    call.** ATC only recognises `(sint-from-boolean e)` if `e` is a
    (transformed) call of `AND` or `OR` over `boolean-from-sint`
    terms; a single `(boolean-from-sint (c::eq-… x y))` is rejected
    as "not a (transformed) call of AND or OR." Workaround used in
    both `:i32-unop-eqz` and `:br-if`: write `(or x x)` over the
    same boolean to satisfy the shape check.

12. **ATC ignore-formal rule applies inside generated `let*`.** If
    an emitter sometimes needs auxiliary bindings
    (`|peek_idx|` / `|peek_v|` / `|cond_true|` for `:br-if` but not
    `:br`), those bindings must be introduced **conditionally** in
    the backquote template — otherwise the unused-variable check
    fires during ATC translation for the variant that doesn't use
    them. Pattern used in [loop.lisp](loop.lisp) `emit-arm-br`:

    ```lisp
    ,@(and is-conditional
           '((|peek_idx| …) (|peek_v| …) (|cond_true| …)))
    ```

13. **Reused shapes with host-provided support must gate their
    guard-hints.** When the same generator (`emit-exec-loop`) is
    reused by both a standalone demo (no `|lpc|` / `|lsp|` slots)
    and an integration demo (with them), the guard-hints must
    conditionally reference the control-flow struct rules.
    [loop.lisp](loop.lisp) uses `entries-have-control-flow-p` to
    splice `STRUCT-wst-lpc/lsp/lkind-INDEX-OKP` and `|scan_end|`
    only when the opcode table actually includes `:block` / `:br`
    / `:br-if`.

14. **Non-local return-type lemmas are needed for host helpers.**
    `wasm-vm1.lisp` declares `sintp-of-mv-nth-0-scan$loop` with
    `defrulel` (local to that book). The `:block` arm in the
    generated loop calls `|scan_end|`, which unfolds into
    `mv-nth 0` of `|scan$loop|`, and that needs to be an `sintp`
    for guard verification.
    [integration-demo.lisp](integration-demo.lisp) re-declares the
    rule non-locally (as `sintp-of-mv-nth-0-scan$loop-for-codegen`)
    alongside the `sint-max->=-65600-for-codegen` rule. Same
    pattern applies whenever a generated arm calls an externally-
    defined helper.

15. **Watch for `pc`/`sp` variable confusion in arm templates.**
    The `:br` arm's new stack pointer is `|tsp_raw|` (the target
    SP read from the label), not `|tpc_raw|` (the target PC). Easy
    to mistype in backquote-heavy template code; the guard failure
    presents as a stack-bound checkpoint `(… <= 64)` that seems
    unrelated to the typo.

16. **ATC's loop shape requires a single non-recursive exit
    `(mv a b c …)` whose args are exactly the loop formals.** When
    we first wrote `|scan_else$loop|` with two early exits (returning
    `(mv (pc+1) 1 fuel)` on "else found" and `(mv 0 0 fuel)` on
    "end-at-1 reached"), ATC rejected it: "The 'else' branch … does
    not have the required form." Fix: make the loop body *always*
    recurse, and encode termination by **setting a loop formal to a
    sentinel** — here `depth := 0` on either exit condition — so the
    guard `(depth > 0)` then terminates the loop on the next call.
    The wrapper function then inspects the final `depth` (and `pc`) to
    decide what to return. This same pattern applies to any host
    helper with multiple semantic exit conditions.

17. **Host helpers with multi-bit return types need a `defrulel`
    per returned mv-nth index you guard against.** `|scan_else|`'s
    wrapper reads *both* `mv-nth 0` (pc) and `mv-nth 1` (depth)
    from the loop and needs each to be provably `sintp` in the guard
    proof. Missing the `mv-nth 1` lemma presents as a key checkpoint
    `(C::SINTP (MV-NTH 1 (|scan_else$loop| …)))` in the wrapper's guard
    conjecture — easy to miss under a "should already be obvious"
    first-reaction, since the analogous `|scan_end|` only reads
    `mv-nth 0`. Add one `defrulel sintp-of-mv-nth-N-<loop>` per index
    used.

18. **`scan$loop`'s `is_wide` list must include every wide opcode
    the input bytecode can contain, not just the control-flow ones.**
    The hand-written `scan$loop` originally marked only
    `0x0c` / `0x0d` / `0x20..0x22` as 2-byte, under the assumption
    that non-control-flow opcodes wouldn't appear inside a `:block`
    body. That's wrong for realistic input: an `i32.const N` at
    `body_pc` would cause `scan$loop` to re-interpret `N` as the next
    opcode, producing a garbage end PC. `is_prime` happened to work
    because its immediates (0, 1, 2) were all structurally harmless;
    `collatz`'s `0x03` (`i32.const 3`) was not. Add every 2-byte
    opcode you support to the `is_wide` cascade in both `scan$loop`
    *and* `scan_else$loop`.

## Adding a new shape

For a new operation whose spec doesn't fit an existing shape, add one
template macro to [templates.lisp](templates.lisp) (for the
standalone step function) and one arm emitter to
[loop.lisp](loop.lisp) (for the dispatched loop), then one dispatch
entry in each of `gen-exec-op` / `emit-arm`. Existing templates to
copy from:

- **Stack-only shapes** (no immediate): `:drop`, `:i32-binop-total`,
  `:i32-binop-nz`.
- **Immediate shapes**: `:i32-const` (u32), `:local-idx-pusher` /
  `:local-idx-popper` / `:local-idx-teer` (local index),
  `:end-toplevel`.
- **Parameterized shapes**: `:i32-binop-total` takes the ATC op
  symbol (`c::add-uint-uint`, `c::mul-uint-uint`, …);
  `:i32-binop-nz` additionally takes the op's `-okp` predicate.

Most of `execution.lisp` fits into shapes of this kind. Completed so far
(see Status above) include `:i32-relop`, `:if`, `:else`, `:return`,
and the `:block` / `:loop-begin` / `:br` / `:br-if` label-stack family.
Still-open additions:

- `:i32-unop` — `clz`/`ctz`/`popcnt` (one pop, one push; `eqz` already
  has its own `:i32-unop-eqz`).
- `:i32-shift` — like binop-total but the rhs is masked `% 32`.
- `:i32-binop-signed` / `:i32-binop-signed-nz` — for `div_s`/`rem_s`;
  also `:i32-relop-signed` for `lt_s`/`gt_s`/`le_s`/`ge_s`.
- `:global-get-set` — straightforward pusher/popper over a separate
  `glob[]` array added to `|wst|`.
- `:i64-*` — same shapes re-instantiated for 64-bit.
- Memory ops (`i32.load` / `i32.store` / `memory.grow`) — would need a
  linear-memory slot in `|wst|` and byte-level access helpers.

## How the generator maps spec → ATC

The correspondence between the AST-level state of the spec and the
concrete `(st, sp)` representation is fixed, once, in
[state-model.lisp](state-model.lisp):

```
(current-operand-stack state)  <->  op[0..sp-1]  (sp = stack height)
(current-locals state)         <->  loc[0..]
```

with the spec's wrapped values (`(make-i32-val v)`) carrying the
concrete `uint` `v` that lives in the op/loc array slot.

Each template knows one structural shape in the spec. For example,
the `:local-idx-pusher` template is a refinement of this spec shape
(from [../execution.lisp](../execution.lisp#L1000-L1013)):

```lisp
(b* ((x (first args))
     (locals (current-locals state))
     (ostack (current-operand-stack state))
     ((when (not (< x (len locals)))) :trap)
     (val (nth-local x locals))
     (ostack (push-operand val ostack))
     (state (update-current-operand-stack ostack state)))
  (advance-instrs state))
```

and it emits exactly:

```lisp
(let* ((val (c::declar (struct-|wst|-read-|loc|-element x st)))
       (st  (struct-|wst|-write-|op|-element sp val st))
       (sp  (c::assign (c::add-sint-sint sp (c::sint-dec-const 1)))))
  sp)
```

with a guard `(and (sintp sp x) (0 <= sp < 63) (0 <= x < 16))` that
encodes the spec's `(when (not (< x (len locals)))) :trap` plus the
bounded-stack bound needed for `add-sint-sint-okp`.

The per-op generator call is then just:

```lisp
(gen-exec-op :local-idx-pusher |exec_local_get|)
```

The spec source for `execute-local.get` is not read, parsed, or
otherwise touched. The pairing of spec function ↔ shape is stated at
the call site; the correctness of that pairing is a one-time reading
of the spec, not a per-invocation operation. Automating the pairing
(by introspecting the unnormalized body of `execute-<op>` and
matching it against each shape's canonical template) is a natural
later step but is not necessary for the code-generation job.

## What this proves about the original concern

The original `|exec$loop|` in [wasm-vm1.lisp](wasm-vm1.lisp)
was hand-authored bottom-up from the C we wanted, not top-down from
the spec. Every opcode arm there carries the plumbing of being *inside*
a dispatch loop: `ok`/`x_safe`/`halted` gating, fuel decrement, PC
arithmetic, the `(|exec$loop| st sp' ...)` recursive tail. That
plumbing is completely absent from the spec, so the shape drift
between spec and implementation was ~40 lines per op.

A spec-driven generator factors out the plumbing (it lives in the
template, once) and makes each op's C a small, one-purpose function
that visibly mirrors the corresponding `execute-<op>` in the spec.
The loop generator shows the same factoring scales the other way:
one table row per opcode, one arm emitter per shape, and the whole
~650-line hand-written dispatcher collapses to a ~110-line C
function with the same operational content.

## Struct calling conventions (informational)

The standalone step functions in [demo.c](demo.c) take `struct wst
st` *by value*; the loop entry `exec_run` in [loop-demo.c](loop-demo.c)
takes `struct wst *st`. That difference is purely ATC calling
convention: top-level target functions with struct parameters are
by-value if they're not called by another target, and by-pointer if
they are. The ACL2 source is the same (`let*`-shadowed `st`);
composition order chooses the C ABI.
