# atc/codegen — spec-driven ATC step-function generator

A small code generator that takes the operational WASM semantics in
[../../execution.lisp](../../execution.lisp) as-is and, for each
operation it understands, emits a standalone ATC-fragment step
function plus its C translation.

No new DSL. No edits to `execution.lisp`. The generator is a
*template family*: for each structural shape occurring in the spec
there is one emitter macro, and the per-op work is one line.

## Status

Today: seven operations generated end-to-end, six template shapes.

| Spec                      | Shape                         | Generated ACL2        | Generated C         |
|---------------------------|-------------------------------|-----------------------|---------------------|
| `wasm::execute-local.get` | `:local-idx-pusher`           | `|exec_local_get|`    | `exec_local_get`    |
| `wasm::execute-local.set` | `:local-idx-popper`           | `|exec_local_set|`    | `exec_local_set`    |
| `wasm::execute-local.tee` | `:local-idx-teer`             | `|exec_local_tee|`    | `exec_local_tee`    |
| `wasm::execute-drop`      | `:drop`                       | `|exec_drop|`         | `exec_drop`         |
| `wasm::execute-i32.const` | `:i32-const`                  | `|exec_i32_const|`    | `exec_i32_const`    |
| `wasm::execute-i32.add`   | `:i32-binop-total` + uint-op  | `|exec_i32_add|`      | `exec_i32_add`      |
| `wasm::execute-i32.rem_u` | `:i32-binop-nz` + uint-op     | `|exec_i32_rem_u|`    | `exec_i32_rem_u`    |

The `:i32-binop-total` shape is parameterized by the ATC uint
operator and so covers `add`/`sub`/`mul`/`and`/`or`/`xor` with a
single additional line each. The `:i32-binop-nz` shape hoists the
divisor-nonzero trap into the ACL2 guard (via the op's `-okp`
predicate) and covers `div_u`/`rem_u` in one line each.

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
[`../wasm-vm1.lisp`](../wasm-vm1.lisp) `|exec$loop|`, which are
~40 ACL2 lines each of `ok` / `x_safe` / `sp_safe` / `halted`
gating, fuel decrement, pc arithmetic, and the recursive tail. The
generated versions are the "shape-pure" form: trap conditions live
in the ACL2 guard, not in the body.

Build: `make -j$(nproc) demo` (from this directory — uses
`/home/acl2/books/build/cert.pl`).

## Files

| File                   | Role                                                        |
|------------------------|-------------------------------------------------------------|
| [state-model.lisp](state-model.lisp) | The one concrete state struct `|wst|` (op[64], loc[16]). Shared by every generated op. |
| [templates.lisp](templates.lisp)     | The template-family emitters. One `gen-<shape>` macro per structural shape in the spec. |
| [demo.lisp](demo.lisp)               | Uses the generator for `local.get` and `local.set`, then invokes `c::atc` on the result. |
| [cert.acl2](cert.acl2)               | Portcullis: ACL2 package + ATC ttags.                        |

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
(from [../../execution.lisp](../../execution.lisp#L1000-L1013)):

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

## Adding a new shape

For a new operation whose spec doesn't fit an existing shape, add one
template macro to [templates.lisp](templates.lisp) and one dispatch
entry to `gen-exec-op`. Existing templates to copy from:

- **Stack-only shapes** (no immediate): `:drop`, `:i32-binop-total`,
  `:i32-binop-nz`.
- **Immediate shapes**: `:i32-const` (u32), `:local-idx-pusher` /
  `:local-idx-popper` / `:local-idx-teer` (local index).
- **Parameterized shapes**: `:i32-binop-total` takes the ATC op
  symbol (`c::add-uint-uint`, `c::mul-uint-uint`, …);
  `:i32-binop-nz` additionally takes the op's `-okp` predicate.

Most of `execution.lisp` fits into shapes of this kind. Future
additions likely needed:

- `:i32-unop` — `clz`/`ctz`/`popcnt`/`eqz` (one pop, one push).
- `:i32-relop` — `eq`/`ne`/`lt_u`/`lt_s`/… (two pops, push 0/1).
- `:i32-shift` — like binop-total but the rhs is masked `% 32`.
- `:i32-binop-signed` / `:i32-binop-signed-nz` — for `div_s`/`rem_s`.
- `:global-get-set` — straightforward pusher/popper over a separate
  `glob[]` array added to `|wst|`.
- `:i64-*` — same shapes re-instantiated for 64-bit.

Control-flow (`block`/`loop`/`br`/`br_if`/`end`/`call`) does not fit
the "one step per op, no dispatch" abstraction and belongs to the
dispatcher layer, not this generator.

## What this proves about the original concern

The original `|exec$loop|` in [../wasm-vm1.lisp](../wasm-vm1.lisp)
was hand-authored bottom-up from the C we wanted, not top-down from
the spec. Every opcode arm there carries the plumbing of being *inside*
a dispatch loop: `ok`/`x_safe`/`halted` gating, fuel decrement, PC
arithmetic, the `(|exec$loop| st sp' ...)` recursive tail. That
plumbing is completely absent from the spec, so the shape drift
between spec and implementation was ~40 lines per op.

A spec-driven generator factors out the plumbing (it lives in the
dispatcher, once) and makes each op's C a small, one-purpose
function that visibly mirrors the corresponding `execute-<op>` in
the spec. The demo here shows that at the ATC-fragment level *and*
at the emitted-C level the two can be put in one-to-one
correspondence mechanically.

## Known limitation

The emitted C takes `struct wst st` by value (top-level functions
with struct parameters get by-value calling convention from ATC when
they are not called from other generated code). Mutations to `st`
inside the generated function therefore don't propagate to a caller.
When these step functions are composed into a dispatcher — either a
hand-written C dispatcher or another ATC-generated one — the caller
holds `st` as a local variable and passes its address; ATC then
emits `struct wst *st` for the callee automatically. The ACL2-level
semantics (shadowed `st` binding in `let*`) is already correct; only
the C calling-convention shape changes when composition is wired up.
