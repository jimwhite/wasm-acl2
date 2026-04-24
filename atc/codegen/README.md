# atc/codegen — spec-driven ATC step-function generator

A small code generator that takes the operational WASM semantics in
[../../execution.lisp](../../execution.lisp) as-is and, for each
operation it understands, emits a standalone ATC-fragment step
function plus its C translation.

No new DSL. No edits to `execution.lisp`. The generator is a
*template family*: for each structural shape occurring in the spec
there is one emitter macro, and the per-op work is one line.

## Status

Today: two operations generated end-to-end.

| Spec                    | Shape                | Generated ACL2           | Generated C         |
|-------------------------|----------------------|--------------------------|---------------------|
| `wasm::execute-local.get` | `:local-idx-pusher` | `|exec_local_get|`       | `exec_local_get`    |
| `wasm::execute-local.set` | `:local-idx-popper` | `|exec_local_set|`       | `exec_local_set`    |

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
```

Compare to the hand-written `local.get` arm inside
[`../wasm-vm1.lisp`](../wasm-vm1.lisp) `|exec$loop|`, which is ~40
ACL2 lines of `ok` / `x_safe` / `sp_safe` / `halted` gating. The
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
entry to `gen-exec-op`. Sketch for drop (pop-one, no operand, no
local):

```lisp
(defmacro gen-drop-shape (name)
  `(defun ,name (|st| |sp|)
     (declare (xargs :guard (and (struct-|wst|-p |st|)
                                 (c::sintp |sp|)
                                 (< 0 (c::integer-from-sint |sp|))
                                 (<= (c::integer-from-sint |sp|) 64))
                     :guard-hints
                     (("Goal" :in-theory (enable c::sub-sint-sint
                                                 c::sub-sint-sint-okp
                                                 c::sint-integerp-alt-def
                                                 c::integer-from-cinteger-alt-def
                                                 c::declar)))))
     (declare (ignore |st|))
     (c::sub-sint-sint |sp| (c::sint-dec-const 1))))
```

Binops over i32 are a single shape (`:i32-binop`) parameterized by
the ATC op symbol; `local.tee` is a trivial variant of the popper
that doesn't decrement `sp`; `i32.const` is the pure pusher with the
immediate as the second argument. Half of `execution.lisp` fits into
maybe six shapes; control-flow (`block`/`loop`/`br`/`end`) does not
fit the "one step per op" abstraction and belongs to the dispatcher,
not this generator.

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
