# ATC Reference (condensed from ACL2 docs)

Source material:
- `/home/acl2/books/kestrel/c/atc/doc.lisp`
- `/home/acl2/books/kestrel/c/atc/defstruct-doc.lisp`
- `/home/acl2/books/kestrel/c/atc/defobject-doc.lisp`
- `/home/acl2/books/kestrel/c/atc/tutorial.lisp`
- Tests under `/home/acl2/books/kestrel/c/atc/tests/`
- Worked examples under `/home/acl2/books/kestrel/c/examples/`

See also the companion empirical guide: [NOTES.md](NOTES.md).

---

## Target subset

- **C17.** Control constructs: `if/else`, `while` (derived from tail
  recursion), sequential composition via `let`, ternary `?:`, and
  short-circuit `&&` / `||`.
- **Not supported:** `for`, `do-while`, `break`, `continue`, `goto`,
  `switch`, mutual recursion, non-tail recursion, function pointers,
  floating-point, `union`, bit-fields.
- **Return shapes:** one integer, `void` (possibly with side effects
  through `mv` returns and pointer-param mutations), or struct by value.

## Integer types

`schar`, `uchar`, `sshort`, `ushort`, `sint`, `uint`, `slong`, `ulong`,
`sllong`, `ullong`.

- Binary ops: `c::<op>-<t1>-<t2>` where `<op>` ∈
  {`add`, `sub`, `mul`, `div`, `rem`, `shl`, `shr`,
  `bitand`, `bitxor`, `bitior`, `lt`, `gt`, `le`, `ge`, `eq`, `ne`}.
- Unary ops: `c::plus-<t>`, `c::minus-<t>`, `c::bitnot-<t>`, `c::lognot-<t>`.
- `-okp` companions: `c::add-sint-sint-okp`, `c::shl-uint-sint-okp`, …
  Include the `-okp` predicate as a guard conjunct whenever overflow,
  division-by-zero, or out-of-range shift is possible.
- Constants: `c::<t>-dec-const`, `-hex-const`, `-oct-const`, but only
  for `sint/uint/slong/ulong/sllong/ullong`. Sub-int constants are
  built via conversions, e.g. `(c::uchar-from-sint (c::sint-dec-const 0))`.
- Conversions: `c::<t1>-from-<t2>` for every applicable pair.
- Booleans ↔ `int`: `c::sint-from-boolean`, `c::boolean-from-sint`
  (mirror C's int-as-bool convention).

## `let` / `declar` / `assign`

- `(let ((v (c::declar EXPR))) body)` → `type v = EXPR; body;`. `v` must be a fresh name.
- `(let ((v (c::assign EXPR))) body)` → `v = EXPR; body;`. `v` already in scope.
- `let` without `declar`/`assign` = pure functional shadowing, emits no C.
- Multi-var side effects: `mv-let` with `c::declarn` / `c::assignn`
  (macros `declar1` … `declar8`, `assign1` … `assign8`).

## `defstruct`

```
(c::defstruct TAG (m1 type1) (m2 type2) ...)
```

- Member types: a single integer type, an integer array
  `(c::uchar 16)`, or a trailing flexible-array member `(c::uchar)`
  (last member only).
- Generated: `struct-TAG-p`, `struct-TAG-fix`, `-read-M`, `-write-M`,
  `-read-M-element`, `-write-M-element`, `-M-index-okp`, `-M-length`,
  `-read-M-list`, `-write-M-list`.
- By-value param guard: `(struct-TAG-p s)` → `struct TAG s`.
- By-pointer param guard: `(c::star (struct-TAG-p s))` → `struct TAG *s`.
- Array-member index guard (by pointer):
  `(c::star (struct-TAG-M-index-okp i))` + `(c::sintp i)`.
- Writes must be rebound: `(let ((s (struct-TAG-write-M v s))) s)`.

## `defobject` (C globals / external objects)

```
(c::defobject NAME :type (uchar SIZE) :init EXPR?)
```

- Scalar form: `:type c::sint`, etc. Optional `:init` seeds the definition.
- Guard for an accessing function: `(object-NAME-p NAME)`.
- Operations: `c::uchar-array-read`, `c::uchar-array-write`, etc.
- Only integer or integer-array types permitted.
- Formal parameters representing external objects **must be named
  identically to the `defobject` target name**.
- In `(c::atc ...)`, list the defobject name before any function that
  accesses it.

## Arrays

- Predicates and helpers per integer type:
  `<t>-arrayp`, `<t>-array-length`, `<t>-array-index-okp arr i`,
  `<t>-array-read arr i`, `<t>-array-write arr i v`.
- Guard typically includes `(equal (<t>-array-length a) N)` to tie the
  abstract length to a concrete size constant.
- Array params: guard `(c::uchar-arrayp a)` emits `unsigned char a[]`.
- Integer-pointer params: guard `(c::star (c::uintp p))` emits
  `unsigned int *p`.

## Loop idiom (tail recursion → `while`)

Follow the pattern in `/home/acl2/books/kestrel/c/atc/tests/loops.lisp`:

```
(defun |f$loop| (|n| |r|)
  (declare (xargs :guard (and (c::uintp |n|) (c::uintp |r|))
                  :measure (c::integer-from-uint |n|)
                  :guard-hints (("Goal" :in-theory (enable c::declar c::assign ...)))))
  (if (c::boolean-from-sint (c::ne-uint-uint |n| (c::uint-dec-const 0)))
      (let* ((|r| (c::assign (c::mul-uint-uint |r| |n|)))
             (|n| (c::assign (c::sub-uint-uint |n| (c::uint-dec-const 1)))))
        (|f$loop| |n| |r|))
    (mv |n| |r|)))

(defun |f| (|n|)
  (declare (xargs :guard (c::uintp |n|)))
  (let ((|r| (c::declar (c::uint-dec-const 1))))
    (mv-let (|n| |r|)
        (|f$loop| |n| |r|)
      (declare (ignore |n|))
      |r|)))
```

- The measure must decrease under `o<`.
- The body is tail-recursive and returns `mv` of all side-effected vars.
- The wrapper `|f|` initialises with `c::declar`, calls `|f$loop|`, and
  extracts the final values with `mv-let`.
- Top-level `if` inside the `$loop` body should be wrapped in an `mbt`
  invariant so the ACL2 function stays total on off-domain inputs.

## `c::atc` macro — full option list

```
(c::atc TARGET*
        :file-name      STRING           ; generated filename stem
        :output-dir     PATHNAME         ; default "."
        :header         t|nil            ; also emit .h
        :proofs         t|nil            ; default t
        :const-name     :auto|SYM
        :print          :error|:result|:info|:all
        :pretty-printing (...))
```

- **Targets** are listed in **dependency order**: first any `defobject`
  names and `defstruct` tags, then functions that use them, with
  callees before callers.
- With `:proofs t` (default), ATC emits correctness theorems of the
  form `<program>-<fn>-correct` for each function.
- `:proofs nil` skips proof generation — valuable for fast iteration.

## Pitfall checklist

1. Struct tags and defobject names must appear **before** functions
   that use them in the `(c::atc ...)` target list.
2. Struct writes require `let` rebinding; return the rebound variable.
3. Array/object length must be provable from the guard, typically via
   an `-index-okp` conjunct.
4. Only tail recursion is allowed; the measure must strictly decrease.
5. Any operator that may overflow, divide by zero, or shift out of
   range needs its `-okp` predicate as a guard conjunct.
6. Pointers to distinct struct formals are assumed non-aliasing by
   generated proofs — don't alias them in callers.
7. No implicit integer conversions; use `<t1>-from-<t2>` explicitly.
8. Only the **last** struct member may be a flexible array `(c::uchar)`.
9. `:proofs nil` skips proof generation; flip it on for release builds.
10. A user function call that takes a `defobject` is an *expression
    term*, not a pure expression. It may not appear inside pure
    operators like `c::boolean-from-sint` or in an `if` test directly;
    bind via `c::declar` first. (See `NOTES.md` §4.)
