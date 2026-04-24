# ATC Development Notes for WASM-VM1

Empirical gotchas and patterns discovered while building the M1 WASM
interpreter via Kestrel ATC (ACL2 → C17 code generator).

References in this workspace:
- `smoke/smoke4.lisp` — struct + array + pointer template (certified).
- `wasm-vm1.lisp` — live baseline: `defobject`, `defstruct`, and a
  cross-function call chain that passes ATC and emits clean C.

External references:
- `/home/acl2/books/kestrel/c/atc/doc.lisp` — normative user documentation.
- `/home/acl2/books/kestrel/c/atc/tests/` — exhaustive idiom test cases.
  In particular: `defobject.lisp`, `ext-objs.lisp`, `arrays.lisp`,
  `loops.lisp`, `conversions.lisp`, `calls.lisp`, `checksum.lisp`.
- `/home/acl2/books/kestrel/c/examples/strcpy-safe-support.lisp` — a
  reusable catalogue of ~150 symbolic-execution rules (`*symb-exec-rules*`)
  plus lemmas like `c::uchar-array-read-of-sint-to-nth` and
  `c::uchar-array-write-of-sint-to-update-nth`. Pull from here for M3
  equivalence proofs; do not redevelop.

---

## 1. Environment and certification

- cert.pl **requires** `-j $(nproc)`. Without it, builds appear to hang.
- The `acl2-jupyter` devcontainer ships with only basic books built.
  To build Kestrel once: `cd $ACL2_SYSTEM_BOOKS && make -j $(nproc) kestrel`.
- Book-level cert flags must appear in the per-dir `cert.acl2` (or
  `BOOK.acl2`) file right after `(in-package "ACL2")`:
  ```
  ; cert-flags: ? t :useless-runes nil :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib) (:open-output-channel!))
  ```
  Without the ttags line, ATC fails with "ttag :QUICKLISP not permitted".
- Use `:proofs nil` on `(c::atc ...)` during development for ~10× faster
  iteration. Turn proofs back on for milestone commits.

---

## 2. `defstruct` (C structures in ACL2)

- The struct tag MUST be listed as an explicit ATC target **before** any
  function that mentions the struct:
  `(c::atc |point2D| |read_x_by_value| :file-name ... :header t)`.
  Omitting it yields: "guard … has no type predicate for formal parameter".
- Member types: integer types (`c::sint`, `c::uint`, `c::uchar`, …) or
  integer-arrays (`(c::uchar 16)`). Nested structs are not allowed.
- Parameter flavours:
  - **By value:**   guard `(struct-TAG-p x)` → emits `struct TAG x`.
  - **By pointer:** guard `(c::star (struct-TAG-p x))` → emits `struct TAG *x`.
- Array-member index guard (by pointer): `(c::star (struct-TAG-FIELD-index-okp i))`
  with `(c::sintp i)`.
- Readers: `(struct-TAG-read-FIELD x)` or
  `(struct-TAG-read-FIELD-element i x)`.
- **Writes must be rebinding `let`s, and the function must return the
  rebound struct variable:**
  ```
  (defun set_x (v s)
    (declare (xargs :guard (and (c::sintp v)
                                (c::star (struct-TAG-p s)))))
    (let ((s (struct-TAG-write-FIELD v s)))
      s))
  ```
  Returning the raw write-call produces "term (STRUCT-TAG-WRITE-FIELD …)
  is not a C expression term".
  Under by-pointer params, ATC emits `s->field = v;` — no memcpy.

---

## 3. External objects (`c::defobject` — C globals)

- `(c::defobject |wasm_buf| :type (c::uchar 65536))` declares a global
  array. Scalars: `:type c::sint` etc. Optional `:init (...)` for init values.
- **The parameter name in every ACL2 fn accessing the global MUST equal
  the defobject name.** So `|wasm_buf|` for the bytes buffer. Guard
  conjunct: `(object-NAME-p NAME)`. ATC emits accesses as the global
  itself (e.g. `wasm_buf[i]`), NOT as a parameter.
- In `:guard-hints`, expand `object-NAME-p` via `:in-theory (enable object-NAME-p)`.
  Example: `(("Goal" :in-theory (enable object-|wasm_buf|-p)))`.
- For array reads needing promotion to sint, enable:
  `c::sint-from-uchar-okp-when-uchar-max-<=-sint-max` and
  `c::uchar-max-vs-sint-max`.
- The global name must appear in the `(c::atc ...)` target list,
  **before** any function using it.

---

## 4. Calling a helper across defobject/struct arguments

Two flavours of "call another function" matter for ATC:

### 4a. A user-fn call that takes a `defobject` is NOT a pure expression

Example: `(|check_magic| |wasm_buf|)` may NOT appear inside
`(c::boolean-from-sint …)`, inside an `if` test directly, or in any pure
expression slot. It is an *expression term* at best.

**Workaround:** bind via `c::declar`:

```
(let* ((|ok| (c::declar (|check_magic| |wasm_buf|))))
  (if (c::boolean-from-sint |ok|)
      ...))
```

The declared variable `|ok|` is a pure expression term. Guard-hints
need `c::declar` (and `c::assign` if rebinding) enabled so the prover
can recover `sintp` for the bound value.

### 4b. Inline byte access — prefer `defmacro`

ATC forbids one user function passing a defobject-array into another
user function in a pure-expression context. Use a macro to inline the
array read instead of wrapping it in a `defun`:

```
(defmacro byte-at (i)
  `(c::sint-from-uchar (c::uchar-array-read |wasm_buf| ,i)))
```

This expands at ACL2 translation time and leaves ATC with a primitive
pure expression to emit.

---

## 5. Integer-type arithmetic and comparisons

- There is **no** `eq-uchar-uchar` or `eq-<subint>-<subint>`. Compare
  sub-int values by promoting to `sint`:
  `(c::eq-sint-sint (c::sint-from-uchar x) (c::sint-dec-const N))`.
- `c::uchar-from-sint` is total; no `-okp` companion rule is needed.
  ATC emits `(unsigned char) v`.
- For shifts (e.g. LEB128): `c::shl-uint-sint` with guard-hints
  enabling `c::shl-uint-sint-okp` and `c::shl-uint-okp`. See
  `kestrel/c/atc/tests/checksum.lisp`.
- Integer constants: `(c::<type>-<base>-const N)` where `<type>` is
  `sint/uint/slong/ulong/sllong/ullong` and `<base>` is `dec/oct/hex`.
  No direct constant-maker for sub-int types — build them with
  `(c::uchar-from-sint (c::sint-dec-const N))`.

---

## 6. Loops (tail recursion with `$loop` suffix)

- Use a `fn$loop` tail-recursive helper + a non-recursive entry `fn`.
  The entry calls the `$loop` and `mv-let`s its result. See
  `kestrel/c/atc/tests/ext-objs.lisp` and `loops.lisp`.
- Loop body uses `c::declar` for fresh locals and `c::assign` for
  rebindings; ATC emits `while(...)` or `for(...)`.
- Typical ingredients in `:guard-hints` and `:hints`:
  `c::add-sint-sint`, `c::add-sint-sint-okp`, `c::sub-sint-sint`,
  `c::sub-sint-sint-okp`, `c::sint-integerp-alt-def`, `c::declar`,
  `c::assign`, `c::ne-sint-sint`, `c::integer-from-cinteger-alt-def`,
  `c::sint-from-boolean`.
- The top-level `if` inside the `$loop` body must have an `mbt`
  invariant to keep the function well-formed on off-domain inputs
  (see `ext-objs.lisp`).

---

## 7. Diagnosing failures

- "has no type predicate for formal parameter" → struct tag missing
  from ATC target list, OR guard conjunct not in recognised shape.
- "is not a C expression term returning a C type" → you used a
  non-pure call (another fn, a struct write, …) in a pure-expression
  slot. Bind via `c::declar`, or refactor into `let`-rebinds that
  return the variable.
- "proof of the guard conjecture has failed" → missing guard-hint rules.
  Read the key checkpoint from the cert output — it shows exactly
  which `c::xxx-okp` or `object-xxx-p` predicate the prover can't open.
- "A theory expression could not be evaluated" → you cited a
  nonexistent rule in `:in-theory (enable …)`. Remove it.

---

## 8. Canonical minimal patterns

### Defobject + struct + cross-call (all present in `wasm-vm1.lisp`)

```
(c::defobject |buf| :type (c::uchar 1024))

(c::defstruct |mod| (|err| c::uchar))

(defun |helper| (|buf|)
  (declare (xargs :guard (object-|buf|-p |buf|)
                  :guard-hints (("Goal" :in-theory (enable object-|buf|-p
                                                           c::uchar-array-index-okp)))))
  (c::sint-from-uchar (c::uchar-array-read |buf| (c::sint-dec-const 0))))

(defun |top| (|m| |buf|)
  (declare (xargs :guard (and (c::star (struct-|mod|-p |m|))
                              (object-|buf|-p |buf|))
                  :guard-hints (("Goal" :in-theory (enable object-|buf|-p
                                                           c::declar)))))
  (let* ((|v| (c::declar (|helper| |buf|)))
         (|m| (struct-|mod|-write-|err| (c::uchar-from-sint |v|) |m|)))
    |m|))

(c::atc |buf| |mod| |helper| |top| :file-name "demo" :header t :proofs nil)
```

### Cert command

```
cd /workspaces/wasm-acl2/atc && \
  /home/acl2/books/build/cert.pl --acl2 /opt/acl2/bin/acl2 -j $(nproc) wasm-vm1
```
