# ATC → Verified C WASM Interpreter — Design Plan

**Goal.** Use Kestrel's ATC (ACL2-to-C) to emit a C implementation of a
WASM interpreter whose correctness against `execution.lisp` is proved
by construction, and whose executable can run the `.wat`/`.wasm`
programs already in [tests/oracle/](tests/oracle/) — producing the
same values the V8 oracle produces.

This document is planning only. Scope it, cut it, approve it, then
build.

---

## 1. What ATC gives us (and doesn't)

### Supports

Confirmed from `books/kestrel/c/atc/` (tests + pretty-printer):

- Integer types: `schar`, `uchar`, `sshort`, `ushort`, `sint`, `uint`,
  `slong`, `ulong`, `sllong`, `ullong` — with tight guards, overflow
  handling, and all bitwise/shift ops.
- Structs (`defstruct`), including nested.
- Arrays (`uchar-array`, etc.), both read and write; passed as
  pointers with explicit length guards.
- Pointers (`pointer-types`, `pointed-integers`).
- Loops via tail recursion (`loops.lisp` in tests).
- Conditionals, sequencing, local variables, function calls.
- External objects (`defobject`) for global-ish state that C sees as a
  top-level variable or passed pointer.

### Does NOT support (current constraints)

- **Floating point.** The pretty-printer has:
  `:float (prog2$ (raise "Internal error: floating constants not supported.") …)`.
  There is `float`/`double` as a type name, but no emission path for
  f32/f64 operations. **This is the single biggest issue for WASM.**
- General recursion (tail recursion only).
- Symbols, quasiquotes, alists, `cons`-based lists. Data has to be
  structs and arrays.
- Dynamic allocation / `malloc`. Every array size has to be a static
  ceiling on the ACL2 side.
- Unions.
- Variadic functions.

### What this implies for us

Every single line of `execution.lisp` today uses symbols
(`'i32.add`, `'i32.const`), quasiquote shapes (`` `(:i32.const ,x) ``),
and alists (frames, stores). None of that is ATC-compatible. A WASM
interpreter for ATC has to be a **second implementation** written in
ATC's C-friendly ACL2 subset, and we prove it equivalent to the
current spec.

---

## 2. Scope cuts for v0

To get *something* running the oracle examples end-to-end, we cut
aggressively:

1. **Integer-only.** Run the subset of oracle programs that do not use
   floats: `gcd`, `sum_array`, `hash`, `collatz`, `is_prime`,
   `packed_mem`, `factorial`, and anything else that only touches
   i32/i64. Defer `float_ops`, `inf_arith_oracle`, `nan_oracle`,
   `signed_zero_oracle` until ATC grows float support (or we add a
   trusted C stub for that subset).
2. **Single module, single instance.** No multi-module linking for v0.
3. **No host imports.** Oracle examples don't use any.
4. **Interpreter only.** No JIT, no ahead-of-time compilation.
5. **Bounded everything.** Operand stack, label stack, call stack,
   locals, memory all have compile-time maxima. Programs exceeding
   them trap cleanly.
6. **Eager decode.** Pre-decode the whole binary into a struct-of-arrays
   representation before execution starts. Keeps the step function
   free of binary-format parsing.

Under these cuts, v0 passes 7–9 of the ~12 oracle programs. That's
enough to demonstrate the methodology.

---

## 3. Architecture

Three layers, each a separate book:

```
┌───────────────────────────────────────────────┐
│ execution.lisp (spec, unchanged)              │  Layer 0 — ground truth
│   - Symbolic AST, run, statep, …              │
└───────────────────────────────────────────────┘
            ▲
            │ refinement theorem (Layer 2)
            │
┌───────────────────────────────────────────────┐
│ execution-atc.lisp                            │  Layer 1 — ATC-ready mirror
│   - defstruct state                           │
│   - enumerated opcodes                        │
│   - tail-recursive run-atc                    │
│   - same step function; sint/uint everywhere  │
└───────────────────────────────────────────────┘
            ▲
            │ ATC emits
            │
┌───────────────────────────────────────────────┐
│ wasm_vm.c  +  wasm_vm.h  (generated)          │  Layer 2 — C output
│   + proofs that wasm_vm.c refines             │
│     execution-atc.lisp                        │
└───────────────────────────────────────────────┘
```

Plus two glue artifacts that live outside ATC:

```
┌───────────────────────────────────────────────┐
│ decoder.c  (hand-written, trusted)            │
│   - Reads .wasm bytes, fills the structs      │
│     that wasm_vm.c expects                    │
└───────────────────────────────────────────────┘
┌───────────────────────────────────────────────┐
│ main.c (hand-written)                         │
│   - CLI: read .wasm, call wasm_vm_invoke,     │
│     print return value                        │
└───────────────────────────────────────────────┘
```

The **trust base** is: ATC + our C compiler + `decoder.c` + `main.c`.
The ACL2 interpreter in `execution.lisp` and the refinement proof
reduce `wasm_vm.c` to the spec; the decoder and main are small and
testable against the oracle.

---

## 4. Data representation

This is where most of the design lives. ATC hates symbols and cons
cells; it loves structs and arrays.

### State struct (proposed)

```
(defstruct wasm-state
  ;; operand stack — 64-bit slots tag a type nibble + value
  (opstk-vals  (array u64 MAX_OPSTK))
  (opstk-tags  (array u8  MAX_OPSTK))     ; 0=i32 1=i64 2=f32 3=f64
  (opstk-top   uint)

  ;; label stack — one entry per active block/loop/if
  (labels-arity     (array u8    MAX_LABELS))
  (labels-is-loop   (array u8    MAX_LABELS))     ; 0/1 bool
  (labels-cont-ip   (array uint  MAX_LABELS))     ; IP to jump to on br
  (labels-end-ip    (array uint  MAX_LABELS))
  (labels-top       uint)

  ;; call stack — one entry per active function invocation
  (frames-fn-idx    (array uint  MAX_FRAMES))
  (frames-ip        (array uint  MAX_FRAMES))
  (frames-locals-base (array uint MAX_FRAMES))
  (frames-top       uint)

  ;; locals — flat arena, each frame has a slice
  (locals-vals (array u64 MAX_LOCALS_TOTAL))
  (locals-tags (array u8  MAX_LOCALS_TOTAL))

  ;; linear memory
  (mem-bytes   (array u8  MAX_MEM_BYTES))
  (mem-size    uint)

  ;; status
  (status      u8))                         ; 0=running 1=done 2=trap
```

### Pre-decoded module

```
(defstruct wasm-module
  ;; decoded instructions, flattened across all functions
  (instrs-op    (array u8   MAX_INSTRS))     ; opcode enum (0..NUM_OPS)
  (instrs-imm1  (array u32  MAX_INSTRS))     ; first immediate (or 0)
  (instrs-imm2  (array u32  MAX_INSTRS))     ; second immediate
  (fn-entry-ip  (array uint MAX_FUNCS))      ; IP where each fn starts
  (fn-num-locals (array u8  MAX_FUNCS))
  (fn-arity     (array u8  MAX_FUNCS))
  ;; …table, types, exports…
  )
```

This is effectively a bytecode VM, not a tree-walking AST
interpreter. The spec in `execution.lisp` is tree-walking; the
equivalence proof (§6) bridges the two.

### Opcode enumeration

```
(defconst *op-unreachable* 0)
(defconst *op-nop*         1)
(defconst *op-block*       2)
(defconst *op-loop*        3)
(defconst *op-br*          4)
(defconst *op-br-if*       5)
(defconst *op-br-table*    6)
(defconst *op-end*         7)
(defconst *op-return*      8)
(defconst *op-call*        9)
(defconst *op-call-indirect* 10)
(defconst *op-drop*        11)
(defconst *op-select*      12)
(defconst *op-local-get*   13)
(defconst *op-local-set*   14)
(defconst *op-local-tee*   15)
(defconst *op-i32-const*   16)
(defconst *op-i32-add*     17)
;; …one per WASM 1.0 instruction we support in v0
```

Integers, not symbols. The decoder translates the binary's WASM opcode
bytes into these (the mapping is 1:1 for single-byte opcodes and
mostly-1:1 for the prefixed ones).

---

## 5. The step function

One tail-recursive ACL2 function:

```
(defun step-atc (s m fuel)
  (declare (xargs :guard (and (wasm-statep s)
                              (wasm-modulep m)
                              (uintp fuel))
                  :measure (nfix fuel)))
  (if (or (zp fuel)
          (not (eq (wasm-state->status s) *status-running*)))
      s
    (let* ((frame-top (wasm-state->frames-top s))
           (ip        (aref (wasm-state->frames-ip s) (- frame-top 1)))
           (op        (aref (wasm-module->instrs-op m) ip)))
      (cond ((= op *op-i32-add*)
             (step-atc (do-i32-add s) m (- fuel 1)))
            ((= op *op-i32-mul*)
             (step-atc (do-i32-mul s) m (- fuel 1)))
            ;; …one branch per opcode…
            (t
             (step-atc (trap s) m (- fuel 1)))))))
```

Each `do-i32-*` is ~5 lines of pure array manipulation (pop two,
compute, push one, advance IP). ATC turns this into a `while` loop
with a switch.

**Top-level entry point (also ATC-compiled):**

```
(defun wasm-vm-invoke (m fn-idx arg0 arg1)
  (declare (xargs :guard …))
  (let ((s (wasm-initial-state m fn-idx arg0 arg1)))
    (let ((s (step-atc s m (wasm-fuel-bound)))) ;; large constant
      (wasm-state-result s))))
```

The C signature becomes `uint64_t wasm_vm_invoke(wasm_module *m,
unsigned fn_idx, uint32_t a0, uint32_t a1)` (or similar — we'll
generate several arities, since ATC requires a fixed signature per
function).

---

## 6. The refinement proof

This is the hard part. Theorem goal:

```
(defthm execution-atc-refines-execution
  (implies (and (wasm-statep s-atc)
                (wasm-modulep m)
                (match-state s-atc s-spec m-spec))
           (match-state (step-atc s-atc m fuel)
                        (run fuel s-spec)
                        m-spec)))
```

where `match-state` is an abstraction function relating the flat
struct-of-arrays representation to the tree-of-alists representation
in `execution.lisp`. The decoder gives the `match-state` premise at
module-load time.

**Strategy.** Prove one opcode at a time:

```
(defthm step-atc-i32-add
  (implies (match-state s-atc s-spec m-spec)
           (match-state (do-i32-add s-atc)
                        (execute-instr '(:i32.add) s-spec)
                        m-spec)))
```

~60 of these (one per supported opcode) plus ~10 structural ones
(operand stack push/pop, label push/pop, frame push/pop, IP advance,
branch target resolution). Each is mechanical given a good
`match-state` definition.

**Then the main theorem** is by induction on fuel, using the per-opcode
lemmas as rewrite rules.

**Effort estimate.** The per-opcode lemmas are copy-paste-intensive
but individually shallow. Plan ~2 months for the full WASM 1.0
integer subset, assuming we've already built `match-state` and proved
5–10 representative opcodes as templates.

---

## 7. Running the oracle

Once `wasm_vm.c` is generated and a hand-written `decoder.c` + `main.c`
link around it, the oracle harness becomes a direct comparison:

```
for wat in tests/oracle/*.wat; do
  wat2wasm "$wat" -o /tmp/$(basename $wat .wat).wasm
  node tests/oracle/check-all.mjs    # V8 values
  ./build/wasm_vm /tmp/*.wasm        # our verified VM values
  diff <(node …) <(./wasm_vm …)
done
```

A new `tests/oracle/check-all-verified.sh` would drive this.

For the v0 cut (integer-only programs), expected pass rate: all 7
integer programs currently in the oracle dir. Floats blocked until a
later phase.

---

## 8. Phases

### Phase A — feasibility probe (≈ 1 week)

Port *just* `gcd` to ATC style:

- `execution-gcd-atc.lisp`: hard-codes the gcd loop as a tail-recursive
  ACL2 function using `uintp`, not the general step function. This is
  essentially what the Axe post-`tailrec` form of a factorial proof
  looks like.
- Run `atc` on it. Get `gcd.c`.
- Compile and run; compare to V8 oracle.
- Outcome: proves or disproves the ATC integration works at all, for
  ~1 week of cost.

### Phase B — state struct + minimum step function (≈ 3 weeks)

- `wasm-state` and `wasm-module` defstructs.
- `do-*` helpers for i32.const, i32.add, i32.sub, i32.mul, i32.eqz,
  local.get, local.set, br_if, loop, block, end.
- `step-atc` with those ~10 opcodes.
- ATC-compile. Link with a hand-written decoder that handles only this
  opcode subset.
- Target: run `factorial.wasm` end-to-end.

### Phase C — full integer WASM 1.0 (≈ 4 weeks)

- All remaining i32/i64 opcodes: shifts, rotates, comparisons,
  conversions (i32↔i64), load/store (8/16/32-bit + signed/unsigned),
  `br_table`, `call`, `call_indirect`, `return`, `select`, `drop`,
  `local.tee`, globals.
- Expanded decoder.
- Target: pass `gcd`, `sum_array`, `hash`, `collatz`, `is_prime`,
  `packed_mem`, `factorial`, `call_indirect`, `edge_cases` (minus
  float parts) against V8.

### Phase D — refinement proof (≈ 8 weeks)

- `match-state` abstraction function.
- Per-opcode simulation lemmas.
- Main `execution-atc-refines-execution` theorem.
- At this point we can say each generated C function has a proof of
  equivalence to `execution.lisp` on all inputs satisfying the
  structural bounds.

### Phase E — floats (blocked on upstream)

- ATC does not currently emit float types/ops. Options:
  1. **Wait / contribute.** Add f32/f64 to ATC's pretty-printer and
     type system. This is upstream work at Kestrel.
  2. **Trusted C stub.** Hand-write `float_ops.c` implementing
     f32/f64, prove it matches `execution.lisp`'s float ops outside
     ATC (by testing against V8, not by formal proof), and link it in.
     Weakens the trust story for float programs only.
- Until one of these lands, `float_ops.wat`, `inf_arith_oracle.wat`,
  `nan_oracle.wat`, `signed_zero_oracle.wat` stay oracle-tested but
  not run through our VM.

### Phase F — performance (optional)

- Benchmark against V8. Verified interpreters are typically 10–100×
  slower than V8; expect that.
- If it matters, consider ACL2-to-LLVM via Kestrel's newer tooling
  once it matures, or hand-written fast paths preserved by
  equivalence.

---

## 9. Deliverables matrix

| Artifact | Phase | Size (est.) | Verified? |
|---|---|---|---|
| `execution-gcd-atc.lisp` | A | 80 LOC | Y (guards) |
| `gcd.c` generated | A | — | Y (ATC) |
| `execution-atc.lisp` | B–C | ~2500 LOC | Y (guards) |
| `wasm_vm.c` generated | B–C | ~5000 LOC | Y (ATC) |
| `match-state` + per-op lemmas | D | ~3000 LOC | Y |
| `execution-atc-refines-execution` | D | ~300 LOC | Y |
| `decoder.c` | B–C | ~1000 LOC | N (trusted) |
| `main.c` + CLI | B | ~200 LOC | N (trusted) |
| Oracle harness | B | ~100 LOC | N |

**Total verified output:** ~10 000 LOC generated C + ~3 000 LOC
refinement proof.
**Total trusted code:** ~1 200 LOC of decoder + CLI.

---

## 10. Risks and open questions

- **R1 — ATC limits.** If ATC can't express something we need (e.g.,
  16-bit signed arithmetic corner case, struct-returning functions),
  we're blocked. Phase A is the cheap probe; if ATC can't even emit
  `gcd`, escalate to Kestrel before committing further.
- **R2 — Size of generated C.** ATC emits one C function per ACL2
  function. A ~60-opcode `step-atc` with inlined helpers will produce
  a very large function. May need to split into per-opcode C
  functions (which means one ACL2 function per opcode); that balloons
  the refinement proof but keeps each unit small.
- **R3 — Pre-decode vs. on-the-fly.** Pre-decoding means the decoder
  is untrusted (reasonable; easy to fuzz against the V8 oracle). But
  it also means the ACL2 side reasons about the decoded form, not the
  raw bytes. To prove "our VM on the raw bytes = V8 on the raw bytes"
  we'd need either a verified decoder (large — WASM binary format is
  ~20 pages of spec) or a separate decoder correctness argument.
  Recommend: start with trusted decoder + fuzzing, revisit later.
- **R4 — Float support in ATC.** As noted. May need upstream work.
- **R5 — Fuel vs. real execution.** ATC-generated C will pass `fuel`
  through as a `uint64_t` counter. That's fine for correctness but
  wastes a register; once the proof is done, we can replace the
  counter with an infinite-loop idiom if ATC supports it.
- **Q1.** Do we keep `execution.lisp` as the reasoning target and
  treat `execution-atc.lisp` as a compilation mirror, or do we make
  `execution-atc.lisp` the primary spec and rewrite the gcd/factorial
  proofs on top of it? The former preserves existing investment; the
  latter would give a simpler story long-term.
- **Q2.** Should we upstream WASM support to ATC as a motivating
  example? Could help the float and struct-return constraints get
  priority attention.

---

## 11. Recommendation

Do Phase A first — one week, one file. If ATC happily emits a working
`gcd.c` from an ATC-style rewrite of the gcd loop, the rest of this
plan is engineering. If it doesn't, we've learned the limits cheaply
and can talk to Kestrel before committing.

After Phase A:

- If success → Phase B (state struct + 10 opcodes + factorial).
- Phase D (refinement proof) can be started in parallel with Phase C
  once the state struct stabilizes; it's the long pole.
- Phase E (floats) is deferred until ATC upstream has float emission,
  or we decide to weaken the trust story for floats via a trusted
  stub.
