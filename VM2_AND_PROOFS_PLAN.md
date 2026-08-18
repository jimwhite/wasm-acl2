# Plan: Complete VM2 + Close the Spec↔VM Proof Gap

**Date:** 2026-08-18
**Status:** Planning only. No code written yet.
**Companion:** [REVIEW.md](REVIEW.md) documents the current state and the gaps this plan closes.

This plan has two goals:

1. **Finish VM2's two-tier execution** — deliver what `codegen/VM2_PLAN.md` claims but has not yet implemented (a real `exec_straight_line` / `exec_blocks` split, the missing opcodes, LEB128 baking).
2. **Close the ATC trust gap** — turn on `:proofs t`, build the read-of-write support book, and complete the spec↔VM refinement proof (milestone M6).

Every phase ends with a runnable artifact or a certifying book. No preparatory work lands without something demonstrable.

---

## Phase A — Finish VM2's two-tier execution

**Goal.** Make `exec_blocks` actually block-structured: an inner straight-line loop with a real structural measure (no fuel) and an outer block-transition loop whose fuel counts block transitions, not instructions.

### A1. Implement `|exec_straight_line|` (inner loop)

- New defun in `codegen/wasm-vm2.lisp`:
  ```
  (defun |exec_straight_line| (|st| |sp| |pc| |end_pc| |halted| |wasm_buf|)
    :measure (nfix (- 65536 (c::integer-from-sint |pc|)))
    ...)
  ```
- Executes only straight-line opcodes (no `block`/`loop`/`if`/`br`/`br_if`/`else`/`return`/`end`). Every iteration consumes ≥1 byte of bytecode, so the measure is structural — **no fuel argument**.
- Stops when it hits a control-flow op or `pc >= end_pc`.

### A2. Implement `|exec_blocks|` (outer dispatcher)

- Rewrite the existing `|exec_blocks|` to:
  1. Run the straight-line body of the current block via `|exec_straight_line|`.
  2. Dispatch on the trailing control-flow op (`block`/`loop`/`if`/`br`/`br_if`/`else`/`return`/`end`).
  3. Decrement fuel (counts block transitions), recurse with the new block index.
- Measure: `(nfix (c::integer-from-sint |fuel|))` — fuel now counts block transitions, not instructions.

### A3. Add the missing opcodes to the straight-line set

Per `VM2_PLAN.md`'s own Phase-4 notes, factorial/is_prime/collatz currently fail because `exec_blocks` lacks:

| Opcode | Hex | Shape |
|---|---|---|
| `i32.const` | 0x41 | push immediate |
| `i32.add` / `i32.sub` / `i32.mul` | 0x6a/0x6b/0x6c | binop over operand stack |
| `i32.lt_u` | 0x49 | relop |
| `i32.le_u` | 0x4f | relop |
| `i32.div_u` | 0x6e | binop-nz |
| `return` | 0x0f | jump to function epilogue |
| `if` / `else` | 0x04/0x05 | bracket kinds in `|wcfg|` |

### A4. Bake LEB128 immediates at parse time

- Extend `|wcfg|` with sparse parallel arrays `(|imm_pc| (c::sint 256))` + `(|imm_val| (c::sint 256))`.
- `|extract_cfg$loop|` records each immediate-bearing PC + decoded value in the next free slot.
- Straight-line arms call a new `|wcfg_imm_at| pc w` helper (mirroring `|wcfg_end_pc_at|`).
- This lifts the "≤63 single-byte immediate" cap and the 16-local cap.

### A5. New fixture + live-V8 oracle

- Add a fixture with constants > 127 (e.g. `(local.get 0) + (i32.const 200)`).
- **Fix the oracle harness:** `codegen-run-vm2` currently compares against hardcoded expected values in the Makefile. Change it to invoke V8 live (like `oracle-verified-m1` does), so every fixture is diffed against the real oracle.

**Exit criteria:**
- `make codegen-run-vm2` passes 8/8 (now 9/9 with the new fixture) against **live V8**.
- Generated C contains no fuel decrement in straight-line arms.
- `|exec_straight_line|` has a structural measure (no fuel argument).

---

## Phase B — Close the ATC trust gap

**Goal.** Make the "generated C refines the ACL2 spec" claim real, not just trusted.

### B1. Turn on `:proofs t`

- Enable `:proofs t` on at least one `c::atc` call (start with the small 7-op `codegen/demo.lisp` set to measure certification cost).
- This emits per-function theorems of the form "the C execution of `invoke` implements the ACL2 `|invoke|`" into the book.
- Measure the certification-time increase before applying broadly.

### B2. Write `atc/refinement/atc-wasm-support.lisp`

The documented blocker for the spec↔VM refinement. Port the `strcpy-safe` idiom to `uint` arrays:

- `uint-array-read-of-sint-to-nth` / `uint-array-write-of-sint-to-update-nth` (convert array ops into `nth`/`update-nth`, where the identity is standard).
- Composed into `struct-wst-read/write-<field>-element` so read-of-write-same/diff reduce to the standard `nth`/`update-nth` identities.
- `sint-from-uchar-of-uchar-from-sint` under the natural bounds (the byte→sint bridge).

**Exit criteria:** The support book certifies; the `local.get` connection theorem in `atc/refinement/proof-local-get.lisp` completes (spec side + ATC side + read-of-write + byte bridge).

---

## Phase C — Spec↔VM refinement proof (M6)

**Goal.** Prove the ATC VM refines `execution.lisp`.

### C1. `match-state` abstraction

- Define `match-state` mapping the flat `struct wst` (op[], loc[]) to the tree-of-alists spec state (`statep`).
- `(current-operand-stack state) <-> op[0..sp-1]`, `(current-locals state) <-> loc[0..]`, with the spec's wrapped value constructors carrying the concrete `uint`.

### C2. Per-opcode simulation lemmas

- Start with the 5 VM2 straight-line ops (`local.get`, `local.set`, `local.tee`, `i32.eqz`, `i32.rem_u`).
- Each: `(match-state s-atc s-spec) ⇒ (match-state (step-atc s-atc m) (run s-spec))` for that opcode.
- Reuse the `atc-wasm-support` book for the read-of-write and byte-bridge steps.

### C3. Main theorem

- `(match-state s-atc s-spec) ⇒ (match-state (step-atc s-atc m) (run s-spec))` extended by fuel induction.

**Exit criteria:** Main refinement theorem certifies with no `skip-proofs`; oracle suite stays green.

---

## Phase D — Honesty fixes

**Goal.** Make the docs match reality.

### D1. Parser honesty

- Update `README.md`, `atc/README.md`, `codegen/README.md`, and `WASM_ATC_PLAN.md` to state clearly that the ATC VM's parser is a **rewrite** (single-byte LEB, one export/function/local-group), not a reuse of `parse-binary.lisp`.
- Treat full `parse-binary.lisp` reuse as a separate future milestone (the plan's M7).

### D2. Oracle harness consistency

- Make every oracle target (`oracle-verified-m1`, `codegen-run`, `codegen-run-vm2`) compare against **live V8**, not hardcoded expected values.

**Exit criteria:** Docs accurately describe the parser and the oracle harness; no target claims V8 verification it doesn't perform.

---

## Verification (definition of done)

1. `make codegen-run-vm2` passes 8/8 (9/9 with new fixture) against live V8.
2. `make wasm-vm1` + `oracle-verified-m1` still green.
3. New fixture with constants > 127 runs correctly through v2.
4. The `:proofs t` book certifies with real C-refinement theorems.
5. `atc/refinement/atc-wasm-support.lisp` certifies; the `local.get` connection theorem completes.
6. Main refinement theorem (C3) certifies with no `skip-proofs`.

---

## Decisions

- **Prioritize the refinement proof (Phases B/C) over adding more opcodes.** Growing the unverified surface is counterproductive.
- **Finish VM2's two-tier execution (Phase A) first** — it's self-contained, gives a runnable artifact, and is the plan's stated architecture. Then Phases B/C.
- **Document the parser as a rewrite now** (cheap); full `parse-binary.lisp` reuse is a separate future milestone.

---

## Open questions

1. **Phase A vs. B/C ordering.** Sequential (A → B → C) is recommended. If certification time is a concern, B1 (the `:proofs t` cost probe) can run in parallel with A.
2. **`:proofs t` scope.** Start with `demo.lisp` (7 ops) to measure cost; apply broadly only if acceptable.
3. **VM2 opcode breadth vs. refinement.** Should Phase A add all 8 missing opcodes, or just enough for the new fixture + factorial? Recommendation: add all 8 — they're the same shape patterns already proven in VM1/codegen.
