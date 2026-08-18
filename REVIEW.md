# Review: WASM-in-ACL2 → ATC → C VM pipeline

**Date:** 2026-08-18
**Scope:** The parts of this project that use the ACL2 WASM spec to build a WASM VM via Kestrel's ATC (ACL2-to-C) generator.

---

## 1. What the project is

A three-layer stack, each layer built by a different agent:

| Layer | Tool | What it is |
|---|---|---|
| **Spec** | OpenHands/Opus | `execution.lisp` — a full WASM 1.0 operational semantics in ACL2 (170 instructions, certifies) |
| **ATC VM** | Copilot | `atc/wasm-vm1.lisp`, `codegen/wasm-vm2.lisp` — a *second*, hand-written interpreter in the ATC fragment |
| **C output** | Kestrel ATC | `wasm-vm1.c`, `run.c`, `wasm-vm2.c` — generated C, guard-verified |

The critical thing to understand up front: **the ATC VM is not the spec.** It is a separate, hand-written interpreter written in the restricted "ATC fragment" (C-typed operators, `defstruct`/`defobject`, tail-recursive `$loop` functions). The spec (`execution.lisp`) is a structured-AST interpreter over `statep`; the ATC VM is a flat bytecode interpreter over `struct wst`. They are linked only by an *intended* refinement proof (milestone M6) that is barely started.

---

## 2. How VM1 works (`atc/wasm-vm1.lisp`)

VM1 is the M1 feasibility proof. It is a **flat opcode dispatcher**:

- `|wasm_buf|` — a `c::defobject` global `uchar[65536]`; `main.c` `fread`s the `.wasm` into it.
- `|parse_module|` / `|parse$loop|` — a hand-written, *simplified* section walker that fills `struct wmod` (body offset/length, num params/locals, export name offset/length). It assumes single-byte LEB128 sizes, one exported function, one local group.
- `|exec$loop|` — a single tail-recursive function that dispatches on the byte at `pc` in a nested `if`-cascade (ATC emits no `switch`). Each arm does `ok`/`x_safe`/`sp_safe` gating, `pc += size`, `halted |= ~ok`, `fuel -= 1`, then tail-calls itself. State is `struct wst { op[64], loc[16], lpc[16], lsp[16], lkind[16] }` plus five scalar invariants threaded as arguments (`sp`, `nl`, `pc`, `halted`, `fuel`).
- Control flow (`block`/`loop`/`if`/`br`/`br_if`/`else`) is handled by **runtime byte-scanning** (`scan_end`/`scan_else`) to find matching `end`/`else` PCs.

**What's verified here:** guard verification proves every array index, struct access, and arithmetic op is well-defined (memory/type safety); the `fuel` measure proves totality. `:proofs nil` on the `c::atc` call means **no per-function C-refinement theorem is emitted** — the C is trusted to be a faithful translation of the ACL2 fragment (ATC is a verified generator, but the in-book proof is off).

---

## 3. The codegen layer (`codegen/`)

This is the most interesting engineering. Rather than hand-writing the ~650-line `|exec$loop|` opcode arms, `codegen/templates.lisp` + `codegen/loop.lisp` define a **template family indexed by structural shape**:

- `templates.lisp` emits standalone per-op step functions (`|exec_local_get|`, `|exec_i32_add|`, …) from shape tags like `:local-idx-pusher`, `:i32-binop-total`, `:i32-binop-nz`.
- `loop.lisp` emits the *arms* of a single dispatcher from the same shape tags, spliced into one `gen-exec-loop` macro. The 18-opcode table in `integration-demo.lisp` is ~20 lines; the generated `run.c` covers gcd/factorial/is_prime/collatz.

The key insight: **trap conditions are hoisted into the ACL2 guard** rather than the body, so the generated C is "shape-pure" — much cleaner than VM1's hand-written `ok`/`safe` gating. This is a genuine improvement and demonstrates the template approach well.

---

## 4. How VM2 works (`codegen/wasm-vm2.lisp`)

VM2 is the *intended* successor: block-structured execution over a precomputed control-flow graph, replacing runtime byte-scanning. **But the reality is more modest than the plan claims:**

- `|extract_cfg|` / `|extract_cfg$loop|` — a real, structural-measure (no fuel) linear pass that builds `struct wcfg`, a parallel-array bracket table (opener PC, kind, `end_pc`, `else_pc`, matcher stack). This is genuinely new and well-built, with `apply_open`/`apply_end`/`apply_else` helpers each carrying their own guard/return-type proofs.
- `|wcfg_end_pc_at|` — a lookup that replaces the runtime `scan_end` byte-walker for `block` entry.
- `|exec_blocks|` — **despite the name, this is still a flat per-opcode dispatcher**, not the two-tier `exec_straight_line`/`exec_blocks` structure described in `VM2_PLAN.md`. It dispatches on the byte at `pc` (0x20, 0x21, …) exactly like VM1's `exec$loop`, but consults `wcfg` for block-end positions instead of scanning. The plan's Phase 2 (inner straight-line loop with a real structural measure + outer block-transition loop) was **not implemented** — `exec_straight_line` appears only in a comment.

So VM2 is "Phase 1 + a slice of Phase 2": CFG extraction landed and is wired in, but execution is still per-opcode with the same lexicographic `fuel*70000 + (60000-pc)` measure. The opcode coverage is also still the small set (the plan's own "Phase 4 picking-up notes" admit factorial/is_prime/collatz fail because `i32.const`, `i32.add/sub/mul`, `i32.lt_u`, `return`, `if/else` aren't in `exec_blocks`).

---

## 5. What is actually demonstrated about ACL2

**Genuinely demonstrated:**
- **ATC is real and usable.** The pipeline works end-to-end: ACL2 fragment → guard-verified, memory-safe C → runnable binary that executes real `.wasm` bytes and matches V8 on the gcd oracle. This is a legitimate, non-trivial result.
- **Guard verification is doing real work.** Every array index, struct access, and arithmetic op carries a machine-checked proof obligation. The `ok`/`safe`/`x_safe` gating pattern is exactly how you make ATC accept a bounds-checked interpreter.
- **The template-family codegen is a good pattern.** Shape-based emission from a single source of truth (the spec's structural shapes) is a clean way to scale ATC without hand-writing ceremony.
- **The refinement-proof direction is sound.** `atc/refinement/proof-local-get.lisp` correctly identifies the two missing lemmas (read-of-write-same-index on generated struct accessors, and the byte→sint bridge) that block the spec↔ATC connection. This is honest, well-scoped proof engineering.

**Not demonstrated (important):**
- **The spec→VM link is not proved.** The refinement proof (M6) is one opcode (`local.get`) and even that is incomplete. The ATC VM is a *separate* implementation, only *empirically* oracle-checked against V8 — not formally shown to implement `execution.lisp`.
- **No C-level refinement theorems.** Every `c::atc` call uses `:proofs nil`, so the "generated C refines the ACL2 spec" theorems are not in any book. The trust story rests entirely on ATC being a correct translator.
- **The spec's 280 Q.E.D.s / 312 assertions are about the spec, not the VM.** They don't transfer to the ATC VM.

---

## 6. What is actually demonstrated about WASM SpecTec

- The **spec formalization** is comprehensive and impressive: 170/170 WASM 1.0 instructions, including IEEE 754 float handling, memory, tables, `call_indirect`, and a type validator with soundness theorems. This is a real, certifying model of the SpecTec semantics.
- But the **ATC VM covers only a tiny integer subset**: gcd/factorial/is_prime/collatz, single-byte LEB128, no memory, no floats, no calls, no globals, no tables. The plan's own scope cuts (M1–M4) acknowledge this.
- The fundamental tension is exposed: **the full spec is not ATC-compilable** (floats, alists, structured ASTs, general recursion all fall outside the ATC fragment). So the project is forced into the "second implementation + refinement proof" architecture, and that refinement proof is the hard, unfinished part.

---

## 7. Is this approach to verified code development effective?

**Honest verdict: promising as a feasibility demonstration, but the verification chain is not yet closed.**

What the project has *actually* delivered:
1. A certifying, comprehensive WASM 1.0 spec in ACL2 (real, valuable).
2. A working ATC-generated C interpreter for a small WASM subset that matches V8 empirically (real, valuable as a PoC).
3. A clean template-based codegen and a well-scoped start on the refinement proof (real engineering).

What it has **not** delivered (despite the plan's framing):
- **"Correctness against `execution.lisp` proved by construction" is not true yet.** The ATC VM is hand-written, not derived from the spec. The refinement proof that would close this is ~1% done.
- **The parser is a rewrite, not a reuse.** The plan said "we call `parse-binary.lisp`, not rewrite it," but the actual ATC VM contains a hand-written simplified parser (single-byte LEB, one export/function/local-group). This is a significant deviation and a trust gap the plan glosses over.
- **The oracle harness is weaker than it looks.** Only `oracle-verified-m1` actually invokes V8 at runtime. The `codegen-run` and `codegen-run-vm2` targets compare against **hardcoded expected values** in the Makefile, not against V8.
- **VM2 is not block-structured** despite the plan's claims.

**The core question — is "spec → ATC → C" effective?** The honest answer is: *the ATC half works, but the spec half doesn't connect to it yet.* ATC is a mature, verified generator, and the project demonstrates you can get memory-safe, guard-verified C from it. But the value proposition of the whole exercise — *verified* WASM execution — depends on the refinement proof (M6), which is the hardest and least-complete part. Until that lands, what you have is a well-engineered but **unverified** interpreter whose only correctness evidence is empirical oracle testing — which is exactly what you'd get from a hand-written C interpreter without any ACL2 at all.

The project is honest about this in its own docs (the READMEs and plans repeatedly flag `:proofs nil`, the missing read-of-write lemmas, and M6 as future work). So as a *research direction* it's sound and the infrastructure is genuinely reusable; as a *claim of verified code*, it's premature.

---

## 8. Concrete recommendations

1. **Turn on `:proofs t`** on at least one `c::atc` call to get real C-refinement theorems in a book — this is the cheapest way to make the ATC half of the trust story concrete.
2. **Close the read-of-write lemma gap** (`atc/refinement/atc-wasm-support.lisp`) — it's the single blocker for the spec↔VM refinement and is well-scoped.
3. **Be honest in the docs** about the parser being a rewrite (not `parse-binary` reuse) and about `codegen-run`/`codegen-run-vm2` using hardcoded expectations rather than live V8.
4. **Either finish VM2's two-tier execution or drop the "block-structured" claim** — the current `exec_blocks` is a flat dispatcher with a CFG lookup, which is fine, but the plan overstates it.
5. **Prioritize the refinement proof over more opcodes.** Adding opcodes to the ATC VM without the spec↔VM link just grows the unverified surface.
