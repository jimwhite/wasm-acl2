# WASM Loop Lifter — Design Plan

**Status:** planning only. No code written yet. Reviewed against the Axe
x86 reference implementation at
`/home/acl2/books/kestrel/axe/x86/loop-lifter.lisp` (2872 LOC, marked
"First working version" with many open TODOs of its own).

**Goal.** Produce a `lift-subroutine`-equivalent macro for WASM so that
a factorial (or gcd, or any single-loop numerical routine) proof can be
written in ~100 lines and look essentially identical to
`kestrel/axe/x86/examples/factorial/factorial-elf64.lisp`.

This document is a plan, not a commitment. It breaks the work into
phases with concrete deliverables, dependencies, and pruning options
("do we really need this for our first working version?"). The answer to
that question is what determines prioritization.

---

## 1. What the Axe x86 lifter actually does

Reading `loop-lifter.lisp` end-to-end, `lift-subroutine` is a pipeline
of roughly these stages:

| # | Stage | Axe x86 artifact |
|---|-------|------------------|
| 1 | Parse binary | `parse-executable` (ELF / Mach-O / PE) |
| 2 | Build an initial assumption set about the machine state | `assumptions-new` / `assumptions32` |
| 3 | Represent the initial state as a DAG over `x86_0` | `dagify0`, `compose-dags` |
| 4 | Symbolically step the DAG with a rewriter, stopping at loop headers | `rewriter-x86`, `run-until-exit-segment-or-hit-loop-header` |
| 5 | Extract PC / RSP from the DAG to detect where we are | `extract-pc-dag`, `extract-rsp-dag`, `extract-rbp-dag` |
| 6 | Analyze one iteration of the loop body: split into *continue* term and *exit* term under a test | `analyze-loop-body` |
| 7 | Decompose the continue-term into "this register got this value, this memory cell got this value, this flag got this value" | `check-and-split-one-rep-term` |
| 8 | Build loop parameters (one per updated state component + read-only components the body depends on) | `make-loop-parameters-*` family |
| 9 | Emit a recursive `defun` for the loop using the supplied `:measures` | `lift-loop` (see `(defun ,loop-fn …)` event) |
| 10 | Splice the recursive call back into the DAG at the loop header | `compose-dags`, `wrap-term-around-dag` |
| 11 | Continue symbolic execution past the loop to the function return | |
| 12 | Emit the top-level `defun <name>` that the user proves against | `lift-subroutine-fn` |
| 13 | (Optionally) prove a correctness theorem linking `run` of the binary to the emitted function | `produce-theorem` path |

Key infrastructure required by 4, 6, 8:

- **An Axe-style DAG + rewriter** tuned to the target ISA's normal form.
  For x86 this is `rewriter-x86` built on `rewriter-basic`, plus many
  rule lists (`new-normal-form-rules64`, `read-over-write-rules*`,
  `write-over-write-rules*`, `canonical-rules-bv`, ~20 more). Total
  rule-list code: several thousand lines, accumulated over ~10 years.
- **A "one step" opener rule** (`run-until-exit-segment-or-hit-loop-header-opener`
  and the base cases). This is the one rule that makes symbolic
  execution terminate at loop headers.
- **State "setter/getter" schema**
  (`*setters-to-getters-alist*`) — a fixed list of state components
  each with a reader and a writer. The rewriter normalizes any update
  into this schema.

Things the x86 lifter *does not do* that we'd want to think about:

- It does not synthesize the measure — the user supplies it.
- It does not handle nested loops in full generality (the source
  comments call this out).
- It does not handle subroutine calls from inside a loop body (same).
- It does not produce the spec-level correctness theorem — only the
  recursive `defun`. The "connection lemma + final" are still
  hand-written.

So a working Axe-equivalent for WASM is a tool that, given
`(factorial.wasm, :target "fact", :loops …, :measures …)`, produces
`(defun factorial-loop-1 …)` and `(defun factorial …)`. Everything
after that is hand-written APT + one-line theorems.

---

## 2. What we have and don't have

### Have

- **Binary parser.** `load-wasm-funcinsts` reads a `.wasm` module and
  produces `funcinst-listp`. This is strictly easier than ELF parsing
  (WASM binaries are self-describing, no relocations). Equivalent of
  stage 1.
- **Concrete interpreter.** `execution.lisp` provides `run`,
  `execute-instr`, and state accessors (`current-instrs`,
  `current-operand-stack`, `current-label-stack`, `state->call-stack`,
  `top-frame`, etc.). This is ground truth.
- **Hand-written proof recipe** (see
  [proofs/GCD_PROOF_NOTES.md](proofs/GCD_PROOF_NOTES.md)) — counted-step
  lemmas, iter-step, exit-step, header shape, iter-fuel, exit-fuel,
  total-fuel, loop-fn spec, final. This is exactly what a lifter would
  *emit*.
- **Failed-lifter post-mortem** (see
  [proofs/GCD_PROOF_NOTES.md](proofs/GCD_PROOF_NOTES.md) Appendix D)
  documenting the encapsulate-witness attempt and why it doesn't scale.

### Don't have

- No Axe DAG rewriter configured for WASM. This is the single biggest
  missing piece.
- No WASM rule lists. Every opener and read-over-write lemma would
  need to be authored and proved against `execute-instr`.
- No normal form for WASM state. x86 has a clean one (registers,
  flags, linear memory, `undef`). WASM state is a tree:
  `call-stack → frames → operand-stack + label-stack + locals`,
  plus a store of function instances. A rewriter needs this tree
  flattened into set/get pairs before stages 6–8 work.
- No loop-header concept baked into `run`. x86's `run-until-exit-…`
  has an explicit stop predicate. WASM's `run` is fuel-bounded and
  doesn't know what a loop header is. We need the equivalent.

---

## 3. Proposed plan

Six phases, each one independently useful. The tool is usable after
phase 4; phases 5 and 6 are polish.

### Phase 1 — Normal form and state schema (≈ 1 week, ~500 LOC)

Decide on a canonical state shape the rewriter will maintain. Candidate:

```
(state call-stack store)
  where call-stack = (frame …)
        frame     = (operand-stack label-stack locals instrs fn-idx)
```

Deliverables:

- `wasm-state-normal-form.lisp`: a list of rewrite rules that push all
  updates into a canonical `(update-frame :operand-stack … :locals …)`
  form, analogous to x86's `xw`/`xr`.
- A `*wasm-setters-to-getters-alist*` listing every named state
  component we're willing to lift over (locals[0..n], operand-stack,
  label-stack, instrs). This bounds the lifter's scope: locals only,
  no memory, no globals, no tables — that's enough for factorial,
  gcd, and most didactic examples.
- Read-over-write lemmas: `(get-local i (set-local j v s))`,
  `(current-operand-stack (push-operand v s))`, etc.

**Pruning question.** If we restrict to locals-only, we can skip
`read-and-write`, `separate`, `disjoint-regions48p`, and the entire
memory-aliasing machinery (which is ≈ 800 LOC of the 2872-line x86
lifter). Recommend yes for v0.

### Phase 2 — Loop-header-stopping run (≈ 3 days, ~150 LOC)

Deliverable: `run-until-loop-header` in a new file
`wasm-run-until.lisp`:

```
(run-until-loop-header loop-instr-ids s)
  = s                                    if (current-instrs s) begins
                                          with a member of loop-instr-ids
  = (run-until-loop-header loop-instr-ids (execute-one s))  otherwise
```

Plus opener / base-case / if-split lemmas, modeled directly on
`run-until-exit-segment-or-hit-loop-header-{opener,base-case-{1,2,3},of-if-split}`.

**Loop-header identification.** In WASM binaries there is no "PC" —
control lives in the `instrs` queue. The natural identifier is the
`(block …)`/`(loop …)` nesting path or a tagged instruction pointer.
Proposal: have the lifter walk the function body and tag each `loop`
instruction with a unique integer label, then have
`run-until-loop-header` compare by that tag.

### Phase 3 — Minimum-viable rewriter configuration (≈ 1 week, ~300 LOC + reused Axe)

We do **not** need to write our own DAG rewriter. `kestrel/axe/rewriter-basic`
is generic. What we need is:

- A rule-alist constant `*wasm-symbolic-execution-rules*` collecting:
  - `run-until-loop-header` opener + base cases
  - All `execute-instr` opener rules (per-opcode)
  - Phase 1 read-over-write rules
  - BV rules already in the Axe tree (`kestrel/bv/*`)
- A thin wrapper `simplify-wasm-term` that calls `simplify-term-basic`
  with this rule-alist and a known-boolean list.

This is where most of the 2872 LOC of the x86 lifter actually lives:
the rule lists. For v0 we only need enough rules to step an i32-only
program through `local.get`, `local.set`, `i32.const`, `i32.mul`,
`i32.sub`, `i32.eqz`, `br_if`, `loop`, `end`. That's ~15 openers.

### Phase 4 — `lift-wasm-loop` for single-loop routines (≈ 1 week, ~400 LOC)

Deliverable: the macro itself. Skeleton mirrors `lift-subroutine-fn`
but targeted at our smaller scope.

```
(lift-wasm-loop factorial
                :module "factorial.wasm"
                :function "fact"
                :loops ((<loop-tag> . <body-tags>))
                :measures ((<loop-tag> (nfix n))))
```

Pipeline:

1. Parse module → `funcinst-listp` (reuse existing `load-wasm-funcinsts`).
2. Walk the target function; tag loop instructions.
3. Build an initial state DAG as
   `(make-initial-state funcinsts args)`.
4. Call `simplify-wasm-term` with `run-until-loop-header` around the
   initial state → get back a DAG representing "one pass from function
   entry to first loop header."
5. Extract state components at that point (Phase 1 readers).
6. Call `analyze-loop-body` (port of x86's, reusing its structure — the
   split-on-if logic is ISA-independent).
7. Use `check-and-split-one-rep-term` ported to our setter schema to
   extract the parameter updates.
8. Emit `(defun factorial-loop-1 (…) (declare (xargs :measure …)) …)`.
9. Continue execution past the loop; repeat if more loops.
10. Emit `(defun factorial-lifted (…) …)`.

**At the end of phase 4 we should be able to reproduce
`factorial-elf64.lisp` as a ~100-line WASM file.** That is the
success criterion for v0.

### Phase 5 — APT glue (≈ 3 days, ~100 LOC)

Axe's factorial proof finishes with:

```
(apt::wrap-output …)
(apt::simplify …)
(apt::drop-irrelevant-params …)
(apt::rename-params …)
(apt::tailrec …)
```

These are already library books. The lifter doesn't need to emit them;
the user writes them. But we should provide a shared `.lisp` with the
right `include-book`s and theory settings for WASM, analogous to what
the Axe factorial example includes.

### Phase 6 — Nice-to-haves (≈ 2 weeks, defer)

- Memory-aliasing support (needed for programs that write to linear
  memory).
- Globals support.
- Nested loops.
- Automatic measure inference for common patterns (counter decrements,
  counter increments against a bound).
- Spec-side correctness-theorem generator (Axe has this as
  `produce-theorem`; useful but orthogonal).

---

## 4. Pruning recommendations for v0

To keep v0 tractable:

1. **Locals only.** No memory, no globals, no tables. Rules out Phase 6
   work until after v0 proves out.
2. **Single loop.** Axe supports nested loops in principle; comments
   say it's under-tested. We explicitly defer.
3. **i32 only.** Skip i64/f32/f64 openers for v0.
4. **User supplies loop tags and measures.** No auto-detection.
5. **No correctness-theorem auto-generation.** Emit the `defun` only;
   the connection lemma and final theorem stay hand-written.

Under these cuts, v0 is roughly **6 weeks for one engineer**, dominated
by Phase 1 (state schema + read-over-write lemmas) and Phase 3 (rule
authoring). Compare to the Axe x86 lifter's accumulated ~10 years.

## 5. Open design questions

These deserve discussion before starting:

- **Q1.** Is the `(call-stack store)` normal form right, or should we
  flatten further (e.g. hoist locals of the top frame to top-level
  setters, so locals look like registers do in x86)? The latter makes
  the rule lists smaller but ties the lifter to single-frame routines.
- **Q2.** Do we want the lifter to emit the loop body as a function of
  the **WASM state** (setter-style, like x86's `loop-fn` takes x86_N)
  or of just the **loop parameters** (numerical args, like Axe's
  post-`drop-irrelevant-params` form)? The latter is closer to what
  the user actually wants to reason about; the former is easier to
  emit.
- **Q3.** Should the lifter depend on `kestrel/axe` (pulls in a large
  book tree) or should we write a simpler rewriter tailored to WASM?
  Reusing Axe is cheaper now but couples us to upstream changes.
- **Q4.** Is there value in supporting the existing encapsulate-witness
  lifter (`wasm-loop-lifter.lisp`) as a front-end that the new lifter
  instantiates? Probably not — the `:functional-instance` path had
  enough friction that direct emission is cleaner.
- **Q5.** What's the story for `br_table`, `if`, `block`, nested
  `loop`? The current scope handles a `loop` with a single `br_if`
  exit. Extending to `if`/`block` adds one layer of label-stack
  bookkeeping; `br_table` is heavier.

---

## 6. Decision point

The cheapest path that delivers an Axe-shaped factorial proof is
**Phases 1–4 with the v0 cuts above**. Anything less and we're still
hand-writing iter-step / exit-step lemmas like v1 does.

If that cost is too high, realistic alternatives are:

- **(A) Accept v1-style ad-hoc proofs** per program. ~400 lines each,
  but they work today.
- **(B) Build only Phase 2 + a thin symbolic-executor tactic**, no
  emission of recursive functions. This would give us ~200 lines of
  savings per proof for ~1 week of tool work. Does *not* match Axe
  line-for-line but compresses the counted-step layer substantially.
- **(C) Full v0.** Matches Axe.

My recommendation: start with (B) as a feasibility probe — if the
rewriter-basic integration works cleanly on WASM, (C) becomes a
straightforward extension. If it doesn't, we've learned that for ~1
week of cost and we fall back to (A).
