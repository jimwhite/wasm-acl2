# End-to-End Correctness Proof of WASM `gcd` — Notes & Playbook

This note documents what was done in [proofs/proof-gcd-spec.lisp](proofs/proof-gcd-spec.lisp)
and distills a reusable recipe for proving other WASM functions correct
against ACL2 community-book specifications.

## 1. What was proved

Final theorem, [proofs/proof-gcd-spec.lisp](proofs/proof-gcd-spec.lisp#L432-L445):

```
(defthm gcd-impl-correct
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (equal (top-operand
                   (current-operand-stack
                    (run (gcd-total-fuel a b) (make-gcd-state a b))))
                  (make-i32-val (acl2::nonneg-int-gcd a b)))))
```

So for **all** 32-bit unsigned `a, b`, running the WASM gcd
implementation under the `execution.lisp` semantics produces, on top of
the operand stack, `(make-i32-val (nonneg-int-gcd a b))` — where
`nonneg-int-gcd` is the mathematical GCD from `arithmetic/mod-gcd`
(proved there to be *the* GCD).

No `skip-proofs`. All supporting lemmas are local.

## 2. Architecture of the proof

The proof is structured in three layers, from the concrete WASM
semantics up to the abstract recursive spec.

### Layer A — Concrete symbolic execution ("counted-step" lemmas)

Each lemma states: *after exactly N WASM steps from this specific
state shape, we land on this specific state shape.* These are proved
by brute-force unfolding; ACL2 just runs the interpreter.

| Lemma | Steps | Shape |
|---|---|---|
| `gcd-impl-base-case` | 6 | `make-gcd-state a 0` → top = `a` |
| `gcd-state-to-loop-entry` | 2 | `make-gcd-state a b` → `make-loop-entry-state a b 0` |
| `loop-entry-step-case` | 13 | `make-loop-entry-state a b tmp` (b≠0) → `make-loop-entry-state b (mod a b) b` |
| `loop-entry-base-case` | 4 | `make-loop-entry-state a 0 tmp` → top = `a` |

The hints are identical boilerplate:

```lisp
:in-theory (union-theories (current-theory :here) *gcd-exec-theory*)
:do-not '(generalize)
:expand ((:free (n s) (run n s))
         (:free (n s a) (top-n-operands n s a))
         (:free (n s) (pop-n-labels n s))
         (:free (v s) (push-vals v s)))
```

`*gcd-exec-theory*` is a big list of the interpreter's constructors,
accessors, and `execute-*` helpers — copied from
[proofs/proof-loop-spec.lisp](proofs/proof-loop-spec.lisp) and
[proofs/proof-abs-e2e.lisp](proofs/proof-abs-e2e.lisp). Think of it as
"enable the interpreter."

### Layer B — Plumbing: splitting `run` across iterations

To connect "13 steps = one iteration" to "`n+13` steps = `n` more steps
after one iteration", we need:

- `statep` facts:
  - `not-statep-of-done`, `not-statep-of-trap` — the non-state sentinel
    tags `:trap` and `(:done ...)` are *not* `statep`.
  - `statep-of-make-loop-entry-state`, `statep-of-make-gcd-state` —
    the states we build are `statep` (proved by enabling every
    component predicate: `call-stackp`, `framep`, `label-stackp`,
    `label-entryp`, `operand-stackp`, `val-listp`, `i32-valp`, `u32p`).

- `run-split-when-statep`:
  ```
  (implies (and (natp m) (natp n) (statep (run m state)))
           (equal (run (+ m n) state)
                  (run n (run m state))))
  ```
  Proved by explicit induction on a hand-written scheme `run-ind` that
  mirrors `run` step-by-step. `statep` on the intermediate state is
  what rules out `:trap`/`:done` branches in the inductive step.

- `run-plus-at-loop-entry`: the "one-iteration" rewrite rule, glued
  together from `loop-entry-step-case` + `run-split-when-statep`:
  ```
  (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b)
                (unsigned-byte-p 32 tmp) (not (equal b 0)) (natp n))
           (equal (run (+ 13 n) (make-loop-entry-state a b tmp))
                  (run n (make-loop-entry-state b (mod a b) b))))
  ```
  **This is the key rewrite consumed by the main induction.** The
  recursive `make-loop-entry-state` on the RHS must stay *folded* so
  subsequent applications match by pattern.

### Layer C — Induction

Three pieces:

1. **Fuel function** `gcd-loop-fuel a b` — mirrors Euclidean recursion,
   measure `(nfix b)`:
   ```
   (if (zp b) 4 (+ 13 (gcd-loop-fuel b (mod a b))))
   ```

2. **Induction scheme** `gcd-loop-ind a b tmp` — identical shape but
   with an extra `tmp` argument. In the recursive call, `tmp` is
   substituted with `b`. That substitution is **critical**: it matches
   the RHS of `run-plus-at-loop-entry`, so the induction hypothesis is
   usable without generalizing away the `tmp` position.

3. **Main loop theorem** `gcd-loop-entry-correct` — induct by
   `gcd-loop-ind`, disable the noisy lemmas
   (`loop-entry-step-case`, `loop-entry-base-case`,
   `run-split-when-statep`, `statep-of-make-loop-entry-state`,
   `(:induction gcd-loop-fuel)`, `make-loop-entry-state`,
   `acl2::nonneg-int-gcd`), `:expand` `nonneg-int-gcd`, and hint the
   base case with `loop-entry-base-case`.

4. **Final theorem** `gcd-impl-correct` — `:use`s
   `gcd-state-to-loop-entry`, `run-split-when-statep` (m=2),
   `gcd-loop-entry-correct` (tmp=0), and `statep-of-make-gcd-state`.

### Layer D — Arithmetic bridge (WASM ints ↔ math ints)

- `arithmetic-5/top` (local) — handles `(unsigned-byte-p 32 (mod a b))`.
- `bvmod-32-when-u32` — `i32.rem_u` on `u32` inputs with nonzero
  divisor equals plain integer `mod`.
- `nonneg-int-mod-is-mod` — `acl2::nonneg-int-mod` on `natp/posp`
  equals plain `mod`.
- `nfix-when-natp`, `nonneg-int-gcd-of-0-{left,right}` — trivial
  rewrites so `nonneg-int-gcd` on `u32p` inputs exposes its
  recursive step to match our rewriter chain.

## 3. Key lessons learned

These are the non-obvious things that cost the most time. When proving
the next function, check these first.

### 3.1 Keep state constructors folded across rewrites

After proving `run-plus-at-loop-entry`, the main induction's step case
*did not fire it*. Reason: ACL2 had unfolded `make-loop-entry-state`
on both sides earlier, so the LHS pattern no longer matched.

**Fix:** disable `make-loop-entry-state` (and anything similar like
`make-gcd-state`) in the outer proof's `:in-theory`. The low-level
symbolic-execution lemmas already contain the expansion, and all the
gluing lemmas consume their inputs as pattern-matched calls.

> Rule of thumb: anything you've established as a pattern in a
> rewrite-rule LHS must stay folded in downstream proofs.

### 3.2 Induction scheme variable must match the step lemma

`gcd-loop-fuel` has two arguments `(a b)`, but `loop-entry-step-case`
rewrites `(make-loop-entry-state a b tmp)` to
`(make-loop-entry-state b (mod a b) b)` — note the `b` in the `tmp`
position on the RHS. If you induct via `(:induction gcd-loop-fuel)`,
the IH has a *free* `tmp` that doesn't match `b`, and ACL2 fails.

**Fix:** hand-write a parallel scheme `gcd-loop-ind a b tmp` whose
recursive call is `(gcd-loop-ind b (mod a b) b)` — with the right
`tmp` substitution — and use `:induct` with it. Also disable
`(:induction gcd-loop-fuel)` so ACL2 doesn't pick the wrong scheme.

### 3.3 `run-split` needs `statep`

Without `statep (run m s)`, you can't cancel `run` over addition,
because `run` returns `:trap` / `(:done ...)` on bad inputs and those
aren't further reducible. The cleanest form of the lemma takes
`statep` as a hypothesis (not a prove-by-case split), and you
discharge it with a `statep-of-make-*` lemma per state-builder.

Those `statep-of-*` lemmas are one-liners once you `:in-theory`
enable every component predicate. There are about eight of them; copy
the list from `statep-of-make-loop-entry-state`.

### 3.4 Force-rounds are a trap, disable them aggressively

When a rewrite rule is nearly firing but hanging on a forced
hypothesis, ACL2 splits into a forcing round that rederives something
you already proved. This showed up repeatedly with `u32p` and
`statep` hypotheses. The defensive pattern:

```lisp
:do-not '(generalize fertilize eliminate-destructors)
:do-not-induct t
```

combined with explicit `:use` of the supporting lemmas and
`(e/d (u32p) (...disables...))` to trim the theory.

### 3.5 Build one rewrite rule per induction step

Temptation: pile everything into the main theorem hint with one giant
`:use` list. This turns the prover's search space exponential.

**Better:** manufacture *one* conditional rewrite rule
(`run-plus-at-loop-entry`) that encapsulates "one iteration of the
loop = 13 extra fuel", prove it once with all the plumbing, then the
induction step case becomes a one-shot application.

### 3.6 `arithmetic-5/top` is heavyweight — keep it local

It rearranges everything and can destabilize symbolic-execution
proofs. `(local (include-book "arithmetic-5/top" :dir :system))` right
before the lemmas that need it, so it doesn't leak into Layer A or
into consumers of this book.

## 4. Recipe for proving another WASM function

Estimated effort scales with **loop depth** of the function, not raw
instruction count. Straight-line code is easy; nested loops need
nested inductions with one `run-plus-at-loop-entry`-style rewrite per
loop.

### Step 0 — Identify the spec
Find a community-book function that defines the same mathematical
behavior. `arithmetic/mod-gcd`, `kestrel/bv/*`, `ihs/*`,
`centaur/bitops/*` are fertile ground. Prefer *defund* specs that
already have rewrite rules.

### Step 1 — Mirror the program as `*foo-body*` defconst
Copy the WASM body from the test file verbatim, as a quoted list.

### Step 2 — Build `make-foo-state args`
A single-frame state with locals, `:instrs *foo-body*`, empty
operand stack, no labels.

### Step 3 — Straight-line prefix lemma
`(equal (run K (make-foo-state args)) (make-loop-entry-state args 0))`
— K is however many steps get you to the first loop header. Use the
boilerplate hint from §2 Layer A.

### Step 4 — Per-loop lemmas
For each loop in the function:
- Define `make-loopN-entry-state` with *all* locals that can change
  during the loop as parameters (don't hardcode initial values like
  `tmp = 0`).
- Prove the iteration lemma: `run K_N (loopN-entry args) = loopN-entry
  args'` where `args'` expresses the one-iteration transition.
- Prove the exit lemma: on the loop's exit condition, `run K_exit`
  leaves the right value on the stack.

### Step 5 — `statep` lemma
One `statep-of-make-loopN-entry-state` per state shape. Boilerplate
theory hint.

### Step 6 — `run-split-when-statep`
You can likely reuse this from `proof-gcd-spec.lisp` verbatim —
lift it to a shared lemma book if you're doing multiple functions.
(It does not depend on the function under analysis.)

### Step 7 — Fuel + induction scheme
- Fuel function `foo-fuel args`: measure = the loop's decreasing
  quantity, body mirrors the recursion.
- Induction scheme `foo-ind args tmps`: same recursive shape, but
  pass through the `tmps` so they substitute correctly in the IH.
  **Test: write out the IH by hand; it must literally match the RHS
  of your iteration lemma, modulo variable renaming.**

### Step 8 — Iteration rewrite rule
`run-plus-at-loopN-entry`: `(run (+ K_N n) (loopN-entry args)) = (run
n (loopN-entry args'))`. Hints: `:use` the iteration lemma +
`run-split-when-statep` + two instances of the `statep` lemma (for
*both* the entry and post-iteration states) + any arithmetic bridge
lemmas. `:in-theory` disable the iteration lemma, `run-split`, the
`statep` lemma, `(:definition run)`, and the state-builder.

### Step 9 — Main loop theorem
`:induct` with your hand scheme, disable the symbolic-execution
lemmas and `(:induction foo-fuel)` and the state-builder, `:expand`
the spec function, and give an explicit `("Subgoal *1/1" :use
((:instance foo-exit-case ...)))` hint.

### Step 10 — Final theorem
One-shot: `:use` the prefix lemma + `run-split-when-statep` + the
main loop theorem, `:in-theory` disable everything.

## 5. Things to reuse across proofs

These are candidates for a shared `proofs/wasm-proof-utils.lisp`:

- `run-split-when-statep` (+ `run-ind`, `not-statep-of-done`,
  `not-statep-of-trap`).
- `nfix-when-natp`.
- `*gcd-exec-theory*` renamed to `*wasm-exec-theory*` — it's
  function-independent.

Candidates for a shared arithmetic bridge book:
- `u32p-of-mod`, `bvmod-32-when-u32`,
  `nonneg-int-mod-is-mod`, `nonneg-int-gcd-of-0-{left,right}`.

## 6. What *not* to do

- Don't `:cases` across `(zp b)` at the top level of the main
  theorem. Use the induction scheme instead.
- Don't enable `arithmetic-5/top` globally — it fights
  `execution.lisp`'s symbolic interpreter.
- Don't leave state-builders enabled in the outer proof. Every
  rewrite you build assumes they're folded.
- Don't rely on `(:induction foo-fuel)` firing with the right
  substitutions — the scheme ACL2 derives from a fuel function
  usually has the wrong `tmp` handling for WASM locals. Write the
  scheme by hand.
- Don't pile everything into one giant theorem. The four-layer
  structure (concrete / plumbing / induction / arithmetic) keeps
  each proof small and diagnosable.

## 7. Open opportunities

- Factor out `run-split-when-statep` and the `*wasm-exec-theory*`
  into a shared utility book so the next function starts with ~100
  lines fewer.
- A macro `def-wasm-symbolic-lemma` that wraps the Layer A
  boilerplate would remove a lot of copy-paste.
- A macro `def-wasm-loop-correct` that, given the loop body, iteration
  count, transition function, and spec, emits the state-builder,
  statep lemma, iteration lemma, rewrite rule, induction scheme, and
  main theorem in one form. This is how the kestrel loop-invariant
  books work and would scale much better than the hand-rolled style
  here.

---

## 8. gcd-v2: shared utility books + parameterized state builders

After landing the §1 result we refactored `proof-gcd-spec.lisp` to
enable reuse across functions and to lift the theorem to start from
`*gcd-func*` under the WASM `(:call 0)` calling convention.

### 8.1 Shared utility books

Two function-independent books were extracted:

- [proofs/wasm-run-utils.lisp](proofs/wasm-run-utils.lisp):
  `*wasm-exec-theory*` (the "enable the interpreter" theory),
  `not-statep-of-done`, `not-statep-of-trap`, `run-ind`, and the
  pivotal `run-split-when-statep`.
- [proofs/wasm-arith-utils.lisp](proofs/wasm-arith-utils.lisp):
  `u32p-of-mod`, `bvmod-32-when-u32`, `nfix-when-natp`,
  `nonneg-int-mod-is-mod`, `nonneg-int-gcd-of-0-{left,right}`.

Neither book depends on `gcd` specifics; both certify standalone and
are `include-book`ed by `proof-gcd-spec`.

### 8.2 Parameterized state builders

The original `make-gcd-state` / `make-loop-entry-state` hardcoded
`:call-stack (list ...)` with empty caller tail and a fixed
`*gcd-store*`. To make the body-level result composable with a
calling convention that pushes a caller frame underneath, the
builders now take two extra parameters:

```lisp
(defun make-gcd-state (a b call-tail store) ...)
(defun make-loop-entry-state (a b tmp call-tail store) ...)
```

where `call-tail` is a `call-stackp` to sit beneath the active frame
and `store` is any `storep`. All Layer A lemmas, the iteration
rewrite `run-plus-at-loop-entry`, the induction `gcd-loop-ind`, and
the main body theorem `gcd-loop-entry-correct` carry these parameters
through unchanged. Consequence: `gcd-impl-correct` is proved once,
for arbitrary `call-tail` / `store`, so a caller's frame is already
"underneath" when we want to lift.

Trick: lemmas stating `statep`, return-arity, and store preservation
of the body-run are now free polymorphic facts — ACL2 doesn't have
to reprove them at the lift layer.

### 8.3 Lift to `*gcd-func*` and the `(:call 0)` entry state

Goal: prove a theorem about `*gcd-func*` invoked via the standard
calling convention, not about an already-set-up frame. The final
result (UNCOMMITTED at the time this note was written):

```lisp
(defthm gcd-func-correct
  (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
           (equal (run (gcd-func-total-fuel a b)
                       (make-gcd-call-state a b))
                  `(:done ,(make-state
                            :store *gcd-store*
                            :call-stack (list (gcd-caller-frame-final a b))
                            :memory nil :globals nil)))))

(defthm gcd-func-correct-result
  (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
           (equal (gcd-done-result
                   (run (gcd-func-total-fuel a b)
                        (make-gcd-call-state a b)))
                  (make-i32-val (acl2::nonneg-int-gcd a b)))))
```

`make-gcd-call-state` is a one-frame state whose instrs are `(:call 0)`
and whose operand stack is `(make-i32-val b) (make-i32-val a)` —
exactly the shape used in `tests/test-spot-check.lisp`.
`gcd-done-result` matches that test file's `get-result` extractor.

### 8.4 The 4-step lift trace

The full run splits into four symbolic steps glued by
`run-split-when-statep`:

```
 S0                 S1                  S2                S3              S4
 call-state ─1→ body-start-state ─N→ body-end-state ─1→ after-return ─1→ :done
 (:call 0)      (execute-call         (gcd-total-fuel   (return-from-    (run-1-from-
  pending)       advances            steps of body)     function)         after-return)
                 instrs)                                 fires)

 total fuel = 1 + gcd-total-fuel a b + 2 = gcd-func-total-fuel a b
```

Named lemmas for each edge:

| Edge | Lemma | Proof technique |
|---|---|---|
| S0→S1 | `gcd-func-call-enters-body` | `:expand (run 1 …)`, enable `execute-instr`, `execute-call`, frame/store accessors |
| S1→S2 | `gcd-impl-correct-state` | reuse body-level theorem with `call-tail = (list (gcd-caller-frame-popped))`, `store = *gcd-store*` |
| S2→S3 | `return-from-body-end` | `:use body-end-call-stack-structure` (structural facts about S2), enable `return-from-function`, `push-vals`, `top-n-operands`, `push-operand`, `pop-operand` |
| S3→S4 | `run-1-from-after-return` | single `:expand (run 1 …)`, enable `current-instrs`/`current-label-stack` so step sees instrs=nil and label-stack=nil, falls through to `return-from-function` on single-frame stack → `(:done ...)` |
| glue  | `gcd-func-correct` | `:use` all four edges + `statep-after-body` + two instances of `run-split-when-statep`, enable only the fuel-arithmetic definitions, disable `(:definition run)` |

### 8.5 The preservation pattern (**important**)

Making S1→S2 usable at the S2→S3 step required proving — by
induction — that the body run preserves *every projection of the
state that S2→S3's single step reads*. The original body-level
theorem only stated one invariant (top-of-operand-stack equals
`nonneg-int-gcd`). `return-from-function` also reads:

1. `(cdr call-stack)` — must equal `call-tail`
2. `(frame->return-arity (car call-stack))` — must be 1
3. `(state->store)` — must equal `store`
4. `(consp call-stack)` — must be non-empty
5. `(consp (frame->operand-stack (car call-stack)))` — non-empty to take top
6. `(<= 1 (operand-stack-height …))` — for `top-n-operands 1` guard
7. `(frame->instrs (car call-stack))` — must be nil (no pending body instr)
8. `(frame->label-stack (car call-stack))` — must be nil (no pending label)
9. `(state->memory) = nil`, `(state->globals) = nil`, `(state->table) = nil`

All nine are proved by a **single** parallel induction
`gcd-loop-entry-preservation` over `gcd-loop-ind a b tmp`. The base
case `(b = 0)` follows from symbolic execution of the final 4 steps
(`loop-entry-base-case-preservation`). The step case uses the already
proved iteration rewrite `run-plus-at-loop-entry` to reduce to the IH.

Do not try to derive these properties *after* the main theorem via
`:use body-end-call-stack-structure`; ACL2 will fail to connect
symbolic structural facts to `consp`/`len` on the operand stack
without the inductive invariant. Add them as conjuncts of the
preservation lemma up front.

The parallel `gcd-impl-correct-state` then asserts all nine (plus
top-of-operand-stack), one-shot `:use` of the preservation lemma.
`body-end-call-stack-structure` re-exports the same set at the
`gcd-body-end-state` alias.

### 8.6 Lessons specific to lifting

Adds to §3:

**8.6.a — Preservation-by-induction > force-plus-hint.**
When the prover can't close a shape conjunct at the lift boundary
(e.g. `(consp ostack)`, `(= memory nil)`), the right move is to add
it as a conjunct of the *body-level* preservation lemma. It costs
nothing at the base case (symbolic execution proves it trivially)
and the step case reuses the existing rewrite. Piling the missing
fact into a `:use`/`:in-theory` hint at the lift layer wastes time
and often doesn't work.

**8.6.b — The 3 "one-step" lemmas each need their own theory.**
S0→S1, S2→S3, S3→S4 are all "one step of `run`", but the step that
fires is different each time (`step` → `execute-instr` →
`execute-call` for S0→S1; `return-from-function` on a non-final frame
for S2→S3; `return-from-function` on the sole frame for S3→S4). Each
lemma therefore enables a different subset of interpreter helpers.
Trying to prove them with a unified theory causes tens of subgoals.

**8.6.c — `make-i32-val` is a macro; `top-n-operands` and `push-vals`
must be :expanded**. In the S2→S3 proof, `top-n-operands 1` and
`push-vals (cons v nil)` both need unfolding with free-variable
`:expand` hints — ACL2 doesn't reduce them via `:in-theory (enable …)`
because the arguments are symbolic. Pattern:

```lisp
:expand ((:free (stack)     (top-n-operands 1 stack nil))
         (:free (stack acc) (top-n-operands 0 stack acc))
         (:free (v rest stack) (push-vals (cons v rest) stack))
         (:free (stack)     (push-vals nil stack)))
```

**8.6.d — `framep`/`statep` of concrete frames need `valp`.**
`framep` ⇒ `operand-stackp` ⇒ `val-listp` ⇒ `valp` (a `defund`).
When proving `framep-of-gcd-caller-frame-final` where the stack is
`(list (make-i32-val (nonneg-int-gcd a b)))`, you must enable `valp`
— not just `i32-valp`. `valp` is disjunctive and its body is hidden
behind the `defund`.

**8.6.e — `not-equal-done-car-when-statep`**. The lift step S3→S4
asks ACL2 to rule out the `(:done …)` branch of the previous step's
return value. Helper:

```lisp
(defthm not-equal-done-car-when-statep
  (implies (statep x) (not (equal :done (car x))))
  :hints (("Goal" :use ((:instance not-statep-of-done (x (cdr x))))
                  :in-theory (disable not-statep-of-done))))
```

paired with a `statep-of-return-from-body-end` lemma, lets the
`run 2` unfolding avoid case-splitting on the returned tag.

### 8.7 Re-runnable iteration recipe (v2)

Amends §4's recipe for functions invoked via `(:call idx)`:

1. Do everything in §4 with **parameterized** builders
   `make-foo-state args call-tail store` and its loop-entry cousin.
   Prove the body-level result for arbitrary `call-tail`/`store`.
2. In a separate section, define `*foo-func*`, `*foo-store* = (list
   *foo-func*)`, `make-foo-call-state args` (caller frame with
   `:instrs '((:call idx))` and WASM-order operand stack), and
   `make-foo-caller-frame-popped` / `-final` (the "empty-instrs after
   the call" shapes).
3. Prove the four edge lemmas S0→S1..S3→S4. Each is 10–30 lines;
   boilerplate the hints from §8.4.
4. Strengthen the body-level preservation lemma with **every
   projection** of the state that your S2→S3 step reads. Re-certify.
5. Compose with `run-split-when-statep` in `foo-func-correct`; extract
   via `foo-done-result` for the user-facing corollary.

This pattern should now cost ~1 hr per additional function body
once the preservation-conjunct set and state-builder generalization
tricks are internalized.

## 9. Fuel-free partial-correctness wrapper

The body-level and lift theorems both state fuel explicitly
(`gcd-total-fuel`, `gcd-func-total-fuel`). For a user-facing result
this is noisy; `defun-sk` packages the existential once:

```lisp
(defun-sk gcd-halts-with (a b v)
  (exists fuel
    (and (natp fuel)
         (equal (run fuel (make-gcd-call-state a b))
                `(:done ,(make-state
                          :store *gcd-store*
                          :call-stack (list (gcd-caller-frame-final a b))
                          :memory nil :globals nil)))
         (equal v (make-i32-val (acl2::nonneg-int-gcd a b))))))

(defthm gcd-func-halts
  (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
           (gcd-halts-with a b (make-i32-val (acl2::nonneg-int-gcd a b))))
  :hints (("Goal"
           :use ((:instance gcd-halts-with-suff
                            (fuel (gcd-func-total-fuel a b)) ...)
                 (:instance gcd-func-correct ...)))))
```

Key move: `defun-sk` auto-generates a `-suff` rule of the shape "if
you can exhibit a witness for `fuel`, the existential holds". Since
`gcd-func-correct` is already a witness instance, a single `:use`
closes the goal. No new work; the wrapper is pure packaging.

The pattern generalizes trivially: for any function `foo` with
`foo-func-correct` at fuel `foo-func-total-fuel`, the companion
`defun-sk foo-halts-with` + `foo-func-halts` is ~15 boilerplate lines.

## Appendix A — Refactor: factor Tier-C into a reusable encapsulate

As of the `gcd-v3` branch (commits `0f9fb8b`, `5158331`), the roughly
550 lines of hand-rolled state-gluing that used to live between
`gcd-impl-correct-state` and `gcd-func-correct` have been replaced by a
single functional instantiation of a generic theorem exported by
[proofs/wasm-call-wrap.lisp](wasm-call-wrap.lisp).

### A.1 What `wasm-call-wrap` provides

An `encapsulate` parameterized over six abstract signatures:

| Signature | Role |
|---|---|
| `(the-func)` | The `funcinst` being called |
| `(input-ok a b)` | Guard on the two argument values |
| `(spec-val a b)` | The `i32-val` the callee leaves on top |
| `(make-call-frame a b)` | Caller frame with args pushed + `(:call 0)` |
| `(make-body-state a b)` | State after the entry step (callee frame on top) |
| `(body-fuel a b)` | Steps required to run the body to `instrs=nil`, `labels=nil` |

Seven constraint theorems the client must discharge (shapes only,
abbreviated): `funcinstp` of the func; `input-ok` implies two `u32p`s
(forward-chaining); `i32-valp` of the spec value; `natp` of the fuel;
`(run 1 <call-state>) = <body-state>`; `statep` of the body-state;
and a 13-conjunct "body-shape-after-fuel" lemma covering every
projection the return path reads.

Given those, the book exports a single theorem, [`call-to-done`](wasm-call-wrap.lisp):

```lisp
(defthm call-to-done
  (implies (and (input-ok a b) (framep (make-call-frame a b)))
           (equal (run (+ 3 (body-fuel a b))
                       (make-state :store (list (the-func))
                                   :call-stack (list (make-call-frame a b))
                                   :memory nil :globals nil))
                  `(:done ,(make-state
                            :store (list (the-func))
                            :call-stack (list (make-frame
                                               :return-arity 1
                                               :locals nil
                                               :operand-stack (list (spec-val a b))
                                               :instrs nil
                                               :label-stack nil))
                            :memory nil :globals nil)))))
```

The statement uses literal `make-state` / `make-frame` forms (not
witness defuns) so that every symbol it mentions is either a macro or
a constrained abstract name — which is the condition that makes
`:functional-instance` substitute cleanly.

### A.2 What §4 of `proof-gcd-spec.lisp` now looks like

1. **Six concrete witness defuns** — `gcd-the-func`, `gcd-input-ok`,
   `gcd-spec-val`, `gcd-body-state`, `gcd-body-fuel-fn` (plus reusing
   `make-gcd-caller-frame`).
2. **Seven local constraint-discharge lemmas**, each `gcd-*`, each
   stated with the witness calls in *closed symbolic form* (i.e. with
   `(gcd-body-state a b)` rather than its expansion) so that the
   rewrites match what `:functional-instance` emits as subgoals.
3. **`gcd-func-correct-raw`** (local) — the single `:functional-instance`
   step, stated with the witnesses substituted literally.
4. **`gcd-func-correct`** (exported) — unfolds the witnesses to the
   user-facing shape with `(make-gcd-call-state a b)` and
   `(acl2::nonneg-int-gcd a b)`.

Net effect: ~330 lines removed from `proof-gcd-spec.lisp`, and the
entire `:call → body → return → :done` glue is now proved once, in
the wrap book, for any future function.

### A.3 Recipe to reuse `wasm-call-wrap` for another function `foo`

Pre-requisite: you already have `foo-impl-correct-state` of the shape
"after `(foo-total-fuel a b)` steps from `(make-foo-state a b
call-tail store)`, the callee has `instrs=nil`, `labels=nil`, top
operand = spec value, and the ten state-projection conjuncts hold".

Then:

1. Prove `foo-func-call-enters-body`: one step of `:call` from the
   `make-foo-call-state a b` matches `make-foo-state a b (list
   (wrap-popped-frame)) <store>`. (The non-local helper
   `wrap-popped-frame` exported by `wasm-call-wrap` is exactly the
   post-pop caller frame with `instrs = '((:call 0))` and empty
   operand stack.)
2. Add `(include-book "wasm-call-wrap")`.
3. Write the six concrete witnesses. Keep them thin — `foo-the-func`
   returns the `defconst`; `foo-body-state` is just `make-foo-state`
   with `call-tail = (list (wrap-popped-frame))` and `store = *foo-store*`;
   `foo-body-fuel-fn` wraps `foo-total-fuel`.
4. Discharge the seven constraint lemmas as `local defthm`s. The
   hardest (13-conjunct shape) is a direct specialization of
   `foo-impl-correct-state`.
5. State `foo-func-correct-raw` as a `local defthm` using

   ```lisp
   :hints (("Goal"
            :use ((:functional-instance
                   call-to-done
                   (the-func   foo-the-func)
                   (input-ok   foo-input-ok)
                   (spec-val   foo-spec-val)
                   (make-call-frame foo-make-call-frame)
                   (make-body-state foo-body-state)
                   (body-fuel  foo-body-fuel-fn)))
            :in-theory (e/d ()
                            (foo-body-state foo-body-fuel-fn
                             foo-input-ok  foo-spec-val
                             foo-the-func  (:executable-counterpart foo-the-func)
                             wrap-popped-frame wrap-final-frame
                             foo-make-call-frame foo-make-body-state
                             current-label-stack current-instrs
                             current-operand-stack current-frame
                             top-frame))))
   ```
6. Write `foo-func-correct` that unfolds the witnesses back to the
   user-facing form.
7. The `defun-sk foo-halts-with` wrapper is boilerplate as before.

### A.4 Gotchas discovered in the refactor

These are not obvious from the ACL2 manual and cost many iterations:

* **`defaggregate` constructors are macros.** `make-state`,
  `make-frame`, and `make-funcinst` cannot appear in `:in-theory`
  lists — doing so causes a hard error at certify time. Disable the
  underlying wrapper `defun`s (e.g. `make-gcd-state`,
  `make-gcd-caller-frame`) instead.

* **Executable-counterpart of a nullary witness.** If your witness is
  `(defun foo-the-func () *foo-func*)`, ACL2 will happily reduce
  `(foo-the-func)` to the quoted value via its executable counterpart
  during the `:functional-instance` constraint subgoals, which
  prevents your `foo-the-func`-based rewrite rules from firing. You
  must add `(:executable-counterpart foo-the-func)` to the disable
  list — not just `foo-the-func` itself.

* **State a `call-to-done`-style exported theorem with literal
  constructors.** If the statement of the exported theorem calls
  non-local helper defuns that wrap `make-state` / `make-frame`
  (e.g. a `wrap-call-state` defun), then a client's
  `:functional-instance` cannot substitute away the `wrap-*` names and
  the generated constraints won't match the client's witnesses. Keep
  the public statement at the level of `make-state` / `make-frame`
  calls applied to abstract signature invocations.

* **Keep constraint-discharge lemmas in closed symbolic form.** The
  LHS of each `gcd-*` rewrite must be stated in terms of the witness
  calls (`(gcd-body-state a b)`, `(gcd-body-fuel-fn a b)`), not their
  `make-gcd-state` / `gcd-total-fuel` expansions — otherwise the
  expansion happens once, the rewrite rules stop matching, and the
  `:functional-instance` subgoal sits there unsimplified.

* **Helper defuns on the call-stack projection are enabled by default.**
  `current-label-stack`, `current-operand-stack`, `current-frame` are
  ordinary `defun`s (not `defund`). They will unfold across the
  `run`-result in subgoals and block rewriting by the shape lemma.
  Disable them explicitly in the raw instantiation's `:in-theory`.
  (`current-instrs`, `top-frame`, `top-operand`,
  `operand-stack-height` are already `defund` — still worth disabling
  for belt-and-braces.)

* **Non-local witness helpers only.** Any symbol appearing in the
  exported `call-to-done` statement must be defined outside the
  `encapsulate`. In `wasm-call-wrap` this is why `wrap-popped-frame`
  is a top-level `defun` rather than a local one — the exported
  theorem's post-state mentions it.



## Appendix B — proof-gcd-measure: measure-based termination via functional instantiation

Companion book [proofs/proof-gcd-measure.lisp](proof-gcd-measure.lisp)
re-proves GCD termination by functionally instantiating the abstract
framework in [proofs/wasm-measure-semantics.lisp](wasm-measure-semantics.lisp),
rather than computing an explicit fuel function. Final exported
theorem:

```lisp
(defthm gcd-run-reaches-terminal
  (implies (gcd-reachable s)
           (and (natp (gcd-run-to-terminal-fuel s))
                (terminalp (run (gcd-run-to-terminal-fuel s) s)))))
```

### B.1 Witnesses

| Abstract signature | GCD witness |
|---|---|
| `reachable`            | `gcd-reachable` (defun-sk over 3-elt u32 list) |
| `mstep`                | `gcd-mstep` = `(run (gcd-mstep-count s) s)` |
| `mstep-count`          | 13 if `b≠0`, 6 if `b=0`, else 0 |
| `state-measure`        | `(nfix (+ 1 (gcd-b s)))` |
| `run-to-terminal-fuel` | `gcd-run-to-terminal-fuel` (see B.3) |

### B.2 The `syntaxp` rule-ordering pattern

Two rewrite rules target `gcd-meas-b` (a structural extractor of the
`b` local):

1. **Structural** on a known constructor:
   `(gcd-meas-b (make-loop-entry-state a b c ct st)) = b`.
2. **General** when `s` is reachable:
   `(gcd-meas-b s) = (gcd-b s)` — lets us transport the measure
   decrease through `gcd-measure-decreases`'s step hypothesis.

If the general rule fires on `(make-loop-entry-state ...)` it
collapses the LHS to opaque `(gcd-b ...)` before the structural rule
gets a chance. Fix: guard the general rule with

```lisp
(syntaxp (not (and (consp s) (eq (car s) 'make-loop-entry-state))))
```

General pattern: when two rules on the same function compete and you
want the structural rule to win on known constructors, add a
`syntaxp` hypothesis to the general rule that blocks it when the
argument is that constructor.

### B.3 Functional instantiation of a recursive witness

The abstract framework's `run-to-terminal-fuel` is an ordinary
`defun` (outside the encapsulate) whose body calls the constrained
symbols `reachable`, `terminalp`, `mstep`, and `mstep-count`. If you
`:functional-instance` `run-reaches-terminal-from-reachable`
substituting only those four, ACL2 emits an unprovable constraint:

```
Subgoal 5.2
(IMPLIES (GCD-REACHABLE S)
         (EQUAL (RUN-TO-TERMINAL-FUEL S)
                (+ (GCD-MSTEP-COUNT S)
                   (RUN-TO-TERMINAL-FUEL (GCD-MSTEP S)))))
```

— i.e. ACL2 insists that the *abstract* `run-to-terminal-fuel`
satisfies its defining recursion equation on the *concrete*
witnesses, which it doesn't.

**Fix:** introduce a concrete counterpart

```lisp
(defun gcd-run-to-terminal-fuel (s)
  (declare (xargs :measure (gcd-state-measure s)
                  :well-founded-relation o<
                  :verify-guards nil
                  :hints (("Goal"
                           :use ((:instance gcd-measure-decreases))
                           :in-theory (e/d (gcd-state-measure)
                                           (gcd-measure-decreases))))))
  (cond ((not (gcd-reachable s)) 0)
        ((terminalp s) 0)
        (t (+ (gcd-mstep-count s)
              (gcd-run-to-terminal-fuel (gcd-mstep s))))))
```

and add `(run-to-terminal-fuel gcd-run-to-terminal-fuel)` to the
`:functional-instance` substitution. The termination hint `:use
gcd-measure-decreases` is the key: it's the framework's
measure-decrease obligation, which you've already discharged.

### B.4 Stable-under-simplificationp computed hint

Five constraint subgoals remain after substitution, each needing a
different combination of the `:rule-classes nil` bridge lemmas
(`gcd-mstep-is-run`, `gcd-mstep-statep-or-terminalp`,
`gcd-measure-decreases`, `gcd-reachable-preserved`), the `:expand`
of `gcd-run-to-terminal-fuel`, and an `enable` of
`gcd-mstep-count`. Rather than enumerate per-subgoal hints (which
break when ACL2's subgoal numbering shifts), supply a single
stable-under-simplificationp hint that fires everywhere simplification
stalls:

```lisp
:hints (("Goal"
         :use ((:functional-instance
                run-reaches-terminal-from-reachable
                (mstep                gcd-mstep)
                (mstep-count          gcd-mstep-count)
                (reachable            gcd-reachable)
                (state-measure        gcd-state-measure)
                (run-to-terminal-fuel gcd-run-to-terminal-fuel)))
         :in-theory (disable run-reaches-terminal-from-reachable))
        (and stable-under-simplificationp
             '(:use ((:instance gcd-mstep-is-run)
                     (:instance gcd-mstep-statep-or-terminalp)
                     (:instance gcd-measure-decreases)
                     (:instance gcd-reachable-preserved))
               :expand ((gcd-run-to-terminal-fuel s))
               :in-theory (enable gcd-mstep-count))))
```

### B.5 Recipe for another function `foo`

1. Define `foo-reachable` (a `defun-sk` over a witness list),
   accessor defuns for each local component (`foo-a`, `foo-b`, ...),
   a `foo-reachable-canonical :rule-classes nil` lemma, and
   `statep-when-foo-reachable` as `:forward-chaining`.
2. Define `foo-mstep-count` (piecewise natural), `foo-mstep = (run
   (foo-mstep-count s) s)`, and `foo-mstep-is-run :rule-classes nil`.
3. Define `foo-state-measure` to be a natural ordinal that strictly
   decreases across `foo-mstep`. For a loop with counter `b`, use
   `(nfix (+ 1 (foo-b s)))`.
4. Discharge the framework constraints as `defthm`s:
   `foo-mstep-statep-or-terminalp :rule-classes nil`,
   `foo-measure-decreases`, `foo-reachable-preserved`,
   `foo-mstep-count-positive :linear`, `o-p-of-foo-state-measure`.
5. Define the concrete `foo-run-to-terminal-fuel` per B.3.
6. State `foo-run-reaches-terminal` via `:functional-instance` of
   `run-reaches-terminal-from-reachable` with all five witnesses,
   dispatching leftover subgoals with the B.4 computed hint.

### B.6 Prerequisites to have in hand

- A low-level "N steps from constructor shape land on next
  constructor shape" lemma per transition (§2 of this note's Layer A
  applies unchanged); `proof-gcd-measure` uses `loop-entry-step-case`
  from `proof-gcd-spec` for the `b≠0` case and proves
  `loop-entry-exit-6` for `b=0`.
- The abstract framework exports `terminalp`, `run-to-terminal`,
  `run-to-terminal-fuel`, `run-reaches-terminal-from-reachable`,
  plus `natp-of-mstep-count`, `mstep-count-positive`,
  `reachable-preserved-by-mstep`, `measure-decreases-on-mstep`,
  `o-p-of-state-measure`, `mstep-is-run :rule-classes nil`, and
  `mstep-statep-or-terminalp :rule-classes nil`.

## Appendix C — Round 1 factorial proof (validates the recipe)

As a second exercise of the Appendix A recipe (minus the call-wrap lift,
deferred to a later round), [proofs/proof-factorial-spec.lisp](proof-factorial-spec.lisp)
proves the iterative i32 factorial in
[tests/oracle/factorial.wat](../tests/oracle/factorial.wat) correct.

### C.1 What was proved

```lisp
(defthm fac-impl-correct
  (implies (and (unsigned-byte-p 32 n)
                (call-stackp call-tail)
                (storep store))
           (equal (top-operand
                   (current-operand-stack
                    (run (fac-total-fuel n) (make-fac-state n call-tail store))))
                  (make-i32-val (fac-spec n)))))

(defthm fac-impl-correct-bounded
  (implies (and (natp n) (<= n 12)
                (call-stackp call-tail) (storep store))
           (equal (top-operand
                   (current-operand-stack
                    (run (fac-total-fuel n) (make-fac-state n call-tail store))))
                  (make-i32-val (acl2::factorial n)))))
```

The bv spec `fac-spec` is defined via `acl2::bvmult 32`; for `n <= 12`
it coincides with the unbounded `acl2::factorial` from
`arithmetic/factorial`, giving the user-facing mathematical form.

Lines of proof: 433 (vs. 1021 for GCD including §4 call-wrap lift and
§5 `defun-sk`). The GCD call-wrap recipe from Appendix A applies
unchanged to factorial but is deferred to keep Round 1 focused.

### C.2 Symbolic-execution step counts match GCD exactly

| Edge | Steps | GCD | factorial |
|---|---|---|---|
| prefix → loop-entry | 2 vs 4 | `(:block)(:loop)` | `(:i32.const 1)(:local.set 1)(:block)(:loop)` |
| one iteration      | 13  | 12 body instrs + `(:br 0)` re-enters loop | same count — different ops |
| exit (b=0 / n=0)   | 4   | eqz / br_if / to-continuation / `(:local.get 0)` | eqz / br_if / to-continuation / `(:local.get 1)` |

The `run-plus-at-loop-entry` rewrite rule and `gcd-loop-ind` induction
scheme pattern are essentially word-for-word reusable; only the state
builder and the post-iteration arguments (`bvminus 32 n 1`, `bvmult 32
acc n`) differ from `(b, (mod a b), b)`.

### C.3 Small arithmetic bridges added to `wasm-arith-utils.lisp`

```lisp
(defthm bvminus-32-of-u32-and-1
  (implies (and (unsigned-byte-p 32 n) (not (equal n 0)))
           (equal (acl2::bvminus 32 n 1) (- n 1))))
(defthm u32p-of-bvmult-32  (unsigned-byte-p 32 (acl2::bvmult 32 a b)))
(defthm u32p-of-bvminus-32 (unsigned-byte-p 32 (acl2::bvminus 32 a b)))
(defthm bvmult-32-of-1      (implies (u32p a) (equal (bvmult 32 1 a) a)))
(defthm bvmult-32-of-1-left (implies (u32p a) (equal (bvmult 32 a 1) a)))
```

`bvminus-32-of-u32-and-1` is the key lemma for the step-case induction:
it lets the post-iteration state `(make-loop-entry (bvminus 32 n 1) ...)`
match the IH, whose first arg is `(- n 1)` (from the hand-written
`fac-loop-ind`).

### C.4 Bounded corollary: when bv-factorial = mathematical factorial

`(fac-spec n) = (acl2::factorial n)` for `n <= 12` but not in general.
Two small lemmas suffice:

1. `u32p-of-factorial-bounded`: proved by **explicit case split** on
   `n ∈ {0,...,12}`, not induction. The inductive proof fails because
   the natural IH `(factorial(n-1) <= 2^32)` is too weak to conclude
   `n * factorial(n-1) <= 2^32` without also knowing
   `factorial(n-1) <= 39916800 = 11!`. A 13-case split closes it
   immediately via the executable counterpart of `factorial`.
2. `fac-spec-when-small`: induct on `fac-spec`; step case uses
   `u32p-of-factorial-bounded` so that `bvmult 32 n x = n * x`.

### C.5 What this confirms for the cross-implementation plan

- The Appendix A recipe is genuinely reusable across iterative WASM
  loops: changing the transition function, step count per iteration,
  and local layout is straightforward; the induction scheme and
  run-plus rewrite adapt cleanly.
- The 13-step per-iteration count is coincidence between GCD and
  factorial, not a fundamental invariant. It depends on loop body
  length. For `fac-rec` (recursive via `(call $fac)`) or `fac-opt`,
  per-iteration counts and state shape will differ.
- APT `tailrec` was not needed. `fac-loop-entry-correct` closes in
  one induction with the GCD-style hand scheme. Round 2 (proving
  `fac-iter-named` or `fac-opt` against the same spec) will be the
  genuine A/B test for APT's value in this codebase.

---

## Appendix D — Attempt at a WASM loop lifter, and what's missing

**Status: incomplete, not aligned with the Axe model. Both artifacts
(`wasm-loop-lifter.lisp` and `proof-factorial-v2.lisp`) certify, but
the approach does not achieve the compression or workflow of the
Axe example `factorial-elf64.lisp` and should be redone.**

### D.1  What was built

- [wasm-loop-lifter.lisp](wasm-loop-lifter.lisp) — a single `encapsulate`
  declaring 10 abstract witnesses (`ll-input-ok`, `ll-exit?`, `ll-next`,
  `ll-result`, `ll-measure`, `ll-fn`, `ll-total-fuel`, `ll-iter-fuel`,
  `ll-exit-fuel`, `ll-state-at-header`) plus 11 exported constraint
  theorems, and one generic theorem `ll-loop-correct` stating that
  running `ll-total-fuel` steps from `ll-state-at-header` leaves
  `ll-fn(vars)` on top of the operand stack. 279 lines, certifies in
  0.3 s.

- [proof-factorial-v2.lisp](proof-factorial-v2.lisp) — first client:
  factorial via `:functional-instance ll-loop-correct`. 447 lines,
  certifies in 0.6 s.

### D.2  Why this is the wrong shape

Compare to [factorial-elf64.lisp](../../../acl2/books/kestrel/axe/x86/examples/factorial/factorial-elf64.lisp),
which is ~100 lines and has this structure:

```
(lift-subroutine factorial                                 ; (1) lift machine code
                 :target "fact"
                 :executable "factorial.elf64"
                 :loops ((40 . (40 44 26 29 33 36)))       ;     → named loops
                 :measures ((40 (bvchop 32 var12)))
                 :stack-slots 4)

(def factorial-loop-1.2-pre (wrap-output factorial-loop-1 …))
(def factorial-loop-1.2     (simplify factorial-loop-1.2-pre))
(def factorial-loop-1.3     (drop-irrelevant-params factorial-loop-1.2 …))
(def factorial-loop-1.4     (rename-params factorial-loop-1.3 ((var12 n) (var16 acc))))
(def factorial-spec.2       (apt::tailrec factorial-spec …))

(defthm connection-lemma (… (factorial-spec.2 n acc) (factorial-loop-1.4 n acc))
  :hints (("Goal" :induct t :in-theory (enable factorial-spec.2))))

(defthm final (… (factorial n undef) (factorial-spec n)))
```

The Axe pipeline **automatically produces the lifted ACL2 function
from the ELF binary**. The user never writes
`factorial-loop-1`, `make-fac-header`, `fac-iter-step`, or
`fac-exit-step` — all of that is generated. Only the tail-recursive
spec and the one-line induction `connection-lemma` are hand-written.

In v2 we still write, by hand:

1. `*fac-body*` / `*fac-loop-body*` / `*fac-block-label*` /
   `*fac-loop-label*` — the body is _copied out of the .wasm binary
   into the proof source_, duplicating information already present in
   `*fac-func*`.
2. `make-fac-state`, `make-fac-header` — state-shape constructors.
3. `fac-iter-step` (13-step iter lemma) and `fac-exit-step` (4-step
   exit lemma) — program-specific symbolic-execution proofs.
4. `fac-vars-ok`, `fac-exit?`, `fac-next`, `fac-result`, `fac-measure`,
   `fac-loop-fn`, `fac-iter-fuel`, `fac-exit-fuel`, `fac-total-fuel`
   — the "lifted loop function" as a manual ACL2 defun, plus fuel
   accounting.
5. A dozen boilerplate constraint theorems matching the encapsulate's
   exported signature (`natp-of-fac-iter-fuel`, `o-p-of-fac-measure`,
   `fac-vars-ok-of-fac-next`, `statep-of-make-fac-header`, …).
6. The functional-instantiation theorem itself, with a brittle
   `:in-theory (disable …)` hint list.

That is **everything the Axe toolchain does automatically**, written
out by hand in ACL2 syntax. The lifter theorem `ll-loop-correct`
only abstracts step 6's inductive argument; items 1–5 are the bulk
and they remain per-program work.

**Line counts:**

| Artifact                            | Lines | Notes                          |
|------------------------------------ |-------|------------------------------- |
| [proof-factorial-spec.lisp](proof-factorial-spec.lisp) (v1)   | 433   | ad-hoc induction, no lifter   |
| [proof-factorial-v2.lisp](proof-factorial-v2.lisp) (v2)       | 447   | uses lifter                    |
| [wasm-loop-lifter.lisp](wasm-loop-lifter.lisp)                | 279   | generic, one-time cost         |
| Axe `factorial-elf64.lisp`          | ~100  | full pipeline, for comparison  |

v2 is *longer* than v1. The generic machinery moved into
`wasm-loop-lifter.lisp` (~100 lines net), but was replaced on the
user side by ~100 lines of witness defuns + constraint theorems.
Net zero.

### D.3  The one genuine lesson — `:functional-instance` gotcha

The `:functional-instance` hint silently fell back to induction for
a long time. The cause: ACL2's preprocessor rewrites
`storep` → `funcinst-listp`, `current-operand-stack` → the
`frame->operand-stack (top-frame (state->call-stack …))` chain, and
reduces `(fac-iter-fuel)` / `(fac-exit-fuel)` to `13` / `4` via
executable-counterparts, before the exported constraint rules are
matched. This breaks syntactic matching for the non-trivial
constraints (`ll-iter-step`, `ll-exit-step`, `statep-of-…`).

Working incantation:

```lisp
:hints (("Goal"
         :use ((:functional-instance ll-loop-correct
                (ll-input-ok fac-vars-ok) … ))
         :in-theory (disable fac-vars-ok fac-exit? fac-next fac-result
                             fac-measure fac-iter-fuel fac-exit-fuel
                             make-fac-header
                             storep
                             current-operand-stack current-instrs
                             current-label-stack
                             (:executable-counterpart fac-iter-fuel)
                             (:executable-counterpart fac-exit-fuel)))
        ("Goal'"
         :expand ((fac-loop-fn vars) (fac-total-fuel vars))))
```

Diagnosis technique: when `:use (:functional-instance …)` fails,
ACL2 prints `Subgoal N.M` checkpoints under the main goal with
"*** Key checkpoint before reverting to proof by induction: ***".
Subgoal numbering is in **reverse order** of the exported
constraints. Inspect the first unsolved constraint and look for
which accessor / definition was unfolded away from the expected
pattern.

This finding is worth keeping (see
[/memories/repo/wasm-loop-lifter.md](../../../memories/repo/wasm-loop-lifter.md))
regardless of whether we take the encapsulate-witness approach
again.

### D.4  What to do instead if we resume

The Axe `lift-subroutine` macro is ~1000 lines in Axe and relies on
an entire DAG-based symbolic executor. Rebuilding that for WASM is a
major engineering effort. Pragmatic intermediate steps, in
increasing order of ambition:

**Option A — Mechanical extractor, no theorem.** Write a small
function `(wasm-extract-loop-body *fac-func* :offset N :len M)` that
slices the loop body directly from the `funcinst->body` rather than
copying it into the proof source. This removes items (1) and (2) of
the per-program boilerplate but does nothing for (3)–(6). Est. 50-line
reduction, no semantic change.

**Option B — Loop-body symbolic executor.** A tactic that, given a
loop body and a header-state shape, *computes* the iter-step and
exit-step lemmas by symbolic execution of `run`. This is what the
`:expand ((:free (n s) (run n s)))` pattern already does inside a
proof; lifting it into a `defthmd`-generator would eliminate items
(2)–(3). Est. 150–200 line reduction per proof, plus ~500 lines of
one-time tool cost.

**Option C — Full `lift-wasm-loop` macro.** Given
`*fac-func*`, a loop offset, and `:measure`, generate all of
`fac-*` defuns, all 11 constraint theorems, the three
symbolic-execution lemmas, and the functional-instantiation call.
This matches Axe's `lift-subroutine` in scope. Est. 1000+ lines of
tool code; per-proof cost drops to the Axe level (~30 lines: measure
annotation, connection lemma, final theorem).

**Option D — Abandon encapsulate, use Axe's DAG framework.** The
correct structural move is to port Axe's x86 loop lifter to WASM
semantics, reusing its DAG simplifier, `:loops` annotation syntax,
`apt::tailrec`, `apt::drop-irrelevant-params`, etc. This is the
architecture the Axe example proves. It is also the largest
investment.

### D.5  What the v2 artifacts are good for

- **`wasm-loop-lifter.lisp` as-is** still has value as a _target_:
  if we ever build option B or C, the generated per-program
  functional-instance call has somewhere to land.
- **`proof-factorial-v2.lisp`** is a worked example of exactly
  what the tool-generated output would look like. Keep it as a
  reference for shape.
- Neither should be treated as a template to be hand-copied for
  other loops; that would propagate the boilerplate problem.

### D.6  Disposition

- Keep both files certified so the infrastructure is preserved
  (`wasm-loop-lifter.cert`, `proof-factorial-v2.cert`).
- Do **not** retrofit `proof-gcd-spec.lisp` onto the lifter — v1 is
  fine and the lifter doesn't buy us anything at GCD's one-loop size
  either.
- Next real step: decide between Option B (loop-body sym-ex tactic)
  or Option D (port Axe) before writing another per-program proof.
  Until that decision, v1-style ad-hoc proofs remain the cheaper
  path per program.
