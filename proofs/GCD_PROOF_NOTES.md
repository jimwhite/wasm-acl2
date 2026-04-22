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
