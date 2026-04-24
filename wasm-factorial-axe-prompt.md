# Coding Agent Prompt: WASM Factorial Proof (Axe/APT Style)

## Task

You are working on `wasm-acl2`, an ACL2 formal semantics for WebAssembly 1.0. We already have a complete, no-`skip-proofs` end-to-end correctness proof for a WASM GCD function (see `proofs/proof-gcd-spec.lisp` and `GCD_PROOF_NOTES.md` on the `gcd-v2` branch). 

Your task is to produce **two files**:

1. `tests/oracle/factorial.wat` — A WebAssembly text-format factorial function that is a good target for proof.
2. `proofs/proof-factorial-spec.lisp` — An ACL2 correctness proof using the **Axe/APT lift-then-simplify-then-connect** methodology, adapted from the Kestrel x86 factorial example.

---

## The WASM Factorial to Target

Source: Extract fac-iter-named from https://github.com/WebAssembly/spec/blob/main/test/core/fac.wast, isolate it into a standalone WASM module (fac-iter-named.wat), compile with wat2wasm, and disassemble the binary back to canonical WAT with wasm2wat. Work from the resulting .wasm binary. All i32 references in the proof template should be replaced with i64; use u64p / bvmult 64 / bvminus 64 from kestrel/bv/* for the arithmetic bridge.

The other implementations in that module will be future proving targets.

**Why this shape?**

- It is structurally identical to the x86 Axe factorial target (iterative `for(i=n; i>0; i--) acc *= i`).
- It uses the same two-variable accumulator pattern (`$n` counts down, `$acc` accumulates product) as `fact-algorithm` in `books/kestrel/axe/x86/examples/factorial/factorial-elf64.lisp`.
- It has exactly one loop, one branch, and no memory or global access — the simplest possible non-trivial loop proof target after GCD.
- `i32.eqz` on the counter maps directly to the `(equal n 0)` base case of `(defun f (n) (if (zp n) 1 (* n (f (- n 1)))))` in ACL2.

The choice of `i32.eqz` as the loop test (rather than `i32.gt_s`) avoids signed-comparison complications and keeps the arithmetic bridge to `natp` clean.

---

## The Proof Structure to Follow

### Primary Reference: Axe x86 Factorial

File: `books/kestrel/axe/x86/examples/factorial/factorial-elf64.lisp`
GitHub: https://github.com/acl2/acl2/blob/master/books/kestrel/axe/x86/examples/factorial/factorial-elf64.lisp

This file uses the following five-step methodology. **Replicate this structure for WASM:**

**Step 1 — Define the spec (`defund factorial-spec`)**  
A clean, naturally recursive ACL2 definition with a `bvchop`/`unsigned-byte-p` guard for the `tailrec` transformation. Map to:

```lisp
(defund factorial-spec (n)
  (declare (xargs :measure (nfix n)))
  (if (or (not (unsigned-byte-p 32 n))
          (equal n 0))
      1
    (bvmult 32 n (factorial-spec (bvminus 32 n 1)))))
```

The ACL2 community book `arithmetic/factorial` (which defines `(defun fact (n) ...)`) is an alternative spec; however, `bvmult`/`bvminus` from `kestrel/bv/*` already handles 32-bit overflow consistently with WASM `i32.mul`/`i32.sub` semantics, so prefer the BV form as the spec here.

**Step 2 — Load the WASM binary and generate the lifted function**  
Replace `lift-subroutine` (x86-specific) with the `wasm-acl2` equivalent: use `load-wasm-funcinsts` (from `proofs/wasm-loader.lisp`) to parse `factorial.wasm` at certification time, exactly as `proof-gcd-spec.lisp` does with `gcd.wasm`.

**Step 3 — Define the concrete algorithm (`defun fact-algorithm`)**  
Write a tail-recursive ACL2 function that exactly mirrors the WASM loop structure: counter `n` decrements, accumulator `acc` multiplies. This is the bridge between the concrete WASM semantics and the spec.

```lisp
(defun fact-algorithm (n acc)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (not (unsigned-byte-p 32 n)) (not (unsigned-byte-p 32 acc)))
      acc
    (fact-algorithm (n32 (- (n32-to-i32 n) 1))
                    (n32 (* (n32-to-i32 acc) (n32-to-i32 n))))))
```

(Use the `n32`/`n32-to-i32` wrappers already established in `wasm-arith-utils.lisp`, analogous to the x86 example's use of `loghead 32` / `logext 32`.)

**Step 4 — Prove the concrete algorithm equals the spec (APT-style)**  
Use `apt::tailrec` to derive a tail-recursive form of `factorial-spec` (call it `factorial-spec.2`), then prove `(equal (factorial-spec.2 n 1) (fact-algorithm n 1))` by induction. This is the **intention proof** and is entirely independent of the WASM interpreter.

In the x86 example:
- `factorial-spec.2` is produced by `(apt::tailrec factorial-spec ...)`
- `connection-lemma` proves `(equal (factorial-spec.2 n acc) (factorial-loop-1.4 n acc))` for all valid `n`, `acc`

**Step 5 — Prove the WASM implementation equals the concrete algorithm**  
This is the **behavior proof** layer, following the GCD recipe from `GCD_PROOF_NOTES.md`. Use `make-factorial-state`, `make-loop-entry-state`, symbolic-execution lemmas (base case + step case), `run-split-when-statep`, a clock function `factorial-loop-fuel`, and an induction scheme `factorial-loop-ind`.

Then chain Steps 4 and 5 for the final theorem:

```lisp
(defthm factorial-impl-correct
  (implies (and (unsigned-byte-p 32 n)
                (sbvle 32 0 n))
           (equal (top-operand
                   (current-operand-stack
                    (run (factorial-total-fuel n) (make-factorial-state n))))
                  (make-i32-val (factorial-spec n)))))
```

---

## Key Differences from the x86 Axe Example

| Aspect | x86 Axe (`factorial-elf64.lisp`) | WASM (`proof-factorial-spec.lisp`) |
|---|---|---|
| Binary loading | `lift-subroutine` with `:executable` | `load-wasm-funcinsts` with `.wasm` path |
| State type | x86 stobj (`x86p`) | `statep` from `execution.lisp` |
| Machine state accessors | `xr :rgf *rdi*`, `xr :rip` | `current-operand-stack`, `top-operand`, `current-locals` |
| Run function | `x86-run-alt x86 clk` | `(run fuel state)` |
| Clock arithmetic | `binary-clk+` | `(+ m n)` with `run-split-when-statep` |
| Loop termination | `def-semantics` (Codewalker) or hand-edit | Hand-written `factorial-loop-fuel` + `factorial-loop-ind` |
| BV arithmetic | `loghead 32` / `logext 32` | `u32p`, `bvmult-32-when-u32` from `wasm-arith-utils.lisp` |
| APT pipeline | `wrap-output`, `simplify`, `drop-irrelevant-params`, `rename-params`, `tailrec` | `tailrec` on spec; connection by direct induction |

The x86 example uses APT's `drop-irrelevant-params` and `rename-params` because `def-semantics`/`lift-subroutine` produces messy intermediate functions with many machine-state parameters. Your `wasm-acl2` state builders (`make-factorial-state`, `make-loop-entry-state`) are already clean — fewer APT transformation steps are needed.

---

## Files to Study (in order)

### 1. The x86 Axe factorial example (primary template)
- `books/kestrel/axe/x86/examples/factorial/factorial-elf64.lisp`
  https://github.com/acl2/acl2/blob/master/books/kestrel/axe/x86/examples/factorial/factorial-elf64.lisp
- `books/kestrel/axe/x86/examples/factorial/factorial.c` — the C source
  https://github.com/acl2/acl2/blob/master/books/kestrel/axe/x86/examples/factorial/factorial.c

### 2. The existing WASM GCD proof (your primary ACL2 template)
- `proofs/proof-gcd-spec.lisp` (branch: `gcd-v2`)
  https://github.com/jimwhite/wasm-acl2/blob/gcd-v2/proofs/proof-gcd-spec.lisp
- `GCD_PROOF_NOTES.md` — the recipe (§4 and §8.7 are the key sections)
  https://github.com/jimwhite/wasm-acl2/blob/gcd-v2/proofs/GCD_PROOF_NOTES.md

### 3. Supporting WASM utility books
- `proofs/wasm-arith-utils.lisp` — `u32p-of-mod`, `bvmod-32-when-u32`, `n32`/`n32-to-i32` bridges
- `proofs/wasm-run-utils.lisp` — `run-split-when-statep`, `*wasm-exec-theory*`
- `proofs/wasm-loader.lisp` — `load-wasm-funcinsts`

### 4. The M1 template (pedagogical reference for the one-loop methodology)
- `books/models/jvm/m1/template.lisp`
  https://github.com/acl2/acl2/blob/master/books/models/jvm/m1/template.lisp
- `books/models/jvm/m1/fact.lisp` — M1 factorial proof (unbounded integers; compare methodology)
  https://github.com/acl2/acl2/blob/master/books/models/jvm/m1/fact.lisp

### 5. APT toolkit (for the spec-side tailrec transformation)
- `books/kestrel/apt/tailrec.lisp`
  https://github.com/acl2/acl2/blob/master/books/kestrel/apt/tailrec.lisp
- APT documentation: https://www.kestrel.edu/research/apt/
- `books/kestrel/apt/def.lisp` — the `def` macro that orchestrates APT steps

### 6. BV arithmetic (for 32-bit multiplication spec)
- `books/kestrel/bv/rules3.lisp` — `bvchop-of-+-becomes-bvplus` (imported in x86 example)
- `books/kestrel/bv/bvmult.lisp` — `bvmult` definition and key rewrite rules
- `books/kestrel/bv/bvminus.lisp`

---

## Proof Outline for `proof-factorial-spec.lisp`

```
§0. Includes
    - (include-book "../execution")
    - (include-book "wasm-run-utils")      ; run-split-when-statep, *wasm-exec-theory*
    - (include-book "wasm-arith-utils")    ; BV bridges for i32.mul, i32.sub
    - (include-book "wasm-loader")         ; load-wasm-funcinsts
    - (local (include-book "arithmetic-5/top" :dir :system))
    - (include-book "kestrel/bv/rules3" :dir :system)
    - (include-book "kestrel/apt/tailrec" :dir :system)

§1. Load program binary
    - (make-event (load-wasm-funcinsts "...factorial.wasm" state))
    - → defines *factorial-func*, *factorial-body*

§2. Spec
    - (defund factorial-spec (n) ...)    ; naturally recursive, bvmult/bvminus

§3. State builders
    - (defun make-factorial-state (n call-tail store) ...)
    - (defun make-factorial-loop-entry-state (n acc call-tail store) ...)

§4. Layer A — Symbolic execution (concrete step lemmas)
    - factorial-impl-base-case     : run K (make-factorial-state 0 ...) → acc=1
    - factorial-state-to-loop-entry: run 2 (make-factorial-state n ...) → loop-entry n 1
    - loop-entry-step-case         : run K_loop (loop-entry n acc ...) [n≠0] → loop-entry (n-1) (acc*n)
    - loop-entry-base-case         : run K_exit (loop-entry 0 acc ...) → top=acc

§5. Layer B — Plumbing
    - statep-of-make-factorial-state
    - statep-of-make-factorial-loop-entry-state
    - run-plus-at-factorial-loop-entry  ; the one-iteration rewrite rule

§6. Layer C — Induction
    - (defun factorial-loop-fuel (n) ...)
    - (defun factorial-loop-ind (n acc) ...)
    - factorial-loop-entry-correct  ; main induction

§7. Layer D — Arithmetic bridge
    - bvmult-32-commutes-with-n32 (if needed)
    - Connect fact-algorithm ↔ factorial-spec via APT tailrec

§8. Final theorem
    - factorial-impl-correct
    - (defun-sk factorial-halts-with ...) ; fuel-free wrapper (optional)
```

---

## Important Pitfalls (from GCD_PROOF_NOTES.md §3)

1. **Keep `make-factorial-loop-entry-state` folded** in all downstream proofs. Disable it after establishing it as a rewrite-rule LHS pattern (§3.1).
2. **Match the induction scheme's variable to the step lemma**: `factorial-loop-ind` must have an `acc` parameter whose substitution in the recursive call matches the RHS of `loop-entry-step-case`. The correct recursive call is `(factorial-loop-ind (- n 1) (* acc n))` (modulo BV wrappers), not `(factorial-loop-ind (- n 1) acc)`.
3. **`run-split-when-statep` needs `statep`**: Prove `statep-of-make-factorial-loop-entry-state` first.
4. **`arithmetic-5/top` local only**: Keep it in a `(local ...)` so it doesn't leak into symbolic-execution proofs.
5. **BV multiplication overflow**: `i32.mul` wraps at 2^32. The spec must use `bvmult 32` (not `*`) and the connection lemma must constrain `n < 13` (or similar) to avoid overflow if connecting to the unbounded `(defun f (n) ...)`.

---

## Connection to the APT Tailrec Pattern (from the x86 Example)

The key APT step in `factorial-elf64.lisp` is:

```lisp
(def factorial-spec.2
  (apt::tailrec factorial-spec :domain (lambda (x) (unsigned-byte-p 32 x))))
```

This produces a tail-recursive equivalent `factorial-spec.2(n, acc)` such that
`(factorial-spec.2 n 1) = (factorial-spec n)`. Then `connection-lemma` directly
proves `(equal (factorial-spec.2 n acc) (fact-algorithm n acc))` by induction,
using `(enable factorial-spec.2)` in the hint.

For the WASM proof, `tailrec` on `factorial-spec` produces exactly the accumulator
form that `fact-algorithm` implements, so the connection proof is one induction
with `:in-theory (enable factorial-spec.2)` — no extra APT transformations
needed.

---

## Expected Output Theorems

The deliverable proof should establish, at minimum:

```lisp
;; Core correctness: WASM body produces factorial-spec result
(defthm factorial-impl-correct
  (implies (and (unsigned-byte-p 32 n)
                (sbvle 32 0 n))
           (equal (top-operand
                   (current-operand-stack
                    (run (factorial-total-fuel n) (make-factorial-state n))))
                  (make-i32-val (factorial-spec n)))))

;; Fuel-free wrapper (optional but good practice)
(defun-sk factorial-halts-with (n v)
  (exists fuel
    (and (natp fuel)
         (equal (run fuel (make-factorial-state n))
                ...)
         (equal v (make-i32-val (factorial-spec n))))))
```

---

## Reference: x86 Factorial Proof Structure (annotated)

The final five theorems in `factorial-elf64.lisp` that form the correctness chain:

```lisp
;; 1. SEM-16-CORRECT   : CLK-16 steps of running from PC=16 = sem-16 (loop body result)
;; 2. SEM-0-CORRECT    : CLK-0 steps of running from PC=0 = sem-0 (full function result)
;; 3. factorial-loop-result-helper : sem-16 output = fact-algorithm(n, acc) [behavior proof]
;; 4. factorial-program-result-helper : sem-0 output = fact-algorithm(n, 1)
;; 5. factorial-program-result [final] : x86-run-alt output = f(n)  [intention proof via connection]
```

Your WASM proof should have an analogous five-step chain, with `run`+`make-factorial-state` replacing `x86-run-alt`+x86 state setup, and `make-i32-val (factorial-spec n)` replacing `(f (rgfi *rdi* x86))`.

---

## Suggested Makefile / Build

Add `factorial.wasm` to the oracle build:

```makefile
tests/oracle/factorial.wasm: tests/oracle/factorial.wat
    wat2wasm $< -o $@
```

And add `proof-factorial-spec.lisp` to `proofs/cert.acl2` after `proof-gcd-spec.lisp`.
