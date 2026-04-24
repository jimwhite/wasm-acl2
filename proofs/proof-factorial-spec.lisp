;; WASM 1.0 ACL2 — iterative factorial end-to-end correctness (Round 1)
;;
;; The WASM program under test (`tests/oracle/factorial.wat`) is an
;; iterative 32-bit unsigned factorial modeled on `fac-iter-named` from
;; the WebAssembly spec test `test/core/fac.wast`:
;;
;;     acc = 1;
;;     while (n != 0) { acc = acc * n; n = n - 1; }
;;     return acc;
;;
;; This book follows the recipe from `GCD_PROOF_NOTES.md` without using
;; APT (see Round 1 plan). Structure:
;;
;;   §0. Preliminaries & binary load.
;;   §1. Symbolic-execution primitives (Layer A).
;;   §2. Plumbing: statep of loop-entry, run-plus iteration rewrite
;;        (Layer B).
;;   §3. Fuel + hand-written induction scheme + main loop theorem
;;        (Layer C).
;;   §4. Spec connection: bv factorial = mathematical factorial for
;;        n <= 12 (Layer D).
;;   §5. Body-level final theorem.
;;
;; Lift to `*fac-func*` via `(:call 0)` + `call-to-done` is deferred.
;; Keeping the first round focused on a working behavior-proof baseline.

(in-package "WASM")
(include-book "../execution")
(include-book "wasm-run-utils")
(include-book "wasm-arith-utils")
(include-book "wasm-loader")

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §0.  Load the factorial funcinst from the .wasm binary.

(make-event
 (mv-let (erp funcs acl2::state)
   (load-wasm-funcinsts "../tests/oracle/factorial.wasm" acl2::state)
   (if erp
       (mv (msg "Failed to load factorial.wasm: ~x0" erp) nil acl2::state)
     (mv nil
         `(progn
            (defconst *fac-func* ',(first funcs))
            (defconst *fac-body* ',(funcinst->body (first funcs))))
         acl2::state))))

;; Initial state of the function body: locals = (n, 0), operand stack
;; empty, instrs = *fac-body*.  The `call-tail` / `store` are plumbed
;; through generically (GCD §8.2 pattern) so the result lifts later.

(defun make-fac-state (n call-tail store)
  (declare (xargs :guard (unsigned-byte-p 32 n)
                  :verify-guards nil))
  (make-state
   :store store
   :call-stack (cons (make-frame
                      :return-arity 1
                      :locals (list (make-i32-val n)
                                    (make-i32-val 0))
                      :operand-stack (empty-operand-stack)
                      :instrs *fac-body*
                      :label-stack nil)
                     call-tail)
   :memory nil :globals nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §1.  Symbolic-execution theory and loop-entry shape.

;; factorial needs i32.mul, i32.sub, i32.const on top of *wasm-exec-theory*.
(local (defconst *fac-exec-theory*
  (append '(execute-i32.mul execute-i32.sub execute-i32.const
            i32-const-argsp)
          *wasm-exec-theory*)))

;; After the 4-instruction prefix (:i32.const 1, :local.set 1, :block,
;; :loop), we are at "loop entry": locals = (n, acc), operand stack
;; empty, instrs = loop body, label-stack = (loop, block).
(defconst *fac-loop-body*
  '((:local.get 0)
    (:i32.eqz)
    (:br_if 1)
    (:local.get 1)
    (:local.get 0)
    (:i32.mul)
    (:local.set 1)
    (:local.get 0)
    (:i32.const 1)
    (:i32.sub)
    (:local.set 0)
    (:br 0)))

(defconst *fac-block-label*
  (make-label-entry :arity 0
                    :continuation '((:local.get 1))
                    :is-loop nil))

(defconst *fac-loop-label*
  (make-label-entry :arity 0
                    :continuation (list (list :loop 0 *fac-loop-body*))
                    :is-loop t))

(defun make-fac-loop-entry-state (n acc call-tail store)
  (declare (xargs :guard (and (unsigned-byte-p 32 n)
                              (unsigned-byte-p 32 acc))
                  :verify-guards nil))
  (make-state
   :store store
   :call-stack (cons (make-frame
                      :return-arity 1
                      :locals (list (make-i32-val n)
                                    (make-i32-val acc))
                      :operand-stack (empty-operand-stack)
                      :instrs *fac-loop-body*
                      :label-stack (list *fac-loop-label* *fac-block-label*))
                     call-tail)
   :memory nil :globals nil))

;; Prefix: 4 steps from (make-fac-state n) reach loop-entry(n, 1).
(defthm fac-state-to-loop-entry
  (implies (unsigned-byte-p 32 n)
           (equal (run 4 (make-fac-state n call-tail store))
                  (make-fac-loop-entry-state n 1 call-tail store)))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here) *fac-exec-theory*)
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))
                    (:free (n s a) (top-n-operands n s a))
                    (:free (v s) (push-vals v s))))))

(value-triple (cw " - fac-state-to-loop-entry: 4 steps reach loop entry (Q.E.D.)~%"))

;; Step case: from loop-entry(n, acc) with n != 0, 13 steps reach
;; loop-entry(n-1, acc*n) using the BV forms emitted by the interpreter.
(defthm loop-entry-step-case
  (implies (and (unsigned-byte-p 32 n)
                (unsigned-byte-p 32 acc)
                (not (equal n 0)))
           (equal (run 13 (make-fac-loop-entry-state n acc call-tail store))
                  (make-fac-loop-entry-state (acl2::bvminus 32 n 1)
                                             (acl2::bvmult 32 acc n)
                                             call-tail store)))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here) *fac-exec-theory*)
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))
                    (:free (n s a) (top-n-operands n s a))
                    (:free (n s) (pop-n-labels n s))
                    (:free (v s) (push-vals v s))))))

(value-triple (cw " - loop-entry-step-case: one iter: (n,acc) -> (n-1, acc*n) (Q.E.D.)~%"))

;; Base case: from loop-entry(0, acc), 4 steps expose acc on top.
(defthm loop-entry-base-case
  (implies (unsigned-byte-p 32 acc)
           (and (equal (top-operand
                        (current-operand-stack
                         (run 4 (make-fac-loop-entry-state 0 acc call-tail store))))
                       (make-i32-val acc))
                (not (consp (current-instrs
                             (run 4 (make-fac-loop-entry-state 0 acc call-tail store)))))
                (not (consp (current-label-stack
                             (run 4 (make-fac-loop-entry-state 0 acc call-tail store)))))))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here) *fac-exec-theory*)
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))
                    (:free (n s a) (top-n-operands n s a))
                    (:free (n s) (pop-n-labels n s))
                    (:free (v s) (push-vals v s))))))

(value-triple (cw " - loop-entry-base-case: n=0 exits with acc on top (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §2.  Plumbing: statep of loop-entry + run-plus iteration rewrite.

(local (defthm statep-of-make-fac-loop-entry-state
  (implies (and (unsigned-byte-p 32 n)
                (unsigned-byte-p 32 acc)
                (call-stackp call-tail)
                (storep store))
           (statep (make-fac-loop-entry-state n acc call-tail store)))
  :hints (("Goal" :in-theory (enable statep call-stackp framep
                                     label-stackp label-entryp
                                     operand-stackp val-listp
                                     i32-valp u32p)))))

;; One-iteration rewrite: (run (+ 13 k) loop-entry) = (run k next-entry).
;; Mirrors GCD's `run-plus-at-loop-entry` verbatim in structure.
(defthm run-plus-at-fac-loop-entry
  (implies (and (unsigned-byte-p 32 n)
                (unsigned-byte-p 32 acc)
                (call-stackp call-tail)
                (storep store)
                (not (equal n 0))
                (natp k))
           (equal (run (+ 13 k) (make-fac-loop-entry-state n acc call-tail store))
                  (run k (make-fac-loop-entry-state (acl2::bvminus 32 n 1)
                                                    (acl2::bvmult 32 acc n)
                                                    call-tail store))))
  :hints (("Goal"
           :do-not '(generalize fertilize eliminate-destructors)
           :do-not-induct t
           :use ((:instance loop-entry-step-case
                            (n n) (acc acc)
                            (call-tail call-tail) (store store))
                 (:instance run-split-when-statep
                            (m 13) (n k)
                            (state (make-fac-loop-entry-state n acc call-tail store)))
                 (:instance statep-of-make-fac-loop-entry-state
                            (n n) (acc acc)
                            (call-tail call-tail) (store store))
                 (:instance statep-of-make-fac-loop-entry-state
                            (n (acl2::bvminus 32 n 1))
                            (acc (acl2::bvmult 32 acc n))
                            (call-tail call-tail) (store store)))
           :in-theory (e/d ()
                           (loop-entry-step-case
                            run-split-when-statep
                            statep-of-make-fac-loop-entry-state
                            (:definition run)
                            (:definition make-fac-loop-entry-state)
                            (:definition make-i32-val))))))

(value-triple (cw " - run-plus-at-fac-loop-entry: (+ 13 k) splits through one iter (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §3.  Fuel, induction scheme, loop-invariant spec, main loop theorem.

(defun fac-loop-fuel (n)
  (declare (xargs :measure (nfix n)
                  :verify-guards nil))
  (if (zp n) 4 (+ 13 (fac-loop-fuel (- n 1)))))

;; Hand-written induction scheme: n decrements via BV (matches what
;; loop-entry-step-case and run-plus-at-fac-loop-entry leave on the
;; RHS); acc accumulates via bvmult (matches the RHS).  Under hyp
;; (u32p n) with n != 0, bvminus 32 n 1 = n - 1, so the measure
;; (nfix n) strictly decreases.
(defun fac-loop-ind (n acc)
  (declare (xargs :measure (nfix n)
                  :guard-hints (("Goal" :in-theory (enable u32p)))
                  :verify-guards nil))
  (if (zp n)
      (list n acc)
    (fac-loop-ind (- n 1) (acl2::bvmult 32 acc n))))

;; Bitvector factorial spec: the loop invariant's closed-form target.
;; For n <= 12 this coincides with the unbounded mathematical factorial
;; (see §4); for larger n it is `n! mod 2^32`, which is exactly what
;; the WASM implementation produces.
(defund fac-spec (n)
  (declare (xargs :measure (nfix n)
                  :verify-guards nil))
  (if (zp n)
      1
    (acl2::bvmult 32 n (fac-spec (- n 1)))))

(defthm u32p-of-fac-spec
  (unsigned-byte-p 32 (fac-spec n))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fac-spec))))

;; Key arithmetic: commutativity of bvmult 32 and re-association to
;; fold one iteration of the spec into the accumulator.
(local
 (defthm bvmult-32-acc-and-spec-step
   ;; acc * fac-spec(n) = (acc * n) * fac-spec(n-1)   when n != 0
   (implies (and (unsigned-byte-p 32 n)
                 (unsigned-byte-p 32 acc)
                 (not (equal n 0)))
            (equal (acl2::bvmult 32 acc (fac-spec n))
                   (acl2::bvmult 32 (acl2::bvmult 32 acc n)
                                 (fac-spec (- n 1)))))
   :hints (("Goal"
            :in-theory (enable fac-spec)
            :expand ((fac-spec n))))))

;; Main loop theorem: running the loop-entry for `fac-loop-fuel n`
;; steps leaves `(bvmult 32 acc (fac-spec n))` on top.
(defthm fac-loop-entry-correct
  (implies (and (unsigned-byte-p 32 n)
                (unsigned-byte-p 32 acc)
                (call-stackp call-tail)
                (storep store))
           (equal (top-operand
                   (current-operand-stack
                    (run (fac-loop-fuel n)
                         (make-fac-loop-entry-state n acc call-tail store))))
                  (make-i32-val (acl2::bvmult 32 acc (fac-spec n)))))
  :hints (("Goal"
           :induct (fac-loop-ind n acc)
           :in-theory (disable loop-entry-step-case
                               loop-entry-base-case
                               run-split-when-statep
                               statep-of-make-fac-loop-entry-state
                               make-fac-loop-entry-state
                               (:induction fac-loop-fuel))
           :expand ((fac-loop-fuel n)))
          ("Subgoal *1/2"
           ;; Step case: rewrite (bvminus 32 n 1) to (- n 1) so the IH
           ;; on (fac-loop-ind (- n 1) ...) lines up with the post-iter
           ;; state produced by run-plus-at-fac-loop-entry.
           :use ((:instance bvminus-32-of-u32-and-1 (n n))))
          ("Subgoal *1/1"
           :use ((:instance loop-entry-base-case
                            (acc acc)
                            (call-tail call-tail) (store store)))
           :in-theory (e/d (fac-spec)
                           (loop-entry-step-case
                            loop-entry-base-case
                            run-split-when-statep
                            statep-of-make-fac-loop-entry-state
                            make-fac-loop-entry-state
                            (:induction fac-loop-fuel))))))

(value-triple (cw " - fac-loop-entry-correct: top-operand = bvmult acc (fac-spec n) (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §4.  Body-level final theorem: from the entry state to the top-operand.

(defun fac-total-fuel (n)
  (declare (xargs :verify-guards nil))
  (+ 4 (fac-loop-fuel n)))

(local (defthm statep-of-make-fac-state
  (implies (and (unsigned-byte-p 32 n)
                (call-stackp call-tail)
                (storep store))
           (statep (make-fac-state n call-tail store)))
  :hints (("Goal" :in-theory (enable statep call-stackp framep
                                     label-stackp label-entryp
                                     operand-stackp val-listp
                                     i32-valp u32p)))))

(defthm fac-impl-correct
  (implies (and (unsigned-byte-p 32 n)
                (call-stackp call-tail)
                (storep store))
           (equal (top-operand
                   (current-operand-stack
                    (run (fac-total-fuel n) (make-fac-state n call-tail store))))
                  (make-i32-val (fac-spec n))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(generalize fertilize)
           :in-theory (disable fac-state-to-loop-entry
                               fac-loop-entry-correct
                               run-split-when-statep
                               statep-of-make-fac-state
                               make-fac-loop-entry-state
                               make-fac-state)
           :use ((:instance fac-state-to-loop-entry
                            (n n) (call-tail call-tail) (store store))
                 (:instance statep-of-make-fac-state
                            (n n) (call-tail call-tail) (store store))
                 (:instance run-split-when-statep
                            (m 4)
                            (n (fac-loop-fuel n))
                            (state (make-fac-state n call-tail store)))
                 (:instance fac-loop-entry-correct
                            (n n) (acc 1)
                            (call-tail call-tail) (store store))))))

(value-triple (cw "~%====================================================~%"))
(value-triple (cw " FACTORIAL IMPLEMENTATION PROVED CORRECT (BV spec).~%"))
(value-triple (cw "====================================================~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §5.  Bounded corollary: bv factorial coincides with mathematical
;; factorial for n <= 12.
;;
;; 12! = 479,001,600 < 2^32 = 4,294,967,296.
;; 13! = 6,227,020,800 > 2^32 — would overflow.

(include-book "arithmetic/factorial" :dir :system)

(local
 (defthm bvmult-32-when-product-is-u32
   (implies (and (natp a)
                 (natp b)
                 (unsigned-byte-p 32 a)
                 (unsigned-byte-p 32 b)
                 (unsigned-byte-p 32 (* a b)))
            (equal (acl2::bvmult 32 a b) (* a b)))
   :hints (("Goal" :in-theory (enable acl2::bvmult acl2::bvchop)))))

;; For n <= 12, factorial n is fully determined and bounded by 12! = 479001600.
;; We case-split explicitly on n because the natural induction doesn't
;; prove the bound tight enough without knowing factorial 11 = 39916800.
(local
 (defthm u32p-of-factorial-bounded
   (implies (and (natp n) (<= n 12))
            (unsigned-byte-p 32 (acl2::factorial n)))
   :hints (("Goal"
            :in-theory (enable acl2::factorial)
            :cases ((equal n 0) (equal n 1) (equal n 2) (equal n 3)
                    (equal n 4) (equal n 5) (equal n 6) (equal n 7)
                    (equal n 8) (equal n 9) (equal n 10) (equal n 11)
                    (equal n 12))))))

(defthm fac-spec-when-small
  (implies (and (natp n) (<= n 12))
           (equal (fac-spec n) (acl2::factorial n)))
  :hints (("Goal"
           :induct (fac-spec n)
           :in-theory (enable fac-spec acl2::factorial))
          ("Subgoal *1/2"
           ;; n * factorial(n-1) = factorial(n); bounded u32 by
           ;; u32p-of-factorial-bounded, so bvmult = plain *.
           :use ((:instance u32p-of-factorial-bounded (n n)))
           :in-theory (e/d (fac-spec acl2::factorial)
                           (u32p-of-factorial-bounded)))))

(defthm fac-impl-correct-bounded
  (implies (and (natp n)
                (<= n 12)
                (call-stackp call-tail)
                (storep store))
           (equal (top-operand
                   (current-operand-stack
                    (run (fac-total-fuel n) (make-fac-state n call-tail store))))
                  (make-i32-val (acl2::factorial n))))
  :hints (("Goal"
           :use ((:instance fac-impl-correct
                            (n n) (call-tail call-tail) (store store))
                 (:instance fac-spec-when-small (n n)))
           :in-theory (disable fac-impl-correct fac-spec-when-small
                               fac-spec fac-total-fuel
                               make-fac-state))))

(value-triple (cw " - fac-impl-correct-bounded: matches (factorial n) for n <= 12 (Q.E.D.)~%"))
