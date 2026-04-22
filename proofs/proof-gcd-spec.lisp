;; WASM 1.0 ACL2 — GCD end-to-end correctness specification (in progress)
;;
;; The WASM program `*gcd-func*` (from tests/test-spot-check.lisp) implements
;; the Euclidean algorithm on unsigned 32-bit integers:
;;
;;     while (b != 0) { t = b; b = a rem_u b; a = t; }
;;     return a;
;;
;; The ACL2 arithmetic book `arithmetic/mod-gcd` already defines the
;; mathematical spec `nonneg-int-gcd` and proves it is a GCD.
;;
;; Strategy: build up from concrete symbolic-execution lemmas (in the
;; style of proofs/proof-loop-spec.lisp) toward the general theorem.
;;
;;   Phase 1 (this file)  — Base case lemma: when b = 0, the WASM
;;                          implementation returns (make-i32-val a).
;;   Phase 2 (future)     — Step-case lemma: one full loop iteration
;;                          reduces (a,b) to (b, a rem_u b).
;;   Phase 3 (future)     — Induction on nonneg-int-gcd to combine.

(in-package "WASM")
(include-book "../execution")
(include-book "arithmetic/mod-gcd" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The program under test — kept in sync with tests/test-spot-check.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Program under test — body mirrors tests/test-spot-check.lisp but we
;; execute it directly in a single frame (no `:call` wrapper), as in
;; proof-abs-e2e.lisp. This keeps the result a plain state (no :done tag).

(defconst *gcd-body*
  '((:block 0 ((:loop 0 ((:local.get 1)
                         (:i32.eqz)
                         (:br_if 1)
                         (:local.get 1)
                         (:local.set 2)
                         (:local.get 0)
                         (:local.get 1)
                         (:i32.rem_u)
                         (:local.set 1)
                         (:local.get 2)
                         (:local.set 0)
                         (:br 0)))))
    (:local.get 0)))

(defun make-gcd-state (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b))
                  :verify-guards nil))
  (make-state
   :store nil
   :call-stack (list (make-frame
                      :return-arity 1
                      :locals (list (make-i32-val a)
                                    (make-i32-val b)
                                    (make-i32-val 0))
                      :operand-stack (empty-operand-stack)
                      :instrs *gcd-body*
                      :label-stack nil))
   :memory nil :globals nil))

(defun gcd-result (st)
  (declare (xargs :guard (statep st) :verify-guards nil))
  (top-operand (current-operand-stack st)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theory for symbolic execution (mirrors proof-loop-spec.lisp /
;; proof-abs-e2e.lisp).

(local (defconst *gcd-exec-theory*
  '(run execute-instr
    execute-block execute-loop
    execute-local.get execute-local.set
    execute-i32.eqz execute-i32.rem_u
    execute-br execute-br_if
    current-frame current-instrs current-operand-stack
    current-label-stack current-locals
    update-current-operand-stack update-current-instrs
    update-current-label-stack update-current-locals
    complete-label return-from-function
    make-i32-val i32-valp i32-const-argsp
    local-idx-argsp no-argsp
    push-operand top-operand pop-operand top-n-operands push-vals
    operand-stack-height empty-operand-stack operand-stackp
    localsp framep top-frame push-call-stack pop-call-stack call-stackp
    valp i64-valp u32p u64p val-listp
    label-entryp label-entry->arity label-entry->continuation
    label-entry->is-loop push-label pop-label top-label
    label-stackp nth-label pop-n-labels
    nth-local update-nth-local
    frame->return-arity frame->locals frame->operand-stack
    frame->instrs frame->label-stack
    state->store state->call-stack state->memory state->globals state->table
    state
    frame
    statep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 1: Base case. When b = 0, running the WASM gcd returns a.

(defthm gcd-impl-base-case
  (implies (unsigned-byte-p 32 a)
           (equal (top-operand
                   (current-operand-stack
                    (run 6 (make-gcd-state a 0))))
                  (make-i32-val a)))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here) *gcd-exec-theory*)
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))
                    (:free (n s a) (top-n-operands n s a))
                    (:free (n s) (pop-n-labels n s))
                    (:free (v s) (push-vals v s))))))

(value-triple (cw "~% - gcd-impl-base-case: gcd(a,0) = a at the WASM level (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 2: Step-case lemma.
;;
;; After 2 steps from `make-gcd-state a b`, we arrive at a "loop-entry"
;; state: locals=(a b 0), instrs = loop-body, label-stack = (loop, block).
;; After one full iteration (13 more WASM steps) we are back at a
;; loop-entry state with locals = (b, a mod b, b).
;;
;; We express the loop-entry state with an extra parameter t (the temp
;; local's value), because on the second and later iterations it is no
;; longer 0.

(defconst *gcd-loop-body*
  '((:local.get 1)
    (:i32.eqz)
    (:br_if 1)
    (:local.get 1)
    (:local.set 2)
    (:local.get 0)
    (:local.get 1)
    (:i32.rem_u)
    (:local.set 1)
    (:local.get 2)
    (:local.set 0)
    (:br 0)))

(defconst *gcd-block-label*
  (make-label-entry :arity 0
                    :continuation '((:local.get 0))
                    :is-loop nil))

(defconst *gcd-loop-label*
  (make-label-entry :arity 0
                    :continuation (list (list :loop 0 *gcd-loop-body*))
                    :is-loop t))

(defun make-loop-entry-state (a b tmp)
  (declare (xargs :guard (and (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b)
                              (unsigned-byte-p 32 tmp))
                  :verify-guards nil))
  (make-state
   :store nil
   :call-stack (list (make-frame
                      :return-arity 1
                      :locals (list (make-i32-val a)
                                    (make-i32-val b)
                                    (make-i32-val tmp))
                      :operand-stack (empty-operand-stack)
                      :instrs *gcd-loop-body*
                      :label-stack (list *gcd-loop-label* *gcd-block-label*)))
   :memory nil :globals nil))

;; Sanity: running 2 steps from a fresh gcd-state gives the corresponding
;; loop-entry-state.
(defthm gcd-state-to-loop-entry
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (equal (run 2 (make-gcd-state a b))
                  (make-loop-entry-state a b 0)))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here) *gcd-exec-theory*)
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))))))

(value-triple (cw " - gcd-state-to-loop-entry: 2 steps reach loop entry (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Step case: from a loop-entry state with b ≠ 0, 13 steps reach
;; loop-entry(b, (mod a b), b).

(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm u32p-of-mod
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (unsigned-byte-p 32 (mod a b)))
  :hints (("Goal" :cases ((equal b 0))))))

(local (defthm bvmod-32-when-u32
  ;; i32.rem_u on u32 inputs with nonzero divisor is plain integer mod.
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (not (equal b 0)))
           (equal (acl2::bvmod 32 a b) (mod a b)))
  :hints (("Goal" :in-theory (enable acl2::bvmod)))))

(defthm loop-entry-step-case
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (unsigned-byte-p 32 tmp)
                (not (equal b 0)))
           (equal (run 13 (make-loop-entry-state a b tmp))
                  (make-loop-entry-state b (mod a b) b)))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here) *gcd-exec-theory*)
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))
                    (:free (n s a) (top-n-operands n s a))
                    (:free (n s) (pop-n-labels n s))
                    (:free (v s) (push-vals v s))))))

(value-triple (cw " - loop-entry-step-case: one iteration reduces (a,b) to (b,a mod b) (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Base case from loop entry: when b = 0, 4 steps from a loop-entry state
;; leave `a` as the top operand.

(defthm loop-entry-base-case
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 tmp))
           (equal (top-operand
                   (current-operand-stack
                    (run 4 (make-loop-entry-state a 0 tmp))))
                  (make-i32-val a)))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here) *gcd-exec-theory*)
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))
                    (:free (n s a) (top-n-operands n s a))
                    (:free (n s) (pop-n-labels n s))
                    (:free (v s) (push-vals v s))))))

(value-triple (cw " - loop-entry-base-case: b=0 exits with a on top (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 3: Induction.
;;
;; Fuel function mirroring the Euclidean recursion: 4 steps for b=0,
;; 13 steps per iteration otherwise.

(defun gcd-loop-fuel (a b)
  (declare (xargs :measure (nfix b)
                  :verify-guards nil))
  (if (zp b)
      4
    (+ 13 (gcd-loop-fuel b (mod a b)))))

;; Induction scheme mirroring the step lemma: the recursive call's
;; `tmp` argument becomes `b` (matching loop-entry-step-case's output).
(defun gcd-loop-ind (a b tmp)
  (declare (xargs :measure (nfix b)
                  :verify-guards nil))
  (if (zp b)
      (list a b tmp)
    (gcd-loop-ind b (mod a b) b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Run-split lemma: when `run M state` lands in a proper state (no trap,
;; no :done), then `run (+ M N) state = run N (run M state)`.
;;
;; This is needed to glue together symbolic-execution lemmas across an
;; inductive proof: we can take 13 steps to reach the next loop entry,
;; then apply the induction hypothesis on the remaining N steps.

(local (defun run-ind (m state)
  (declare (xargs :measure (nfix m)))
  (if (zp m)
      state
    (if (not (consp (current-instrs state)))
        (if (consp (current-label-stack state))
            (let ((ns (complete-label state)))
              (if (eq :trap ns) state (run-ind (+ -1 m) ns)))
          (let ((r (return-from-function state)))
            (cond ((eq :trap r) state)
                  ((and (consp r) (eq :done (first r))) state)
                  (t (run-ind (+ -1 m) r)))))
      (let ((ns (step state)))
        (if (eq :trap ns) state (run-ind (+ -1 m) ns)))))))

(local (defthm not-statep-of-done
  (not (statep (cons :done x)))
  :hints (("Goal" :in-theory (enable statep)))))

(local (defthm not-statep-of-trap
  (not (statep :trap))
  :hints (("Goal" :in-theory (enable statep)))))

(local (defthm run-split-when-statep
  (implies (and (natp m) (natp n) (statep (run m state)))
           (equal (run (+ m n) state)
                  (run n (run m state))))
  :hints (("Goal" :induct (run-ind m state)))))

(value-triple (cw " - run-split-when-statep: local run-decomposition lemma (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; statep-ness of a loop-entry state (needed to discharge the hyp of
;; run-split-when-statep after taking 13 steps).

(local (defthm statep-of-make-loop-entry-state
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (unsigned-byte-p 32 tmp))
           (statep (make-loop-entry-state a b tmp)))
  :hints (("Goal" :in-theory (enable statep call-stackp framep
                                     label-stackp label-entryp
                                     operand-stackp val-listp
                                     i32-valp u32p)))))

(local (defthm nonneg-int-gcd-of-0-right
  (equal (acl2::nonneg-int-gcd x 0) (nfix x))
  :hints (("Goal" :expand ((acl2::nonneg-int-gcd x 0))))))

(local (defthm nonneg-int-gcd-of-0-left
  (equal (acl2::nonneg-int-gcd 0 x) (nfix x))
  :hints (("Goal" :expand ((acl2::nonneg-int-gcd 0 x))
                  :in-theory (enable acl2::nonneg-int-mod)))))

(local (defthm nfix-when-natp
  (implies (natp x) (equal (nfix x) x))))

(local (defthm nonneg-int-mod-is-mod
  (implies (and (natp a) (posp b))
           (equal (acl2::nonneg-int-mod a b) (mod a b)))
  :hints (("Goal" :in-theory (enable acl2::nonneg-int-mod mod floor)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Combined run/step rewrite: one loop iteration, distributed into
;; additional fuel.  This avoids forcing rounds over statep during the
;; main induction.

(defthm run-plus-at-loop-entry
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (unsigned-byte-p 32 tmp)
                (not (equal b 0))
                (natp n))
           (equal (run (+ 13 n) (make-loop-entry-state a b tmp))
                  (run n (make-loop-entry-state b (mod a b) b))))
  :hints (("Goal"
           :do-not '(generalize fertilize eliminate-destructors)
           :do-not-induct t
           :use ((:instance loop-entry-step-case (a a) (b b) (tmp tmp))
                 (:instance run-split-when-statep
                            (m 13) (n n)
                            (state (make-loop-entry-state a b tmp)))
                 (:instance statep-of-make-loop-entry-state
                            (a a) (b b) (tmp tmp))
                 (:instance statep-of-make-loop-entry-state
                            (a b) (b (mod a b)) (tmp b))
                 (:instance u32p-of-mod (a a) (b b)))
           :in-theory (e/d (u32p)
                           (loop-entry-step-case
                            run-split-when-statep
                            statep-of-make-loop-entry-state
                            u32p-of-mod
                            (:definition run)
                            (:definition make-loop-entry-state)
                            (:definition make-i32-val))))))

(value-triple (cw " - run-plus-at-loop-entry: splits (+ 13 n) run through one iter (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main correctness theorem (loop-entry form).

(defthm gcd-loop-entry-correct
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (unsigned-byte-p 32 tmp))
           (equal (top-operand
                   (current-operand-stack
                    (run (gcd-loop-fuel a b)
                         (make-loop-entry-state a b tmp))))
                  (make-i32-val (acl2::nonneg-int-gcd a b))))
  :hints (("Goal"
           :induct (gcd-loop-ind a b tmp)
           :in-theory (disable loop-entry-step-case
                               loop-entry-base-case
                               run-split-when-statep
                               statep-of-make-loop-entry-state
                               acl2::nonneg-int-gcd
                               make-loop-entry-state
                               (:induction gcd-loop-fuel))
           :expand ((:free (x) (acl2::nonneg-int-gcd a x))))
          ("Subgoal *1/1"
           :use ((:instance loop-entry-base-case (a a) (tmp tmp))))))

(value-triple (cw " - gcd-loop-entry-correct: top-operand = nonneg-int-gcd for all u32 (a,b) (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final theorem: starting from the fresh gcd-state, the WASM
;; implementation computes nonneg-int-gcd.

(defun gcd-total-fuel (a b)
  (declare (xargs :verify-guards nil))
  (+ 2 (gcd-loop-fuel a b)))

(local (defthm statep-of-make-gcd-state
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (statep (make-gcd-state a b)))
  :hints (("Goal" :in-theory (enable statep call-stackp framep
                                     label-stackp label-entryp
                                     operand-stackp val-listp
                                     i32-valp u32p)))))

(defthm gcd-impl-correct
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (equal (top-operand
                   (current-operand-stack
                    (run (gcd-total-fuel a b) (make-gcd-state a b))))
                  (make-i32-val (acl2::nonneg-int-gcd a b))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(generalize fertilize)
           :in-theory (disable gcd-state-to-loop-entry
                               gcd-loop-entry-correct
                               run-split-when-statep
                               statep-of-make-gcd-state
                               make-loop-entry-state
                               make-gcd-state
                               acl2::nonneg-int-gcd)
           :use ((:instance gcd-state-to-loop-entry (a a) (b b))
                 (:instance statep-of-make-gcd-state (a a) (b b))
                 (:instance run-split-when-statep
                            (m 2)
                            (n (gcd-loop-fuel a b))
                            (state (make-gcd-state a b)))
                 (:instance gcd-loop-entry-correct
                            (a a) (b b) (tmp 0))))))

(value-triple (cw "~%====================================================~%"))
(value-triple (cw " GCD IMPLEMENTATION PROVED CORRECT for all u32 a,b.~%"))
(value-triple (cw "====================================================~%"))



