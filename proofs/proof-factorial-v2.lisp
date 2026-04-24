;; WASM 1.0 ACL2 — iterative factorial end-to-end correctness (Round 2)
;;
;; v2 of [proof-factorial-spec.lisp](proof-factorial-spec.lisp), using
;; the generic loop lifter from [wasm-loop-lifter.lisp](wasm-loop-lifter.lisp).
;;
;; Compared to v1:
;;   * No `fac-loop-ind` induction scheme.
;;   * No `run-plus-at-fac-loop-entry` rewrite lemma.
;;   * No hand-written main induction proof for `fac-loop-entry-correct`
;;     (it is obtained by functional instantiation of `ll-loop-correct`).
;;
;; What remains:
;;   §0. Binary load + state constructors.
;;   §1. Lifted loop function `fac-loop-fn` and total-fuel (plain
;;       recursive defuns — the user's "code model").
;;   §2. 4-step prefix + 13-step iter + 4-step exit (the 3 irreducibly
;;       program-specific symbolic-execution lemmas).
;;   §3. Functional instantiation of the generic lifter.
;;   §4. Body-level final theorem.
;;   §5. Spec connection: `fac-loop-fn n 1 = fac-spec n`, and bounded
;;       corollary against `acl2::factorial`.

(in-package "WASM")
(include-book "../execution")
(include-book "wasm-run-utils")
(include-book "wasm-arith-utils")
(include-book "wasm-loader")
(include-book "wasm-loop-lifter")

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
;; §1.  Lifted loop.  `vars = (cons n acc)`.
;;
;; The lifter treats `vars` as opaque; we pick a list layout here and
;; destructure at each use.  Writing these by hand is the "code model"
;; (analogous to Axe's `factorial-loop-1.4` after the APT pipeline).

(defun fac-vars-ok (vars)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp vars)
       (unsigned-byte-p 32 (car vars))
       (unsigned-byte-p 32 (cdr vars))))

(defun fac-exit? (vars)
  (declare (xargs :guard t :verify-guards nil))
  ;; Defensively treat non-u32 cars as "exit": the lifter's
  ;; measure-decrease constraint is unconditional on `fac-vars-ok`,
  ;; so we need the exit predicate to catch any case where
  ;; `(bvminus 32 n 1)` might fail to strictly decrease.
  (or (not (unsigned-byte-p 32 (car vars)))
      (equal (car vars) 0)))

(defun fac-next (vars)
  (declare (xargs :guard t :verify-guards nil))
  (cons (acl2::bvminus 32 (car vars) 1)
        (acl2::bvmult 32 (cdr vars) (car vars))))

(defun fac-result (vars)
  (declare (xargs :guard t :verify-guards nil))
  (make-i32-val (cdr vars)))

(defun fac-measure (vars)
  (declare (xargs :guard t :verify-guards nil))
  (nfix (car vars)))

(defthm o-p-of-fac-measure
  (o-p (fac-measure vars)))

(defthm fac-measure-decreases
  (implies (not (fac-exit? vars))
           (o< (fac-measure (fac-next vars)) (fac-measure vars)))
  :hints (("Goal" :in-theory (enable acl2::bvminus acl2::bvchop))))

(defthm fac-vars-ok-of-fac-next
  (implies (and (fac-vars-ok vars)
                (not (fac-exit? vars)))
           (fac-vars-ok (fac-next vars))))

(defun fac-loop-fn (vars)
  (declare (xargs :measure (fac-measure vars)
                  :verify-guards nil))
  (if (fac-exit? vars)
      (fac-result vars)
    (fac-loop-fn (fac-next vars))))

(defconst *fac-iter-fuel* 13)
(defconst *fac-exit-fuel* 4)

(defun fac-iter-fuel () (declare (xargs :guard t)) *fac-iter-fuel*)
(defun fac-exit-fuel () (declare (xargs :guard t)) *fac-exit-fuel*)

(defun fac-total-fuel (vars)
  (declare (xargs :measure (fac-measure vars)
                  :verify-guards nil))
  (if (fac-exit? vars)
      (fac-exit-fuel)
    (+ (fac-iter-fuel) (fac-total-fuel (fac-next vars)))))

(defthm natp-of-fac-iter-fuel
  (natp (fac-iter-fuel))
  :rule-classes :type-prescription)

(defthm natp-of-fac-exit-fuel
  (natp (fac-exit-fuel))
  :rule-classes :type-prescription)

(defthm natp-of-fac-total-fuel
  (natp (fac-total-fuel vars))
  :rule-classes :type-prescription)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §2.  The three irreducibly program-specific symbolic-execution lemmas.
;; These are the analogue of Axe's `:loops` annotations: the raw ISA
;; semantics of this particular loop body.

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

(defun make-fac-header (vars call-tail store)
  (declare (xargs :guard (fac-vars-ok vars) :verify-guards nil))
  (make-state
   :store store
   :call-stack (cons (make-frame
                      :return-arity 1
                      :locals (list (make-i32-val (car vars))
                                    (make-i32-val (cdr vars)))
                      :operand-stack (empty-operand-stack)
                      :instrs *fac-loop-body*
                      :label-stack (list *fac-loop-label* *fac-block-label*))
                     call-tail)
   :memory nil :globals nil))

(local (defconst *fac-exec-theory*
  (append '(execute-i32.mul execute-i32.sub execute-i32.const
            i32-const-argsp)
          *wasm-exec-theory*)))

;; (a) Prefix: 4 steps from the body entry reach the loop header.
(defthm fac-state-to-header
  (implies (unsigned-byte-p 32 n)
           (equal (run 4 (make-fac-state n call-tail store))
                  (make-fac-header (cons n 1) call-tail store)))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here) *fac-exec-theory*)
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))
                    (:free (n s a) (top-n-operands n s a))
                    (:free (v s) (push-vals v s))))))

;; (b) Iter-step: 13 steps through one iteration.
(defthm fac-iter-step
  (implies (and (fac-vars-ok vars)
                (not (fac-exit? vars))
                (call-stackp call-tail)
                (storep store))
           (equal (run (fac-iter-fuel) (make-fac-header vars call-tail store))
                  (make-fac-header (fac-next vars) call-tail store)))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here) *fac-exec-theory*)
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))
                    (:free (n s a) (top-n-operands n s a))
                    (:free (n s) (pop-n-labels n s))
                    (:free (v s) (push-vals v s))))))

;; (c) Exit-step: 4 steps when n=0 expose (cdr vars) on top.
(defthm fac-exit-step
  (implies (and (fac-vars-ok vars)
                (fac-exit? vars)
                (call-stackp call-tail)
                (storep store))
           (and (equal (top-operand
                        (current-operand-stack
                         (run (fac-exit-fuel) (make-fac-header vars call-tail store))))
                       (fac-result vars))
                (not (consp (current-instrs
                             (run (fac-exit-fuel) (make-fac-header vars call-tail store)))))
                (not (consp (current-label-stack
                             (run (fac-exit-fuel) (make-fac-header vars call-tail store)))))))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here) *fac-exec-theory*)
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))
                    (:free (n s a) (top-n-operands n s a))
                    (:free (n s) (pop-n-labels n s))
                    (:free (v s) (push-vals v s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §3.  Functional instantiation of `ll-loop-correct`.
;;
;; This is the only place the generic lifter shows through.  The
;; instantiation is purely mechanical: every abstract witness is mapped
;; to a `fac-*` counterpart.

(local (defthm statep-of-make-fac-header
  (implies (and (fac-vars-ok vars)
                (call-stackp call-tail)
                (storep store))
           (statep (make-fac-header vars call-tail store)))
  :hints (("Goal" :in-theory (enable statep call-stackp framep
                                     label-stackp label-entryp
                                     operand-stackp val-listp
                                     i32-valp u32p)))))

(defthm fac-loop-header-correct
  (implies (and (fac-vars-ok vars)
                (call-stackp call-tail)
                (storep store))
           (and (equal (top-operand
                        (current-operand-stack
                         (run (fac-total-fuel vars)
                              (make-fac-header vars call-tail store))))
                       (fac-loop-fn vars))
                (not (consp (current-instrs
                             (run (fac-total-fuel vars)
                                  (make-fac-header vars call-tail store)))))
                (not (consp (current-label-stack
                             (run (fac-total-fuel vars)
                                  (make-fac-header vars call-tail store)))))))
  :hints (("Goal"
           :use ((:functional-instance ll-loop-correct
                  (ll-input-ok        fac-vars-ok)
                  (ll-exit?           fac-exit?)
                  (ll-next            fac-next)
                  (ll-result          fac-result)
                  (ll-measure         fac-measure)
                  (ll-fn              fac-loop-fn)
                  (ll-total-fuel      fac-total-fuel)
                  (ll-iter-fuel       fac-iter-fuel)
                  (ll-exit-fuel       fac-exit-fuel)
                  (ll-state-at-header make-fac-header)))
           :in-theory (disable fac-vars-ok fac-exit? fac-next fac-result
                               fac-measure
                               fac-iter-fuel fac-exit-fuel
                               make-fac-header
                               storep
                               current-operand-stack current-instrs
                               current-label-stack
                               (:executable-counterpart fac-iter-fuel)
                               (:executable-counterpart fac-exit-fuel)))
          ;; Subgoal numbers are in REVERSE order of the 11 exported
          ;; constraints.  Only the non-trivial ones actually appear.
          ;; Explicit :expand forces unfolding of the user's recursive
          ;; defuns in the matching subgoal.
          ("Goal'"
           :expand ((fac-loop-fn vars) (fac-total-fuel vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §4.  Body-level final theorem: glue the 4-step prefix with the
;; loop-correctness theorem via `run-split-when-statep`.

(local (defthm statep-of-make-fac-state
  (implies (and (unsigned-byte-p 32 n)
                (call-stackp call-tail)
                (storep store))
           (statep (make-fac-state n call-tail store)))
  :hints (("Goal" :in-theory (enable statep call-stackp framep
                                     label-stackp label-entryp
                                     operand-stackp val-listp
                                     i32-valp u32p)))))

(defun fac-run-fuel (n)
  (declare (xargs :verify-guards nil))
  (+ 4 (fac-total-fuel (cons n 1))))

(defthm fac-impl-correct
  (implies (and (unsigned-byte-p 32 n)
                (call-stackp call-tail)
                (storep store))
           (equal (top-operand
                   (current-operand-stack
                    (run (fac-run-fuel n) (make-fac-state n call-tail store))))
                  (fac-loop-fn (cons n 1))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (disable fac-state-to-header
                               fac-loop-header-correct
                               make-fac-header make-fac-state
                               run-split-when-statep)
           :use ((:instance fac-state-to-header (n n))
                 (:instance statep-of-make-fac-state)
                 (:instance run-split-when-statep
                            (m 4)
                            (n (fac-total-fuel (cons n 1)))
                            (state (make-fac-state n call-tail store)))
                 (:instance fac-loop-header-correct
                            (vars (cons n 1)))))))

(value-triple (cw "~%=====================================================~%"))
(value-triple (cw " FACTORIAL IMPL CORRECT via wasm-loop-lifter (v2). ~%"))
(value-triple (cw "=====================================================~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §5.  Spec connection and bounded corollary.

(defund fac-spec (n)
  (declare (xargs :measure (nfix n) :verify-guards nil))
  (if (zp n) 1 (acl2::bvmult 32 n (fac-spec (- n 1)))))

(defthm u32p-of-fac-spec
  (unsigned-byte-p 32 (fac-spec n))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fac-spec))))

;; Hand-written induction matching fac-loop-fn's recursion on (n, acc).
(local
 (defun fac-loop-ind (n acc)
   (declare (xargs :measure (nfix n) :verify-guards nil))
   (if (zp n) (list n acc)
     (fac-loop-ind (- n 1) (acl2::bvmult 32 acc n)))))

;; Fold one iteration of the spec into the accumulator.
(local
 (defthm bvmult-32-acc-and-spec-step
   (implies (and (unsigned-byte-p 32 n)
                 (unsigned-byte-p 32 acc)
                 (not (equal n 0)))
            (equal (acl2::bvmult 32 acc (fac-spec n))
                   (acl2::bvmult 32 (acl2::bvmult 32 acc n)
                                 (fac-spec (- n 1)))))
   :hints (("Goal"
            :in-theory (enable fac-spec)
            :expand ((fac-spec n))))))

;; `fac-loop-fn (n, acc)` = `(bvmult 32 acc (fac-spec n))`.
(local
 (defthm fac-loop-fn-characterization-lemma
   (implies (and (unsigned-byte-p 32 n)
                 (unsigned-byte-p 32 acc))
            (equal (fac-loop-fn (cons n acc))
                   (make-i32-val (acl2::bvmult 32 acc (fac-spec n)))))
   :hints (("Goal"
            :induct (fac-loop-ind n acc)
            :in-theory (enable fac-loop-fn fac-exit? fac-next fac-result
                               fac-spec acl2::bvminus)))))

(defthm fac-loop-fn-of-n-1
  (implies (unsigned-byte-p 32 n)
           (equal (fac-loop-fn (cons n 1))
                  (make-i32-val (fac-spec n))))
  :hints (("Goal" :use ((:instance fac-loop-fn-characterization-lemma
                                   (n n) (acc 1)))
           :in-theory (disable fac-loop-fn-characterization-lemma
                               fac-loop-fn))))

;; Bounded corollary: factorial n fits in u32 for n <= 12.
(include-book "arithmetic/factorial" :dir :system)

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

(local
 (defthm bvmult-32-when-product-is-u32
   (implies (and (natp a) (natp b)
                 (unsigned-byte-p 32 a) (unsigned-byte-p 32 b)
                 (unsigned-byte-p 32 (* a b)))
            (equal (acl2::bvmult 32 a b) (* a b)))
   :hints (("Goal" :in-theory (enable acl2::bvmult acl2::bvchop)))))

(defthm fac-spec-when-small
  (implies (and (natp n) (<= n 12))
           (equal (fac-spec n) (acl2::factorial n)))
  :hints (("Goal"
           :induct (fac-spec n)
           :in-theory (enable fac-spec acl2::factorial))
          ("Subgoal *1/2"
           :use ((:instance u32p-of-factorial-bounded (n n)))
           :in-theory (e/d (fac-spec acl2::factorial)
                           (u32p-of-factorial-bounded)))))

(defthm fac-impl-correct-bounded
  (implies (and (natp n) (<= n 12)
                (call-stackp call-tail) (storep store))
           (equal (top-operand
                   (current-operand-stack
                    (run (fac-run-fuel n) (make-fac-state n call-tail store))))
                  (make-i32-val (acl2::factorial n))))
  :hints (("Goal"
           :use ((:instance fac-impl-correct)
                 (:instance fac-spec-when-small)
                 (:instance fac-loop-fn-of-n-1))
           :in-theory (disable fac-impl-correct
                               fac-spec-when-small
                               fac-loop-fn-of-n-1
                               fac-loop-fn fac-spec fac-total-fuel
                               make-fac-state))))

(value-triple (cw " - fac-impl-correct-bounded: matches (factorial n) for n <= 12 (Q.E.D.)~%"))
