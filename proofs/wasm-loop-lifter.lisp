; wasm-loop-lifter.lisp — generic WASM loop-correctness lifter.
;
; Copyright (C) 2026 Kestrel Institute
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; MOTIVATION
; ----------
;
; Every iterative WASM program we prove correct has the same skeleton:
;
;     (run (total-fuel vars) (state-at-loop-header vars ct s))
;
;       =  <fixed shape with (lifted-fn vars) on top of the operand stack>
;
; and the proof is always the same induction:
;
;     base  (exit condition holds)
;         → run exit-fuel steps, top of stack = result
;     step  (exit condition fails)
;         → run iter-fuel steps, reach state-at-header(next-vars)
;         → IH on next-vars completes the run
;
; Prior to this book we wrote that induction by hand in every proof
; (e.g. [proofs/proof-gcd-spec.lisp](proof-gcd-spec.lisp) §3 and
; [proofs/proof-factorial-spec.lisp](proof-factorial-spec.lisp) §3).
; This book factors the induction into one abstract theorem,
; `ll-loop-correct`, that callers functionally-instantiate.  The
; per-program work reduces to:
;
;   (a) define your loop as a pair of recursive ACL2 functions
;       (the lifted `fn` and the closed-form `total-fuel`);
;   (b) prove the 13-step iter-step and 4-step exit-step lemmas (the
;       only irreducibly program-specific part of any WASM proof,
;       analogous to the `:loops` annotations Axe consumes);
;   (c) functionally-instantiate `ll-loop-correct`.
;
; See [proofs/GCD_PROOF_NOTES.md](GCD_PROOF_NOTES.md) Appendix D for
; the full recipe and an example of its use on `factorial`.

(in-package "WASM")

(include-book "../execution")
(include-book "wasm-run-utils")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §1. Abstract program signature.
;;
;; `vars` is an opaque argument tuple (typically a list of u32s).  The
;; user supplies:
;;
;;   ll-input-ok       : shape/guard on vars
;;   ll-exit?          : when the loop terminates
;;   ll-next           : one-iteration transition on vars
;;   ll-result         : observable left on top of the stack at exit
;;   ll-measure        : ordinal measure, strictly decreases each iter
;;   ll-fn             : the lifted loop function (satisfies ll-fn-eqn)
;;   ll-total-fuel     : the closed-form total fuel (satisfies fuel-eqn)
;;   ll-iter-fuel      : nat, # steps consumed by one iteration
;;   ll-exit-fuel      : nat, # steps consumed on exit
;;   ll-state-at-header: the WASM state sitting at the top of the loop
;;
;; All constraints exported are stated purely in terms of these
;; witnesses plus primitives from `execution.lisp` (`run`, `top-operand`,
;; `current-*`, `call-stackp`, `storep`, `statep`).

(encapsulate
  (((ll-input-ok *)               => *)
   ((ll-exit? *)                  => *)
   ((ll-next *)                   => *)
   ((ll-result *)                 => *)
   ((ll-measure *)                => *)
   ((ll-fn *)                     => *)
   ((ll-total-fuel *)             => *)
   ((ll-iter-fuel)                => *)
   ((ll-exit-fuel)                => *)
   ((ll-state-at-header * * *)    => *))

  ;; ---- Trivial witnesses ------------------------------------------------
  ;; The witness instance is "always exit immediately": no iteration
  ;; ever happens, the header-state already exposes the result on top
  ;; of the operand stack with empty instrs and label-stack.

  (local (defun ll-input-ok (vars) (declare (ignore vars)) t))
  (local (defun ll-exit? (vars) (declare (ignore vars)) t))
  (local (defun ll-next (vars) vars))
  (local (defun ll-result (vars) (declare (ignore vars)) (make-i32-val 0)))
  (local (defun ll-measure (vars) (declare (ignore vars)) 0))
  (local (defun ll-fn (vars) (declare (ignore vars)) (make-i32-val 0)))
  (local (defun ll-total-fuel (vars) (declare (ignore vars)) 0))
  (local (defun ll-iter-fuel () 0))
  (local (defun ll-exit-fuel () 0))

  (local (defun ll-state-at-header (vars call-tail store)
           (declare (ignore vars))
           (make-state
            :store store
            :call-stack (cons (make-frame
                               :return-arity 1
                               :locals nil
                               :operand-stack (list (make-i32-val 0))
                               :instrs nil
                               :label-stack nil)
                              call-tail)
            :memory nil :globals nil)))

  ;; ---- Fuel is natural --------------------------------------------------

  (defthm natp-of-ll-iter-fuel
    (natp (ll-iter-fuel))
    :rule-classes :type-prescription)

  (defthm natp-of-ll-exit-fuel
    (natp (ll-exit-fuel))
    :rule-classes :type-prescription)

  ;; ---- Measure is a well-founded ordinal and strictly decreases ---------
  ;;
  ;; Unconditional on ll-input-ok so that ll-fn / ll-total-fuel can be
  ;; admitted without a hypothesis in the recursive call.

  (defthm o-p-of-ll-measure
    (o-p (ll-measure vars)))

  (defthm ll-measure-decreases
    (implies (not (ll-exit? vars))
             (o< (ll-measure (ll-next vars)) (ll-measure vars))))

  ;; ---- ll-input-ok is preserved across a single iteration ---------------

  (defthm ll-input-ok-of-ll-next
    (implies (and (ll-input-ok vars)
                  (not (ll-exit? vars)))
             (ll-input-ok (ll-next vars))))

  ;; ---- Defining equations for the user's lifted fn / total-fuel --------
  ;;
  ;; The user is expected to define these as recursive ACL2 functions
  ;; by the obvious clauses; the constraint captures just the equation
  ;; we need for the main induction.

  (defthm ll-fn-eqn
    (equal (ll-fn vars)
           (if (ll-exit? vars)
               (ll-result vars)
             (ll-fn (ll-next vars)))))

  (defthm ll-total-fuel-eqn
    (equal (ll-total-fuel vars)
           (if (ll-exit? vars)
               (ll-exit-fuel)
             (+ (ll-iter-fuel) (ll-total-fuel (ll-next vars))))))

  (defthm natp-of-ll-total-fuel
    (natp (ll-total-fuel vars))
    :rule-classes :type-prescription)

  ;; ---- The header-state is a statep ------------------------------------

  (defthm statep-of-ll-state-at-header
    (implies (and (ll-input-ok vars)
                  (call-stackp call-tail)
                  (storep store))
             (statep (ll-state-at-header vars call-tail store)))
    :hints (("Goal" :in-theory (enable statep call-stackp framep
                                       label-stackp operand-stackp
                                       val-listp valp i32-valp u32p))))

  ;; ---- Iter step: running ll-iter-fuel from the header state ----------
  ;; reaches the header state for the next iter's vars.

  (defthm ll-iter-step
    (implies (and (ll-input-ok vars)
                  (not (ll-exit? vars))
                  (call-stackp call-tail)
                  (storep store))
             (equal (run (ll-iter-fuel)
                         (ll-state-at-header vars call-tail store))
                    (ll-state-at-header (ll-next vars) call-tail store))))

  ;; ---- Exit step: at exit, running ll-exit-fuel leaves ll-result on top
  ;; with empty instrs and label-stack (the standard "body done" shape).

  (defthm ll-exit-step
    (implies (and (ll-input-ok vars)
                  (ll-exit? vars)
                  (call-stackp call-tail)
                  (storep store))
             (and (equal (top-operand
                          (current-operand-stack
                           (run (ll-exit-fuel)
                                (ll-state-at-header vars call-tail store))))
                         (ll-result vars))
                  (not (consp (current-instrs
                               (run (ll-exit-fuel)
                                    (ll-state-at-header vars call-tail store)))))
                  (not (consp (current-label-stack
                               (run (ll-exit-fuel)
                                    (ll-state-at-header vars call-tail store)))))))
    :hints (("Goal"
             :in-theory (enable run top-operand top-frame current-frame
                                current-operand-stack current-instrs
                                current-label-stack make-i32-val))))
  ) ; end encapsulate

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §2. Induction scheme and statep of all visited header states.

(local
 (defun ll-ind (vars call-tail store)
   (declare (xargs :measure (ll-measure vars)
                   :hints (("Goal" :use ((:instance ll-measure-decreases))))))
   (if (ll-exit? vars)
       (list vars call-tail store)
     (ll-ind (ll-next vars) call-tail store))))

(local
 (defthm statep-of-run-at-header-iter
   ;; After running `ll-iter-fuel` steps from a header state, we are in
   ;; another header state, hence a statep.
   (implies (and (ll-input-ok vars)
                 (not (ll-exit? vars))
                 (call-stackp call-tail)
                 (storep store))
            (statep (run (ll-iter-fuel)
                         (ll-state-at-header vars call-tail store))))
   :hints (("Goal"
            :use ((:instance ll-iter-step)
                  (:instance ll-input-ok-of-ll-next)
                  (:instance statep-of-ll-state-at-header
                             (vars (ll-next vars))))
            :in-theory (disable ll-iter-step
                                ll-input-ok-of-ll-next
                                statep-of-ll-state-at-header)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §3. The generic loop-correctness theorem.

(defthm ll-loop-correct
  (implies (and (ll-input-ok vars)
                (call-stackp call-tail)
                (storep store))
           (and (equal (top-operand
                        (current-operand-stack
                         (run (ll-total-fuel vars)
                              (ll-state-at-header vars call-tail store))))
                       (ll-fn vars))
                (not (consp (current-instrs
                             (run (ll-total-fuel vars)
                                  (ll-state-at-header vars call-tail store)))))
                (not (consp (current-label-stack
                             (run (ll-total-fuel vars)
                                  (ll-state-at-header vars call-tail store)))))))
  :hints (("Goal"
           :induct (ll-ind vars call-tail store)
           :in-theory (disable ll-iter-step ll-exit-step
                               ll-fn-eqn ll-total-fuel-eqn
                               statep-of-ll-state-at-header
                               statep-of-run-at-header-iter
                               run-split-when-statep))
          ("Subgoal *1/2"
           ;; Step case: (not (ll-exit? vars)).  Split
           ;; run(iter-fuel + total-fuel(next)) = run(total-fuel(next))
           ;; applied to the post-iter header state, then invoke IH.
           :use ((:instance ll-fn-eqn)
                 (:instance ll-total-fuel-eqn)
                 (:instance ll-iter-step)
                 (:instance statep-of-run-at-header-iter)
                 (:instance run-split-when-statep
                            (m (ll-iter-fuel))
                            (n (ll-total-fuel (ll-next vars)))
                            (state (ll-state-at-header vars call-tail store)))))
          ("Subgoal *1/1"
           ;; Base case: (ll-exit? vars).  Directly from exit-step.
           :use ((:instance ll-exit-step)
                 (:instance ll-fn-eqn)
                 (:instance ll-total-fuel-eqn)))))

(value-triple (cw " - wasm-loop-lifter: ll-loop-correct (Q.E.D.)~%"))
(value-triple (cw "wasm-loop-lifter: loaded.~%"))
