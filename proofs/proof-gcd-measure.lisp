; proof-gcd-measure.lisp — GCD correctness via measure-based semantics.
;
; Copyright (C) 2025 Kestrel Institute
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Companion to `proof-gcd-spec.lisp`.  Where the latter characterises
; GCD's trajectory through the interpreter by an explicit fuel
; `gcd-total-fuel`, this book re-proves the same correctness result
; via the generic framework in `wasm-measure-semantics.lisp`.
;
; GCD-specific content:
;
;   REACHABLE    The set of "loop-entry" machine states: the callee's
;                instruction pointer is at the top of the Euclidean
;                loop body, locals are (a, b, tmp) with u32 values,
;                label-stack holds the (loop, block) pair, operand
;                stack is empty.  The canonical caller frame below
;                the callee is `wrap-popped-frame` from the call-wrap
;                book; the store is `*gcd-store*`.
;
;   MSTEP        A variable big-step:
;                   b ≠ 0 : run 13 — one full loop iteration.
;                   b = 0 : run 6  — 4 exit steps + return-from-function
;                                    + final step that produces (:done ...).
;
;   STATE-MEASURE   ω · (b + 1).  One ω per potential iteration, indexed
;                   by the strictly-decreasing Euclidean b.
;
; Final exported theorem: from any reachable state there exists a
; natural N such that (run N state) is (:done ...), i.e. the WASM
; program halts successfully — without the theorem statement itself
; mentioning any fuel function.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

(in-package "WASM")

(include-book "../execution")
(include-book "wasm-run-utils")
(include-book "wasm-arith-utils")
(include-book "wasm-measure-semantics")
(include-book "wasm-call-wrap")
(include-book "proof-gcd-spec")

(local (include-book "arithmetic-5/top" :dir :system))

(set-induction-depth-limit 1)
(set-verify-guards-eagerness 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §1.  Canonical call-tail and post-return skeleton.

(defund gcd-call-tail ()
  (list (wrap-popped-frame)))

(defund gcd-after-return-state (a)
  (make-state
   :store *gcd-store*
   :call-stack (list (make-frame
                      :return-arity 1
                      :locals nil
                      :operand-stack (list (make-i32-val a))
                      :instrs nil
                      :label-stack nil))
   :memory nil :globals nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §2.  Six-step exit lemma: from LOOP-ENTRY(a, 0, tmp) the interpreter
;; reaches the final (:done ...) value in exactly 6 real run steps.

(defthm loop-entry-exit-6
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 tmp))
           (equal (run 6 (make-loop-entry-state a 0 tmp
                                                (gcd-call-tail)
                                                *gcd-store*))
                  `(:done ,(gcd-after-return-state a))))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here)
                                      (append '(gcd-call-tail
                                                gcd-after-return-state
                                                wrap-popped-frame)
                                              *wasm-exec-theory*))
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))
                    (:free (n s a) (top-n-operands n s a))
                    (:free (n s) (pop-n-labels n s))
                    (:free (v s) (push-vals v s))))))

(value-triple (cw "proof-gcd-measure: loop-entry-exit-6 established.~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §3.  Reachable predicate via a 3-element u32 witness list.

(defun-sk gcd-reachable-fn (s)
  (exists (abt)
    (and (true-listp abt)
         (equal (len abt) 3)
         (unsigned-byte-p 32 (nth 0 abt))
         (unsigned-byte-p 32 (nth 1 abt))
         (unsigned-byte-p 32 (nth 2 abt))
         (equal s (make-loop-entry-state (nth 0 abt)
                                         (nth 1 abt)
                                         (nth 2 abt)
                                         (gcd-call-tail)
                                         *gcd-store*)))))

(defund gcd-reachable (s)
  (gcd-reachable-fn s))

(defund gcd-a (s)
  (nth 0 (gcd-reachable-fn-witness s)))
(defund gcd-b (s)
  (nth 1 (gcd-reachable-fn-witness s)))
(defund gcd-tmp (s)
  (nth 2 (gcd-reachable-fn-witness s)))

(defthm gcd-reachable-u32-a
  (implies (gcd-reachable s)
           (unsigned-byte-p 32 (gcd-a s)))
  :hints (("Goal" :in-theory (enable gcd-reachable gcd-a))))

(defthm natp-of-gcd-a-when-reachable
  (implies (gcd-reachable s)
           (natp (gcd-a s)))
  :rule-classes (:rewrite :type-prescription :forward-chaining)
  :hints (("Goal" :use (:instance gcd-reachable-u32-a)
                  :in-theory (disable gcd-reachable-u32-a))))

(defthm gcd-reachable-u32-b
  (implies (gcd-reachable s)
           (unsigned-byte-p 32 (gcd-b s)))
  :hints (("Goal" :in-theory (enable gcd-reachable gcd-b))))

(defthm natp-of-gcd-b-when-reachable
  (implies (gcd-reachable s)
           (natp (gcd-b s)))
  :rule-classes (:rewrite :type-prescription :forward-chaining)
  :hints (("Goal" :use (:instance gcd-reachable-u32-b)
                  :in-theory (disable gcd-reachable-u32-b))))

(defthm gcd-reachable-u32-tmp
  (implies (gcd-reachable s)
           (unsigned-byte-p 32 (gcd-tmp s)))
  :hints (("Goal" :in-theory (enable gcd-reachable gcd-tmp))))

(defthm gcd-reachable-canonical
  (implies (gcd-reachable s)
           (equal s
                  (make-loop-entry-state (gcd-a s) (gcd-b s) (gcd-tmp s)
                                         (gcd-call-tail)
                                         *gcd-store*)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable gcd-reachable gcd-a gcd-b gcd-tmp))))

(local (defthm call-stackp-of-gcd-call-tail
         (call-stackp (gcd-call-tail))
         :hints (("Goal" :in-theory (enable gcd-call-tail call-stackp framep
                                            label-stackp operand-stackp
                                            val-listp wrap-popped-frame)))))

(local (defthm storep-of-gcd-store
         (storep *gcd-store*)))

(local (defthm statep-of-make-loop-entry-state-local
         (implies (and (unsigned-byte-p 32 a)
                       (unsigned-byte-p 32 b)
                       (unsigned-byte-p 32 tmp)
                       (call-stackp call-tail)
                       (storep store))
                  (statep (make-loop-entry-state a b tmp call-tail store)))
         :hints (("Goal" :in-theory (enable statep call-stackp framep
                                            label-stackp label-entryp
                                            operand-stackp val-listp
                                            i32-valp u32p)))))

(defthm statep-when-gcd-reachable
  (implies (gcd-reachable s)
           (statep s))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :use ((:instance gcd-reachable-canonical)
                 (:instance statep-of-make-loop-entry-state-local
                            (a (gcd-a s)) (b (gcd-b s)) (tmp (gcd-tmp s))
                            (call-tail (gcd-call-tail))
                            (store *gcd-store*)))
           :in-theory (disable gcd-reachable))))

(value-triple (cw "proof-gcd-measure: reachable predicate defined.~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §4.  Coarse mstep and ordinal measure.

(defund gcd-mstep-count (s)
  (if (gcd-reachable s)
      (if (equal (gcd-b s) 0) 6 13)
    0))

(defthm natp-of-gcd-mstep-count
  (natp (gcd-mstep-count s))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable gcd-mstep-count))))

(defund gcd-mstep (s)
  (run (gcd-mstep-count s) s))

(defthm gcd-mstep-is-run
  (equal (gcd-mstep s)
         (run (gcd-mstep-count s) s))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable gcd-mstep))))

(defund gcd-meas-b (s)
  (declare (xargs :verify-guards nil))
  (nfix (cadr (nth 1 (frame->locals (car (state->call-stack s)))))))

(defthm natp-of-gcd-meas-b
  (natp (gcd-meas-b s))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable gcd-meas-b))))

(local (defthm gcd-meas-b-of-make-loop-entry-state
  (implies (unsigned-byte-p 32 b)
           (equal (gcd-meas-b (make-loop-entry-state a b c ct st))
                  b))
  :hints (("Goal" :in-theory (enable gcd-meas-b make-i32-val
                                     make-loop-entry-state)))))

(local (defthm gcd-meas-b-when-reachable
  (implies (and (syntaxp (not (and (consp s)
                                   (eq (car s) 'make-loop-entry-state))))
                (gcd-reachable s))
           (equal (gcd-meas-b s) (gcd-b s)))
  :hints (("Goal"
           :use ((:instance gcd-reachable-canonical)
                 (:instance gcd-reachable-u32-b)
                 (:instance gcd-meas-b-of-make-loop-entry-state
                            (a (gcd-a s)) (b (gcd-b s)) (c (gcd-tmp s))
                            (ct (gcd-call-tail)) (st *gcd-store*)))
           :in-theory (disable gcd-meas-b-of-make-loop-entry-state)))))

(defund gcd-state-measure (s)
  (if (gcd-reachable s)
      (+ 1 (gcd-meas-b s))
    0))

(defthm natp-of-gcd-state-measure
  (natp (gcd-state-measure s))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable gcd-state-measure))))

(defthm o-p-of-gcd-state-measure
  (o-p (gcd-state-measure s))
  :hints (("Goal" :in-theory (enable gcd-state-measure))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §5.  Transition lemmas.

(defthm gcd-mstep-when-b-nonzero
  (implies (and (gcd-reachable s)
                (not (equal (gcd-b s) 0)))
           (equal (gcd-mstep s)
                  (make-loop-entry-state (gcd-b s)
                                         (mod (gcd-a s) (gcd-b s))
                                         (gcd-b s)
                                         (gcd-call-tail)
                                         *gcd-store*)))
  :hints (("Goal"
           :use ((:instance gcd-reachable-canonical)
                 (:instance loop-entry-step-case
                            (a (gcd-a s)) (b (gcd-b s)) (tmp (gcd-tmp s))
                            (call-tail (gcd-call-tail))
                            (store *gcd-store*)))
           :in-theory (e/d (gcd-mstep gcd-mstep-count)
                           (loop-entry-step-case
                            gcd-reachable)))))

(defthm gcd-mstep-when-b-zero
  (implies (and (gcd-reachable s)
                (equal (gcd-b s) 0))
           (equal (gcd-mstep s)
                  `(:done ,(gcd-after-return-state (gcd-a s)))))
  :hints (("Goal"
           :use ((:instance gcd-reachable-canonical)
                 (:instance loop-entry-exit-6
                            (a (gcd-a s)) (tmp (gcd-tmp s))))
           :in-theory (e/d (gcd-mstep gcd-mstep-count)
                           (loop-entry-exit-6
                            gcd-reachable)))))

(defthm gcd-reachable-of-next-iteration
  (implies (and (gcd-reachable s)
                (not (equal (gcd-b s) 0)))
           (gcd-reachable
            (make-loop-entry-state (gcd-b s)
                                   (mod (gcd-a s) (gcd-b s))
                                   (gcd-b s)
                                   (gcd-call-tail)
                                   *gcd-store*)))
  :hints (("Goal"
           :use ((:instance gcd-reachable-fn-suff
                            (abt (list (gcd-b s)
                                       (mod (gcd-a s) (gcd-b s))
                                       (gcd-b s)))
                            (s (make-loop-entry-state
                                (gcd-b s)
                                (mod (gcd-a s) (gcd-b s))
                                (gcd-b s)
                                (gcd-call-tail)
                                *gcd-store*)))
                 (:instance gcd-reachable-canonical)
                 (:instance u32p-of-mod (a (gcd-a s)) (b (gcd-b s))))
           :in-theory (e/d (gcd-reachable u32p)
                           (u32p-of-mod)))))

(defthm not-terminalp-when-gcd-reachable
  (implies (gcd-reachable s)
           (not (terminalp s)))
  :hints (("Goal"
           :use ((:instance statep-when-gcd-reachable)))))

;; Reachability preservation.
(defthm gcd-reachable-preserved
  (implies (and (gcd-reachable s)
                (not (terminalp s))
                (not (terminalp (gcd-mstep s))))
           (gcd-reachable (gcd-mstep s)))
  :hints (("Goal"
           :cases ((equal (gcd-b s) 0))
           :use ((:instance gcd-reachable-of-next-iteration))
           :in-theory (e/d (terminalp done-statep trapp)
                           (gcd-reachable-of-next-iteration)))))

(local (defthm not-statep-of-done
  (not (statep (cons :done x)))
  :hints (("Goal" :in-theory (enable statep)))))

(defthm not-gcd-reachable-of-done
  (not (gcd-reachable (cons :done x)))
  :hints (("Goal"
           :use (:instance statep-when-gcd-reachable (s (cons :done x)))
           :in-theory (disable statep-when-gcd-reachable))))

;; Measure decrease.
(defthm gcd-measure-decreases
  (implies (and (gcd-reachable s)
                (not (terminalp s)))
           (o< (gcd-state-measure (gcd-mstep s))
               (gcd-state-measure s)))
  :hints (("Goal"
           :cases ((equal (gcd-b s) 0))
           :in-theory (disable make-loop-entry-state))
          ("Subgoal 2"
           ;; b = 0: mstep lands on (:done ...) which is not reachable.
           :use ((:instance gcd-mstep-when-b-zero))
           :in-theory (e/d (gcd-state-measure)
                           (gcd-mstep-when-b-zero make-loop-entry-state)))
          ("Subgoal 1"
           ;; b /= 0: new b = (mod a b) < b.
           :use ((:instance gcd-mstep-when-b-nonzero)
                 (:instance u32p-of-mod (a (gcd-a s)) (b (gcd-b s)))
                 (:instance gcd-meas-b-when-reachable))
           :in-theory (e/d (gcd-state-measure u32p)
                           (gcd-mstep-when-b-nonzero
                            u32p-of-mod
                            gcd-meas-b-when-reachable
                            make-loop-entry-state)))))

(defthm gcd-mstep-statep-or-terminalp
  (implies (gcd-reachable s)
           (or (statep (gcd-mstep s))
               (terminalp (gcd-mstep s))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((equal (gcd-b s) 0))
           :use ((:instance gcd-reachable-of-next-iteration)
                 (:instance statep-when-gcd-reachable
                            (s (make-loop-entry-state
                                (gcd-b s) (mod (gcd-a s) (gcd-b s))
                                (gcd-b s) (gcd-call-tail) *gcd-store*)))))))

(defthm gcd-mstep-count-positive
  (implies (and (gcd-reachable s)
                (not (terminalp s)))
           (< 0 (gcd-mstep-count s)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable gcd-mstep-count))))

(value-triple (cw "proof-gcd-measure: framework constraints discharged.~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §6.  Functional instantiation of the framework's termination theorem.

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

(defthm gcd-run-reaches-terminal
  (implies (gcd-reachable s)
           (and (natp (gcd-run-to-terminal-fuel s))
                (terminalp (run (gcd-run-to-terminal-fuel s) s))))
  :hints (("Goal"
           :use ((:functional-instance
                  run-reaches-terminal-from-reachable
                  (mstep               gcd-mstep)
                  (mstep-count         gcd-mstep-count)
                  (reachable           gcd-reachable)
                  (state-measure       gcd-state-measure)
                  (run-to-terminal-fuel gcd-run-to-terminal-fuel)))
           :in-theory (disable run-reaches-terminal-from-reachable))
          ;; Computed hint: at every unresolved subgoal, supply the
          ;; key non-rewrite lemmas.
          (and stable-under-simplificationp
               '(:use ((:instance gcd-mstep-is-run)
                       (:instance gcd-mstep-statep-or-terminalp)
                       (:instance gcd-measure-decreases)
                       (:instance gcd-reachable-preserved))
                 :expand ((gcd-run-to-terminal-fuel s))
                 :in-theory (enable gcd-mstep-count)))))

(value-triple (cw "proof-gcd-measure: functional instance (termination) discharged.~%"))
