; wasm-call-wrap.lisp — generic WASM :call → body → return → :done wrapper.
;
; Copyright (C) 2025 Kestrel Institute
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; This book abstracts the four-step "call shell" that surrounds every
; function-body correctness proof:
;
;     call-state ─1→ body-start ─Nfuel→ body-end ─1→ after-return ─1→ :done
;       (S0)      step  (S1)      body    (S2)    rff   (S3)       step (S4)
;
; A user whose program-specific proof has established
;   (a) a single-step `:call 0` that enters the body (S0→S1), and
;   (b) a multi-step body correctness theorem that leaves the callee
;       frame in a "13-conjunct" shape (S1→S2),
; can functionally instantiate `call-to-done` below to obtain the full
; S0→S4 trace, and package it behind a fuel-free `defun-sk` on their end.
;
; The wrap book assumes a (2-param, 1-return, locals-free-caller) calling
; convention.  That matches every WASM function we care about today; the
; callee's local-count is abstract and is not constrained here.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

(in-package "WASM")

(include-book "../execution")
(include-book "wasm-run-utils")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §0. Concrete (non-abstract) caller-frame helpers.
;;
;; These are fixed by the 2-in / 1-out / locals-free-caller calling
;; convention and do not vary with the program.  They are defined
;; BEFORE the encapsulate so that the encapsulate's constraint theorems
;; can mention them in a form that remains valid post-exit.

(defun wrap-popped-frame ()
  ;; Caller frame while callee runs: args popped, instrs still `(:call 0)`
  ;; (return-from-function advances past the :call when the callee exits).
  (declare (xargs :guard t :verify-guards nil))
  (make-frame :return-arity 1
              :locals nil
              :operand-stack (empty-operand-stack)
              :instrs (list '(:call 0))
              :label-stack nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §1. Abstract program signature.
;;
;; Abstract functions (all nullary or binary on the two u32 arguments):
;;
;;   (the-func)          — the funcinst under study; stored at index 0.
;;   (input-ok a b)      — guard on the arguments (typically u32 × u32).
;;   (spec-val a b)      — the expected i32-val result on the operand stack.
;;   (make-call-frame a b) — caller frame with args already pushed and
;;                           instrs = (:call 0).
;;   (make-body-state a b) — state obtained after one step of `:call 0`:
;;                           callee frame on top of the caller-popped frame.
;;   (body-fuel a b)     — number of steps to drive the body to the 13-conjunct
;;                           shape (see §3 below).

(encapsulate
  (((the-func) => *)
   ((input-ok * *) => *)
   ((spec-val * *) => *)
   ((make-call-frame * *) => *)
   ((make-body-state * *) => *)
   ((body-fuel * *) => *))

  ;; ---- Witnesses (local) --------------------------------------------------
  ;; A trivial 2-param, 1-return function whose body is `(:i32.const 0)`;
  ;; running it yields `(make-i32-val 0)` on the operand stack.

  (local (defun the-func ()
           (make-funcinst :param-count 2
                          :local-count 0
                          :return-arity 1
                          :body (list '(:i32.const 0)))))

  (local (defun input-ok (a b)
           (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))))

  (local (defun spec-val (a b)
           (declare (ignore a b))
           (make-i32-val 0)))

  (local (defun make-call-frame (a b)
           (make-frame :return-arity 1
                       :locals nil
                       :operand-stack (list (make-i32-val b) (make-i32-val a))
                       :instrs (list '(:call 0))
                       :label-stack nil)))

  (local (defun make-body-state (a b)
           (make-state
            :store (list (the-func))
            :call-stack
            (list
             ;; Callee frame: locals = (a b) (after top-n-operands reversal),
             ;; body = (:i32.const 0), empty ostack/labels.
             (make-frame :return-arity 1
                         :locals (list (make-i32-val a) (make-i32-val b))
                         :operand-stack (empty-operand-stack)
                         :instrs (list '(:i32.const 0))
                         :label-stack nil)
             ;; Caller frame (popped): instrs still = (:call 0); ret-arity=1.
             (make-frame :return-arity 1
                         :locals nil
                         :operand-stack (empty-operand-stack)
                         :instrs (list '(:call 0))
                         :label-stack nil))
            :memory nil :globals nil)))

  (local (defun body-fuel (a b) (declare (ignore a b)) 1))

  ;; ---- Constraints --------------------------------------------------------

  ;; (1) The-func is a funcinst.
  (defthm funcinstp-of-the-func
    (funcinstp (the-func)))

  ;; (2) Input-ok implies both args are u32.
  (defthm input-ok-implies-u32
    (implies (input-ok a b)
             (and (unsigned-byte-p 32 a)
                  (unsigned-byte-p 32 b)))
    :rule-classes :forward-chaining)

  ;; (3) spec-val returns an i32-val.
  (defthm i32-valp-of-spec-val
    (implies (input-ok a b)
             (i32-valp (spec-val a b))))

  ;; (4) body-fuel is a natural number.
  (defthm natp-of-body-fuel
    (implies (input-ok a b)
             (natp (body-fuel a b)))
    :rule-classes :type-prescription)

  ;; (5) One step of `:call 0` from the call-state enters the body.
  (defthm call-enters-body
    (implies (input-ok a b)
             (equal (run 1 (make-state
                            :store (list (the-func))
                            :call-stack (list (make-call-frame a b))
                            :memory nil :globals nil))
                    (make-body-state a b)))
    :hints (("Goal"
             :in-theory (union-theories
                         (current-theory :here)
                         (append '(execute-call
                                   funcinst->param-count
                                   funcinst->local-count
                                   funcinst->return-arity
                                   funcinst->body)
                                 *wasm-exec-theory*))
             :expand ((:free (n s) (run n s))
                      (:free (n s a) (top-n-operands n s a))))))

  ;; (5b) The body-start state is a statep.  Every well-formed witness
  ;; trivially satisfies this; it is needed to glue the S0→S1→S2 run
  ;; split in §8.
  (defthm statep-of-make-body-state
    (implies (input-ok a b)
             (statep (make-body-state a b)))
    :hints (("Goal"
             :in-theory (union-theories
                         (current-theory :here)
                         (append '(execute-call
                                   funcinst->param-count
                                   funcinst->local-count
                                   funcinst->return-arity
                                   funcinst->body)
                                 *wasm-exec-theory*))
             :expand ((:free (n s) (run n s))
                      (:free (n s a) (top-n-operands n s a))))))

  ;; (6) After `body-fuel` steps from `make-body-state`, the state is in
  ;;     the 13-conjunct "body-end" shape:
  ;;       - current-instrs empty, current-label-stack empty
  ;;       - statep
  ;;       - cdr call-stack = (list (wrap-popped-frame))  (the caller)
  ;;       - top frame's return-arity = 1
  ;;       - store = (list (the-func))
  ;;       - call-stack non-empty
  ;;       - top frame's operand-stack non-empty, height ≥ 1
  ;;       - memory = globals = table = nil
  ;;       - top-operand = spec-val a b
  ;;
  ;; The "popped caller frame" is the one sitting underneath the callee
  ;; during the body run, and resurfaces on return.  It has a fixed
  ;; shape set by the calling convention; see `wrap-popped-frame` above.

  (defthm body-shape-after-fuel
    (implies (input-ok a b)
             (and (not (consp (current-instrs
                               (run (body-fuel a b) (make-body-state a b)))))
                  (not (consp (current-label-stack
                               (run (body-fuel a b) (make-body-state a b)))))
                  (statep (run (body-fuel a b) (make-body-state a b)))
                  (equal (cdr (state->call-stack
                               (run (body-fuel a b) (make-body-state a b))))
                         (list (wrap-popped-frame)))
                  (equal (frame->return-arity
                          (car (state->call-stack
                                (run (body-fuel a b) (make-body-state a b)))))
                         1)
                  (equal (state->store
                          (run (body-fuel a b) (make-body-state a b)))
                         (list (the-func)))
                  (consp (state->call-stack
                          (run (body-fuel a b) (make-body-state a b))))
                  (consp (frame->operand-stack
                          (car (state->call-stack
                                (run (body-fuel a b) (make-body-state a b))))))
                  (<= 1 (operand-stack-height
                         (frame->operand-stack
                          (car (state->call-stack
                                (run (body-fuel a b) (make-body-state a b)))))))
                  (equal (state->memory
                          (run (body-fuel a b) (make-body-state a b)))
                         nil)
                  (equal (state->globals
                          (run (body-fuel a b) (make-body-state a b)))
                         nil)
                  (equal (state->table
                          (run (body-fuel a b) (make-body-state a b)))
                         nil)
                  (equal (top-operand
                          (current-operand-stack
                           (run (body-fuel a b) (make-body-state a b))))
                         (spec-val a b))))
    :hints (("Goal"
             :in-theory (union-theories
                         (current-theory :here)
                         (append '(execute-instr execute-i32.const
                                   funcinst->param-count
                                   funcinst->local-count
                                   funcinst->return-arity
                                   funcinst->body)
                                 *wasm-exec-theory*))
             :expand ((:free (n s) (run n s))))))
  ) ; end encapsulate

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §2. Concrete scaffolding: the caller frame after return, and the
;; overall call-state / body-end-state abbreviations.

(defun wrap-final-frame (a b)
  ;; Caller frame after return-from-function: result pushed, instrs nil.
  (declare (xargs :guard (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
                  :verify-guards nil))
  (make-frame :return-arity 1
              :locals nil
              :operand-stack (list (spec-val a b))
              :instrs nil
              :label-stack nil))

(defun wrap-call-state (a b)
  ;; The starting state: one caller frame with args pushed, about to :call.
  (declare (xargs :guard (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
                  :verify-guards nil))
  (make-state
   :store (list (the-func))
   :call-stack (list (make-call-frame a b))
   :memory nil :globals nil))

(defun wrap-body-end-state (a b)
  ;; Abbreviation: the post-body state that body-shape-after-fuel describes.
  (declare (xargs :verify-guards nil))
  (run (body-fuel a b) (make-body-state a b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §4. Derivations: statep glue.

(local
 (defthm statep-of-wrap-call-state
   (implies (and (input-ok a b)
                 (framep (make-call-frame a b)))
            (statep (wrap-call-state a b)))
   :hints (("Goal" :in-theory (enable statep call-stackp funcinst-listp
                                      wrap-call-state)))))

(local
 (defthm statep-after-body-run
   (implies (input-ok a b)
            (statep (wrap-body-end-state a b)))
   :hints (("Goal"
            :use ((:instance body-shape-after-fuel (a a) (b b)))
            :in-theory (e/d (wrap-body-end-state)
                            (body-shape-after-fuel))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §5. Return-from-function step (S2 → S3).
;;
;; After `body-fuel` steps from `make-body-state`, the call-stack has
;; two frames: callee on top (instrs nil, labels nil, one value on ostack)
;; and `wrap-popped-frame` underneath.  One more step triggers
;; `return-from-function`, which pops the callee, pushes the returned
;; value onto the caller's ostack, and advances the caller past `:call 0`.
;; The resulting state has a single frame = `wrap-final-frame`.

(local
 (defthm run-1-from-body-end
   (implies (input-ok a b)
            (equal (run 1 (wrap-body-end-state a b))
                   (make-state
                    :store (list (the-func))
                    :call-stack (list (wrap-final-frame a b))
                    :memory nil :globals nil)))
   :hints (("Goal"
            :do-not-induct t
            :do-not '(generalize fertilize)
            :use ((:instance body-shape-after-fuel (a a) (b b)))
            :expand ((:free (stack) (top-n-operands 1 stack nil))
                     (:free (stack acc) (top-n-operands 0 stack acc))
                     (:free (v rest stack) (push-vals (cons v rest) stack))
                     (:free (stack) (push-vals nil stack))
                     (:free (s) (run 1 s)))
            :in-theory (e/d (return-from-function
                             pop-call-stack push-call-stack push-vals
                             top-n-operands top-operand push-operand
                             pop-operand
                             operand-stack-height
                             current-frame current-instrs current-operand-stack
                             current-label-stack top-frame
                             update-current-operand-stack
                             update-current-instrs
                             wrap-final-frame
                             wrap-popped-frame
                             wrap-body-end-state)
                            (body-shape-after-fuel))))))

(value-triple (cw " - wasm-call-wrap: run-1-from-body-end (S2 → S3) (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §6. Final step (S3 → :done).
;;
;; From a single-frame state with instrs=nil and label-stack=nil, `run`
;; signals `(:done <state>)` after one step.

(local
 (defthm framep-of-wrap-final-frame
   (implies (input-ok a b)
            (framep (wrap-final-frame a b)))
   :hints (("Goal"
            :use ((:instance i32-valp-of-spec-val (a a) (b b)))
            :in-theory (e/d (framep label-stackp operand-stackp
                                    val-listp valp wrap-final-frame)
                            (i32-valp-of-spec-val))))))

(local
 (defthm run-1-from-after-return
   (implies (input-ok a b)
            (equal (run 1 (make-state
                           :store (list (the-func))
                           :call-stack (list (wrap-final-frame a b))
                           :memory nil :globals nil))
                   `(:done ,(make-state
                             :store (list (the-func))
                             :call-stack (list (wrap-final-frame a b))
                             :memory nil :globals nil))))
   :hints (("Goal"
            :in-theory (e/d (return-from-function
                             current-instrs current-label-stack
                             current-frame top-frame
                             state->call-stack
                             frame->instrs frame->label-stack
                             frame->operand-stack
                             wrap-final-frame)
                            nil)
            :expand ((:free (s) (run 1 s)))))))

(value-triple (cw " - wasm-call-wrap: run-1-from-after-return (S3 → :done) (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §7. Gluing lemmas: statep after S2→S3, and the 2-step S2→:done chain.

(local
 (defthm not-equal-done-car-when-statep
   (implies (statep x)
            (not (equal :done (car x))))
   :hints (("Goal"
            :use ((:instance not-statep-of-done (x (cdr x))))
            :in-theory (disable not-statep-of-done)))))

(local
 (defthm statep-of-wrap-final-state
   (implies (input-ok a b)
            (statep (make-state :store (list (the-func))
                                :call-stack (list (wrap-final-frame a b))
                                :memory nil :globals nil)))
   :hints (("Goal"
            :use ((:instance framep-of-wrap-final-frame (a a) (b b))
                  (:instance funcinstp-of-the-func)
                  (:instance i32-valp-of-spec-val (a a) (b b)))
            :in-theory (e/d (statep call-stackp funcinst-listp
                                    operand-stackp val-listp valp)
                            (framep-of-wrap-final-frame
                             funcinstp-of-the-func
                             i32-valp-of-spec-val))))))

(local
 (defthm statep-of-run-1-from-body-end
   (implies (input-ok a b)
            (statep (run 1 (wrap-body-end-state a b))))
   :hints (("Goal"
            :use ((:instance run-1-from-body-end (a a) (b b))
                  (:instance statep-of-wrap-final-state (a a) (b b)))
            :in-theory (union-theories
                        (theory 'minimal-theory)
                        '(run-1-from-body-end
                          statep-of-wrap-final-state))))))

(local
 (defthm run-2-from-body-end
   (implies (input-ok a b)
            (equal (run 2 (wrap-body-end-state a b))
                   `(:done ,(make-state
                             :store (list (the-func))
                             :call-stack (list (wrap-final-frame a b))
                             :memory nil :globals nil))))
   :hints (("Goal"
            :do-not-induct t
            :do-not '(generalize fertilize)
            :use ((:instance run-1-from-body-end (a a) (b b))
                  (:instance run-1-from-after-return (a a) (b b))
                  (:instance statep-of-run-1-from-body-end (a a) (b b)))
            :expand ((:free (s) (run 2 s))
                     (:free (s) (run 1 s)))
            :in-theory (e/d (current-instrs current-label-stack)
                            (run-1-from-body-end
                             run-1-from-after-return
                             statep-of-run-1-from-body-end
                             wrap-body-end-state
                             wrap-final-frame))))))

(value-triple (cw " - wasm-call-wrap: run-2-from-body-end (S2 → :done) (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §8. End-to-end: call-state → :done in (3 + body-fuel) steps.
;;
;; We split the run across S0→S1 (call-enters-body), S1→S2 (body-shape
;; via run-split-when-statep), and S2→S4 (run-2-from-body-end).

(defthm call-to-done
  (implies (and (input-ok a b)
                (framep (make-call-frame a b)))
           (equal (run (+ 3 (body-fuel a b)) (wrap-call-state a b))
                  `(:done ,(make-state
                            :store (list (the-func))
                            :call-stack (list (wrap-final-frame a b))
                            :memory nil :globals nil))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(generalize fertilize)
           :use ((:instance call-enters-body (a a) (b b))
                 (:instance statep-of-wrap-call-state (a a) (b b))
                 (:instance statep-after-body-run (a a) (b b))
                 (:instance run-2-from-body-end (a a) (b b))
                 (:instance run-split-when-statep
                            (m 1)
                            (n (+ 2 (body-fuel a b)))
                            (state (wrap-call-state a b)))
                 (:instance run-split-when-statep
                            (m (body-fuel a b))
                            (n 2)
                            (state (make-body-state a b))))
           :in-theory (e/d (wrap-body-end-state
                            wrap-call-state)
                           (call-enters-body
                            statep-of-wrap-call-state
                            statep-after-body-run
                            run-2-from-body-end
                            run-split-when-statep
                            wrap-final-frame
                            (:definition run))))))

(value-triple (cw " - wasm-call-wrap: call-to-done (S0 → :done) (Q.E.D.)~%"))
(value-triple (cw "wasm-call-wrap: loaded.~%"))
