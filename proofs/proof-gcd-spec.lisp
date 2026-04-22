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
