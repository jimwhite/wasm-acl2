;; WASM 1.0 ACL2 — GCD end-to-end correctness specification
;;
;; The WASM program `*gcd-func*` (from tests/test-spot-check.lisp) implements
;; the Euclidean algorithm on unsigned 32-bit integers:
;;
;;     while (b != 0) { t = b; b = a rem_u b; a = t; }
;;     return a;
;;
;; The ACL2 arithmetic book `arithmetic/mod-gcd` already defines the
;; mathematical spec `nonneg-int-gcd` and proves it is the greatest common
;; divisor (largest common divisor, is-common-divisor, etc.).
;;
;; The top-level correctness theorem we want is:
;;
;;     For all u32 a, b, running the WASM gcd implementation on (a, b)
;;     produces the i32 value (nonneg-int-gcd a b).
;;
;; Since `run` takes a fuel argument, we need a step bound large enough
;; to cover the worst case. Euclidean GCD on u32 inputs terminates in
;; O(log phi (min(a,b))) iterations; a safe per-u32-input upper bound is
;; roughly 100 iterations (Fibonacci worst case < 47). Each loop iteration
;; executes ~13 WASM steps plus fixed enter/exit overhead, so 2000 fuel is
;; more than enough for any u32 pair.

(in-package "WASM")
(include-book "../execution")
(include-book "arithmetic/mod-gcd" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The program under test — kept in sync with tests/test-spot-check.lisp

(defconst *gcd-func*
  (make-funcinst
   :param-count 2 :local-count 1 :return-arity 1
   :body (list
          '(:block 0 ((:loop 0 ((:local.get 1)
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
          '(:local.get 0))))

(defun make-gcd-state (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b))
                  :verify-guards nil))
  (make-state
   :store (list *gcd-func*)
   :call-stack (list (make-frame :return-arity 1 :locals nil
                      :operand-stack (list (make-i32-val b) (make-i32-val a))
                      :instrs (list '(:call 0)) :label-stack nil))
   :memory nil :globals nil))

;; Extract final i32 result from a :done payload or terminal state.
(defun get-result (r)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp r) (eq :done (first r)))
      (let* ((st (second r))
             (cs (state->call-stack st))
             (f (car cs)))
        (top-operand (frame->operand-stack f)))
    (if (statep r)
        (top-operand (current-operand-stack r))
      r)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Fuel bound.
;;
;; For u32 inputs, Euclidean GCD iterates at most ~47 times (Fibonacci
;; bound on pairs below 2^32). Each iteration is 13 body steps; loop
;; enter/exit overhead is a small constant. 2000 is a conservative cap.
;;
;; We express this as a defun so it's easy to refine (e.g. to an exact
;; bound) during the proof.

(defun gcd-fuel (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b))
                  :verify-guards nil)
           (ignore a b))
  2000)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Top-level correctness theorem (statement only for now).
;;
;; For every pair of unsigned 32-bit integers a, b, executing the WASM
;; gcd implementation yields (make-i32-val (nonneg-int-gcd a b)).
;;
;; Proof strategy (future work):
;;   1. Define a "gcd-loop-invariant" relating the WASM state after k
;;      loop iterations to (nonneg-int-gcd a0 b0).
;;   2. Prove a stepwise lemma: one loop iteration transforms
;;      locals = (a, b, _) into (b, a mod b, b), preserving
;;      (nonneg-int-gcd local0 local1) = (nonneg-int-gcd a0 b0).
;;   3. Prove termination: (a, b) strictly decreases in the well-founded
;;      measure `b` (as natp), so after finitely many iterations b = 0
;;      and the loop exits with local0 = (nonneg-int-gcd a0 b0).
;;   4. Bound the iteration count by gcd-fuel and discharge the outer run.

(skip-proofs
 (defthm gcd-impl-correct
   (implies (and (unsigned-byte-p 32 a)
                 (unsigned-byte-p 32 b))
            (equal (get-result (run (gcd-fuel a b) (make-gcd-state a b)))
                   (make-i32-val (acl2::nonneg-int-gcd a b))))))

(value-triple (cw "~% - gcd-impl-correct: WASM gcd = nonneg-int-gcd (STATEMENT, proof pending)~%"))
