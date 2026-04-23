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
(include-book "wasm-run-utils")    ; run-split-when-statep, *wasm-exec-theory*, not-statep-of-*
(include-book "wasm-arith-utils") ; u32p-of-mod, bvmod-32-when-u32, nonneg-int-* bridges
(include-book "wasm-loader")     ; load-wasm-funcinsts: .wasm -> (funcinst ...)

;; arithmetic-5/top is needed locally to discharge the termination measure
;; `(< (mod a b) b)` for gcd-loop-fuel and for linear-arith goals on mod
;; that are not covered by wasm-arith-utils' published rewrites.
(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The program under test is loaded directly from the .wasm binary
;; produced by `wat2wasm tests/oracle/gcd.wat`. The WAT source is the
;; canonical definition of the program; this book parses the binary at
;; certification time rather than hand-transcribing the instruction list.
;;
;; Pipeline:  gcd.wat -(wat2wasm)-> gcd.wasm -(parse-binary)-> sections
;;            -(module->funcinsts)-> (list *gcd-func*)

(make-event
 (mv-let (erp funcs acl2::state)
   (load-wasm-funcinsts "../tests/oracle/gcd.wasm" acl2::state)
   (if erp
       (mv (msg "Failed to load gcd.wasm: ~x0" erp) nil acl2::state)
     (mv nil
         `(progn
            (defconst *gcd-func* ',(first funcs))
            (defconst *gcd-body* ',(funcinst->body (first funcs))))
         acl2::state))))

(defun make-gcd-state (a b call-tail store)
  ;; `call-tail` is the list of additional (caller) frames beneath the
  ;; gcd frame; `store` is the function store.  None of the gcd body's
  ;; instructions touch either — they're plumbed through generically so
  ;; the internal correctness theorem can be lifted to `*gcd-func*`.
  (declare (xargs :guard (and (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b))
                  :verify-guards nil))
  (make-state
   :store store
   :call-stack (cons (make-frame
                      :return-arity 1
                      :locals (list (make-i32-val a)
                                    (make-i32-val b)
                                    (make-i32-val 0))
                      :operand-stack (empty-operand-stack)
                      :instrs *gcd-body*
                      :label-stack nil)
                     call-tail)
   :memory nil :globals nil))

(defun gcd-result (st)
  (declare (xargs :guard (statep st) :verify-guards nil))
  (top-operand (current-operand-stack st)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theory for symbolic execution (mirrors proof-loop-spec.lisp /
;; proof-abs-e2e.lisp).

;; Symbolic-execution enable list: the reusable one from wasm-run-utils.
;; (We defer handling of `:call`/`execute-call` until the lift-to-*gcd-func*
;; section below, which enables those as extra rules in its own hints.)
(local (defconst *gcd-exec-theory* *wasm-exec-theory*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 1: Base case. When b = 0, running the WASM gcd returns a.

(defthm gcd-impl-base-case
  (implies (unsigned-byte-p 32 a)
           (equal (top-operand
                   (current-operand-stack
                    (run 6 (make-gcd-state a 0 call-tail store))))
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

(defun make-loop-entry-state (a b tmp call-tail store)
  (declare (xargs :guard (and (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b)
                              (unsigned-byte-p 32 tmp))
                  :verify-guards nil))
  (make-state
   :store store
   :call-stack (cons (make-frame
                      :return-arity 1
                      :locals (list (make-i32-val a)
                                    (make-i32-val b)
                                    (make-i32-val tmp))
                      :operand-stack (empty-operand-stack)
                      :instrs *gcd-loop-body*
                      :label-stack (list *gcd-loop-label* *gcd-block-label*))
                     call-tail)
   :memory nil :globals nil))

;; Sanity: running 2 steps from a fresh gcd-state gives the corresponding
;; loop-entry-state.
(defthm gcd-state-to-loop-entry
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (equal (run 2 (make-gcd-state a b call-tail store))
                  (make-loop-entry-state a b 0 call-tail store)))
  :hints (("Goal"
           :in-theory (union-theories (current-theory :here) *gcd-exec-theory*)
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))))))

(value-triple (cw " - gcd-state-to-loop-entry: 2 steps reach loop entry (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Step case: from a loop-entry state with b ≠ 0, 13 steps reach
;; loop-entry(b, (mod a b), b).
;;
;; The u32p/bvmod bridge lemmas live in `wasm-arith-utils.lisp`.

(defthm loop-entry-step-case
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (unsigned-byte-p 32 tmp)
                (not (equal b 0)))
           (equal (run 13 (make-loop-entry-state a b tmp call-tail store))
                  (make-loop-entry-state b (mod a b) b call-tail store)))
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
           (and (equal (top-operand
                        (current-operand-stack
                         (run 4 (make-loop-entry-state a 0 tmp call-tail store))))
                       (make-i32-val a))
                ;; Body has finished: no more instrs, no labels outstanding.
                (not (consp (current-instrs
                             (run 4 (make-loop-entry-state a 0 tmp call-tail store)))))
                (not (consp (current-label-stack
                             (run 4 (make-loop-entry-state a 0 tmp call-tail store)))))))
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
;; Run-split and non-arithmetic bridge lemmas live in wasm-run-utils and
;; wasm-arith-utils; see those files.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; statep-ness of a loop-entry state (needed to discharge the hyp of
;; run-split-when-statep after taking 13 steps).

(local (defthm statep-of-make-loop-entry-state
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Combined run/step rewrite: one loop iteration, distributed into
;; additional fuel.  This avoids forcing rounds over statep during the
;; main induction.

(defthm run-plus-at-loop-entry
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (unsigned-byte-p 32 tmp)
                (call-stackp call-tail)
                (storep store)
                (not (equal b 0))
                (natp n))
           (equal (run (+ 13 n) (make-loop-entry-state a b tmp call-tail store))
                  (run n (make-loop-entry-state b (mod a b) b call-tail store))))
  :hints (("Goal"
           :do-not '(generalize fertilize eliminate-destructors)
           :do-not-induct t
           :use ((:instance loop-entry-step-case
                            (a a) (b b) (tmp tmp)
                            (call-tail call-tail) (store store))
                 (:instance run-split-when-statep
                            (m 13) (n n)
                            (state (make-loop-entry-state a b tmp call-tail store)))
                 (:instance statep-of-make-loop-entry-state
                            (a a) (b b) (tmp tmp)
                            (call-tail call-tail) (store store))
                 (:instance statep-of-make-loop-entry-state
                            (a b) (b (mod a b)) (tmp b)
                            (call-tail call-tail) (store store))
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
                (unsigned-byte-p 32 tmp)
                (call-stackp call-tail)
                (storep store))
           (equal (top-operand
                   (current-operand-stack
                    (run (gcd-loop-fuel a b)
                         (make-loop-entry-state a b tmp call-tail store))))
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
           :use ((:instance loop-entry-base-case
                            (a a) (tmp tmp)
                            (call-tail call-tail) (store store))))))

(value-triple (cw " - gcd-loop-entry-correct: top-operand = nonneg-int-gcd for all u32 (a,b) (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parallel theorem: after running the body, the current frame has no
;; more instrs and no outstanding labels — i.e. the body is "done" and
;; ready to trigger `return-from-function`.

(defthm gcd-loop-entry-done-shape
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (unsigned-byte-p 32 tmp)
                (call-stackp call-tail)
                (storep store))
           (and (not (consp (current-instrs
                             (run (gcd-loop-fuel a b)
                                  (make-loop-entry-state a b tmp call-tail store)))))
                (not (consp (current-label-stack
                             (run (gcd-loop-fuel a b)
                                  (make-loop-entry-state a b tmp call-tail store)))))))
  :hints (("Goal"
           :induct (gcd-loop-ind a b tmp)
           :in-theory (disable loop-entry-step-case
                               loop-entry-base-case
                               run-split-when-statep
                               statep-of-make-loop-entry-state
                               make-loop-entry-state
                               (:induction gcd-loop-fuel)))
          ("Subgoal *1/1"
           :use ((:instance loop-entry-base-case
                            (a a) (tmp tmp)
                            (call-tail call-tail) (store store))))))

(value-triple (cw " - gcd-loop-entry-done-shape: body ends with empty instrs/labels (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Preservation lemmas: the caller tail, the callee frame's return-arity,
;; and the store are unchanged across body execution.  These are needed
;; to drive `return-from-function` on the final wrap-up steps.

;; First, strengthen loop-entry-base-case with preservation conjuncts.
;; (We keep the original as-is and prove these independently.)
(local
 (defthm loop-entry-base-case-preservation
   (implies (and (unsigned-byte-p 32 a)
                 (unsigned-byte-p 32 tmp)
                 (call-stackp call-tail)
                 (storep store))
            (and (statep (run 4 (make-loop-entry-state a 0 tmp call-tail store)))
                 (equal (cdr (state->call-stack
                              (run 4 (make-loop-entry-state a 0 tmp call-tail store))))
                        call-tail)
                 (equal (frame->return-arity
                         (car (state->call-stack
                               (run 4 (make-loop-entry-state a 0 tmp call-tail store)))))
                        1)
                 (equal (state->store
                         (run 4 (make-loop-entry-state a 0 tmp call-tail store)))
                        store)
                 (consp (state->call-stack
                         (run 4 (make-loop-entry-state a 0 tmp call-tail store))))
                 (consp (frame->operand-stack
                         (car (state->call-stack
                               (run 4 (make-loop-entry-state a 0 tmp call-tail store))))))
                 (<= 1 (operand-stack-height
                        (frame->operand-stack
                         (car (state->call-stack
                               (run 4 (make-loop-entry-state a 0 tmp call-tail store)))))))
                 (equal (state->memory
                         (run 4 (make-loop-entry-state a 0 tmp call-tail store)))
                        nil)
                 (equal (state->globals
                         (run 4 (make-loop-entry-state a 0 tmp call-tail store)))
                        nil)
                 (equal (state->table
                         (run 4 (make-loop-entry-state a 0 tmp call-tail store)))
                        nil)))
   :hints (("Goal"
            :in-theory (union-theories (current-theory :here)
                                       (append '(statep framep
                                                 label-stackp label-entryp
                                                 operand-stackp val-listp
                                                 i32-valp u32p)
                                               *gcd-exec-theory*))
            :do-not '(generalize)
            :expand ((:free (n s) (run n s))
                     (:free (n s a) (top-n-operands n s a))
                     (:free (n s) (pop-n-labels n s))
                     (:free (v s) (push-vals v s)))))))

(defthm gcd-loop-entry-preservation
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (unsigned-byte-p 32 tmp)
                (call-stackp call-tail)
                (storep store))
           (and (statep (run (gcd-loop-fuel a b)
                             (make-loop-entry-state a b tmp call-tail store)))
                (equal (cdr (state->call-stack
                             (run (gcd-loop-fuel a b)
                                  (make-loop-entry-state a b tmp call-tail store))))
                       call-tail)
                (equal (frame->return-arity
                        (car (state->call-stack
                              (run (gcd-loop-fuel a b)
                                   (make-loop-entry-state a b tmp call-tail store)))))
                       1)
                (equal (state->store
                        (run (gcd-loop-fuel a b)
                             (make-loop-entry-state a b tmp call-tail store)))
                       store)
                (consp (state->call-stack
                        (run (gcd-loop-fuel a b)
                             (make-loop-entry-state a b tmp call-tail store))))
                (consp (frame->operand-stack
                        (car (state->call-stack
                              (run (gcd-loop-fuel a b)
                                   (make-loop-entry-state a b tmp call-tail store))))))
                (<= 1 (operand-stack-height
                       (frame->operand-stack
                        (car (state->call-stack
                              (run (gcd-loop-fuel a b)
                                   (make-loop-entry-state a b tmp call-tail store)))))))
                (equal (state->memory
                        (run (gcd-loop-fuel a b)
                             (make-loop-entry-state a b tmp call-tail store)))
                       nil)
                (equal (state->globals
                        (run (gcd-loop-fuel a b)
                             (make-loop-entry-state a b tmp call-tail store)))
                       nil)
                (equal (state->table
                        (run (gcd-loop-fuel a b)
                             (make-loop-entry-state a b tmp call-tail store)))
                       nil)))
  :hints (("Goal"
           :induct (gcd-loop-ind a b tmp)
           :in-theory (disable loop-entry-step-case
                               loop-entry-base-case
                               loop-entry-base-case-preservation
                               run-split-when-statep
                               statep-of-make-loop-entry-state
                               make-loop-entry-state
                               (:induction gcd-loop-fuel)))
          ("Subgoal *1/1"
           :use ((:instance loop-entry-base-case-preservation
                            (a a) (tmp tmp)
                            (call-tail call-tail) (store store))))))

(value-triple (cw " - gcd-loop-entry-preservation: caller tail / return-arity / store preserved (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Final theorem: starting from the fresh gcd-state, the WASM
;; implementation computes nonneg-int-gcd.

(defun gcd-total-fuel (a b)
  (declare (xargs :verify-guards nil))
  (+ 2 (gcd-loop-fuel a b)))

(local (defthm statep-of-make-gcd-state
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (call-stackp call-tail)
                (storep store))
           (statep (make-gcd-state a b call-tail store)))
  :hints (("Goal" :in-theory (enable statep call-stackp framep
                                     label-stackp label-entryp
                                     operand-stackp val-listp
                                     i32-valp u32p)))))

(defthm gcd-impl-correct
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (call-stackp call-tail)
                (storep store))
           (equal (top-operand
                   (current-operand-stack
                    (run (gcd-total-fuel a b) (make-gcd-state a b call-tail store))))
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
           :use ((:instance gcd-state-to-loop-entry
                            (a a) (b b) (call-tail call-tail) (store store))
                 (:instance statep-of-make-gcd-state
                            (a a) (b b) (call-tail call-tail) (store store))
                 (:instance run-split-when-statep
                            (m 2)
                            (n (gcd-loop-fuel a b))
                            (state (make-gcd-state a b call-tail store)))
                 (:instance gcd-loop-entry-correct
                            (a a) (b b) (tmp 0)
                            (call-tail call-tail) (store store))))))

(value-triple (cw "~%====================================================~%"))
(value-triple (cw " GCD IMPLEMENTATION PROVED CORRECT for all u32 a,b.~%"))
(value-triple (cw "====================================================~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Phase 4: Lift to start from `*gcd-func*` (a `funcinst`) invoked via
;; the `(:call 0)` calling convention. This removes all function-internal
;; knowledge from the *interface* of the theorem — the only thing the
;; client must know is the funcinst and the argument-passing discipline.
;;
;; The body of this lift is three small glue lemmas:
;;   - gcd-func-call-enters-body : 1 step of `:call 0` on a call-state
;;     yields the (generalized) body state we proved correct above.
;;   - gcd-func-body-returns     : 2 steps past the top-of-operand-stack
;;     "result" state yield `(:done <caller-state-with-result>)`.
;;   - gcd-func-correct          : stitched together via run-split.

;; The funcinst `*gcd-func*` and its body `*gcd-body*` are loaded from
;; `tests/oracle/gcd.wasm` at the top of this book (see the make-event
;; above). We reuse them here.
(defconst *gcd-store* (list *gcd-func*))

;; The caller frame: invokes `(:call 0)` with args (a, b) already pushed.
;; WASM push order: arg0 first, arg1 on top; after popping, `top-n-operands`
;; reverses so the callee's locals become (a b 0).
(defun make-gcd-caller-frame (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b))
                  :verify-guards nil))
  (make-frame :return-arity 1
              :locals nil
              :operand-stack (list (make-i32-val b) (make-i32-val a))
              :instrs (list '(:call 0))
              :label-stack nil))

(defun make-gcd-call-state (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b))
                  :verify-guards nil))
  (make-state
   :store *gcd-store*
   :call-stack (list (make-gcd-caller-frame a b))
   :memory nil :globals nil))

;; The caller frame *after* `:call 0` has popped the two args and (per
;; `return-from-function`) advanced its instrs past the `:call`.  This
;; is what will be sitting underneath the gcd frame during the body run,
;; and what resurfaces with the result after we return.
(defun gcd-caller-frame-returned (r)
  ;; `r` is the gcd return value on top of the caller's operand stack.
  (declare (xargs :guard (valp r) :verify-guards nil))
  (make-frame :return-arity 1
              :locals nil
              :operand-stack (list r)
              :instrs nil
              :label-stack nil))

(defun gcd-caller-frame-popped ()
  ;; `:call` popped args but did not yet advance past itself; that
  ;; happens inside `return-from-function`.
  (declare (xargs :guard t :verify-guards nil))
  (make-frame :return-arity 1
              :locals nil
              :operand-stack (empty-operand-stack)
              :instrs (list '(:call 0))
              :label-stack nil))

;; --- Entry: one step of `:call 0` ------------------------------------------
;;
;; From the call-state, a single WASM step executes `:call 0` and pushes
;; the callee frame on top of the caller (with args popped).  The result
;; matches our generalized `make-gcd-state` with the caller-popped frame
;; as `call-tail`.

(defthm gcd-func-call-enters-body
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (equal (run 1 (make-gcd-call-state a b))
                  (make-gcd-state a b
                                  (list (gcd-caller-frame-popped))
                                  *gcd-store*)))
  :hints (("Goal"
           :in-theory (union-theories
                       (current-theory :here)
                       (append '(execute-call funcinst->param-count
                                 funcinst->local-count funcinst->return-arity
                                 funcinst->body)
                               *gcd-exec-theory*))
           :do-not '(generalize)
           :expand ((:free (n s) (run n s))
                    (:free (n s a) (top-n-operands n s a))))))

(value-triple (cw " - gcd-func-call-enters-body: `(:call 0)` enters gcd body (Q.E.D.)~%"))

;; --- Exit: two steps wrap the result back to the caller and signal :done ---
;;
;; After gcd-impl-correct fires, the callee has instrs=nil, label-stack=nil,
;; and the result on top of its operand stack.  One step of `run`:
;;   - triggers `return-from-function`, which pops the callee, pushes the
;;     result on the caller's operand stack, and advances caller past :call.
;; A second step sees instrs=nil, label-stack=nil on the sole remaining
;; frame and returns `(:done <state>)`.
;;
;; For this to be a useful rewrite we need access to the *whole* body
;; state, not just its top-operand projection.  The strengthened lemma
;; below gives that.

(defthm gcd-impl-correct-state
  ;; All the shape/projection facts the caller needs to drive the return.
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (call-stackp call-tail)
                (storep store))
           (and (not (consp (current-instrs
                             (run (gcd-total-fuel a b)
                                  (make-gcd-state a b call-tail store)))))
                (not (consp (current-label-stack
                             (run (gcd-total-fuel a b)
                                  (make-gcd-state a b call-tail store)))))
                (equal (top-operand
                        (current-operand-stack
                         (run (gcd-total-fuel a b)
                              (make-gcd-state a b call-tail store))))
                       (make-i32-val (acl2::nonneg-int-gcd a b)))
                (statep (run (gcd-total-fuel a b)
                             (make-gcd-state a b call-tail store)))
                (equal (cdr (state->call-stack
                             (run (gcd-total-fuel a b)
                                  (make-gcd-state a b call-tail store))))
                       call-tail)
                (equal (frame->return-arity
                        (car (state->call-stack
                              (run (gcd-total-fuel a b)
                                   (make-gcd-state a b call-tail store)))))
                       1)
                (equal (state->store
                        (run (gcd-total-fuel a b)
                             (make-gcd-state a b call-tail store)))
                       store)
                (consp (state->call-stack
                        (run (gcd-total-fuel a b)
                             (make-gcd-state a b call-tail store))))
                (consp (frame->operand-stack
                        (car (state->call-stack
                              (run (gcd-total-fuel a b)
                                   (make-gcd-state a b call-tail store))))))
                (<= 1 (operand-stack-height
                       (frame->operand-stack
                        (car (state->call-stack
                              (run (gcd-total-fuel a b)
                                   (make-gcd-state a b call-tail store)))))))
                (equal (state->memory
                        (run (gcd-total-fuel a b)
                             (make-gcd-state a b call-tail store)))
                       nil)
                (equal (state->globals
                        (run (gcd-total-fuel a b)
                             (make-gcd-state a b call-tail store)))
                       nil)
                (equal (state->table
                        (run (gcd-total-fuel a b)
                             (make-gcd-state a b call-tail store)))
                       nil)))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(generalize fertilize)
           :in-theory (disable gcd-state-to-loop-entry
                               gcd-loop-entry-correct
                               gcd-loop-entry-done-shape
                               gcd-loop-entry-preservation
                               gcd-impl-correct
                               run-split-when-statep
                               statep-of-make-gcd-state
                               make-loop-entry-state
                               make-gcd-state
                               acl2::nonneg-int-gcd)
           :use ((:instance gcd-impl-correct
                            (a a) (b b)
                            (call-tail call-tail) (store store))
                 (:instance gcd-state-to-loop-entry
                            (a a) (b b) (call-tail call-tail) (store store))
                 (:instance statep-of-make-gcd-state
                            (a a) (b b) (call-tail call-tail) (store store))
                 (:instance run-split-when-statep
                            (m 2)
                            (n (gcd-loop-fuel a b))
                            (state (make-gcd-state a b call-tail store)))
                 (:instance gcd-loop-entry-done-shape
                            (a a) (b b) (tmp 0)
                            (call-tail call-tail) (store store))
                 (:instance gcd-loop-entry-preservation
                            (a a) (b b) (tmp 0)
                            (call-tail call-tail) (store store))))))

(value-triple (cw " - gcd-impl-correct: state projections after body execution (Q.E.D.)~%"))

;; --- End-to-end theorem -----------------------------------------------------

(defun gcd-func-total-fuel (a b)
  ;; 1 step to enter via `:call`; `gcd-total-fuel` steps for the body;
  ;; 1 step to return-from-function; 1 step to signal :done.
  (declare (xargs :verify-guards nil))
  (+ 3 (gcd-total-fuel a b)))

;; Extraction: top-of-operand-stack of the caller frame in a :done state,
;; matching tests/test-spot-check.lisp's `get-result`.
(defun gcd-done-result (r)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp r) (eq :done (first r)))
      (let* ((st (second r))
             (cs (state->call-stack st))
             (f (car cs)))
        (top-operand (frame->operand-stack f)))
    r))

;; -- Intermediate stepping lemmas --------------------------------------------
;;
;; We split the `gcd-func-total-fuel a b` run into four pieces, using
;; `run-split-when-statep` at each boundary:
;;
;;     call-state ─1→ body-start ─body→ body-end ─1→ after-return ─1→ :done
;;      (S0)      step1   (S1)   Nfuel  (S2)    step (S3)        step (S4)
;;
;; We already have S0→S1 (`gcd-func-call-enters-body`) and S1→S2 (via
;; `gcd-impl-correct-state`).  The final two steps (S2→S3→S4) are
;; driven by `return-from-function`; we characterize them below.

;; Caller frame after `return-from-function` has popped the gcd frame
;; and pushed the result on top of the caller's operand stack.  Its
;; instrs list was `(:call 0)` in `gcd-caller-frame-popped`; after
;; return-from-function advances past the :call, instrs = nil.
(defun gcd-caller-frame-final (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
                  :verify-guards nil))
  (make-frame :return-arity 1
              :locals nil
              :operand-stack (list (make-i32-val (acl2::nonneg-int-gcd a b)))
              :instrs nil
              :label-stack nil))

;; -- statep of the body-start state (needed for run-split) ------------------
(local
 (defthm statep-of-body-start
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
            (statep (make-gcd-state a b
                                    (list (gcd-caller-frame-popped))
                                    *gcd-store*)))
   :hints (("Goal" :in-theory (enable statep call-stackp framep
                                      label-stackp operand-stackp
                                      val-listp i32-valp u32p
                                      funcinst-listp funcinstp
                                      gcd-caller-frame-popped)))))

;; -- statep of call-state ---------------------------------------------------
(local
 (defthm statep-of-call-state
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
            (statep (make-gcd-call-state a b)))
   :hints (("Goal" :in-theory (enable statep call-stackp framep
                                      label-stackp operand-stackp
                                      val-listp i32-valp u32p
                                      funcinst-listp funcinstp)))))

;; -- statep after the body run ----------------------------------------------
;; After gcd-total-fuel steps the state still has non-empty call-stack
;; (by preservation) so it cannot be :done or :trap.

(local
 (defthm statep-after-body
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
            (statep (run (gcd-total-fuel a b)
                         (make-gcd-state a b
                                         (list (gcd-caller-frame-popped))
                                         *gcd-store*))))
   :hints (("Goal"
            :do-not-induct t
            :do-not '(generalize fertilize)
            :use ((:instance gcd-impl-correct-state
                             (a a) (b b)
                             (call-tail (list (gcd-caller-frame-popped)))
                             (store *gcd-store*)))
            :in-theory (disable gcd-impl-correct-state
                                gcd-state-to-loop-entry
                                gcd-total-fuel
                                (:definition run)
                                make-gcd-state)))))

(value-triple (cw " - statep lemmas for call-state / body-start / body-end (Q.E.D.)~%"))

;; --- S2 → S3: one step of return-from-function at the body-end state -------
;;
;; We don't know the full shape of S2 (its locals/intermediate operand
;; stack are whatever the last iteration produced), but we know all the
;; projections `return-from-function` reads.  We therefore prove:
;;   top-operand of S3's current-operand-stack = gcd
;;   current-instrs of S3 = nil
;;   current-label-stack of S3 = nil
;;   call-stack of S3 = (list gcd-caller-frame-popped-with-instrs-popped)
;; From these, the final step (S3 → :done) follows by direct execution.

(defun gcd-body-end-state (a b)
  ;; Abbreviation for the body-end state.
  (declare (xargs :verify-guards nil))
  (run (gcd-total-fuel a b)
       (make-gcd-state a b (list (gcd-caller-frame-popped)) *gcd-store*)))

;; Structural facts about the call-stack of S2 that we'll feed into
;; `return-from-function`.  All come from gcd-impl-correct-state.
(local
 (defthm body-end-call-stack-structure
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
            (and (statep (gcd-body-end-state a b))
                 (consp (state->call-stack (gcd-body-end-state a b)))
                 (consp (cdr (state->call-stack (gcd-body-end-state a b))))
                 (equal (cdr (state->call-stack (gcd-body-end-state a b)))
                        (list (gcd-caller-frame-popped)))
                 (equal (frame->return-arity
                         (car (state->call-stack (gcd-body-end-state a b))))
                        1)
                 (equal (state->store (gcd-body-end-state a b))
                        *gcd-store*)
                 (not (consp (current-instrs (gcd-body-end-state a b))))
                 (not (consp (current-label-stack (gcd-body-end-state a b))))
                 (consp (frame->operand-stack
                         (car (state->call-stack (gcd-body-end-state a b)))))
                 (<= 1 (operand-stack-height
                        (frame->operand-stack
                         (car (state->call-stack (gcd-body-end-state a b))))))
                 (equal (state->memory (gcd-body-end-state a b)) nil)
                 (equal (state->globals (gcd-body-end-state a b)) nil)
                 (equal (state->table (gcd-body-end-state a b)) nil)
                 (equal (top-operand
                         (current-operand-stack (gcd-body-end-state a b)))
                        (make-i32-val (acl2::nonneg-int-gcd a b)))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance gcd-impl-correct-state
                             (a a) (b b)
                             (call-tail (list (gcd-caller-frame-popped)))
                             (store *gcd-store*)))
            :in-theory (e/d (gcd-body-end-state)
                            (gcd-impl-correct-state
                             gcd-state-to-loop-entry
                             gcd-total-fuel
                             (:definition run)
                             make-gcd-state))))))

;; Auxiliary: operand stack has height >= 1 at body end.  Derived from
;; `top-operand = make-i32-val (gcd a b)` which is a non-nil cons, so
;; the stack must be non-empty.

;; Auxiliary: operand stack has height >= 1 at body end — now follows
;; directly from the strengthened `body-end-call-stack-structure`.
;; (Kept as a rename/alias so return-from-body-end's :use clause
;; continues to work.)

(local
 (defthm body-end-operand-stack-consp
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
            (and (consp (frame->operand-stack
                         (car (state->call-stack (gcd-body-end-state a b)))))
                 (<= 1 (operand-stack-height
                        (frame->operand-stack
                         (car (state->call-stack (gcd-body-end-state a b))))))))
   :hints (("Goal"
            :use ((:instance body-end-call-stack-structure (a a) (b b)))
            :in-theory (disable body-end-call-stack-structure
                                gcd-body-end-state
                                (:definition run))))))

;; From these projections, we characterize `return-from-function` applied
;; to the body-end state.  The resulting state has:
;;   - call-stack = (list gcd-caller-frame-final)
;;   - store = *gcd-store*
;; so that a subsequent step immediately produces (:done ...).

(local
 (defthm return-from-body-end
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
            (equal (return-from-function (gcd-body-end-state a b))
                   (make-state
                    :store *gcd-store*
                    :call-stack (list (gcd-caller-frame-final a b))
                    :memory nil :globals nil)))
   :hints (("Goal"
            :do-not-induct t
            :do-not '(generalize fertilize)
            :use ((:instance body-end-call-stack-structure (a a) (b b))
                  (:instance body-end-operand-stack-consp (a a) (b b)))
            :expand ((:free (stack)
                      (top-n-operands 1 stack nil))
                     (:free (stack acc)
                      (top-n-operands 0 stack acc))
                     (:free (v rest stack)
                      (push-vals (cons v rest) stack))
                     (:free (stack)
                      (push-vals nil stack)))
            :in-theory (e/d (return-from-function
                             pop-call-stack push-call-stack push-vals
                             top-n-operands top-operand push-operand
                             pop-operand
                             operand-stack-height
                             current-frame current-instrs current-operand-stack
                             current-label-stack top-frame
                             update-current-operand-stack
                             update-current-instrs
                             gcd-caller-frame-final
                             gcd-caller-frame-popped)
                            (body-end-call-stack-structure
                             body-end-operand-stack-consp
                             gcd-body-end-state
                             (:definition run)
                             make-gcd-state))))))

(value-triple (cw " - return-from-body-end: S2 -> S3 via return-from-function (Q.E.D.)~%"))

;; --- S3 → :done.  One more step, which calls return-from-function on a
;; single-frame call-stack with empty instrs/labels.

(local
 (defthm run-1-from-after-return
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
            (equal (run 1
                        (make-state
                         :store *gcd-store*
                         :call-stack (list (gcd-caller-frame-final a b))
                         :memory nil :globals nil))
                   `(:done ,(make-state
                             :store *gcd-store*
                             :call-stack (list (gcd-caller-frame-final a b))
                             :memory nil :globals nil))))
   :hints (("Goal"
            :in-theory (e/d (return-from-function
                             current-instrs current-label-stack
                             current-frame top-frame
                             state->call-stack
                             frame->instrs frame->label-stack
                             frame->operand-stack
                             gcd-caller-frame-final)
                            nil)
            :expand ((:free (s) (run 1 s)))))))

(value-triple (cw " - run-1-from-after-return: S3 -> :done (Q.E.D.)~%"))

(local
 (defthm not-equal-done-car-when-statep
   (implies (statep x)
            (not (equal :done (car x))))
   :hints (("Goal"
            :use ((:instance not-statep-of-done (x (cdr x))))
            :in-theory (disable not-statep-of-done)))))

(local
 (defthm framep-of-gcd-caller-frame-final
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
            (framep (gcd-caller-frame-final a b)))
   :hints (("Goal" :in-theory (enable framep label-stackp
                                      operand-stackp val-listp
                                      valp i32-valp u32p
                                      make-i32-val
                                      gcd-caller-frame-final)))))

(local
 (defthm statep-of-return-from-body-end
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
            (statep (return-from-function (gcd-body-end-state a b))))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance return-from-body-end (a a) (b b)))
            :in-theory (e/d (call-stackp framep label-stackp
                                         operand-stackp val-listp
                                         valp i32-valp u32p
                                         make-i32-val
                                         gcd-caller-frame-final)
                            (gcd-body-end-state))))))

;; --- Chain: S2 (= run gcd-total-fuel body-start) → :done via 2 more steps.

(local
 (defthm run-2-from-body-end
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
            (equal (run 2 (gcd-body-end-state a b))
                   `(:done ,(make-state
                             :store *gcd-store*
                             :call-stack (list (gcd-caller-frame-final a b))
                             :memory nil :globals nil))))
   :hints (("Goal"
            :do-not-induct t
            :do-not '(generalize fertilize)
            :use ((:instance body-end-call-stack-structure (a a) (b b))
                  (:instance return-from-body-end (a a) (b b))
                  (:instance run-1-from-after-return (a a) (b b))
                  (:instance statep-of-return-from-body-end (a a) (b b)))
            :expand ((:free (s) (run 2 s))
                     (:free (s) (run 1 s)))
            :in-theory (e/d (current-instrs current-label-stack)
                            (body-end-call-stack-structure
                             return-from-body-end
                             run-1-from-after-return
                             statep-of-return-from-body-end
                             gcd-body-end-state
                             gcd-caller-frame-final))))))

(value-triple (cw " - run-2-from-body-end: 2 final steps land in :done (Q.E.D.)~%"))

;; --- Chain: call-state → body-start (1 step) → body-end (gcd-total-fuel)
;; → :done (2 steps).  All glued with run-split-when-statep.

(defthm gcd-func-correct
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (equal (run (gcd-func-total-fuel a b)
                       (make-gcd-call-state a b))
                  `(:done ,(make-state
                            :store *gcd-store*
                            :call-stack (list (gcd-caller-frame-final a b))
                            :memory nil :globals nil))))
  :hints (("Goal"
           :do-not-induct t
           :do-not '(generalize fertilize)
           :use ((:instance gcd-func-call-enters-body (a a) (b b))
                 (:instance statep-of-call-state (a a) (b b))
                 (:instance statep-of-body-start (a a) (b b))
                 (:instance statep-after-body (a a) (b b))
                 (:instance run-2-from-body-end (a a) (b b))
                 (:instance run-split-when-statep
                            (m 1)
                            (n (+ 2 (gcd-total-fuel a b)))
                            (state (make-gcd-call-state a b)))
                 (:instance run-split-when-statep
                            (m (gcd-total-fuel a b))
                            (n 2)
                            (state (make-gcd-state a b
                                                   (list (gcd-caller-frame-popped))
                                                   *gcd-store*))))
           :in-theory (e/d (gcd-func-total-fuel
                            gcd-body-end-state)
                           (gcd-func-call-enters-body
                            statep-of-call-state
                            statep-of-body-start
                            statep-after-body
                            run-2-from-body-end
                            run-split-when-statep
                            make-gcd-call-state
                            make-gcd-state
                            (:definition run))))))

(value-triple (cw " - gcd-func-correct: full :call-to-:done trace (Q.E.D.)~%"))

;; --- User-facing corollary: extraction via `gcd-done-result` ---------------

(defthm gcd-func-correct-result
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (equal (gcd-done-result
                   (run (gcd-func-total-fuel a b)
                        (make-gcd-call-state a b)))
                  (make-i32-val (acl2::nonneg-int-gcd a b))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance gcd-func-correct (a a) (b b)))
           :in-theory (e/d (gcd-done-result
                            gcd-caller-frame-final
                            top-operand
                            state->call-stack frame->operand-stack)
                           (gcd-func-correct
                            (:definition run))))))

(value-triple (cw "~%====================================================~%"))
(value-triple (cw " *GCD-FUNC* PROVED CORRECT starting from :call state.~%"))
(value-triple (cw "====================================================~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 9. Fuel-free partial-correctness wrapper.
;;
;; The theorems above are stated with a concrete fuel value
;; `gcd-func-total-fuel a b`.  For an end-user-facing statement it's
;; cleaner to say "there exists some fuel for which the run reaches
;; :done with the expected value".  `defun-sk` packages that existential
;; once, and the two witness lemmas below discharge it using the fuel
;; we already know works.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun-sk gcd-halts-with (a b v)
  (exists fuel
    (and (natp fuel)
         (equal (run fuel (make-gcd-call-state a b))
                `(:done ,(make-state
                          :store *gcd-store*
                          :call-stack (list (gcd-caller-frame-final a b))
                          :memory nil :globals nil)))
         (equal v (make-i32-val (acl2::nonneg-int-gcd a b))))))

(defthm gcd-func-halts
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (gcd-halts-with a b
                           (make-i32-val (acl2::nonneg-int-gcd a b))))
  :hints (("Goal"
           :use ((:instance gcd-halts-with-suff
                            (fuel (gcd-func-total-fuel a b))
                            (a a) (b b)
                            (v (make-i32-val (acl2::nonneg-int-gcd a b))))
                 (:instance gcd-func-correct (a a) (b b)))
           :in-theory (e/d ()
                           (gcd-halts-with
                            gcd-halts-with-suff
                            gcd-func-correct
                            gcd-func-total-fuel
                            make-gcd-call-state
                            gcd-caller-frame-final
                            (:definition run))))))

(value-triple (cw " - gcd-func-halts: fuel-free existential statement (Q.E.D.)~%"))

(value-triple (cw "~%====================================================~%"))
(value-triple (cw " FUEL-FREE WRAPPER: gcd-halts-with established.~%"))
(value-triple (cw "====================================================~%"))



