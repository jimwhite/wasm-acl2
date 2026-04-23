;; WASM 1.0 ACL2 — GCD end-to-end correctness
;;
;; The WASM program under test implements the Euclidean algorithm on
;; unsigned 32-bit integers:
;;
;;     while (b != 0) { t = b; b = a rem_u b; a = t; }
;;     return a;
;;
;; It is loaded at certification time from the binary-format module in
;; `tests/oracle/gcd.wasm` (itself produced from `tests/oracle/gcd.wat`
;; via `wat2wasm`; see `Makefile` and `tools/README.md`).
;;
;; The ACL2 arithmetic book `arithmetic/mod-gcd` already defines the
;; mathematical spec `nonneg-int-gcd` and proves it is a GCD.
;;
;; Strategy: build up from concrete symbolic-execution lemmas toward the
;; general theorem (cf. proofs/proof-loop-spec.lisp, proof-abs-e2e.lisp).
;;
;;   §1. Base case     — when b = 0, the WASM impl returns (i32 a).
;;   §2. Step case     — one loop iteration reduces (a, b) to (b, a mod b).
;;   §3. Induction     — combine §1 and §2 via `gcd-loop-fuel` /
;;                       `gcd-loop-ind` to match `nonneg-int-gcd`.
;;   §4. Lift to call  — run the `(:call 0)` entry and `return-from-
;;                       function` exit so the theorem is stated at the
;;                       `*gcd-func*` funcinst interface, ending in :done.
;;   §5. Fuel-free     — a `defun-sk gcd-halts-with` existential wrapper
;;                       so user-facing consumers do not mention fuel.
;;
;; See `GCD_PROOF_NOTES.md` for the lessons learned and the recipe to
;; replicate this for another function.

(in-package "WASM")
(include-book "../execution")
(include-book "wasm-run-utils")    ; run-split-when-statep, *wasm-exec-theory*, not-statep-of-*
(include-book "wasm-arith-utils") ; u32p-of-mod, bvmod-32-when-u32, nonneg-int-* bridges
(include-book "wasm-loader")     ; load-wasm-funcinsts: .wasm -> (funcinst ...)
(include-book "wasm-call-wrap")  ; generic :call / body / return wrapper

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
;; §1. Base case. When b = 0, running the WASM gcd returns a.

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
;; §2. Step-case lemma.
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
;; §3. Induction.
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
;; the store, memory / globals / table, and the (non-empty) operand
;; stack are all unchanged in shape across body execution.  Needed by
;; the lifting section to drive `return-from-function` on the final
;; wrap-up steps.

;; Base case (`b = 0`) preservation: 10 conjuncts covering every
;; projection the lift will read through the body-end state.
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
;; §4. Lift to start from `*gcd-func*` (a `funcinst`) invoked via the
;; `(:call 0)` calling convention.  This removes all function-internal
;; knowledge from the *interface* of the theorem — the client only needs
;; to know the funcinst and the argument-passing discipline.
;;
;; The trace we stitch together is
;;
;;   call-state ─1→ body-start ─body-fuel→ body-end ─1→ after-return ─1→ :done
;;     (S0)  step1   (S1)   gcd-total-fuel   (S2)  step (S3)         step (S4)
;;
;; with these lemmas driving the edges:
;;
;;   S0 → S1 : `gcd-func-call-enters-body`  (one step of `:call 0`
;;              pushes the gcd frame on top of the caller-popped frame,
;;              matching `make-gcd-state` with a synthetic call-tail).
;;   S1 → S2 : `gcd-impl-correct-state`     (strengthened shape lemma:
;;              gathers everything a subsequent `return-from-function`
;;              step reads — call-tail, return-arity, store, operand
;;              stack, emptiness of instrs / labels / memory / globals,
;;              and the top operand = nonneg-int-gcd a b).
;;   S2 → S3 : `return-from-body-end`       (one step of
;;              `return-from-function` pops the gcd frame and leaves
;;              the caller in `gcd-caller-frame-final`).
;;   S3 → S4 : `run-1-from-after-return`    (one final step sees
;;              instrs=nil, label-stack=nil, single-frame call-stack,
;;              and emits `(:done <state>)`).
;;
;; The top-level theorem `gcd-func-correct` glues these with
;; `run-split-when-statep` at each boundary.

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
;; is what sits underneath the gcd frame during the body run and
;; resurfaces with the result after we return.  It is provided by the
;; generic call-wrap book as `wrap-popped-frame`; we use that directly.

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
                                  (list (wrap-popped-frame))
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §4. End-to-end: lift `gcd-impl-correct-state` to a full `:call` → `:done`
;; trace by functionally instantiating `call-to-done` from the generic
;; call-wrap book.
;;
;; The wrap book's encapsulate has six abstract signatures plus seven
;; constraint theorems; we discharge them with the gcd-specific witnesses
;; below and then obtain `gcd-func-correct` in a single `:use` clause.

;; --- Concrete witnesses for the six abstract signatures --------------------

(defun gcd-the-func ()
  (declare (xargs :guard t :verify-guards nil))
  *gcd-func*)

(defun gcd-input-ok (a b)
  (declare (xargs :guard t :verify-guards nil))
  (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b)))

(defun gcd-spec-val (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
                  :verify-guards nil))
  (make-i32-val (acl2::nonneg-int-gcd a b)))

(defun gcd-body-state (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
                  :verify-guards nil))
  (make-gcd-state a b (list (wrap-popped-frame)) *gcd-store*))

(defun gcd-body-fuel-fn (a b)
  (declare (xargs :guard t :verify-guards nil))
  (gcd-total-fuel a b))

;; --- Discharge the seven constraint theorems of the wrap book -------------

(local
 (defthm gcd-funcinstp-of-the-func
   (funcinstp (gcd-the-func))
   :hints (("Goal" :in-theory (enable funcinstp)))))

(local
 (defthm gcd-input-ok-implies-u32
   (implies (gcd-input-ok a b)
            (and (unsigned-byte-p 32 a)
                 (unsigned-byte-p 32 b)))
   :rule-classes :forward-chaining))

(local
 (defthm gcd-i32-valp-of-spec-val
   (implies (gcd-input-ok a b)
            (i32-valp (gcd-spec-val a b)))
   :hints (("Goal" :in-theory (enable i32-valp make-i32-val u32p)))))

(local
 (defthm gcd-natp-of-body-fuel
   (implies (gcd-input-ok a b)
            (natp (gcd-body-fuel-fn a b)))
   :rule-classes :type-prescription))

;; The call-enters-body constraint instantiates to exactly
;; `gcd-func-call-enters-body`, once we expand `make-gcd-call-state` and
;; `gcd-body-state`.
(local
 (defthm gcd-call-enters-body
   (implies (gcd-input-ok a b)
            (equal (run 1 (make-state
                           :store (list (gcd-the-func))
                           :call-stack (list (make-gcd-caller-frame a b))
                           :memory nil :globals nil))
                   (gcd-body-state a b)))
   :hints (("Goal"
            :use ((:instance gcd-func-call-enters-body (a a) (b b)))
            :in-theory (e/d (gcd-body-state) ; gcd-the-func unfolds via exec-counterpart
                            (gcd-func-call-enters-body))))))

;; statep-of-make-body-state: gcd-body-state is a statep.
(local
 (defthm gcd-statep-of-make-body-state
   (implies (gcd-input-ok a b)
            (statep (gcd-body-state a b)))
   :hints (("Goal"
            :use ((:instance statep-of-make-gcd-state
                             (a a) (b b)
                             (call-tail (list (wrap-popped-frame)))
                             (store *gcd-store*)))
            :in-theory (e/d (gcd-body-state call-stackp framep
                                            label-stackp operand-stackp
                                            funcinst-listp)
                            (statep-of-make-gcd-state))))))

;; body-shape-after-fuel: the 13-conjunct shape at the end of the body run.
;; `gcd-impl-correct-state` states exactly this for arbitrary (call-tail,
;; store); we specialize to (list (wrap-popped-frame)) and *gcd-store*.
(local
 (defthm gcd-body-shape-after-fuel
   (implies (gcd-input-ok a b)
            (and (not (consp (current-instrs
                              (run (gcd-body-fuel-fn a b) (gcd-body-state a b)))))
                 (not (consp (current-label-stack
                              (run (gcd-body-fuel-fn a b) (gcd-body-state a b)))))
                 (statep (run (gcd-body-fuel-fn a b) (gcd-body-state a b)))
                 (equal (cdr (state->call-stack
                              (run (gcd-body-fuel-fn a b) (gcd-body-state a b))))
                        (list (wrap-popped-frame)))
                 (equal (frame->return-arity
                         (car (state->call-stack
                               (run (gcd-body-fuel-fn a b) (gcd-body-state a b)))))
                        1)
                 (equal (state->store
                         (run (gcd-body-fuel-fn a b) (gcd-body-state a b)))
                        (list (gcd-the-func)))
                 (consp (state->call-stack
                         (run (gcd-body-fuel-fn a b) (gcd-body-state a b))))
                 (consp (frame->operand-stack
                         (car (state->call-stack
                               (run (gcd-body-fuel-fn a b) (gcd-body-state a b))))))
                 (<= 1 (operand-stack-height
                        (frame->operand-stack
                         (car (state->call-stack
                               (run (gcd-body-fuel-fn a b) (gcd-body-state a b)))))))
                 (equal (state->memory
                         (run (gcd-body-fuel-fn a b) (gcd-body-state a b)))
                        nil)
                 (equal (state->globals
                         (run (gcd-body-fuel-fn a b) (gcd-body-state a b)))
                        nil)
                 (equal (state->table
                         (run (gcd-body-fuel-fn a b) (gcd-body-state a b)))
                        nil)
                 (equal (top-operand
                         (current-operand-stack
                          (run (gcd-body-fuel-fn a b) (gcd-body-state a b))))
                        (gcd-spec-val a b))))
   :hints (("Goal"
            :use ((:instance gcd-impl-correct-state
                             (a a) (b b)
                             (call-tail (list (wrap-popped-frame)))
                             (store *gcd-store*)))
            :in-theory (e/d (gcd-body-state gcd-body-fuel-fn)
                            (gcd-impl-correct-state))))))

(value-triple (cw " - wrap-book constraints discharged for gcd (Q.E.D.)~%"))

;; --- Functionally instantiate `call-to-done` ------------------------------

;; First, the raw instantiation.  We avoid enabling the gcd-specific
;; witness defuns here so that the constraint-discharge rewrite rules
;; (`gcd-*` above) match the substituted constraints unchanged.
(local
 (defthm gcd-func-correct-raw
   (implies (and (gcd-input-ok a b)
                 (framep (make-gcd-caller-frame a b)))
            (equal (run (+ 3 (gcd-body-fuel-fn a b))
                        (make-state
                         :store (list (gcd-the-func))
                         :call-stack (list (make-gcd-caller-frame a b))
                         :memory nil :globals nil))
                   `(:done ,(make-state
                             :store (list (gcd-the-func))
                             :call-stack (list (make-frame
                                                :return-arity 1
                                                :locals nil
                                                :operand-stack (list (gcd-spec-val a b))
                                                :instrs nil
                                                :label-stack nil))
                             :memory nil :globals nil))))
   :hints (("Goal"
            :use ((:functional-instance
                   call-to-done
                   (the-func gcd-the-func)
                   (input-ok gcd-input-ok)
                   (spec-val gcd-spec-val)
                   (make-call-frame make-gcd-caller-frame)
                   (make-body-state gcd-body-state)
                   (body-fuel gcd-body-fuel-fn)))
            :in-theory (e/d ()
                                (gcd-body-state
                                 gcd-body-fuel-fn
                                 gcd-input-ok
                                 gcd-spec-val
                                 gcd-the-func
                                 (:executable-counterpart gcd-the-func)
                                 wrap-popped-frame
                                 wrap-final-frame
                                 make-gcd-caller-frame
                                 make-gcd-state
                                 current-label-stack
                                 current-instrs
                                 current-operand-stack
                                 current-frame
                                 top-frame))))))

(local
 (defthm framep-of-make-gcd-caller-frame
   (implies (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
            (framep (make-gcd-caller-frame a b)))
   :hints (("Goal" :in-theory (enable framep label-stackp operand-stackp
                                      val-listp valp i32-valp u32p
                                      make-i32-val)))))

;; Second, unfold the gcd-specific witnesses to get the user-facing form.
(defthm gcd-func-correct
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (equal (run (+ 3 (gcd-total-fuel a b)) (make-gcd-call-state a b))
                  `(:done ,(make-state
                            :store *gcd-store*
                            :call-stack (list (make-frame
                                               :return-arity 1
                                               :locals nil
                                               :operand-stack
                                               (list (make-i32-val
                                                      (acl2::nonneg-int-gcd a b)))
                                               :instrs nil
                                               :label-stack nil))
                            :memory nil :globals nil))))
  :hints (("Goal"
           :use ((:instance gcd-func-correct-raw (a a) (b b))
                 (:instance framep-of-make-gcd-caller-frame (a a) (b b)))
           :in-theory (e/d (gcd-input-ok
                            gcd-the-func
                            gcd-spec-val
                            gcd-body-fuel-fn
                            make-gcd-call-state)
                           (gcd-func-correct-raw
                            framep-of-make-gcd-caller-frame
                            make-gcd-caller-frame
                            (:definition run))))))

(value-triple (cw " - gcd-func-correct: full :call-to-:done trace (Q.E.D.)~%"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §5. Fuel-free partial-correctness wrapper.
;;
;; A `defun-sk` existential over the fuel, satisfied by witnessing with
;; `(+ 3 (gcd-total-fuel a b))` via `gcd-func-correct`.

(defun-sk gcd-halts-with (a b v)
  (exists fuel
    (and (natp fuel)
         (equal (run fuel (make-gcd-call-state a b))
                `(:done ,(make-state
                          :store *gcd-store*
                          :call-stack (list (make-frame
                                             :return-arity 1
                                             :locals nil
                                             :operand-stack (list v)
                                             :instrs nil
                                             :label-stack nil))
                          :memory nil :globals nil)))
         (equal v (make-i32-val (acl2::nonneg-int-gcd a b))))))

(defthm gcd-func-halts
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (gcd-halts-with a b
                           (make-i32-val (acl2::nonneg-int-gcd a b))))
  :hints (("Goal"
           :use ((:instance gcd-halts-with-suff
                            (fuel (+ 3 (gcd-total-fuel a b)))
                            (a a) (b b)
                            (v (make-i32-val (acl2::nonneg-int-gcd a b))))
                 (:instance gcd-func-correct (a a) (b b)))
           :in-theory (e/d ()
                           (gcd-halts-with
                            gcd-halts-with-suff
                            gcd-func-correct
                            make-gcd-call-state
                            (:definition run))))))

(value-triple (cw " - gcd-func-halts: fuel-free existential statement (Q.E.D.)~%"))

(value-triple (cw "~%====================================================~%"))
(value-triple (cw " FUEL-FREE WRAPPER: gcd-halts-with established.~%"))
(value-triple (cw "====================================================~%"))
