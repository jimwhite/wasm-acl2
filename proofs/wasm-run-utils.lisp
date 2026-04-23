;; Shared run/statep utilities for WASM correctness proofs.
;;
;; These lemmas are independent of any particular function: they state
;; fundamental properties of the small-step interpreter `run` and the
;; state predicate `statep`, and they are consumed by essentially every
;; multi-iteration proof.
;;
;; Organization:
;;   *wasm-exec-theory*           — function-independent enable list
;;                                  for symbolic execution
;;   not-statep-of-done/trap      — sentinel tags are not states
;;   run-ind                      — local induction scheme mirroring run
;;   run-split-when-statep        — run over addition splits on statep
;;
;; See proofs/GCD_PROOF_NOTES.md for the broader proof methodology.

(in-package "WASM")
(include-book "../execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Theory list used by concrete symbolic-execution lemmas.  Enable this
;; alongside the standard theory to unfold one step of `run` at a time.

(defconst *wasm-exec-theory*
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
    statep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The sentinel tags that `run` returns on trap or normal completion are
;; disjoint from `statep`.

(defthm not-statep-of-done
  (not (statep (cons :done x)))
  :hints (("Goal" :in-theory (enable statep))))

(defthm not-statep-of-trap
  (not (statep :trap))
  :hints (("Goal" :in-theory (enable statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Induction scheme mirroring the step-by-step structure of `run`.

(defun run-ind (m state)
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
        (if (eq :trap ns) state (run-ind (+ -1 m) ns))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The key glue lemma: run over addition splits once we know the
;; intermediate is still a statep (i.e. no trap, no :done).
;; Downstream proofs use this to chain multi-step symbolic-execution
;; lemmas across an inductive argument.

(defthm run-split-when-statep
  (implies (and (natp m) (natp n) (statep (run m state)))
           (equal (run (+ m n) state)
                  (run n (run m state))))
  :hints (("Goal" :induct (run-ind m state))))

(value-triple (cw "wasm-run-utils: loaded.~%"))
