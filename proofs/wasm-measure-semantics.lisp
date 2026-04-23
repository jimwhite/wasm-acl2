; wasm-measure-semantics.lisp — measure-based operational semantics.
;
; Copyright (C) 2025 Kestrel Institute
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; A program-agnostic operational-refinement framework that does NOT rely
; on step-counting fuel to reason about WASM programs to completion.
;
; The framework introduces four abstract signatures:
;
;   mstep         :: state -> value    abstract "machine step"
;   mstep-count   :: state -> nat      how many `run` steps `mstep` takes
;   reachable     :: state -> bool     program-specific invariant
;   state-measure :: state -> ordinal  lexicographic progress measure
;
; bound by the following constraints:
;
;   MSTEP-IS-RUN
;       (mstep s) equals (run (mstep-count s) s) — so every abstract
;       step corresponds to a real run.  This grounds the framework in
;       the concrete WASM interpreter: no abstract step can cheat.
;
;   REACHABLE-PRESERVED-BY-MSTEP
;       A non-terminal step taken from inside the invariant stays in
;       the invariant (unless it happens to land on a terminal).
;
;   MEASURE-DECREASES-ON-MSTEP
;       The ordinal measure strictly decreases on every non-terminal
;       step taken from the invariant.
;
;   MSTEP-COUNT-POSITIVE
;       Every non-terminal step consumes at least one real-run step.
;       Without this, `mstep` could fraudulently stand still.
;
; A program specialises the framework by choosing granularity:
;
;   - For unseen / recursive code you might pick `mstep = run 1` with
;     a structural state measure — this yields a single-step refinement
;     proof with no implementation-specific fuel.
;
;   - For a well-understood loop (like Euclidean GCD) you can pick a
;     larger `mstep-count` (e.g. 13, one full loop iteration) and reuse
;     existing multi-step lemmas.  The framework's correctness is the
;     same either way; granularity is a tactical choice.
;
; The exported termination results, `terminalp-of-run-to-terminal` and
; `run-reaches-terminal-from-reachable`, state that starting from any
; reachable state, some real number of `run` steps reaches a terminal
; value (:trap or (:done ...)).  Program authors then discharge the
; program-specific obligation that the terminal is `(:done correct)`
; — NOT `:trap`.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

(in-package "WASM")

(include-book "../execution")
(include-book "wasm-run-utils")
(include-book "ordinals/lexicographic-ordering" :dir :system)

(set-induction-depth-limit 1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §1.  Terminal-value recognisers.
;;
;; The interpreter's "machine value" space is the disjoint union of
;;   (a) genuine states (satisfying `statep`),
;;   (b) the bare keyword :trap, and
;;   (c) pairs of the form (:done . rest), which wrap a successful
;;       exit state.
;; The recognisers below are shape tests; they do NOT assume statep
;; or anything about the contents of :done.

(defund trapp (x)
  (declare (xargs :guard t))
  (eq x :trap))

(defund done-statep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (eq (car x) :done)))

(defund terminalp (x)
  (declare (xargs :guard t))
  (or (trapp x)
      (done-statep x)))

(defthm terminalp-when-trap
  (terminalp :trap)
  :hints (("Goal" :in-theory (enable terminalp trapp))))

(defthm terminalp-of-done
  (terminalp (cons :done rest))
  :hints (("Goal" :in-theory (enable terminalp done-statep))))

(defthm not-terminalp-when-statep
  ;; A real state is never a terminal value.
  (implies (statep s)
           (not (terminalp s)))
  :hints (("Goal" :in-theory (enable terminalp trapp done-statep statep))))

(defthm done-statep-implies-not-trapp
  (implies (done-statep x)
           (not (trapp x)))
  :hints (("Goal" :in-theory (enable done-statep trapp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §2.  Abstract machine step, reachability, measure.

(encapsulate
  (((mstep *)         => *)
   ((mstep-count *)   => *)
   ((reachable *)     => *)
   ((state-measure *) => *))

  ;; Default witnesses (trivial): the "mstep" is (run 1 s); reachability
  ;; is empty; the measure is always zero.  These satisfy every
  ;; constraint vacuously, so the encapsulate admits.
  (local (defun mstep-count (s) (declare (ignore s)) 1))
  (local (defun mstep (s) (run (mstep-count s) s)))
  (local (defun reachable (s) (declare (ignore s)) nil))
  (local (defun state-measure (s) (declare (ignore s)) 0))

  ;; Every abstract step is a real number of concrete run steps.
  ;; `:rule-classes nil` keeps this fact available for explicit `:use`
  ;; hints while preventing it from unfolding mstep (and thereby
  ;; defeating the `measure-decreases-on-mstep` rewrite) during
  ;; termination proofs.
  (defthm mstep-is-run
    (equal (mstep s)
           (run (mstep-count s) s))
    :rule-classes nil)

  ;; The step count is a natural.
  (defthm natp-of-mstep-count
    (natp (mstep-count s))
    :rule-classes :type-prescription)

  ;; Every abstract step taken from a reachable non-terminal consumes at
  ;; least one real-run tick (so it can't stand still fraudulently).
  (defthm mstep-count-positive
    (implies (and (reachable s)
                  (not (terminalp s)))
             (< 0 (mstep-count s)))
    :rule-classes :linear)

  ;; Reachable states are real states (so the concrete `run` laws
  ;; apply).  Terminals are never reachable.
  (defthm statep-when-reachable
    (implies (reachable s)
             (statep s))
    :rule-classes :forward-chaining)

  ;; An mstep from a reachable state either terminates or lands on a
  ;; real state — no malformed junk in between.  (For the concrete
  ;; WASM interpreter this is inhabited because `run` only ever returns
  ;; a statep, a :trap, or a (:done ...).)
  (defthm mstep-statep-or-terminalp
    (implies (reachable s)
             (or (statep (mstep s))
                 (terminalp (mstep s))))
    :rule-classes nil)

  ;; The state-measure is always an ordinal (needed for o< induction).
  (defthm o-p-of-state-measure
    (o-p (state-measure s)))

  ;; Reachability is closed under non-terminal mstep (as long as the
  ;; step itself didn't fall off into a terminal; a terminal is not a
  ;; state so asking whether it's reachable is a category error).
  (defthm reachable-preserved-by-mstep
    (implies (and (reachable s)
                  (not (terminalp s))
                  (not (terminalp (mstep s))))
             (reachable (mstep s))))

  ;; Strict ordinal decrease on every non-terminal step from inside the
  ;; invariant.  This is the key well-foundedness ingredient that
  ;; replaces fuel.
  (defthm measure-decreases-on-mstep
    (implies (and (reachable s)
                  (not (terminalp s)))
             (o< (state-measure (mstep s))
                 (state-measure s)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §3.  Fuel-free execution to termination.
;;
;; `run-to-terminal` is admitted by well-founded recursion on state-measure,
;; not on a step count.  From any reachable state it returns a terminal
;; value; from any non-reachable state it returns the input unchanged
;; (we are agnostic outside the invariant).

(defun run-to-terminal (s)
  (declare (xargs :measure (state-measure s)
                  :well-founded-relation o<
                  :guard t
                  :verify-guards nil))
  (cond ((not (reachable s)) s)
        ((terminalp s)        s)
        (t (run-to-terminal (mstep s)))))

(defthm run-to-terminal-of-terminal
  (implies (terminalp s)
           (equal (run-to-terminal s) s)))

(defthm run-to-terminal-of-non-reachable
  (implies (not (reachable s))
           (equal (run-to-terminal s) s)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §4.  Main export: every reachable state reaches a terminal.

(defthm terminalp-of-run-to-terminal
  (implies (reachable s)
           (terminalp (run-to-terminal s)))
  :hints (("Goal" :induct (run-to-terminal s))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §5.  Fuel-count witness: run-to-terminal corresponds to some
;; concrete `run n s`.
;;
;; Accumulating mstep-counts along the trajectory gives a natural fuel
;; value n such that (run n s) equals (run-to-terminal s).  This closes
;; the abstract-to-concrete loop.

(defun run-to-terminal-fuel (s)
  (declare (xargs :measure (state-measure s)
                  :well-founded-relation o<
                  :guard t
                  :guard-hints (("Goal" :in-theory (enable natp)))
                  :verify-guards nil))
  (cond ((not (reachable s)) 0)
        ((terminalp s)        0)
        (t (+ (mstep-count s)
              (run-to-terminal-fuel (mstep s))))))

(defthm natp-of-run-to-terminal-fuel
  (natp (run-to-terminal-fuel s))
  :rule-classes :type-prescription)

(defthm run-to-terminal-is-run-fuel
  (implies (reachable s)
           (equal (run (run-to-terminal-fuel s) s)
                  (run-to-terminal s)))
  :hints (("Goal"
           :induct (run-to-terminal s)
           :in-theory (enable run-split-when-statep))
          ("Subgoal *1/2"
           :use ((:instance mstep-is-run (s s))
                 (:instance mstep-statep-or-terminalp (s s))
                 (:instance run-split-when-statep
                            (m (mstep-count s))
                            (n (run-to-terminal-fuel (mstep s)))
                            (state s))))))

;; Exported form: there exists a natural fuel value on which plain `run`
;; reaches a terminal from every reachable state.
(defthm run-reaches-terminal-from-reachable
  (implies (reachable s)
           (and (natp (run-to-terminal-fuel s))
                (terminalp (run (run-to-terminal-fuel s) s))))
  :hints (("Goal"
           :use ((:instance run-to-terminal-is-run-fuel (s s))
                 (:instance terminalp-of-run-to-terminal (s s)))
           :in-theory (disable run-to-terminal-is-run-fuel
                               terminalp-of-run-to-terminal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; §6.  Housekeeping.

(in-theory (disable run-to-terminal
                    run-to-terminal-fuel))
