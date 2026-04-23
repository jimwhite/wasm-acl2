; wasm-loader.lisp — translate a Kestrel `parse-module` result into the
; list of `funcinst`s expected by our execution model.
;
; The Kestrel parser (kestrel/wasm/parse-binary.lisp) produces module
; sections whose instruction lists are structurally almost identical to
; what execution.lisp consumes, with two small normalisations required:
;
;   1. Blocktype: the parser emits `:empty` (or a valtype symbol like
;      `:i32`) where our model expects a numeric arity (0 or 1).
;
;   2. `:instrs` wrapper: the parser wraps a code body as
;      `((:instrs . <flat-list>))`; our model wants just the flat list.
;
; Everything else — opcode tags, operand shapes, `:block`/`:loop` args,
; label indices — already lines up byte-for-byte with the body consts in
; proof-*-spec.lisp (verified for gcd.wasm on 2026-04-23).

(in-package "WASM")

(include-book "../execution")
(include-book "kestrel/wasm/parse-binary" :dir :system)

(set-state-ok t)

;; Loader code is used only at make-event/codegen time to translate a
;; parsed module into a defconst. We don't reason about it, so program
;; mode is fine and avoids guard obligations on generic alist walks.
(program)

;; --- Blocktype translation -------------------------------------------------
;;
;; WASM blocktypes in the binary form are either empty (no value produced),
;; a single valtype (one value produced), or a typeidx (an already-declared
;; functype — not yet handled here; functions used in call_indirect etc.
;; can grow this translator when we get there). Our `execute-block` /
;; `execute-loop` take a numeric *arity*, so we collapse to 0 or 1.

(defun blocktype->arity (bt)
  (declare (xargs :guard t))
  (case bt
    (:empty 0)
    ((:i32 :i64 :f32 :f64) 1)
    (t (if (natp bt)
           ;; a typeidx — unsupported here
           (prog2$ (er hard? 'blocktype->arity
                       "typeidx blocktype ~x0 not supported by loader" bt)
                   0)
         (prog2$ (er hard? 'blocktype->arity "unknown blocktype ~x0" bt)
                 0)))))

;; --- Instruction list translation ------------------------------------------
;;
;; Walk a list of parsed instructions; rewrite `:block`/`:loop`/`:if` args
;; recursively.

(mutual-recursion
 (defun translate-instr (i)
   (declare (xargs :guard t
                   :measure (acl2-count i)))
   (cond ((atom i) i)
         ((and (eq (first i) :block)
               (consp (cdr i))
               (consp (cddr i)))
          ;; (:block <blocktype> <body-instrs>)
          (list :block
                (blocktype->arity (second i))
                (translate-instrs (third i))))
         ((and (eq (first i) :loop)
               (consp (cdr i))
               (consp (cddr i)))
          (list :loop
                (blocktype->arity (second i))
                (translate-instrs (third i))))
         ((and (eq (first i) :if)
               (consp (cdr i))
               (consp (cddr i))
               (consp (cdddr i)))
          ;; (:if <blocktype> <then-body> <else-body>)
          (list :if
                (blocktype->arity (second i))
                (translate-instrs (third i))
                (translate-instrs (fourth i))))
         (t i)))

 (defun translate-instrs (instrs)
   (declare (xargs :guard t
                   :measure (acl2-count instrs)))
   (if (atom instrs)
       nil
     (cons (translate-instr (first instrs))
           (translate-instrs (rest instrs))))))

;; --- Section lookup helpers ------------------------------------------------

(defun section-contents (id sections)
  ;; sections is a list of ((:id . id) (:contents . contents)); return the
  ;; contents for id, or nil if the section is absent.
  (declare (xargs :guard t))
  (cond ((atom sections) nil)
        ((and (alistp (car sections))
              (equal (cdr (assoc :id (car sections))) id))
         (cdr (assoc :contents (car sections))))
        (t (section-contents id (cdr sections)))))

(defun functype->param-count (ft)
  (declare (xargs :guard t))
  (len (cdr (assoc :parameter-type ft))))

(defun functype->return-arity (ft)
  (declare (xargs :guard t))
  (len (cdr (assoc :result-type ft))))

(defun code->local-count (code)
  ;; parse-binary expands run-length local groups into a flat list; the
  ;; local count is simply its length.
  (declare (xargs :guard t))
  (len (cdr (assoc :locals code))))

(defun code->body (code)
  (declare (xargs :guard t))
  (cdr (assoc :instrs (cdr (assoc :body code)))))

;; --- Build one funcinst ----------------------------------------------------

(defun build-funcinst (typeidx types codes)
  ;; typeidx indexes into `types`; codes[i] is the i'th function's code.
  ;; We assume this is called with `(nth i funcidxs)`, `types`, and the
  ;; i'th element of `codes` spliced out by the caller.
  (declare (xargs :guard t))
  (let* ((ft (nth typeidx types))
         (code (car codes)))
    (make-funcinst
     :param-count (functype->param-count ft)
     :local-count (code->local-count code)
     :return-arity (functype->return-arity ft)
     :body (translate-instrs (code->body code)))))

(defun build-funcinsts-aux (funcidxs types codes)
  (declare (xargs :guard t
                  :measure (acl2-count funcidxs)))
  (if (or (atom funcidxs) (atom codes))
      nil
    (cons (build-funcinst (car funcidxs) types codes)
          (build-funcinsts-aux (cdr funcidxs) types (cdr codes)))))

(defun module->funcinsts (sections)
  ;; Top-level: given parsed sections, return the list of funcinsts in
  ;; source order (same order as the :code section).
  (declare (xargs :guard t))
  (let* ((types    (section-contents :type sections))
         (funcidxs (section-contents :function sections))
         (codes    (section-contents :code sections)))
    (build-funcinsts-aux funcidxs types codes)))

;; --- File-level entry point ------------------------------------------------

;; Returns (mv erp funcinsts state). Suitable for use inside make-event.
(defun load-wasm-funcinsts (path acl2::state)
  (declare (xargs :mode :program :stobjs acl2::state))
  (mv-let (erp sections acl2::state)
    (parse-module path acl2::state)
    (if erp
        (mv erp nil acl2::state)
      (mv nil (module->funcinsts sections) acl2::state))))
