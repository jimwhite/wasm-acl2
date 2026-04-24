; atc/codegen/templates.lisp
;
; Template family for generating ATC-fragment step functions from the
; shapes of `execute-<op>` defuns in execution.lisp.
;
; The spec file execution.lisp is the single source of truth.  The
; generator here does NOT introduce a new DSL; it provides a library of
; emission templates, one per *structural shape* occurring in the spec.
; The operator-specific behavior (which local slot is read, what
; arithmetic is performed, etc.) is expressed with ordinary ATC
; operators; only the surrounding plumbing comes from the template.
;
; Each generated function has signature
;
;     (NAME st sp <op-args>)  ==>  (mv new-st new-sp)
;
; and corresponds to one step of the spec function `execute-<op>`.  No
; dispatch loop.  No `halted`/`ok`/`safe` gating inside — trap
; conditions are hoisted into the ACL2 guard on the generated function.
;
; Shapes implemented today:
;
;   * :local-idx-pusher
;       Matches `execute-local.get`: read nth-local, push to operand
;       stack, advance.  Spec shape (quoting execution.lisp:1000-1013):
;
;           (b* ((x (first args))
;                (locals (current-locals state))
;                (ostack (current-operand-stack state))
;                ((when (not (< x (len locals)))) :trap)
;                (val (nth-local x locals))
;                (ostack (push-operand val ostack))
;                (state (update-current-operand-stack ostack state)))
;             (advance-instrs state))
;
;   * :local-idx-popper
;       Matches `execute-local.set`: pop operand, write nth-local,
;       advance.
;
; New shapes (tee, drop, const, i32 binop, ...) are added as new
; macros here; each is a ~10-line ATC-fragment defun built from the
; struct accessors and the standard ATC operators.

(in-package "ACL2")

(include-book "state-model")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Shape: local-idx-pusher (local.get).
;;
;; Generated body, fully spelled out:
;;
;;   (let* ((val (c::declar (struct-|wst|-read-|loc|-element x st)))
;;          (st  (struct-|wst|-write-|op|-element sp val st))
;;          (sp  (c::assign (c::add-sint-sint sp (c::sint-dec-const 1)))))
;;     (mv st sp))
;;
;; Guard: struct-wst-p st, sintp sp/x, 0 <= sp < 64, 0 <= x < 16.

(defmacro gen-local-idx-pusher (name)
  `(defun ,name (|st| |sp| |x|)
     (declare (xargs :guard (and (struct-|wst|-p |st|)
                                 (c::sintp |sp|)
                                 (c::sintp |x|)
                                 (<= 0 (c::integer-from-sint |sp|))
                                 (< (c::integer-from-sint |sp|) 63)
                                 (<= 0 (c::integer-from-sint |x|))
                                 (< (c::integer-from-sint |x|) 16))
                     :guard-hints
                     (("Goal"
                       :in-theory
                       (enable c::add-sint-sint
                               c::add-sint-sint-okp
                               c::sint-integerp-alt-def
                               c::integer-from-cinteger-alt-def
                               c::declar
                               |STRUCT-wst-op-INDEX-OKP|
                               |STRUCT-wst-loc-INDEX-OKP|)))))
     (let* ((|val| (c::declar (struct-|wst|-read-|loc|-element |x| |st|)))
            (|st|  (struct-|wst|-write-|op|-element |sp| |val| |st|))
            (|sp|  (c::assign (c::add-sint-sint |sp|
                                                (c::sint-dec-const 1)))))
       (declare (ignorable |st|))
       |sp|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Shape: local-idx-popper (local.set).
;;
;;   (let* ((idx (c::declar (c::sub-sint-sint sp (c::sint-dec-const 1))))
;;          (val (c::declar (struct-|wst|-read-|op|-element idx st)))
;;          (st  (struct-|wst|-write-|loc|-element x val st))
;;          (sp  (c::assign idx)))
;;     (mv st sp))
;;
;; Guard: 1 <= sp <= 64, 0 <= x < 16.

(defmacro gen-local-idx-popper (name)
  `(defun ,name (|st| |sp| |x|)
     (declare (xargs :guard (and (struct-|wst|-p |st|)
                                 (c::sintp |sp|)
                                 (c::sintp |x|)
                                 (< 0 (c::integer-from-sint |sp|))
                                 (<= (c::integer-from-sint |sp|) 64)
                                 (<= 0 (c::integer-from-sint |x|))
                                 (< (c::integer-from-sint |x|) 16))
                     :guard-hints
                     (("Goal"
                       :in-theory
                       (enable c::sub-sint-sint
                               c::sub-sint-sint-okp
                               c::sint-integerp-alt-def
                               c::integer-from-cinteger-alt-def
                               c::declar
                               |STRUCT-wst-op-INDEX-OKP|
                               |STRUCT-wst-loc-INDEX-OKP|)))))
     (let* ((|idx| (c::declar (c::sub-sint-sint |sp|
                                                (c::sint-dec-const 1))))
            (|val| (c::declar (struct-|wst|-read-|op|-element |idx| |st|)))
            (|st|  (struct-|wst|-write-|loc|-element |x| |val| |st|))
            (|sp|  (c::assign |idx|)))
       (declare (ignorable |st|))
       |sp|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The one-line generator entry point.  `shape' selects the template;
;; everything else is filled in by the template itself.
;;
;; Usage:
;;   (gen-exec-op :local-idx-pusher |exec-local.get|)
;;   (gen-exec-op :local-idx-popper |exec-local.set|)
;;
;; The shape is the generator's knowledge of how the spec is structured;
;; it is not an annotation on the spec, and the spec in execution.lisp
;; is unchanged.

(defmacro gen-exec-op (shape name)
  (case shape
    (:local-idx-pusher `(gen-local-idx-pusher ,name))
    (:local-idx-popper `(gen-local-idx-popper ,name))
    (t (er hard? 'gen-exec-op
           "Unknown shape ~x0.  Add a template in templates.lisp."
           shape))))
