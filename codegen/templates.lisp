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
;; Shape: local-idx-teer (local.tee).
;;
;; Peek top of operand stack, write to local x, leave sp unchanged.
;;
;;   (let* ((idx (c::declar (c::sub-sint-sint sp (c::sint-dec-const 1))))
;;          (val (c::declar (struct-|wst|-read-|op|-element idx st)))
;;          (st  (struct-|wst|-write-|loc|-element x val st)))
;;     sp)

(defmacro gen-local-idx-teer (name)
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
            (|st|  (struct-|wst|-write-|loc|-element |x| |val| |st|)))
       (declare (ignorable |st|))
       |sp|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Shape: drop.  Pop one operand; state struct is unchanged.
;;
;;   (c::sub-sint-sint sp (c::sint-dec-const 1))

(defmacro gen-drop (name)
  `(defun ,name (|st| |sp|)
     (declare (xargs :guard (and (struct-|wst|-p |st|)
                                 (c::sintp |sp|)
                                 (< 0 (c::integer-from-sint |sp|))
                                 (<= (c::integer-from-sint |sp|) 64))
                     :guard-hints
                     (("Goal"
                       :in-theory
                       (enable c::sub-sint-sint
                               c::sub-sint-sint-okp
                               c::sint-integerp-alt-def
                               c::integer-from-cinteger-alt-def)))))
     (declare (ignore |st|))
     (c::sub-sint-sint |sp| (c::sint-dec-const 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Shape: i32-const.  Push immediate n onto operand stack; sp++.
;;
;; The immediate is passed as a u32 uint parameter.
;;
;;   (let* ((st (struct-|wst|-write-|op|-element sp n st))
;;          (sp (c::assign (c::add-sint-sint sp (c::sint-dec-const 1)))))
;;     sp)

(defmacro gen-i32-const (name)
  `(defun ,name (|st| |sp| |n|)
     (declare (xargs :guard (and (struct-|wst|-p |st|)
                                 (c::sintp |sp|)
                                 (c::uintp |n|)
                                 (<= 0 (c::integer-from-sint |sp|))
                                 (< (c::integer-from-sint |sp|) 63))
                     :guard-hints
                     (("Goal"
                       :in-theory
                       (enable c::add-sint-sint
                               c::add-sint-sint-okp
                               c::sint-integerp-alt-def
                               c::integer-from-cinteger-alt-def
                               c::declar
                               |STRUCT-wst-op-INDEX-OKP|)))))
     (let* ((|st| (struct-|wst|-write-|op|-element |sp| |n| |st|))
            (|sp| (c::assign (c::add-sint-sint |sp|
                                               (c::sint-dec-const 1)))))
       (declare (ignorable |st|))
       |sp|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Shape: i32-binop-total — add/sub/mul/and/or/xor.
;;
;; Pop two operands, apply the C uint op (modular 2^32), push result.
;; sp decreases by 1.  Parameterized by the ATC op symbol, e.g.
;; c::add-uint-uint.
;;
;;   (let* ((i1 (c::declar (c::sub-sint-sint sp (c::sint-dec-const 2))))
;;          (i2 (c::declar (c::sub-sint-sint sp (c::sint-dec-const 1))))
;;          (v1 (c::declar (struct-|wst|-read-|op|-element i1 st)))
;;          (v2 (c::declar (struct-|wst|-read-|op|-element i2 st)))
;;          (r  (c::declar (<op> v1 v2)))
;;          (st (struct-|wst|-write-|op|-element i1 r st))
;;          (sp (c::assign i2)))
;;     sp)

(defmacro gen-i32-binop-total (name op)
  `(defun ,name (|st| |sp|)
     (declare (xargs :guard (and (struct-|wst|-p |st|)
                                 (c::sintp |sp|)
                                 (<= 2 (c::integer-from-sint |sp|))
                                 (<= (c::integer-from-sint |sp|) 64))
                     :guard-hints
                     (("Goal"
                       :in-theory
                       (enable c::sub-sint-sint
                               c::sub-sint-sint-okp
                               c::sint-integerp-alt-def
                               c::integer-from-cinteger-alt-def
                               c::declar
                               |STRUCT-wst-op-INDEX-OKP|)))))
     (let* ((|i1| (c::declar (c::sub-sint-sint |sp|
                                               (c::sint-dec-const 2))))
            (|i2| (c::declar (c::sub-sint-sint |sp|
                                               (c::sint-dec-const 1))))
            (|v1| (c::declar (struct-|wst|-read-|op|-element |i1| |st|)))
            (|v2| (c::declar (struct-|wst|-read-|op|-element |i2| |st|)))
            (|r|  (c::declar (,op |v1| |v2|)))
            (|st| (struct-|wst|-write-|op|-element |i1| |r| |st|))
            (|sp| (c::assign |i2|)))
       (declare (ignorable |st|))
       |sp|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Shape: i32-binop-nz — i32.div_u, i32.rem_u.
;;
;; Like i32-binop-total but the C op has an -okp predicate that
;; requires the divisor to be nonzero.  We hoist that into the ACL2
;; guard, so the body stays linear.  Parameterized by (op, op-okp).

(defmacro gen-i32-binop-nz (name op op-okp)
  `(defun ,name (|st| |sp|)
     (declare (xargs :guard
                     (and (struct-|wst|-p |st|)
                          (c::sintp |sp|)
                          (<= 2 (c::integer-from-sint |sp|))
                          (<= (c::integer-from-sint |sp|) 64)
                          (,op-okp
                           (struct-|wst|-read-|op|-element
                            (c::sub-sint-sint |sp| (c::sint-dec-const 2))
                            |st|)
                           (struct-|wst|-read-|op|-element
                            (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                            |st|)))
                     :guard-hints
                     (("Goal"
                       :in-theory
                       (enable c::sub-sint-sint
                               c::sub-sint-sint-okp
                               c::sint-integerp-alt-def
                               c::integer-from-cinteger-alt-def
                               c::declar
                               |STRUCT-wst-op-INDEX-OKP|)))))
     (let* ((|i1| (c::declar (c::sub-sint-sint |sp|
                                               (c::sint-dec-const 2))))
            (|i2| (c::declar (c::sub-sint-sint |sp|
                                               (c::sint-dec-const 1))))
            (|v1| (c::declar (struct-|wst|-read-|op|-element |i1| |st|)))
            (|v2| (c::declar (struct-|wst|-read-|op|-element |i2| |st|)))
            (|r|  (c::declar (,op |v1| |v2|)))
            (|st| (struct-|wst|-write-|op|-element |i1| |r| |st|))
            (|sp| (c::assign |i2|)))
       (declare (ignorable |st|))
       |sp|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The one-line generator entry point.  `shape' selects the template;
;; everything else is filled in by the template itself.
;;
;; Usage:
;;   (gen-exec-op :local-idx-pusher |exec_local_get|)
;;   (gen-exec-op :local-idx-popper |exec_local_set|)
;;   (gen-exec-op :local-idx-teer   |exec_local_tee|)
;;   (gen-exec-op :drop             |exec_drop|)
;;   (gen-exec-op :i32-const        |exec_i32_const|)
;;   (gen-exec-op :i32-binop-total  |exec_i32_add| c::add-uint-uint)
;;   (gen-exec-op :i32-binop-nz     |exec_i32_rem_u| c::rem-uint-uint
;;                                                   c::rem-uint-uint-okp)
;;
;; The shape is the generator's knowledge of how the spec is structured;
;; it is not an annotation on the spec, and the spec in execution.lisp
;; is unchanged.

(defmacro gen-exec-op (shape name &rest args)
  (case shape
    (:local-idx-pusher `(gen-local-idx-pusher ,name))
    (:local-idx-popper `(gen-local-idx-popper ,name))
    (:local-idx-teer   `(gen-local-idx-teer   ,name))
    (:drop             `(gen-drop             ,name))
    (:i32-const        `(gen-i32-const        ,name))
    (:i32-binop-total  `(gen-i32-binop-total  ,name ,(first args)))
    (:i32-binop-nz     `(gen-i32-binop-nz     ,name ,(first args)
                                                    ,(second args)))
    (t (er hard? 'gen-exec-op
           "Unknown shape ~x0.  Add a template in templates.lisp."
           shape))))
