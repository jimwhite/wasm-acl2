; atc/codegen/demo.lisp
;
; Demonstration: the template-family generator emits ATC step
; functions for seven operations in ../../execution.lisp, by shape.
; Each generated defun is admitted by ACL2 with full guard
; verification and translated to a standalone C function by ATC.
;
; The spec file execution.lisp is not edited.  The per-op work here is
; one line of `gen-exec-op' per operation.  Compare the resulting
; demo.c to the ~300 lines of hand-written opcode arms that would be
; needed to cover the same seven ops inside `|exec$loop|'.

(in-package "ACL2")

(include-book "templates")

;; Variable/local ops.
(gen-exec-op :local-idx-pusher |exec_local_get|)
(gen-exec-op :local-idx-popper |exec_local_set|)
(gen-exec-op :local-idx-teer   |exec_local_tee|)

;; Parametric.
(gen-exec-op :drop             |exec_drop|)

;; Numeric: i32.const immediate.
(gen-exec-op :i32-const        |exec_i32_const|)

;; i32 binops — total (no trap).
(gen-exec-op :i32-binop-total  |exec_i32_add| c::add-uint-uint)

;; i32 binops — nonzero-divisor (trap hoisted into ACL2 guard).
(gen-exec-op :i32-binop-nz     |exec_i32_rem_u|
                               c::rem-uint-uint
                               c::rem-uint-uint-okp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Emit C.

(c::atc |wst|
        |exec_local_get|
        |exec_local_set|
        |exec_local_tee|
        |exec_drop|
        |exec_i32_const|
        |exec_i32_add|
        |exec_i32_rem_u|
        :file-name "demo"
        :header t
        :proofs nil)
