; atc/codegen/demo.lisp
;
; Demonstration: use the template-family generator to emit the ATC
; step functions for execute-local.get and execute-local.set from
; execution.lisp, by shape.  The generated defuns are admitted by
; ACL2 with full guard verification.
;
; The spec file execution.lisp is not edited.  The generator's
; templates live in templates.lisp.
;
; Compare the bodies emitted here against the hand-written opcode
; arms in ../wasm-vm1.lisp: each generated defun is ~6 meaningful
; lines, instead of the ~40 lines of ok/safe/halted plumbing the
; in-loop arm requires.  The shape is that of the ACL2 spec, just
; re-expressed over the concrete struct/sp representation.

(in-package "ACL2")

(include-book "templates")

;; Shape: "local-idx pusher" — matches `wasm::execute-local.get`.
(gen-exec-op :local-idx-pusher |exec_local_get|)

;; Shape: "local-idx popper" — matches `wasm::execute-local.set`.
(gen-exec-op :local-idx-popper |exec_local_set|)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Emit C for the generated step functions.  One free-standing C
;; function per ACL2 defun, no enclosing dispatch.  The struct `wst'
;; from state-model is emitted as a C `struct wst' and passed by
;; pointer; the mv-return becomes a by-ref `sp' out-parameter.

(c::atc |wst|
        |exec_local_get|
        |exec_local_set|
        :file-name "demo"
        :header t
        :proofs nil)
