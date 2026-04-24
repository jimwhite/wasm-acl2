; atc/codegen/loop-demo.lisp
;
; Generate an 8-opcode execution loop from shape tags, and emit a C file
; containing the dispatcher as `exec_loop`.
;
; The table below is the entire per-op work.  No additional spec files,
; no hand-written arm bodies.  Compare to wasm-vm1.lisp |exec$loop|
; which has ~650 hand-written lines covering roughly this same set.

(in-package "ACL2")

(include-book "standalone-state")
(include-book "loop")

(gen-exec-loop
  |exec_loop|
  (:end-toplevel    #x0b)
  (:drop            #x1a)
  (:local-idx-pusher #x20)
  (:local-idx-popper #x21)
  (:local-idx-teer   #x22)
  (:i32-const        #x41)                       ; u8 imm (simplified)
  (:i32-binop-total  #x6a c::add-uint-uint)      ; i32.add
  (:i32-binop-nz     #x70 c::rem-uint-uint))     ; i32.rem_u

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Non-recursive entry point that initializes the scalar registers and
;; drives the loop.  (ATC requires recursive target functions to be
;; called by another target function.)

(defun |exec_run| (|st| |pc| |wasm_buf|)
  (declare (xargs
    :guard (and (c::star (struct-|wst|-p |st|))
                (c::sintp |pc|)
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (object-|wasm_buf|-p |wasm_buf|))
    :guard-hints
    (("Goal" :in-theory (enable c::declar c::sint-integerp-alt-def)))))
  (let* ((|sp|     (c::declar (c::sint-dec-const 0)))
         (|nl|     (c::declar (c::sint-dec-const 0)))
         (|halted| (c::declar (c::sint-dec-const 0)))
         (|fuel|   (c::declar (c::sint-dec-const 100000))))
    (mv-let (|st| |sp| |nl| |pc| |halted| |fuel|)
        (|exec_loop| |st| |sp| |nl| |pc| |halted| |fuel| |wasm_buf|)
      (declare (ignore |sp| |nl| |pc| |halted| |fuel|))
      |st|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Emit C.

(c::atc |wasm_buf|
        |wst|
        |exec_loop|
        |exec_run|
        :file-name "loop-demo"
        :header t
        :proofs nil)
