; atc/codegen/integration-demo.lisp
;
; Integration: plug the generated execution loop into the hand-written
; `.wasm' reader in ../wasm-vm1.lisp.  The pipeline is:
;
;       main.c → fread → wasm_buf[65536]
;                  │
;                  ▼
;          parse_module       (hand-written, in wasm-vm1.lisp)
;                  │   fills |wmod|: body_off, body_len, num_locals,
;                  │                 export_off, export_len
;                  ▼
;          run_wasm_gen       (THIS BOOK, generated)
;                  │   seeds loc[0..1] with the two u32 args,
;                  │   then calls exec_loop_gen (generated from a table),
;                  │   then reads op[0] as the result.
;                  ▼
;              uint result
;
; Deliberate contrast with ../wasm-vm1.lisp:
;   - |exec$loop|  there — HAND-WRITTEN ~650 lines of opcode arms.
;   - |exec_loop_gen| here — GENERATED from an 8-row table.
; Both share ../wasm-vm1.lisp's state layout and parser.

(in-package "ACL2")

(include-book "../wasm-vm1")
(include-book "loop")

;; wasm-vm1.lisp declares `sint-max->=-65600' LOCALly, so we re-declare
;; the concrete SINT_MAX bound here for the generated loop's guard proofs.
(defrule sint-max->=-65600-for-codegen
  (>= (c::sint-max) 65600)
  :rule-classes :linear
  :enable (c::sint-max c::int-bits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generate the dispatcher.  Same 8-opcode table as loop-demo.lisp; bodies
;; are spliced in by the template-family emitters in loop.lisp.

(gen-exec-loop
  |exec_loop_gen|
  (:end-toplevel    #x0b)
  (:drop            #x1a)
  (:local-idx-pusher #x20)
  (:local-idx-popper #x21)
  (:local-idx-teer   #x22)
  (:i32-const        #x41)                       ; u8 immediate (simplified)
  (:i32-binop-total  #x6a c::add-uint-uint)      ; i32.add
  (:i32-binop-nz     #x70 c::rem-uint-uint))     ; i32.rem_u

;; Needed so `|run_wasm_gen|'s guard proof can see that the loop preserves
;; `struct-|wst|-p'.  Mirrors `struct-wst-p-of-mv-nth-0-exec$loop' in
;; ../wasm-vm1.lisp.
(defrulel struct-wst-p-of-mv-nth-0-exec_loop_gen
  (implies (struct-|wst|-p |st|)
           (struct-|wst|-p
            (mv-nth 0 (|exec_loop_gen| |st| |sp| |nl| |pc| |halted| |fuel|
                                       |wasm_buf|))))
  :induct (|exec_loop_gen| |st| |sp| |nl| |pc| |halted| |fuel| |wasm_buf|)
  :enable (|exec_loop_gen|))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Top-level entry: seed argument locals, drive the loop, return op[0].
;;
;; Mirrors |invoke| in ../wasm-vm1.lisp but calls the generated
;; |exec_loop_gen| instead of the hand-written |exec$loop|.  The caller
;; (main.c, or the equivalent) is responsible for calling |parse_module|
;; first to populate |m|, exactly as wasm-vm1's main does.

(defun |run_wasm_gen| (|st| |m| |a| |b| |wasm_buf|)
  (declare (xargs
    :guard (and (c::star (struct-|wst|-p |st|))
                (c::star (struct-|wmod|-p |m|))
                (c::uintp |a|)
                (c::uintp |b|)
                (object-|wasm_buf|-p |wasm_buf|))
    :guard-hints
    (("Goal" :in-theory (enable object-|wasm_buf|-p
                                c::declar c::assign
                                c::condexpr
                                c::ge-sint-sint
                                c::le-sint-sint
                                c::boolean-from-sint
                                c::sint-from-boolean
                                c::sint-integerp-alt-def)))))
  (let* ((|st| (struct-|wst|-write-|loc|-element
                (c::sint-dec-const 0) |a| |st|))
         (|st| (struct-|wst|-write-|loc|-element
                (c::sint-dec-const 1) |b| |st|))
         ;; Clamp body_off into the exec loop's guard range.
         (|pc_raw| (c::declar (struct-|wmod|-read-|body_off| |m|)))
         (|pc| (c::declar
                (c::condexpr
                 (if (c::boolean-from-sint
                      (c::sint-from-boolean
                       (and (c::boolean-from-sint
                             (c::ge-sint-sint
                              |pc_raw| (c::sint-dec-const 0)))
                            (c::boolean-from-sint
                             (c::le-sint-sint
                              |pc_raw| (c::sint-dec-const 60000))))))
                     |pc_raw|
                   (c::sint-dec-const 0)))))
         (|sp|     (c::declar (c::sint-dec-const 0)))
         (|nl|     (c::declar (c::sint-dec-const 0)))
         (|halted| (c::declar (c::sint-dec-const 0)))
         (|fuel|   (c::declar (c::sint-dec-const 100000))))
    (mv-let (|st| |sp| |nl| |pc| |halted| |fuel|)
        (|exec_loop_gen| |st| |sp| |nl| |pc| |halted| |fuel| |wasm_buf|)
      (declare (ignore |sp| |nl| |pc| |halted| |fuel|))
      (mv (struct-|wst|-read-|op|-element (c::sint-dec-const 0) |st|)
          |st|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Emit C.  We ask ATC to translate only the pieces NEW to this book
;; (plus their freshly-introduced state dependencies); the parser and
;; supporting helpers are already in wasm-vm1.c.

(c::atc |wasm_buf|
        |wmod|
        |wst|
        |check_magic|
        |parse$loop|
        |parse_module|
        |exec_loop_gen|
        |run_wasm_gen|
        :file-name "run"
        :header t
        :proofs nil)
