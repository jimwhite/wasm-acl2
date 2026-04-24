; atc/codegen/loop.lisp
;
; Generator for the execution LOOP (opcode dispatcher).
;
; Relationship to templates.lisp:
;   - templates.lisp emits per-op STEP functions (standalone C entry points).
;   - loop.lisp emits per-op ARM bodies, spliced into a single dispatcher
;     defun that tail-calls itself.  Same shape tags, different emitter.
;
; Why inline rather than call the step functions from the loop:
; ATC passes structs by value, so a step function that "mutates" |st| would
; not actually mutate the caller's st at C level.  The existing hand-written
; `|exec$loop|` in ../wasm-vm1.lisp inlines all arms for exactly this reason.
; We do the same — but by table.
;
; Loop contract (mirrors wasm-vm1.lisp |exec$loop|):
;   (,LOOP-NAME |st| |sp| |nl| |pc| |halted| |fuel| |wasm_buf|) → struct-|wst|
; State machine:
;   sp    : operand stack height  ∈ [0, 64]
;   nl    : label stack height    ∈ [0, 16]   (unused in this demo; present for parity)
;   pc    : program counter       ∈ [0, 60000]
;   halted: boolean sint          ∈ {0, 1}
;   fuel  : remaining steps       ∈ [0, 100000]
; Header: while (!halted && fuel > 0 && pc < 59998) { ... }
; Every arm ends with fuel := fuel - 1 and a tail call.
;
; Each arm emitter takes:
;   opcode   : the dispatch byte (hex literal)
;   loop-name: symbol for the tail call
; plus shape-specific args.  It returns a two-element list (TEST THEN) to be
; spliced into (if TEST THEN ELSE).

(in-package "ACL2")

;; Minimal include: we just need the C package (for `c::...' symbols
;; that appear in the s-exprs we construct).  All actual state — the
;; `|wst|' defstruct, `|wasm_buf|' defobject, `byte-at' macro, and the
;; SINT_MAX bound rule — comes from the HOST at the `gen-exec-loop'
;; call site.

(include-book "kestrel/c/atc/atc" :dir :system
              :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib)
                      (:open-output-channel!)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Program-mode helpers that build S-expressions at macroexpansion time.

(defun emit-test (opcode)
  (declare (xargs :mode :program))
  `(c::eq-sint-sint |b| (c::sint-dec-const ,opcode)))

(defun emit-tail (loop-name)
  (declare (xargs :mode :program))
  `(,loop-name |st| |sp| |nl| |pc| |halted| |fuel| |wasm_buf|))

;; Common trailer: pc += size, halted |= ~ok, fuel -= 1, tail call.
;; `size` is the instruction length in bytes.  `ok-var` is the symbol (e.g. |ok|
;; or |safe|) holding the gating sint.
(defun emit-pc-halted-fuel (size ok-var loop-name)
  (declare (xargs :mode :program))
  (declare (ignore loop-name))
  `((|pc| (c::assign
           (c::add-sint-sint |pc| (c::sint-dec-const ,size))))
    (|halted| (c::assign
               (c::condexpr
                (if (c::boolean-from-sint ,ok-var)
                    |halted|
                  (c::sint-dec-const 1)))))
    (|fuel| (c::assign
             (c::sub-sint-sint |fuel| (c::sint-dec-const 1))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Arm emitters — one per shape.  Each returns (TEST THEN).

;; :local-idx-pusher — opcode 0x20 local.get X
(defun emit-arm-local-idx-pusher (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|x| (c::declar (byte-at (c::add-sint-sint
                                     |pc| (c::sint-dec-const 1)))))
           (|ok| (c::declar
                  (c::sint-from-boolean
                   (and (c::boolean-from-sint
                         (c::lt-sint-sint |sp| (c::sint-dec-const 64)))
                        (c::boolean-from-sint
                         (c::lt-sint-sint |x| (c::sint-dec-const 16)))))))
           (|x_safe| (c::declar
                      (c::condexpr
                       (if (c::boolean-from-sint |ok|)
                           |x|
                         (c::sint-dec-const 0)))))
           (|sp_safe| (c::declar
                       (c::condexpr
                        (if (c::boolean-from-sint |ok|)
                            |sp|
                          (c::sint-dec-const 0)))))
           (|v| (c::declar (struct-|wst|-read-|loc|-element |x_safe| |st|)))
           (|st| (struct-|wst|-write-|op|-element |sp_safe| |v| |st|))
           (|sp| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::add-sint-sint |sp| (c::sint-dec-const 1))
                     |sp|))))
           ,@(emit-pc-halted-fuel 2 '|ok| loop-name))
      ,(emit-tail loop-name))))

;; :local-idx-popper — opcode 0x21 local.set X
(defun emit-arm-local-idx-popper (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|x| (c::declar (byte-at (c::add-sint-sint
                                     |pc| (c::sint-dec-const 1)))))
           (|ok| (c::declar
                  (c::sint-from-boolean
                   (and (c::boolean-from-sint
                         (c::gt-sint-sint |sp| (c::sint-dec-const 0)))
                        (c::boolean-from-sint
                         (c::lt-sint-sint |x| (c::sint-dec-const 16)))))))
           (|x_safe| (c::declar
                      (c::condexpr
                       (if (c::boolean-from-sint |ok|)
                           |x|
                         (c::sint-dec-const 0)))))
           (|idx| (c::declar
                   (c::condexpr
                    (if (c::boolean-from-sint |ok|)
                        (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                      (c::sint-dec-const 0)))))
           (|v| (c::declar (struct-|wst|-read-|op|-element |idx| |st|)))
           (|st| (struct-|wst|-write-|loc|-element |x_safe| |v| |st|))
           (|sp| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                     |sp|))))
           ,@(emit-pc-halted-fuel 2 '|ok| loop-name))
      ,(emit-tail loop-name))))

;; :local-idx-teer — opcode 0x22 local.tee X (peek, not pop)
(defun emit-arm-local-idx-teer (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|x| (c::declar (byte-at (c::add-sint-sint
                                     |pc| (c::sint-dec-const 1)))))
           (|ok| (c::declar
                  (c::sint-from-boolean
                   (and (c::boolean-from-sint
                         (c::gt-sint-sint |sp| (c::sint-dec-const 0)))
                        (c::boolean-from-sint
                         (c::lt-sint-sint |x| (c::sint-dec-const 16)))))))
           (|x_safe| (c::declar
                      (c::condexpr
                       (if (c::boolean-from-sint |ok|)
                           |x|
                         (c::sint-dec-const 0)))))
           (|idx| (c::declar
                   (c::condexpr
                    (if (c::boolean-from-sint |ok|)
                        (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                      (c::sint-dec-const 0)))))
           (|v| (c::declar (struct-|wst|-read-|op|-element |idx| |st|)))
           (|st| (struct-|wst|-write-|loc|-element |x_safe| |v| |st|))
           ,@(emit-pc-halted-fuel 2 '|ok| loop-name))
      ,(emit-tail loop-name))))

;; :drop — opcode 0x1a drop
(defun emit-arm-drop (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|ok| (c::declar
                  (c::gt-sint-sint |sp| (c::sint-dec-const 0))))
           (|sp| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                     |sp|))))
           ,@(emit-pc-halted-fuel 1 '|ok| loop-name))
      ,(emit-tail loop-name))))

;; :i32-const — opcode 0x41 i32.const N (simplified: single u8 immediate)
(defun emit-arm-i32-const (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|n| (c::declar (byte-at (c::add-sint-sint
                                     |pc| (c::sint-dec-const 1)))))
           (|ok| (c::declar
                  (c::lt-sint-sint |sp| (c::sint-dec-const 64))))
           (|sp_safe| (c::declar
                       (c::condexpr
                        (if (c::boolean-from-sint |ok|)
                            |sp|
                          (c::sint-dec-const 0)))))
           (|nv| (c::declar (c::uint-from-sint |n|)))
           (|st| (struct-|wst|-write-|op|-element |sp_safe| |nv| |st|))
           (|sp| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::add-sint-sint |sp| (c::sint-dec-const 1))
                     |sp|))))
           ,@(emit-pc-halted-fuel 2 '|ok| loop-name))
      ,(emit-tail loop-name))))

;; :i32-binop-total — opcode 0x6a etc.; `op` is the ATC c::*-uint-uint symbol.
(defun emit-arm-i32-binop-total (opcode op loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|ok| (c::declar
                  (c::gt-sint-sint |sp| (c::sint-dec-const 1))))
           (|bi| (c::declar
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                     (c::sint-dec-const 0)))))
           (|ai| (c::declar
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::sub-sint-sint |sp| (c::sint-dec-const 2))
                     (c::sint-dec-const 0)))))
           (|bv| (c::declar (struct-|wst|-read-|op|-element |bi| |st|)))
           (|av| (c::declar (struct-|wst|-read-|op|-element |ai| |st|)))
           (|rv| (c::declar (,op |av| |bv|)))
           (|st| (struct-|wst|-write-|op|-element |ai| |rv| |st|))
           (|sp| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                     |sp|))))
           ,@(emit-pc-halted-fuel 1 '|ok| loop-name))
      ,(emit-tail loop-name))))

;; :i32-binop-nz — opcode 0x70 etc.; `op` and `op-okp` are the ATC names.
;; Divisor-zero hoisted into `safe`; body uses a constant-1 fallback to keep
;; the guard proof of `op` trivial even on the not-ok branch.
(defun emit-arm-i32-binop-nz (opcode op loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|ok| (c::declar
                  (c::gt-sint-sint |sp| (c::sint-dec-const 1))))
           (|bi| (c::declar
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                     (c::sint-dec-const 0)))))
           (|ai| (c::declar
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::sub-sint-sint |sp| (c::sint-dec-const 2))
                     (c::sint-dec-const 0)))))
           (|bv| (c::declar (struct-|wst|-read-|op|-element |bi| |st|)))
           (|av| (c::declar (struct-|wst|-read-|op|-element |ai| |st|)))
           (|nz| (c::declar
                  (c::ne-uint-uint |bv| (c::uint-dec-const 0))))
           (|safe| (c::declar
                    (c::sint-from-boolean
                     (and (c::boolean-from-sint |ok|)
                          (c::boolean-from-sint |nz|)))))
           (|bv_safe| (c::declar
                       (c::condexpr
                        (if (c::boolean-from-sint |safe|)
                            |bv|
                          (c::uint-dec-const 1)))))
           (|rv| (c::declar (,op |av| |bv_safe|)))
           (|st| (struct-|wst|-write-|op|-element |ai| |rv| |st|))
           (|sp| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |safe|)
                       (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                     |sp|))))
           ,@(emit-pc-halted-fuel 1 '|safe| loop-name))
      ,(emit-tail loop-name))))

;; :end-toplevel — opcode 0x0b end; in this demo (no labels), halt immediately.
(defun emit-arm-end-toplevel (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|halted| (c::assign (c::sint-dec-const 1)))
           (|fuel| (c::assign
                    (c::sub-sint-sint |fuel| (c::sint-dec-const 1)))))
      ,(emit-tail loop-name))))

;; :end — opcode 0x0b end; label-stack aware.
;; When nl == 0 this is the top-level end and we halt.  Otherwise pop
;; the current label and advance pc by 1.  Strict superset of :end-toplevel.
(defun emit-arm-end (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(if (c::boolean-from-sint
         (c::eq-sint-sint |nl| (c::sint-dec-const 0)))
        (let* ((|halted| (c::assign (c::sint-dec-const 1)))
               (|fuel| (c::assign
                        (c::sub-sint-sint |fuel| (c::sint-dec-const 1)))))
          ,(emit-tail loop-name))
      (let* ((|nl| (c::assign
                    (c::sub-sint-sint |nl| (c::sint-dec-const 1))))
             (|pc| (c::assign
                    (c::add-sint-sint |pc| (c::sint-dec-const 1))))
             (|fuel| (c::assign
                      (c::sub-sint-sint |fuel| (c::sint-dec-const 1)))))
        ,(emit-tail loop-name)))))

;; :i32-unop-eqz — opcode 0x45 i32.eqz (peek-and-replace, no sp change).
(defun emit-arm-i32-unop-eqz (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|ok| (c::declar
                  (c::gt-sint-sint |sp| (c::sint-dec-const 0))))
           (|idx| (c::declar
                   (c::condexpr
                    (if (c::boolean-from-sint |ok|)
                        (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                      (c::sint-dec-const 0)))))
           (|v| (c::declar (struct-|wst|-read-|op|-element |idx| |st|)))
           (|is0| (c::declar
                   (c::sint-from-boolean
                    (or (c::boolean-from-sint
                         (c::eq-uint-uint |v| (c::uint-dec-const 0)))
                        (c::boolean-from-sint
                         (c::eq-uint-uint |v| (c::uint-dec-const 0)))))))
           (|new_v| (c::declar (c::uint-from-sint |is0|)))
           (|st| (struct-|wst|-write-|op|-element |idx| |new_v| |st|))
           ,@(emit-pc-halted-fuel 1 '|ok| loop-name))
      ,(emit-tail loop-name))))

;; :block — opcode 0x02 BT.  Requires the host to provide |scan_end|
;; (as in ../wasm-vm1.lisp) and `lpc`/`lsp`/`lkind` slots on |wst|.
;; Pushes a label with target = pc after matching end.
(defun emit-arm-block (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|ok| (c::declar
                  (c::lt-sint-sint |nl| (c::sint-dec-const 16))))
           (|nl_safe| (c::declar
                       (c::condexpr
                        (if (c::boolean-from-sint |ok|)
                            |nl|
                          (c::sint-dec-const 0)))))
           (|end_pc_raw| (c::declar
                          (|scan_end|
                           (c::add-sint-sint |pc| (c::sint-dec-const 2))
                           |wasm_buf|)))
           (|end_pc| (c::declar
                      (c::condexpr
                       (if (c::boolean-from-sint
                            (c::sint-from-boolean
                             (and (c::boolean-from-sint
                                   (c::ge-sint-sint
                                    |end_pc_raw| (c::sint-dec-const 0)))
                                  (c::boolean-from-sint
                                   (c::le-sint-sint
                                    |end_pc_raw| (c::sint-dec-const 60000))))))
                           |end_pc_raw|
                         (c::sint-dec-const 0)))))
           (|st| (struct-|wst|-write-|lpc|-element |nl_safe| |end_pc| |st|))
           (|st| (struct-|wst|-write-|lsp|-element |nl_safe| |sp| |st|))
           (|st| (struct-|wst|-write-|lkind|-element
                  |nl_safe|
                  (c::uchar-from-sint (c::sint-dec-const 0))
                  |st|))
           (|nl| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::add-sint-sint |nl| (c::sint-dec-const 1))
                     |nl|))))
           ,@(emit-pc-halted-fuel 2 '|ok| loop-name))
      ,(emit-tail loop-name))))

;; :loop-begin — opcode 0x03 BT.  Label target is start of loop body
;; (pc + 2).  kind=1 distinguishes loop from block at br time.
(defun emit-arm-loop-begin (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|ok| (c::declar
                  (c::lt-sint-sint |nl| (c::sint-dec-const 16))))
           (|nl_safe| (c::declar
                       (c::condexpr
                        (if (c::boolean-from-sint |ok|)
                            |nl|
                          (c::sint-dec-const 0)))))
           (|loop_pc| (c::declar
                       (c::add-sint-sint |pc| (c::sint-dec-const 2))))
           (|st| (struct-|wst|-write-|lpc|-element |nl_safe| |loop_pc| |st|))
           (|st| (struct-|wst|-write-|lsp|-element |nl_safe| |sp| |st|))
           (|st| (struct-|wst|-write-|lkind|-element
                  |nl_safe|
                  (c::uchar-from-sint (c::sint-dec-const 1))
                  |st|))
           (|nl| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::add-sint-sint |nl| (c::sint-dec-const 1))
                     |nl|))))
           (|pc| (c::assign |loop_pc|))
           (|halted| (c::assign
                      (c::condexpr
                       (if (c::boolean-from-sint |ok|)
                           |halted|
                         (c::sint-dec-const 1)))))
           (|fuel| (c::assign
                    (c::sub-sint-sint |fuel| (c::sint-dec-const 1)))))
      ,(emit-tail loop-name))))

;; :br and :br-if — opcode 0x0c / 0x0d.  is-conditional decides whether
;; we pop a value and test it before jumping.  The peek bindings
;; (peek_idx/peek_v/cond_true) are only introduced in the conditional
;; case so ATC's ignore-formal rule is satisfied.
(defun emit-arm-br (opcode is-conditional loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|l_byte| (c::declar (byte-at
                                 (c::add-sint-sint
                                  |pc| (c::sint-dec-const 1)))))
           (|pop_ok| (c::declar
                      ,(if is-conditional
                           '(c::gt-sint-sint |sp| (c::sint-dec-const 0))
                         '(c::sint-dec-const 1))))
           (|sp_after_pop|
            (c::declar
             ,(if is-conditional
                  '(c::condexpr
                    (if (c::boolean-from-sint
                         (c::gt-sint-sint |sp| (c::sint-dec-const 0)))
                        (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                      |sp|))
                '|sp|)))
           ,@(and is-conditional
                  '((|peek_idx| (c::declar
                                 (c::condexpr
                                  (if (c::boolean-from-sint
                                       (c::gt-sint-sint
                                        |sp| (c::sint-dec-const 0)))
                                      (c::sub-sint-sint
                                       |sp| (c::sint-dec-const 1))
                                    (c::sint-dec-const 0)))))
                    (|peek_v| (c::declar (struct-|wst|-read-|op|-element
                                          |peek_idx| |st|)))
                    (|cond_true| (c::declar
                                  (c::sint-from-boolean
                                   (or (c::boolean-from-sint
                                        (c::ne-uint-uint
                                         |peek_v|
                                         (c::uint-dec-const 0)))
                                       (c::boolean-from-sint
                                        (c::ne-uint-uint
                                         |peek_v|
                                         (c::uint-dec-const 0)))))))))
           (|take| (c::declar
                    ,(if is-conditional
                         '(c::sint-from-boolean
                           (or (c::boolean-from-sint |cond_true|)
                               (c::boolean-from-sint |cond_true|)))
                       '(c::sint-dec-const 1))))
           (|l_ok| (c::declar
                    (c::lt-sint-sint |l_byte| |nl|)))
           (|target_idx| (c::declar
                          (c::condexpr
                           (if (c::boolean-from-sint |l_ok|)
                               (c::sub-sint-sint
                                (c::sub-sint-sint
                                 |nl| (c::sint-dec-const 1))
                                |l_byte|)
                             (c::sint-dec-const 0)))))
           (|tpc_raw| (c::declar (struct-|wst|-read-|lpc|-element
                                  |target_idx| |st|)))
           (|tsp_raw| (c::declar (struct-|wst|-read-|lsp|-element
                                  |target_idx| |st|)))
           (|tkind_uc| (c::declar (struct-|wst|-read-|lkind|-element
                                   |target_idx| |st|)))
           (|tkind| (c::declar (c::sint-from-uchar |tkind_uc|)))
           (|tpc_ok| (c::declar
                      (c::sint-from-boolean
                       (and (c::boolean-from-sint
                             (c::ge-sint-sint
                              |tpc_raw| (c::sint-dec-const 0)))
                            (c::boolean-from-sint
                             (c::le-sint-sint
                              |tpc_raw| (c::sint-dec-const 60000)))))))
           (|tsp_ok| (c::declar
                      (c::sint-from-boolean
                       (and (c::boolean-from-sint
                             (c::ge-sint-sint
                              |tsp_raw| (c::sint-dec-const 0)))
                            (c::boolean-from-sint
                             (c::le-sint-sint
                              |tsp_raw| (c::sint-dec-const 64)))))))
           (|all_ok| (c::declar
                      (c::sint-from-boolean
                       (and (c::boolean-from-sint |pop_ok|)
                            (c::boolean-from-sint |l_ok|)
                            (c::boolean-from-sint |tpc_ok|)
                            (c::boolean-from-sint |tsp_ok|)))))
           (|new_nl|
            (c::declar
             (c::condexpr
              (if (c::boolean-from-sint
                   (c::sint-from-boolean
                    (and (c::boolean-from-sint |all_ok|)
                         (c::boolean-from-sint |take|))))
                  (c::condexpr
                   (if (c::boolean-from-sint
                        (c::eq-sint-sint
                         |tkind| (c::sint-dec-const 1)))
                       (c::add-sint-sint
                        |target_idx| (c::sint-dec-const 1))
                     |target_idx|))
                |nl|))))
           (|new_sp|
            (c::declar
             (c::condexpr
              (if (c::boolean-from-sint
                   (c::sint-from-boolean
                    (and (c::boolean-from-sint |all_ok|)
                         (c::boolean-from-sint |take|))))
                  |tsp_raw|
                |sp_after_pop|))))
           (|new_pc|
            (c::declar
             (c::condexpr
              (if (c::boolean-from-sint
                   (c::sint-from-boolean
                    (and (c::boolean-from-sint |all_ok|)
                         (c::boolean-from-sint |take|))))
                  |tpc_raw|
                (c::add-sint-sint
                 |pc| (c::sint-dec-const 2))))))
           (|sp| (c::assign |new_sp|))
           (|nl| (c::assign |new_nl|))
           (|pc| (c::assign |new_pc|))
           (|halted| (c::assign
                      (c::condexpr
                       (if (c::boolean-from-sint |all_ok|)
                           |halted|
                         (c::sint-dec-const 1)))))
           (|fuel| (c::assign
                    (c::sub-sint-sint |fuel| (c::sint-dec-const 1)))))
      ,(emit-tail loop-name))))

;; :return — opcode 0x0f.  WebAssembly `return' unwinds all labels and
;; ends the current function.  We treat it as "halt" because the outer
;; driver reads the result from `op[0]' after halting.  This matches
;; the single-export / single-return-value contract of our fixtures.
(defun emit-arm-return (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|halted| (c::assign (c::sint-dec-const 1)))
           (|fuel| (c::assign
                    (c::sub-sint-sint |fuel| (c::sint-dec-const 1)))))
      ,(emit-tail loop-name))))

;; :i32-relop — opcodes 0x46..0x4f (eq/ne/lt_u/lt_s/gt_u/gt_s/le_u/le_s/ge_u/ge_s).
;; Same stack shape as :i32-binop-total (two pops, one push) but:
;;   - the ATC operator (e.g. c::lt-uint-uint) returns sintp (C's <),
;;   - we push it as uint (i32 0/1) via uint-from-sint.
;; `op` is one of c::{eq,ne,lt,gt,le,ge}-uint-uint.  Signed variants use
;; c::{lt,gt,le,ge}-sint-sint by first converting values through
;; sint-from-uint (not needed for is_prime / collatz, which are all _u).
(defun emit-arm-i32-relop (opcode op loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|ok| (c::declar
                  (c::gt-sint-sint |sp| (c::sint-dec-const 1))))
           (|bi| (c::declar
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                     (c::sint-dec-const 0)))))
           (|ai| (c::declar
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::sub-sint-sint |sp| (c::sint-dec-const 2))
                     (c::sint-dec-const 0)))))
           (|bv| (c::declar (struct-|wst|-read-|op|-element |bi| |st|)))
           (|av| (c::declar (struct-|wst|-read-|op|-element |ai| |st|)))
           (|r_sint| (c::declar (,op |av| |bv|)))
           (|rv| (c::declar (c::uint-from-sint |r_sint|)))
           (|st| (struct-|wst|-write-|op|-element |ai| |rv| |st|))
           (|sp| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |ok|)
                       (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                     |sp|))))
           ,@(emit-pc-halted-fuel 1 '|ok| loop-name))
      ,(emit-tail loop-name))))

;; :if — opcode 0x04 BT.  Pops a condition.
;;   cond true  → enter body (pc += 2), push label targeting end_pc.
;;   cond false → if body has an else, jump past the 0x05 into the
;;                else-branch and push a label; otherwise jump past
;;                the matching end and do NOT push a label.
;; Requires the host to provide |scan_end| (for end_pc) and |scan_else|
;; (returns pc-after-0x05 at depth 1, or 0 if none).
(defun emit-arm-if (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|sp_ok| (c::declar
                     (c::gt-sint-sint |sp| (c::sint-dec-const 0))))
           (|nl_ok| (c::declar
                     (c::lt-sint-sint |nl| (c::sint-dec-const 16))))
           (|ok| (c::declar
                  (c::sint-from-boolean
                   (and (c::boolean-from-sint |sp_ok|)
                        (c::boolean-from-sint |nl_ok|)))))
           (|cond_idx| (c::declar
                        (c::condexpr
                         (if (c::boolean-from-sint |sp_ok|)
                             (c::sub-sint-sint |sp| (c::sint-dec-const 1))
                           (c::sint-dec-const 0)))))
           (|cond_v| (c::declar (struct-|wst|-read-|op|-element
                                 |cond_idx| |st|)))
           (|cond_true| (c::declar
                         (c::sint-from-boolean
                          (or (c::boolean-from-sint
                               (c::ne-uint-uint
                                |cond_v| (c::uint-dec-const 0)))
                              (c::boolean-from-sint
                               (c::ne-uint-uint
                                |cond_v| (c::uint-dec-const 0)))))))
           (|sp_after_pop| (c::declar
                            (c::condexpr
                             (if (c::boolean-from-sint |sp_ok|)
                                 (c::sub-sint-sint
                                  |sp| (c::sint-dec-const 1))
                               |sp|))))
           (|nl_safe| (c::declar
                       (c::condexpr
                        (if (c::boolean-from-sint |nl_ok|)
                            |nl|
                          (c::sint-dec-const 0)))))
           (|body_pc| (c::declar
                       (c::add-sint-sint |pc| (c::sint-dec-const 2))))
           (|end_pc_raw| (c::declar
                          (|scan_end| |body_pc| |wasm_buf|)))
           (|end_pc_ok| (c::declar
                         (c::sint-from-boolean
                          (and (c::boolean-from-sint
                                (c::ge-sint-sint
                                 |end_pc_raw| (c::sint-dec-const 0)))
                               (c::boolean-from-sint
                                (c::le-sint-sint
                                 |end_pc_raw| (c::sint-dec-const 60000)))))))
           (|end_pc| (c::declar
                      (c::condexpr
                       (if (c::boolean-from-sint |end_pc_ok|)
                           |end_pc_raw|
                         (c::sint-dec-const 0)))))
           (|else_pc_raw| (c::declar
                           (|scan_else| |body_pc| |wasm_buf|)))
           (|else_pc_ok| (c::declar
                          (c::sint-from-boolean
                           (and (c::boolean-from-sint
                                 (c::ge-sint-sint
                                  |else_pc_raw| (c::sint-dec-const 0)))
                                (c::boolean-from-sint
                                 (c::le-sint-sint
                                  |else_pc_raw| (c::sint-dec-const 60000)))))))
           (|else_pc| (c::declar
                       (c::condexpr
                        (if (c::boolean-from-sint |else_pc_ok|)
                            |else_pc_raw|
                          (c::sint-dec-const 0)))))
           (|has_else| (c::declar
                        (c::sint-from-boolean
                         (and (c::boolean-from-sint |else_pc_ok|)
                              (c::boolean-from-sint
                               (c::gt-sint-sint
                                |else_pc| (c::sint-dec-const 0)))))))
           (|st| (struct-|wst|-write-|lpc|-element |nl_safe| |end_pc| |st|))
           (|st| (struct-|wst|-write-|lsp|-element
                  |nl_safe| |sp_after_pop| |st|))
           (|st| (struct-|wst|-write-|lkind|-element
                  |nl_safe|
                  (c::uchar-from-sint (c::sint-dec-const 0))
                  |st|))
           (|all_ok| (c::declar
                      (c::sint-from-boolean
                       (and (c::boolean-from-sint |ok|)
                            (c::boolean-from-sint |end_pc_ok|)))))
           ;; push label if: (cond true) OR (cond false AND has_else).
           (|push_label| (c::declar
                          (c::sint-from-boolean
                           (and (c::boolean-from-sint |all_ok|)
                                (or (c::boolean-from-sint |cond_true|)
                                    (c::boolean-from-sint |has_else|))))))
           (|sp| (c::assign |sp_after_pop|))
           (|nl| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |push_label|)
                       (c::add-sint-sint |nl| (c::sint-dec-const 1))
                     |nl|))))
           (|pc| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |all_ok|)
                       (c::condexpr
                        (if (c::boolean-from-sint |cond_true|)
                            |body_pc|
                          (c::condexpr
                           (if (c::boolean-from-sint |has_else|)
                               |else_pc|
                             |end_pc|))))
                     |pc|))))
           (|halted| (c::assign
                      (c::condexpr
                       (if (c::boolean-from-sint |all_ok|)
                           |halted|
                         (c::sint-dec-const 1)))))
           (|fuel| (c::assign
                    (c::sub-sint-sint |fuel| (c::sint-dec-const 1)))))
      ,(emit-tail loop-name))))

;; :else — opcode 0x05.  Reached only by falling out of the then-branch
;; of an :if (the false branch jumps directly to past-else).  Action:
;; pop the if's label (we were inside it) and jump to end_pc, which
;; we recompute as scan_end(pc+1) — one byte past the 0x05.
(defun emit-arm-else (opcode loop-name)
  (declare (xargs :mode :program))
  (list
   (emit-test opcode)
   `(let* ((|nl_ok| (c::declar
                     (c::gt-sint-sint |nl| (c::sint-dec-const 0))))
           (|end_pc_raw| (c::declar
                          (|scan_end|
                           (c::add-sint-sint |pc| (c::sint-dec-const 1))
                           |wasm_buf|)))
           (|end_pc_ok| (c::declar
                         (c::sint-from-boolean
                          (and (c::boolean-from-sint
                                (c::ge-sint-sint
                                 |end_pc_raw| (c::sint-dec-const 0)))
                               (c::boolean-from-sint
                                (c::le-sint-sint
                                 |end_pc_raw| (c::sint-dec-const 60000)))))))
           (|end_pc| (c::declar
                      (c::condexpr
                       (if (c::boolean-from-sint |end_pc_ok|)
                           |end_pc_raw|
                         (c::sint-dec-const 0)))))
           (|all_ok| (c::declar
                      (c::sint-from-boolean
                       (and (c::boolean-from-sint |nl_ok|)
                            (c::boolean-from-sint |end_pc_ok|)))))
           (|nl| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |all_ok|)
                       (c::sub-sint-sint |nl| (c::sint-dec-const 1))
                     |nl|))))
           (|pc| (c::assign
                  (c::condexpr
                   (if (c::boolean-from-sint |all_ok|)
                       |end_pc|
                     |pc|))))
           (|halted| (c::assign
                      (c::condexpr
                       (if (c::boolean-from-sint |all_ok|)
                           |halted|
                         (c::sint-dec-const 1)))))
           (|fuel| (c::assign
                    (c::sub-sint-sint |fuel| (c::sint-dec-const 1)))))
      ,(emit-tail loop-name))))

(defun emit-arm (entry loop-name)
  (declare (xargs :mode :program))
  (let ((shape  (first entry))
        (opcode (second entry))
        (args   (cddr entry)))
    (case shape
      (:local-idx-pusher (emit-arm-local-idx-pusher opcode loop-name))
      (:local-idx-popper (emit-arm-local-idx-popper opcode loop-name))
      (:local-idx-teer   (emit-arm-local-idx-teer   opcode loop-name))
      (:drop             (emit-arm-drop             opcode loop-name))
      (:i32-const        (emit-arm-i32-const        opcode loop-name))
      (:i32-binop-total  (emit-arm-i32-binop-total  opcode (first args)
                                                    loop-name))
      (:i32-binop-nz     (emit-arm-i32-binop-nz     opcode (first args)
                                                    loop-name))
      (:end-toplevel     (emit-arm-end-toplevel     opcode loop-name))
      (:end              (emit-arm-end              opcode loop-name))
      (:i32-unop-eqz     (emit-arm-i32-unop-eqz     opcode loop-name))
      (:block            (emit-arm-block            opcode loop-name))
      (:loop-begin       (emit-arm-loop-begin       opcode loop-name))
      (:br               (emit-arm-br               opcode nil loop-name))
      (:br-if            (emit-arm-br               opcode t   loop-name))
      (:return           (emit-arm-return           opcode loop-name))
      (:i32-relop        (emit-arm-i32-relop        opcode (first args)
                                                    loop-name))
      (:if               (emit-arm-if               opcode loop-name))
      (:else             (emit-arm-else             opcode loop-name))
      (t (er hard? 'emit-arm "Unknown shape: ~x0" shape)))))

;; Fold arms into a nested if-else chain.
;; Default (unknown opcode) = halt and recurse so fuel drains out.
(defun emit-dispatch (entries loop-name)
  (declare (xargs :mode :program))
  (if (endp entries)
      ;; default: halt.
      `(let* ((|halted| (c::assign (c::sint-dec-const 1)))
              (|fuel| (c::assign
                       (c::sub-sint-sint |fuel| (c::sint-dec-const 1)))))
         ,(emit-tail loop-name))
    (let ((arm (emit-arm (car entries) loop-name)))
      `(if (c::boolean-from-sint ,(first arm))
           ,(second arm)
         ,(emit-dispatch (cdr entries) loop-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Predicate: does this table use any control-flow shape?
;; If yes, the loop defun needs guard enables for the lpc/lsp/lkind
;; INDEX-OKP rules (which only exist when the host's |wst| has those
;; slots — i.e. when integrating with ../wasm-vm1.lisp).

(defun entries-have-control-flow-p (entries)
  (declare (xargs :mode :program))
  (if (endp entries)
      nil
    (let ((shape (first (car entries))))
      (or (member shape '(:block :loop-begin :br :br-if :if :else))
          (entries-have-control-flow-p (cdr entries))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun emit-exec-loop (loop-name entries)
  (declare (xargs :mode :program))
  (let ((has-cf (entries-have-control-flow-p entries)))
  `(defun ,loop-name (|st| |sp| |nl| |pc| |halted| |fuel| |wasm_buf|)
     (declare (xargs
       :guard (and (c::star (struct-|wst|-p |st|))
                   (c::sintp |sp|)
                   (<= 0 (c::integer-from-sint |sp|))
                   (<= (c::integer-from-sint |sp|) 64)
                   (c::sintp |nl|)
                   (<= 0 (c::integer-from-sint |nl|))
                   (<= (c::integer-from-sint |nl|) 16)
                   (c::sintp |pc|)
                   (<= 0 (c::integer-from-sint |pc|))
                   (<= (c::integer-from-sint |pc|) 60000)
                   (c::sintp |halted|)
                   (<= 0 (c::integer-from-sint |halted|))
                   (<= (c::integer-from-sint |halted|) 1)
                   (c::sintp |fuel|)
                   (<= 0 (c::integer-from-sint |fuel|))
                   (<= (c::integer-from-sint |fuel|) 100000)
                   (object-|wasm_buf|-p |wasm_buf|))
       :guard-hints
       (("Goal"
         :in-theory
         (enable object-|wasm_buf|-p
                 c::uchar-array-index-okp
                 c::integer-from-cinteger-alt-def
                 c::sint-from-uchar-okp-when-uchar-max-<=-sint-max
                 c::uchar-max-vs-sint-max
                 c::uint-from-sint
                 c::uchar-from-sint
                 c::add-sint-sint
                 c::add-sint-sint-okp
                 c::sub-sint-sint
                 c::sub-sint-sint-okp
                 c::add-uint-uint
                 c::rem-uint-uint
                 c::rem-uint-uint-okp
                 c::div-uint-uint
                 c::div-uint-uint-okp
                 c::sub-uint-uint
                 c::mul-uint-uint
                 c::lt-uint-uint
                 c::gt-uint-uint
                 c::le-uint-uint
                 c::ge-uint-uint
                 c::sint-integerp-alt-def
                 c::integer-from-sint-of-sint-from-uchar
                 c::integer-from-uchar-upper-bound
                 c::ne-sint-sint
                 c::eq-sint-sint
                 c::gt-sint-sint
                 c::lt-sint-sint
                 c::le-sint-sint
                 c::ge-sint-sint
                 c::eq-uint-uint
                 c::ne-uint-uint
                 c::declar
                 c::assign
                 c::condexpr
                 |STRUCT-wst-op-INDEX-OKP|
                 |STRUCT-wst-loc-INDEX-OKP|
                 ,@(and has-cf
                        '(|STRUCT-wst-lpc-INDEX-OKP|
                          |STRUCT-wst-lsp-INDEX-OKP|
                          |STRUCT-wst-lkind-INDEX-OKP|
                          |scan_end|
                          |scan_else|)))))
       :measure (nfix (c::integer-from-sint |fuel|))
       :hints (("Goal"
                :in-theory
                (enable c::gt-sint-sint
                        c::sub-sint-sint
                        c::sint-integerp-alt-def
                        c::assign
                        c::condexpr)))))
     (if (mbt (and (<= 0 (c::integer-from-sint |sp|))
                   (<= (c::integer-from-sint |sp|) 64)
                   (<= 0 (c::integer-from-sint |nl|))
                   (<= (c::integer-from-sint |nl|) 16)
                   (<= 0 (c::integer-from-sint |pc|))
                   (<= (c::integer-from-sint |pc|) 60000)
                   (<= 0 (c::integer-from-sint |halted|))
                   (<= (c::integer-from-sint |halted|) 1)
                   (<= 0 (c::integer-from-sint |fuel|))
                   (<= (c::integer-from-sint |fuel|) 100000)))
         (if (c::boolean-from-sint
              (c::sint-from-boolean
               (and (c::boolean-from-sint
                     (c::eq-sint-sint |halted| (c::sint-dec-const 0)))
                    (c::boolean-from-sint
                     (c::gt-sint-sint |fuel| (c::sint-dec-const 0)))
                    (c::boolean-from-sint
                     (c::lt-sint-sint |pc| (c::sint-dec-const 59998))))))
             (let* ((|b| (c::declar (byte-at |pc|))))
               ,(emit-dispatch entries loop-name))
           (mv |st| |sp| |nl| |pc| |halted| |fuel|))
       (mv |st| |sp| |nl| |pc| |halted| |fuel|))))) ; close let, defun

(defmacro gen-exec-loop (loop-name &rest entries)
  (emit-exec-loop loop-name entries))
