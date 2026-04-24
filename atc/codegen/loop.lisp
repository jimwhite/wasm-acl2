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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Dispatcher on one entry.

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
;; Top-level loop generator.

(defun emit-exec-loop (loop-name entries)
  (declare (xargs :mode :program))
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
                 |STRUCT-wst-loc-INDEX-OKP|)))
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
       (mv |st| |sp| |nl| |pc| |halted| |fuel|))))

(defmacro gen-exec-loop (loop-name &rest entries)
  (emit-exec-loop loop-name entries))
