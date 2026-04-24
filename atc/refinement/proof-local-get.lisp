; atc/refinement/proof-local-get.lisp
;
; First opcode-level refinement proof: the local.get arm of the ATC
; interpreter |exec$loop| agrees with the WASM operational-semantics
; function wasm::execute-local.get on the value it pushes onto the
; operand stack.
;
; Scope of this spike:
;   - One opcode (0x20 local.get).
;   - Exactly one step (fuel = 1 on the ATC side, one execute-local.get
;     call on the spec side).
;   - No operand-stack / locals abstraction function yet; we instead
;     pick a concrete spec state whose locals list matches the ATC loc[]
;     array on one coordinate, and show the two sides push the same i32
;     value.
;
; Purpose: shake out the cross-package plumbing and establish a pattern
; that scales to the other 9 M1 opcodes.  See
; /workspaces/wasm-acl2/WASM_ATC_PLAN.md §M6 and
; /workspaces/wasm-acl2/proofs/GCD_PROOF_NOTES.md for the proof style
; this follows.

(in-package "ACL2")

(include-book "../wasm-vm1")

; The spec is a WASM-package book.  include-book is fine across packages;
; its events land in the current ACL2 world with their original packages.
(include-book "../../execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Spec side: what does execute-local.get do on top of the stack?
;;
;; For any state whose current frame has locals L (at least x+1 long) and
;; an empty operand stack, after (execute-local.get (list x) state) the
;; top of the operand stack is (nth-local x L).

(defthm spec-local-get-top
  (implies
   (and (natp x)
        (wasm::localsp locals)
        (< x (len locals))
        (let ((frame (wasm::make-frame
                      :return-arity 1
                      :locals locals
                      :operand-stack (wasm::empty-operand-stack)
                      :instrs (cons (list :local.get x) rest-instrs)
                      :label-stack nil)))
          (and (wasm::framep frame)
               (equal state
                      (wasm::make-state
                       :store nil
                       :call-stack (list frame)
                       :memory nil
                       :globals nil
                       :table nil))
               (wasm::statep state))))
   (equal (wasm::top-operand
           (wasm::current-operand-stack
            (wasm::execute-local.get (list x) state)))
          (wasm::nth-local x locals)))
  :hints (("Goal" :in-theory (enable wasm::execute-local.get
                                     wasm::current-locals
                                     wasm::current-operand-stack
                                     wasm::update-current-operand-stack
                                     wasm::update-current-instrs
                                     wasm::current-instrs
                                     wasm::push-operand
                                     wasm::top-operand
                                     wasm::operand-stack-height
                                     wasm::empty-operand-stack
                                     wasm::nth-local
                                     wasm::push-call-stack
                                     wasm::pop-call-stack
                                     wasm::top-frame
                                     wasm::call-stackp
                                     wasm::framep
                                     wasm::localsp
                                     wasm::val-listp
                                     wasm::operand-stackp
                                     wasm::label-stackp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ATC side: the local.get arm of |exec$loop| with fuel = 1 writes loc[x]
;; to op[sp] and stops (fuel = 0 terminates the recursion on the next
;; entry).
;;
;; We state this as a fact about the mv-nth 0 (final struct) and about
;; the operand-stack element ATC just wrote.

;; Predicate: (st, sp, pc, wasm_buf, x) is well-formed for one local.get step.
(defund wf-local-get (st sp pc |wasm_buf| x)
  (declare (xargs :guard t :verify-guards nil))
  (and (struct-|wst|-p st)
       (c::sintp sp)
       (<= 0 (c::integer-from-sint sp))
       (< (c::integer-from-sint sp) 64)
       (c::sintp pc)
       (<= 0 (c::integer-from-sint pc))
       (<= (c::integer-from-sint pc) 59997)
       (object-|wasm_buf|-p |wasm_buf|)
       (c::sintp x)
       (<= 0 (c::integer-from-sint x))
       (< (c::integer-from-sint x) 16)
       ;; byte at pc is 0x20 (local.get), byte at pc+1 is x.
       (equal (c::integer-from-uchar
               (c::uchar-array-read |wasm_buf| pc))
              #x20)
       (equal (c::integer-from-uchar
               (c::uchar-array-read |wasm_buf|
                                    (c::add-sint-sint
                                     pc (c::sint-dec-const 1))))
              (c::integer-from-sint x))))

;; After one step at a local.get, op[sp] holds the value that was at loc[x]
;; in the original state.
;;
;; We express this as a structural equality between the resulting wst and
;; the one obtained by writing loc[x] to op[sp].  This avoids needing a
;; read-of-write-same-index lemma for the defstruct-generated element
;; accessors at this stage; the projection is handled by the connection
;; lemma further below, which introduces its own read-of-write lemma.

(defthm atc-local-get-unfolds
  (implies (wf-local-get |st| |sp| |pc| |wasm_buf| |x|)
           (equal (mv-nth 0 (|exec$loop|
                             |st| |sp|
                             (c::sint-dec-const 0)      ;; nl = 0
                             |pc|
                             (c::sint-dec-const 0)      ;; halted = 0
                             (c::sint-dec-const 1)      ;; fuel = 1
                             |wasm_buf|))
                  (struct-|wst|-write-|op|-element
                   |sp|
                   (struct-|wst|-read-|loc|-element
                    (c::sint-from-uchar
                     (c::uchar-array-read
                      |wasm_buf|
                      (c::add-sint-sint |pc| (c::sint-dec-const 1))))
                    |st|)
                   |st|)))
  :hints
  (("Goal"
    :expand ((:free (|st| |sp| |nl| |pc| |halted| |fuel| |wasm_buf|)
                    (|exec$loop| |st| |sp| |nl| |pc| |halted| |fuel|
                                 |wasm_buf|)))
    :in-theory
    (enable wf-local-get
            object-|wasm_buf|-p
            c::uchar-array-index-okp
            c::integer-from-cinteger-alt-def
            c::sint-from-uchar-okp-when-uchar-max-<=-sint-max
            c::uchar-max-vs-sint-max
            c::uchar-from-sint
            c::add-sint-sint
            c::sub-sint-sint
            c::sint-integerp-alt-def
            c::integer-from-sint-of-sint-from-uchar
            c::integer-from-uchar-upper-bound
            c::ne-sint-sint
            c::eq-sint-sint
            c::gt-sint-sint
            c::lt-sint-sint
            c::le-sint-sint
            c::ge-sint-sint
            c::declar
            c::assign
            c::condexpr
            c::sint-from-boolean
            c::boolean-from-sint
            |STRUCT-wst-op-INDEX-OKP|
            |STRUCT-wst-loc-INDEX-OKP|)
    :do-not '(generalize fertilize eliminate-destructors))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Status and next step.
;;
;; Certifying in this book today:
;;   spec-local-get-top     — execute-local.get (list x) pushes (nth-local x
;;                            locals) onto the stack.
;;   atc-local-get-unfolds  — one step of |exec$loop| at pc-byte 0x20 is
;;                            equal to writing the loc element (indexed by
;;                            the x byte) into op[sp].
;;
;; Missing for an end-to-end refinement theorem — "after one local.get
;; step, the i32 on top of the abstracted ATC operand stack equals the
;; i32 on top of the spec operand stack":
;;
;;   A. A read-of-write-same-index lemma for defstruct-generated
;;      element accessors:
;;        (struct-|wst|-read-|op|-element i
;;           (struct-|wst|-write-|op|-element i v s))
;;          = v
;;      under (struct-|wst|-p s), (c::uintp v), and i in [0, 64).
;;      The corresponding lemma for uchar arrays is proved in Kestrel's
;;      books/kestrel/c/examples/strcpy-safe-support.lisp, via
;;      uchar-array-read-of-sint-to-nth / -write-of-sint-to-update-nth
;;      plus the standard nth/update-nth rule.  We need a parallel
;;      development for uint arrays and for the composition through
;;      value-struct-read/write-aux at same-tag.
;;
;;   B. A small bridge lemma:
;;        (c::sint-from-uchar (c::uchar-array-read wasm_buf (pc+1))) = x
;;      from the wf-local-get hypothesis.
;;
;; Both belong in a shared atc/refinement/atc-wasm-support.lisp book;
;; they will be reused verbatim for local.set, local.tee, i32.eqz, and
;; every other opcode arm.  Keeping this book tight to what certifies
;; today documents exactly which pieces of the support layer are still
;; to be written.
