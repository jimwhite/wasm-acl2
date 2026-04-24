; atc/codegen/state-model.lisp
;
; Fixed concrete state used by every generated WASM step function.
;
; This is the *one* place where the ATC concrete representation of a
; WASM runtime state is defined.  All generated `|exec-<op>|` functions
; operate over this struct plus an `sp` scalar threading the operand
; stack height.  The AST-level spec state (`wasm::statep`) maps to
; `(st, sp)` under the correspondence:
;
;   (current-operand-stack state)     <->  op[0..sp-1]   (sp = height)
;   (current-locals state)            <->  loc[0..]
;
; with the spec's wrapped value constructors (e.g. `(make-i32-val v)`)
; carrying the concrete `uint` v that lives in op[i] / loc[i].

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system
              :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib)
                      (:open-output-channel!)))

(local (include-book "arithmetic-5/top" :dir :system))

;; Concrete bounds for the ATC int type.  Same idiom as atc/wasm-vm1.lisp.

(defrulel sint-max->=-65600
  (>= (c::sint-max) 65600)
  :rule-classes :linear
  :enable (c::sint-max c::int-bits))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The concrete state struct.
;;
;; M1 scope: operand stack of 64 uints and 16 i32-sized locals, matching
;; the shape used by atc/wasm-vm1.lisp.  Control-flow fields (label stack,
;; pc, halted) are *not* in the struct — they belong to the dispatcher,
;; not to any single op.

(c::defstruct |wst|
  (|op|  (c::uint 64))
  (|loc| (c::uint 16)))
