; atc/codegen/standalone-state.lisp
;
; Minimal host state for the standalone loop-demo: a |wasm_buf| external
; object, a byte-at accessor macro, and the concrete SINT_MAX bound needed
; for cursor arithmetic.  The real integration uses the wasm-vm1 state
; instead (see integration-demo.lisp) and does not include this book.

(in-package "ACL2")

(include-book "state-model")

(defrule sint-max->=-65600-nonlocal
  (>= (c::sint-max) 65600)
  :rule-classes :linear
  :enable (c::sint-max c::int-bits))

(c::defobject |wasm_buf|
  :type (c::uchar 65536))

(defmacro byte-at (i)
  `(c::sint-from-uchar (c::uchar-array-read |wasm_buf| ,i)))