; ATC smoke test: simplest possible ATC invocation.
; Goal: confirm ATC pipeline is healthy in this environment
; (ttags, output dir, .c/.h emission) before writing the real
; parser + interpreter.

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system
              :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib)
                      (:open-output-channel!)))

; Trivial integer function: add two uints.
(defun |add2| (|x| |y|)
  (declare (xargs :guard (and (c::uintp |x|) (c::uintp |y|))))
  (c::add-uint-uint |x| |y|))

; Struct with scalars AND an integer array member (the shape we need
; for wasm-module). ATC supports only integer and integer-array members.
(c::defstruct |scalar_and_array|
  (|scalar| c::sint)
  (|aggreg| (c::uchar 10)))

; Read a scalar field from a pointed struct.
(defun |get_num| (|m|)
  (declare (xargs :guard (c::star (struct-|scalar_and_array|-p |m|))))
  (struct-|scalar_and_array|-read-|scalar| |m|))

; Read a byte at index from the array member (struct passed by pointer).
(defun |get_byte| (|i| |m|)
  (declare (xargs :guard (and (c::sintp |i|)
                              (c::star (struct-|scalar_and_array|-p |m|))
                              (c::star (struct-|scalar_and_array|-|aggreg|-index-okp |i|)))))
  (struct-|scalar_and_array|-read-|aggreg|-element |i| |m|))

(c::atc |add2| |get_num| |get_byte|
        :file-name "smoke" :header t)
