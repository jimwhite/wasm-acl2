; ATC smoke test: struct with scalar + integer-array member passed by pointer.
; This matches the shape of wasm-module we'll need for M1.

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system
              :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib)
                      (:open-output-channel!)))

(c::defstruct |modu|
  (|num| c::sint)
  (|bytes| (c::uchar 16)))

; Read scalar by pointer.
(defun |get_num| (|m|)
  (declare (xargs :guard (c::star (struct-|modu|-p |m|))))
  (struct-|modu|-read-|num| |m|))

; Read indexed byte by pointer.
(defun |get_byte| (|i| |m|)
  (declare (xargs :guard (and (c::sintp |i|)
                              (c::star (struct-|modu|-p |m|))
                              (c::star (struct-|modu|-|bytes|-index-okp |i|)))))
  (struct-|modu|-read-|bytes|-element |i| |m|))

; Write scalar by pointer (in-place mutation at C level).
(defun |set_num| (|v| |m|)
  (declare (xargs :guard (and (c::sintp |v|)
                              (c::star (struct-|modu|-p |m|)))))
  (let ((|m| (struct-|modu|-write-|num| |v| |m|)))
    |m|))

(c::atc |modu|
        |get_num| |get_byte| |set_num|
        :file-name "smoke4" :header t)
