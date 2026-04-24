; WASM VM1 — ACL2 source for ATC to translate to C.
;
; M1 scope: enough to parse gcd.wasm and interpret it.

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system
              :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib)
                      (:open-output-channel!)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; External object: raw WASM bytes. main.c fills this before calling parse.

(c::defobject |wasm_buf|
  :type (c::uchar 65536))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Inline macro for byte access, since ATC disallows passing |wasm_buf|
;; into user-defined helper functions.

(defmacro byte-at (i)
  `(c::sint-from-uchar (c::uchar-array-read |wasm_buf| ,i)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Parsed-module struct.  Minimal fields for gcd-like one-function modules.
;;
;;   err              0 = ok, 1 = magic mismatch, 2 = malformed
;;   body_off         byte offset of fn 0 body (after local decls)
;;   body_len         byte length of fn 0 body (bytes from body_off to end+1)
;;   num_params       declared param count for fn 0
;;   num_results      declared result count for fn 0
;;   num_locals       total declared locals (after params) for fn 0
;;   export_off       byte offset of export 0's name bytes in wasm_buf
;;   export_len       byte length of export 0's name

(c::defstruct |wmod|
  (|err|         c::uchar)
  (|body_off|    c::uint)
  (|body_len|    c::uint)
  (|num_params|  c::uchar)
  (|num_results| c::uchar)
  (|num_locals|  c::uchar)
  (|export_off|  c::uint)
  (|export_len|  c::uchar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Check magic: buf[0..3] == 00 61 73 6d.  Returns sint (1 or 0).

(defun |check_magic| (|wasm_buf|)
  (declare (xargs :guard (object-|wasm_buf|-p |wasm_buf|)
                  :guard-hints
                  (("Goal"
                    :in-theory
                    (enable object-|wasm_buf|-p
                            c::uchar-array-index-okp
                            c::integer-from-cinteger-alt-def
                            c::sint-from-uchar-okp-when-uchar-max-<=-sint-max
                            c::uchar-max-vs-sint-max)))))
  (c::sint-from-boolean
   (and (c::boolean-from-sint
         (c::eq-sint-sint (byte-at (c::sint-dec-const 0))
                          (c::sint-dec-const #x00)))
        (c::boolean-from-sint
         (c::eq-sint-sint (byte-at (c::sint-dec-const 1))
                          (c::sint-dec-const #x61)))
        (c::boolean-from-sint
         (c::eq-sint-sint (byte-at (c::sint-dec-const 2))
                          (c::sint-dec-const #x73)))
        (c::boolean-from-sint
         (c::eq-sint-sint (byte-at (c::sint-dec-const 3))
                          (c::sint-dec-const #x6d))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Integration test: a function that both reads |wasm_buf| and writes a struct
;; field via a pointer param.  Mirrors the shape of the eventual parse_module:
;;
;;    void parse_header(struct wmod *m) {
;;        m->err = !check_magic();
;;    }

(defun |parse_header| (|m| |wasm_buf|)
  (declare (xargs :guard (and (c::star (struct-|wmod|-p |m|))
                              (object-|wasm_buf|-p |wasm_buf|))
                  :guard-hints
                  (("Goal"
                    :in-theory
                    (enable object-|wasm_buf|-p
                            c::uchar-array-index-okp
                            c::integer-from-cinteger-alt-def
                            c::sint-from-uchar-okp-when-uchar-max-<=-sint-max
                            c::uchar-max-vs-sint-max
                            c::declar
                            c::assign)))))
  (let* ((|ok| (c::declar (|check_magic| |wasm_buf|))))
    (if (c::boolean-from-sint |ok|)
        (let ((|m| (struct-|wmod|-write-|err|
                    (c::uchar-from-sint (c::sint-dec-const 0))
                    |m|)))
          |m|)
      (let ((|m| (struct-|wmod|-write-|err|
                  (c::uchar-from-sint (c::sint-dec-const 1))
                  |m|)))
        |m|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c::atc |wasm_buf|
        |wmod|
        |check_magic|
        |parse_header|
        :file-name "wasm-vm1"
        :header t
        :proofs nil)
