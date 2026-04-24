; WASM VM1 — ACL2 source for ATC to translate to C.
;
; M1 scope: interpret small WebAssembly i32 modules (one exported function,
; i32 params/result, one local group, single-byte LEB128s for sizes).
;
; Design:
;   - `|wasm_buf|`: 64 KiB uchar external object; main.c fread's the .wasm here.
;   - `|wmod|`:    parsed-module struct populated by `|parse_module|`.
;   - `|parse_module|`: walks sections 0..N via `|parse$loop|`, filling |wmod|.
;   - `|invoke|`:  interprets bytecode via `|exec$loop|`, with operand stack,
;                  locals, and a small label stack for block/loop/br{,_if}.

(in-package "ACL2")

(include-book "kestrel/c/atc/atc" :dir :system
              :ttags ((:quicklisp) (:quicklisp.osicat) (:oslib)
                      (:open-output-channel!)))

(local (include-book "arithmetic-5/top" :dir :system))

;; The C standard only guarantees SINT_MAX >= 32767.  Our cursor arithmetic
;; needs SINT_MAX >= ~65536 (so that cursor + small constant stays representable).
;; ATC's model fixes int-bits=32 and char-bits=8 (see integer-formats.lisp),
;; so we expose those concrete linear bounds here and use them in guard hints.

(defrulel sint-max->=-65600
  (>= (c::sint-max) 65600)
  :rule-classes :linear
  :enable (c::sint-max c::int-bits))

(defrulel uchar-max-=-255
  (equal (c::uchar-max) 255)
  :enable (c::uchar-max c::char-bits))

(defrulel integer-from-uchar->=-0
  (<= 0 (c::integer-from-uchar x))
  :rule-classes :linear
  :enable c::integer-from-uchar)

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
;; Parsed-module struct.

(c::defstruct |wmod|
  (|err|         c::uchar)
  (|body_off|    c::sint)
  (|body_len|    c::sint)
  (|num_params|  c::uchar)
  (|num_results| c::uchar)
  (|num_locals|  c::uchar)
  (|export_off|  c::sint)
  (|export_len|  c::uchar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Magic check: buf[0..3] == 00 61 73 6d.  Returns sint (1 or 0).

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
;; Section walker.  Iterates sections in the binary, each shaped:
;;
;;     <id:u8> <size:LEB> <payload:size bytes>
;;
;; Only single-byte LEBs are supported for sizes (size < 128).
;;
;; The loop terminates when fuel runs out, when cursor would exceed
;; a safe upper bound, or when an error is noted in |m|.
;;
;; Per-section handling (inlined in the body):
;;
;;   id=7 (exports):  take the FIRST export's name as (export_off, export_len)
;;                    (assumes the payload starts with count=1 byte, then
;;                    name_len byte, then name_len name bytes, then kind+idx).
;;
;;   id=10 (code):    take fn 0's (body_off, body_len, num_locals), assuming
;;                    payload = count(=1)|body_size|num_local_groups|...|body.
;;                    Supported shapes: num_local_groups ∈ {0, 1}.
;;
;;   any other id:    just skip the payload.
;;
;; Unsupported shapes set m.err = 2.

(defun |parse$loop| (|cursor| |fuel| |m| |wasm_buf|)
  (declare (xargs
    :guard (and (c::sintp |cursor|)
                (c::sintp |fuel|)
                (c::star (struct-|wmod|-p |m|))
                (object-|wasm_buf|-p |wasm_buf|)
                (<= 0 (c::integer-from-sint |cursor|))
                (<= (c::integer-from-sint |cursor|) 60000)
                (<= 0 (c::integer-from-sint |fuel|))
                (<= (c::integer-from-sint |fuel|) 16))
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
              c::condexpr)))
    :measure (nfix (c::integer-from-sint |fuel|))
    :hints (("Goal"
             :in-theory
             (enable c::ne-sint-sint
                     c::gt-sint-sint
                     c::sub-sint-sint
                     c::sint-integerp-alt-def
                     c::assign
                     c::condexpr)))))
  (if (mbt (and (<= 0 (c::integer-from-sint |cursor|))
                (<= (c::integer-from-sint |cursor|) 60000)
                (<= 0 (c::integer-from-sint |fuel|))
                (<= (c::integer-from-sint |fuel|) 16)))
      (if (c::boolean-from-sint
           (c::gt-sint-sint |fuel| (c::sint-dec-const 0)))
          (let* ((|id|   (c::declar (byte-at |cursor|)))
                 (|size| (c::declar
                          (byte-at (c::add-sint-sint
                                    |cursor| (c::sint-dec-const 1)))))
                 (|next| (c::declar
                          (c::add-sint-sint
                           |cursor|
                           (c::add-sint-sint
                            |size| (c::sint-dec-const 2)))))
                 ;; |safe| = 1 if next stays within the guard bound.
                 ;; Every path still recurses; on unsafe we clamp cursor and
                 ;; zero fuel so the next iteration exits via the fuel test.
                 (|safe|
                  (c::declar
                   (c::le-sint-sint |next| (c::sint-dec-const 60000))))
                 ;; id == 7 (export): record first export's name.
                 (|m|
                  (if (c::boolean-from-sint
                       (c::sint-from-boolean
                        (and (c::boolean-from-sint |safe|)
                             (c::boolean-from-sint
                              (c::eq-sint-sint |id|
                                               (c::sint-dec-const 7))))))
                      (let* ((|name_len|
                              (c::declar
                               (byte-at (c::add-sint-sint
                                         |cursor| (c::sint-dec-const 3)))))
                             (|name_off|
                              (c::declar
                               (c::add-sint-sint
                                |cursor| (c::sint-dec-const 4))))
                             (|m|
                              (struct-|wmod|-write-|export_off|
                               |name_off| |m|))
                             (|m|
                              (struct-|wmod|-write-|export_len|
                               (c::uchar-from-sint |name_len|) |m|)))
                        |m|)
                    |m|))
                 ;; id == 10 (code): record fn 0 body_off/body_len/num_locals.
                 (|m|
                  (if (c::boolean-from-sint
                       (c::sint-from-boolean
                        (and (c::boolean-from-sint |safe|)
                             (c::boolean-from-sint
                              (c::eq-sint-sint |id|
                                               (c::sint-dec-const 10))))))
                      (let* ((|body_size|
                              (c::declar
                               (byte-at (c::add-sint-sint
                                         |cursor| (c::sint-dec-const 3)))))
                             (|ng|
                              (c::declar
                               (byte-at (c::add-sint-sint
                                         |cursor| (c::sint-dec-const 4))))))
                        (if (c::boolean-from-sint
                             (c::eq-sint-sint |ng| (c::sint-dec-const 0)))
                            ;; no locals
                            (let* ((|body_off|
                                    (c::declar
                                     (c::add-sint-sint
                                      |cursor| (c::sint-dec-const 5))))
                                   (|body_len|
                                    (c::declar
                                     (c::sub-sint-sint
                                      |body_size| (c::sint-dec-const 1))))
                                   (|m|
                                    (struct-|wmod|-write-|body_off|
                                     |body_off| |m|))
                                   (|m|
                                    (struct-|wmod|-write-|body_len|
                                     |body_len| |m|))
                                   (|m|
                                    (struct-|wmod|-write-|num_locals|
                                     (c::uchar-from-sint
                                      (c::sint-dec-const 0))
                                     |m|)))
                              |m|)
                          (if (c::boolean-from-sint
                               (c::eq-sint-sint |ng|
                                                (c::sint-dec-const 1)))
                              ;; one group
                              (let* ((|nloc|
                                      (c::declar
                                       (byte-at (c::add-sint-sint
                                                 |cursor|
                                                 (c::sint-dec-const 5)))))
                                     (|body_off|
                                      (c::declar
                                       (c::add-sint-sint
                                        |cursor| (c::sint-dec-const 7))))
                                     (|body_len|
                                      (c::declar
                                       (c::sub-sint-sint
                                        |body_size| (c::sint-dec-const 3))))
                                     (|m|
                                      (struct-|wmod|-write-|body_off|
                                       |body_off| |m|))
                                     (|m|
                                      (struct-|wmod|-write-|body_len|
                                       |body_len| |m|))
                                     (|m|
                                      (struct-|wmod|-write-|num_locals|
                                       (c::uchar-from-sint |nloc|) |m|)))
                                |m|)
                            ;; unsupported number of local groups
                            (let ((|m|
                                   (struct-|wmod|-write-|err|
                                    (c::uchar-from-sint
                                     (c::sint-dec-const 2))
                                    |m|)))
                              |m|))))
                    |m|))
                 (|cursor|
                  (c::assign
                   (c::condexpr
                    (if (c::boolean-from-sint |safe|) |next| |cursor|))))
                 (|fuel|
                  (c::assign
                   (c::condexpr
                    (if (c::boolean-from-sint |safe|)
                        (c::sub-sint-sint |fuel| (c::sint-dec-const 1))
                      (c::sint-dec-const 0))))))
            (|parse$loop| |cursor| |fuel| |m| |wasm_buf|))
        (mv |cursor| |fuel| |m|))
    (mv nil nil nil)))

(defun |parse_module| (|m| |wasm_buf|)
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
                            c::assign
                            c::sint-integerp-alt-def)))))
  (let* ((|ok| (c::declar (|check_magic| |wasm_buf|))))
    (if (c::boolean-from-sint |ok|)
        (let* ((|cursor| (c::declar (c::sint-dec-const 8)))
               (|fuel|   (c::declar (c::sint-dec-const 16))))
          (mv-let (|cursor| |fuel| |m|)
              (|parse$loop| |cursor| |fuel| |m| |wasm_buf|)
            (declare (ignore |cursor| |fuel|))
            |m|))
      (let ((|m|
             (struct-|wmod|-write-|err|
              (c::uchar-from-sint (c::sint-dec-const 1)) |m|)))
        |m|))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpreter state.
;;
;;   op     operand stack (64 u32 slots)
;;   loc    locals        (16 u32 slots)
;;   lpc    label target PCs (16 slots) — for block: pc just after matching end;
;;                                        for loop:  pc of first body instr
;;   lsp    label target SPs (16 slots) — sp to restore on br
;;   lkind  label kinds (16 slots)      — 0 = block, 1 = loop
;;
;; Scalar pieces of state (sp, nl, pc, halted) are passed as separate args
;; to exec$loop so their ranges can be tracked in guards without struct
;; invariants.

(c::defstruct |wst|
  (|op|     (c::uint 64))
  (|loc|    (c::uint 16))
  (|lpc|    (c::sint 16))
  (|lsp|    (c::sint 16))
  (|lkind|  (c::uchar 16)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Forward scan for matching `end`.
;;
;; Walk forward from |pc| tracking opcode lengths and block depth.
;; When depth drops to 0, the scan stops; the returned pc points to the
;; position right after the matching `end` byte.
;;
;; Opcode size table (bytes consumed including the opcode itself):
;;   0x02 block BT, 0x03 loop BT, 0x04 if BT                              : 2
;;   0x0c br L, 0x0d br_if L                                              : 2
;;   0x20 local.get X, 0x21 local.set X, 0x22 local.tee X                 : 2
;;   everything else (including 0x0b end, 0x45, 0x70, etc.)               : 1

(defun |scan$loop| (|pc| |depth| |fuel| |wasm_buf|)
  (declare (xargs
    :guard (and (c::sintp |pc|)
                (c::sintp |depth|)
                (c::sintp |fuel|)
                (object-|wasm_buf|-p |wasm_buf|)
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (<= 0 (c::integer-from-sint |depth|))
                (<= (c::integer-from-sint |depth|) 4096)
                (<= 0 (c::integer-from-sint |fuel|))
                (<= (c::integer-from-sint |fuel|) 4096))
    :guard-hints
    (("Goal"
      :in-theory
      (enable object-|wasm_buf|-p
              c::uchar-array-index-okp
              c::integer-from-cinteger-alt-def
              c::sint-from-uchar-okp-when-uchar-max-<=-sint-max
              c::uchar-max-vs-sint-max
              c::add-sint-sint
              c::add-sint-sint-okp
              c::sub-sint-sint
              c::sub-sint-sint-okp
              c::sint-integerp-alt-def
              c::integer-from-sint-of-sint-from-uchar
              c::integer-from-uchar-upper-bound
              c::eq-sint-sint
              c::gt-sint-sint
              c::lt-sint-sint
              c::le-sint-sint
              c::declar
              c::assign
              c::condexpr)))
    :measure (nfix (c::integer-from-sint |fuel|))
    :hints (("Goal"
             :in-theory
             (enable c::gt-sint-sint
                     c::sub-sint-sint
                     c::sint-integerp-alt-def
                     c::assign
                     c::condexpr)))))
  (if (mbt (and (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (<= 0 (c::integer-from-sint |depth|))
                (<= (c::integer-from-sint |depth|) 4096)
                (<= 0 (c::integer-from-sint |fuel|))
                (<= (c::integer-from-sint |fuel|) 4096)))
      (if (c::boolean-from-sint
           (c::sint-from-boolean
            (and (c::boolean-from-sint
                  (c::gt-sint-sint |depth| (c::sint-dec-const 0)))
                 (c::boolean-from-sint
                  (c::gt-sint-sint |fuel| (c::sint-dec-const 0)))
                 (c::boolean-from-sint
                  (c::lt-sint-sint |pc| (c::sint-dec-const 59998)))
                 (c::boolean-from-sint
                  (c::lt-sint-sint |depth| (c::sint-dec-const 4095))))))
          (let* ((|b| (c::declar (byte-at |pc|)))
                 (|is_open|
                  (c::declar
                   (c::sint-from-boolean
                    (or (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x02)))
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x03)))
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x04)))))))
                 (|is_end|
                  (c::declar
                   (c::eq-sint-sint |b| (c::sint-dec-const #x0b))))
                 (|is_wide|
                  (c::declar
                   (c::sint-from-boolean
                    (or (c::boolean-from-sint |is_open|)
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x0c)))
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x0d)))
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x20)))
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x21)))
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x22)))))))
                 (|depth|
                  (c::assign
                   (c::condexpr
                    (if (c::boolean-from-sint |is_open|)
                        (c::add-sint-sint |depth| (c::sint-dec-const 1))
                      (c::condexpr
                       (if (c::boolean-from-sint |is_end|)
                           (c::sub-sint-sint |depth| (c::sint-dec-const 1))
                         |depth|))))))
                 (|pc|
                  (c::assign
                   (c::condexpr
                    (if (c::boolean-from-sint |is_wide|)
                        (c::add-sint-sint |pc| (c::sint-dec-const 2))
                      (c::add-sint-sint |pc| (c::sint-dec-const 1))))))
                 (|fuel|
                  (c::assign
                   (c::sub-sint-sint |fuel| (c::sint-dec-const 1)))))
            (|scan$loop| |pc| |depth| |fuel| |wasm_buf|))
        (mv |pc| |depth| |fuel|))
    (mv nil nil nil)))

(defrulel sintp-of-mv-nth-0-scan$loop
  (implies (and (c::sintp |pc|)
                (c::sintp |depth|)
                (c::sintp |fuel|)
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (<= 0 (c::integer-from-sint |depth|))
                (<= (c::integer-from-sint |depth|) 4096)
                (<= 0 (c::integer-from-sint |fuel|))
                (<= (c::integer-from-sint |fuel|) 4096))
           (c::sintp (mv-nth 0 (|scan$loop| |pc| |depth| |fuel| |wasm_buf|))))
  :induct (|scan$loop| |pc| |depth| |fuel| |wasm_buf|)
  :enable (|scan$loop|
           c::add-sint-sint
           c::sub-sint-sint
           c::gt-sint-sint
           c::lt-sint-sint
           c::eq-sint-sint
           c::boolean-from-sint
           c::sint-from-boolean
           c::sint-integerp-alt-def
           c::declar
           c::assign
           c::condexpr))

(defun |scan_end| (|pc| |wasm_buf|)
  (declare (xargs
    :guard (and (c::sintp |pc|)
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (object-|wasm_buf|-p |wasm_buf|))
    :guard-hints
    (("Goal" :in-theory (enable object-|wasm_buf|-p
                                c::declar c::sint-integerp-alt-def)))))
  (let* ((|depth| (c::declar (c::sint-dec-const 1)))
         (|fuel|  (c::declar (c::sint-dec-const 4096))))
    (mv-let (|pc| |depth| |fuel|)
        (|scan$loop| |pc| |depth| |fuel| |wasm_buf|)
      (declare (ignore |depth| |fuel|))
      |pc|)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Real interpreter.
;;
;; Scalars (sp, nl, pc, halted, fuel) are threaded as separate args;
;; struct stores only the arrays.  Every opcode branch ends in a
;; recursive call, satisfying ATC's loop-body rule.
;;
;; Halt conditions: end at top-level; stack overflow/underflow;
;; label stack overflow; divide-by-zero; invalid local index;
;; invalid br target; unknown opcode.

(defun |exec$loop| (|st| |sp| |nl| |pc| |halted| |fuel| |wasm_buf|)
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
              |STRUCT-wst-loc-INDEX-OKP|
              |STRUCT-wst-lpc-INDEX-OKP|
              |STRUCT-wst-lsp-INDEX-OKP|
              |STRUCT-wst-lkind-INDEX-OKP|)))
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
            ;; ===== 0x20 local.get =====
            (if (c::boolean-from-sint
                 (c::eq-sint-sint |b| (c::sint-dec-const #x20)))
                (let* ((|x| (c::declar
                             (byte-at (c::add-sint-sint
                                       |pc| (c::sint-dec-const 1)))))
                       (|ok| (c::declar
                              (c::sint-from-boolean
                               (and (c::boolean-from-sint
                                     (c::lt-sint-sint
                                      |sp| (c::sint-dec-const 64)))
                                    (c::boolean-from-sint
                                     (c::lt-sint-sint
                                      |x| (c::sint-dec-const 16)))))))
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
                       (|v| (c::declar
                             (struct-|wst|-read-|loc|-element |x_safe| |st|)))
                       (|st| (struct-|wst|-write-|op|-element
                              |sp_safe| |v| |st|))
                       (|sp| (c::assign
                              (c::condexpr
                               (if (c::boolean-from-sint |ok|)
                                   (c::add-sint-sint
                                    |sp| (c::sint-dec-const 1))
                                 |sp|))))
                       (|pc| (c::assign
                              (c::add-sint-sint |pc| (c::sint-dec-const 2))))
                       (|halted| (c::assign
                                  (c::condexpr
                                   (if (c::boolean-from-sint |ok|)
                                       |halted|
                                     (c::sint-dec-const 1)))))
                       (|fuel| (c::assign
                                (c::sub-sint-sint
                                 |fuel| (c::sint-dec-const 1)))))
                  (|exec$loop| |st| |sp| |nl| |pc| |halted| |fuel|
                               |wasm_buf|))
              ;; ===== 0x21 local.set =====
              (if (c::boolean-from-sint
                   (c::eq-sint-sint |b| (c::sint-dec-const #x21)))
                  (let* ((|x| (c::declar
                               (byte-at (c::add-sint-sint
                                         |pc| (c::sint-dec-const 1)))))
                         (|ok| (c::declar
                                (c::sint-from-boolean
                                 (and (c::boolean-from-sint
                                       (c::gt-sint-sint
                                        |sp| (c::sint-dec-const 0)))
                                      (c::boolean-from-sint
                                       (c::lt-sint-sint
                                        |x| (c::sint-dec-const 16)))))))
                         (|x_safe| (c::declar
                                    (c::condexpr
                                     (if (c::boolean-from-sint |ok|)
                                         |x|
                                       (c::sint-dec-const 0)))))
                         (|idx| (c::declar
                                 (c::condexpr
                                  (if (c::boolean-from-sint |ok|)
                                      (c::sub-sint-sint
                                       |sp| (c::sint-dec-const 1))
                                    (c::sint-dec-const 0)))))
                         (|v| (c::declar
                               (struct-|wst|-read-|op|-element |idx| |st|)))
                         (|st| (struct-|wst|-write-|loc|-element
                                |x_safe| |v| |st|))
                         (|sp| (c::assign
                                (c::condexpr
                                 (if (c::boolean-from-sint |ok|)
                                     (c::sub-sint-sint
                                      |sp| (c::sint-dec-const 1))
                                   |sp|))))
                         (|pc| (c::assign
                                (c::add-sint-sint
                                 |pc| (c::sint-dec-const 2))))
                         (|halted| (c::assign
                                    (c::condexpr
                                     (if (c::boolean-from-sint |ok|)
                                         |halted|
                                       (c::sint-dec-const 1)))))
                         (|fuel| (c::assign
                                  (c::sub-sint-sint
                                   |fuel| (c::sint-dec-const 1)))))
                    (|exec$loop| |st| |sp| |nl| |pc| |halted| |fuel|
                                 |wasm_buf|))
                ;; ===== 0x22 local.tee =====
                (if (c::boolean-from-sint
                     (c::eq-sint-sint |b| (c::sint-dec-const #x22)))
                    (let* ((|x| (c::declar
                                 (byte-at (c::add-sint-sint
                                           |pc| (c::sint-dec-const 1)))))
                           (|ok| (c::declar
                                  (c::sint-from-boolean
                                   (and (c::boolean-from-sint
                                         (c::gt-sint-sint
                                          |sp| (c::sint-dec-const 0)))
                                        (c::boolean-from-sint
                                         (c::lt-sint-sint
                                          |x| (c::sint-dec-const 16)))))))
                           (|x_safe| (c::declar
                                      (c::condexpr
                                       (if (c::boolean-from-sint |ok|)
                                           |x|
                                         (c::sint-dec-const 0)))))
                           (|idx| (c::declar
                                   (c::condexpr
                                    (if (c::boolean-from-sint |ok|)
                                        (c::sub-sint-sint
                                         |sp| (c::sint-dec-const 1))
                                      (c::sint-dec-const 0)))))
                           (|v| (c::declar
                                 (struct-|wst|-read-|op|-element |idx| |st|)))
                           (|st| (struct-|wst|-write-|loc|-element
                                  |x_safe| |v| |st|))
                           (|pc| (c::assign
                                  (c::add-sint-sint
                                   |pc| (c::sint-dec-const 2))))
                           (|halted| (c::assign
                                      (c::condexpr
                                       (if (c::boolean-from-sint |ok|)
                                           |halted|
                                         (c::sint-dec-const 1)))))
                           (|fuel| (c::assign
                                    (c::sub-sint-sint
                                     |fuel| (c::sint-dec-const 1)))))
                      (|exec$loop| |st| |sp| |nl| |pc| |halted| |fuel|
                                   |wasm_buf|))
                  ;; ===== 0x45 i32.eqz =====
                  (if (c::boolean-from-sint
                       (c::eq-sint-sint |b| (c::sint-dec-const #x45)))
                      (let* ((|ok| (c::declar
                                    (c::gt-sint-sint
                                     |sp| (c::sint-dec-const 0))))
                             (|idx| (c::declar
                                     (c::condexpr
                                      (if (c::boolean-from-sint |ok|)
                                          (c::sub-sint-sint
                                           |sp| (c::sint-dec-const 1))
                                        (c::sint-dec-const 0)))))
                             (|v| (c::declar
                                   (struct-|wst|-read-|op|-element
                                    |idx| |st|)))
                             (|is0| (c::declar
                                     (c::sint-from-boolean
                                      (or (c::boolean-from-sint
                                           (c::eq-uint-uint
                                            |v| (c::uint-dec-const 0)))
                                          (c::boolean-from-sint
                                           (c::eq-uint-uint
                                            |v| (c::uint-dec-const 0)))))))
                             (|new_v| (c::declar
                                       (c::uint-from-sint |is0|)))
                             (|st| (struct-|wst|-write-|op|-element
                                    |idx| |new_v| |st|))
                             (|pc| (c::assign
                                    (c::add-sint-sint
                                     |pc| (c::sint-dec-const 1))))
                             (|halted| (c::assign
                                        (c::condexpr
                                         (if (c::boolean-from-sint |ok|)
                                             |halted|
                                           (c::sint-dec-const 1)))))
                             (|fuel| (c::assign
                                      (c::sub-sint-sint
                                       |fuel| (c::sint-dec-const 1)))))
                        (|exec$loop| |st| |sp| |nl| |pc| |halted| |fuel|
                                     |wasm_buf|))
                    ;; ===== 0x70 i32.rem_u =====
                    (if (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x70)))
                        (let* ((|ok| (c::declar
                                      (c::gt-sint-sint
                                       |sp| (c::sint-dec-const 1))))
                               (|bi| (c::declar
                                      (c::condexpr
                                       (if (c::boolean-from-sint |ok|)
                                           (c::sub-sint-sint
                                            |sp| (c::sint-dec-const 1))
                                         (c::sint-dec-const 0)))))
                               (|ai| (c::declar
                                      (c::condexpr
                                       (if (c::boolean-from-sint |ok|)
                                           (c::sub-sint-sint
                                            |sp| (c::sint-dec-const 2))
                                         (c::sint-dec-const 0)))))
                               (|bv| (c::declar
                                      (struct-|wst|-read-|op|-element
                                       |bi| |st|)))
                               (|av| (c::declar
                                      (struct-|wst|-read-|op|-element
                                       |ai| |st|)))
                               (|nz| (c::declar
                                      (c::sint-from-boolean
                                       (or (c::boolean-from-sint
                                            (c::ne-uint-uint
                                             |bv| (c::uint-dec-const 0)))
                                           (c::boolean-from-sint
                                            (c::ne-uint-uint
                                             |bv| (c::uint-dec-const 0)))))))
                               (|safe| (c::declar
                                        (c::sint-from-boolean
                                         (and (c::boolean-from-sint |ok|)
                                              (c::boolean-from-sint |nz|)))))
                               (|bv_safe| (c::declar
                                           (c::condexpr
                                            (if (c::boolean-from-sint |safe|)
                                                |bv|
                                              (c::uint-dec-const 1)))))
                               (|rv| (c::declar
                                      (c::rem-uint-uint |av| |bv_safe|)))
                               (|st| (struct-|wst|-write-|op|-element
                                      |ai| |rv| |st|))
                               (|sp| (c::assign
                                      (c::condexpr
                                       (if (c::boolean-from-sint |safe|)
                                           (c::sub-sint-sint
                                            |sp| (c::sint-dec-const 1))
                                         |sp|))))
                               (|pc| (c::assign
                                      (c::add-sint-sint
                                       |pc| (c::sint-dec-const 1))))
                               (|halted| (c::assign
                                          (c::condexpr
                                           (if (c::boolean-from-sint |safe|)
                                               |halted|
                                             (c::sint-dec-const 1)))))
                               (|fuel| (c::assign
                                        (c::sub-sint-sint
                                         |fuel| (c::sint-dec-const 1)))))
                          (|exec$loop| |st| |sp| |nl| |pc| |halted| |fuel|
                                       |wasm_buf|))
                      ;; ===== 0x02 block =====
                      (if (c::boolean-from-sint
                           (c::eq-sint-sint |b| (c::sint-dec-const #x02)))
                          (let* ((|ok| (c::declar
                                        (c::lt-sint-sint
                                         |nl| (c::sint-dec-const 16))))
                                 (|nl_safe| (c::declar
                                             (c::condexpr
                                              (if (c::boolean-from-sint |ok|)
                                                  |nl|
                                                (c::sint-dec-const 0)))))
                                 (|end_pc_raw| (c::declar
                                                (|scan_end|
                                                 (c::add-sint-sint
                                                  |pc|
                                                  (c::sint-dec-const 2))
                                                 |wasm_buf|)))
                                 (|end_pc| (c::declar
                                            (c::condexpr
                                             (if (c::boolean-from-sint
                                                  (c::sint-from-boolean
                                                   (and (c::boolean-from-sint
                                                         (c::ge-sint-sint
                                                          |end_pc_raw|
                                                          (c::sint-dec-const 0)))
                                                        (c::boolean-from-sint
                                                         (c::le-sint-sint
                                                          |end_pc_raw|
                                                          (c::sint-dec-const 60000))))))
                                                 |end_pc_raw|
                                               (c::sint-dec-const 0)))))
                                 (|st| (struct-|wst|-write-|lpc|-element
                                        |nl_safe| |end_pc| |st|))
                                 (|st| (struct-|wst|-write-|lsp|-element
                                        |nl_safe| |sp| |st|))
                                 (|st| (struct-|wst|-write-|lkind|-element
                                        |nl_safe|
                                        (c::uchar-from-sint
                                         (c::sint-dec-const 0))
                                        |st|))
                                 (|nl| (c::assign
                                        (c::condexpr
                                         (if (c::boolean-from-sint |ok|)
                                             (c::add-sint-sint
                                              |nl| (c::sint-dec-const 1))
                                           |nl|))))
                                 (|pc| (c::assign
                                        (c::add-sint-sint
                                         |pc| (c::sint-dec-const 2))))
                                 (|halted| (c::assign
                                            (c::condexpr
                                             (if (c::boolean-from-sint |ok|)
                                                 |halted|
                                               (c::sint-dec-const 1)))))
                                 (|fuel| (c::assign
                                          (c::sub-sint-sint
                                           |fuel| (c::sint-dec-const 1)))))
                            (|exec$loop| |st| |sp| |nl| |pc| |halted| |fuel|
                                         |wasm_buf|))
                        ;; ===== 0x03 loop =====
                        (if (c::boolean-from-sint
                             (c::eq-sint-sint |b| (c::sint-dec-const #x03)))
                            (let* ((|ok| (c::declar
                                          (c::lt-sint-sint
                                           |nl| (c::sint-dec-const 16))))
                                   (|nl_safe| (c::declar
                                               (c::condexpr
                                                (if (c::boolean-from-sint |ok|)
                                                    |nl|
                                                  (c::sint-dec-const 0)))))
                                   (|loop_pc| (c::declar
                                               (c::add-sint-sint
                                                |pc| (c::sint-dec-const 2))))
                                   (|st| (struct-|wst|-write-|lpc|-element
                                          |nl_safe| |loop_pc| |st|))
                                   (|st| (struct-|wst|-write-|lsp|-element
                                          |nl_safe| |sp| |st|))
                                   (|st| (struct-|wst|-write-|lkind|-element
                                          |nl_safe|
                                          (c::uchar-from-sint
                                           (c::sint-dec-const 1))
                                          |st|))
                                   (|nl| (c::assign
                                          (c::condexpr
                                           (if (c::boolean-from-sint |ok|)
                                               (c::add-sint-sint
                                                |nl| (c::sint-dec-const 1))
                                             |nl|))))
                                   (|pc| (c::assign |loop_pc|))
                                   (|halted| (c::assign
                                              (c::condexpr
                                               (if (c::boolean-from-sint |ok|)
                                                   |halted|
                                                 (c::sint-dec-const 1)))))
                                   (|fuel| (c::assign
                                            (c::sub-sint-sint
                                             |fuel| (c::sint-dec-const 1)))))
                              (|exec$loop| |st| |sp| |nl| |pc| |halted| |fuel|
                                           |wasm_buf|))
                          ;; ===== 0x0b end =====
                          (if (c::boolean-from-sint
                               (c::eq-sint-sint |b| (c::sint-dec-const #x0b)))
                              (if (c::boolean-from-sint
                                   (c::eq-sint-sint
                                    |nl| (c::sint-dec-const 0)))
                                  ;; top-level end: halt.
                                  (let* ((|halted|
                                          (c::assign (c::sint-dec-const 1)))
                                         (|fuel|
                                          (c::assign
                                           (c::sub-sint-sint
                                            |fuel| (c::sint-dec-const 1)))))
                                    (|exec$loop| |st| |sp| |nl| |pc| |halted|
                                                 |fuel| |wasm_buf|))
                                ;; pop label, advance pc.
                                (let* ((|nl| (c::assign
                                              (c::sub-sint-sint
                                               |nl| (c::sint-dec-const 1))))
                                       (|pc| (c::assign
                                              (c::add-sint-sint
                                               |pc| (c::sint-dec-const 1))))
                                       (|fuel| (c::assign
                                                (c::sub-sint-sint
                                                 |fuel| (c::sint-dec-const 1)))))
                                  (|exec$loop| |st| |sp| |nl| |pc| |halted|
                                               |fuel| |wasm_buf|)))
                            ;; ===== 0x0c br / 0x0d br_if =====
                            (let* ((|is_br| (c::declar
                                             (c::eq-sint-sint
                                              |b| (c::sint-dec-const #x0c))))
                                   (|is_brif| (c::declar
                                               (c::eq-sint-sint
                                                |b| (c::sint-dec-const #x0d))))
                                   (|is_brx| (c::declar
                                              (c::sint-from-boolean
                                               (or (c::boolean-from-sint
                                                    |is_br|)
                                                   (c::boolean-from-sint
                                                    |is_brif|))))))
                              (if (c::boolean-from-sint |is_brx|)
                                  ;; br / br_if: optionally pop, decide,
                                  ;; compute target.
                                  (let* ((|l_byte| (c::declar
                                                    (byte-at
                                                     (c::add-sint-sint
                                                      |pc|
                                                      (c::sint-dec-const 1)))))
                                         ;; For br_if, pop value and test.
                                         (|pop_ok| (c::declar
                                                    (c::sint-from-boolean
                                                     (or (c::boolean-from-sint
                                                          |is_br|)
                                                         (c::boolean-from-sint
                                                          (c::gt-sint-sint
                                                           |sp|
                                                           (c::sint-dec-const 0)))))))
                                         (|sp_after_pop|
                                          (c::declar
                                           (c::condexpr
                                            (if (c::boolean-from-sint |is_brif|)
                                                (c::condexpr
                                                 (if (c::boolean-from-sint
                                                      (c::gt-sint-sint
                                                       |sp|
                                                       (c::sint-dec-const 0)))
                                                     (c::sub-sint-sint
                                                      |sp|
                                                      (c::sint-dec-const 1))
                                                   |sp|))
                                              |sp|))))
                                         (|peek_idx|
                                          (c::declar
                                           (c::condexpr
                                            (if (c::boolean-from-sint
                                                 (c::gt-sint-sint
                                                  |sp|
                                                  (c::sint-dec-const 0)))
                                                (c::sub-sint-sint
                                                 |sp|
                                                 (c::sint-dec-const 1))
                                              (c::sint-dec-const 0)))))
                                         (|peek_v|
                                          (c::declar
                                           (struct-|wst|-read-|op|-element
                                            |peek_idx| |st|)))
                                         (|cond_true|
                                          (c::declar
                                           (c::sint-from-boolean
                                            (or (c::boolean-from-sint
                                                 (c::ne-uint-uint
                                                  |peek_v| (c::uint-dec-const 0)))
                                                (c::boolean-from-sint
                                                 (c::ne-uint-uint
                                                  |peek_v| (c::uint-dec-const 0)))))))
                                         (|take| (c::declar
                                                  (c::sint-from-boolean
                                                   (or (c::boolean-from-sint
                                                        |is_br|)
                                                       (c::boolean-from-sint
                                                        (c::sint-from-boolean
                                                         (and (c::boolean-from-sint
                                                               |is_brif|)
                                                              (c::boolean-from-sint
                                                               |cond_true|))))))))
                                         ;; Compute target when taking.
                                         (|l_ok|
                                          (c::declar
                                           (c::lt-sint-sint |l_byte| |nl|)))
                                         (|target_idx|
                                          (c::declar
                                           (c::condexpr
                                            (if (c::boolean-from-sint |l_ok|)
                                                (c::sub-sint-sint
                                                 (c::sub-sint-sint
                                                  |nl|
                                                  (c::sint-dec-const 1))
                                                 |l_byte|)
                                              (c::sint-dec-const 0)))))
                                         (|tpc_raw|
                                          (c::declar
                                           (struct-|wst|-read-|lpc|-element
                                            |target_idx| |st|)))
                                         (|tsp_raw|
                                          (c::declar
                                           (struct-|wst|-read-|lsp|-element
                                            |target_idx| |st|)))
                                         (|tkind_uc|
                                          (c::declar
                                           (struct-|wst|-read-|lkind|-element
                                            |target_idx| |st|)))
                                         (|tkind|
                                          (c::declar
                                           (c::sint-from-uchar |tkind_uc|)))
                                         (|tpc_ok|
                                          (c::declar
                                           (c::sint-from-boolean
                                            (and (c::boolean-from-sint
                                                  (c::ge-sint-sint
                                                   |tpc_raw|
                                                   (c::sint-dec-const 0)))
                                                 (c::boolean-from-sint
                                                  (c::le-sint-sint
                                                   |tpc_raw|
                                                   (c::sint-dec-const 60000)))))))
                                         (|tsp_ok|
                                          (c::declar
                                           (c::sint-from-boolean
                                            (and (c::boolean-from-sint
                                                  (c::ge-sint-sint
                                                   |tsp_raw|
                                                   (c::sint-dec-const 0)))
                                                 (c::boolean-from-sint
                                                  (c::le-sint-sint
                                                   |tsp_raw|
                                                   (c::sint-dec-const 64)))))))
                                         (|all_ok|
                                          (c::declar
                                           (c::sint-from-boolean
                                            (and (c::boolean-from-sint
                                                  |pop_ok|)
                                                 (c::boolean-from-sint
                                                  |l_ok|)
                                                 (c::boolean-from-sint
                                                  |tpc_ok|)
                                                 (c::boolean-from-sint
                                                  |tsp_ok|)))))
                                         ;; Compute new state.
                                         (|new_nl|
                                          (c::declar
                                           (c::condexpr
                                            (if (c::boolean-from-sint
                                                 (c::sint-from-boolean
                                                  (and (c::boolean-from-sint
                                                        |all_ok|)
                                                       (c::boolean-from-sint
                                                        |take|))))
                                                (c::condexpr
                                                 (if (c::boolean-from-sint
                                                      (c::eq-sint-sint
                                                       |tkind|
                                                       (c::sint-dec-const 1)))
                                                     (c::add-sint-sint
                                                      |target_idx|
                                                      (c::sint-dec-const 1))
                                                   |target_idx|))
                                              |nl|))))
                                         (|new_sp|
                                          (c::declar
                                           (c::condexpr
                                            (if (c::boolean-from-sint
                                                 (c::sint-from-boolean
                                                  (and (c::boolean-from-sint
                                                        |all_ok|)
                                                       (c::boolean-from-sint
                                                        |take|))))
                                                |tsp_raw|
                                              |sp_after_pop|))))
                                         (|new_pc|
                                          (c::declar
                                           (c::condexpr
                                            (if (c::boolean-from-sint
                                                 (c::sint-from-boolean
                                                  (and (c::boolean-from-sint
                                                        |all_ok|)
                                                       (c::boolean-from-sint
                                                        |take|))))
                                                |tpc_raw|
                                              (c::add-sint-sint
                                               |pc|
                                               (c::sint-dec-const 2))))))
                                         (|sp| (c::assign |new_sp|))
                                         (|nl| (c::assign |new_nl|))
                                         (|pc| (c::assign |new_pc|))
                                         (|halted|
                                          (c::assign
                                           (c::condexpr
                                            (if (c::boolean-from-sint
                                                 |all_ok|)
                                                |halted|
                                              (c::sint-dec-const 1)))))
                                         (|fuel| (c::assign
                                                  (c::sub-sint-sint
                                                   |fuel|
                                                   (c::sint-dec-const 1)))))
                                    (|exec$loop| |st| |sp| |nl| |pc| |halted|
                                                 |fuel| |wasm_buf|))
                                ;; unknown opcode: halt.
                                (let* ((|halted|
                                        (c::assign (c::sint-dec-const 1)))
                                       (|fuel|
                                        (c::assign
                                         (c::sub-sint-sint
                                          |fuel| (c::sint-dec-const 1)))))
                                  (|exec$loop| |st| |sp| |nl| |pc| |halted|
                                               |fuel| |wasm_buf|)))))))))))))
        (mv |st| |sp| |nl| |pc| |halted| |fuel|))
    (mv |st| |sp| |nl| |pc| |halted| |fuel|)))

(defrulel struct-wst-p-of-mv-nth-0-exec$loop
  (implies (struct-|wst|-p |st|)
           (struct-|wst|-p
            (mv-nth 0 (|exec$loop| |st| |sp| |nl| |pc| |halted| |fuel| |wasm_buf|))))
  :induct (|exec$loop| |st| |sp| |nl| |pc| |halted| |fuel| |wasm_buf|)
  :enable (|exec$loop|))

(defun |invoke| (|st| |m| |a| |b| |wasm_buf|)
  (declare (xargs :guard (and (c::star (struct-|wst|-p |st|))
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
        (|exec$loop| |st| |sp| |nl| |pc| |halted| |fuel| |wasm_buf|)
      (declare (ignore |sp| |nl| |pc| |halted| |fuel|))
      (mv (struct-|wst|-read-|op|-element (c::sint-dec-const 0) |st|)
          |st|))))

(c::atc |wasm_buf|
        |wmod|
        |wst|
        |check_magic|
        |parse$loop|
        |parse_module|
        |scan$loop|
        |scan_end|
        |exec$loop|
        |invoke|
        :file-name "wasm-vm1"
        :header t
        :proofs nil)
