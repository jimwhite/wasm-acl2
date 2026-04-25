; WASM VM2 — ACL2 source for ATC to translate to C.
;
; Block-structured successor to wasm-vm1.lisp.  See VM2_PLAN.md.
;
; Phase 1 status: vm2 = vm1 + a CFG side table (|wcfg|) populated by
; |extract_cfg|.  Execution is still per-opcode via |exec$loop| (unchanged
; from vm1) — we just compute the CFG as a side product and dump it for
; visual verification.  Phase 2 will replace |exec$loop| with the
; (|exec_straight_line|, |exec_blocks|) two-tier pair that consumes |wcfg|.
;
; |wcfg| is a parallel-array record of every block bracket
; (block / loop / if … else? … end) in the function body, with the
; matching `end` and (for `if`) `else` PCs precomputed.  This replaces
; the runtime byte-scan done by |scan_end| / |scan_else|.
;
; M1 scope: interpret small WebAssembly i32 modules (one exported function,
; i32 params/result, one local group, single-byte LEB128s for sizes).
;
; Design:
;   - `|wasm_buf|`: 64 KiB uchar external object; main.c fread's the .wasm here.
;   - `|wmod|`:    parsed-module struct populated by `|parse_module|`.
;   - `|wcfg|`:    bracket table populated by `|extract_cfg|` (NEW in vm2).
;   - `|parse_module|`: walks sections 0..N via `|parse$loop|`, filling |wmod|.
;   - `|extract_cfg|`:  one linear pass over the function body, filling |wcfg|.
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

(defrulel sint-max->=-200000
  (>= (c::sint-max) 200000)
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
;; Control-flow side table — populated by |extract_cfg| in one linear pass.
;;
;; Phase 1 (this commit): only |nbr| and |opener_pc|/|opener| are populated;
;; |end_pc|/|else_pc|/|pend|/|pend_top| are reserved for Phase 1.1's bracket
;; matcher.  This commit demonstrates the ATC pipeline accepts the new
;; defstruct + parallel-array-write pattern; it does not yet replace
;; |scan_end|/|scan_else|.
;;
;; Bounds:
;;   nbr      ∈ [0, 64]  — number of bracket entries used
;;   pend_top ∈ [0, 16]  — current bracket-matcher stack height (Phase 1.1)
;;   err      0=ok, 1=bracket overflow (>64), 2=pending overflow (>16),
;;            3=unbalanced (Phase 1.1)

(c::defstruct |wcfg|
  (|err|        c::uchar)
  (|nbr|        c::sint)
  (|opener_pc|  (c::sint  64))
  (|opener|     (c::uchar 64))
  (|end_pc|     (c::sint  64))
  (|else_pc|    (c::sint  64))
  (|pend_top|   c::sint)
  (|pend|       (c::sint  16)))

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
;; CFG extraction — Phase 1.1 (full bracket matching).
;;
;; Walks bytes [pc, end_pc) once, recording every block / loop / if opener
;; and resolving each `end` and `else` against the matcher stack `|pend|`.
;; Termination is structural: pc strictly advances by >=1 every iteration
;; and is bounded above by end_pc, so the measure (nfix (end_pc - pc))
;; strictly decreases — NO FUEL ARGUMENT.
;;
;; Per-step actions (mutually compatible — at most one ever fires):
;;   opener (0x02/0x03/0x04): write opener_pc/opener[nbr] = pc/b,
;;                            push nbr onto pend, nbr++, pend_top++.
;;   end    (0x0b)           : let slot = pend[pend_top-1];
;;                            write end_pc[slot] = pc+1; pend_top--.
;;                            (No-op when pend_top=0 — every function body
;;                             legally ends with a top-level end.)
;;   else   (0x05)           : let slot = pend[pend_top-1];
;;                            write else_pc[slot] = pc+1; pend stays.
;;
;; Wide opcodes (2-byte immediate) recognised: 0x02 0x03 0x04 0x05 0x0c
;; 0x0d 0x20 0x21 0x22 0x41.  Anything else is treated as 1-byte.  This
;; list matches scan$loop's is_wide list in vm1.
;;
;; Error reporting (writes |err|=1):
;;   - opener overflow: nbr already 64, or pend_top already 16.
;;   - stray else at depth 0.
;; A stray top-level end is *not* an error — required by spec.
;;
;; Bounds on |wcfg| fields after extract_cfg returns:
;;   nbr      ∈ [0, 64]
;;   pend_top ∈ [0, 16]   (should be 0 on a well-formed function body —
;;                         the final 0x0b at top level is silently dropped)
;;   end_pc[i], else_pc[i] ∈ [0, 60001]   (0 = unset for if without else)

;; ---- Per-step action helpers ---------------------------------------------
;; Each helper takes the running |w| and returns a new |w|.  Splitting these
;; out keeps each guard / return-type proof small; the main loop's
;; defrulel then only has to combine four leaf cases (open / end / else /
;; no-op) rather than expand a 3-deep chain of conditional rebinds.

(defun |apply_open| (|pc| |b| |w|)
  ;; Opener (0x02/0x03/0x04): write opener_pc/opener[nbr], push nbr onto
  ;; pend, bump nbr and pend_top.  Sets err=1 on overflow.
  (declare (xargs
    :guard (and (c::sintp |pc|)
                (c::sintp |b|)
                (c::star (struct-|wcfg|-p |w|))
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (<= 0 (c::integer-from-sint |b|))
                (<= (c::integer-from-sint |b|) 255))
    :guard-hints
    (("Goal"
      :in-theory
      (enable c::add-sint-sint
              c::add-sint-sint-okp
              c::sint-integerp-alt-def
              c::integer-from-cinteger-alt-def
              c::ge-sint-sint
              c::lt-sint-sint
              c::declar
              c::condexpr
              |STRUCT-wcfg-opener_pc-INDEX-OKP|
              |STRUCT-wcfg-opener-INDEX-OKP|
              |STRUCT-wcfg-pend-INDEX-OKP|)))))
  (let* ((|nbr_raw| (c::declar (struct-|wcfg|-read-|nbr| |w|)))
         (|pt_raw|  (c::declar (struct-|wcfg|-read-|pend_top| |w|)))
         (|ok|
          (c::declar
           (c::sint-from-boolean
            (and (c::boolean-from-sint
                  (c::ge-sint-sint |nbr_raw| (c::sint-dec-const 0)))
                 (c::boolean-from-sint
                  (c::lt-sint-sint |nbr_raw| (c::sint-dec-const 64)))
                 (c::boolean-from-sint
                  (c::ge-sint-sint |pt_raw| (c::sint-dec-const 0)))
                 (c::boolean-from-sint
                  (c::lt-sint-sint |pt_raw| (c::sint-dec-const 16))))))))
    (if (c::boolean-from-sint |ok|)
        (let* ((|w| (struct-|wcfg|-write-|opener_pc|-element
                     |nbr_raw| |pc| |w|))
               (|w| (struct-|wcfg|-write-|opener|-element
                     |nbr_raw| (c::uchar-from-sint |b|) |w|))
               (|w| (struct-|wcfg|-write-|pend|-element
                     |pt_raw| |nbr_raw| |w|))
               (|w| (struct-|wcfg|-write-|nbr|
                     (c::add-sint-sint |nbr_raw| (c::sint-dec-const 1))
                     |w|))
               (|w| (struct-|wcfg|-write-|pend_top|
                     (c::add-sint-sint |pt_raw| (c::sint-dec-const 1))
                     |w|)))
          |w|)
      (let ((|w| (struct-|wcfg|-write-|err|
                  (c::uchar-from-sint (c::sint-dec-const 1)) |w|)))
        |w|))))

(defrulel struct-wcfg-p-of-apply_open
  (implies (and (c::sintp |pc|)
                (c::sintp |b|)
                (c::star (struct-|wcfg|-p |w|))
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (<= 0 (c::integer-from-sint |b|))
                (<= (c::integer-from-sint |b|) 255))
           (c::star (struct-|wcfg|-p (|apply_open| |pc| |b| |w|))))
  :enable (|apply_open|
           c::add-sint-sint
           c::ge-sint-sint
           c::lt-sint-sint
           c::declar
           c::condexpr))

(defun |apply_end| (|pc| |w|)
  ;; End (0x0b): if pend stack non-empty, write end_pc[peek]=pc+1 and
  ;; pop; otherwise silently no-op (top-level end is legal).
  (declare (xargs
    :guard (and (c::sintp |pc|)
                (c::star (struct-|wcfg|-p |w|))
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000))
    :guard-hints
    (("Goal"
      :in-theory
      (enable c::add-sint-sint
              c::add-sint-sint-okp
              c::sub-sint-sint
              c::sub-sint-sint-okp
              c::sint-integerp-alt-def
              c::integer-from-cinteger-alt-def
              c::gt-sint-sint
              c::le-sint-sint
              c::ge-sint-sint
              c::lt-sint-sint
              c::declar
              c::condexpr
              |STRUCT-wcfg-pend-INDEX-OKP|
              |STRUCT-wcfg-end_pc-INDEX-OKP|)))))
  (let* ((|pt_raw| (c::declar (struct-|wcfg|-read-|pend_top| |w|)))
         (|ok|
          (c::declar
           (c::sint-from-boolean
            (and (c::boolean-from-sint
                  (c::gt-sint-sint |pt_raw| (c::sint-dec-const 0)))
                 (c::boolean-from-sint
                  (c::le-sint-sint |pt_raw| (c::sint-dec-const 16))))))))
    (if (c::boolean-from-sint |ok|)
        (let* ((|top_idx|
                (c::declar
                 (c::sub-sint-sint |pt_raw| (c::sint-dec-const 1))))
               (|peek_raw|
                (c::declar
                 (struct-|wcfg|-read-|pend|-element |top_idx| |w|)))
               (|peek|
                (c::declar
                 (c::condexpr
                  (if (c::boolean-from-sint
                       (c::sint-from-boolean
                        (and (c::boolean-from-sint
                              (c::ge-sint-sint
                               |peek_raw| (c::sint-dec-const 0)))
                             (c::boolean-from-sint
                              (c::lt-sint-sint
                               |peek_raw| (c::sint-dec-const 64))))))
                      |peek_raw|
                    (c::sint-dec-const 0)))))
               (|w| (struct-|wcfg|-write-|end_pc|-element
                     |peek|
                     (c::add-sint-sint |pc| (c::sint-dec-const 1))
                     |w|))
               (|w| (struct-|wcfg|-write-|pend_top| |top_idx| |w|)))
          |w|)
      (let ((|w| (struct-|wcfg|-write-|pend_top| |pt_raw| |w|)))
        |w|))))

(defrulel struct-wcfg-p-of-apply_end
  (implies (and (c::sintp |pc|)
                (c::star (struct-|wcfg|-p |w|))
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000))
           (c::star (struct-|wcfg|-p (|apply_end| |pc| |w|))))
  :enable (|apply_end|
           c::add-sint-sint
           c::sub-sint-sint
           c::gt-sint-sint
           c::le-sint-sint
           c::ge-sint-sint
           c::lt-sint-sint
           c::declar
           c::condexpr))

(defun |apply_else| (|pc| |w|)
  ;; Else (0x05): if pend stack non-empty, write else_pc[peek]=pc+1 and
  ;; do NOT pop; otherwise stray else — set err=1.
  (declare (xargs
    :guard (and (c::sintp |pc|)
                (c::star (struct-|wcfg|-p |w|))
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000))
    :guard-hints
    (("Goal"
      :in-theory
      (enable c::add-sint-sint
              c::add-sint-sint-okp
              c::sub-sint-sint
              c::sub-sint-sint-okp
              c::sint-integerp-alt-def
              c::integer-from-cinteger-alt-def
              c::gt-sint-sint
              c::le-sint-sint
              c::ge-sint-sint
              c::lt-sint-sint
              c::declar
              c::condexpr
              |STRUCT-wcfg-pend-INDEX-OKP|
              |STRUCT-wcfg-else_pc-INDEX-OKP|)))))
  (let* ((|pt_raw| (c::declar (struct-|wcfg|-read-|pend_top| |w|)))
         (|ok|
          (c::declar
           (c::sint-from-boolean
            (and (c::boolean-from-sint
                  (c::gt-sint-sint |pt_raw| (c::sint-dec-const 0)))
                 (c::boolean-from-sint
                  (c::le-sint-sint |pt_raw| (c::sint-dec-const 16))))))))
    (if (c::boolean-from-sint |ok|)
        (let* ((|top_idx|
                (c::declar
                 (c::sub-sint-sint |pt_raw| (c::sint-dec-const 1))))
               (|peek_raw|
                (c::declar
                 (struct-|wcfg|-read-|pend|-element |top_idx| |w|)))
               (|peek|
                (c::declar
                 (c::condexpr
                  (if (c::boolean-from-sint
                       (c::sint-from-boolean
                        (and (c::boolean-from-sint
                              (c::ge-sint-sint
                               |peek_raw| (c::sint-dec-const 0)))
                             (c::boolean-from-sint
                              (c::lt-sint-sint
                               |peek_raw| (c::sint-dec-const 64))))))
                      |peek_raw|
                    (c::sint-dec-const 0))))))
          (let ((|w| (struct-|wcfg|-write-|else_pc|-element
                     |peek|
                     (c::add-sint-sint |pc| (c::sint-dec-const 1))
                     |w|)))
            |w|))
      (let ((|w| (struct-|wcfg|-write-|err|
                  (c::uchar-from-sint (c::sint-dec-const 1)) |w|)))
        |w|))))

(defrulel struct-wcfg-p-of-apply_else
  (implies (and (c::sintp |pc|)
                (c::star (struct-|wcfg|-p |w|))
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000))
           (c::star (struct-|wcfg|-p (|apply_else| |pc| |w|))))
  :enable (|apply_else|
           c::add-sint-sint
           c::sub-sint-sint
           c::gt-sint-sint
           c::le-sint-sint
           c::ge-sint-sint
           c::lt-sint-sint
           c::declar
           c::condexpr))

;; ---- Main extraction loop ------------------------------------------------

(defun |extract_cfg$loop| (|pc| |end_pc| |w| |wasm_buf|)
  (declare (xargs
    :guard (and (c::sintp |pc|)
                (c::sintp |end_pc|)
                (c::star (struct-|wcfg|-p |w|))
                (object-|wasm_buf|-p |wasm_buf|)
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (<= 0 (c::integer-from-sint |end_pc|))
                (<= (c::integer-from-sint |end_pc|) 60000))
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
              c::ne-sint-sint
              c::gt-sint-sint
              c::lt-sint-sint
              c::le-sint-sint
              c::ge-sint-sint
              c::declar
              c::assign
              c::condexpr
              |STRUCT-wcfg-opener_pc-INDEX-OKP|
              |STRUCT-wcfg-opener-INDEX-OKP|
              |STRUCT-wcfg-end_pc-INDEX-OKP|
              |STRUCT-wcfg-else_pc-INDEX-OKP|
              |STRUCT-wcfg-pend-INDEX-OKP|)))
    :measure (nfix (- (c::integer-from-sint |end_pc|)
                      (c::integer-from-sint |pc|)))
    :hints (("Goal"
             :in-theory
             (enable c::lt-sint-sint
                     c::add-sint-sint
                     c::sint-integerp-alt-def
                     c::declar
                     c::assign
                     c::condexpr)))))
  (if (mbt (and (c::sintp |pc|)
                (c::sintp |end_pc|)
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (<= 0 (c::integer-from-sint |end_pc|))
                (<= (c::integer-from-sint |end_pc|) 60000)))
      (if (c::boolean-from-sint
           (c::sint-from-boolean
            (and (c::boolean-from-sint
                  (c::lt-sint-sint |pc| |end_pc|))
                 (c::boolean-from-sint
                  (c::lt-sint-sint |pc| (c::sint-dec-const 59998))))))
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
                 (|is_end_op|
                  (c::declar
                   (c::eq-sint-sint |b| (c::sint-dec-const #x0b))))
                 (|is_else_op|
                  (c::declar
                   (c::eq-sint-sint |b| (c::sint-dec-const #x05))))
                 (|is_wide|
                  (c::declar
                   (c::sint-from-boolean
                    (or (c::boolean-from-sint |is_open|)
                        (c::boolean-from-sint |is_else_op|)
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x0c)))
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x0d)))
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x20)))
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x21)))
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x22)))
                        (c::boolean-from-sint
                         (c::eq-sint-sint |b| (c::sint-dec-const #x41)))))))
                 ;; Single-call dispatch — at most one helper fires per step
                 ;; because is_open / is_end_op / is_else_op are mutually
                 ;; exclusive (b can only equal one of those constants).
                 (|w|
                  (if (c::boolean-from-sint |is_open|)
                      (|apply_open| |pc| |b| |w|)
                    (if (c::boolean-from-sint |is_end_op|)
                        (|apply_end| |pc| |w|)
                      (if (c::boolean-from-sint |is_else_op|)
                          (|apply_else| |pc| |w|)
                        |w|))))
                 (|step|
                  (c::declar
                   (c::condexpr
                    (if (c::boolean-from-sint |is_wide|)
                        (c::sint-dec-const 2)
                      (c::sint-dec-const 1)))))
                 (|pc| (c::assign (c::add-sint-sint |pc| |step|))))
            (|extract_cfg$loop| |pc| |end_pc| |w| |wasm_buf|))
        (mv |pc| |w|))
    (mv nil nil)))

(defrulel struct-wcfg-p-of-mv-nth-1-extract_cfg$loop
  (implies (and (c::sintp |pc|)
                (c::sintp |end_pc|)
                (c::star (struct-|wcfg|-p |w|))
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (<= 0 (c::integer-from-sint |end_pc|))
                (<= (c::integer-from-sint |end_pc|) 60000))
           (c::star
            (struct-|wcfg|-p
             (mv-nth 1 (|extract_cfg$loop| |pc| |end_pc| |w| |wasm_buf|)))))
  :induct (|extract_cfg$loop| |pc| |end_pc| |w| |wasm_buf|)
  :enable (|extract_cfg$loop|
           c::add-sint-sint
           c::lt-sint-sint
           c::eq-sint-sint
           c::boolean-from-sint
           c::sint-from-boolean
           c::sint-integerp-alt-def
           c::declar
           c::assign
           c::condexpr))

(defun |extract_cfg| (|w| |m| |wasm_buf|)
  (declare (xargs
    :guard (and (c::star (struct-|wcfg|-p |w|))
                (c::star (struct-|wmod|-p |m|))
                (object-|wasm_buf|-p |wasm_buf|))
    :guard-hints
    (("Goal"
      :in-theory
      (enable object-|wasm_buf|-p
              c::declar
              c::assign
              c::condexpr
              c::add-sint-sint
              c::add-sint-sint-okp
              c::ge-sint-sint
              c::le-sint-sint
              c::lt-sint-sint
              c::boolean-from-sint
              c::sint-from-boolean
              c::sint-integerp-alt-def)))))
  (let* ((|body_off_raw| (c::declar (struct-|wmod|-read-|body_off| |m|)))
         (|body_len_raw| (c::declar (struct-|wmod|-read-|body_len| |m|)))
         (|safe|
          (c::declar
           (c::sint-from-boolean
            (and (c::boolean-from-sint
                  (c::ge-sint-sint
                   |body_off_raw| (c::sint-dec-const 0)))
                 (c::boolean-from-sint
                  (c::le-sint-sint
                   |body_off_raw| (c::sint-dec-const 60000)))
                 (c::boolean-from-sint
                  (c::ge-sint-sint
                   |body_len_raw| (c::sint-dec-const 0)))
                 (c::boolean-from-sint
                  (c::le-sint-sint
                   |body_len_raw| (c::sint-dec-const 60000)))))))
         (|pc|
          (c::declar
           (c::condexpr
            (if (c::boolean-from-sint |safe|)
                |body_off_raw|
              (c::sint-dec-const 0)))))
         (|end_raw|
          (c::declar
           (c::condexpr
            (if (c::boolean-from-sint |safe|)
                (c::add-sint-sint |body_off_raw| |body_len_raw|)
              (c::sint-dec-const 0)))))
         (|end_pc|
          (c::declar
           (c::condexpr
            (if (c::boolean-from-sint
                 (c::le-sint-sint |end_raw| (c::sint-dec-const 60000)))
                |end_raw|
              (c::sint-dec-const 60000))))))
    (mv-let (|pc| |w|)
        (|extract_cfg$loop| |pc| |end_pc| |w| |wasm_buf|)
      (declare (ignore |pc|))
      |w|)))

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
;; |wcfg_end_pc_at| — linear scan over the precomputed wcfg.
;;
;; Returns end_pc[i] for the first i where opener_pc[i] == |pc|, else 0.
;; Replaces the runtime |scan_end| byte-walker for block (0x02) entry in
;; the block-structured dispatcher |exec_blocks|.
;;
;; Structured as a $loop accumulator + thin wrapper, matching the
;; |scan$loop| / |scan_end| pattern that ATC accepts as a C while-loop.

(defun |wcfg_end_pc_at$loop| (|pc| |i| |acc| |w|)
  (declare (xargs
    :guard (and (c::sintp |pc|)
                (c::sintp |i|)
                (c::sintp |acc|)
                (c::star (struct-|wcfg|-p |w|))
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (<= 0 (c::integer-from-sint |i|))
                (<= (c::integer-from-sint |i|) 64))
    :guard-hints
    (("Goal"
      :in-theory
      (enable c::declar c::assign c::condexpr
              c::add-sint-sint c::add-sint-sint-okp
              c::lt-sint-sint c::ge-sint-sint c::eq-sint-sint
              c::boolean-from-sint c::sint-from-boolean
              c::sint-integerp-alt-def
              c::integer-from-cinteger-alt-def
              |STRUCT-wcfg-opener_pc-INDEX-OKP|
              |STRUCT-wcfg-end_pc-INDEX-OKP|)))
    :measure (nfix (- 64 (c::integer-from-sint |i|)))
    :hints (("Goal" :in-theory (enable c::lt-sint-sint
                                       c::ge-sint-sint
                                       c::eq-sint-sint
                                       c::add-sint-sint
                                       c::sint-integerp-alt-def
                                       c::boolean-from-sint
                                       c::sint-from-boolean
                                       c::declar
                                       c::assign
                                       c::condexpr)))))
  (if (mbt (and (<= 0 (c::integer-from-sint |i|))
                (<= (c::integer-from-sint |i|) 64)))
      (if (c::boolean-from-sint
           (c::sint-from-boolean
            (and (c::boolean-from-sint
                  (c::ge-sint-sint
                   (struct-|wcfg|-read-|nbr| |w|) (c::sint-dec-const 0)))
                 (c::boolean-from-sint
                  (c::lt-sint-sint
                   (struct-|wcfg|-read-|nbr| |w|) (c::sint-dec-const 65)))
                 (c::boolean-from-sint
                  (c::lt-sint-sint |i| (struct-|wcfg|-read-|nbr| |w|)))
                 (c::boolean-from-sint
                  (c::lt-sint-sint |i| (c::sint-dec-const 64))))))
          (let* ((|opc| (c::declar
                         (struct-|wcfg|-read-|opener_pc|-element |i| |w|)))
                 (|acc|
                  (c::assign
                   (c::condexpr
                    (if (c::boolean-from-sint
                         (c::sint-from-boolean
                          (and (c::boolean-from-sint
                                (c::eq-sint-sint
                                 |acc| (c::sint-dec-const 0)))
                               (c::boolean-from-sint
                                (c::eq-sint-sint |opc| |pc|)))))
                        (struct-|wcfg|-read-|end_pc|-element |i| |w|)
                      |acc|))))
                 (|i| (c::assign (c::add-sint-sint
                                  |i| (c::sint-dec-const 1)))))
            (|wcfg_end_pc_at$loop| |pc| |i| |acc| |w|))
        (mv |i| |acc|))
    (mv |i| |acc|)))

(defrulel sintp-of-mv-nth-1-wcfg_end_pc_at$loop
  (implies (and (c::sintp |pc|)
                (c::sintp |i|)
                (c::sintp |acc|)
                (c::star (struct-|wcfg|-p |w|))
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000)
                (<= 0 (c::integer-from-sint |i|))
                (<= (c::integer-from-sint |i|) 64))
           (c::sintp (mv-nth 1 (|wcfg_end_pc_at$loop| |pc| |i| |acc| |w|))))
  :induct (|wcfg_end_pc_at$loop| |pc| |i| |acc| |w|)
  :enable (|wcfg_end_pc_at$loop|
           c::lt-sint-sint
           c::ge-sint-sint
           c::eq-sint-sint
           c::add-sint-sint
           c::declar
           c::assign
           c::condexpr))

(defun |wcfg_end_pc_at| (|pc| |w|)
  (declare (xargs
    :guard (and (c::sintp |pc|)
                (c::star (struct-|wcfg|-p |w|))
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000))
    :guard-hints
    (("Goal" :in-theory (enable c::declar c::sint-integerp-alt-def)))))
  (let* ((|i|   (c::declar (c::sint-dec-const 0)))
         (|acc| (c::declar (c::sint-dec-const 0))))
    (mv-let (|i| |acc|)
        (|wcfg_end_pc_at$loop| |pc| |i| |acc| |w|)
      (declare (ignore |i|))
      |acc|)))

(defrulel sintp-of-wcfg_end_pc_at
  (implies (and (c::sintp |pc|)
                (c::star (struct-|wcfg|-p |w|))
                (<= 0 (c::integer-from-sint |pc|))
                (<= (c::integer-from-sint |pc|) 60000))
           (c::sintp (|wcfg_end_pc_at| |pc| |w|)))
  :enable (|wcfg_end_pc_at| c::declar))

(defun |exec_blocks| (|st| |sp| |nl| |pc| |halted| |fuel| |w| |wasm_buf|)
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
                (c::star (struct-|wcfg|-p |w|))
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
    ;; Lex-style measure: fuel dominates, with pc as tiebreaker.  CF arms
    ;; decrement fuel by 1 (always shrinks measure).  SL arms (0x20 0x21
    ;; 0x22 0x45 0x70) leave fuel alone but advance pc by 1 or 2, shrinking
    ;; the (60000 - pc) tail.  The 70000 multiplier dominates any pc swing
    ;; in [0,60000] so CF transitions strictly decrease the total.
    :measure (nfix (+ (* (c::integer-from-sint |fuel|) 70000)
                      (- 60000 (c::integer-from-sint |pc|))))
    :hints (("Goal"
             :in-theory
             (enable c::gt-sint-sint
                     c::lt-sint-sint
                     c::ge-sint-sint
                     c::le-sint-sint
                     c::eq-sint-sint
                     c::ne-sint-sint
                     c::eq-uint-uint
                     c::ne-uint-uint
                     c::add-sint-sint
                     c::sub-sint-sint
                     c::sint-integerp-alt-def
                     c::boolean-from-sint
                     c::sint-from-boolean
                     c::declar
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
                                     (c::sint-dec-const 1))))))

                  (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel|
                               |w| |wasm_buf|))
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
                                       (c::sint-dec-const 1))))))

                    (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel|
                                 |w| |wasm_buf|))
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
                                         (c::sint-dec-const 1))))))

                      (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel|
                                   |w| |wasm_buf|))
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
                                           (c::sint-dec-const 1))))))

                        (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel|
                                     |w| |wasm_buf|))
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
                                             (c::sint-dec-const 1))))))

                          (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel|
                                       |w| |wasm_buf|))
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
                                                (|wcfg_end_pc_at|
                                                 |pc|
                                                 |w|)))
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
                            (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel|
                                         |w| |wasm_buf|))
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
                              (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel|
                                           |w| |wasm_buf|))
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
                                    (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel| |w| |wasm_buf|))
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
                                  (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel| |w| |wasm_buf|)))
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
                                    (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel| |w| |wasm_buf|))
                                ;; unknown opcode: halt.
                                (let* ((|halted|
                                        (c::assign (c::sint-dec-const 1)))
                                       (|fuel|
                                        (c::assign
                                         (c::sub-sint-sint
                                          |fuel| (c::sint-dec-const 1)))))
                                  (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel| |w| |wasm_buf|)))))))))))))
        (mv |st| |sp| |nl| |pc| |halted| |fuel|))
    (mv |st| |sp| |nl| |pc| |halted| |fuel|)))

(defrulel struct-wst-p-of-mv-nth-0-exec_blocks
  (implies (struct-|wst|-p |st|)
           (struct-|wst|-p
            (mv-nth 0 (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel| |w| |wasm_buf|))))
  :induct (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel| |w| |wasm_buf|)
  :enable (|exec_blocks|))


;; Phase 2b entry point.  Calls |extract_cfg| once over the function body
;; to populate |w|, then runs |exec_blocks| (the block-structured outer
;; dispatcher) which uses |w| to look up matching `end' positions instead
;; of doing the runtime byte-scan that |exec$loop| does via |scan_end|.
(defun |invoke_v2| (|st| |m| |a| |b| |w| |wasm_buf|)
  (declare (xargs :guard (and (c::star (struct-|wst|-p |st|))
                              (c::star (struct-|wmod|-p |m|))
                              (c::uintp |a|)
                              (c::uintp |b|)
                              (c::star (struct-|wcfg|-p |w|))
                              (object-|wasm_buf|-p |wasm_buf|))
                  :guard-hints
                  (("Goal" :in-theory (enable object-|wasm_buf|-p
                                              c::declar c::assign
                                              c::condexpr
                                              c::add-sint-sint
                                              c::add-sint-sint-okp
                                              c::ge-sint-sint
                                              c::le-sint-sint
                                              c::boolean-from-sint
                                              c::sint-from-boolean
                                              c::sint-integerp-alt-def)))))
  (let* ((|st| (struct-|wst|-write-|loc|-element
                (c::sint-dec-const 0) |a| |st|))
         (|st| (struct-|wst|-write-|loc|-element
                (c::sint-dec-const 1) |b| |st|))
         (|w|  (|extract_cfg| |w| |m| |wasm_buf|))
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
        (|exec_blocks| |st| |sp| |nl| |pc| |halted| |fuel| |w| |wasm_buf|)
      (declare (ignore |sp| |nl| |pc| |halted| |fuel|))
      (mv (struct-|wst|-read-|op|-element (c::sint-dec-const 0) |st|)
          |st|
          |w|))))

(c::atc |wasm_buf|
        |wmod|
        |wst|
        |check_magic|
        |parse$loop|
        |parse_module|
        |wcfg|
        |apply_open|
        |apply_end|
        |apply_else|
        |extract_cfg$loop|
        |extract_cfg|
        |wcfg_end_pc_at$loop|
        |wcfg_end_pc_at|
        |exec_blocks|
        |invoke_v2|
        :file-name "wasm-vm2"
        :header t
        :proofs nil)
