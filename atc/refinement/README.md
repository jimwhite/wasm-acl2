# atc/refinement — bridging the ATC VM to the ACL2 WASM spec

This directory contains the first refinement proof between the ATC-generated
WebAssembly VM (`atc/wasm-vm1.lisp`, in the `ACL2` package, ATC fragment)
and the operational WASM semantics (`execution.lisp`, in the `WASM` package,
structured AST over `statep`).

## 1. What is here

- [cert.acl2](cert.acl2) — portcullis that mirrors the ATC book's
  `:ttags` and pulls in `kestrel/wasm/portcullis` so the spec package is
  available.
- [proof-local-get.lisp](proof-local-get.lisp) — the first end-to-end
  spike, targeting the `local.get` opcode. Certifies in ~8 s.

Two theorems are proven today:

1. **`spec-local-get-top`** (spec side). Given a well-formed `statep`
   whose current frame has `(:local.get x) :: rest` as its next
   instructions and an empty operand stack, `wasm::execute-local.get`
   produces a state whose operand-stack top equals `(nth-local x locals)`.

2. **`atc-local-get-unfolds`** (ATC side). Under a well-formedness
   predicate `wf-local-get` that pins down struct/buffer types, the
   scalar argument ranges (`sp ∈ [0,64)`, `pc ∈ [0,59998)`,
   `x ∈ [0,16)`), and the two bytes at `pc` being `0x20` and the uchar
   encoding of `x`, one fueled step of `|exec$loop|` equals

   ```
   (struct-wst-write-op-element
     sp
     (struct-wst-read-loc-element
       (sint-from-uchar (uchar-array-read wasm_buf (pc+1)))
       st)
     st)
   ```

   That is: op[sp] becomes loc[x] (with x recovered from the pc+1 byte),
   expressed as a pure structural rewrite — no read-of-write simplification
   happens here.

The book is deliberately kept to what certifies without a supporting
rewrite layer, so the missing infrastructure is visible in the source.

## 2. What's *not* here yet, and why

The obvious next theorem — "after one step, the i32 on top of the
abstracted ATC operand stack equals the i32 on top of the spec operand
stack" — needs two small lemmas that ATC's code-generator `defstruct`
does **not** emit for us:

1. **Read-of-write-same-index** on the generated element accessors:

   ```
   (struct-wst-read-op-element i (struct-wst-write-op-element i v s)) = v
   ```

   under `(struct-wst-p s)`, `(c::uintp v)`, `i ∈ [0, 64)`.

2. **Byte → sint bridge** under the wf hypothesis:

   ```
   (c::sint-from-uchar (c::uchar-array-read wasm_buf (pc+1))) = x
   ```

`defstruct` emits the return-type theorems, fix congruences, and
index-okp rules but no read-of-write theory. The analogous machinery
exists for *uchar* arrays in
[`books/kestrel/c/examples/strcpy-safe-support.lisp`](../../../../../home/acl2/books/kestrel/c/examples/strcpy-safe-support.lisp)
via `c::uchar-array-read-of-sint-to-nth` and its `update-nth` sibling
(they convert array ops into `nth`/`update-nth`, where the identity is
standard). We need a parallel development for `uint` arrays and for the
composition through the `value-struct-read-aux` / `-write-aux` layer.

Tried and rejected: proving the lemma inline with an aggressive `:enable`
cloud (`value-struct-read-aux`, `value-struct-write-aux`,
`uint-array-of`, `uint-list-fix`, etc.). The proof walks deep into the
alist representation of struct members and stalls; it is library-scale,
not inline-scale.

Proposed next step: write `atc/refinement/atc-wasm-support.lisp` — a
small shared book providing:

- `uint-array-read-of-sint-to-nth` / `-write-of-sint-to-update-nth`
  (port of the strcpy-safe idiom to `uint`).
- Composed into `struct-wst-read/write-<field>-element` so that
  read-of-write-same/diff reduce to the standard `nth`/`update-nth`
  identities.
- `sint-from-uchar-of-uchar-from-sint` under the natural bounds.

Once that exists, the connection theorem for `local.get` is a short
`:use`-combination of `spec-local-get-top`, `atc-local-get-unfolds`,
read-of-write-same, and the byte bridge. The same support book is then
reused for every other opcode refinement (`local.set`, `local.tee`,
`i32.eqz`, `i32.rem_u`, …).

## 3. Proof-engineering notes (keep for the next opcode)

- **`|exec$loop|` only unfolds via `:free`-expand.** The hint

  ```lisp
  :expand ((:free (st sp nl pc halted fuel wasm_buf)
                  (|exec$loop| st sp nl pc halted fuel wasm_buf)))
  ```

  is what actually opens the dispatch. A plain `:expand` with concrete
  argument terms is silently ignored.

- **`wf-local-get` is introduced with `:guard t :verify-guards nil`.**
  Its body uses `c::add-sint-sint` etc., which require okp side
  conditions we don't want to discharge at predicate-admit time. The
  theorems that `:use` the predicate do the arithmetic reasoning.

- **`make-state` takes 5 fields** (`:store :call-stack :memory :globals
  :table`), not 4. Easy to miss.

- **`advance-instrs` is a macro**, not a function. It cannot go in an
  `:in-theory (enable ...)` list; enable `update-current-instrs` and
  `current-instrs` instead.

- **Style borrowed from [`proofs/GCD_PROOF_NOTES.md`](../../proofs/GCD_PROOF_NOTES.md):**
  `:do-not '(generalize fertilize eliminate-destructors)`, enable a
  bounded cluster of ATC operators, keep state constructors folded, one
  rewrite per induction step. The cluster that works for `local.get` is
  in [`proof-local-get.lisp`](proof-local-get.lisp) and should be the
  starting point for `local.set` / `local.tee`.

## 4. Honest architectural review: are we actually refining the spec?

The request that prompted this note: *"was this ATC implementation of the
WASM VM constructed by following the pattern of using the ACL2 WASM spec
to generate that code?"* — Short answer: **no, and the seam is real.**

### 4.1 How the ATC VM was actually authored

[`atc/wasm-vm1.lisp`](../wasm-vm1.lisp) is a **hand-written** ATC-fragment
interpreter. It was designed bottom-up against the C code we wanted ATC
to emit, not top-down from `execution.lisp`. Concretely:

- Its state is a flat `(c::defstruct |wst| …)` with fixed-size `uint`
  and `sint` arrays (`op[64]`, `loc[16]`, `lpc/lsp/lkind[16]`). The
  spec's state is `(defaggregate state …)` with a call-stack of frames,
  each holding a `locals` list, an `operand-stack`, an AST-level
  `instrs` list, and a `label-stack`. There is no shared type.
- Its "program counter" is a byte offset into a 64 KiB `uchar` external
  object (`|wasm_buf|`). The spec's "program counter" is the head of
  `(frame->instrs (current-frame state))` — a list of tagged AST nodes.
- Its dispatch is a hand-written 10-opcode `if` cascade (`local.get`,
  `local.set`, `local.tee`, `i32.eqz`, `i32.rem_u`, `block`, `loop`,
  `end`, `br`, `br_if`). The spec has one `execute-<op>` function per
  opcode, factored around structured AST forms.
- Its parser (`|check_magic|`, `|parse$loop|`, `|parse_module|`) was
  authored from scratch in ATC fragment against the raw binary layout.

None of this was produced by a refinement-style derivation from
`execution.lisp`, and none of it shares package, types, or signatures
with the spec.

### 4.2 Where it went off-track

The inflection point is the parser. The spec
([`execution.lisp`](../../execution.lisp)) executes over *already-decoded
AST instructions* (`:local.get`, `(:block bt body)`, …). It deliberately
does not know about the binary format — indeed its line 773 comment
points at [`kestrel/wasm/parse-binary.lisp`](../../../../../home/acl2/books/kestrel/wasm/parse-binary.lisp)
(which does exist and decodes `byte-listp` into an AST) as the upstream
for bytes. So when M1 needed to load a real `.wasm` file, there were
two spec-aligned paths:

- **(a) Refinement path.** Import `wasm::parse-binary` to turn bytes into
  the AST the spec consumes. Then express the ATC VM as a refinement of
  the spec's AST-level interpreter, and emit C from that. The parser is
  out-of-scope for ATC (it allocates lists); it stays in ACL2 and runs
  at module-load time in a separate tool, or is translated by a
  different mechanism.
- **(b) Pragmatic path.** Bytes → interpreter, all in ATC fragment, in
  one binary. No AST. This is what we did.

Path (b) got the oracle-verified M1 demo quickly, but it broke the
refinement chain in two places: the ATC parser has no ACL2 spec
counterpart to refine against (it's its own source of truth), and the
ATC interpreter is written in the binary representation rather than the
AST representation, so every opcode proof now has to carry the
byte-decoding overhead (`sint-from-uchar (uchar-array-read buf (pc+k))`
≡ the AST field we care about) as side lemmas. `proof-local-get.lisp`
already shows that cost: the cleanest half of the refinement comes from
the operand-stack write; the ugly half is proving the byte at `pc+1`
*means* the immediate `x` of the `local.get` AST node.

### 4.3 What "on-spec" would have looked like

A spec-driven ATC VM would have had the following layers:

```
.wasm bytes  ── wasm::parse-binary ──►  AST (module with :instrs lists)
                  (ACL2 spec, not ATC-C-exportable; run once per module)

AST instr list  ── spec: execute-<op> over statep ──►  new statep
                  (execution.lisp; the reference semantics)

Mirror in ATC fragment:
   fixed-size struct wst  ≅  projection/abstraction of a restricted statep
   |exec$loop|-style dispatch whose every arm is a syntactic image of an
       execute-<op> call under that projection
   No re-parsing of bytes inside the interpreter — immediates come from
       the AST node in the instrs list.
```

Then for each opcode the refinement theorem is a one-liner: "apply
`execute-<op>` on the spec side, apply the ATC arm on the concrete
side; under the projection they agree." No `uchar-array-read` in the
proof. No `scan_end` byte walker at all — block/loop targets are
carried by the AST, not rediscovered at run time.

### 4.4 What to do about it

Two options, honestly stated:

- **Keep wasm-vm1 and retrofit the proofs.** Finish the support book
  described in §2, prove the read-of-write and byte-bridge lemmas once,
  and grind through `local.set`, `local.tee`, `i32.eqz`, `i32.rem_u`,
  `block`/`loop`/`br`, `end`. Then the final fuel induction. Every
  proof carries the byte-decoding overhead, but we keep the artifact we
  have.

- **Redesign wasm-vm1 as a spec refinement (recommended if scope allows).**
  Put the parser in a separate ACL2-only book that calls
  `wasm::parse-binary` (or, if we need to generate C for a loader, do it
  with a different code-generation tool whose input is the byte-list
  parser). Rewrite `|exec$loop|` as a shallow syntactic image of the
  spec's `execute-<op>` cascade, with immediates coming from the
  current AST instruction rather than from `wasm_buf`. Under this
  rewrite, every opcode arm's refinement theorem is the kind of short
  `:use (:instance execute-<op>-definition)` proof we want, and the
  support book shrinks dramatically.

The call is the user's. This note documents the current state honestly
so the decision is made with eyes open.
