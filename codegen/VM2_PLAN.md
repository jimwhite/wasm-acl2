# wasm-vm2 — block-structured codegen VM

> Successor to `wasm-vm1.lisp` in this directory. Same ATC pipeline, same
> opcode coverage to start, but execution is **block-structured** rather
> than per-opcode-dispatched.
>
> Status: **planning / Phase 1 in progress** (branch `vm`).

## Why

`wasm-vm1`'s `exec$loop` is a flat opcode dispatcher. Every iteration
decrements `|fuel|` for ACL2 termination; every control-flow op
(`block` / `loop` / `if` / `br`) does a runtime byte-scan
(`scan_end` / `scan_else`) to find its target. Both are hacks:

1. **Per-instruction fuel** is fuel taxed at the wrong granularity. A
   small inner `i32.add` costs the same as a `br`. For the eventual
   Milawa-on-WASM termination proofs we want fuel counted in the
   currency the program *actually* iterates over — basic blocks /
   branches.
2. **Runtime byte-scanning** is not how real engines work. WASM is
   designed with an explicit, statically resolvable block structure
   (matched `block`/`loop`/`if` … `end`, static `br N` depths). V8,
   SpiderMonkey, Wasmtime, wasm3 all extract a CFG once at load time.

`wasm-vm2` does the WASM-spec-blessed thing: parse the function body
into a flat array of basic blocks plus a precomputed branch table at
load time, then execute against that.

## What's in WASM 1.0 that makes this clean

(All from `specification/wasm-1.0`, binary format §5 and execution §4.)

- `block bt … end`, `loop bt … end`, `if bt … else? … end` are bracketed
  with a static `end` (`0x0b`). The validator rejects unbalanced
  bytecode, so a single linear pass over the bytes with an operator
  stack is enough to find every block's start, end, and (if present)
  else.
- `br N` / `br_if N` / `br_table` use **static** label depths resolved
  against the lexical block stack. Targets are decidable at parse time.
- Functions have an explicit body length (LEB128 in the Code section),
  so we know exactly where parsing stops.
- `return` always exits the function.
- Block types (`blocktype`: empty `0x40`, single valtype, or type index)
  are immediate after the opening byte and tell us arity at parse time.

Nothing in the spec is hostile to this design.

## State shape (post-cutover)

Today:
```
|wasm_buf|[65536]       raw bytes
|wmod|                  parsed-module struct (export name, body off+len, num_locals)
|wst|                   exec state (op[64], loc[16], lpc[16], lsp[16], lkind[16])
```

After:
```
|wasm_buf|[65536]       raw bytes (unchanged)
|wmod|                  parsed-module struct (unchanged)
|wcfg|                  control-flow graph (NEW)
|wst|                   exec state — drops lpc/lsp/lkind (label stack now in wcfg / runtime stack of block indices)
```

`|wcfg|` is parallel arrays — ATC handles `(c::uint N)` / `(c::sint N)`
struct fields well, but not arrays-of-structs. Bound: 256 blocks per
function (Milawa's biggest functions are well under this).

```
(c::defstruct |wcfg|
  (|nblocks|   c::sint)             ; how many entries are populated
  (|start_pc|  (c::sint  256))      ; first instruction byte of straight-line body
  (|end_pc|    (c::sint  256))      ; one past last straight-line byte (the ctl-flow op)
  (|kind|      (c::uchar 256))      ; 0=block, 1=loop, 2=if, 3=else, 4=function-top, 5=tail
  (|else_blk|  (c::sint  256))      ; for kind=if: matching else block, or -1
  (|end_blk|   (c::sint  256))      ; block index following the matching `end`
  (|parent|    (c::sint  256)))     ; enclosing block (for static label-depth resolution)
```

Branch resolution: at parse time, every `br N` / `br_if N` we encounter
is rewritten to a direct successor block index by walking `parent` N
times from the current block. We can either (a) bake the resolved
target into a parallel `|br_target|[256]` keyed by branch-instruction
PC, or (b) leave the runtime to walk `parent` (cheap — bounded by the
program's max nesting depth, typically ≤ 20 even for big Milawa funcs).
**Decision: (b) for v2.0**, with `(a)` as a tunable optimisation if
profiling shows it matters. Keeps the CFG simpler.

## The two execution levels

```lisp
;; INNER — straight-line opcodes only.  Measure: BUF-END - pc.  No fuel.
(defun |exec_straight_line| (|st| |sp| |pc| |end_pc| |halted| |wasm_buf|)
  :measure (nfix (- 65536 (c::integer-from-sint |pc|)))
  ...)

;; OUTER — block-level dispatch.  Fuel = remaining block transitions.
(defun |exec_blocks| (|st| |sp| |blk| |halted| |fuel| |wcfg| |wasm_buf|)
  :measure (nfix (c::integer-from-sint |fuel|))
  ;; 1. run straight-line body of current block
  ;; 2. dispatch on the trailing control-flow op
  ;; 3. decrement fuel, recurse with new block index
  ...)
```

Properties:

- **Inner loop has a real structural measure.** Every iteration
  consumes ≥1 byte of bytecode; the buffer is bounded; ATC accepts it
  without fuel.
- **Outer loop's fuel counts block transitions.** A
  10⁶-iteration WASM `loop` block is one `br` per iteration, so it
  costs 10⁶ fuel — but the inner straight-line body of each iteration
  is fuel-free. Total per-step overhead unchanged; semantic clarity
  much better.
- **Per-shape arm templates lose all fuel bookkeeping.** Today every
  arm in `loop.lisp` calls `emit-pc-halted-fuel`; in v2 the
  straight-line arms emit just `pc += size, halted |= ~ok`, no fuel.

## Code we delete

- `|scan$loop|` + `|scan_end|` and their `defrulel`s.
- `|scan_else$loop|` + `|scan_else|` and their `defrulel`s.
- `:if` and `:else` arm emitters' calls to those helpers.
- `entries-have-control-flow-p` — no longer needed; the inner emitter
  is *only* straight-line by construction, the outer is *only*
  control-flow.
- The "is_wide" opcode list; immediates are baked into the CFG.

About 250–300 lines of ATC ceremony go away.

## Phase plan

Each phase is independently committable with all 8 oracle fixtures
still green.

### Phase 1 — Add `extract_cfg` to wasm-vm2 (CFG as a side product)

- New file: `codegen/wasm-vm2.lisp`. Initially a copy of
  `wasm-vm1.lisp` with `|wcfg|` defstruct + `|extract_cfg$loop|` /
  `|extract_cfg|` added.
- `extract_cfg` walks the function body once, populates `|wcfg|`.
  Uses a parser-stack approach: open-brackets push a half-built block;
  the matching `end` pops and finalises; `else` finalises an `if`
  block and opens an `else` sibling.
- Recursion measure: `(nfix (- BUF-END pc))`. **No fuel argument.**
- Register the helper with `c::atc`. Don't yet wire it into execution
  — we just want the call to succeed and produce a sensible CFG for
  the existing 4 oracle fixtures.
- Add a sanity dump in `run_main.c` (`--dump-cfg` flag) for visual
  verification on `gcd.wasm` / `factorial.wasm` / `is_prime.wasm` /
  `collatz.wasm`.

**Exit criteria**: `make codegen-run` still passes 8/8 (extract_cfg
called but result ignored); `--dump-cfg` produces sensible output.

### Phase 2 — `exec_straight_line` + `exec_blocks` (parallel to wasm-vm1's loop)

- New emitter file alongside `loop.lisp`: `loop-blocks.lisp` with
  `emit-arm-straight-line` (no fuel) and `gen-exec-blocks` (outer
  dispatcher). Or — likely cleaner — split `loop.lisp` itself into
  two emitter functions and pick which one based on a flag.
- New defuns: `|exec_straight_line|` (pc-advance measure) and
  `|exec_blocks|` (block fuel measure). Both ATC-targeted.
- Don't yet replace the existing `exec_loop_gen` — call the new pair
  from a separate entry point `|run_wasm_v2|` in
  `integration-demo.lisp` (or a new `integration-demo-v2.lisp`),
  selected by a `--vm v2` CLI flag.
- Run the 8 oracle fixtures through *both* paths and diff.

**Exit criteria**: `run_demo --vm v2` produces identical output on
all 8 fixtures.

### Phase 3 — Cutover, delete fuel from arms

- Replace `run_wasm_gen` with the v2 path. Delete `scan_end` /
  `scan_else` / `scan$loop` / `scan_else$loop` and their lemmas.
- Remove fuel decrement from every straight-line arm in `loop.lisp`
  (the new straight-line emitter is fuel-free by construction; the
  old emitter goes away with `exec_loop_gen`).
- Update gotchas list in `README.md`. Several entries (#16, #17, #18
  about `scan_else$loop` and `is_wide`) become historical.

**Exit criteria**: Single execution path. 8/8 fixtures green. Generated
C is shorter and contains no fuel decrement in straight-line arms.

### Phase 4 (optional) — LEB128 immediates baked at parse time

- During `extract_cfg`, also fully decode every `i32.const` /
  `local.get|set|tee` / `br` / `br_if` immediate into a parallel
  `|imm|[N]` array indexed by instruction PC (or use a sparse map keyed
  by PC).
- Drop the "≤63 single-byte immediate" simplification on `:i32-const`
  and the 16-local cap on `:local-idx-*`. Necessary for Milawa, which
  has plenty of constants ≥ 128.

**Exit criteria**: A new fixture with constants > 127 runs correctly
through v2.

## Open design questions

1. **Branch resolution: lazy parent-walk vs. precomputed `br_target`?**
   Currently leaning lazy. Reconsider after Phase 3 if profiling on
   Milawa shows nesting-depth × branch-count is meaningful.
2. **`br_table`** has a vector of label depths. Storing this needs
   either a separate `br_table_targets[256][16]` array (most-direct,
   16 = depth limit) or a flat indirect `br_table_starts[256]` +
   `br_table_pool[2048]`. Punt until we have a real `br_table` use case
   — Milawa probably won't generate one.
3. **Function-local block index space, or global?** A function compiles
   to its own `|wcfg|` slice. Single-function programs (everything we
   have today) → flat. Multi-function (call) → either reuse the same
   `|wcfg|` per-call (rebuild) or maintain a global `|wcfg|` keyed by
   function index. **Defer to wasm-vm3 / call support.**

## What stays the same

- `state-model.lisp`'s `|wst|` shape — still op[64], loc[16].
  (Phase 3 *removes* lpc/lsp/lkind because the label stack moves into
  the block dispatcher's recursion structure, but the state defstruct
  stays in `state-model.lisp`.)
- `templates.lisp` (the standalone step-function emitters) is
  unchanged.
- ATC pipeline, packaging, `cert.acl2`, Makefile target structure.

## Glossary

- **CFG (control-flow graph)**: the static block decomposition of a
  function body. For our purposes, the parallel-array `|wcfg|`
  contents.
- **Straight-line block**: a maximal run of opcodes that does not open
  or close a block and does not branch. Ends when we hit one of:
  `block`, `loop`, `if`, `else`, `end`, `br`, `br_if`, `br_table`,
  `return`, or end-of-function.
- **Block transition**: one tick of the outer dispatcher. Costs one
  fuel.
