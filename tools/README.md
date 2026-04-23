# tools/

Host-side helpers (not part of the ACL2 model).

## `wat2wasm.mjs`

A minimal stand-in for `wabt`'s `wat2wasm` binary, implemented on top
of the [`wabt` npm package](https://www.npmjs.com/package/wabt) (pure
JavaScript port). Use when the system does not provide a native
`wat2wasm` (e.g., this devcontainer's package repos do not ship wabt).

### Setup (once)

```
cd tools && npm install
```

### Usage

```
node tools/wat2wasm.mjs tests/oracle/gcd.wat -o tests/oracle/gcd.wasm
```

The top-level `Makefile` provides a pattern rule:

```
make wasm                        # compile every tests/oracle/*.wat
make tests/oracle/gcd.wasm       # compile a specific one
```

## Why not native `wat2wasm`?

If `wat2wasm` (from [WABT](https://github.com/WebAssembly/wabt)) is on
the PATH, prefer that — it's faster and is the reference implementation.
Swap the `Makefile` rule to `wat2wasm $< -o $@` in that case. The JS
port is bundled here only so the .wat → .wasm step has zero external
dependencies in this workspace.
