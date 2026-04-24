// One-shot oracle invoker: loads a .wasm, calls a named export with numeric
// args, prints the result as a decimal integer on stdout.
//
// Usage: node oracle-invoke.mjs FILE.wasm EXPORT_NAME ARG...

import { readFileSync } from 'fs';

const [,, wasmPath, exportName, ...args] = process.argv;
if (!wasmPath || !exportName) {
  console.error('usage: oracle-invoke.mjs FILE.wasm EXPORT_NAME ARG...');
  process.exit(2);
}

const bytes = readFileSync(wasmPath);
const { instance } = await WebAssembly.instantiate(bytes);
const fn = instance.exports[exportName];
if (typeof fn !== 'function') {
  console.error(`oracle: export ${exportName} not found`);
  process.exit(1);
}
const numArgs = args.map(a => {
  const n = Number(a);
  if (!Number.isFinite(n)) { throw new Error(`bad arg: ${a}`); }
  return n;
});
const r = fn(...numArgs);
// Match our C driver's %u format: unsigned 32-bit decimal.
const u32 = r >>> 0;
console.log(u32.toString());
