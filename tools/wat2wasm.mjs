#!/usr/bin/env node
// Minimal wat2wasm replacement using the `wabt` npm package.
// Usage: wat2wasm.mjs <input.wat> -o <output.wasm>
import { readFileSync, writeFileSync } from 'node:fs';
import wabtInit from 'wabt';

const args = process.argv.slice(2);
let input = null, output = null;
for (let i = 0; i < args.length; i++) {
  if (args[i] === '-o') { output = args[++i]; }
  else if (!input) { input = args[i]; }
}
if (!input || !output) {
  console.error('usage: wat2wasm.mjs <input.wat> -o <output.wasm>');
  process.exit(2);
}
const wabt = await wabtInit();
const src = readFileSync(input, 'utf8');
const mod = wabt.parseWat(input, src, {});
const { buffer } = mod.toBinary({ log: false, write_debug_names: false });
writeFileSync(output, Buffer.from(buffer));
mod.destroy();
