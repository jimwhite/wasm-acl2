;; tests/oracle/factorial.wat
;;
;; Iterative 32-bit unsigned factorial: $acc *= $n; $n--; until $n == 0.
;; Structurally modeled on `fac-iter-named` from the WebAssembly spec
;; test `test/core/fac.wast`, but at i32 (not i64) so that it reuses the
;; same bitvector bridge lemmas as `gcd.wat`.
;;
;; Overflow note: i32.mul wraps at 2^32, so the result equals the
;; mathematical factorial only for n <= 12 (since 13! > 2^32).  The
;; body-level correctness theorem in `proofs/proof-factorial-spec.lisp`
;; is stated with a `bvmult 32`-wrapped spec that holds for *all* u32 n;
;; a bounded corollary re-states it against the unbounded `fact` for
;; n <= 12.

(module
  (func $fac (export "fac") (param $n i32) (result i32)
    (local $acc i32)
    (local.set $acc (i32.const 1))
    (block $exit
      (loop $loop
        (br_if $exit (i32.eqz (local.get $n)))
        (local.set $acc (i32.mul (local.get $acc) (local.get $n)))
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        (br $loop)))
    (local.get $acc)))
