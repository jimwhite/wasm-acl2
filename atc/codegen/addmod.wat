(module
  ;; Straight-line: uses only the 8 opcodes the generated loop handles:
  ;;   local.get (0x20), local.set (0x21), local.tee (0x22),
  ;;   drop (0x1a), i32.const (0x41), i32.add (0x6a),
  ;;   i32.rem_u (0x70), end (0x0b).
  ;; NOTE: the generated :i32-const arm reads a 1-byte immediate (simplified
  ;; LEB128).  Use a constant <= 63 so the signed-LEB encoding is one byte.
  (func $addmod (export "addmod") (param $a i32) (param $b i32) (result i32)
    ;; (a + b) % 50
    (i32.rem_u
      (i32.add (local.get $a) (local.get $b))
      (i32.const 50))))
