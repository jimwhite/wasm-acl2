;; Shared arithmetic utilities for WASM correctness proofs.
;;
;; Bridges between WASM-level operations (i32 bitvector arithmetic) and
;; the mathematical specs used by community books (plain integer `mod`,
;; `nonneg-int-gcd`, etc.).
;;
;; Keeping arithmetic-5 `local` prevents it from destabilizing symbolic
;; execution proofs downstream.

(in-package "WASM")
(include-book "../execution")
(include-book "arithmetic/mod-gcd" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system)
(include-book "kestrel/bv/bvmult" :dir :system)
(include-book "kestrel/bv/bvminus" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; u32 / mod bridge

(defthm u32p-of-mod
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b))
           (unsigned-byte-p 32 (mod a b)))
  :hints (("Goal" :cases ((equal b 0)))))

(defthm bvmod-32-when-u32
  ;; i32.rem_u on u32 inputs with nonzero divisor is plain integer mod.
  (implies (and (unsigned-byte-p 32 a)
                (unsigned-byte-p 32 b)
                (not (equal b 0)))
           (equal (acl2::bvmod 32 a b) (mod a b)))
  :hints (("Goal" :in-theory (enable acl2::bvmod))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; nfix / nonneg-int-mod / nonneg-int-gcd utility rewrites

(defthm nfix-when-natp
  (implies (natp x) (equal (nfix x) x)))

(defthm nonneg-int-mod-is-mod
  (implies (and (natp a) (posp b))
           (equal (acl2::nonneg-int-mod a b) (mod a b)))
  :hints (("Goal" :in-theory (enable acl2::nonneg-int-mod mod floor))))

(defthm nonneg-int-gcd-of-0-right
  (equal (acl2::nonneg-int-gcd x 0) (nfix x))
  :hints (("Goal" :expand ((acl2::nonneg-int-gcd x 0)))))

(defthm nonneg-int-gcd-of-0-left
  (equal (acl2::nonneg-int-gcd 0 x) (nfix x))
  :hints (("Goal" :expand ((acl2::nonneg-int-gcd 0 x))
                  :in-theory (enable acl2::nonneg-int-mod))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; bvminus / bvmult bridges for small-constant cases used by loop
;; counters and i32 multiplication of u32 accumulators.

(defthm bvminus-32-of-u32-and-1
  ;; i32.sub on a non-zero u32 and the constant 1 is plain subtraction.
  (implies (and (unsigned-byte-p 32 n)
                (not (equal n 0)))
           (equal (acl2::bvminus 32 n 1) (- n 1)))
  :hints (("Goal" :in-theory (enable acl2::bvminus acl2::bvchop))))

(defthm u32p-of-bvmult-32
  (unsigned-byte-p 32 (acl2::bvmult 32 a b))
  :rule-classes (:rewrite :type-prescription))

(defthm u32p-of-bvminus-32
  (unsigned-byte-p 32 (acl2::bvminus 32 a b))
  :rule-classes (:rewrite :type-prescription))

(defthm bvmult-32-of-1
  ;; i32.mul by the constant 1 is the identity on u32.
  (implies (unsigned-byte-p 32 a)
           (equal (acl2::bvmult 32 1 a) a))
  :hints (("Goal" :in-theory (enable acl2::bvmult acl2::bvchop))))

(defthm bvmult-32-of-1-left
  (implies (unsigned-byte-p 32 a)
           (equal (acl2::bvmult 32 a 1) a))
  :hints (("Goal" :in-theory (enable acl2::bvmult acl2::bvchop))))

(value-triple (cw "wasm-arith-utils: loaded.~%"))
