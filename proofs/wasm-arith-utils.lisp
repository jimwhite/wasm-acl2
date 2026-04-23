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

(value-triple (cw "wasm-arith-utils: loaded.~%"))
