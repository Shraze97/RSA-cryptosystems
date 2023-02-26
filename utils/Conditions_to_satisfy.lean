import Mathlib
import RSACryptosystems



theorem mod_pow_eq :  mod_pow a b n = (a ^ b) % n :=
  by
  by_cases h : n = 0
  · simp[h]
    rw[mod_pow]



theorem fermat_little_theorem (p : ℕ) (hp : Prime p) (a : ℕ) : a ^ (p - 1) % p = 1 :=
  by 
    sorry 

theorem ende : (decryption e n (encryption e n m)) = m :=
  by
  sorry