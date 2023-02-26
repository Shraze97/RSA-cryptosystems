import Mathlib
import RSAcryptosystems


theorem mod_pow_eq :  mod_pow a b n = (a ^ b) % n :=
  by
  rw[mod_pow]
  by_cases h : b = 0 
  · simp[h]
    
  · simp[mod_pow_aux_eq h]


theorem fermat_little_theorem (p : ℕ) (hp : Prime p) (a : ℕ) : a ^ (p - 1) % p = 1 :=
  by 
    sorry 

theorem ende : (decryption e n (encryption e n m)) = m :=
  by
  sorry