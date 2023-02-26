import Mathlib
import RSAcryptosystems


theorem mod_pow_eq :  mod_pow a b n = (a ^ b) % n :=
  by
  rw[mod_pow]
  have h' : n > 1 := by
    sorry
  by_cases h : b = 0
  · simp[h, h', Nat.mod_eq_of_lt]
  · simp[h, h']
    sorry

--#check Nat.Finset.BigOperators.Commute.add_pow
theorem freshman's_dream (a b : ℕ) (hp : Prime p) : (a + b) ^ p = a ^ p + b ^ p :=
  by 
  sorry


theorem fermat_little_theorem (p : ℕ) (hp : Prime p) (a : ℕ) : a ^ (p - 1) % p = 1 :=
  sorry


theorem ende : (decryption e n (encryption e n m)) = m :=
  by
  sorry
