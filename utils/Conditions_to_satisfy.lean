import Mathlib
import RSACryptosystems

theorem mod_pow_eq :  mod_pow a b n = (a ^ b) % n :=
  by
  rw[mod_pow]
  have h' : n > 1 := by
    sorry
  by_cases h : b = 0
  · simp[h, h', Nat.mod_eq_of_lt]
  · simp[h, h']
    sorry

#check Commute.add_pow
#check Nat.Prime.dvd_choose_self

theorem freshman's_dream (a b : ℕ) (hp : Nat.Prime p) : ((a + b) ^ p) % p = (a ^ p + b ^ p)%p := by
  rw[← Nat.ModEq]
  rw[add_pow]
  rw[Nat.ModEq.comm]
  have h1 : {0, p} ⊆  Finset.range (p + 1) := by 
    rw[Finset.subset_iff]
    simp 
  rw[←Finset.sum_sdiff h1 ]
  have h2 : 0 ≠p := by 
    sorry
  rw[Finset.sum_pair h2] 
  simp 
  rw[Nat.modEq_iff_dvd']
  rw[Nat.sub_add_eq,← Nat.add_assoc]
  simp
  sorry

  

  







theorem fermat_little_theorem (p : ℕ) (hp : Nat.Prime p) (a : ℕ) : a ^ (p - 1) % p = 1 :=
  sorry

theorem ende : (decryption e n (encryption e n m)) = m :=
  by
  sorry
