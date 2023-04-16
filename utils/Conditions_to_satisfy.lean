import Mathlib
import RSACryptosystems

theorem mod_pow_eq :  mod_pow a b n = (a ^ b) % n :=
  by
  rw[mod_pow]
  have h' : n > 0 := by

    sorry
  by_cases h : b = 0
  · simp[h, h', Nat.mod_eq_of_lt]
  · simp[h, h']
    sorry

#check Commute.add_pow
#check Nat.Prime.dvd_choose_self

/-
theorem freshman's_dream (a b : ℕ) (hp : Nat.Prime p) : ((a + b) ^ p) % p = (a ^ p + b ^ p)%p := by
  rw[← Nat.ModEq]
  rw[add_pow]
  rw[Nat.ModEq.comm]
  have h1 : {0, p} ⊆  Finset.range (p + 1) := by 
    rw[Finset.subset_iff]
    simp 
  rw[←Finset.sum_sdiff h1]
  have h2 : 0 ≠ p := by 
    intro h3 
    apply Nat.Prime.ne_zero hp
    rw[h3] 
  rw[Finset.sum_pair h2] 
  simp 
  rw[Nat.modEq_iff_dvd']
  rw[Nat.sub_add_eq,← Nat.add_assoc]
  simp[Nat.add_le_add_left] 
  rw[Nat.add_comm] 
  linarith 
  sorry  
-/

theorem freshman's_dream' (a b : ℕ) (hp : Nat.Prime p) : ((a + b) ^ p) % p = (a ^ p + b ^ p)%p := by
  rw[← Nat.ModEq]
  rw[add_pow]
  rw[Nat.ModEq.comm]
  have h1 : {0, p} ⊆  Finset.range (p + 1) := by 
    rw[Finset.subset_iff]
    simp 
  rw[←Finset.sum_sdiff h1]
  have h2 : 0 ≠ p := by 
    intro h3 
    apply Nat.Prime.ne_zero hp
    rw[h3] 
  rw[Finset.sum_pair h2] 
  simp
  have h3 : (a ^ p) ≡ (a ^ p) [MOD p] := by
    rw[Nat.ModEq] 
  have h4 : (b ^ p) ≡ (b ^ p) [MOD p] := by
    rw[Nat.ModEq] 
  rw[Nat.add_comm (a ^ p) (b ^ p)]  
  apply Nat.ModEq.add_right_cancel h3
  apply Nat.ModEq.add_right_cancel h4
  sorry

theorem fermat_little_theorem (p : ℕ) (hp : Nat.Prime p) (a : ℕ) : a ^ (p - 1) % p = 1 := by
  
  sorry

theorem ende : (decryption e n (encryption e n m)) = m := by
  rw[decryption]
  rw[encryption]
  rw[mod_pow_eq]
  rw[mod_pow_eq]
  sorry

#check Nat.Prime.ne_zero
#check Nat.Prime.dvd_choose_self
