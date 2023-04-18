import Mathlib
import RSACryptosystems

/-
theorem mod_pow_eq (pos: n ≠ 1): mod_pow a b n = (a ^ b) % n := by
  rw[mod_pow]
  split_ifs
  · rename_i h1
    rw[h1]
    simp 
    have h2 : 1 % n = 1 := by
      cases n
      · simp 
      · rename_i k 
        simp 
        rw[← Nat.add_one k]
        have h2 : k ≠ 0 := by
          intro h3 
          have h4 : Nat.succ k = 1 := by
            rw[h3]
          contradiction 
        simp 
        have h4 : (k = 0 ∨ 0 < k) := by
          apply Nat.eq_zero_or_pos k
        cases h4 
        · rename_i left 
          rw[left] at h2 
          contradiction
        · rename_i right
          assumption
    simp[h2] 
  · rename_i h1 h2
    rw[h2]
    simp
  · rename_i h1 h2 h3
    simp 
    induction b
    · simp 
      rw[mod_pow]
      simp 
    · rename_i k base 
      rw[← Nat.add_one k]   

  · rename_i h1 h2 h3    

  sorry
-/

theorem mod_pow_eq' (pos: n ≠ 1)(a : ℕ ) (b : ℕ) (n : ℕ): mod_pow a b n hneq = (a ^ b) % n := by
  rw[mod_pow]
  split_ifs
  · rename_i k h1

    



theorem freshman's_dream (a b : ℕ) (hp : Nat.Prime p) : ((a + b) ^ p) % p = (a ^ p + b ^ p) % p := by
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
  rw[Nat.add_comm (a ^ p) (b ^ p)]
  nth_rewrite 1[← Nat.add_zero (b ^ p + a ^ p)] 
  rw[Nat.add_comm] 
  apply Nat.ModEq.add_right 
  apply Nat.ModEq.symm 
  rw[Nat.modEq_zero_iff_dvd]
  apply Finset.dvd_sum 
  intro i hi 
  rw[← Nat.modEq_zero_iff_dvd] 
  have h3 : Nat.choose p i ≡ 0 [MOD p]:= by
    rw[Nat.modEq_zero_iff_dvd] 
    apply Nat.Prime.dvd_choose_self hp
    intro h4
    rw[h4] at hi 
    simp at hi 
    simp[Finset.range] at hi 
    cases hi 
    rename_i left right 
    cases left 
    · rename_i left'
      rw[left'] at right
      simp at right
    · rename_i right' 
      assumption
  apply Nat.ModEq.mul_left (a ^ i * b ^ (p - i)) h3


theorem fermat_little_theorem' (p : ℕ) (hp : Nat.Prime p) (a : ℕ) : a ^ p ≡ a [MOD p] := by
  induction a 
  · simp 
    have h1 : 0 ^ p = 0 := by
      simp
      have h2 : p ≠ 0 := by 
        intro h3 
        apply Nat.Prime.ne_zero hp
        rw[h3] 
      have h4 : (p = 0 ∨ 0 < p) := by
        apply Nat.eq_zero_or_pos p  
      cases h4 
      · rename_i left 
        rw[left] at h2 
        contradiction
      · rename_i right
        assumption
    simp[h1]
    trivial 
  · rename_i k base
    rw[← Nat.add_one k]
    have h1 : (k + 1) ^ p ≡ k ^ p + 1 ^ p [MOD p] := by
      apply freshman's_dream
      assumption
    have h2 : k ^ p + 1 ^ p ≡ k ^ p + 1 [MOD p] := by
      simp
      trivial 
    have h3 : (k + 1) ^ p ≡ k ^ p + 1 [MOD p] := by
      apply Nat.ModEq.trans h1 h2
    have h4 : k ^ p + 1 ≡ k + 1 [MOD p] := by
       apply Nat.ModEq.add_right _ base
    apply Nat.ModEq.trans h3 h4  

  theorem fermat_little_theorem (p : ℕ) (hp : Nat.Prime p) (a : ℕ)(hpneqn : ¬(p ∣ a)) : a ^ (p - 1) % p = 1 := by
  rw[← Nat.Prime.coprime_iff_not_dvd hp] at hpneqn
  rw[Nat.coprime_iff_gcd_eq_one] at hpneqn
  have h1 : a ^ p ≡ a [MOD p] := fermat_little_theorem' p hp a
  have lem : a * a ^ (p - 1) ≡ a * 1 [MOD p] := by
    have h' : a = a * 1 := by
      simp
    rw[← h']
    have h'' : a ^ p = a * a ^ (p - 1) := by
      have h''' : p - 1 + 1 = p := by
        apply Nat.sub_add_cancel hp.pos
      rw[add_comm] at h'''
      nth_rewrite 1[← h'''] 
      rw[pow_add]
      simp
    rw[← h'']
    assumption  
  have h3 : a ^ (p - 1) ≡ 1 [MOD p] :=  Nat.ModEq.cancel_left_of_coprime hpneqn lem
  have h4 : a ^ (p - 1) % p = 1 % p := by
    rw[h3]
  have h5 : 1 % p = 1 := by
    have h6 : (p > 1) := by
      apply Nat.Prime.one_lt hp
    apply Nat.mod_eq_of_lt h6 
  rw[h5] at h4  
  assumption

theorem ende (h : n ≠ 1): (decryption e n (encryption e n m)) = m := by
  rw[decryption]
  rw[encryption]
  rw[mod_pow_eq]
  rw[mod_pow_eq]
  sorry

#check Commute.add_pow
#check Nat.Prime.ne_zero
#check Nat.Prime.dvd_choose_self
#check Nat.ModEq.add_right_cancel
#check Finset.mem_range
#check Nat.eq_zero_or_pos
#check pow_add
