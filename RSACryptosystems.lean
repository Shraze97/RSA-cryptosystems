import Mathlib
import Init 




def inverse (a : ℕ) (b : ℕ) : ℕ := 
  let (x, _) := Nat.xgcd a b
  if x < 0 then 
    Int.toNat (x + b)
  else
    Int.toNat x

/- The key generation Function-/
def key_generation (p : ℕ) (q : ℕ)(e : ℕ ) : ℕ  := 
  let n := p * q 
  let phi := Nat.lcm (p - 1) (q - 1)
  if p = q then 
    0
  else
  if Nat.gcd e phi = 1 then
    let d  :=  inverse e phi
    if e < n ∧ e > 2  then 
      d
    else 
      d
  else
    0
#check fermat_little_theorem
/- The decryption Function-/
def decryption (p : ℕ) (q : ℕ) (c : ℕ) : ℕ := sorry
/- The encryption Function-/
def encryption (p : ℕ) (m : ℕ) : ℕ := sorry