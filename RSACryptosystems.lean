import Mathlib
import Init 



def mod_pow (a : ℕ) (b : ℕ) (n : ℕ) : ℕ :=
  if b = 0 then 
    1
  else
  if b = 1 then 
    a % n
  else 
  if b%2 = 0 then 
    let c := mod_pow a (b/2) n
    (c * c) % n
  else 
    (a * mod_pow a (b - 1) n) % n
termination_by _ _ => b
decreasing_by 
have h : 1 < 2 := by norm_num
have h1 : ¬ (b =0) := by assumption    
have h3 : b -1 < b := by 
  apply Nat.sub_lt_of_pos_le
  apply Nat.zero_lt_of_ne_zero
  simp
  rw[Nat.one_le_iff_ne_zero]
  assumption;
try simp
try apply Nat.div_lt_self 
try apply Nat.zero_lt_of_ne_zero
assumption
try apply h 

  
def inverse (a : ℕ) (b : ℕ) : ℕ := 
  let (x, _) := Nat.xgcd a b
  if x < 0 then 
    Int.toNat (x + b)
  else
    Int.toNat x

/- The key generation Function-/
def key_generation (p : ℕ) (q : ℕ)(e : ℕ ) : ℕ ×  ℕ  := 
  let n := p * q 
  let phi := Nat.lcm (p - 1) (q - 1)
  if p = q then 
    (n,0) 
  else
  let r := e % phi 
  if Nat.gcd r phi = 1 then
    let d  :=  inverse r phi
    if  r > 2  then 
      (n,d)
    else 
      (n,0)
  else
    (n,0)

/- The decryption Function-/
def decryption (d : ℕ) (n : ℕ) (me : ℕ) : ℕ := 
  mod_pow me d n


/- The encryption Function-/
def encryption (e : ℕ)(n : ℕ) (m : ℕ) : ℕ := 
  mod_pow m e n