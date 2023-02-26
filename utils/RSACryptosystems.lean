import Mathlib
import Init 



def mod_pow (a : ℕ) (b : ℕ) (n : ℕ) : ℕ :=
  match b with 
  | 0 => 1
  | 1 => a % n
  | b + 2 => 
    if b%2 = 0 then 
    let c := mod_pow a (b+2/2) n
    (c * c) % n
  else 
    (a * (mod_pow a (b + 1) n)) % n
termination_by _ _ => b
decreasing_by      
have h : 1 < 2 := by norm_num
simp 
have h3 : b + 1 < b + 2 := by
  apply Nat.add_lt_add_left
  apply h
simp[Nat.succ_eq_add_one]
apply h3


def inverse (a : ℕ) (b : ℕ)(h : (Nat.gcd a b) = 1) : ℕ := 
  let (x, _) := Nat.xgcd a b
  if x < 0 then 
    Int.toNat (x + b)
  else
    Int.toNat x

structure Public_key : Type where 
  n : ℕ
  e : ℕ
  deriving Repr

structure Key_pair : Type where 
  p : ℕ
  hp : Nat.Prime p
  q : ℕ 
  hq : Nat.Prime q
  ho : p ≠ q
  n := p * q 
  phi := Nat.lcm (p - 1) (q - 1)
  e : ℕ
  he : 2 < e ∧ Nat.gcd e phi = 1
  d := inverse e phi he.right
  Public_key := (n,e)
  Private_key := (n,d)
  deriving Repr

#check Key_pair.Public_key
/- The key generation Function-/
def key_generation1 (p : ℕ) (q : ℕ)(e : ℕ )(hp : Nat.Prime p)(hq : Nat.Prime q)(ho : p ≠ q) : Key_pair := 
  let n := p * q 
  let phi := Nat.lcm (p - 1) (q - 1)
  if p = q then 
    (n,0) 
  else



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