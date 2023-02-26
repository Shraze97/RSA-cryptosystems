import Mathlib
import Init 



def mod_pow (a : ℕ) (b : ℕ) (n : ℕ) : ℕ :=
  if n = 0 then 0 
  else
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

structure Public_key  where 
  mk :: (n : ℕ) (e : ℕ)
  deriving Repr
#check Public_key 
structure Key_pair extends Public_key where
  p : ℕ
  hp : Nat.Prime p
  q : ℕ 
  hq : Nat.Prime q
  ho : p ≠ q
  hn : n = p * q
  he : 2 < e ∧ Nat.gcd e (Nat.lcm (p - 1) (q - 1)) = 1
  deriving Repr

/- The key generation Function-/
def value_d(a : Key_pair) : ℕ   :=
  let d := inverse a.e (Nat.lcm (a.p - 1) (a.q - 1)) a.he.right
  d

structure Private_key extends Key_pair where
  d : ℕ
  hd : d = (value_d toKey_pair)
  deriving Repr

def key_generation  (a : Key_pair) : Private_key := 
  let d := (value_d a)
  have h : d = (value_d a) := rfl
  Private_key.mk a d h

#check Key_pair

/- The encryption Function-/
def encryption (a : Public_key) (m : ℕ) : ℕ := 
  mod_pow m a.e a.n


/- The decryption Function-/
def decryption (b : Private_key)(me : ℕ) : ℕ := 
  mod_pow me b.d b.n



