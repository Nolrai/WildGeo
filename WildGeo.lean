import Mathlib.Data.Nat.Gcd
import Mathlib.Algebra.Ring.Basic

def hello := "world"

instance [CommSemiring R] : Dvd R where
  dvd := λ x y => ∃ z, x * z = y

class IntegralSemidomain (R : Type u) extends CommSemiring R where
  no_zero_dvd : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0

lemma no_zero_dvd [inst : IntegralSemidomain R] {a b : R} : a * b = 0 → a = 0 ∨ b = 0 := 
  inst.no_zero_dvd a b

class IntegralDomain (R : Type u) extends IntegralSemidomain R, CommRing R

lemma non_zero_cancel [IntegralDomain R] : ∀ a b c : R, a ≠ 0 → a * b = a * c → b = c :=
  by
  intros a b c a_nonzero ab_ac
  have h : a * b + -(a * c) = 0 :=
    by
    rw [ab_ac, add_neg_self (a * c)]
  rw [mul_comm _ c, neg_mul_eq_neg_mul, mul_comm (-c), ← left_distrib] at h
  apply add_right_cancel
  rw [add_neg_self c]
  have h' := no_zero_dvd h
  cases h'
  case a.inl a_zero => exact (a_nonzero a_zero).elim
  case a.inr g => exact g

class GCD_Domain (R : Type u) extends IntegralSemidomain R : Type (u + 1) where
  gcd : R → R → R
  gcd_dvd : ∀ (m n : R), (gcd m n ∣ m) ∧ (gcd m n ∣ n)
  dvd_gcd : ∀ (m n k : R), (k ∣ m) → (k ∣ n) → k ∣ gcd m n

def gcdOfList := 

section defs

variable {R : Type u} [Semiring R]

structure VArr (n : ℕ) (α : Type u) where
  arr : Array α
  sized : arr.size = n

def VArr.get : VArr n α → Fin n → α 
  | {arr := arr, sized := sized} => 
  λ fin => arr.get $ (congr_arg Fin sized).mpr fin

class SMul (Scalar : Type u) (Carrier : Type v) where
  smul : Scalar → Carrier → Carrier

infixr:70 " • " => SMul.smul

class MulAction (Scalar : Type u) (Carrier : Type v) 
  extends Monoid Scalar, SMul Scalar Carrier where
  
  one_smul : ∀ x : Carrier, (1 : Scalar) • x = x
  mul_smul : ∀ r s : Scalar, ∀ x : Carrier, (r * s) • x = r • (s • x)

class DistribMulAction (Scalar : Type u) (Carrier : Type v) 
  extends MulAction Scalar Carrier, AddMonoid Carrier where
  
  smul_add : ∀ (r : Scalar) (x y : Carrier), r • (x + y) = r • x + r • y
  smul_zero : ∀ r : Scalar, r • (0 : Carrier) = 0

class Module (Scalar : Type u) (Vector : Type v)
  extends DistribMulAction Scalar Vector where
  toSemiring : Semiring Scalar
  one_ne_zero : (1 : Scalar) ≠ 0
  add_smul : ∀ (r s : Scalar) (x : Vector), (r + s) • x = r • x + s • x
  zero_smul : ∀ x : Vector, (0 : Scalar ) • x = 0
  mul_comm : ∀ r s : Scalar, r * s = s * r

instance [Module Scalar Vector] : Dvd Vector where
  dvd := λ x y => ∃ (s : Scalar), s • x = y

theorem dvd_trans 
  [Module Scalar Vector] (x y z : Vector) : 
    x ∣ y → y ∣ z → x ∣ z
  | ⟨sxy, xy⟩, ⟨syz, yz⟩ => ⟨syz * sxy, 
    by
    rw [MulAction.mul_smul, xy, yz] 
    ⟩

def NonZero (α : Type u) [Zero α] := Subtype (λ x : α => x ≠ 0)

