import Mathlib.Data.Nat.Gcd
import Mathlib.Algebra.Ring.Basic

def hello := "world"

instance [CommSemiring R] : Dvd R where
  dvd := λ x y => ∃ z, x * z = y

class IntegralDomain (R : Type u) extends CommRing R where
  no_zero_dvd : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0

lemma non_zero_cancel [IntegralDomain R] : ∀ a b c : R, a ≠ 0 → a * b = a * c → b = c :=
  by
  intros a b c a_nonzero ab_ac
  have h : a * b + (a * - c) = 0 :=
    by
    rw [ab_ac, mul_comm _ (-c), ← neg_mul_eq_neg_mul, add_neg_self (a * c)]
  rw [← left_distrib] at h
     


class GCD_Domain (R : Type u) extends CommSemiring R : Type (u + 1) where
  gcd : R → R → R
  gcd_dvd : ∀ (m n : R), (gcd m n ∣ m) ∧ (gcd m n ∣ n)
  dvd_gcd : ∀ (m n k : R), (k ∣ m) → (k ∣ n) → k ∣ gcd m n

section defs

variable {R : Type u} [Semiring R]

instance 