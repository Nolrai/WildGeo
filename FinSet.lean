import Mathlib.Data.List.Perm
import Mathlib.Algebra.Group.Defs
import Std.Data.RBTree

def ListMultiset α [s : Setoid (List α)] := Quotient (s : Setoid (List α))

def List.toListMultiset (l : List α) : ListMultiset α := Quotient.mk _ l

def ListMultiset.nil {α} : ListMultiset α := [].toListMultiset

def ListMultiset.cons {α} : α → ListMultiset α → ListMultiset α
  | x, xs => Quotient.liftOn xs (List.toListMultiset ∘ List.cons x) $
    by
    intros a b a_eqv_b
    simp [Function.comp]
    apply Quotient.sound
    constructor
    assumption

def ListMultiset.mem {α} : α → ListMultiset α → Prop
  | x, xs => Quotient.liftOn xs (λ xs' => x ∈ xs') $
    by
    intros a b a_eqv_b
    simp
    apply Iff.intro
    all_goals apply List.Perm.subset
    apply a_eqv_b
    apply a_eqv_b.symm

def ListMultiset.subset (l₁ l₂ : List α) : Prop := ∀ x, x ∈ l₁ → x ∈ l₂

def ListMultiset.sum [CommMonoid α] : ListMultiset α → α :=
  Quotient.lift (λ l => l.foldr (λ a b => a * b) 1) $
    by
    intros a b a_eqv_b
    simp
    induction a_eqv_b
    case nil => rw []
    case cons x l₁ l₂ l₁l₂ ih =>
      simp [List.foldr, ih]
    case swap x y l =>
      simp [List.foldr, ← mul_assoc]
      apply congr_arg2
      apply mul_comm
      rfl
    case trans l₁ l₂ l₃ l₁l₂ l₂l₃ ih₁₂ ih₂₃ => rw [ih₁₂, ih₂₃]

def ListMultiset.foldr {α β} (f : α → β → β) (z : β) (f_comm : ∀ (x y : α) (c : β), 
  f x (f y c) = f y (f x c)) : ListMultiset α → β :=
  Quotient.lift (λ (l : List α) => l.foldr f z) $
    by
    intros a b a_eqv_b
    simp
    induction a_eqv_b
    case nil => rfl
    case cons x l₁ l₂ l₁l₂ ih =>
      simp [List.foldr, ih]
    case swap x y l =>
      simp [List.foldr, ← f_comm]
    case trans l₁ l₂ l₃ l₁l₂ l₂l₃ ih₁₂ ih₂₃ => rw [ih₁₂, ih₂₃]
