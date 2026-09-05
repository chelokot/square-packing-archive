import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace SquarePackingArchive

structure QuadraticNumber (radicand : ℕ) where
  rational : ℚ
  radical : ℚ
deriving DecidableEq, Repr

namespace QuadraticNumber

variable {radicand : ℕ}

noncomputable def toReal (number : QuadraticNumber radicand) : ℝ :=
  number.rational + number.radical * Real.sqrt radicand

def ofRat (rational : ℚ) : QuadraticNumber radicand := ⟨rational, 0⟩

def add (left right : QuadraticNumber radicand) : QuadraticNumber radicand :=
  ⟨left.rational + right.rational, left.radical + right.radical⟩

def neg (number : QuadraticNumber radicand) : QuadraticNumber radicand :=
  ⟨-number.rational, -number.radical⟩

def sub (left right : QuadraticNumber radicand) : QuadraticNumber radicand :=
  left.add right.neg

def mul (left right : QuadraticNumber radicand) : QuadraticNumber radicand :=
  ⟨left.rational * right.rational + radicand * left.radical * right.radical,
    left.rational * right.radical + left.radical * right.rational⟩

def half (number : QuadraticNumber radicand) : QuadraticNumber radicand :=
  ⟨number.rational / 2, number.radical / 2⟩

def Nonnegative (number : QuadraticNumber radicand) : Prop :=
  if 0 ≤ number.radical then
    0 ≤ number.rational ∨ number.rational ^ 2 ≤ radicand * number.radical ^ 2
  else
    0 ≤ number.rational ∧ radicand * number.radical ^ 2 ≤ number.rational ^ 2

instance (number : QuadraticNumber radicand) : Decidable number.Nonnegative := by
  unfold Nonnegative
  infer_instance

def Le (left right : QuadraticNumber radicand) : Prop :=
  (right.sub left).Nonnegative

instance (left right : QuadraticNumber radicand) : Decidable (left.Le right) := by
  unfold Le
  infer_instance

def abs (number : QuadraticNumber radicand) : QuadraticNumber radicand :=
  if number.Nonnegative then number else number.neg

@[simp] theorem ofRat_toReal (rational : ℚ) :
    (ofRat rational : QuadraticNumber radicand).toReal = rational := by
  simp [ofRat, toReal]

@[simp] theorem add_toReal (left right : QuadraticNumber radicand) :
    (left.add right).toReal = left.toReal + right.toReal := by
  simp [add, toReal]
  ring

@[simp] theorem neg_toReal (number : QuadraticNumber radicand) :
    number.neg.toReal = -number.toReal := by
  simp [neg, toReal]
  ring

@[simp] theorem sub_toReal (left right : QuadraticNumber radicand) :
    (left.sub right).toReal = left.toReal - right.toReal := by
  simp [sub, sub_eq_add_neg]

@[simp] theorem mul_toReal (left right : QuadraticNumber radicand) :
    (left.mul right).toReal = left.toReal * right.toReal := by
  have square_root : Real.sqrt (radicand : ℝ) ^ 2 = radicand :=
    Real.sq_sqrt (Nat.cast_nonneg radicand)
  simp [mul, toReal]
  nlinarith [congrArg (fun value : ℝ =>
    (left.radical : ℝ) * (right.radical : ℝ) * value) square_root]

@[simp] theorem half_toReal (number : QuadraticNumber radicand) :
    number.half.toReal = number.toReal / 2 := by
  simp [half, toReal]
  ring

theorem nonnegative_iff (number : QuadraticNumber radicand) :
    number.Nonnegative ↔ 0 ≤ number.toReal := by
  have root_nonnegative := Real.sqrt_nonneg (radicand : ℝ)
  have root_square := Real.sq_sqrt (Nat.cast_nonneg radicand : (0 : ℝ) ≤ radicand)
  have radical_square :
      ((number.radical : ℝ) * Real.sqrt radicand) ^ 2 =
        radicand * (number.radical : ℝ) ^ 2 := by
    rw [mul_pow, root_square]
    ring
  unfold Nonnegative toReal
  split_ifs with radical_nonnegative
  · have product_nonnegative : 0 ≤ (number.radical : ℝ) * Real.sqrt radicand :=
      mul_nonneg (by exact_mod_cast radical_nonnegative) root_nonnegative
    have cast_iff :
        (0 ≤ number.rational ∨ number.rational ^ 2 ≤ radicand * number.radical ^ 2) ↔
          (0 ≤ (number.rational : ℝ) ∨
            (number.rational : ℝ) ^ 2 ≤ radicand * (number.radical : ℝ) ^ 2) := by
      norm_cast
    rw [cast_iff]
    constructor
    · rintro (positive | squared) <;> nlinarith
    · intro positive
      by_cases rational_nonnegative : 0 ≤ (number.rational : ℝ)
      · exact Or.inl rational_nonnegative
      · right
        nlinarith
  · have product_nonpositive : (number.radical : ℝ) * Real.sqrt radicand ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast le_of_not_ge radical_nonnegative)
        root_nonnegative
    have cast_iff :
        (0 ≤ number.rational ∧ radicand * number.radical ^ 2 ≤ number.rational ^ 2) ↔
          (0 ≤ (number.rational : ℝ) ∧
            radicand * (number.radical : ℝ) ^ 2 ≤ (number.rational : ℝ) ^ 2) := by
      norm_cast
    rw [cast_iff]
    constructor
    · rintro ⟨positive, squared⟩
      nlinarith
    · intro positive
      constructor <;> nlinarith

theorem le_iff (left right : QuadraticNumber radicand) :
    left.Le right ↔ left.toReal ≤ right.toReal := by
  rw [Le, nonnegative_iff, sub_toReal]
  exact sub_nonneg

@[simp] theorem abs_toReal (number : QuadraticNumber radicand) :
    number.abs.toReal = |number.toReal| := by
  unfold abs
  split_ifs with positive
  · exact (abs_of_nonneg ((nonnegative_iff number).mp positive)).symm
  · rw [neg_toReal, abs_of_neg (lt_of_not_ge ((nonnegative_iff number).not.mp positive))]

end QuadraticNumber

end SquarePackingArchive
