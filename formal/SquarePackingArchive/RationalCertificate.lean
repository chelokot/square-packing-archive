import SquarePackingArchive.Geometry
import Mathlib.Data.Rat.Cast.Order

namespace SquarePackingArchive

structure RationalSquare where
  centerX : ℚ
  centerY : ℚ
  cosine : ℚ
  sine : ℚ
deriving DecidableEq, Repr

def RationalSquare.IsUnit (square : RationalSquare) : Prop :=
  square.cosine ^ 2 + square.sine ^ 2 = 1

instance (square : RationalSquare) : Decidable square.IsUnit := by
  unfold RationalSquare.IsUnit
  infer_instance

def RationalSquare.extent (square : RationalSquare) : ℚ :=
  (|square.cosine| + |square.sine|) / 2

def RationalSquare.Fits (side : ℚ) (square : RationalSquare) : Prop :=
  square.extent ≤ square.centerX ∧
    square.centerX + square.extent ≤ side ∧
      square.extent ≤ square.centerY ∧
        square.centerY + square.extent ≤ side

instance (side : ℚ) (square : RationalSquare) : Decidable (square.Fits side) :=
  by unfold RationalSquare.Fits; infer_instance

def rationalDot (leftX leftY rightX rightY : ℚ) : ℚ :=
  leftX * rightX + leftY * rightY

def RationalSquare.projectionRadius
    (square : RationalSquare) (axisX axisY : ℚ) : ℚ :=
  (|rationalDot axisX axisY square.cosine square.sine| +
    |rationalDot axisX axisY (-square.sine) square.cosine|) / 2

def RationalSquare.SeparatedOn
    (left right : RationalSquare) (axisX axisY : ℚ) : Prop :=
  left.projectionRadius axisX axisY + right.projectionRadius axisX axisY ≤
    |rationalDot
      (right.centerX - left.centerX)
      (right.centerY - left.centerY)
      axisX axisY|

instance (left right : RationalSquare) (axisX axisY : ℚ) :
    Decidable (left.SeparatedOn right axisX axisY) := by
  unfold RationalSquare.SeparatedOn
  infer_instance

def RationalSquare.Separated (left right : RationalSquare) : Prop :=
  left.SeparatedOn right left.cosine left.sine ∨
    left.SeparatedOn right (-left.sine) left.cosine ∨
      left.SeparatedOn right right.cosine right.sine ∨
        left.SeparatedOn right (-right.sine) right.cosine

instance (left right : RationalSquare) : Decidable (left.Separated right) :=
  by unfold RationalSquare.Separated; infer_instance

inductive AxisWitness where
  | leftHorizontal
  | leftVertical
  | rightHorizontal
  | rightVertical
deriving DecidableEq, Repr

def AxisWitness.axis
    (witness : AxisWitness) (left right : RationalSquare) : ℚ × ℚ :=
  match witness with
  | .leftHorizontal => (left.cosine, left.sine)
  | .leftVertical => (-left.sine, left.cosine)
  | .rightHorizontal => (right.cosine, right.sine)
  | .rightVertical => (-right.sine, right.cosine)

structure RationalCertificate (squareCount : ℕ) where
  side : ℚ
  squares : Vector RationalSquare squareCount
  separatingAxes : Vector (Vector AxisWitness squareCount) squareCount

def RationalCertificate.Valid
    {squareCount : ℕ} (certificate : RationalCertificate squareCount) : Prop :=
  0 ≤ certificate.side ∧
    (∀ index,
      (certificate.squares.get index).IsUnit ∧
        (certificate.squares.get index).Fits certificate.side) ∧
      ∀ left right, left < right →
        let witness := (certificate.separatingAxes.get left).get right
        let axis := witness.axis
          (certificate.squares.get left) (certificate.squares.get right)
        (certificate.squares.get left).SeparatedOn
          (certificate.squares.get right) axis.1 axis.2

instance {squareCount : ℕ} (certificate : RationalCertificate squareCount) :
    Decidable certificate.Valid := by
  unfold RationalCertificate.Valid
  infer_instance

def RationalSquare.toPlacedSquare
    (square : RationalSquare) (unit : square.IsUnit) : PlacedSquare where
  center := ⟨square.centerX, square.centerY⟩
  frame := {
    cosine := square.cosine
    sine := square.sine
    unit := by exact_mod_cast unit
  }

@[simp] lemma RationalSquare.extent_cast (square : RationalSquare) :
    (square.extent : ℝ) =
      (|(square.cosine : ℝ)| + |(square.sine : ℝ)|) / 2 := by
  simp [RationalSquare.extent]

lemma RationalSquare.fits_sound
    {side : ℚ} {square : RationalSquare}
    (unit : square.IsUnit)
    (fits : square.Fits side) :
    (square.toPlacedSquare unit).Fits side := by
  intro point contains
  rcases contains with ⟨localX, localY, localX_le, localY_le, point_eq⟩
  subst point
  have horizontal := abs_linearCombination_le
    (coefficientX := (square.cosine : ℝ))
    (coefficientY := -(square.sine : ℝ))
    localX_le localY_le
  have vertical := abs_linearCombination_le
    (coefficientX := (square.sine : ℝ))
    (coefficientY := (square.cosine : ℝ))
    localX_le localY_le
  have horizontal_bounds := abs_le.mp horizontal
  have vertical_bounds := abs_le.mp vertical
  simp only [abs_neg] at horizontal_bounds
  have left_bound : (square.extent : ℝ) ≤ square.centerX := by exact_mod_cast fits.1
  have right_bound : square.centerX + square.extent ≤ (side : ℝ) := by
    exact_mod_cast fits.2.1
  have bottom_bound : (square.extent : ℝ) ≤ square.centerY := by
    exact_mod_cast fits.2.2.1
  have top_bound : square.centerY + square.extent ≤ (side : ℝ) := by
    exact_mod_cast fits.2.2.2
  rw [square.extent_cast] at left_bound right_bound bottom_bound top_bound
  simp only [PlacedSquare.point, RationalSquare.toPlacedSquare, Frame.place]
  constructor
  · dsimp
    nlinarith
  · constructor
    · dsimp
      nlinarith
    · dsimp
      constructor <;> nlinarith

@[simp] lemma rationalDot_cast (leftX leftY rightX rightY : ℚ) :
    (rationalDot leftX leftY rightX rightY : ℝ) =
      dot leftX leftY rightX rightY := by
  simp [rationalDot, dot]

@[simp] lemma RationalSquare.projectionRadius_cast
    (square : RationalSquare) (unit : square.IsUnit) (axisX axisY : ℚ) :
    (square.projectionRadius axisX axisY : ℝ) =
      (square.toPlacedSquare unit).projectionRadius axisX axisY := by
  simp [RationalSquare.projectionRadius, PlacedSquare.projectionRadius,
    RationalSquare.toPlacedSquare]

lemma RationalSquare.orientation_nonzero
    (square : RationalSquare) (unit : square.IsUnit) :
    (square.cosine : ℝ) ≠ 0 ∨ (square.sine : ℝ) ≠ 0 := by
  by_contra both_zero
  push Not at both_zero
  have unit_real : (square.cosine : ℝ) ^ 2 + (square.sine : ℝ) ^ 2 = 1 := by
    exact_mod_cast unit
  rw [both_zero.1, both_zero.2] at unit_real
  norm_num at unit_real

lemma AxisWitness.axis_nonzero
    (witness : AxisWitness) (left right : RationalSquare)
    (left_unit : left.IsUnit) (right_unit : right.IsUnit) :
    let axis := witness.axis left right
    (axis.1 : ℝ) ≠ 0 ∨ (axis.2 : ℝ) ≠ 0 := by
  rcases witness with _ | _ | _ | _
  · simpa [AxisWitness.axis] using left.orientation_nonzero left_unit
  · rcases left.orientation_nonzero left_unit with cosine_nonzero | sine_nonzero
    · exact Or.inr cosine_nonzero
    · left
      simpa [AxisWitness.axis] using neg_ne_zero.mpr sine_nonzero
  · simpa [AxisWitness.axis] using right.orientation_nonzero right_unit
  · rcases right.orientation_nonzero right_unit with cosine_nonzero | sine_nonzero
    · exact Or.inr cosine_nonzero
    · left
      simpa [AxisWitness.axis] using neg_ne_zero.mpr sine_nonzero

lemma RationalSquare.separatedOn_sound
    {left right : RationalSquare} {axisX axisY : ℚ}
    (left_unit : left.IsUnit)
    (right_unit : right.IsUnit)
    (separated : left.SeparatedOn right axisX axisY) :
    (left.toPlacedSquare left_unit).SeparatedOn
      (right.toPlacedSquare right_unit) axisX axisY := by
  have casted :
      ((left.projectionRadius axisX axisY +
        right.projectionRadius axisX axisY : ℚ) : ℝ) ≤
      (|rationalDot
        (right.centerX - left.centerX)
        (right.centerY - left.centerY)
        axisX axisY| : ℚ) := by
    exact_mod_cast separated
  push_cast at casted
  rw [left.projectionRadius_cast left_unit,
    right.projectionRadius_cast right_unit] at casted
  simpa [PlacedSquare.SeparatedOn, RationalSquare.toPlacedSquare] using casted

lemma RationalSquare.separated_sound
    {left right : RationalSquare}
    (left_unit : left.IsUnit)
    (right_unit : right.IsUnit)
    (separated : left.Separated right) :
    (left.toPlacedSquare left_unit).InteriorDisjoint
      (right.toPlacedSquare right_unit) := by
  rcases separated with on_left_horizontal | on_left_vertical |
      on_right_horizontal | on_right_vertical
  · exact PlacedSquare.separatedOn_interiorDisjoint
      (RationalSquare.separatedOn_sound left_unit right_unit on_left_horizontal)
      (left.orientation_nonzero left_unit)
  · exact PlacedSquare.separatedOn_interiorDisjoint
      (RationalSquare.separatedOn_sound left_unit right_unit on_left_vertical)
      (by rcases left.orientation_nonzero left_unit with cosine_nonzero | sine_nonzero
          · exact Or.inr cosine_nonzero
          · left
            simpa using neg_ne_zero.mpr sine_nonzero)
  · exact PlacedSquare.separatedOn_interiorDisjoint
      (RationalSquare.separatedOn_sound left_unit right_unit on_right_horizontal)
      (right.orientation_nonzero right_unit)
  · exact PlacedSquare.separatedOn_interiorDisjoint
      (RationalSquare.separatedOn_sound left_unit right_unit on_right_vertical)
      (by rcases right.orientation_nonzero right_unit with cosine_nonzero | sine_nonzero
          · exact Or.inr cosine_nonzero
          · left
            simpa using neg_ne_zero.mpr sine_nonzero)

theorem RationalCertificate.valid_sound
    {squareCount : ℕ} {certificate : RationalCertificate squareCount}
    (valid : certificate.Valid) :
    HasPacking squareCount certificate.side := by
  refine ⟨{
    squares := fun index =>
      (certificate.squares.get index).toPlacedSquare (valid.2.1 index).1
    side_nonnegative := ?_
    fits := ?_
    disjoint := ?_
  }⟩
  · exact_mod_cast valid.1
  · intro index
    exact RationalSquare.fits_sound (valid.2.1 index).1 (valid.2.1 index).2
  · intro left right different
    rcases lt_or_gt_of_ne different with left_before_right | right_before_left
    · let witness := (certificate.separatingAxes.get left).get right
      let axis := witness.axis
        (certificate.squares.get left) (certificate.squares.get right)
      have separated := valid.2.2 left right left_before_right
      exact PlacedSquare.separatedOn_interiorDisjoint
        (RationalSquare.separatedOn_sound
          (valid.2.1 left).1 (valid.2.1 right).1 separated)
        (witness.axis_nonzero
          (certificate.squares.get left) (certificate.squares.get right)
          (valid.2.1 left).1 (valid.2.1 right).1)
    · let witness := (certificate.separatingAxes.get right).get left
      let axis := witness.axis
        (certificate.squares.get right) (certificate.squares.get left)
      have separated := valid.2.2 right left right_before_left
      apply PlacedSquare.InteriorDisjoint.symm
      exact PlacedSquare.separatedOn_interiorDisjoint
        (RationalSquare.separatedOn_sound
          (valid.2.1 right).1 (valid.2.1 left).1 separated)
        (witness.axis_nonzero
          (certificate.squares.get right) (certificate.squares.get left)
          (valid.2.1 right).1 (valid.2.1 left).1)

end SquarePackingArchive
