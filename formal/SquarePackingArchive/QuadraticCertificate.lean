import SquarePackingArchive.RationalCertificate
import SquarePackingArchive.QuadraticNumber

namespace SquarePackingArchive

structure QuadraticSquare (radicand : ℕ) where
  centerX : QuadraticNumber radicand
  centerY : QuadraticNumber radicand
  cosine : QuadraticNumber radicand
  sine : QuadraticNumber radicand
deriving DecidableEq, Repr

variable {radicand : ℕ}

def QuadraticSquare.IsUnit (square : QuadraticSquare radicand) : Prop :=
  (square.cosine.mul square.cosine).add (square.sine.mul square.sine) =
    QuadraticNumber.ofRat 1

instance (square : QuadraticSquare radicand) : Decidable square.IsUnit := by
  unfold QuadraticSquare.IsUnit
  infer_instance

def QuadraticSquare.extent (square : QuadraticSquare radicand) : QuadraticNumber radicand :=
  (square.cosine.abs.add square.sine.abs).half

def QuadraticSquare.Fits
    (side : QuadraticNumber radicand) (square : QuadraticSquare radicand) : Prop :=
  square.extent.Le square.centerX ∧
    (square.centerX.add square.extent).Le side ∧
      square.extent.Le square.centerY ∧
        (square.centerY.add square.extent).Le side

instance (side : QuadraticNumber radicand) (square : QuadraticSquare radicand) :
    Decidable (square.Fits side) := by
  unfold QuadraticSquare.Fits
  infer_instance

def quadraticDot (leftX leftY rightX rightY : QuadraticNumber radicand) :
    QuadraticNumber radicand :=
  (leftX.mul rightX).add (leftY.mul rightY)

def QuadraticSquare.projectionRadius
    (square : QuadraticSquare radicand) (axisX axisY : QuadraticNumber radicand) :
    QuadraticNumber radicand :=
  ((quadraticDot axisX axisY square.cosine square.sine).abs.add
    (quadraticDot axisX axisY square.sine.neg square.cosine).abs).half

def QuadraticSquare.SeparatedOn
    (left right : QuadraticSquare radicand) (axisX axisY : QuadraticNumber radicand) : Prop :=
  ((left.projectionRadius axisX axisY).add (right.projectionRadius axisX axisY)).Le
    (quadraticDot (right.centerX.sub left.centerX) (right.centerY.sub left.centerY)
      axisX axisY).abs

instance (left right : QuadraticSquare radicand) (axisX axisY : QuadraticNumber radicand) :
    Decidable (left.SeparatedOn right axisX axisY) := by
  unfold QuadraticSquare.SeparatedOn
  infer_instance

def AxisWitness.quadraticAxis
    (witness : AxisWitness) (left right : QuadraticSquare radicand) :
    QuadraticNumber radicand × QuadraticNumber radicand :=
  match witness with
  | .leftHorizontal => (left.cosine, left.sine)
  | .leftVertical => (left.sine.neg, left.cosine)
  | .rightHorizontal => (right.cosine, right.sine)
  | .rightVertical => (right.sine.neg, right.cosine)

structure QuadraticCertificate (radicand squareCount : ℕ) where
  side : QuadraticNumber radicand
  squares : Vector (QuadraticSquare radicand) squareCount
  separatingAxes : Vector (Vector AxisWitness squareCount) squareCount

def QuadraticCertificate.Valid
    {squareCount : ℕ} (certificate : QuadraticCertificate radicand squareCount) : Prop :=
  certificate.side.Nonnegative ∧
    (∀ index,
      (certificate.squares.get index).IsUnit ∧
        (certificate.squares.get index).Fits certificate.side) ∧
      ∀ left right, left < right →
        let witness := (certificate.separatingAxes.get left).get right
        let axis := witness.quadraticAxis
          (certificate.squares.get left) (certificate.squares.get right)
        (certificate.squares.get left).SeparatedOn
          (certificate.squares.get right) axis.1 axis.2

instance {squareCount : ℕ} (certificate : QuadraticCertificate radicand squareCount) :
    Decidable certificate.Valid := by
  unfold QuadraticCertificate.Valid
  infer_instance

def QuadraticCertificate.BoundariesValid
    {squareCount : ℕ} (certificate : QuadraticCertificate radicand squareCount) : Prop :=
  certificate.side.Nonnegative ∧
    ∀ index, (certificate.squares.get index).IsUnit ∧
      (certificate.squares.get index).Fits certificate.side

instance {squareCount : ℕ} (certificate : QuadraticCertificate radicand squareCount) :
    Decidable certificate.BoundariesValid := by
  unfold QuadraticCertificate.BoundariesValid
  infer_instance

def QuadraticCertificate.SeparatedRow
    {squareCount : ℕ} (certificate : QuadraticCertificate radicand squareCount)
    (left : Fin squareCount) : Prop :=
  ∀ right, left < right →
    let witness := (certificate.separatingAxes.get left).get right
    let axis := witness.quadraticAxis
      (certificate.squares.get left) (certificate.squares.get right)
    (certificate.squares.get left).SeparatedOn
      (certificate.squares.get right) axis.1 axis.2

instance {squareCount : ℕ} (certificate : QuadraticCertificate radicand squareCount)
    (left : Fin squareCount) : Decidable (certificate.SeparatedRow left) := by
  unfold QuadraticCertificate.SeparatedRow
  infer_instance

theorem QuadraticCertificate.valid_of_rows
    {squareCount : ℕ} {certificate : QuadraticCertificate radicand squareCount}
    (boundaries : certificate.BoundariesValid)
    (rows : ∀ left, certificate.SeparatedRow left) : certificate.Valid :=
  ⟨boundaries.1, boundaries.2, rows⟩

lemma QuadraticSquare.unit_sound
    (square : QuadraticSquare radicand) (unit : square.IsUnit) :
    square.cosine.toReal ^ 2 + square.sine.toReal ^ 2 = 1 := by
  have evaluated := congrArg QuadraticNumber.toReal unit
  simpa [pow_two] using evaluated

noncomputable def QuadraticSquare.toPlacedSquare
    (square : QuadraticSquare radicand) (unit : square.IsUnit) : PlacedSquare where
  center := ⟨square.centerX.toReal, square.centerY.toReal⟩
  frame := {
    cosine := square.cosine.toReal
    sine := square.sine.toReal
    unit := square.unit_sound unit
  }

@[simp] lemma QuadraticSquare.extent_toReal (square : QuadraticSquare radicand) :
    square.extent.toReal = (|square.cosine.toReal| + |square.sine.toReal|) / 2 := by
  simp [QuadraticSquare.extent]

lemma QuadraticSquare.fits_sound
    {side : QuadraticNumber radicand} {square : QuadraticSquare radicand}
    (unit : square.IsUnit) (fits : square.Fits side) :
    (square.toPlacedSquare unit).Fits side.toReal := by
  intro point contains
  rcases contains with ⟨localX, localY, localX_le, localY_le, point_eq⟩
  subst point
  have horizontal := abs_linearCombination_le
    (coefficientX := square.cosine.toReal) (coefficientY := -square.sine.toReal)
    localX_le localY_le
  have vertical := abs_linearCombination_le
    (coefficientX := square.sine.toReal) (coefficientY := square.cosine.toReal)
    localX_le localY_le
  have horizontal_bounds := abs_le.mp horizontal
  have vertical_bounds := abs_le.mp vertical
  simp only [abs_neg] at horizontal_bounds
  have left_bound := (QuadraticNumber.le_iff _ _).mp fits.1
  have right_bound := (QuadraticNumber.le_iff _ _).mp fits.2.1
  have bottom_bound := (QuadraticNumber.le_iff _ _).mp fits.2.2.1
  have top_bound := (QuadraticNumber.le_iff _ _).mp fits.2.2.2
  simp only [QuadraticNumber.add_toReal, QuadraticSquare.extent_toReal] at left_bound right_bound bottom_bound top_bound
  simp only [PlacedSquare.point, QuadraticSquare.toPlacedSquare, Frame.place]
  constructor
  · dsimp
    nlinarith
  · constructor
    · dsimp
      nlinarith
    · dsimp
      constructor <;> nlinarith

@[simp] lemma quadraticDot_toReal
    (leftX leftY rightX rightY : QuadraticNumber radicand) :
    (quadraticDot leftX leftY rightX rightY).toReal =
      dot leftX.toReal leftY.toReal rightX.toReal rightY.toReal := by
  simp [quadraticDot, dot]

@[simp] lemma QuadraticSquare.projectionRadius_toReal
    (square : QuadraticSquare radicand) (unit : square.IsUnit)
    (axisX axisY : QuadraticNumber radicand) :
    (square.projectionRadius axisX axisY).toReal =
      (square.toPlacedSquare unit).projectionRadius axisX.toReal axisY.toReal := by
  simp [QuadraticSquare.projectionRadius, PlacedSquare.projectionRadius,
    QuadraticSquare.toPlacedSquare]

lemma QuadraticSquare.orientation_nonzero
    (square : QuadraticSquare radicand) (unit : square.IsUnit) :
    square.cosine.toReal ≠ 0 ∨ square.sine.toReal ≠ 0 := by
  by_contra both_zero
  push Not at both_zero
  have unit_real := square.unit_sound unit
  rw [both_zero.1, both_zero.2] at unit_real
  norm_num at unit_real

lemma AxisWitness.quadraticAxis_nonzero
    (witness : AxisWitness) (left right : QuadraticSquare radicand)
    (left_unit : left.IsUnit) (right_unit : right.IsUnit) :
    let axis := witness.quadraticAxis left right
    axis.1.toReal ≠ 0 ∨ axis.2.toReal ≠ 0 := by
  rcases witness with _ | _ | _ | _
  · simpa [AxisWitness.quadraticAxis] using left.orientation_nonzero left_unit
  · rcases left.orientation_nonzero left_unit with cosine_nonzero | sine_nonzero
    · exact Or.inr cosine_nonzero
    · left
      simpa [AxisWitness.quadraticAxis] using neg_ne_zero.mpr sine_nonzero
  · simpa [AxisWitness.quadraticAxis] using right.orientation_nonzero right_unit
  · rcases right.orientation_nonzero right_unit with cosine_nonzero | sine_nonzero
    · exact Or.inr cosine_nonzero
    · left
      simpa [AxisWitness.quadraticAxis] using neg_ne_zero.mpr sine_nonzero

lemma QuadraticSquare.separatedOn_sound
    {left right : QuadraticSquare radicand} {axisX axisY : QuadraticNumber radicand}
    (left_unit : left.IsUnit) (right_unit : right.IsUnit)
    (separated : left.SeparatedOn right axisX axisY) :
    (left.toPlacedSquare left_unit).SeparatedOn
      (right.toPlacedSquare right_unit) axisX.toReal axisY.toReal := by
  have evaluated := (QuadraticNumber.le_iff _ _).mp separated
  simpa [PlacedSquare.SeparatedOn, QuadraticSquare.toPlacedSquare,
    QuadraticSquare.projectionRadius, PlacedSquare.projectionRadius] using evaluated

theorem QuadraticCertificate.valid_sound
    {squareCount : ℕ} {certificate : QuadraticCertificate radicand squareCount}
    (valid : certificate.Valid) :
    HasPacking squareCount certificate.side.toReal := by
  refine ⟨{
    squares := fun index =>
      (certificate.squares.get index).toPlacedSquare (valid.2.1 index).1
    side_nonnegative := (QuadraticNumber.nonnegative_iff _).mp valid.1
    fits := ?_
    disjoint := ?_
  }⟩
  · intro index
    exact QuadraticSquare.fits_sound (valid.2.1 index).1 (valid.2.1 index).2
  · intro left right different
    rcases lt_or_gt_of_ne different with left_before_right | right_before_left
    · let witness := (certificate.separatingAxes.get left).get right
      have separated := valid.2.2 left right left_before_right
      exact PlacedSquare.separatedOn_interiorDisjoint
        (QuadraticSquare.separatedOn_sound
          (valid.2.1 left).1 (valid.2.1 right).1 separated)
        (witness.quadraticAxis_nonzero
          (certificate.squares.get left) (certificate.squares.get right)
          (valid.2.1 left).1 (valid.2.1 right).1)
    · let witness := (certificate.separatingAxes.get right).get left
      have separated := valid.2.2 right left right_before_left
      apply PlacedSquare.InteriorDisjoint.symm
      exact PlacedSquare.separatedOn_interiorDisjoint
        (QuadraticSquare.separatedOn_sound
          (valid.2.1 right).1 (valid.2.1 left).1 separated)
        (witness.quadraticAxis_nonzero
          (certificate.squares.get right) (certificate.squares.get left)
          (valid.2.1 right).1 (valid.2.1 left).1)

end SquarePackingArchive
