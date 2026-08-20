import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

namespace SquarePackingArchive

structure Point where
  x : ℝ
  y : ℝ

def Point.swap (point : Point) : Point :=
  ⟨point.y, point.x⟩

def Point.reflectX (coordinateSum : ℝ) (point : Point) : Point :=
  ⟨coordinateSum - point.x, point.y⟩

def Point.reflectY (coordinateSum : ℝ) (point : Point) : Point :=
  ⟨point.x, coordinateSum - point.y⟩

@[simp] lemma Point.swap_swap (point : Point) :
    point.swap.swap = point := by
  rfl

lemma Point.swap_injective : Function.Injective Point.swap := by
  intro left right equality
  have := congrArg Point.swap equality
  simpa using this

@[simp] lemma Point.reflectX_reflectX (coordinateSum : ℝ) (point : Point) :
    (point.reflectX coordinateSum).reflectX coordinateSum = point := by
  cases point
  simp [Point.reflectX]

lemma Point.reflectX_injective (coordinateSum : ℝ) :
    Function.Injective (Point.reflectX coordinateSum) := by
  intro left right equality
  have := congrArg (Point.reflectX coordinateSum) equality
  simpa using this

@[simp] lemma Point.reflectY_reflectY (coordinateSum : ℝ) (point : Point) :
    (point.reflectY coordinateSum).reflectY coordinateSum = point := by
  cases point
  simp [Point.reflectY]

lemma Point.reflectY_injective (coordinateSum : ℝ) :
    Function.Injective (Point.reflectY coordinateSum) := by
  intro left right equality
  have := congrArg (Point.reflectY coordinateSum) equality
  simpa using this

structure Frame where
  cosine : ℝ
  sine : ℝ
  unit : cosine ^ 2 + sine ^ 2 = 1

lemma Frame.cosine_le_one (frame : Frame) (cosine_nonnegative : 0 ≤ frame.cosine) :
    frame.cosine ≤ 1 := by
  nlinarith [frame.unit, sq_nonneg frame.sine]

lemma Frame.sine_le_one (frame : Frame) (sine_nonnegative : 0 ≤ frame.sine) :
    frame.sine ≤ 1 := by
  nlinarith [frame.unit, sq_nonneg frame.cosine]

def Frame.swap (frame : Frame) : Frame where
  cosine := frame.sine
  sine := frame.cosine
  unit := by nlinarith [frame.unit]

def Frame.rotateQuarter (frame : Frame) : Frame where
  cosine := -frame.sine
  sine := frame.cosine
  unit := by nlinarith [frame.unit]

def Frame.reflectX (frame : Frame) : Frame where
  cosine := -frame.cosine
  sine := frame.sine
  unit := by nlinarith [frame.unit]

def Frame.reflectY (frame : Frame) : Frame where
  cosine := frame.cosine
  sine := -frame.sine
  unit := by nlinarith [frame.unit]

def Frame.place (frame : Frame) (localX localY : ℝ) : Point :=
  ⟨localX * frame.cosine - localY * frame.sine,
    localX * frame.sine + localY * frame.cosine⟩

structure PlacedSquare where
  center : Point
  frame : Frame

def PlacedSquare.swap (square : PlacedSquare) : PlacedSquare where
  center := square.center.swap
  frame := square.frame.swap

def PlacedSquare.rotateQuarter (square : PlacedSquare) : PlacedSquare where
  center := square.center
  frame := square.frame.rotateQuarter

def PlacedSquare.rotateHalf (square : PlacedSquare) : PlacedSquare :=
  square.rotateQuarter.rotateQuarter

def PlacedSquare.rotateThreeQuarter (square : PlacedSquare) : PlacedSquare :=
  square.rotateHalf.rotateQuarter

def PlacedSquare.reflectX (coordinateSum : ℝ) (square : PlacedSquare) : PlacedSquare where
  center := square.center.reflectX coordinateSum
  frame := square.frame.reflectX

def PlacedSquare.reflectY (coordinateSum : ℝ) (square : PlacedSquare) : PlacedSquare where
  center := square.center.reflectY coordinateSum
  frame := square.frame.reflectY

noncomputable def PlacedSquare.firstQuadrant (square : PlacedSquare) : PlacedSquare :=
  if 0 ≤ square.frame.cosine then
    if 0 ≤ square.frame.sine then square else square.rotateQuarter
  else if 0 ≤ square.frame.sine then square.rotateThreeQuarter else square.rotateHalf

lemma PlacedSquare.firstQuadrant_cosine_nonnegative (square : PlacedSquare) :
    0 ≤ square.firstQuadrant.frame.cosine := by
  simp only [PlacedSquare.firstQuadrant]
  split_ifs with cosine_nonnegative sine_nonnegative sine_nonnegative
  · exact cosine_nonnegative
  · simp [PlacedSquare.rotateQuarter, Frame.rotateQuarter]
    linarith
  · simp [PlacedSquare.rotateThreeQuarter, PlacedSquare.rotateHalf,
      PlacedSquare.rotateQuarter, Frame.rotateQuarter]
    exact sine_nonnegative
  · simp [PlacedSquare.rotateHalf, PlacedSquare.rotateQuarter, Frame.rotateQuarter]
    linarith

lemma PlacedSquare.firstQuadrant_sine_nonnegative (square : PlacedSquare) :
    0 ≤ square.firstQuadrant.frame.sine := by
  simp only [PlacedSquare.firstQuadrant]
  split_ifs with cosine_nonnegative sine_nonnegative sine_nonnegative
  · exact sine_nonnegative
  · simp [PlacedSquare.rotateQuarter, Frame.rotateQuarter]
    exact cosine_nonnegative
  · simp [PlacedSquare.rotateThreeQuarter, PlacedSquare.rotateHalf,
      PlacedSquare.rotateQuarter, Frame.rotateQuarter]
    linarith
  · simp [PlacedSquare.rotateHalf, PlacedSquare.rotateQuarter, Frame.rotateQuarter]
    linarith

@[simp] lemma PlacedSquare.firstQuadrant_center (square : PlacedSquare) :
    square.firstQuadrant.center = square.center := by
  simp only [PlacedSquare.firstQuadrant]
  split_ifs <;>
    rfl

def PlacedSquare.point (square : PlacedSquare) (localX localY : ℝ) : Point :=
  let offset := square.frame.place localX localY
  ⟨square.center.x + offset.x, square.center.y + offset.y⟩

def PlacedSquare.Contains (square : PlacedSquare) (point : Point) : Prop :=
  ∃ localX localY : ℝ,
    |localX| ≤ 1 / 2 ∧
      |localY| ≤ 1 / 2 ∧
        point = square.point localX localY

def PlacedSquare.InteriorContains (square : PlacedSquare) (point : Point) : Prop :=
  ∃ localX localY : ℝ,
    |localX| < 1 / 2 ∧
      |localY| < 1 / 2 ∧
        point = square.point localX localY

def Container.Contains (side : ℝ) (point : Point) : Prop :=
  0 ≤ point.x ∧ point.x ≤ side ∧ 0 ≤ point.y ∧ point.y ≤ side

def PlacedSquare.Fits (square : PlacedSquare) (side : ℝ) : Prop :=
  ∀ ⦃point⦄, square.Contains point → Container.Contains side point

def PlacedSquare.InteriorDisjoint (left right : PlacedSquare) : Prop :=
  ∀ point, ¬(left.InteriorContains point ∧ right.InteriorContains point)

lemma PlacedSquare.InteriorDisjoint.symm
    {left right : PlacedSquare} (disjoint : left.InteriorDisjoint right) :
    right.InteriorDisjoint left := by
  intro point shared
  exact disjoint point ⟨shared.2, shared.1⟩

def dot (leftX leftY rightX rightY : ℝ) : ℝ :=
  leftX * rightX + leftY * rightY

noncomputable def PlacedSquare.projectionRadius
    (square : PlacedSquare) (axisX axisY : ℝ) : ℝ :=
  (|dot axisX axisY square.frame.cosine square.frame.sine| +
    |dot axisX axisY (-square.frame.sine) square.frame.cosine|) / 2

def PlacedSquare.SeparatedOn
    (left right : PlacedSquare) (axisX axisY : ℝ) : Prop :=
  left.projectionRadius axisX axisY + right.projectionRadius axisX axisY ≤
    |dot
      (right.center.x - left.center.x)
      (right.center.y - left.center.y)
      axisX axisY|

structure Packing (squareCount : ℕ) (side : ℝ) where
  squares : Fin squareCount → PlacedSquare
  side_nonnegative : 0 ≤ side
  fits : ∀ index, (squares index).Fits side
  disjoint : ∀ left right, left ≠ right →
    (squares left).InteriorDisjoint (squares right)

def HasPacking (squareCount : ℕ) (side : ℝ) : Prop :=
  Nonempty (Packing squareCount side)

def IsMinimumSide (squareCount : ℕ) (side : ℝ) : Prop :=
  HasPacking squareCount side ∧
    ∀ candidateSide, HasPacking squareCount candidateSide → side ≤ candidateSide

def Packing.reindex
    {sourceCount targetCount : ℕ} {side : ℝ}
    (packing : Packing sourceCount side)
    (embedding : Fin targetCount ↪ Fin sourceCount) :
    Packing targetCount side where
  squares := packing.squares ∘ embedding
  side_nonnegative := packing.side_nonnegative
  fits := fun index => packing.fits (embedding index)
  disjoint := by
    intro left right different
    exact packing.disjoint (embedding left) (embedding right)
      fun equality => different (embedding.injective equality)

lemma HasPacking.mono
    {sourceCount targetCount : ℕ} {side : ℝ}
    (packing : HasPacking sourceCount side)
    (count_le : targetCount ≤ sourceCount) :
    HasPacking targetCount side := by
  rcases packing with ⟨source⟩
  exact ⟨source.reindex (Fin.castLEEmb count_le)⟩

def Packing.enlarge
    {squareCount : ℕ} {side largerSide : ℝ}
    (packing : Packing squareCount side) (side_le : side ≤ largerSide) :
    Packing squareCount largerSide where
  squares := packing.squares
  side_nonnegative := packing.side_nonnegative.trans side_le
  fits := by
    intro index point point_mem
    have contained := packing.fits index point_mem
    exact ⟨contained.1, contained.2.1.trans side_le,
      contained.2.2.1, contained.2.2.2.trans side_le⟩
  disjoint := packing.disjoint

lemma HasPacking.enlarge
    {squareCount : ℕ} {side largerSide : ℝ}
    (packing : HasPacking squareCount side) (side_le : side ≤ largerSide) :
    HasPacking squareCount largerSide :=
  ⟨packing.some.enlarge side_le⟩

lemma abs_linearCombination_le
    {localX localY coefficientX coefficientY : ℝ}
    (localX_le : |localX| ≤ 1 / 2)
    (localY_le : |localY| ≤ 1 / 2) :
    |localX * coefficientX + localY * coefficientY| ≤
      (|coefficientX| + |coefficientY|) / 2 := by
  calc
    |localX * coefficientX + localY * coefficientY| ≤
        |localX * coefficientX| + |localY * coefficientY| := abs_add_le _ _
    _ = |localX| * |coefficientX| + |localY| * |coefficientY| := by
      rw [abs_mul, abs_mul]
    _ ≤ (1 / 2) * |coefficientX| + (1 / 2) * |coefficientY| := by
      gcongr
    _ = (|coefficientX| + |coefficientY|) / 2 := by ring

lemma abs_linearCombination_lt
    {localX localY coefficientX coefficientY : ℝ}
    (localX_lt : |localX| < 1 / 2)
    (localY_lt : |localY| < 1 / 2)
    (coefficient_nonzero : coefficientX ≠ 0 ∨ coefficientY ≠ 0) :
    |localX * coefficientX + localY * coefficientY| <
      (|coefficientX| + |coefficientY|) / 2 := by
  calc
    |localX * coefficientX + localY * coefficientY| ≤
        |localX * coefficientX| + |localY * coefficientY| := abs_add_le _ _
    _ = |localX| * |coefficientX| + |localY| * |coefficientY| := by
      rw [abs_mul, abs_mul]
    _ < (1 / 2) * |coefficientX| + (1 / 2) * |coefficientY| := by
      rcases coefficient_nonzero with coefficientX_nonzero | coefficientY_nonzero
      · exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_right localX_lt (abs_pos.mpr coefficientX_nonzero))
          (mul_le_mul_of_nonneg_right (le_of_lt localY_lt) (abs_nonneg _))
      · exact add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_right (le_of_lt localX_lt) (abs_nonneg _))
          (mul_lt_mul_of_pos_right localY_lt (abs_pos.mpr coefficientY_nonzero))
    _ = (|coefficientX| + |coefficientY|) / 2 := by ring

lemma Frame.projection_coefficients_nonzero
    (frame : Frame) {axisX axisY : ℝ}
    (axis_nonzero : axisX ≠ 0 ∨ axisY ≠ 0) :
    dot axisX axisY frame.cosine frame.sine ≠ 0 ∨
      dot axisX axisY (-frame.sine) frame.cosine ≠ 0 := by
  by_contra both_zero
  push Not at both_zero
  rcases both_zero with ⟨first_zero, second_zero⟩
  simp only [dot] at first_zero second_zero
  rcases axis_nonzero with axisX_nonzero | axisY_nonzero
  · have : axisX * (frame.cosine ^ 2 + frame.sine ^ 2) = 0 := by
      linear_combination frame.cosine * first_zero - frame.sine * second_zero
    rw [frame.unit, mul_one] at this
    exact axisX_nonzero this
  · have : axisY * (frame.cosine ^ 2 + frame.sine ^ 2) = 0 := by
      linear_combination frame.sine * first_zero + frame.cosine * second_zero
    rw [frame.unit, mul_one] at this
    exact axisY_nonzero this

lemma PlacedSquare.projection_lt_radius
    {square : PlacedSquare} {point : Point} {axisX axisY : ℝ}
    (point_interior : square.InteriorContains point)
    (axis_nonzero : axisX ≠ 0 ∨ axisY ≠ 0) :
    |dot
      (point.x - square.center.x)
      (point.y - square.center.y)
      axisX axisY| < square.projectionRadius axisX axisY := by
  rcases point_interior with ⟨localX, localY, localX_lt, localY_lt, point_eq⟩
  subst point
  have bound := abs_linearCombination_lt
    localX_lt localY_lt (square.frame.projection_coefficients_nonzero axis_nonzero)
  simp only [PlacedSquare.point, Frame.place, dot]
  rw [PlacedSquare.projectionRadius]
  convert bound using 1
  congr 1
  simp only [dot]
  ring

lemma PlacedSquare.separatedOn_interiorDisjoint
    {left right : PlacedSquare} {axisX axisY : ℝ}
    (separated : left.SeparatedOn right axisX axisY)
    (axis_nonzero : axisX ≠ 0 ∨ axisY ≠ 0) :
    left.InteriorDisjoint right := by
  intro point shared
  have left_projection := left.projection_lt_radius shared.1 axis_nonzero
  have right_projection := right.projection_lt_radius shared.2 axis_nonzero
  have triangle :
      |dot
        (right.center.x - left.center.x)
        (right.center.y - left.center.y)
        axisX axisY| ≤
        |dot
          (point.x - left.center.x)
          (point.y - left.center.y)
          axisX axisY| +
        |dot
          (point.x - right.center.x)
          (point.y - right.center.y)
          axisX axisY| := by
    calc
      |dot
        (right.center.x - left.center.x)
        (right.center.y - left.center.y)
        axisX axisY| =
          |dot
            (point.x - left.center.x)
            (point.y - left.center.y)
            axisX axisY -
          dot
            (point.x - right.center.x)
            (point.y - right.center.y)
            axisX axisY| := by
              congr 1
              simp only [dot]
              ring
      _ ≤ _ := abs_sub _ _
  exact (not_lt_of_ge separated) (lt_of_le_of_lt triangle (add_lt_add left_projection right_projection))

end SquarePackingArchive
