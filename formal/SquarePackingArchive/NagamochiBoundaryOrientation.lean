import SquarePackingArchive.NagamochiWeightedChain
import SquarePackingArchive.PackingSymmetry

namespace SquarePackingArchive

open MeasureTheory Set

def NagamochiResource.CornerPoint.edge : NagamochiResource.CornerPoint → NagamochiResource.EdgePoint
  | .leftBottom | .rightBottom => .bottom
  | .leftTop | .rightTop => .top
  | .bottomLeft | .topLeft => .left
  | .bottomRight | .topRight => .right

def NagamochiResource.CornerPoint.reversed : NagamochiResource.CornerPoint → Bool
  | .rightBottom | .rightTop | .topLeft | .topRight => true
  | _ => false

def NagamochiResource.CornerPoint.oppositeEndpoint :
    NagamochiResource.CornerPoint → NagamochiResource.CornerPoint
  | .leftBottom => .rightBottom
  | .rightBottom => .leftBottom
  | .leftTop => .rightTop
  | .rightTop => .leftTop
  | .bottomLeft => .topLeft
  | .topLeft => .bottomLeft
  | .bottomRight => .topRight
  | .topRight => .bottomRight

@[simp] lemma NagamochiResource.CornerPoint.oppositeEndpoint_involutive
    (corner : NagamochiResource.CornerPoint) :
    corner.oppositeEndpoint.oppositeEndpoint = corner := by cases corner <;> rfl

lemma NagamochiResource.CornerPoint.oppositeEndpoint_injective :
    Function.Injective NagamochiResource.CornerPoint.oppositeEndpoint := by
  intro first second equality
  simpa using congrArg NagamochiResource.CornerPoint.oppositeEndpoint equality

def NagamochiResource.EdgePoint.bottomSquare (edge : NagamochiResource.EdgePoint)
    (square : PlacedSquare) (side : ℝ) : PlacedSquare :=
  match edge with
  | .bottom => square
  | .top => square.reflectY side
  | .left => square.swap
  | .right => (square.reflectX side).swap

def NagamochiResource.EdgePoint.originalPoint (edge : NagamochiResource.EdgePoint)
    (side : ℝ) (point : Plane) : Plane :=
  match edge with
  | .bottom => point
  | .top => point.reflectY side
  | .left => point.swap
  | .right => point.swap.reflectX side

def NagamochiResource.CornerPoint.canonicalSquare (corner : NagamochiResource.CornerPoint)
    (square : PlacedSquare) (side : ℝ) : PlacedSquare :=
  let bottom := corner.edge.bottomSquare square side
  if corner.reversed then bottom.reflectX side else bottom

def NagamochiResource.CornerPoint.originalPoint (corner : NagamochiResource.CornerPoint)
    (side : ℝ) (point : Plane) : Plane :=
  corner.edge.originalPoint side (if corner.reversed then point.reflectX side else point)

def NagamochiResource.CornerPoint.originalCoordinate (corner : NagamochiResource.CornerPoint)
    (side coordinate : ℝ) : ℝ :=
  if corner.reversed then side - coordinate else coordinate

lemma NagamochiResource.EdgePoint.bottomSquare_mem_iff
    (edge : NagamochiResource.EdgePoint) (square : PlacedSquare)
    {side factor : ℝ} (factor_positive : 0 < factor) (point : Plane) :
    point ∈ (edge.bottomSquare square side).dilatedInteriorRegion factor ↔
      edge.originalPoint (factor * side) point ∈ square.dilatedInteriorRegion factor := by
  cases edge with
  | bottom => rfl
  | top =>
    simpa [bottomSquare, originalPoint] using
      square.mem_reflectY_dilatedInteriorRegion_iff
        (coordinateSum := side) factor_positive (point.reflectY (factor * side))
  | left =>
    simpa [bottomSquare, originalPoint] using
      square.mem_swap_dilatedInteriorRegion_iff factor_positive point.swap
  | right =>
    have swapped := (square.reflectX side).mem_swap_dilatedInteriorRegion_iff factor_positive point.swap
    have reflected := square.mem_reflectX_dilatedInteriorRegion_iff
      (coordinateSum := side) factor_positive (point.swap.reflectX (factor * side))
    simp only [Plane.swap_swap] at swapped
    simp only [Plane.reflectX_reflectX] at reflected
    exact swapped.trans reflected

lemma NagamochiResource.CornerPoint.canonicalSquare_mem_iff
    (corner : NagamochiResource.CornerPoint) (square : PlacedSquare)
    {side factor : ℝ} (factor_positive : 0 < factor) (point : Plane) :
    point ∈ (corner.canonicalSquare square side).dilatedInteriorRegion factor ↔
      corner.originalPoint (factor * side) point ∈ square.dilatedInteriorRegion factor := by
  unfold canonicalSquare originalPoint
  split
  · have reflected := (corner.edge.bottomSquare square side).mem_reflectX_dilatedInteriorRegion_iff
      (coordinateSum := side) factor_positive (point.reflectX (factor * side))
    simpa using reflected.trans
      (corner.edge.bottomSquare_mem_iff square factor_positive (point.reflectX (factor * side)))
  · exact corner.edge.bottomSquare_mem_iff square factor_positive point

@[simp] lemma NagamochiResource.CornerPoint.originalPoint_anchor
    (corner : NagamochiResource.CornerPoint) (size : ℕ) :
    corner.originalPoint size ![(1 : ℝ), 9 / 10] = NagamochiResource.cornerPoint size corner := by
  cases corner <;> rfl

@[simp] lemma NagamochiResource.CornerPoint.originalPoint_opposite_anchor
    (corner : NagamochiResource.CornerPoint) (size : ℕ) :
    corner.originalPoint size ![(size : ℝ) - 1, 9 / 10] =
      NagamochiResource.cornerPoint size corner.oppositeEndpoint := by
  cases corner <;>
    simp [originalPoint, edge, reversed, oppositeEndpoint, EdgePoint.originalPoint,
      cornerPoint, Plane.reflectX, Plane.reflectY, Plane.swap]

lemma NagamochiResource.CornerPoint.originalPoint_baseline
    (corner : NagamochiResource.CornerPoint) (size : ℕ) (coordinate : ℝ) :
    corner.originalPoint size ![coordinate, (9 / 10 : ℝ)] =
      corner.edge.pointAt size (corner.originalCoordinate size coordinate) := by
  cases corner <;> rfl

def NagamochiResource.EdgePoint.bottomPacking (edge : NagamochiResource.EdgePoint)
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side) : Packing squareCount side :=
  match edge with
  | .bottom => packing
  | .top => packing.reflectY
  | .left => packing.swap
  | .right => packing.reflectX.swap

def NagamochiResource.CornerPoint.canonicalPacking (corner : NagamochiResource.CornerPoint)
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side) : Packing squareCount side :=
  let bottom := corner.edge.bottomPacking packing
  if corner.reversed then bottom.reflectX else bottom

@[simp] lemma NagamochiResource.CornerPoint.canonicalPacking_squares
    (corner : NagamochiResource.CornerPoint) {squareCount : ℕ} {side : ℝ}
    (packing : Packing squareCount side) (owner : Fin squareCount) :
    (corner.canonicalPacking packing).squares owner = corner.canonicalSquare (packing.squares owner) side := by
  cases corner <;> rfl

lemma NagamochiResource.EdgePoint.bottomPacking_score
    (edge : NagamochiResource.EdgePoint) {squareCount size : ℕ} {factor : ℝ}
    (packing : Packing squareCount ((size : ℝ) / factor))
    (factor_positive : 0 < factor) (owner : Fin squareCount) :
    NagamochiResource.measure size ((edge.bottomPacking packing).squares owner |>.dilatedInteriorRegion factor) =
      NagamochiResource.measure size ((packing.squares owner).dilatedInteriorRegion factor) := by
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  cases edge with
  | bottom => rfl
  | top =>
    rw [bottomPacking, packing.reflectY_dilatedInteriorRegion_eq_preimage factor_positive owner, identity]
    exact Nagamochi.resourceMeasure_preimage_reflectY size
      ((packing.squares owner).measurableSet_dilatedInteriorRegion factor_positive.ne')
  | left =>
    rw [bottomPacking, packing.swap_dilatedInteriorRegion_eq_preimage factor_positive owner]
    exact Nagamochi.resourceMeasure_preimage_swap size
      ((packing.squares owner).measurableSet_dilatedInteriorRegion factor_positive.ne')
  | right =>
    rw [bottomPacking, packing.reflectX.swap_dilatedInteriorRegion_eq_preimage factor_positive owner,
      Nagamochi.resourceMeasure_preimage_swap size
        ((packing.reflectX.squares owner).measurableSet_dilatedInteriorRegion factor_positive.ne'),
      packing.reflectX_dilatedInteriorRegion_eq_preimage factor_positive owner, identity]
    exact Nagamochi.resourceMeasure_preimage_reflectX size
      ((packing.squares owner).measurableSet_dilatedInteriorRegion factor_positive.ne')

lemma NagamochiResource.CornerPoint.canonicalPacking_score
    (corner : NagamochiResource.CornerPoint) {squareCount size : ℕ} {factor : ℝ}
    (packing : Packing squareCount ((size : ℝ) / factor))
    (factor_positive : 0 < factor) (owner : Fin squareCount) :
    NagamochiResource.measure size ((corner.canonicalPacking packing).squares owner |>.dilatedInteriorRegion factor) =
      NagamochiResource.measure size ((packing.squares owner).dilatedInteriorRegion factor) := by
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  unfold canonicalPacking
  split
  · rw [(corner.edge.bottomPacking packing).reflectX_dilatedInteriorRegion_eq_preimage factor_positive owner,
      identity, Nagamochi.resourceMeasure_preimage_reflectX size
        (((corner.edge.bottomPacking packing).squares owner).measurableSet_dilatedInteriorRegion factor_positive.ne')]
    exact corner.edge.bottomPacking_score packing factor_positive owner
  · exact corner.edge.bottomPacking_score packing factor_positive owner

theorem Nagamochi.bad_corner_owner_reaches_weighted_terminal
    {size : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (corner : NagamochiResource.CornerPoint) (origin : Fin (size * size - 2))
    (corner_mem : NagamochiResource.cornerPoint size corner ∈
      (packing.squares origin).dilatedInteriorRegion factor)
    (bad : NagamochiResource.measure size ((packing.squares origin).dilatedInteriorRegion factor) ≤ 1) :
    ∃ coordinate ∈ Finset.Icc 2 (size - 1), ∃ owner height,
      height ∈ Icc (9 / 10 : ℝ) 1 ∧
      corner.edge.pointAt size (corner.originalCoordinate size coordinate) ∈
        (packing.squares owner).dilatedInteriorRegion factor ∧
      Nagamochi.BoundaryChainTerminal
        (corner.canonicalSquare (packing.squares owner) (size / factor)) factor coordinate height ∧
      ENNReal.ofReal ((1 + height) / 2) <
        NagamochiResource.measure size ((packing.squares origin).dilatedInteriorRegion factor) := by
  have positive : 0 < factor := by linarith
  have side_bound : side ≤ (size : ℝ) / factor := by
    rw [le_div_iff₀ positive]
    nlinarith
  have identity : factor * ((size : ℝ) / factor) = size := by field_simp
  let enlarged := packing.enlarge side_bound
  let canonical := corner.canonicalPacking enlarged
  have canonical_square (owner : Fin (size * size - 2)) : canonical.squares owner =
      corner.canonicalSquare (packing.squares owner) (size / factor) := by
    simp [canonical, enlarged]
  have canonical_anchor : ![(1 : ℝ), 9 / 10] ∈
      (canonical.squares origin).dilatedInteriorRegion factor := by
    rw [canonical_square]
    rw [corner.canonicalSquare_mem_iff _ positive, identity, corner.originalPoint_anchor]
    exact corner_mem
  have score_eq (owner : Fin (size * size - 2)) :
      NagamochiResource.measure size ((canonical.squares owner).dilatedInteriorRegion factor) =
      NagamochiResource.measure size ((packing.squares owner).dilatedInteriorRegion factor) :=
    corner.canonicalPacking_score enlarged positive owner
  obtain ⟨coordinate, coordinate_mem, owner, height, height_mem, anchor, terminal, budget⟩ :=
    Nagamochi.bottom_left_bad_owner_reaches_weighted_terminal canonical size_lower factor_gt_one
      factor_at_most identity.le origin canonical_anchor (by rwa [score_eq])
  rw [canonical_square] at terminal anchor
  refine ⟨coordinate, coordinate_mem, owner, height, height_mem, ?_, terminal, ?_⟩
  ·
    rwa [corner.canonicalSquare_mem_iff _ positive, identity, corner.originalPoint_baseline] at anchor
  · rwa [score_eq] at budget

end SquarePackingArchive
