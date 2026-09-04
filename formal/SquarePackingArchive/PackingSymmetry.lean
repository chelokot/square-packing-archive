import SquarePackingArchive.Area

namespace SquarePackingArchive

open Set

@[simp] lemma PlacedSquare.dilatedInteriorContains_one_iff
    (square : PlacedSquare) (point : Point) :
    square.DilatedInteriorContains 1 point ↔ square.InteriorContains point := by
  simp [PlacedSquare.DilatedInteriorContains, PlacedSquare.InteriorContains,
    PlacedSquare.dilatedPoint, PlacedSquare.point]

@[simp] lemma PlacedSquare.interiorContains_swap_iff
    (square : PlacedSquare) (point : Point) :
    square.swap.InteriorContains point.swap ↔ square.InteriorContains point := by
  simpa using square.dilatedInteriorContains_swap_iff 1 point

@[simp] lemma PlacedSquare.interiorContains_reflectX_iff
    (square : PlacedSquare) (coordinateSum : ℝ) (point : Point) :
    (square.reflectX coordinateSum).InteriorContains (point.reflectX coordinateSum) ↔
      square.InteriorContains point := by
  simpa using square.dilatedInteriorContains_reflectX_iff coordinateSum 1 point

@[simp] lemma PlacedSquare.interiorContains_reflectY_iff
    (square : PlacedSquare) (coordinateSum : ℝ) (point : Point) :
    (square.reflectY coordinateSum).InteriorContains (point.reflectY coordinateSum) ↔
      square.InteriorContains point := by
  simpa using square.dilatedInteriorContains_reflectY_iff coordinateSum 1 point

lemma PlacedSquare.InteriorDisjoint.swap
    {first second : PlacedSquare} (disjoint : first.InteriorDisjoint second) :
    first.swap.InteriorDisjoint second.swap := by
  intro point shared
  apply disjoint point.swap
  constructor
  · exact (first.interiorContains_swap_iff point.swap).1 (by simpa using shared.1)
  · exact (second.interiorContains_swap_iff point.swap).1 (by simpa using shared.2)

lemma PlacedSquare.InteriorDisjoint.reflectX
    {first second : PlacedSquare} (disjoint : first.InteriorDisjoint second) (coordinateSum : ℝ) :
    (first.reflectX coordinateSum).InteriorDisjoint (second.reflectX coordinateSum) := by
  intro point shared
  apply disjoint (point.reflectX coordinateSum)
  constructor
  · exact (first.interiorContains_reflectX_iff coordinateSum (point.reflectX coordinateSum)).1
      (by simpa using shared.1)
  · exact (second.interiorContains_reflectX_iff coordinateSum (point.reflectX coordinateSum)).1
      (by simpa using shared.2)

lemma PlacedSquare.InteriorDisjoint.reflectY
    {first second : PlacedSquare} (disjoint : first.InteriorDisjoint second) (coordinateSum : ℝ) :
    (first.reflectY coordinateSum).InteriorDisjoint (second.reflectY coordinateSum) := by
  intro point shared
  apply disjoint (point.reflectY coordinateSum)
  constructor
  · exact (first.interiorContains_reflectY_iff coordinateSum (point.reflectY coordinateSum)).1
      (by simpa using shared.1)
  · exact (second.interiorContains_reflectY_iff coordinateSum (point.reflectY coordinateSum)).1
      (by simpa using shared.2)

def Packing.swap {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side) :
    Packing squareCount side where
  squares := fun index => (packing.squares index).swap
  side_nonnegative := packing.side_nonnegative
  fits := fun index => ((packing.squares index).swap_fits_iff side).2 (packing.fits index)
  disjoint := fun first second different => (packing.disjoint first second different).swap

def Packing.reflectX {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side) :
    Packing squareCount side where
  squares := fun index => (packing.squares index).reflectX side
  side_nonnegative := packing.side_nonnegative
  fits := fun index => ((packing.squares index).reflectX_fits_iff side).2 (packing.fits index)
  disjoint := fun first second different => (packing.disjoint first second different).reflectX side

def Packing.reflectY {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side) :
    Packing squareCount side where
  squares := fun index => (packing.squares index).reflectY side
  side_nonnegative := packing.side_nonnegative
  fits := fun index => ((packing.squares index).reflectY_fits_iff side).2 (packing.fits index)
  disjoint := fun first second different => (packing.disjoint first second different).reflectY side

@[simp] lemma Packing.enlarge_squares {squareCount : ℕ} {side largerSide : ℝ}
    (packing : Packing squareCount side) (side_bound : side ≤ largerSide) (index : Fin squareCount) :
    (packing.enlarge side_bound).squares index = packing.squares index := rfl

@[simp] lemma Packing.swap_squares {squareCount : ℕ} {side : ℝ}
    (packing : Packing squareCount side) (index : Fin squareCount) :
    packing.swap.squares index = (packing.squares index).swap := rfl

@[simp] lemma Packing.reflectX_squares {squareCount : ℕ} {side : ℝ}
    (packing : Packing squareCount side) (index : Fin squareCount) :
    packing.reflectX.squares index = (packing.squares index).reflectX side := rfl

@[simp] lemma Packing.reflectY_squares {squareCount : ℕ} {side : ℝ}
    (packing : Packing squareCount side) (index : Fin squareCount) :
    packing.reflectY.squares index = (packing.squares index).reflectY side := rfl

lemma Packing.swap_dilatedInteriorRegion_eq_preimage
    {squareCount : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (factor_positive : 0 < factor) (index : Fin squareCount) :
    (packing.swap.squares index).dilatedInteriorRegion factor =
      Plane.swap ⁻¹' (packing.squares index).dilatedInteriorRegion factor := by
  ext point
  simpa using (packing.squares index).mem_swap_dilatedInteriorRegion_iff factor_positive point.swap

lemma Packing.reflectX_dilatedInteriorRegion_eq_preimage
    {squareCount : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (factor_positive : 0 < factor) (index : Fin squareCount) :
    (packing.reflectX.squares index).dilatedInteriorRegion factor =
      Plane.reflectX (factor * side) ⁻¹' (packing.squares index).dilatedInteriorRegion factor := by
  ext point
  simpa using (packing.squares index).mem_reflectX_dilatedInteriorRegion_iff
    (coordinateSum := side) factor_positive (point.reflectX (factor * side))

lemma Packing.reflectY_dilatedInteriorRegion_eq_preimage
    {squareCount : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (factor_positive : 0 < factor) (index : Fin squareCount) :
    (packing.reflectY.squares index).dilatedInteriorRegion factor =
      Plane.reflectY (factor * side) ⁻¹' (packing.squares index).dilatedInteriorRegion factor := by
  ext point
  simpa using (packing.squares index).mem_reflectY_dilatedInteriorRegion_iff
    (coordinateSum := side) factor_positive (point.reflectY (factor * side))

end SquarePackingArchive
