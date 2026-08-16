import SquarePackingArchive.Geometry

namespace SquarePackingArchive.Records.Basic

noncomputable def squareOne : PlacedSquare where
  center := ⟨1 / 2, 1 / 2⟩
  frame := { cosine := 1, sine := 0, unit := by norm_num }

theorem s1_le_one : HasPacking 1 1 := by
  refine ⟨{
    squares := fun _ => squareOne
    side_nonnegative := by norm_num
    fits := ?_
    disjoint := ?_
  }⟩
  · intro index point contains
    rcases contains with ⟨localX, localY, localX_le, localY_le, rfl⟩
    rcases abs_le.mp localX_le with ⟨localX_lower, localX_upper⟩
    rcases abs_le.mp localY_le with ⟨localY_lower, localY_upper⟩
    simp only [squareOne, PlacedSquare.point, Frame.place, Container.Contains]
    constructor
    · norm_num
      linarith
    · constructor
      · norm_num
        linarith
      · constructor <;> norm_num <;> linarith
  · intro left right different
    exact (different (Subsingleton.elim left right)).elim

lemma single_square_side_ge_one {side : ℝ} (packing : Packing 1 side) :
    1 ≤ side := by
  let square := packing.squares 0
  have firstCorner := packing.fits 0 (point := square.point (1 / 2) (1 / 2)) (by
    refine ⟨1 / 2, 1 / 2, ?_, ?_, rfl⟩ <;> norm_num)
  have oppositeFirstCorner :=
    packing.fits 0 (point := square.point (-1 / 2) (-1 / 2)) (by
      refine ⟨-1 / 2, -1 / 2, ?_, ?_, rfl⟩ <;> norm_num)
  have secondCorner := packing.fits 0 (point := square.point (1 / 2) (-1 / 2)) (by
    refine ⟨1 / 2, -1 / 2, ?_, ?_, rfl⟩ <;> norm_num)
  have oppositeSecondCorner :=
    packing.fits 0 (point := square.point (-1 / 2) (1 / 2)) (by
      refine ⟨-1 / 2, 1 / 2, ?_, ?_, rfl⟩ <;> norm_num)
  have difference_le :
      |square.frame.cosine - square.frame.sine| ≤ side := by
    apply abs_le.mpr
    constructor
    · have firstLower := firstCorner.1
      have oppositeUpper := oppositeFirstCorner.2.1
      simp only [PlacedSquare.point, Frame.place] at firstLower oppositeUpper
      nlinarith
    · have firstUpper := firstCorner.2.1
      have oppositeLower := oppositeFirstCorner.1
      simp only [PlacedSquare.point, Frame.place] at firstUpper oppositeLower
      nlinarith
  have sum_le :
      |square.frame.cosine + square.frame.sine| ≤ side := by
    apply abs_le.mpr
    constructor
    · have secondLower := secondCorner.1
      have oppositeUpper := oppositeSecondCorner.2.1
      simp only [PlacedSquare.point, Frame.place] at secondLower oppositeUpper
      nlinarith
    · have secondUpper := secondCorner.2.1
      have oppositeLower := oppositeSecondCorner.1
      simp only [PlacedSquare.point, Frame.place] at secondUpper oppositeLower
      nlinarith
  by_contra side_too_small
  have side_lt : side < 1 := lt_of_not_ge side_too_small
  have difference_lt : |square.frame.cosine - square.frame.sine| < 1 :=
    lt_of_le_of_lt difference_le side_lt
  have sum_lt : |square.frame.cosine + square.frame.sine| < 1 :=
    lt_of_le_of_lt sum_le side_lt
  rcases abs_lt.mp difference_lt with ⟨difference_lower, difference_upper⟩
  rcases abs_lt.mp sum_lt with ⟨sum_lower, sum_upper⟩
  nlinarith [square.frame.unit]

theorem s1_eq_one : IsMinimumSide 1 1 := by
  constructor
  · exact s1_le_one
  · intro side packing
    exact single_square_side_ge_one packing.some

end SquarePackingArchive.Records.Basic
