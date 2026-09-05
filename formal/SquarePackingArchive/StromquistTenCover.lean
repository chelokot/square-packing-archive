import SquarePackingArchive.StromquistTenTriangleCover
import SquarePackingArchive.StromquistTenBoundary

namespace SquarePackingArchive.Stromquist.TenPoints

private lemma stepThree_area_7_6 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 7) (stepThreePoints 6) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_6_5 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 6) (stepThreePoints 5) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_5_4 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 5) (stepThreePoints 4) square.center =
      ((-3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_4_3 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 4) (stepThreePoints 3) square.center =
      ((3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_3_2 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 3) (stepThreePoints 2) square.center =
      ((24 / 25 : ℝ) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((-23 / 50 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_2_0 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 2) (stepThreePoints 0) square.center =
      (((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((-29 / 100 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_0_7 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 0) (stepThreePoints 7) square.center =
      ((0 : ℝ) * square.center.x + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_boundary_0 (square : PlacedSquare) :
    StepThreeBoundaryRegion 0 square.center ↔ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by
  constructor <;> rintro ⟨part_0, part_1⟩ <;> repeat' apply And.intro
  all_goals nlinarith only [part_0, part_1, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_1 (square : PlacedSquare) :
    StepThreeBoundaryRegion 1 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by
  constructor <;> rintro ⟨part_0, part_1⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 ⊢
  all_goals nlinarith only [part_0, part_1, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_2 (square : PlacedSquare) :
    StepThreeBoundaryRegion 2 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 ⊢
  all_goals nlinarith only [part_0, part_1, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_3 (square : PlacedSquare) :
    StepThreeBoundaryRegion 3 square.center ↔ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 ⊢
  all_goals nlinarith only [part_0, part_1, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_4 (square : PlacedSquare) :
    StepThreeBoundaryRegion 4 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (6 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (1 / 5 : ℝ)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_5 (square : PlacedSquare) :
    StepThreeBoundaryRegion 5 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-6 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_6 (square : PlacedSquare) :
    StepThreeBoundaryRegion 6 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_7 (square : PlacedSquare) :
    StepThreeBoundaryRegion 7 square.center ↔ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((26 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_8 (square : PlacedSquare) :
    StepThreeBoundaryRegion 8 square.center ↔ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-26 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_9 (square : PlacedSquare) :
    StepThreeBoundaryRegion 9 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_10 (square : PlacedSquare) :
    StepThreeBoundaryRegion 10 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_11 (square : PlacedSquare) :
    StepThreeBoundaryRegion 11 square.center ↔ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepThree_boundary_12 (square : PlacedSquare) :
    StepThreeBoundaryRegion 12 square.center ↔ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

set_option maxHeartbeats 4000000 in
theorem stepThree_unavoidable : Unavoidable stepThreePoints side := by
  intro square fits
  have center_inside : square.Contains square.center := by
    refine ⟨0, 0, by norm_num, by norm_num, ?_⟩
    simp [PlacedSquare.point, Frame.place]
  have container_bounds := fits center_inside
  have container_0 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (0 : ℝ)) := by
    dsimp [side, gap, Records.Square5.diagonal] at container_bounds
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  have container_1 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by
    dsimp [side, gap, Records.Square5.diagonal] at container_bounds
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  have container_2 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) := by
    dsimp [side, gap, Records.Square5.diagonal] at container_bounds
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  have container_3 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by
    dsimp [side, gap, Records.Square5.diagonal] at container_bounds
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  by_cases branch_0 : 0 ≤ ((0 : ℝ) * square.center.x + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
  ·
    by_cases branch_1 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
    ·
      by_cases branch_2 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ))
      ·
        by_cases branch_3 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
        ·
          apply stepThree_hit_boundary square fits 3
          rw [stepThree_boundary_3]
          refine ⟨?_ , ?_ ⟩
          ·
            exact branch_2
          ·
            exact branch_3
        ·
          have branch_3_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_3]
          by_cases branch_4 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((26 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2))
          ·
            by_cases branch_5 : 0 ≤ (((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((-29 / 100 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
            ·
              apply stepThree_hit_in_hull square
              ·
                rw [stepThree_area_7_6]
                by_contra! failed
                have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_2
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_1
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (3 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) = ((-69 / 200 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((69 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_6_5]
                by_contra! failed
                have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_3
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_1
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (3 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) = ((-69 / 200 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((69 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_5_4]
                by_contra! failed
                have negative : 0 < ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_1
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_4
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (3 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((26 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) = ((-9 / 20 : ℝ) + (-6 / 25 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((9 / 20 : ℝ) + (6 / 25 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_4_3]
                by_contra! failed
                have negative : 0 < ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_0
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_4
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (3 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (0 : ℝ)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((26 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) = ((-9 / 20 : ℝ) + (-6 / 25 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((9 / 20 : ℝ) + (6 / 25 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_3_2]
                by_contra! failed
                have negative : 0 < ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((1 / 4 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2)) branch_4
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (24 / 25 : ℝ)) branch_5
                have weighted_2 := mul_pos (by positivity : 0 < ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
                have identity : ((1 / 4 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((26 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + (24 / 25 : ℝ) * (((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((-29 / 100 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                rw [stepThree_area_2_0]
                exact branch_5
              ·
                rw [stepThree_area_0_7]
                exact branch_0
            ·
              have branch_5_negative : 0 < (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_5]
              apply stepThree_hit_boundary square fits 7
              rw [stepThree_boundary_7]
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_0
                have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_4
              ·
                exact branch_5_negative.le
          ·
            have branch_4_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-26 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_4]
            by_cases branch_6 : 0 ≤ ((24 / 25 : ℝ) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((-23 / 50 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2))
            ·
              apply stepThree_hit_in_hull square
              ·
                rw [stepThree_area_7_6]
                by_contra! failed
                have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_2
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_1
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (3 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) = ((-69 / 200 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((69 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_6_5]
                by_contra! failed
                have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_3
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_1
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (3 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) = ((-69 / 200 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((69 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_5_4]
                by_contra! failed
                have negative : 0 < ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) branch_1
                have weighted_1 := mul_pos (by positivity : 0 < ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_3_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (3 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) = ((-3 / 200 : ℝ) + (-3 / 400 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((3 / 200 : ℝ) + (3 / 400 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_4_3]
                by_contra! failed
                have negative : 0 < ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((189 / 400 : ℝ) + (6 / 25 : ℝ) * Real.sqrt 2)) branch_2
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_6
                have weighted_2 := mul_pos (by norm_num : 0 < (1 / 4 : ℝ)) negative
                have identity : ((189 / 400 : ℝ) + (6 / 25 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((24 / 25 : ℝ) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((-23 / 50 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2)) + (1 / 4 : ℝ) * ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                rw [stepThree_area_3_2]
                exact branch_6
              ·
                rw [stepThree_area_2_0]
                by_contra! failed
                have negative : 0 < (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_pos (by positivity : 0 < ((1 / 4 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2)) branch_4_negative
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_6
                have weighted_2 := mul_pos (by norm_num : 0 < (24 / 25 : ℝ)) negative
                have identity : ((1 / 4 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-26 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((24 / 25 : ℝ) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((-23 / 50 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2)) + (24 / 25 : ℝ) * (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                rw [stepThree_area_0_7]
                exact branch_0
            ·
              have branch_6_negative : 0 < ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) := by linarith only [branch_6]
              apply stepThree_hit_boundary square fits 8
              rw [stepThree_boundary_8]
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_4_negative.le
              ·
                exact branch_3_negative.le
              ·
                exact branch_6_negative.le
      ·
        have branch_2_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [branch_2]
        by_cases branch_7 : 0 ≤ ((3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2))
        ·
          apply stepThree_hit_in_hull square
          ·
            rw [stepThree_area_7_6]
            by_contra! failed
            have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_2
            have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_1
            have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
            have identity : (3 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) = ((-69 / 200 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            have constant_negative := (by positivity : 0 < ((69 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
            nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
          ·
            rw [stepThree_area_6_5]
            by_contra! failed
            have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_3
            have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_1
            have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
            have identity : (3 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) = ((-69 / 200 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            have constant_negative := (by positivity : 0 < ((69 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
            nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
          ·
            rw [stepThree_area_5_4]
            by_contra! failed
            have negative : 0 < ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((3 / 100 : ℝ) + (3 / 200 : ℝ) * Real.sqrt 2)) branch_1
            have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_7
            have weighted_2 := mul_pos (by positivity : 0 < ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
            have identity : ((3 / 100 : ℝ) + (3 / 200 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            rw [stepThree_area_4_3]
            exact branch_7
          ·
            rw [stepThree_area_3_2]
            by_contra! failed
            have negative : 0 < ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_pos (by positivity : 0 < ((189 / 400 : ℝ) + (6 / 25 : ℝ) * Real.sqrt 2)) branch_2_negative
            have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ)) branch_7
            have weighted_2 := mul_pos (by positivity : 0 < ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
            have identity : ((189 / 400 : ℝ) + (6 / 25 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) + (1 / 4 : ℝ) * ((3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            rw [stepThree_area_2_0]
            by_contra! failed
            have negative : 0 < (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ)) branch_0
            have weighted_1 := mul_pos (by positivity : 0 < ((27 / 50 : ℝ) + (13 / 25 : ℝ) * Real.sqrt 2)) branch_2_negative
            have weighted_2 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
            have identity : (1 / 4 : ℝ) * ((0 : ℝ) * square.center.x + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((27 / 50 : ℝ) + (13 / 25 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            rw [stepThree_area_0_7]
            exact branch_0
        ·
          have branch_7_negative : 0 < ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_7]
          apply stepThree_hit_boundary square fits 9
          rw [stepThree_boundary_9]
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_2_negative.le
          ·
            exact branch_1
          ·
            exact branch_7_negative.le
    ·
      have branch_1_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_1]
      by_cases branch_8 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
      ·
        by_cases branch_9 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
        ·
          apply stepThree_hit_boundary square fits 2
          rw [stepThree_boundary_2]
          refine ⟨?_ , ?_ ⟩
          ·
            exact branch_8
          ·
            exact branch_9
        ·
          have branch_9_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_9]
          by_cases branch_10 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
          ·
            by_cases branch_11 : 0 ≤ (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2))
            ·
              apply stepThree_hit_in_hull square
              ·
                rw [stepThree_area_7_6]
                exact branch_11
              ·
                rw [stepThree_area_6_5]
                by_contra! failed
                have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((3 / 100 : ℝ) + (3 / 200 : ℝ) * Real.sqrt 2)) branch_10
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_11
                have weighted_2 := mul_pos (by positivity : 0 < ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
                have identity : ((3 / 100 : ℝ) + (3 / 200 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                rw [stepThree_area_5_4]
                by_contra! failed
                have negative : 0 < ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_1
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_10
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (3 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) = ((-69 / 200 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((69 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_4_3]
                by_contra! failed
                have negative : 0 < ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_0
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_10
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (3 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (0 : ℝ)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) = ((-69 / 200 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((69 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_3_2]
                by_contra! failed
                have negative : 0 < ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ)) container_3
                have weighted_1 := mul_pos (by norm_num : 0 < (24 / 25 : ℝ)) branch_1_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (1 / 4 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + (24 / 25 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) = ((-23 / 100 : ℝ) + (-6 / 25 : ℝ) * Real.sqrt 2) := by
                  ring
                have constant_negative := (by positivity : 0 < ((23 / 100 : ℝ) + (6 / 25 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_2_0]
                by_contra! failed
                have negative : 0 < (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ)) container_2
                have weighted_1 := mul_pos (by positivity : 0 < ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_1_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (1 / 4 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) = ((-1 / 50 : ℝ) + (-13 / 50 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((1 / 50 : ℝ) + (13 / 50 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_0_7]
                exact branch_0
            ·
              have branch_11_negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_11]
              apply stepThree_hit_boundary square fits 11
              rw [stepThree_boundary_11]
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_0
                have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_10
              ·
                exact branch_11_negative.le
          ·
            have branch_10_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_10]
            by_cases branch_12 : 0 ≤ (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2))
            ·
              apply stepThree_hit_in_hull square
              ·
                rw [stepThree_area_7_6]
                by_contra! failed
                have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_pos (by positivity : 0 < ((3 / 100 : ℝ) + (3 / 200 : ℝ) * Real.sqrt 2)) branch_10_negative
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_12
                have weighted_2 := mul_pos (by positivity : 0 < ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
                have identity : ((3 / 100 : ℝ) + (3 / 200 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                rw [stepThree_area_6_5]
                exact branch_12
              ·
                rw [stepThree_area_5_4]
                by_contra! failed
                have negative : 0 < ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((3741 / 10000 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_8
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_12
                have weighted_2 := mul_pos (by norm_num : 0 < (3 / 100 : ℝ)) negative
                have identity : ((3741 / 10000 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2)) + (3 / 100 : ℝ) * ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                rw [stepThree_area_4_3]
                by_contra! failed
                have negative : 0 < ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (3 / 100 : ℝ)) branch_1_negative
                have weighted_1 := mul_pos (by positivity : 0 < ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_9_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (3 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) = ((-3 / 200 : ℝ) + (-3 / 400 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((3 / 200 : ℝ) + (3 / 400 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_3_2]
                by_contra! failed
                have negative : 0 < ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ)) container_3
                have weighted_1 := mul_pos (by norm_num : 0 < (24 / 25 : ℝ)) branch_1_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (1 / 4 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + (24 / 25 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) = ((-23 / 100 : ℝ) + (-6 / 25 : ℝ) * Real.sqrt 2) := by
                  ring
                have constant_negative := (by positivity : 0 < ((23 / 100 : ℝ) + (6 / 25 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_2_0]
                by_contra! failed
                have negative : 0 < (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ)) container_2
                have weighted_1 := mul_pos (by positivity : 0 < ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_1_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (1 / 4 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) = ((-1 / 50 : ℝ) + (-13 / 50 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((1 / 50 : ℝ) + (13 / 50 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                rw [stepThree_area_0_7]
                exact branch_0
            ·
              have branch_12_negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [branch_12]
              apply stepThree_hit_boundary square fits 12
              rw [stepThree_boundary_12]
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_10_negative.le
              ·
                exact branch_9_negative.le
              ·
                exact branch_12_negative.le
      ·
        have branch_8_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_8]
        by_cases branch_13 : 0 ≤ ((-3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2))
        ·
          apply stepThree_hit_in_hull square
          ·
            rw [stepThree_area_7_6]
            by_contra! failed
            have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) branch_0
            have weighted_1 := mul_pos (by positivity : 0 < ((3 / 4 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_8_negative
            have weighted_2 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
            have identity : (3 / 100 : ℝ) * ((0 : ℝ) * square.center.x + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((3 / 4 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            rw [stepThree_area_6_5]
            by_contra! failed
            have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_pos (by positivity : 0 < ((3741 / 10000 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_8_negative
            have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) branch_13
            have weighted_2 := mul_pos (by positivity : 0 < ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
            have identity : ((3741 / 10000 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + (3 / 100 : ℝ) * ((-3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            rw [stepThree_area_5_4]
            exact branch_13
          ·
            rw [stepThree_area_4_3]
            by_contra! failed
            have negative : 0 < ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_pos (by positivity : 0 < ((3 / 100 : ℝ) + (3 / 200 : ℝ) * Real.sqrt 2)) branch_1_negative
            have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_13
            have weighted_2 := mul_pos (by positivity : 0 < ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
            have identity : ((3 / 100 : ℝ) + (3 / 200 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            rw [stepThree_area_3_2]
            by_contra! failed
            have negative : 0 < ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ)) container_3
            have weighted_1 := mul_pos (by norm_num : 0 < (24 / 25 : ℝ)) branch_1_negative
            have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
            have identity : (1 / 4 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + (24 / 25 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) = ((-23 / 100 : ℝ) + (-6 / 25 : ℝ) * Real.sqrt 2) := by
              ring
            have constant_negative := (by positivity : 0 < ((23 / 100 : ℝ) + (6 / 25 : ℝ) * Real.sqrt 2))
            nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
          ·
            rw [stepThree_area_2_0]
            by_contra! failed
            have negative : 0 < (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ)) container_2
            have weighted_1 := mul_pos (by positivity : 0 < ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_1_negative
            have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
            have identity : (1 / 4 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + (1 : ℝ) * (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) = ((-1 / 50 : ℝ) + (-13 / 50 : ℝ) * Real.sqrt 2) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            have constant_negative := (by positivity : 0 < ((1 / 50 : ℝ) + (13 / 50 : ℝ) * Real.sqrt 2))
            nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
          ·
            rw [stepThree_area_0_7]
            exact branch_0
        ·
          have branch_13_negative : 0 < ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [branch_13]
          apply stepThree_hit_boundary square fits 10
          rw [stepThree_boundary_10]
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_1_negative.le
          ·
            exact branch_8_negative.le
          ·
            exact branch_13_negative.le
  ·
    have branch_0_negative : 0 < ((0 : ℝ) * square.center.x + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_0]
    by_cases branch_14 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ))
    ·
      by_cases branch_15 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ))
      ·
        apply stepThree_hit_boundary square fits 0
        rw [stepThree_boundary_0]
        refine ⟨?_ , ?_ ⟩
        ·
          exact branch_15
        ·
          by_contra! failed
          have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
          have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
          have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
          have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
            ring
          nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_15_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [branch_15]
        by_cases branch_16 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (6 / 5 : ℝ))
        ·
          apply stepThree_hit_boundary square fits 4
          rw [stepThree_boundary_4]
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_15_negative.le
          ·
            exact branch_16
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-1 / 5 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_pos (by norm_num : 0 < (1 / 5 : ℝ)) branch_0_negative
            have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
            have identity : (1 / 5 : ℝ) * ((0 : ℝ) * square.center.x + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-1 / 5 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_16_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-6 / 5 : ℝ)) := by linarith only [branch_16]
          apply stepThree_hit_boundary square fits 5
          rw [stepThree_boundary_5]
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_16_negative.le
          ·
            exact branch_14
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) branch_0_negative
            have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
            have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
    ·
      have branch_14_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) := by linarith only [branch_14]
      by_cases branch_17 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
      ·
        apply stepThree_hit_boundary square fits 1
        rw [stepThree_boundary_1]
        refine ⟨?_ , ?_ ⟩
        ·
          exact branch_17
        ·
          by_contra! failed
          have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
          have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
          have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
          have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
            ring
          nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_17_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_17]
        apply stepThree_hit_boundary square fits 6
        rw [stepThree_boundary_6]
        refine ⟨?_ , ?_ , ?_ ⟩
        ·
          exact branch_14_negative.le
        ·
          exact branch_17_negative.le
        ·
          by_contra! failed
          have negative : 0 < ((0 : ℝ) * square.center.x + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
          have weighted_0 := mul_pos (by positivity : 0 < ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_0_negative
          have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
          have identity : ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
            ring
          nlinarith only [weighted_0, weighted_1, identity]

end SquarePackingArchive.Stromquist.TenPoints
