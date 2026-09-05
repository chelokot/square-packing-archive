import SquarePackingArchive.StromquistStepFour

namespace SquarePackingArchive.Stromquist.TenPoints

private lemma stepFour_area_9_3 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 9) (stepFourPoints 3) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((13 / 10 : ℝ) + (9 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_3_2 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 3) (stepFourPoints 2) square.center =
      ((24 / 25 : ℝ) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((-23 / 50 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_2_9 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 2) (stepFourPoints 9) square.center =
      (((-23 / 50 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (13 / 20 : ℝ) * square.center.y + ((-331 / 1000 : ℝ) + (-41 / 80 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_5_10 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 5) (stepFourPoints 10) square.center =
      (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((-9 / 20 : ℝ) + (-11 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_10_6 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 10) (stepFourPoints 6) square.center =
      ((0 : ℝ) * square.center.x + (43 / 100 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_6_5 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 6) (stepFourPoints 5) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_10_7 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 10) (stepFourPoints 7) square.center =
      (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((-33 / 20 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_7_6 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 7) (stepFourPoints 6) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_6_10 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 6) (stepFourPoints 10) square.center =
      ((0 : ℝ) * square.center.x + (-43 / 100 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_0_9 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 0) (stepFourPoints 9) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_9_2 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 9) (stepFourPoints 2) square.center =
      (((23 / 50 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-13 / 20 : ℝ) * square.center.y + ((331 / 1000 : ℝ) + (41 / 80 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_2_0 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 2) (stepFourPoints 0) square.center =
      (((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((-29 / 100 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_3_12 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 3) (stepFourPoints 12) square.center =
      ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-33 / 20 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_12_4 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 12) (stepFourPoints 4) square.center =
      ((-43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_4_3 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 4) (stepFourPoints 3) square.center =
      ((3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_12_3 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 12) (stepFourPoints 3) square.center =
      ((-2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((33 / 20 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_3_9 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 3) (stepFourPoints 9) square.center =
      (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((-13 / 10 : ℝ) + (-9 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_9_12 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 9) (stepFourPoints 12) square.center =
      (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_12_5 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 12) (stepFourPoints 5) square.center =
      ((-2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-9 / 20 : ℝ) + (-11 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_5_4 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 5) (stepFourPoints 4) square.center =
      ((-3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_4_12 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 4) (stepFourPoints 12) square.center =
      ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_12_10 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 12) (stepFourPoints 10) square.center =
      (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-137 / 200 : ℝ) + (-17 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_10_5 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 10) (stepFourPoints 5) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((9 / 20 : ℝ) + (11 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_5_12 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 5) (stepFourPoints 12) square.center =
      ((2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((9 / 20 : ℝ) + (11 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_10_8 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 10) (stepFourPoints 8) square.center =
      (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((2 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + (-7 / 5 : ℝ)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_8_7 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 8) (stepFourPoints 7) square.center =
      ((0 : ℝ) * square.center.x + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_7_10 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 7) (stepFourPoints 10) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((33 / 20 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_8_1 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 8) (stepFourPoints 1) square.center =
      ((1 / 10 : ℝ) * square.center.x + (3 / 25 : ℝ) * square.center.y + (-8 / 25 : ℝ)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_1_7 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 1) (stepFourPoints 7) square.center =
      ((-1 / 10 : ℝ) * square.center.x + ((-3 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((8 / 25 : ℝ) + (-9 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_7_8 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 7) (stepFourPoints 8) square.center =
      ((0 : ℝ) * square.center.x + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_0_11 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 0) (stepFourPoints 11) square.center =
      ((-2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_11_9 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 11) (stepFourPoints 9) square.center =
      (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((83 / 200 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_9_0 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 9) (stepFourPoints 0) square.center =
      (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_8_11 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 8) (stepFourPoints 11) square.center =
      ((-2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((13 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_11_0 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 11) (stepFourPoints 0) square.center =
      ((2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_0_8 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 0) (stepFourPoints 8) square.center =
      ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_11_8 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 11) (stepFourPoints 8) square.center =
      ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-13 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_8_10 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 8) (stepFourPoints 10) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-2 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + (7 / 5 : ℝ)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepFour_area_10_11 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 10) (stepFourPoints 11) square.center =
      (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_12_11 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 12) (stepFourPoints 11) square.center =
      (((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((-11 / 20 : ℝ) + (-4 / 5 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_11_10 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 11) (stepFourPoints 10) square.center =
      (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_10_12 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 10) (stepFourPoints 12) square.center =
      (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((137 / 200 : ℝ) + (17 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_11_12 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 11) (stepFourPoints 12) square.center =
      (((-1 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((11 / 20 : ℝ) + (4 / 5 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_12_9 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 12) (stepFourPoints 9) square.center =
      (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_area_9_11 (square : PlacedSquare) :
    Point.orientedArea (stepFourPoints 9) (stepFourPoints 11) square.center =
      (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-83 / 200 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepFourPoints, stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepFour_boundary_0 (square : PlacedSquare) :
    StepFourBoundaryRegion 0 square.center ↔ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by
  constructor <;> rintro ⟨part_0, part_1⟩ <;> repeat' apply And.intro
  all_goals nlinarith only [part_0, part_1, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepFour_boundary_1 (square : PlacedSquare) :
    StepFourBoundaryRegion 1 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by
  constructor <;> rintro ⟨part_0, part_1⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepFourBoundaryRegion, stepFourOldRegion, StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 ⊢
  all_goals nlinarith only [part_0, part_1, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepFour_boundary_2 (square : PlacedSquare) :
    StepFourBoundaryRegion 2 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepFourBoundaryRegion, stepFourOldRegion, StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 ⊢
  all_goals nlinarith only [part_0, part_1, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepFour_boundary_3 (square : PlacedSquare) :
    StepFourBoundaryRegion 3 square.center ↔ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepFourBoundaryRegion, stepFourOldRegion, StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 ⊢
  all_goals nlinarith only [part_0, part_1, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepFour_boundary_4 (square : PlacedSquare) :
    StepFourBoundaryRegion 4 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (53 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((-5 : ℝ) * square.center.x + (-6 : ℝ) * square.center.y + (16 : ℝ)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2, part_3⟩ <;> repeat' apply And.intro
  all_goals nlinarith only [part_0, part_1, part_2, part_3, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepFour_boundary_5 (square : PlacedSquare) :
    StepFourBoundaryRegion 5 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-53 / 25 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((1 / 10 : ℝ) * square.center.x + ((3 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-8 / 25 : ℝ) + (9 / 20 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepFourBoundaryRegion, stepFourOldRegion, StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepFour_boundary_6 (square : PlacedSquare) :
    StepFourBoundaryRegion 6 square.center ↔ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((26 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepFourBoundaryRegion, stepFourOldRegion, StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepFour_boundary_7 (square : PlacedSquare) :
    StepFourBoundaryRegion 7 square.center ↔ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-26 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepFourBoundaryRegion, stepFourOldRegion, StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepFour_boundary_8 (square : PlacedSquare) :
    StepFourBoundaryRegion 8 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepFourBoundaryRegion, stepFourOldRegion, StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepFour_boundary_9 (square : PlacedSquare) :
    StepFourBoundaryRegion 9 square.center ↔ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepFourBoundaryRegion, stepFourOldRegion, StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepFour_boundary_10 (square : PlacedSquare) :
    StepFourBoundaryRegion 10 square.center ↔ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepFourBoundaryRegion, stepFourOldRegion, StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private lemma stepFour_boundary_11 (square : PlacedSquare) :
    StepFourBoundaryRegion 11 square.center ↔ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) ∧ 0 ≤ (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by
  constructor <;> rintro ⟨part_0, part_1, part_2⟩ <;> repeat' apply And.intro
  all_goals dsimp -failIfUnchanged [StepFourBoundaryRegion, stepFourOldRegion, StepThreeBoundaryRegion, side, gap, Records.Square5.diagonal] at part_0 part_1 part_2 ⊢
  all_goals nlinarith only [part_0, part_1, part_2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

set_option maxHeartbeats 4000000 in
theorem stepFour_cover : ∀ square : PlacedSquare, square.Fits side → StepFourHit square := by
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
  by_cases branch_0 : 0 ≤ ((-43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2))
  ·
    by_cases branch_1 : 0 ≤ (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2))
    ·
      by_cases branch_2 : 0 ≤ (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((13 / 10 : ℝ) + (9 / 20 : ℝ) * Real.sqrt 2))
      ·
        by_cases branch_3 : 0 ≤ ((24 / 25 : ℝ) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((-23 / 50 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2))
        ·
          by_cases branch_4 : 0 ≤ (((-23 / 50 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (13 / 20 : ℝ) * square.center.y + ((-331 / 1000 : ℝ) + (-41 / 80 : ℝ) * Real.sqrt 2))
          ·
            apply stepFour_hit_triangle square 0
            · change 0 ≤ Point.orientedArea (stepFourPoints 9) (stepFourPoints 3) square.center
              rw [stepFour_area_9_3]
              exact branch_2
            · change 0 ≤ Point.orientedArea (stepFourPoints 3) (stepFourPoints 2) square.center
              rw [stepFour_area_3_2]
              exact branch_3
            · change 0 ≤ Point.orientedArea (stepFourPoints 2) (stepFourPoints 9) square.center
              rw [stepFour_area_2_9]
              exact branch_4
          ·
            have branch_4_negative : 0 < (((23 / 50 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-13 / 20 : ℝ) * square.center.y + ((331 / 1000 : ℝ) + (41 / 80 : ℝ) * Real.sqrt 2)) := by linarith only [branch_4]
            by_cases branch_5 : 0 ≤ (((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((-29 / 100 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
            ·
              apply stepFour_hit_triangle square 3
              · change 0 ≤ Point.orientedArea (stepFourPoints 0) (stepFourPoints 9) square.center
                rw [stepFour_area_0_9]
                by_contra! failed
                have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((2 / 5 : ℝ) + (1 / 5 : ℝ) * Real.sqrt 2)) branch_1
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) branch_2
                have weighted_2 := mul_pos (by positivity : 0 < ((43 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
                have identity : ((2 / 5 : ℝ) + (1 / 5 : ℝ) * Real.sqrt 2) * (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2)) + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((13 / 10 : ℝ) + (9 / 20 : ℝ) * Real.sqrt 2)) + ((43 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              · change 0 ≤ Point.orientedArea (stepFourPoints 9) (stepFourPoints 2) square.center
                rw [stepFour_area_9_2]
                exact branch_4_negative.le
              · change 0 ≤ Point.orientedArea (stepFourPoints 2) (stepFourPoints 0) square.center
                rw [stepFour_area_2_0]
                exact branch_5
            ·
              have branch_5_negative : 0 < (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_5]
              apply stepFour_hit_boundary square fits 6
              rw [stepFour_boundary_6]
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (24 / 25 : ℝ)) branch_1
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_3
                have weighted_2 := mul_pos (by positivity : 0 < ((71 / 1000 : ℝ) + (71 / 400 : ℝ) * Real.sqrt 2)) negative
                have identity : (24 / 25 : ℝ) * (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2)) + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((24 / 25 : ℝ) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((-23 / 50 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2)) + ((71 / 1000 : ℝ) + (71 / 400 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = ((-421 / 10000 : ℝ) + (27 / 1000 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 < ((421 / 10000 : ℝ) + (-27 / 1000 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-26 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_3
                have weighted_1 := mul_pos (by norm_num : 0 < (24 / 25 : ℝ)) branch_5_negative
                have weighted_2 := mul_pos (by positivity : 0 < ((1 / 4 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2)) negative
                have identity : ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((24 / 25 : ℝ) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((-23 / 50 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2)) + (24 / 25 : ℝ) * (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 / 4 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-26 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_5_negative.le
        ·
          have branch_3_negative : 0 < ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) := by linarith only [branch_3]
          by_cases branch_6 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
          ·
            apply stepFour_hit_boundary square fits 3
            rw [stepFour_boundary_3]
            refine ⟨?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ)) branch_2
              have weighted_1 := mul_pos (by norm_num : 0 < (2 / 5 : ℝ)) branch_3_negative
              have weighted_2 := mul_pos (by positivity : 0 < ((509 / 1000 : ℝ) + (1 / 16 : ℝ) * Real.sqrt 2)) negative
              have identity : (1 / 4 : ℝ) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((13 / 10 : ℝ) + (9 / 20 : ℝ) * Real.sqrt 2)) + (2 / 5 : ℝ) * ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) + ((509 / 1000 : ℝ) + (1 / 16 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_6
          ·
            have branch_6_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_6]
            by_cases branch_7 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((26 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2))
            ·
              by_cases branch_8 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
              ·
                apply stepFour_hit_boundary square fits 0
                rw [stepFour_boundary_0]
                refine ⟨?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_1
                  have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_8
                  have weighted_2 := mul_pos (by positivity : 0 < ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
                  have identity : (1 : ℝ) * (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2)) + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) = ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2) := by
                    ring
                  have constant_negative := (by positivity : 0 < ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_8
              ·
                have branch_8_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [branch_8]
                apply stepFour_hit_boundary square fits 6
                rw [stepFour_boundary_6]
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_8_negative.le
                ·
                  exact branch_7
                ·
                  by_contra! failed
                  have negative : 0 < (((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((-29 / 100 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by positivity : 0 < ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_3_negative
                  have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((1 / 4 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2)) branch_7
                  have weighted_2 := mul_pos (by norm_num : 0 < (24 / 25 : ℝ)) negative
                  have identity : ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((-24 / 25 : ℝ) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((23 / 50 : ℝ) + (-1 / 8 : ℝ) * Real.sqrt 2)) + ((1 / 4 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((26 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + (24 / 25 : ℝ) * (((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((-29 / 100 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_7_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-26 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_7]
              apply stepFour_hit_boundary square fits 7
              rw [stepFour_boundary_7]
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_7_negative.le
              ·
                exact branch_6_negative.le
              ·
                exact branch_3_negative.le
      ·
        have branch_2_negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((-13 / 10 : ℝ) + (-9 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_2]
        by_cases branch_9 : 0 ≤ ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-33 / 20 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2))
        ·
          by_cases branch_10 : 0 ≤ ((3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2))
          ·
            apply stepFour_hit_triangle square 4
            · change 0 ≤ Point.orientedArea (stepFourPoints 3) (stepFourPoints 12) square.center
              rw [stepFour_area_3_12]
              exact branch_9
            · change 0 ≤ Point.orientedArea (stepFourPoints 12) (stepFourPoints 4) square.center
              rw [stepFour_area_12_4]
              exact branch_0
            · change 0 ≤ Point.orientedArea (stepFourPoints 4) (stepFourPoints 3) square.center
              rw [stepFour_area_4_3]
              exact branch_10
          ·
            have branch_10_negative : 0 < ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_10]
            by_cases branch_11 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ))
            ·
              apply stepFour_hit_boundary square fits 3
              rw [stepFour_boundary_3]
              refine ⟨?_ , ?_ ⟩
              ·
                exact branch_11
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (3 / 100 : ℝ)) branch_2_negative
                have weighted_1 := mul_pos (by positivity : 0 < ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_10_negative
                have weighted_2 := mul_pos (by positivity : 0 < ((387 / 1000 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
                have identity : (3 / 100 : ℝ) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((-13 / 10 : ℝ) + (-9 / 20 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) + ((387 / 1000 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_11_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [branch_11]
              apply stepFour_hit_boundary square fits 8
              rw [stepFour_boundary_8]
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_11_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_0
                have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((-43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_10_negative.le
        ·
          have branch_9_negative : 0 < ((-2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((33 / 20 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_9]
          apply stepFour_hit_triangle square 5
          · change 0 ≤ Point.orientedArea (stepFourPoints 12) (stepFourPoints 3) square.center
            rw [stepFour_area_12_3]
            exact branch_9_negative.le
          · change 0 ≤ Point.orientedArea (stepFourPoints 3) (stepFourPoints 9) square.center
            rw [stepFour_area_3_9]
            exact branch_2_negative.le
          · change 0 ≤ Point.orientedArea (stepFourPoints 9) (stepFourPoints 12) square.center
            rw [stepFour_area_9_12]
            exact branch_1
    ·
      have branch_1_negative : 0 < (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_1]
      by_cases branch_12 : 0 ≤ (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((83 / 200 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2))
      ·
        by_cases branch_13 : 0 ≤ (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
        ·
          by_cases branch_14 : 0 ≤ (((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((-29 / 100 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
          ·
            apply stepFour_hit_triangle square 3
            · change 0 ≤ Point.orientedArea (stepFourPoints 0) (stepFourPoints 9) square.center
              rw [stepFour_area_0_9]
              exact branch_13
            · change 0 ≤ Point.orientedArea (stepFourPoints 9) (stepFourPoints 2) square.center
              rw [stepFour_area_9_2]
              by_contra! failed
              have negative : 0 < (((-23 / 50 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (13 / 20 : ℝ) * square.center.y + ((-331 / 1000 : ℝ) + (-41 / 80 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
              have weighted_0 := mul_pos (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 < ((-7 / 500 : ℝ) + (101 / 400 : ℝ) * Real.sqrt 2)) branch_1_negative
              have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((18 / 125 : ℝ) + (29 / 400 : ℝ) * Real.sqrt 2)) branch_12
              have weighted_2 := mul_pos (by positivity : 0 < ((27 / 100 : ℝ) + (1 / 10 : ℝ) * Real.sqrt 2)) negative
              have identity : ((-7 / 500 : ℝ) + (101 / 400 : ℝ) * Real.sqrt 2) * (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) + ((18 / 125 : ℝ) + (29 / 400 : ℝ) * Real.sqrt 2) * (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((83 / 200 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) + ((27 / 100 : ℝ) + (1 / 10 : ℝ) * Real.sqrt 2) * (((-23 / 50 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (13 / 20 : ℝ) * square.center.y + ((-331 / 1000 : ℝ) + (-41 / 80 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                ring_nf
                simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            · change 0 ≤ Point.orientedArea (stepFourPoints 2) (stepFourPoints 0) square.center
              rw [stepFour_area_2_0]
              exact branch_14
          ·
            have branch_14_negative : 0 < (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_14]
            by_cases branch_15 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ))
            ·
              apply stepFour_hit_boundary square fits 6
              rw [stepFour_boundary_6]
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_15
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-26 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_pos (by positivity : 0 < ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_1_negative
                have weighted_1 := mul_pos (by positivity : 0 < ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_14_negative
                have weighted_2 := mul_pos (by positivity : 0 < ((279 / 1000 : ℝ) + (49 / 400 : ℝ) * Real.sqrt 2)) negative
                have identity : ((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((279 / 1000 : ℝ) + (49 / 400 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-26 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) = ((-3913 / 50000 : ℝ) + (-749 / 10000 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by positivity : 0 < ((3913 / 50000 : ℝ) + (749 / 10000 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                exact branch_14_negative.le
            ·
              have branch_15_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [branch_15]
              apply stepFour_hit_boundary square fits 0
              rw [stepFour_boundary_0]
              refine ⟨?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 4 : ℝ)) branch_13
                have weighted_1 := mul_pos (by norm_num : 0 < (2 / 5 : ℝ)) branch_14_negative
                have weighted_2 := mul_pos (by positivity : 0 < ((141 / 1000 : ℝ) + (21 / 80 : ℝ) * Real.sqrt 2)) negative
                have identity : (1 / 4 : ℝ) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) + (2 / 5 : ℝ) * (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((29 / 100 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((141 / 1000 : ℝ) + (21 / 80 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_15_negative.le
        ·
          have branch_13_negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_13]
          by_cases branch_16 : 0 ≤ ((-2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2))
          ·
            apply stepFour_hit_triangle square 10
            · change 0 ≤ Point.orientedArea (stepFourPoints 0) (stepFourPoints 11) square.center
              rw [stepFour_area_0_11]
              exact branch_16
            · change 0 ≤ Point.orientedArea (stepFourPoints 11) (stepFourPoints 9) square.center
              rw [stepFour_area_11_9]
              exact branch_12
            · change 0 ≤ Point.orientedArea (stepFourPoints 9) (stepFourPoints 0) square.center
              rw [stepFour_area_9_0]
              exact branch_13_negative.le
          ·
            have branch_16_negative : 0 < ((2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_16]
            by_cases branch_17 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ))
            ·
              apply stepFour_hit_triangle square 11
              · change 0 ≤ Point.orientedArea (stepFourPoints 8) (stepFourPoints 11) square.center
                rw [stepFour_area_8_11]
                by_contra! failed
                have negative : 0 < ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-13 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (23 / 200 : ℝ)) branch_0
                have weighted_1 := mul_nonneg (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 ≤ ((43 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) branch_12
                have weighted_2 := mul_pos (by positivity : 0 < ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) negative
                have identity : (23 / 200 : ℝ) * ((-43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) + ((43 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2) * (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((83 / 200 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) + ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) * ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-13 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              · change 0 ≤ Point.orientedArea (stepFourPoints 11) (stepFourPoints 0) square.center
                rw [stepFour_area_11_0]
                exact branch_16_negative.le
              · change 0 ≤ Point.orientedArea (stepFourPoints 0) (stepFourPoints 8) square.center
                rw [stepFour_area_0_8]
                exact branch_17
            ·
              have branch_17_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [branch_17]
              by_cases branch_18 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ))
              ·
                apply stepFour_hit_boundary square fits 0
                rw [stepFour_boundary_0]
                refine ⟨?_ , ?_ ⟩
                ·
                  exact branch_18
                ·
                  exact branch_17_negative.le
              ·
                have branch_18_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [branch_18]
                apply stepFour_hit_boundary square fits 4
                rw [stepFour_boundary_4]
                refine ⟨?_ , ?_ , ?_ , ?_ ⟩
                ·
                  exact branch_18_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-53 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_0
                  have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
                  have identity : (1 : ℝ) * ((-43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-53 / 25 : ℝ)) = ((-1333 / 5000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) := by
                    ring
                  have constant_negative := (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 < ((1333 / 5000 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_17_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((5 : ℝ) * square.center.x + (6 : ℝ) * square.center.y + (-16 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (5 : ℝ)) branch_0
                  have weighted_1 := mul_pos (by norm_num : 0 < (129 / 50 : ℝ)) branch_17_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
                  have identity : (5 : ℝ) * ((-43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) + (129 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) + (43 / 100 : ℝ) * ((5 : ℝ) * square.center.x + (6 : ℝ) * square.center.y + (-16 : ℝ)) = ((-43 / 40 : ℝ) + (43 / 80 : ℝ) * Real.sqrt 2) := by
                    ring
                  have constant_negative := (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 < ((43 / 40 : ℝ) + (-43 / 80 : ℝ) * Real.sqrt 2))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
      ·
        have branch_12_negative : 0 < (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-83 / 200 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_12]
        apply stepFour_hit_triangle square 14
        · change 0 ≤ Point.orientedArea (stepFourPoints 11) (stepFourPoints 12) square.center
          rw [stepFour_area_11_12]
          by_contra! failed
          have negative : 0 < (((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((-11 / 20 : ℝ) + (-4 / 5 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
          have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_0
          have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
          have identity : ((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((-43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * (((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((-11 / 20 : ℝ) + (-4 / 5 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
            ring_nf
            simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
            ring
          nlinarith only [weighted_0, weighted_1, identity]
        · change 0 ≤ Point.orientedArea (stepFourPoints 12) (stepFourPoints 9) square.center
          rw [stepFour_area_12_9]
          exact branch_1_negative.le
        · change 0 ≤ Point.orientedArea (stepFourPoints 9) (stepFourPoints 11) square.center
          rw [stepFour_area_9_11]
          exact branch_12_negative.le
  ·
    have branch_0_negative : 0 < ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) := by linarith only [branch_0]
    by_cases branch_19 : 0 ≤ ((0 : ℝ) * square.center.x + (43 / 100 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2))
    ·
      by_cases branch_20 : 0 ≤ (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((-9 / 20 : ℝ) + (-11 / 20 : ℝ) * Real.sqrt 2))
      ·
        by_cases branch_21 : 0 ≤ (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2))
        ·
          apply stepFour_hit_triangle square 1
          · change 0 ≤ Point.orientedArea (stepFourPoints 5) (stepFourPoints 10) square.center
            rw [stepFour_area_5_10]
            exact branch_20
          · change 0 ≤ Point.orientedArea (stepFourPoints 10) (stepFourPoints 6) square.center
            rw [stepFour_area_10_6]
            exact branch_19
          · change 0 ≤ Point.orientedArea (stepFourPoints 6) (stepFourPoints 5) square.center
            rw [stepFour_area_6_5]
            exact branch_21
        ·
          have branch_21_negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [branch_21]
          by_cases branch_22 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
          ·
            apply stepFour_hit_boundary square fits 2
            rw [stepFour_boundary_2]
            refine ⟨?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) branch_20
              have weighted_1 := mul_pos (by norm_num : 0 < (2 / 5 : ℝ)) branch_21_negative
              have weighted_2 := mul_pos (by positivity : 0 < ((43 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) negative
              have identity : (3 / 100 : ℝ) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((-9 / 20 : ℝ) + (-11 / 20 : ℝ) * Real.sqrt 2)) + (2 / 5 : ℝ) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) + ((43 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                ring_nf
                simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_22
          ·
            have branch_22_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_22]
            apply stepFour_hit_boundary square fits 11
            rw [stepFour_boundary_11]
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_19
              have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (43 / 100 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_22_negative.le
            ·
              exact branch_21_negative.le
      ·
        have branch_20_negative : 0 < (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((9 / 20 : ℝ) + (11 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_20]
        by_cases branch_23 : 0 ≤ ((-2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-9 / 20 : ℝ) + (-11 / 20 : ℝ) * Real.sqrt 2))
        ·
          by_cases branch_24 : 0 ≤ ((-3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2))
          ·
            apply stepFour_hit_triangle square 6
            · change 0 ≤ Point.orientedArea (stepFourPoints 12) (stepFourPoints 5) square.center
              rw [stepFour_area_12_5]
              exact branch_23
            · change 0 ≤ Point.orientedArea (stepFourPoints 5) (stepFourPoints 4) square.center
              rw [stepFour_area_5_4]
              exact branch_24
            · change 0 ≤ Point.orientedArea (stepFourPoints 4) (stepFourPoints 12) square.center
              rw [stepFour_area_4_12]
              exact branch_0_negative.le
          ·
            have branch_24_negative : 0 < ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) := by linarith only [branch_24]
            by_cases branch_25 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
            ·
              apply stepFour_hit_boundary square fits 2
              rw [stepFour_boundary_2]
              refine ⟨?_ , ?_ ⟩
              ·
                exact branch_25
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (3 / 100 : ℝ)) branch_20_negative
                have weighted_1 := mul_pos (by positivity : 0 < ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) branch_24_negative
                have weighted_2 := mul_pos (by positivity : 0 < ((387 / 1000 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
                have identity : (3 / 100 : ℝ) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((9 / 20 : ℝ) + (11 / 20 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((3 / 100 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-131 / 100 : ℝ) + (-153 / 200 : ℝ) * Real.sqrt 2)) + ((387 / 1000 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_25_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_25]
              apply stepFour_hit_boundary square fits 9
              rw [stepFour_boundary_9]
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((3 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_25_negative.le
              ·
                exact branch_24_negative.le
        ·
          have branch_23_negative : 0 < ((2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((9 / 20 : ℝ) + (11 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_23]
          by_cases branch_26 : 0 ≤ (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-137 / 200 : ℝ) + (-17 / 20 : ℝ) * Real.sqrt 2))
          ·
            apply stepFour_hit_triangle square 7
            · change 0 ≤ Point.orientedArea (stepFourPoints 12) (stepFourPoints 10) square.center
              rw [stepFour_area_12_10]
              exact branch_26
            · change 0 ≤ Point.orientedArea (stepFourPoints 10) (stepFourPoints 5) square.center
              rw [stepFour_area_10_5]
              exact branch_20_negative.le
            · change 0 ≤ Point.orientedArea (stepFourPoints 5) (stepFourPoints 12) square.center
              rw [stepFour_area_5_12]
              exact branch_23_negative.le
          ·
            have branch_26_negative : 0 < (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((137 / 200 : ℝ) + (17 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_26]
            apply stepFour_hit_triangle square 13
            · change 0 ≤ Point.orientedArea (stepFourPoints 12) (stepFourPoints 11) square.center
              rw [stepFour_area_12_11]
              by_contra! failed
              have negative : 0 < (((-1 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((11 / 20 : ℝ) + (4 / 5 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
              have weighted_0 := mul_pos (by positivity : 0 < ((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_0_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
              have identity : ((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * (((-1 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((11 / 20 : ℝ) + (4 / 5 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                ring_nf
                simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            · change 0 ≤ Point.orientedArea (stepFourPoints 11) (stepFourPoints 10) square.center
              rw [stepFour_area_11_10]
              by_contra! failed
              have negative : 0 < (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) branch_19
              have weighted_1 := mul_pos (by positivity : 0 < ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) branch_20_negative
              have weighted_2 := mul_pos (by positivity : 0 < ((43 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) negative
              have identity : ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (43 / 100 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) + ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((9 / 20 : ℝ) + (11 / 20 : ℝ) * Real.sqrt 2)) + ((43 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) * (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                ring_nf
                simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            · change 0 ≤ Point.orientedArea (stepFourPoints 10) (stepFourPoints 12) square.center
              rw [stepFour_area_10_12]
              exact branch_26_negative.le
    ·
      have branch_19_negative : 0 < ((0 : ℝ) * square.center.x + (-43 / 100 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) := by linarith only [branch_19]
      by_cases branch_27 : 0 ≤ (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((2 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + (-7 / 5 : ℝ))
      ·
        by_cases branch_28 : 0 ≤ ((0 : ℝ) * square.center.x + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
        ·
          by_cases branch_29 : 0 ≤ (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((-33 / 20 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2))
          ·
            by_cases branch_30 : 0 ≤ (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2))
            ·
              apply stepFour_hit_triangle square 2
              · change 0 ≤ Point.orientedArea (stepFourPoints 10) (stepFourPoints 7) square.center
                rw [stepFour_area_10_7]
                exact branch_29
              · change 0 ≤ Point.orientedArea (stepFourPoints 7) (stepFourPoints 6) square.center
                rw [stepFour_area_7_6]
                exact branch_30
              · change 0 ≤ Point.orientedArea (stepFourPoints 6) (stepFourPoints 10) square.center
                rw [stepFour_area_6_10]
                exact branch_19_negative.le
            ·
              have branch_30_negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_30]
              apply stepFour_hit_boundary square fits 10
              rw [stepFour_boundary_10]
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_28
                have weighted_1 := mul_pos (by positivity : 0 < ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_19_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-43 / 100 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + ((-3 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_30_negative.le
          ·
            have branch_29_negative : 0 < (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((33 / 20 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_29]
            apply stepFour_hit_triangle square 8
            · change 0 ≤ Point.orientedArea (stepFourPoints 10) (stepFourPoints 8) square.center
              rw [stepFour_area_10_8]
              exact branch_27
            · change 0 ≤ Point.orientedArea (stepFourPoints 8) (stepFourPoints 7) square.center
              rw [stepFour_area_8_7]
              exact branch_28
            · change 0 ≤ Point.orientedArea (stepFourPoints 7) (stepFourPoints 10) square.center
              rw [stepFour_area_7_10]
              exact branch_29_negative.le
        ·
          have branch_28_negative : 0 < ((0 : ℝ) * square.center.x + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_28]
          by_cases branch_31 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-2 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
          ·
            apply stepFour_hit_boundary square fits 1
            rw [stepFour_boundary_1]
            refine ⟨?_ , ?_ ⟩
            ·
              exact branch_31
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_28_negative
              have weighted_1 := mul_pos (by positivity : 0 < ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_31_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((2 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_31]
            by_cases branch_32 : 0 ≤ ((-1 / 10 : ℝ) * square.center.x + ((-3 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((8 / 25 : ℝ) + (-9 / 20 : ℝ) * Real.sqrt 2))
            ·
              by_cases branch_33 : 0 ≤ ((1 / 10 : ℝ) * square.center.x + (3 / 25 : ℝ) * square.center.y + (-8 / 25 : ℝ))
              ·
                apply stepFour_hit_triangle square 9
                · change 0 ≤ Point.orientedArea (stepFourPoints 8) (stepFourPoints 1) square.center
                  rw [stepFour_area_8_1]
                  exact branch_33
                · change 0 ≤ Point.orientedArea (stepFourPoints 1) (stepFourPoints 7) square.center
                  rw [stepFour_area_1_7]
                  exact branch_32
                · change 0 ≤ Point.orientedArea (stepFourPoints 7) (stepFourPoints 8) square.center
                  rw [stepFour_area_7_8]
                  exact branch_28_negative.le
              ·
                have branch_33_negative : 0 < ((-1 / 10 : ℝ) * square.center.x + (-3 / 25 : ℝ) * square.center.y + (8 / 25 : ℝ)) := by linarith only [branch_33]
                apply stepFour_hit_boundary square fits 4
                rw [stepFour_boundary_4]
                refine ⟨?_ , ?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
                  have identity : (1 : ℝ) * ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = ((-43 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2) := by
                    ring
                  have constant_negative := (by positivity : 0 < ((43 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-53 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 25 : ℝ)) branch_32
                  have weighted_1 := mul_pos (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 < ((-3 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_33_negative
                  have weighted_2 := mul_pos (by positivity : 0 < ((0 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) negative
                  have identity : (3 / 25 : ℝ) * ((-1 / 10 : ℝ) * square.center.x + ((-3 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((8 / 25 : ℝ) + (-9 / 20 : ℝ) * Real.sqrt 2)) + ((-3 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((-1 / 10 : ℝ) * square.center.x + (-3 / 25 : ℝ) * square.center.y + (8 / 25 : ℝ)) + ((0 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-53 / 25 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_28_negative
                  have weighted_1 := mul_pos (by positivity : 0 < ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((5 : ℝ) * square.center.x + (6 : ℝ) * square.center.y + (-16 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (5 : ℝ)) branch_33_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 / 10 : ℝ)) negative
                  have identity : (5 : ℝ) * ((-1 / 10 : ℝ) * square.center.x + (-3 / 25 : ℝ) * square.center.y + (8 / 25 : ℝ)) + (1 / 10 : ℝ) * ((5 : ℝ) * square.center.x + (6 : ℝ) * square.center.y + (-16 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_32_negative : 0 < ((1 / 10 : ℝ) * square.center.x + ((3 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-8 / 25 : ℝ) + (9 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_32]
              by_cases branch_34 : 0 ≤ (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2))
              ·
                by_cases branch_35 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (53 / 25 : ℝ))
                ·
                  apply stepFour_hit_boundary square fits 4
                  rw [stepFour_boundary_4]
                  refine ⟨?_ , ?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
                    have identity : (1 : ℝ) * ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = ((-43 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2) := by
                      ring
                    have constant_negative := (by positivity : 0 < ((43 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_35
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_28_negative
                    have weighted_1 := mul_pos (by positivity : 0 < ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((5 : ℝ) * square.center.x + (6 : ℝ) * square.center.y + (-16 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (6 : ℝ)) branch_32_negative
                    have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((0 : ℝ) + (5 / 2 : ℝ) * Real.sqrt 2)) branch_35
                    have weighted_2 := mul_pos (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 < ((-3 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
                    have identity : (6 : ℝ) * ((1 / 10 : ℝ) * square.center.x + ((3 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-8 / 25 : ℝ) + (9 / 20 : ℝ) * Real.sqrt 2)) + ((0 : ℝ) + (5 / 2 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (53 / 25 : ℝ)) + ((-3 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((5 : ℝ) * square.center.x + (6 : ℝ) * square.center.y + (-16 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  have branch_35_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-53 / 25 : ℝ)) := by linarith only [branch_35]
                  apply stepFour_hit_boundary square fits 5
                  rw [stepFour_boundary_5]
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_35_negative.le
                  ·
                    exact branch_31_negative.le
                  ·
                    exact branch_32_negative.le
              ·
                have branch_34_negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_34]
                apply stepFour_hit_boundary square fits 5
                rw [stepFour_boundary_5]
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (53 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_2
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_34_negative
                  have weighted_2 := mul_pos (by positivity : 0 < ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
                  have identity : (3 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + (1 : ℝ) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((-61 / 50 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (53 / 25 : ℝ)) = ((-4 / 25 : ℝ) + (-11 / 50 : ℝ) * Real.sqrt 2) := by
                    ring
                  have constant_negative := (by positivity : 0 < ((4 / 25 : ℝ) + (11 / 50 : ℝ) * Real.sqrt 2))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_31_negative.le
                ·
                  exact branch_32_negative.le
      ·
        have branch_27_negative : 0 < (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-2 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + (7 / 5 : ℝ)) := by linarith only [branch_27]
        by_cases branch_36 : 0 ≤ (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2))
        ·
          by_cases branch_37 : 0 ≤ ((-2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((13 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2))
          ·
            by_cases branch_38 : 0 ≤ ((0 : ℝ) * square.center.x + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2))
            ·
              apply stepFour_hit_triangle square 11
              · change 0 ≤ Point.orientedArea (stepFourPoints 8) (stepFourPoints 11) square.center
                rw [stepFour_area_8_11]
                exact branch_37
              · change 0 ≤ Point.orientedArea (stepFourPoints 11) (stepFourPoints 0) square.center
                rw [stepFour_area_11_0]
                by_contra! failed
                have negative : 0 < ((-2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (2 / 5 : ℝ)) branch_0_negative
                have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((43 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) branch_37
                have weighted_2 := mul_pos (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 < ((43 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) negative
                have identity : (2 / 5 : ℝ) * ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) + ((43 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) * ((-2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((13 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + ((43 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2) * ((-2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              · change 0 ≤ Point.orientedArea (stepFourPoints 0) (stepFourPoints 8) square.center
                rw [stepFour_area_0_8]
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_38
                have weighted_1 := mul_pos (by positivity : 0 < ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_38_negative : 0 < ((0 : ℝ) * square.center.x + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [branch_38]
              apply stepFour_hit_boundary square fits 4
              rw [stepFour_boundary_4]
              refine ⟨?_ , ?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = ((-43 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2) := by
                  ring
                have constant_negative := (by positivity : 0 < ((43 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-53 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 < ((1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) branch_27_negative
                have weighted_1 := mul_nonneg (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 ≤ ((-2 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_37
                have weighted_2 := mul_pos (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 < ((-7 / 200 : ℝ) + (1 / 5 : ℝ) * Real.sqrt 2)) negative
                have identity : ((1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-2 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + (7 / 5 : ℝ)) + ((-2 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((-2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((13 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + ((-7 / 200 : ℝ) + (1 / 5 : ℝ) * Real.sqrt 2) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-53 / 25 : ℝ)) = ((21 / 5000 : ℝ) + (-3 / 125 : ℝ) * Real.sqrt 2) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                have constant_negative := (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 < ((-21 / 5000 : ℝ) + (3 / 125 : ℝ) * Real.sqrt 2))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_38_negative
                have weighted_1 := mul_pos (by positivity : 0 < ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((5 : ℝ) * square.center.x + (6 : ℝ) * square.center.y + (-16 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by positivity : 0 < ((0 : ℝ) + (5 / 2 : ℝ) * Real.sqrt 2)) branch_27_negative
                have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (4 : ℝ) * Real.sqrt 2)) branch_38_negative
                have weighted_2 := mul_pos (by positivity : 0 < ((1 / 4 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
                have identity : ((0 : ℝ) + (5 / 2 : ℝ) * Real.sqrt 2) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-2 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + (7 / 5 : ℝ)) + ((1 : ℝ) + (4 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) + ((1 / 4 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * ((5 : ℝ) * square.center.x + (6 : ℝ) * square.center.y + (-16 : ℝ)) = (0 : ℝ) := by
                  ring_nf
                  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_37_negative : 0 < ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-13 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_37]
            apply stepFour_hit_triangle square 12
            · change 0 ≤ Point.orientedArea (stepFourPoints 11) (stepFourPoints 8) square.center
              rw [stepFour_area_11_8]
              exact branch_37_negative.le
            · change 0 ≤ Point.orientedArea (stepFourPoints 8) (stepFourPoints 10) square.center
              rw [stepFour_area_8_10]
              exact branch_27_negative.le
            · change 0 ≤ Point.orientedArea (stepFourPoints 10) (stepFourPoints 11) square.center
              rw [stepFour_area_10_11]
              exact branch_36
        ·
          have branch_36_negative : 0 < (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_36]
          apply stepFour_hit_triangle square 13
          · change 0 ≤ Point.orientedArea (stepFourPoints 12) (stepFourPoints 11) square.center
            rw [stepFour_area_12_11]
            by_contra! failed
            have negative : 0 < (((-1 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((11 / 20 : ℝ) + (4 / 5 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_pos (by positivity : 0 < ((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_0_negative
            have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
            have identity : ((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * (((-1 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((11 / 20 : ℝ) + (4 / 5 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          · change 0 ≤ Point.orientedArea (stepFourPoints 11) (stepFourPoints 10) square.center
            rw [stepFour_area_11_10]
            exact branch_36_negative.le
          · change 0 ≤ Point.orientedArea (stepFourPoints 10) (stepFourPoints 12) square.center
            rw [stepFour_area_10_12]
            by_contra! failed
            have negative : 0 < (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-137 / 200 : ℝ) + (-17 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_pos (by positivity : 0 < ((77 / 200 : ℝ) + (1 / 10 : ℝ) * Real.sqrt 2)) branch_19_negative
            have weighted_1 := mul_pos (by positivity : 0 < ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) branch_27_negative
            have weighted_2 := mul_pos (by positivity : 0 < ((43 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) negative
            have identity : ((77 / 200 : ℝ) + (1 / 10 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-43 / 100 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) + ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-2 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + (7 / 5 : ℝ)) + ((43 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) * (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-137 / 200 : ℝ) + (-17 / 20 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]

end SquarePackingArchive.Stromquist.TenPoints
