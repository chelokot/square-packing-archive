import SquarePackingArchive.StromquistTenReplacementPoints

namespace SquarePackingArchive.Stromquist.TenPoints

private lemma stepThree_area_9_3 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 9) (stepThreePoints 3) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((13 / 10 : ℝ) + (9 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_3_2 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 3) (stepThreePoints 2) square.center =
      ((24 / 25 : ℝ) * square.center.x + (-1 / 4 : ℝ) * square.center.y + ((-23 / 50 : ℝ) + (1 / 8 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_2_9 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 2) (stepThreePoints 9) square.center =
      (((-23 / 50 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (13 / 20 : ℝ) * square.center.y + ((-331 / 1000 : ℝ) + (-41 / 80 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_5_10 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 5) (stepThreePoints 10) square.center =
      (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((-9 / 20 : ℝ) + (-11 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_10_6 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 10) (stepThreePoints 6) square.center =
      ((0 : ℝ) * square.center.x + (43 / 100 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_6_5 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 6) (stepThreePoints 5) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-3 / 100 : ℝ) * square.center.y + ((131 / 100 : ℝ) + (153 / 200 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_10_7 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 10) (stepThreePoints 7) square.center =
      (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((-33 / 20 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_7_6 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 7) (stepThreePoints 6) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (3 / 100 : ℝ) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_6_10 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 6) (stepThreePoints 10) square.center =
      ((0 : ℝ) * square.center.x + (-43 / 100 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_3_12 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 3) (stepThreePoints 12) square.center =
      ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-33 / 20 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_12_4 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 12) (stepThreePoints 4) square.center =
      ((-43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_4_3 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 4) (stepThreePoints 3) square.center =
      ((3 / 100 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((61 / 50 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_12_3 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 12) (stepThreePoints 3) square.center =
      ((-2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((33 / 20 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_3_9 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 3) (stepThreePoints 9) square.center =
      (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((-13 / 10 : ℝ) + (-9 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_9_12 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 9) (stepThreePoints 12) square.center =
      (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_12_5 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 12) (stepThreePoints 5) square.center =
      ((-2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-9 / 20 : ℝ) + (-11 / 20 : ℝ) * Real.sqrt 2)) := by
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

private lemma stepThree_area_4_12 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 4) (stepThreePoints 12) square.center =
      ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_12_10 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 12) (stepThreePoints 10) square.center =
      (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-137 / 200 : ℝ) + (-17 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_10_5 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 10) (stepThreePoints 5) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((9 / 20 : ℝ) + (11 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_5_12 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 5) (stepThreePoints 12) square.center =
      ((2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((9 / 20 : ℝ) + (11 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_10_8 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 10) (stepThreePoints 8) square.center =
      (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((2 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + (-7 / 5 : ℝ)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_8_7 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 8) (stepThreePoints 7) square.center =
      ((0 : ℝ) * square.center.x + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_7_10 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 7) (stepThreePoints 10) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((33 / 20 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_11_8 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 11) (stepThreePoints 8) square.center =
      ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-13 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_8_10 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 8) (stepThreePoints 10) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-2 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + (7 / 5 : ℝ)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_10_11 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 10) (stepThreePoints 11) square.center =
      (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_11_1 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 11) (stepThreePoints 1) square.center =
      ((2 / 5 : ℝ) * square.center.x + ((-3 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-9 / 50 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_1_8 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 1) (stepThreePoints 8) square.center =
      ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_8_11 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 8) (stepThreePoints 11) square.center =
      ((-2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((13 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_1_11 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 1) (stepThreePoints 11) square.center =
      ((-2 / 5 : ℝ) * square.center.x + ((3 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((9 / 50 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_11_9 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 11) (stepThreePoints 9) square.center =
      (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((83 / 200 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_9_1 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 9) (stepThreePoints 1) square.center =
      (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 5 : ℝ) * square.center.y + ((-2 / 5 : ℝ) + (-3 / 10 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_1_9 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 1) (stepThreePoints 9) square.center =
      (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 5 : ℝ) * square.center.y + ((2 / 5 : ℝ) + (3 / 10 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_9_2 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 9) (stepThreePoints 2) square.center =
      (((23 / 50 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-13 / 20 : ℝ) * square.center.y + ((331 / 1000 : ℝ) + (41 / 80 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_2_1 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 2) (stepThreePoints 1) square.center =
      (((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (9 / 20 : ℝ) * square.center.y + ((-249 / 500 : ℝ) + (-3 / 5 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_0_1 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 0) (stepThreePoints 1) square.center =
      ((0 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-1 / 5 : ℝ)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_1_2 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 1) (stepThreePoints 2) square.center =
      (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-9 / 20 : ℝ) * square.center.y + ((249 / 500 : ℝ) + (3 / 5 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_2_0 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 2) (stepThreePoints 0) square.center =
      (((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 4 : ℝ) * square.center.y + ((-29 / 100 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

private lemma stepThree_area_12_11 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 12) (stepThreePoints 11) square.center =
      (((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((-11 / 20 : ℝ) + (-4 / 5 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_11_10 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 11) (stepThreePoints 10) square.center =
      (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_10_12 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 10) (stepThreePoints 12) square.center =
      (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((137 / 200 : ℝ) + (17 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_11_12 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 11) (stepThreePoints 12) square.center =
      (((-1 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((11 / 20 : ℝ) + (4 / 5 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_12_9 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 12) (stepThreePoints 9) square.center =
      (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_9_11 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 9) (stepThreePoints 11) square.center =
      (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-83 / 200 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring_nf
  simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  ring

private lemma stepThree_area_0_7 (square : PlacedSquare) :
    Point.orientedArea (stepThreePoints 0) (stepThreePoints 7) square.center =
      ((0 : ℝ) * square.center.x + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) := by
  norm_num [stepThreePoints, points, leftReplacement, Point.swap, Point.orientedArea,
    side, gap, Records.Square5.diagonal]
  ring

set_option maxHeartbeats 4000000 in
theorem stepThree_hit_in_hull (square : PlacedSquare)
    (hull_0 : 0 ≤ Point.orientedArea (stepThreePoints 7) (stepThreePoints 6) square.center)
    (hull_1 : 0 ≤ Point.orientedArea (stepThreePoints 6) (stepThreePoints 5) square.center)
    (hull_2 : 0 ≤ Point.orientedArea (stepThreePoints 5) (stepThreePoints 4) square.center)
    (hull_3 : 0 ≤ Point.orientedArea (stepThreePoints 4) (stepThreePoints 3) square.center)
    (hull_4 : 0 ≤ Point.orientedArea (stepThreePoints 3) (stepThreePoints 2) square.center)
    (hull_5 : 0 ≤ Point.orientedArea (stepThreePoints 2) (stepThreePoints 0) square.center)
    (hull_6 : 0 ≤ Point.orientedArea (stepThreePoints 0) (stepThreePoints 7) square.center)
    : ∃ index, square.Contains (stepThreePoints index) := by
  rw [stepThree_area_7_6] at hull_0
  rw [stepThree_area_6_5] at hull_1
  rw [stepThree_area_5_4] at hull_2
  rw [stepThree_area_4_3] at hull_3
  rw [stepThree_area_3_2] at hull_4
  rw [stepThree_area_2_0] at hull_5
  rw [stepThree_area_0_7] at hull_6
  by_cases branch_0 : 0 ≤ ((-43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2))
  ·
    by_cases branch_1 : 0 ≤ (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((83 / 200 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2))
    ·
      by_cases branch_2 : 0 ≤ (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-1 / 5 : ℝ) * square.center.y + ((-2 / 5 : ℝ) + (-3 / 10 : ℝ) * Real.sqrt 2))
      ·
        by_cases branch_3 : 0 ≤ ((2 / 5 : ℝ) * square.center.x + ((-3 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-9 / 50 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
        ·
          apply stepThree_hit_triangle square 9
          · change 0 ≤ Point.orientedArea (stepThreePoints 11) (stepThreePoints 1) square.center
            rw [stepThree_area_11_1]
            exact branch_3
          · change 0 ≤ Point.orientedArea (stepThreePoints 1) (stepThreePoints 8) square.center
            rw [stepThree_area_1_8]
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (4 / 5 : ℝ)) hull_6
            have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
            have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          · change 0 ≤ Point.orientedArea (stepThreePoints 8) (stepThreePoints 11) square.center
            rw [stepThree_area_8_11]
            by_contra! failed
            have negative : 0 < ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-13 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (23 / 200 : ℝ)) branch_0
            have weighted_1 := mul_nonneg (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 ≤ ((43 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) branch_1
            have weighted_2 := mul_pos (by positivity : 0 < ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) negative
            have identity : (23 / 200 : ℝ) * ((-43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) + ((43 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2) * (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((83 / 200 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) + ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) * ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-13 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]
        ·
          have branch_3_negative : 0 < ((-2 / 5 : ℝ) * square.center.x + ((3 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((9 / 50 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_3]
          apply stepThree_hit_triangle square 10
          · change 0 ≤ Point.orientedArea (stepThreePoints 1) (stepThreePoints 11) square.center
            rw [stepThree_area_1_11]
            exact branch_3_negative.le
          · change 0 ≤ Point.orientedArea (stepThreePoints 11) (stepThreePoints 9) square.center
            rw [stepThree_area_11_9]
            exact branch_1
          · change 0 ≤ Point.orientedArea (stepThreePoints 9) (stepThreePoints 1) square.center
            rw [stepThree_area_9_1]
            exact branch_2
      ·
        have branch_2_negative : 0 < (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 5 : ℝ) * square.center.y + ((2 / 5 : ℝ) + (3 / 10 : ℝ) * Real.sqrt 2)) := by linarith only [branch_2]
        by_cases branch_4 : 0 ≤ (((-23 / 50 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (13 / 20 : ℝ) * square.center.y + ((-331 / 1000 : ℝ) + (-41 / 80 : ℝ) * Real.sqrt 2))
        ·
          apply stepThree_hit_triangle square 0
          · change 0 ≤ Point.orientedArea (stepThreePoints 9) (stepThreePoints 3) square.center
            rw [stepThree_area_9_3]
            by_contra! failed
            have negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((-13 / 10 : ℝ) + (-9 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((3 / 10 : ℝ) + (3 / 20 : ℝ) * Real.sqrt 2)) branch_1
            have weighted_1 := mul_pos (by positivity : 0 < ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) branch_2_negative
            have weighted_2 := mul_pos (by positivity : 0 < ((39 / 200 : ℝ) + (1 / 5 : ℝ) * Real.sqrt 2)) negative
            have identity : ((3 / 10 : ℝ) + (3 / 20 : ℝ) * Real.sqrt 2) * (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((83 / 200 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (1 / 5 : ℝ) * square.center.y + ((2 / 5 : ℝ) + (3 / 10 : ℝ) * Real.sqrt 2)) + ((39 / 200 : ℝ) + (1 / 5 : ℝ) * Real.sqrt 2) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((-13 / 10 : ℝ) + (-9 / 20 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          · change 0 ≤ Point.orientedArea (stepThreePoints 3) (stepThreePoints 2) square.center
            rw [stepThree_area_3_2]
            exact hull_4
          · change 0 ≤ Point.orientedArea (stepThreePoints 2) (stepThreePoints 9) square.center
            rw [stepThree_area_2_9]
            exact branch_4
        ·
          have branch_4_negative : 0 < (((23 / 50 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-13 / 20 : ℝ) * square.center.y + ((331 / 1000 : ℝ) + (41 / 80 : ℝ) * Real.sqrt 2)) := by linarith only [branch_4]
          by_cases branch_5 : 0 ≤ (((1 / 25 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (9 / 20 : ℝ) * square.center.y + ((-249 / 500 : ℝ) + (-3 / 5 : ℝ) * Real.sqrt 2))
          ·
            apply stepThree_hit_triangle square 11
            · change 0 ≤ Point.orientedArea (stepThreePoints 1) (stepThreePoints 9) square.center
              rw [stepThree_area_1_9]
              exact branch_2_negative.le
            · change 0 ≤ Point.orientedArea (stepThreePoints 9) (stepThreePoints 2) square.center
              rw [stepThree_area_9_2]
              exact branch_4_negative.le
            · change 0 ≤ Point.orientedArea (stepThreePoints 2) (stepThreePoints 1) square.center
              rw [stepThree_area_2_1]
              exact branch_5
          ·
            have branch_5_negative : 0 < (((-1 / 25 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (-9 / 20 : ℝ) * square.center.y + ((249 / 500 : ℝ) + (3 / 5 : ℝ) * Real.sqrt 2)) := by linarith only [branch_5]
            apply stepThree_hit_triangle square 12
            · change 0 ≤ Point.orientedArea (stepThreePoints 0) (stepThreePoints 1) square.center
              rw [stepThree_area_0_1]
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (1 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 5 : ℝ)) hull_6
              have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
              have identity : (1 / 5 : ℝ) * ((0 : ℝ) * square.center.x + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (1 / 5 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            · change 0 ≤ Point.orientedArea (stepThreePoints 1) (stepThreePoints 2) square.center
              rw [stepThree_area_1_2]
              exact branch_5_negative.le
            · change 0 ≤ Point.orientedArea (stepThreePoints 2) (stepThreePoints 0) square.center
              rw [stepThree_area_2_0]
              exact hull_5
    ·
      have branch_1_negative : 0 < (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-83 / 200 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_1]
      by_cases branch_6 : 0 ≤ (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2))
      ·
        by_cases branch_7 : 0 ≤ ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-33 / 20 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2))
        ·
          apply stepThree_hit_triangle square 3
          · change 0 ≤ Point.orientedArea (stepThreePoints 3) (stepThreePoints 12) square.center
            rw [stepThree_area_3_12]
            exact branch_7
          · change 0 ≤ Point.orientedArea (stepThreePoints 12) (stepThreePoints 4) square.center
            rw [stepThree_area_12_4]
            exact branch_0
          · change 0 ≤ Point.orientedArea (stepThreePoints 4) (stepThreePoints 3) square.center
            rw [stepThree_area_4_3]
            exact hull_3
        ·
          have branch_7_negative : 0 < ((-2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((33 / 20 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_7]
          by_cases branch_8 : 0 ≤ (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((13 / 10 : ℝ) + (9 / 20 : ℝ) * Real.sqrt 2))
          ·
            apply stepThree_hit_triangle square 0
            · change 0 ≤ Point.orientedArea (stepThreePoints 9) (stepThreePoints 3) square.center
              rw [stepThree_area_9_3]
              exact branch_8
            · change 0 ≤ Point.orientedArea (stepThreePoints 3) (stepThreePoints 2) square.center
              rw [stepThree_area_3_2]
              exact hull_4
            · change 0 ≤ Point.orientedArea (stepThreePoints 2) (stepThreePoints 9) square.center
              rw [stepThree_area_2_9]
              by_contra! failed
              have negative : 0 < (((23 / 50 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-13 / 20 : ℝ) * square.center.y + ((331 / 1000 : ℝ) + (41 / 80 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
              have weighted_0 := mul_pos (by positivity : 0 < ((18 / 125 : ℝ) + (29 / 400 : ℝ) * Real.sqrt 2)) branch_1_negative
              have weighted_1 := mul_nonneg (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 ≤ ((-7 / 500 : ℝ) + (101 / 400 : ℝ) * Real.sqrt 2)) branch_6
              have weighted_2 := mul_pos (by positivity : 0 < ((27 / 100 : ℝ) + (1 / 10 : ℝ) * Real.sqrt 2)) negative
              have identity : ((18 / 125 : ℝ) + (29 / 400 : ℝ) * Real.sqrt 2) * (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-83 / 200 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2)) + ((-7 / 500 : ℝ) + (101 / 400 : ℝ) * Real.sqrt 2) * (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2)) + ((27 / 100 : ℝ) + (1 / 10 : ℝ) * Real.sqrt 2) * (((23 / 50 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-13 / 20 : ℝ) * square.center.y + ((331 / 1000 : ℝ) + (41 / 80 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                ring_nf
                simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_8_negative : 0 < (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((-13 / 10 : ℝ) + (-9 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_8]
            apply stepThree_hit_triangle square 4
            · change 0 ≤ Point.orientedArea (stepThreePoints 12) (stepThreePoints 3) square.center
              rw [stepThree_area_12_3]
              exact branch_7_negative.le
            · change 0 ≤ Point.orientedArea (stepThreePoints 3) (stepThreePoints 9) square.center
              rw [stepThree_area_3_9]
              exact branch_8_negative.le
            · change 0 ≤ Point.orientedArea (stepThreePoints 9) (stepThreePoints 12) square.center
              rw [stepThree_area_9_12]
              exact branch_6
      ·
        have branch_6_negative : 0 < (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_6]
        apply stepThree_hit_triangle square 14
        · change 0 ≤ Point.orientedArea (stepThreePoints 11) (stepThreePoints 12) square.center
          rw [stepThree_area_11_12]
          by_contra! failed
          have negative : 0 < (((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((-11 / 20 : ℝ) + (-4 / 5 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
          have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_0
          have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
          have identity : ((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((-43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * (((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((-11 / 20 : ℝ) + (-4 / 5 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
            ring_nf
            simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
            ring
          nlinarith only [weighted_0, weighted_1, identity]
        · change 0 ≤ Point.orientedArea (stepThreePoints 12) (stepThreePoints 9) square.center
          rw [stepThree_area_12_9]
          exact branch_6_negative.le
        · change 0 ≤ Point.orientedArea (stepThreePoints 9) (stepThreePoints 11) square.center
          rw [stepThree_area_9_11]
          exact branch_1_negative.le
  ·
    have branch_0_negative : 0 < ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) := by linarith only [branch_0]
    by_cases branch_9 : 0 ≤ (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-137 / 200 : ℝ) + (-17 / 20 : ℝ) * Real.sqrt 2))
    ·
      by_cases branch_10 : 0 ≤ (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((-9 / 20 : ℝ) + (-11 / 20 : ℝ) * Real.sqrt 2))
      ·
        by_cases branch_11 : 0 ≤ ((0 : ℝ) * square.center.x + (43 / 100 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2))
        ·
          apply stepThree_hit_triangle square 1
          · change 0 ≤ Point.orientedArea (stepThreePoints 5) (stepThreePoints 10) square.center
            rw [stepThree_area_5_10]
            exact branch_10
          · change 0 ≤ Point.orientedArea (stepThreePoints 10) (stepThreePoints 6) square.center
            rw [stepThree_area_10_6]
            exact branch_11
          · change 0 ≤ Point.orientedArea (stepThreePoints 6) (stepThreePoints 5) square.center
            rw [stepThree_area_6_5]
            exact hull_1
        ·
          have branch_11_negative : 0 < ((0 : ℝ) * square.center.x + (-43 / 100 : ℝ) * square.center.y + ((129 / 200 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) := by linarith only [branch_11]
          apply stepThree_hit_triangle square 2
          · change 0 ≤ Point.orientedArea (stepThreePoints 10) (stepThreePoints 7) square.center
            rw [stepThree_area_10_7]
            by_contra! failed
            have negative : 0 < (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((33 / 20 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((2 / 5 : ℝ) + (1 / 5 : ℝ) * Real.sqrt 2)) branch_9
            have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) branch_10
            have weighted_2 := mul_pos (by positivity : 0 < ((43 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2)) negative
            have identity : ((2 / 5 : ℝ) + (1 / 5 : ℝ) * Real.sqrt 2) * (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-137 / 200 : ℝ) + (-17 / 20 : ℝ) * Real.sqrt 2)) + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2) * (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((-9 / 20 : ℝ) + (-11 / 20 : ℝ) * Real.sqrt 2)) + ((43 / 200 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((33 / 20 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
              ring_nf
              simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          · change 0 ≤ Point.orientedArea (stepThreePoints 7) (stepThreePoints 6) square.center
            rw [stepThree_area_7_6]
            exact hull_0
          · change 0 ≤ Point.orientedArea (stepThreePoints 6) (stepThreePoints 10) square.center
            rw [stepThree_area_6_10]
            exact branch_11_negative.le
      ·
        have branch_10_negative : 0 < (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((9 / 20 : ℝ) + (11 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_10]
        by_cases branch_12 : 0 ≤ ((-2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-9 / 20 : ℝ) + (-11 / 20 : ℝ) * Real.sqrt 2))
        ·
          apply stepThree_hit_triangle square 5
          · change 0 ≤ Point.orientedArea (stepThreePoints 12) (stepThreePoints 5) square.center
            rw [stepThree_area_12_5]
            exact branch_12
          · change 0 ≤ Point.orientedArea (stepThreePoints 5) (stepThreePoints 4) square.center
            rw [stepThree_area_5_4]
            exact hull_2
          · change 0 ≤ Point.orientedArea (stepThreePoints 4) (stepThreePoints 12) square.center
            rw [stepThree_area_4_12]
            exact branch_0_negative.le
        ·
          have branch_12_negative : 0 < ((2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((9 / 20 : ℝ) + (11 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_12]
          apply stepThree_hit_triangle square 6
          · change 0 ≤ Point.orientedArea (stepThreePoints 12) (stepThreePoints 10) square.center
            rw [stepThree_area_12_10]
            exact branch_9
          · change 0 ≤ Point.orientedArea (stepThreePoints 10) (stepThreePoints 5) square.center
            rw [stepThree_area_10_5]
            exact branch_10_negative.le
          · change 0 ≤ Point.orientedArea (stepThreePoints 5) (stepThreePoints 12) square.center
            rw [stepThree_area_5_12]
            exact branch_12_negative.le
    ·
      have branch_9_negative : 0 < (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((137 / 200 : ℝ) + (17 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_9]
      by_cases branch_13 : 0 ≤ (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2))
      ·
        by_cases branch_14 : 0 ≤ (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((2 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + (-7 / 5 : ℝ))
        ·
          by_cases branch_15 : 0 ≤ (((1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (2 / 5 : ℝ) * square.center.y + ((-33 / 20 : ℝ) + (-3 / 4 : ℝ) * Real.sqrt 2))
          ·
            apply stepThree_hit_triangle square 2
            · change 0 ≤ Point.orientedArea (stepThreePoints 10) (stepThreePoints 7) square.center
              rw [stepThree_area_10_7]
              exact branch_15
            · change 0 ≤ Point.orientedArea (stepThreePoints 7) (stepThreePoints 6) square.center
              rw [stepThree_area_7_6]
              exact hull_0
            · change 0 ≤ Point.orientedArea (stepThreePoints 6) (stepThreePoints 10) square.center
              rw [stepThree_area_6_10]
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (43 / 100 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
              have weighted_0 := mul_pos (by positivity : 0 < ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) branch_9_negative
              have weighted_1 := mul_nonneg (by positivity : 0 ≤ ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) branch_13
              have weighted_2 := mul_pos (by positivity : 0 < ((27 / 100 : ℝ) + (1 / 10 : ℝ) * Real.sqrt 2)) negative
              have identity : ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) * (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((137 / 200 : ℝ) + (17 / 20 : ℝ) * Real.sqrt 2)) + ((43 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) * (((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-27 / 200 : ℝ) + (-1 / 20 : ℝ) * Real.sqrt 2)) + ((27 / 100 : ℝ) + (1 / 10 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (43 / 100 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                ring_nf
                simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_15_negative : 0 < (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + (-2 / 5 : ℝ) * square.center.y + ((33 / 20 : ℝ) + (3 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_15]
            apply stepThree_hit_triangle square 7
            · change 0 ≤ Point.orientedArea (stepThreePoints 10) (stepThreePoints 8) square.center
              rw [stepThree_area_10_8]
              exact branch_14
            · change 0 ≤ Point.orientedArea (stepThreePoints 8) (stepThreePoints 7) square.center
              rw [stepThree_area_8_7]
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by positivity : 0 ≤ ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) hull_6
              have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
              have identity : ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + ((0 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((0 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            · change 0 ≤ Point.orientedArea (stepThreePoints 7) (stepThreePoints 10) square.center
              rw [stepThree_area_7_10]
              exact branch_15_negative.le
        ·
          have branch_14_negative : 0 < (((-1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((-2 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + (7 / 5 : ℝ)) := by linarith only [branch_14]
          by_cases branch_16 : 0 ≤ ((2 / 5 : ℝ) * square.center.x + ((1 / 2 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((-13 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2))
          ·
            apply stepThree_hit_triangle square 8
            · change 0 ≤ Point.orientedArea (stepThreePoints 11) (stepThreePoints 8) square.center
              rw [stepThree_area_11_8]
              exact branch_16
            · change 0 ≤ Point.orientedArea (stepThreePoints 8) (stepThreePoints 10) square.center
              rw [stepThree_area_8_10]
              exact branch_14_negative.le
            · change 0 ≤ Point.orientedArea (stepThreePoints 10) (stepThreePoints 11) square.center
              rw [stepThree_area_10_11]
              exact branch_13
          ·
            have branch_16_negative : 0 < ((-2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((13 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [branch_16]
            apply stepThree_hit_triangle square 9
            · change 0 ≤ Point.orientedArea (stepThreePoints 11) (stepThreePoints 1) square.center
              rw [stepThree_area_11_1]
              by_contra! failed
              have negative : 0 < ((-2 / 5 : ℝ) * square.center.x + ((3 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((9 / 50 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (8 / 25 : ℝ)) branch_0_negative
              have weighted_1 := mul_pos (by positivity : 0 < ((129 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2)) branch_16_negative
              have weighted_2 := mul_pos (by nlinarith only [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)] : 0 < ((43 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) negative
              have identity : (8 / 25 : ℝ) * ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) + ((129 / 1000 : ℝ) + (43 / 400 : ℝ) * Real.sqrt 2) * ((-2 / 5 : ℝ) * square.center.x + ((-1 / 2 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((13 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) + ((43 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2) * ((-2 / 5 : ℝ) * square.center.x + ((3 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((9 / 50 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            · change 0 ≤ Point.orientedArea (stepThreePoints 1) (stepThreePoints 8) square.center
              rw [stepThree_area_1_8]
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (4 / 5 : ℝ)) hull_6
              have weighted_1 := mul_pos (by positivity : 0 < ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) negative
              have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * square.center.y + ((-1 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2)) + ((1 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            · change 0 ≤ Point.orientedArea (stepThreePoints 8) (stepThreePoints 11) square.center
              rw [stepThree_area_8_11]
              exact branch_16_negative.le
      ·
        have branch_13_negative : 0 < (((-1 / 10 : ℝ) + (-1 / 4 : ℝ) * Real.sqrt 2) * square.center.x + ((1 / 10 : ℝ) + (1 / 4 : ℝ) * Real.sqrt 2) * square.center.y + ((27 / 200 : ℝ) + (1 / 20 : ℝ) * Real.sqrt 2)) := by linarith only [branch_13]
        apply stepThree_hit_triangle square 13
        · change 0 ≤ Point.orientedArea (stepThreePoints 12) (stepThreePoints 11) square.center
          rw [stepThree_area_12_11]
          by_contra! failed
          have negative : 0 < (((-1 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((11 / 20 : ℝ) + (4 / 5 : ℝ) * Real.sqrt 2)) := by linarith only [failed]
          have weighted_0 := mul_pos (by positivity : 0 < ((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2)) branch_0_negative
          have weighted_1 := mul_pos (by norm_num : 0 < (43 / 100 : ℝ)) negative
          have identity : ((1 / 5 : ℝ) + (1 / 2 : ℝ) * Real.sqrt 2) * ((43 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + ((-129 / 200 : ℝ) + (-43 / 400 : ℝ) * Real.sqrt 2)) + (43 / 100 : ℝ) * (((-1 / 5 : ℝ) + (-1 / 2 : ℝ) * Real.sqrt 2) * square.center.x + (0 : ℝ) * square.center.y + ((11 / 20 : ℝ) + (4 / 5 : ℝ) * Real.sqrt 2)) = (0 : ℝ) := by
            ring_nf
            simp only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
            ring
          nlinarith only [weighted_0, weighted_1, identity]
        · change 0 ≤ Point.orientedArea (stepThreePoints 11) (stepThreePoints 10) square.center
          rw [stepThree_area_11_10]
          exact branch_13_negative.le
        · change 0 ≤ Point.orientedArea (stepThreePoints 10) (stepThreePoints 12) square.center
          rw [stepThree_area_10_12]
          exact branch_9_negative.le

end SquarePackingArchive.Stromquist.TenPoints
