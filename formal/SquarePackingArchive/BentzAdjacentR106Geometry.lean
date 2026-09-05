import SquarePackingArchive.BentzAdjacentR106Data

namespace SquarePackingArchive.BentzThirteen

set_option maxRecDepth 10000

def adjacentR106Region (index : Fin 44) (center : Point) : Prop :=
  match index.val with
  | 0 => 0 ≤ ((-43 / 500 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-37 / 100 : ℝ) * center.y + (37 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (-13 / 100 : ℝ) * center.y + (1641 / 50000 : ℝ))
  | 1 => 0 ≤ ((-43 / 500 : ℝ) * center.x + (13 / 100 : ℝ) * center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-27 / 125 : ℝ) * center.y + (27 / 125 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (-41151 / 250000 : ℝ))
  | 2 => 0 ≤ ((77 / 500 : ℝ) * center.x + (87 / 100 : ℝ) * center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (-37 / 100 : ℝ) * center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (371 / 1000 : ℝ))
  | 3 => 0 ≤ ((-43 / 500 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * center.x + (0 : ℝ) * center.y + (-453 / 500 : ℝ))
  | 4 => 0 ≤ ((-453 / 500 : ℝ) * center.x + (0 : ℝ) * center.y + (453 / 500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (-41151 / 250000 : ℝ))
  | 5 => 0 ≤ ((6 / 25 : ℝ) * center.x + (37 / 50 : ℝ) * center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (-13 / 100 : ℝ) * center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-61 / 100 : ℝ) * center.y + (61 / 100 : ℝ))
  | 6 => 0 ≤ ((0 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (-6 / 25 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (13 / 50 : ℝ) * center.y + (2917 / 2500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (-73 / 100 : ℝ))
  | 7 => 0 ≤ ((6 / 25 : ℝ) * center.x + (37 / 100 : ℝ) * center.y + (-73 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (63 / 100 : ℝ) * center.y + (-3 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 8 => 0 ≤ ((-41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (293 / 500 : ℝ) * center.y + (-293 / 500 : ℝ))
  | 9 => 0 ≤ ((-41 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-173 / 100 : ℝ))
  | 10 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (51 / 20 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (-73 / 100 : ℝ))
  | 11 => 0 ≤ ((-27 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-37 / 100 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * center.x + (-37 / 50 : ℝ) * center.y + (1433 / 1250 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (-721 / 1250 : ℝ))
  | 12 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (199 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (37 / 100 : ℝ))
  | 13 => 0 ≤ ((-2 / 5 : ℝ) * center.x + (37 / 50 : ℝ) * center.y + (-1433 / 1250 : ℝ)) ∧ 0 ≤ ((-14 / 25 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (101 / 50 : ℝ)) ∧ 0 ≤ ((24 / 25 : ℝ) * center.x + (-6 / 25 : ℝ) * center.y + (-162 / 625 : ℝ))
  | 14 => 0 ≤ ((-73 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (219 / 200 : ℝ)) ∧ 0 ≤ ((17 / 100 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (129 / 100 : ℝ)) ∧ 0 ≤ ((14 / 25 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-101 / 50 : ℝ))
  | 15 => 0 ≤ ((-7 / 50 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-839 / 500 : ℝ)) ∧ 0 ≤ ((-59 / 100 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (3357 / 1000 : ℝ)) ∧ 0 ≤ ((73 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (-219 / 200 : ℝ))
  | 16 => 0 ≤ ((27 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-199 / 100 : ℝ)) ∧ 0 ≤ ((-17 / 25 : ℝ) * center.x + (3 / 10 : ℝ) * center.y + (407 / 500 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (839 / 500 : ℝ))
  | 17 => 0 ≤ ((9 / 100 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (141 / 100 : ℝ)) ∧ 0 ≤ ((2 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (-2 / 25 : ℝ)) ∧ 0 ≤ ((-17 / 100 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-129 / 100 : ℝ))
  | 18 => 0 ≤ ((59 / 100 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-3357 / 1000 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * center.x + (0 : ℝ) * center.y + (23 / 20 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (2607 / 1000 : ℝ))
  | 19 => 0 ≤ ((0 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-1 / 2 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (123 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (-31 / 20 : ℝ))
  | 20 => 0 ≤ ((-41 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (31 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-51 / 20 : ℝ))
  | 21 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((-17 / 25 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (1657 / 500 : ℝ)) ∧ 0 ≤ ((17 / 25 : ℝ) * center.x + (-3 / 10 : ℝ) * center.y + (-407 / 500 : ℝ))
  | 22 => 0 ≤ ((-17 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (51 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (7 / 4 : ℝ)) ∧ 0 ≤ ((17 / 25 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-1657 / 500 : ℝ))
  | 23 => 0 ≤ ((0 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-7 / 4 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * center.x + (0 : ℝ) * center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (3 / 5 : ℝ))
  | 24 => 0 ≤ ((-1 / 2 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-3 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (21 / 10 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * center.x + (0 : ℝ) * center.y + (-23 / 20 : ℝ))
  | 25 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 26 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 27 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))
  | 28 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))
  | 29 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * center.x + (-87 / 100 : ℝ) * center.y + (47459 / 50000 : ℝ))
  | 30 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-19 / 25 : ℝ) * center.y + (19 / 25 : ℝ))
  | 31 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-27 / 125 : ℝ) * center.y + (27 / 125 : ℝ))
  | 32 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (1 / 2 : ℝ))
  | 33 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * center.x + (0 : ℝ) * center.y + (27 / 125 : ℝ))
  | 34 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (69 / 100 : ℝ))
  | 35 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (49 / 25 : ℝ)) ∧ 0 ≤ ((-7 / 50 : ℝ) * center.x + (-6 / 25 : ℝ) * center.y + (721 / 1250 : ℝ))
  | 36 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-73 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((-2 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (2 / 25 : ℝ))
  | 37 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-3 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (23 / 10 : ℝ)) ∧ 0 ≤ ((9 / 100 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-2607 / 1000 : ℝ))
  | 38 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-141 / 100 : ℝ))
  | 39 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-23 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-21 / 10 : ℝ))
  | 40 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (-123 / 50 : ℝ))
  | 41 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((17 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (-51 / 25 : ℝ))
  | 42 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * center.x + (0 : ℝ) * center.y + (-3 / 2 : ℝ))
  | _ => 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (73 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-49 / 25 : ℝ)) ∧ 0 ≤ ((-24 / 25 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (162 / 625 : ℝ))

set_option maxHeartbeats 4000000 in
theorem adjacentR106_hit_boundary (square : PlacedSquare) (fits : square.Fits 4)
    (index : Fin 44) (membership : adjacentR106Region index square.center) :
    adjacentR106Outcome square := by
  fin_cases index
  · change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1641 / 50000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![0, 3, 1]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-41151 / 250000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![0, 1, 6]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![0, 5, 3]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![0, 3, 8]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-41151 / 250000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![0, 8, 6]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![1, 5, 4]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-6 / 25 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (13 / 50 : ℝ) * square.center.y + (2917 / 2500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-73 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![3, 4, 15]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (63 / 100 : ℝ) * square.center.y + (-3 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![3, 5, 13]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![3, 8, 6]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![3, 15, 8]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (51 / 20 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-73 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![3, 13, 15]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (1433 / 1250 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-721 / 1250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![8, 10, 9]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (199 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (37 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![8, 15, 10]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-1433 / 1250 : ℝ)) ∧ 0 ≤ ((-14 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (101 / 50 : ℝ)) ∧ 0 ≤ ((24 / 25 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (-162 / 625 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![9, 10, 12]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (219 / 200 : ℝ)) ∧ 0 ≤ ((17 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (129 / 100 : ℝ)) ∧ 0 ≤ ((14 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-101 / 50 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![10, 11, 12]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-7 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-839 / 500 : ℝ)) ∧ 0 ≤ ((-59 / 100 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (3357 / 1000 : ℝ)) ∧ 0 ≤ ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-219 / 200 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![10, 17, 11]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-199 / 100 : ℝ)) ∧ 0 ≤ ((-17 / 25 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (407 / 500 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (839 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![10, 15, 17]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((9 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (141 / 100 : ℝ)) ∧ 0 ≤ ((2 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 / 25 : ℝ)) ∧ 0 ≤ ((-17 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-129 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![11, 19, 12]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((59 / 100 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-3357 / 1000 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 20 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (2607 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![11, 17, 20]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-1 / 2 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-31 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![13, 14, 16]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (31 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-51 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![13, 16, 15]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((-17 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (1657 / 500 : ℝ)) ∧ 0 ≤ ((17 / 25 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-407 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![15, 16, 17]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (51 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (7 / 4 : ℝ)) ∧ 0 ≤ ((17 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-1657 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![16, 18, 17]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-7 / 4 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (3 / 5 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![17, 18, 21]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-3 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (21 / 10 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR106Points ![17, 21, 20]
    all_goals norm_num [adjacentR106Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := square.contains_cornerPoint (targetX := (457 / 500 : ℝ)) (targetY := (1 : ℝ)) fits (by norm_num) (by norm_num)
      (by linarith) (by linarith)
    refine ⟨6, ?_⟩
    convert contained using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := (square.reflectX 4).contains_cornerPoint (targetX := (1 : ℝ)) (targetY := (1 : ℝ)) ((square.reflectX_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by change (4 - square.center.x) ≤ (1 : ℝ); linarith) (by change square.center.y ≤ (1 : ℝ); linarith)
    refine ⟨14, ?_⟩
    apply (square.reflectX_contains_iff 4 (adjacentR106Points 14)).1
    convert contained using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := (square.reflectY 4).contains_cornerPoint (targetX := (1 : ℝ)) (targetY := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by change square.center.x ≤ (1 : ℝ); linarith) (by change (4 - square.center.y) ≤ (1 : ℝ); linarith)
    refine ⟨19, ?_⟩
    apply (square.reflectY_contains_iff 4 (adjacentR106Points 19)).1
    convert contained using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := ((square.reflectX 4).reflectY 4).contains_cornerPoint (targetX := (1 : ℝ)) (targetY := (1 : ℝ)) (((square.reflectX 4).reflectY_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num)
      (by change (4 - square.center.x) ≤ (1 : ℝ); linarith) (by change (4 - square.center.y) ≤ (1 : ℝ); linarith)
    refine ⟨21, ?_⟩
    apply (square.reflectX_contains_iff 4 (adjacentR106Points 21)).1
    apply ((square.reflectX 4).reflectY_contains_iff 4 ((adjacentR106Points 21).reflectX 4)).1
    convert contained using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Bentz.contains_descending_pair (square := square) (left := (1 : ℝ)) (width := (87 / 100 : ℝ)) (firstHeight := (457 / 500 : ℝ)) (secondHeight := (19 / 25 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Bentz.weighted_bound_first (by norm_num) (by norm_num))
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨0, ?_⟩
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨5, ?_⟩
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (87 / 50 : ℝ)) (width := (19 / 25 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨4, ?_⟩
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨13, ?_⟩
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (457 / 500 : ℝ)) (width := (27 / 125 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨6, ?_⟩
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨1, ?_⟩
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (1 / 2 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (5 / 2 : ℝ)) (width := (1 / 2 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨13, ?_⟩
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨14, ?_⟩
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (457 / 500 : ℝ)) (width := (27 / 125 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (457 / 500 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (457 / 500 : ℝ) + (27 / 125 : ℝ); linarith) (by change (27 / 125 : ℝ) * square.center.x ≤ (27 / 125 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (457 / 500 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨0, ?_⟩
      apply (square.swap_contains_iff (adjacentR106Points 0)).1
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨7, ?_⟩
      apply (square.swap_contains_iff (adjacentR106Points 7)).1
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (113 / 100 : ℝ)) (width := (69 / 100 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (113 / 100 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (113 / 100 : ℝ) + (69 / 100 : ℝ); linarith) (by change (69 / 100 : ℝ) * square.center.x ≤ (69 / 100 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (113 / 100 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨7, ?_⟩
      apply (square.swap_contains_iff (adjacentR106Points 7)).1
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨8, ?_⟩
      apply (square.swap_contains_iff (adjacentR106Points 8)).1
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (49 / 25 : ℝ)) ∧ 0 ≤ ((-7 / 50 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (721 / 1250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (91 / 50 : ℝ)) (width := (7 / 50 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (19 / 25 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (91 / 50 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (91 / 50 : ℝ) + (7 / 50 : ℝ); linarith) (by change (7 / 50 : ℝ) * square.center.x ≤ (7 / 50 : ℝ) * (1 : ℝ) + ((19 / 25 : ℝ) - (1 : ℝ)) * (square.center.y - (91 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨8, ?_⟩
      apply (square.swap_contains_iff (adjacentR106Points 8)).1
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨9, ?_⟩
      apply (square.swap_contains_iff (adjacentR106Points 9)).1
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-73 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-2 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (73 / 25 : ℝ)) (width := (2 / 25 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (73 / 25 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (73 / 25 : ℝ) + (2 / 25 : ℝ); linarith) (by change (2 / 25 : ℝ) * square.center.x ≤ (2 / 25 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (73 / 25 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨12, ?_⟩
      apply (square.swap_contains_iff (adjacentR106Points 12)).1
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨19, ?_⟩
      apply (square.swap_contains_iff (adjacentR106Points 19)).1
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) ∧ 0 ≤ ((9 / 100 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-2607 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (3 / 2 : ℝ)) (width := (4 / 5 : ℝ)) (firstHeight := (91 / 100 : ℝ)) (secondHeight := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (3 / 2 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (3 / 2 : ℝ) + (4 / 5 : ℝ); linarith) (by change (4 / 5 : ℝ) * (4 - square.center.y) ≤ (4 / 5 : ℝ) * (91 / 100 : ℝ) + ((1 : ℝ) - (91 / 100 : ℝ)) * (square.center.x - (3 / 2 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨11, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR106Points 11)).1
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨20, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR106Points 20)).1
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-141 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (1 : ℝ)) (width := (1 / 2 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (91 / 100 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (1 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (1 : ℝ) + (1 / 2 : ℝ); linarith) (by change (1 / 2 : ℝ) * (4 - square.center.y) ≤ (1 / 2 : ℝ) * (1 : ℝ) + ((91 / 100 : ℝ) - (1 : ℝ)) * (square.center.x - (1 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨19, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR106Points 19)).1
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨11, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR106Points 11)).1
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-21 / 10 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (23 / 10 : ℝ)) (width := (7 / 10 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (23 / 10 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (23 / 10 : ℝ) + (7 / 10 : ℝ); linarith) (by change (7 / 10 : ℝ) * (4 - square.center.y) ≤ (7 / 10 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.x - (23 / 10 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨20, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR106Points 20)).1
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨21, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR106Points 21)).1
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := (square.reflectX 4).swap.contains_bottomSharpPair (left := (1 : ℝ)) (gap := (41 / 50 : ℝ)) (targetHeight := (1 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num) (by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
      (by change (1 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (1 : ℝ) + (41 / 50 : ℝ); linarith) (by change (4 - square.center.x) ≤ (1 : ℝ); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨14, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR106Points 14)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR106Points 14).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨16, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR106Points 16)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR106Points 16).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-51 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectX 4).swap) (left := (91 / 50 : ℝ)) (width := (17 / 25 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (91 / 50 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (91 / 50 : ℝ) + (17 / 25 : ℝ); linarith) (by change (17 / 25 : ℝ) * (4 - square.center.x) ≤ (17 / 25 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (91 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨16, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR106Points 16)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR106Points 16).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨18, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR106Points 18)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR106Points 18).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectX 4).swap) (left := (5 / 2 : ℝ)) (width := (1 / 2 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (5 / 2 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (5 / 2 : ℝ) + (1 / 2 : ℝ); linarith) (by change (1 / 2 : ℝ) * (4 - square.center.x) ≤ (1 / 2 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (5 / 2 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨18, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR106Points 18)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR106Points 18).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨21, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR106Points 21)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR106Points 21).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (73 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-49 / 25 : ℝ)) ∧ 0 ≤ ((-24 / 25 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (162 / 625 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Bentz.contains_descending_pair (square := (square.swap.reflectX 4)) (left := (27 / 25 : ℝ)) (width := (24 / 25 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (19 / 25 : ℝ)) ((square.swap.reflectX_fits_iff 4).2 ((square.swap_fits_iff 4).2 fits))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Bentz.weighted_bound_third (by norm_num) (by norm_num))
      (by change (27 / 25 : ℝ) ≤ (4 - square.center.y); linarith) (by change (4 - square.center.y) ≤ (27 / 25 : ℝ) + (24 / 25 : ℝ); linarith) (by change (24 / 25 : ℝ) * square.center.x ≤ (24 / 25 : ℝ) * (1 : ℝ) + ((19 / 25 : ℝ) - (1 : ℝ)) * ((4 - square.center.y) - (27 / 25 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨12, ?_⟩
      apply (square.swap_contains_iff (adjacentR106Points 12)).1
      apply ((square.swap).reflectX_contains_iff 4 ((adjacentR106Points 12).swap)).1
      convert first_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨9, ?_⟩
      apply (square.swap_contains_iff (adjacentR106Points 9)).1
      apply ((square.swap).reflectX_contains_iff 4 ((adjacentR106Points 9).swap)).1
      convert second_mem using 1; norm_num [adjacentR106Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]

end SquarePackingArchive.BentzThirteen
