import SquarePackingArchive.BentzAdjacentInitialData

namespace SquarePackingArchive.BentzThirteen

set_option maxRecDepth 10000

def adjacentInitialRegion (index : Fin 35) (center : Point) : Prop :=
  match index.val with
  | 0 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (49 / 100 : ℝ))
  | 1 => 0 ≤ ((-43 / 500 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-37 / 100 : ℝ) * center.y + (37 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (-13 / 100 : ℝ) * center.y + (1641 / 50000 : ℝ))
  | 2 => 0 ≤ ((-43 / 500 : ℝ) * center.x + (13 / 100 : ℝ) * center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-27 / 125 : ℝ) * center.y + (27 / 125 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (-41151 / 250000 : ℝ))
  | 3 => 0 ≤ ((77 / 500 : ℝ) * center.x + (87 / 100 : ℝ) * center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (-37 / 100 : ℝ) * center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (371 / 1000 : ℝ))
  | 4 => 0 ≤ ((-43 / 500 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * center.x + (0 : ℝ) * center.y + (-453 / 500 : ℝ))
  | 5 => 0 ≤ ((-453 / 500 : ℝ) * center.x + (0 : ℝ) * center.y + (453 / 500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (-41151 / 250000 : ℝ))
  | 6 => 0 ≤ ((6 / 25 : ℝ) * center.x + (37 / 50 : ℝ) * center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (-13 / 100 : ℝ) * center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-61 / 100 : ℝ) * center.y + (61 / 100 : ℝ))
  | 7 => 0 ≤ ((0 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (-6 / 25 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (13 / 50 : ℝ) * center.y + (2917 / 2500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (-73 / 100 : ℝ))
  | 8 => 0 ≤ ((6 / 25 : ℝ) * center.x + (37 / 100 : ℝ) * center.y + (-73 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (63 / 100 : ℝ) * center.y + (-3 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 9 => 0 ≤ ((-41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (293 / 500 : ℝ) * center.y + (-293 / 500 : ℝ))
  | 10 => 0 ≤ ((-41 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-173 / 100 : ℝ))
  | 11 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (51 / 20 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (-73 / 100 : ℝ))
  | 12 => 0 ≤ ((-27 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (27 / 50 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * center.x + (-6 / 25 : ℝ) * center.y + (104 / 625 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (-721 / 1250 : ℝ))
  | 13 => 0 ≤ ((0 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-1 / 2 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (123 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (-31 / 20 : ℝ))
  | 14 => 0 ≤ ((-41 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (31 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-51 / 20 : ℝ))
  | 15 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 16 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 17 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-309 / 100 : ℝ))
  | 18 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-309 / 100 : ℝ))
  | 19 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * center.x + (-87 / 100 : ℝ) * center.y + (47459 / 50000 : ℝ))
  | 20 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-19 / 25 : ℝ) * center.y + (19 / 25 : ℝ))
  | 21 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-27 / 125 : ℝ) * center.y + (27 / 125 : ℝ))
  | 22 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (1 / 2 : ℝ))
  | 23 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (59 / 25 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (27 / 50 : ℝ))
  | 24 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (309 / 100 : ℝ)) ∧ 0 ≤ ((-73 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (73 / 100 : ℝ))
  | 25 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-309 / 100 : ℝ))
  | 26 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-309 / 100 : ℝ))
  | 27 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (-123 / 50 : ℝ))
  | 28 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (59 / 25 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (-81 / 50 : ℝ))
  | 29 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (309 / 100 : ℝ)) ∧ 0 ≤ ((73 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (-219 / 100 : ℝ))
  | 30 => 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (16587 / 25000 : ℝ))
  | 31 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (309 / 100 : ℝ))
  | 32 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (309 / 100 : ℝ))
  | 33 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (59 / 25 : ℝ))
  | _ => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (59 / 25 : ℝ))

set_option maxHeartbeats 4000000 in
theorem adjacentInitial_hit_boundary (square : PlacedSquare) (fits : square.Fits 4)
    (index : Fin 35) (membership : adjacentInitialRegion index square.center) :
    adjacentInitialOutcome square := by
  fin_cases index
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (49 / 100 : ℝ)) at membership
    norm_num at membership
    exfalso
    have bounds := center_inside_half_margin fits
    linarith [bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2]
  · change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1641 / 50000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![0, 3, 1]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-41151 / 250000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![0, 1, 6]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![0, 5, 3]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![0, 3, 8]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-41151 / 250000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![0, 8, 6]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![1, 5, 4]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-6 / 25 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (13 / 50 : ℝ) * square.center.y + (2917 / 2500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-73 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![3, 4, 12]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (63 / 100 : ℝ) * square.center.y + (-3 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![3, 5, 10]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![3, 8, 6]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![3, 12, 8]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (51 / 20 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-73 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![3, 10, 12]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 50 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (104 / 625 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-721 / 1250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![8, 14, 9]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-1 / 2 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-31 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![10, 11, 13]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (31 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-51 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    apply square.contains_indexed_triangleVertex adjacentInitialPoints ![10, 13, 12]
    all_goals norm_num [adjacentInitialPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    apply Or.inl
    have contained := square.contains_cornerPoint (targetX := (457 / 500 : ℝ)) (targetY := (1 : ℝ)) fits (by norm_num) (by norm_num)
      (by linarith) (by linarith)
    refine ⟨6, ?_⟩
    convert contained using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    apply Or.inl
    have contained := (square.reflectX 4).contains_cornerPoint (targetX := (1 : ℝ)) (targetY := (1 : ℝ)) ((square.reflectX_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by change (4 - square.center.x) ≤ (1 : ℝ); linarith) (by change square.center.y ≤ (1 : ℝ); linarith)
    refine ⟨11, ?_⟩
    apply (square.reflectX_contains_iff 4 (adjacentInitialPoints 11)).1
    convert contained using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    apply Or.inl
    have contained := (square.reflectY 4).contains_cornerPoint (targetX := (1 : ℝ)) (targetY := (91 / 100 : ℝ)) ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by change square.center.x ≤ (1 : ℝ); linarith) (by change (4 - square.center.y) ≤ (91 / 100 : ℝ); linarith)
    refine ⟨17, ?_⟩
    apply (square.reflectY_contains_iff 4 (adjacentInitialPoints 17)).1
    convert contained using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    apply Or.inl
    have contained := ((square.reflectX 4).reflectY 4).contains_cornerPoint (targetX := (1 : ℝ)) (targetY := (91 / 100 : ℝ)) (((square.reflectX 4).reflectY_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num)
      (by change (4 - square.center.x) ≤ (1 : ℝ); linarith) (by change (4 - square.center.y) ≤ (91 / 100 : ℝ); linarith)
    refine ⟨19, ?_⟩
    apply (square.reflectX_contains_iff 4 (adjacentInitialPoints 19)).1
    apply ((square.reflectX 4).reflectY_contains_iff 4 ((adjacentInitialPoints 19).reflectX 4)).1
    convert contained using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := Bentz.contains_descending_pair (square := square) (left := (1 : ℝ)) (width := (87 / 100 : ℝ)) (firstHeight := (457 / 500 : ℝ)) (secondHeight := (19 / 25 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Bentz.weighted_bound_first (by norm_num) (by norm_num))
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨0, ?_⟩
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨5, ?_⟩
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (87 / 50 : ℝ)) (width := (19 / 25 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨4, ?_⟩
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨10, ?_⟩
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (457 / 500 : ℝ)) (width := (27 / 125 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨6, ?_⟩
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨1, ?_⟩
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (1 / 2 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (5 / 2 : ℝ)) (width := (1 / 2 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨10, ?_⟩
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨11, ?_⟩
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 50 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (91 / 50 : ℝ)) (width := (27 / 50 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (91 / 50 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (91 / 50 : ℝ) + (27 / 50 : ℝ); linarith) (by change (27 / 50 : ℝ) * square.center.x ≤ (27 / 50 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (91 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨8, ?_⟩
      apply (square.swap_contains_iff (adjacentInitialPoints 8)).1
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨14, ?_⟩
      apply (square.swap_contains_iff (adjacentInitialPoints 14)).1
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ)) ∧ 0 ≤ ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (59 / 25 : ℝ)) (width := (73 / 100 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (59 / 25 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (59 / 25 : ℝ) + (73 / 100 : ℝ); linarith) (by change (73 / 100 : ℝ) * square.center.x ≤ (73 / 100 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (59 / 25 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨14, ?_⟩
      apply (square.swap_contains_iff (adjacentInitialPoints 14)).1
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨17, ?_⟩
      apply (square.swap_contains_iff (adjacentInitialPoints 17)).1
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := (square.reflectY 4).contains_bottomLowPair (left := (1 : ℝ)) (gap := (1 : ℝ)) (targetHeight := (91 / 100 : ℝ)) ((square.reflectY_fits_iff 4).2 fits) (by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) (by norm_num) (by norm_num)
      (by change (1 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (1 : ℝ) + (1 : ℝ); linarith) (by change (4 - square.center.y) ≤ (91 / 100 : ℝ); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨17, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentInitialPoints 17)).1
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨18, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentInitialPoints 18)).1
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := (square.reflectY 4).contains_bottomLowPair (left := (2 : ℝ)) (gap := (1 : ℝ)) (targetHeight := (91 / 100 : ℝ)) ((square.reflectY_fits_iff 4).2 fits) (by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) (by norm_num) (by norm_num)
      (by change (2 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (2 : ℝ) + (1 : ℝ); linarith) (by change (4 - square.center.y) ≤ (91 / 100 : ℝ); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨18, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentInitialPoints 18)).1
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨19, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentInitialPoints 19)).1
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := (square.reflectX 4).swap.contains_bottomSharpPair (left := (1 : ℝ)) (gap := (41 / 50 : ℝ)) (targetHeight := (1 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num) (by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
      (by change (1 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (1 : ℝ) + (41 / 50 : ℝ); linarith) (by change (4 - square.center.x) ≤ (1 : ℝ); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨11, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentInitialPoints 11)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentInitialPoints 11).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨13, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentInitialPoints 13)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentInitialPoints 13).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-81 / 50 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectX 4).swap) (left := (91 / 50 : ℝ)) (width := (27 / 50 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (91 / 50 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (91 / 50 : ℝ) + (27 / 50 : ℝ); linarith) (by change (27 / 50 : ℝ) * (4 - square.center.x) ≤ (27 / 50 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (91 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨13, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentInitialPoints 13)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentInitialPoints 13).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨16, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentInitialPoints 16)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentInitialPoints 16).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ)) ∧ 0 ≤ ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-219 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectX 4).swap) (left := (59 / 25 : ℝ)) (width := (73 / 100 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (59 / 25 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (59 / 25 : ℝ) + (73 / 100 : ℝ); linarith) (by change (73 / 100 : ℝ) * (4 - square.center.x) ≤ (73 / 100 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (59 / 25 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨16, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentInitialPoints 16)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentInitialPoints 16).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨19, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentInitialPoints 19)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentInitialPoints 19).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (16587 / 25000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply Or.inl
    have pair := Bentz.contains_descending_pair (square := (square.swap.reflectX 4)) (left := (109 / 50 : ℝ)) (width := (41 / 50 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (457 / 500 : ℝ)) ((square.swap.reflectX_fits_iff 4).2 ((square.swap_fits_iff 4).2 fits))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Bentz.weighted_bound_first (by norm_num) (by norm_num))
      (by change (109 / 50 : ℝ) ≤ (4 - square.center.y); linarith) (by change (4 - square.center.y) ≤ (109 / 50 : ℝ) + (41 / 50 : ℝ); linarith) (by change (41 / 50 : ℝ) * square.center.x ≤ (41 / 50 : ℝ) * (1 : ℝ) + ((457 / 500 : ℝ) - (1 : ℝ)) * ((4 - square.center.y) - (109 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨8, ?_⟩
      apply (square.swap_contains_iff (adjacentInitialPoints 8)).1
      apply ((square.swap).reflectX_contains_iff 4 ((adjacentInitialPoints 8).swap)).1
      convert first_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨6, ?_⟩
      apply (square.swap_contains_iff (adjacentInitialPoints 6)).1
      apply ((square.swap).reflectX_contains_iff 4 ((adjacentInitialPoints 6).swap)).1
      convert second_mem using 1; norm_num [adjacentInitialPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    exact Or.inr ⟨0, by norm_num [adjacentInitialCriticalRegion]; exact ⟨plane_0, plane_1, plane_2, plane_3⟩⟩
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    exact Or.inr ⟨1, by norm_num [adjacentInitialCriticalRegion]; exact ⟨plane_0, plane_1, plane_2, plane_3⟩⟩
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    exact Or.inr ⟨2, by norm_num [adjacentInitialCriticalRegion]; exact ⟨plane_0, plane_1, plane_2, plane_3⟩⟩
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    exact Or.inr ⟨3, by norm_num [adjacentInitialCriticalRegion]; exact ⟨plane_0, plane_1, plane_2, plane_3⟩⟩

end SquarePackingArchive.BentzThirteen
