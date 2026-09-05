import SquarePackingArchive.BentzAdjacentR2LeftData

namespace SquarePackingArchive.BentzThirteen

set_option maxRecDepth 10000

def adjacentR2LeftRegion (index : Fin 46) (center : Point) : Prop :=
  match index.val with
  | 0 => 0 ≤ ((-43 / 500 : ℝ) * center.x + (13 / 100 : ℝ) * center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-27 / 125 : ℝ) * center.y + (27 / 125 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (-41151 / 250000 : ℝ))
  | 1 => 0 ≤ ((6 / 25 : ℝ) * center.x + (37 / 50 : ℝ) * center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (-13 / 100 : ℝ) * center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-61 / 100 : ℝ) * center.y + (61 / 100 : ℝ))
  | 2 => 0 ≤ ((0 : ℝ) * center.x + (17 / 50 : ℝ) * center.y + (-17 / 50 : ℝ)) ∧ 0 ≤ ((-19 / 20 : ℝ) * center.x + (-7 / 50 : ℝ) * center.y + (1793 / 1000 : ℝ)) ∧ 0 ≤ ((19 / 20 : ℝ) * center.x + (-1 / 5 : ℝ) * center.y + (-113 / 100 : ℝ))
  | 3 => 0 ≤ ((-41 / 50 : ℝ) * center.x + (-2 / 5 : ℝ) * center.y + (387 / 250 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (243 / 500 : ℝ) * center.y + (-243 / 500 : ℝ))
  | 4 => 0 ≤ ((-19 / 20 : ℝ) * center.x + (1 / 5 : ℝ) * center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (481 / 500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (2 / 5 : ℝ) * center.y + (-387 / 250 : ℝ))
  | 5 => 0 ≤ ((0 : ℝ) * center.x + (19 / 25 : ℝ) * center.y + (-19 / 25 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * center.x + (0 : ℝ) * center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * center.x + (-19 / 25 : ℝ) * center.y + (-71 / 250 : ℝ))
  | 6 => 0 ≤ ((-3 / 5 : ℝ) * center.x + (19 / 25 : ℝ) * center.y + (71 / 250 : ℝ)) ∧ 0 ≤ ((-7 / 20 : ℝ) * center.x + (-9 / 10 : ℝ) * center.y + (463 / 200 : ℝ)) ∧ 0 ≤ ((19 / 20 : ℝ) * center.x + (7 / 50 : ℝ) * center.y + (-1793 / 1000 : ℝ))
  | 7 => 0 ≤ ((-13 / 100 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-481 / 500 : ℝ)) ∧ 0 ≤ ((-1 / 100 : ℝ) * center.x + (-21 / 25 : ℝ) * center.y + (827 / 500 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (-721 / 1250 : ℝ))
  | 8 => 0 ≤ ((-9 / 10 : ℝ) * center.x + (0 : ℝ) * center.y + (9 / 10 : ℝ)) ∧ 0 ≤ ((19 / 25 : ℝ) * center.x + (-6 / 25 : ℝ) * center.y + (-67 / 625 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (-721 / 1250 : ℝ))
  | 9 => 0 ≤ ((-13 / 100 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-481 / 500 : ℝ)) ∧ 0 ≤ ((-77 / 100 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (1201 / 500 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * center.x + (0 : ℝ) * center.y + (-9 / 10 : ℝ))
  | 10 => 0 ≤ ((1 / 100 : ℝ) * center.x + (21 / 25 : ℝ) * center.y + (-827 / 500 : ℝ)) ∧ 0 ≤ ((-77 / 100 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (1201 / 500 : ℝ)) ∧ 0 ≤ ((19 / 25 : ℝ) * center.x + (-6 / 25 : ℝ) * center.y + (-67 / 625 : ℝ))
  | 11 => 0 ≤ ((-73 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (73 / 40 : ℝ)) ∧ 0 ≤ ((37 / 100 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (31 / 50 : ℝ)) ∧ 0 ≤ ((9 / 25 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-52 / 25 : ℝ))
  | 12 => 0 ≤ ((-73 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (73 / 40 : ℝ)) ∧ 0 ≤ ((9 / 100 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (969 / 500 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-813 / 250 : ℝ))
  | 13 => 0 ≤ ((-16 / 25 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (23 / 125 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (2079 / 1000 : ℝ)) ∧ 0 ≤ ((73 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (-73 / 40 : ℝ))
  | 14 => 0 ≤ ((-9 / 25 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (52 / 25 : ℝ)) ∧ 0 ≤ ((77 / 100 : ℝ) * center.x + (-2 / 5 : ℝ) * center.y + (-113 / 250 : ℝ)) ∧ 0 ≤ ((-41 / 100 : ℝ) * center.x + (9 / 10 : ℝ) * center.y + (-1099 / 1000 : ℝ))
  | 15 => 0 ≤ ((-16 / 25 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (813 / 250 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * center.x + (1 / 5 : ℝ) * center.y + (-138 / 125 : ℝ)) ∧ 0 ≤ ((9 / 25 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-52 / 25 : ℝ))
  | 16 => 0 ≤ ((41 / 100 : ℝ) * center.x + (-9 / 10 : ℝ) * center.y + (1099 / 1000 : ℝ)) ∧ 0 ≤ ((7 / 20 : ℝ) * center.x + (9 / 10 : ℝ) * center.y + (-463 / 200 : ℝ)) ∧ 0 ≤ ((-19 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (19 / 10 : ℝ))
  | 17 => 0 ≤ ((19 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (-19 / 10 : ℝ)) ∧ 0 ≤ ((-2 / 5 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (1 / 25 : ℝ)) ∧ 0 ≤ ((-9 / 25 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (579 / 250 : ℝ))
  | 18 => 0 ≤ ((9 / 25 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-579 / 250 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (-23 / 125 : ℝ))
  | 19 => 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (68 / 25 : ℝ)) ∧ 0 ≤ ((77 / 100 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-1201 / 500 : ℝ)) ∧ 0 ≤ ((-77 / 100 : ℝ) * center.x + (2 / 5 : ℝ) * center.y + (113 / 250 : ℝ))
  | 20 => 0 ≤ ((-7 / 25 : ℝ) * center.x + (-1 / 5 : ℝ) * center.y + (138 / 125 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (237 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-68 / 25 : ℝ))
  | 21 => 0 ≤ ((0 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-3 / 5 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (123 / 50 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * center.x + (0 : ℝ) * center.y + (-3 / 2 : ℝ))
  | 22 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (-1 / 25 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-123 / 50 : ℝ))
  | 23 => 0 ≤ ((-7 / 25 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-237 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (-7 / 25 : ℝ))
  | 24 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-39 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (37 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (27 / 20 : ℝ))
  | 25 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-139 / 100 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (209 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (27 / 20 : ℝ))
  | 26 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 27 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 28 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-43 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (57 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-5 / 4 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (39 / 20 : ℝ))
  | 29 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-5 / 4 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (39 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (23 / 10 : ℝ))
  | 30 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))
  | 31 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))
  | 32 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * center.x + (-87 / 100 : ℝ) * center.y + (47459 / 50000 : ℝ))
  | 33 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-19 / 25 : ℝ) * center.y + (19 / 25 : ℝ))
  | 34 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-27 / 125 : ℝ) * center.y + (27 / 125 : ℝ))
  | 35 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (3 / 5 : ℝ))
  | 36 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * center.x + (0 : ℝ) * center.y + (27 / 125 : ℝ))
  | 37 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (69 / 100 : ℝ))
  | 38 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (49 / 25 : ℝ)) ∧ 0 ≤ ((-7 / 50 : ℝ) * center.x + (-6 / 25 : ℝ) * center.y + (721 / 1250 : ℝ))
  | 39 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-49 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (68 / 25 : ℝ)) ∧ 0 ≤ ((-19 / 25 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (67 / 625 : ℝ))
  | 40 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-68 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((-7 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (7 / 25 : ℝ))
  | 41 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((9 / 100 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-2079 / 1000 : ℝ))
  | 42 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (9 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-12 / 5 : ℝ))
  | 43 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-9 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-969 / 500 : ℝ))
  | 44 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (2 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-31 / 10 : ℝ))
  | _ => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-31 / 10 : ℝ))

set_option maxHeartbeats 4000000 in
theorem adjacentR2Left_hit_boundary (square : PlacedSquare) (fits : square.Fits 4)
    (index : Fin 46) (membership : adjacentR2LeftRegion index square.center) :
    adjacentR2LeftOutcome square := by
  fin_cases index
  · change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-41151 / 250000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![0, 1, 6]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![1, 5, 4]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (17 / 50 : ℝ) * square.center.y + (-17 / 50 : ℝ)) ∧ 0 ≤ ((-19 / 20 : ℝ) * square.center.x + (-7 / 50 : ℝ) * square.center.y + (1793 / 1000 : ℝ)) ∧ 0 ≤ ((19 / 20 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-113 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![2, 4, 16]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (387 / 250 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (243 / 500 : ℝ) * square.center.y + (-243 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![2, 8, 6]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-19 / 20 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (481 / 500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-387 / 250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![2, 16, 8]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (-71 / 250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![4, 13, 15]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (71 / 250 : ℝ)) ∧ 0 ≤ ((-7 / 20 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (463 / 200 : ℝ)) ∧ 0 ≤ ((19 / 20 : ℝ) * square.center.x + (7 / 50 : ℝ) * square.center.y + (-1793 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![4, 15, 16]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-13 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-481 / 500 : ℝ)) ∧ 0 ≤ ((-1 / 100 : ℝ) * square.center.x + (-21 / 25 : ℝ) * square.center.y + (827 / 500 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-721 / 1250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![8, 16, 9]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ)) ∧ 0 ≤ ((19 / 25 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (-67 / 625 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-721 / 1250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![8, 18, 9]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-13 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-481 / 500 : ℝ)) ∧ 0 ≤ ((-77 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (1201 / 500 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![8, 16, 18]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((1 / 100 : ℝ) * square.center.x + (21 / 25 : ℝ) * square.center.y + (-827 / 500 : ℝ)) ∧ 0 ≤ ((-77 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (1201 / 500 : ℝ)) ∧ 0 ≤ ((19 / 25 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (-67 / 625 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![9, 16, 18]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 40 : ℝ)) ∧ 0 ≤ ((37 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (31 / 50 : ℝ)) ∧ 0 ≤ ((9 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-52 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![10, 11, 12]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 40 : ℝ)) ∧ 0 ≤ ((9 / 100 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (969 / 500 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-813 / 250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![10, 11, 20]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (23 / 125 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (2079 / 1000 : ℝ)) ∧ 0 ≤ ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-73 / 40 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![10, 21, 11]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-9 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (52 / 25 : ℝ)) ∧ 0 ≤ ((77 / 100 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-113 / 250 : ℝ)) ∧ 0 ≤ ((-41 / 100 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-1099 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![10, 12, 16]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (813 / 250 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-138 / 125 : ℝ)) ∧ 0 ≤ ((9 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-52 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![10, 20, 12]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((41 / 100 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (1099 / 1000 : ℝ)) ∧ 0 ≤ ((7 / 20 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-463 / 200 : ℝ)) ∧ 0 ≤ ((-19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 10 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![10, 16, 15]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 10 : ℝ)) ∧ 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (1 / 25 : ℝ)) ∧ 0 ≤ ((-9 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (579 / 250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![10, 15, 17]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((9 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-579 / 250 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-23 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![10, 17, 21]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (68 / 25 : ℝ)) ∧ 0 ≤ ((77 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-1201 / 500 : ℝ)) ∧ 0 ≤ ((-77 / 100 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (113 / 250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![12, 18, 16]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (138 / 125 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (237 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-68 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![12, 20, 18]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-3 / 5 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (123 / 50 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![13, 14, 15]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-1 / 25 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-123 / 50 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![14, 17, 15]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-237 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR2LeftPoints ![18, 20, 19]
    all_goals norm_num [adjacentR2LeftPoints, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (37 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨1, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR2LeftPoints]; linarith)
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-139 / 100 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (209 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨4, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR2LeftPoints]; linarith)
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := square.contains_cornerPoint (targetX := (457 / 500 : ℝ)) (targetY := (1 : ℝ)) fits (by norm_num) (by norm_num)
      (by linarith) (by linarith)
    refine ⟨6, ?_⟩
    convert contained using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := (square.reflectX 4).contains_cornerPoint (targetX := (9 / 10 : ℝ)) (targetY := (1 : ℝ)) ((square.reflectX_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by change (4 - square.center.x) ≤ (9 / 10 : ℝ); linarith) (by change square.center.y ≤ (1 : ℝ); linarith)
    refine ⟨14, ?_⟩
    apply (square.reflectX_contains_iff 4 (adjacentR2LeftPoints 14)).1
    convert contained using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-43 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (57 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-5 / 4 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (39 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨15, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR2LeftPoints]; linarith)
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 4 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (23 / 10 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨16, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR2LeftPoints]; linarith)
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := (square.reflectY 4).contains_cornerPoint (targetX := (1 : ℝ)) (targetY := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by change square.center.x ≤ (1 : ℝ); linarith) (by change (4 - square.center.y) ≤ (1 : ℝ); linarith)
    refine ⟨19, ?_⟩
    apply (square.reflectY_contains_iff 4 (adjacentR2LeftPoints 19)).1
    convert contained using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := ((square.reflectX 4).reflectY 4).contains_cornerPoint (targetX := (9 / 10 : ℝ)) (targetY := (1 : ℝ)) (((square.reflectX 4).reflectY_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num)
      (by change (4 - square.center.x) ≤ (9 / 10 : ℝ); linarith) (by change (4 - square.center.y) ≤ (1 : ℝ); linarith)
    refine ⟨21, ?_⟩
    apply (square.reflectX_contains_iff 4 (adjacentR2LeftPoints 21)).1
    apply ((square.reflectX 4).reflectY_contains_iff 4 ((adjacentR2LeftPoints 21).reflectX 4)).1
    convert contained using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Bentz.contains_descending_pair (square := square) (left := (1 : ℝ)) (width := (87 / 100 : ℝ)) (firstHeight := (457 / 500 : ℝ)) (secondHeight := (19 / 25 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Bentz.weighted_bound_first (by norm_num) (by norm_num))
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨0, ?_⟩
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨5, ?_⟩
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (87 / 50 : ℝ)) (width := (19 / 25 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨4, ?_⟩
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨13, ?_⟩
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (457 / 500 : ℝ)) (width := (27 / 125 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨6, ?_⟩
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨1, ?_⟩
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (3 / 5 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (5 / 2 : ℝ)) (width := (3 / 5 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨13, ?_⟩
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨14, ?_⟩
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (457 / 500 : ℝ)) (width := (27 / 125 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (457 / 500 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (457 / 500 : ℝ) + (27 / 125 : ℝ); linarith) (by change (27 / 125 : ℝ) * square.center.x ≤ (27 / 125 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (457 / 500 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨0, ?_⟩
      apply (square.swap_contains_iff (adjacentR2LeftPoints 0)).1
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨7, ?_⟩
      apply (square.swap_contains_iff (adjacentR2LeftPoints 7)).1
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (113 / 100 : ℝ)) (width := (69 / 100 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (113 / 100 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (113 / 100 : ℝ) + (69 / 100 : ℝ); linarith) (by change (69 / 100 : ℝ) * square.center.x ≤ (69 / 100 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (113 / 100 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨7, ?_⟩
      apply (square.swap_contains_iff (adjacentR2LeftPoints 7)).1
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨8, ?_⟩
      apply (square.swap_contains_iff (adjacentR2LeftPoints 8)).1
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (49 / 25 : ℝ)) ∧ 0 ≤ ((-7 / 50 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (721 / 1250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (91 / 50 : ℝ)) (width := (7 / 50 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (19 / 25 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (91 / 50 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (91 / 50 : ℝ) + (7 / 50 : ℝ); linarith) (by change (7 / 50 : ℝ) * square.center.x ≤ (7 / 50 : ℝ) * (1 : ℝ) + ((19 / 25 : ℝ) - (1 : ℝ)) * (square.center.y - (91 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨8, ?_⟩
      apply (square.swap_contains_iff (adjacentR2LeftPoints 8)).1
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨9, ?_⟩
      apply (square.swap_contains_iff (adjacentR2LeftPoints 9)).1
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-49 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (68 / 25 : ℝ)) ∧ 0 ≤ ((-19 / 25 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (67 / 625 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (49 / 25 : ℝ)) (width := (19 / 25 : ℝ)) (firstHeight := (19 / 25 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (49 / 25 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (49 / 25 : ℝ) + (19 / 25 : ℝ); linarith) (by change (19 / 25 : ℝ) * square.center.x ≤ (19 / 25 : ℝ) * (19 / 25 : ℝ) + ((1 : ℝ) - (19 / 25 : ℝ)) * (square.center.y - (49 / 25 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨9, ?_⟩
      apply (square.swap_contains_iff (adjacentR2LeftPoints 9)).1
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨18, ?_⟩
      apply (square.swap_contains_iff (adjacentR2LeftPoints 18)).1
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-68 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (68 / 25 : ℝ)) (width := (7 / 25 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (68 / 25 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (68 / 25 : ℝ) + (7 / 25 : ℝ); linarith) (by change (7 / 25 : ℝ) * square.center.x ≤ (7 / 25 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (68 / 25 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨18, ?_⟩
      apply (square.swap_contains_iff (adjacentR2LeftPoints 18)).1
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨19, ?_⟩
      apply (square.swap_contains_iff (adjacentR2LeftPoints 19)).1
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((9 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-2079 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (5 / 2 : ℝ)) (width := (3 / 5 : ℝ)) (firstHeight := (91 / 100 : ℝ)) (secondHeight := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (5 / 2 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (5 / 2 : ℝ) + (3 / 5 : ℝ); linarith) (by change (3 / 5 : ℝ) * (4 - square.center.y) ≤ (3 / 5 : ℝ) * (91 / 100 : ℝ) + ((1 : ℝ) - (91 / 100 : ℝ)) * (square.center.x - (5 / 2 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨11, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR2LeftPoints 11)).1
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨21, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR2LeftPoints 21)).1
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (1 : ℝ)) (width := (4 / 5 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (1 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (1 : ℝ) + (4 / 5 : ℝ); linarith) (by change (4 / 5 : ℝ) * (4 - square.center.y) ≤ (4 / 5 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.x - (1 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨19, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR2LeftPoints 19)).1
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨20, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR2LeftPoints 20)).1
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-969 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (9 / 5 : ℝ)) (width := (7 / 10 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (91 / 100 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (9 / 5 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (9 / 5 : ℝ) + (7 / 10 : ℝ); linarith) (by change (7 / 10 : ℝ) * (4 - square.center.y) ≤ (7 / 10 : ℝ) * (1 : ℝ) + ((91 / 100 : ℝ) - (1 : ℝ)) * (square.center.x - (9 / 5 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨20, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR2LeftPoints 20)).1
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨11, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR2LeftPoints 11)).1
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := (square.reflectX 4).swap.contains_bottomLowPair (left := (1 : ℝ)) (gap := (1 : ℝ)) (targetHeight := (9 / 10 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) (by norm_num) (by norm_num)
      (by change (1 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (1 : ℝ) + (1 : ℝ); linarith) (by change (4 - square.center.x) ≤ (9 / 10 : ℝ); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨14, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR2LeftPoints 14)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR2LeftPoints 14).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨17, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR2LeftPoints 17)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR2LeftPoints 17).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := (square.reflectX 4).swap.contains_bottomLowPair (left := (2 : ℝ)) (gap := (1 : ℝ)) (targetHeight := (9 / 10 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) (by norm_num) (by norm_num)
      (by change (2 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (2 : ℝ) + (1 : ℝ); linarith) (by change (4 - square.center.x) ≤ (9 / 10 : ℝ); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨17, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR2LeftPoints 17)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR2LeftPoints 17).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨21, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR2LeftPoints 21)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR2LeftPoints 21).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentR2LeftPoints, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]

end SquarePackingArchive.BentzThirteen
