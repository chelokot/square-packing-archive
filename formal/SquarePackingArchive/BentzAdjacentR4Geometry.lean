import SquarePackingArchive.BentzAdjacentR4Data

namespace SquarePackingArchive.BentzThirteen

set_option maxRecDepth 10000

def adjacentR4Region (index : Fin 54) (center : Point) : Prop :=
  match index.val with
  | 0 => 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (49 / 100 : ℝ))
  | 1 => 0 ≤ ((77 / 500 : ℝ) * center.x + (87 / 100 : ℝ) * center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (-37 / 100 : ℝ) * center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (371 / 1000 : ℝ))
  | 2 => 0 ≤ ((-43 / 500 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-293 / 500 : ℝ) * center.y + (293 / 500 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (-41151 / 250000 : ℝ))
  | 3 => 0 ≤ ((6 / 25 : ℝ) * center.x + (37 / 50 : ℝ) * center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (-13 / 100 : ℝ) * center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-61 / 100 : ℝ) * center.y + (61 / 100 : ℝ))
  | 4 => 0 ≤ ((0 : ℝ) * center.x + (61 / 100 : ℝ) * center.y + (-61 / 100 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (-6 / 25 : ℝ) * center.y + (4167 / 2500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-37 / 100 : ℝ) * center.y + (-2783 / 5000 : ℝ))
  | 5 => 0 ≤ ((6 / 25 : ℝ) * center.x + (37 / 100 : ℝ) * center.y + (-73 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (63 / 100 : ℝ) * center.y + (-3 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 6 => 0 ≤ ((-41 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (123 / 100 : ℝ)) ∧ 0 ≤ ((69 / 100 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (-1 / 8 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-139 / 200 : ℝ))
  | 7 => 0 ≤ ((-13 / 100 : ℝ) * center.x + (-37 / 50 : ℝ) * center.y + (4831 / 5000 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (413 / 500 : ℝ) * center.y + (-413 / 500 : ℝ))
  | 8 => 0 ≤ ((-3 / 5 : ℝ) * center.x + (33 / 50 : ℝ) * center.y + (48 / 125 : ℝ)) ∧ 0 ≤ ((-11 / 50 : ℝ) * center.x + (-9 / 10 : ℝ) * center.y + (246 / 125 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (-4167 / 2500 : ℝ))
  | 9 => 0 ≤ ((0 : ℝ) * center.x + (19 / 25 : ℝ) * center.y + (-19 / 25 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * center.x + (-1 / 10 : ℝ) * center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * center.x + (-33 / 50 : ℝ) * center.y + (-48 / 125 : ℝ))
  | 10 => 0 ≤ ((-69 / 100 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (1 / 8 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (91 / 100 : ℝ)) ∧ 0 ≤ ((69 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (-69 / 100 : ℝ))
  | 11 => 0 ≤ ((-69 / 100 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (1 / 8 : ℝ)) ∧ 0 ≤ ((-7 / 50 : ℝ) * center.x + (-37 / 50 : ℝ) * center.y + (973 / 625 : ℝ)) ∧ 0 ≤ ((83 / 100 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (-2753 / 2500 : ℝ))
  | 12 => 0 ≤ ((-97 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (97 / 100 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * center.x + (-6 / 25 : ℝ) * center.y + (91 / 250 : ℝ)) ∧ 0 ≤ ((83 / 100 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (-2753 / 2500 : ℝ))
  | 13 => 0 ≤ ((0 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-91 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (81 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (37 / 100 : ℝ))
  | 14 => 0 ≤ ((-27 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-37 / 100 : ℝ)) ∧ 0 ≤ ((13 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (79 / 100 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (-7 / 25 : ℝ))
  | 15 => 0 ≤ ((-7 / 25 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-49 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (157 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (-81 / 100 : ℝ))
  | 16 => 0 ≤ ((11 / 50 : ℝ) * center.x + (9 / 10 : ℝ) * center.y + (-246 / 125 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * center.x + (-2 / 5 : ℝ) * center.y + (46 / 25 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (49 / 100 : ℝ))
  | 17 => 0 ≤ ((-16 / 25 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (297 / 125 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * center.x + (1 / 10 : ℝ) * center.y + (-111 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-79 / 100 : ℝ))
  | 18 => 0 ≤ ((13 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-157 / 100 : ℝ)) ∧ 0 ≤ ((-2 / 5 : ℝ) * center.x + (2 / 5 : ℝ) * center.y + (-1 / 25 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * center.x + (-9 / 10 : ℝ) * center.y + (957 / 500 : ℝ))
  | 19 => 0 ≤ ((13 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-157 / 100 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * center.x + (-3 / 10 : ℝ) * center.y + (243 / 100 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * center.x + (-1 / 5 : ℝ) * center.y + (-61 / 125 : ℝ))
  | 20 => 0 ≤ ((-7 / 50 : ℝ) * center.x + (9 / 10 : ℝ) * center.y + (-957 / 500 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (59 / 20 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * center.x + (-1 / 5 : ℝ) * center.y + (-61 / 125 : ℝ))
  | 21 => 0 ≤ ((-16 / 25 : ℝ) * center.x + (1 / 5 : ℝ) * center.y + (61 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-297 / 125 : ℝ))
  | 22 => 0 ≤ ((1 / 2 : ℝ) * center.x + (2 / 5 : ℝ) * center.y + (-46 / 25 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * center.x + (0 : ℝ) * center.y + (54 / 25 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * center.x + (-2 / 5 : ℝ) * center.y + (1 / 25 : ℝ))
  | 23 => 0 ≤ ((0 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-3 / 5 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (64 / 25 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * center.x + (1 / 10 : ℝ) * center.y + (-8 / 5 : ℝ))
  | 24 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (4 / 25 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-64 / 25 : ℝ))
  | 25 => 0 ≤ ((-2 / 5 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-4 / 25 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (59 / 20 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * center.x + (0 : ℝ) * center.y + (-54 / 25 : ℝ))
  | 26 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (11 / 20 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-59 / 20 : ℝ))
  | 27 => 0 ≤ ((-1 / 2 : ℝ) * center.x + (1 / 10 : ℝ) * center.y + (19 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-59 / 20 : ℝ))
  | 28 => 0 ≤ ((-1 / 2 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-11 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (9 / 5 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * center.x + (-1 / 10 : ℝ) * center.y + (-19 / 20 : ℝ))
  | 29 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 30 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-41 / 100 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (111 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-161 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (231 / 100 : ℝ))
  | 31 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-23 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (37 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-147 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (217 / 100 : ℝ))
  | 32 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-33 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (47 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-7 / 4 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (49 / 20 : ℝ))
  | 33 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 34 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-11 / 4 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (69 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-33 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (47 / 20 : ℝ))
  | 35 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-11 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (5 / 4 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-53 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (67 / 20 : ℝ))
  | 36 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (9 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))
  | 37 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))
  | 38 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (-13 / 100 : ℝ) * center.y + (1641 / 50000 : ℝ))
  | 39 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (371 / 1000 : ℝ))
  | 40 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * center.x + (-87 / 100 : ℝ) * center.y + (47459 / 50000 : ℝ))
  | 41 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-7 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (-47 / 100 : ℝ) * center.y + (403 / 500 : ℝ))
  | 42 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-19 / 25 : ℝ) * center.y + (19 / 25 : ℝ))
  | 43 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-27 / 125 : ℝ) * center.y + (27 / 125 : ℝ))
  | 44 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (3 / 5 : ℝ))
  | 45 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * center.x + (0 : ℝ) * center.y + (27 / 125 : ℝ))
  | 46 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (69 / 100 : ℝ))
  | 47 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (21 / 10 : ℝ)) ∧ 0 ≤ ((-7 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (7 / 25 : ℝ))
  | 48 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-21 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * center.x + (-1 / 10 : ℝ) * center.y + (111 / 100 : ℝ))
  | 49 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-9 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (17 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-12 / 5 : ℝ))
  | 50 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-17 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-12 / 5 : ℝ))
  | 51 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-9 / 5 : ℝ))
  | 52 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (2 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-31 / 10 : ℝ))
  | _ => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-31 / 10 : ℝ))

set_option maxHeartbeats 4000000 in
theorem adjacentR4_hit_boundary (square : PlacedSquare) (fits : square.Fits 4)
    (index : Fin 54) (membership : adjacentR4Region index square.center) :
    adjacentR4Outcome square := by
  fin_cases index
  · change 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (49 / 100 : ℝ)) at membership
    norm_num at membership
    exfalso
    have bounds := center_inside_half_margin fits
    linarith [bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2]
  · change 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![0, 5, 3]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-41151 / 250000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![0, 3, 6]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![1, 5, 4]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (4167 / 2500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (-2783 / 5000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![1, 4, 10]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (63 / 100 : ℝ) * square.center.y + (-3 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![3, 5, 14]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 100 : ℝ)) ∧ 0 ≤ ((69 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-1 / 8 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-139 / 200 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![3, 10, 7]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-13 / 100 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (4831 / 5000 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (413 / 500 : ℝ) * square.center.y + (-413 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![4, 7, 6]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (48 / 125 : ℝ)) ∧ 0 ≤ ((-11 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (246 / 125 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-4167 / 2500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![4, 16, 10]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (-48 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![4, 14, 16]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (1 / 8 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (91 / 100 : ℝ)) ∧ 0 ≤ ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![7, 10, 8]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (1 / 8 : ℝ)) ∧ 0 ≤ ((-7 / 50 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (973 / 625 : ℝ)) ∧ 0 ≤ ((83 / 100 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-2753 / 2500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![7, 10, 9]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-97 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (97 / 100 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (91 / 250 : ℝ)) ∧ 0 ≤ ((83 / 100 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-2753 / 2500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![7, 12, 9]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-91 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (81 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (37 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![8, 10, 11]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) ∧ 0 ≤ ((13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (79 / 100 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![8, 11, 12]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-49 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (157 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-81 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![10, 13, 11]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((11 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-246 / 125 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (46 / 25 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (49 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![10, 16, 13]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (297 / 125 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (-111 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-79 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![11, 19, 12]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-157 / 100 : ℝ)) ∧ 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-1 / 25 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (957 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![11, 13, 18]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-157 / 100 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (243 / 100 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-61 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![11, 13, 20]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-7 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-957 / 500 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (59 / 20 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-61 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![11, 18, 20]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (61 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-297 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![11, 20, 19]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((1 / 2 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-46 / 25 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (54 / 25 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (1 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![13, 16, 18]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-3 / 5 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (64 / 25 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (-8 / 5 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![14, 15, 16]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (4 / 25 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-64 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![15, 17, 16]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-4 / 25 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (59 / 20 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-54 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![16, 17, 18]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (11 / 20 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-59 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![17, 22, 18]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (19 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-59 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![18, 21, 20]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-11 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (9 / 5 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (-19 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR4Points ![18, 22, 21]
    all_goals norm_num [adjacentR4Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := square.contains_cornerPoint (targetX := (457 / 500 : ℝ)) (targetY := (1 : ℝ)) fits (by norm_num) (by norm_num)
      (by linarith) (by linarith)
    refine ⟨6, ?_⟩
    convert contained using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-41 / 100 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (111 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-161 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (231 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨9, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR4Points]; linarith)
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (37 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-147 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (217 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨10, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR4Points]; linarith)
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-33 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (47 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-7 / 4 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (49 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨13, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR4Points]; linarith)
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := (square.reflectX 4).contains_cornerPoint (targetX := (9 / 10 : ℝ)) (targetY := (1 : ℝ)) ((square.reflectX_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by change (4 - square.center.x) ≤ (9 / 10 : ℝ); linarith) (by change square.center.y ≤ (1 : ℝ); linarith)
    refine ⟨15, ?_⟩
    apply (square.reflectX_contains_iff 4 (adjacentR4Points 15)).1
    convert contained using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-11 / 4 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-33 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (47 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨17, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR4Points]; linarith)
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-11 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 4 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-53 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (67 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨19, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR4Points]; linarith)
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := (square.reflectY 4).contains_cornerPoint (targetX := (9 / 10 : ℝ)) (targetY := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by change square.center.x ≤ (9 / 10 : ℝ); linarith) (by change (4 - square.center.y) ≤ (1 : ℝ); linarith)
    refine ⟨19, ?_⟩
    apply (square.reflectY_contains_iff 4 (adjacentR4Points 19)).1
    convert contained using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := ((square.reflectX 4).reflectY 4).contains_cornerPoint (targetX := (9 / 10 : ℝ)) (targetY := (1 : ℝ)) (((square.reflectX 4).reflectY_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num)
      (by change (4 - square.center.x) ≤ (9 / 10 : ℝ); linarith) (by change (4 - square.center.y) ≤ (1 : ℝ); linarith)
    refine ⟨22, ?_⟩
    apply (square.reflectX_contains_iff 4 (adjacentR4Points 22)).1
    apply ((square.reflectX 4).reflectY_contains_iff 4 ((adjacentR4Points 22).reflectX 4)).1
    convert contained using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1641 / 50000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (1 : ℝ)) (width := (13 / 100 : ℝ)) (firstHeight := (457 / 500 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨0, ?_⟩
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨1, ?_⟩
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (1 : ℝ)) (width := (1 / 2 : ℝ)) (firstHeight := (457 / 500 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨0, ?_⟩
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨3, ?_⟩
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Bentz.contains_descending_pair (square := square) (left := (1 : ℝ)) (width := (87 / 100 : ℝ)) (firstHeight := (457 / 500 : ℝ)) (secondHeight := (19 / 25 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Bentz.weighted_bound_first (by norm_num) (by norm_num))
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨0, ?_⟩
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨5, ?_⟩
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-47 / 100 : ℝ) * square.center.y + (403 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (7 / 5 : ℝ)) (width := (47 / 100 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (19 / 25 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨2, ?_⟩
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨5, ?_⟩
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (87 / 50 : ℝ)) (width := (19 / 25 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨4, ?_⟩
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨14, ?_⟩
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (457 / 500 : ℝ)) (width := (27 / 125 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨6, ?_⟩
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨1, ?_⟩
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (3 / 5 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (5 / 2 : ℝ)) (width := (3 / 5 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨14, ?_⟩
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨15, ?_⟩
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (457 / 500 : ℝ)) (width := (27 / 125 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (457 / 500 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (457 / 500 : ℝ) + (27 / 125 : ℝ); linarith) (by change (27 / 125 : ℝ) * square.center.x ≤ (27 / 125 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (457 / 500 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨0, ?_⟩
      apply (square.swap_contains_iff (adjacentR4Points 0)).1
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨7, ?_⟩
      apply (square.swap_contains_iff (adjacentR4Points 7)).1
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (113 / 100 : ℝ)) (width := (69 / 100 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (113 / 100 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (113 / 100 : ℝ) + (69 / 100 : ℝ); linarith) (by change (69 / 100 : ℝ) * square.center.x ≤ (69 / 100 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (113 / 100 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨7, ?_⟩
      apply (square.swap_contains_iff (adjacentR4Points 7)).1
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨8, ?_⟩
      apply (square.swap_contains_iff (adjacentR4Points 8)).1
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ)) ∧ 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (91 / 50 : ℝ)) (width := (7 / 25 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (91 / 50 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (91 / 50 : ℝ) + (7 / 25 : ℝ); linarith) (by change (7 / 25 : ℝ) * square.center.x ≤ (7 / 25 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (91 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨8, ?_⟩
      apply (square.swap_contains_iff (adjacentR4Points 8)).1
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨12, ?_⟩
      apply (square.swap_contains_iff (adjacentR4Points 12)).1
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-21 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (111 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Bentz.contains_descending_pair (square := square.swap) (left := (21 / 10 : ℝ)) (width := (9 / 10 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (9 / 10 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Bentz.weighted_bound_second (by norm_num) (by norm_num))
      (by change (21 / 10 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (21 / 10 : ℝ) + (9 / 10 : ℝ); linarith) (by change (9 / 10 : ℝ) * square.center.x ≤ (9 / 10 : ℝ) * (1 : ℝ) + ((9 / 10 : ℝ) - (1 : ℝ)) * (square.center.y - (21 / 10 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨12, ?_⟩
      apply (square.swap_contains_iff (adjacentR4Points 12)).1
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨19, ?_⟩
      apply (square.swap_contains_iff (adjacentR4Points 19)).1
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (17 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (9 / 10 : ℝ)) (width := (4 / 5 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (9 / 10 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (9 / 10 : ℝ) + (4 / 5 : ℝ); linarith) (by change (4 / 5 : ℝ) * (4 - square.center.y) ≤ (4 / 5 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.x - (9 / 10 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨19, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR4Points 19)).1
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨20, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR4Points 20)).1
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-17 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (17 / 10 : ℝ)) (width := (4 / 5 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (17 / 10 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (17 / 10 : ℝ) + (4 / 5 : ℝ); linarith) (by change (4 / 5 : ℝ) * (4 - square.center.y) ≤ (4 / 5 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.x - (17 / 10 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨20, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR4Points 20)).1
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨21, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR4Points 21)).1
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-9 / 5 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (5 / 2 : ℝ)) (width := (3 / 5 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (5 / 2 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (5 / 2 : ℝ) + (3 / 5 : ℝ); linarith) (by change (3 / 5 : ℝ) * (4 - square.center.y) ≤ (3 / 5 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.x - (5 / 2 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨21, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR4Points 21)).1
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨22, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR4Points 22)).1
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := (square.reflectX 4).swap.contains_bottomLowPair (left := (1 : ℝ)) (gap := (1 : ℝ)) (targetHeight := (9 / 10 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) (by norm_num) (by norm_num)
      (by change (1 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (1 : ℝ) + (1 : ℝ); linarith) (by change (4 - square.center.x) ≤ (9 / 10 : ℝ); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨15, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR4Points 15)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR4Points 15).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨17, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR4Points 17)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR4Points 17).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := (square.reflectX 4).swap.contains_bottomLowPair (left := (2 : ℝ)) (gap := (1 : ℝ)) (targetHeight := (9 / 10 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]) (by norm_num) (by norm_num)
      (by change (2 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (2 : ℝ) + (1 : ℝ); linarith) (by change (4 - square.center.x) ≤ (9 / 10 : ℝ); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨17, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR4Points 17)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR4Points 17).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨22, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR4Points 22)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR4Points 22).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentR4Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]

end SquarePackingArchive.BentzThirteen
