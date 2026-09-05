import SquarePackingArchive.BentzAdjacentR3Data

namespace SquarePackingArchive.BentzThirteen

set_option maxRecDepth 10000

def adjacentR3Region (index : Fin 48) (center : Point) : Prop :=
  match index.val with
  | 0 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (49 / 100 : ℝ))
  | 1 => 0 ≤ ((-43 / 500 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * center.x + (0 : ℝ) * center.y + (-453 / 500 : ℝ))
  | 2 => 0 ≤ ((6 / 25 : ℝ) * center.x + (37 / 50 : ℝ) * center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (-13 / 100 : ℝ) * center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-61 / 100 : ℝ) * center.y + (61 / 100 : ℝ))
  | 3 => 0 ≤ ((6 / 25 : ℝ) * center.x + (47 / 100 : ℝ) * center.y + (-403 / 500 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (43 / 100 : ℝ) * center.y + (61 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-9 / 10 : ℝ) * center.y + (9 / 10 : ℝ))
  | 4 => 0 ≤ ((-4 / 5 : ℝ) * center.x + (2 / 5 : ℝ) * center.y + (18 / 25 : ℝ)) ∧ 0 ≤ ((-1 / 50 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (369 / 250 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (2 / 5 : ℝ) * center.y + (-387 / 250 : ℝ))
  | 5 => 0 ≤ ((0 : ℝ) * center.x + (9 / 10 : ℝ) * center.y + (-9 / 10 : ℝ)) ∧ 0 ≤ ((-4 / 5 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (117 / 50 : ℝ)) ∧ 0 ≤ ((4 / 5 : ℝ) * center.x + (-2 / 5 : ℝ) * center.y + (-18 / 25 : ℝ))
  | 6 => 0 ≤ ((-41 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (293 / 500 : ℝ) * center.y + (-293 / 500 : ℝ))
  | 7 => 0 ≤ ((-4 / 5 : ℝ) * center.x + (3 / 10 : ℝ) * center.y + (9 / 10 : ℝ)) ∧ 0 ≤ ((-1 / 50 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (369 / 250 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-173 / 100 : ℝ))
  | 8 => 0 ≤ ((-8 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (8 / 25 : ℝ)) ∧ 0 ≤ ((9 / 50 : ℝ) * center.x + (-6 / 25 : ℝ) * center.y + (417 / 1250 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * center.x + (6 / 25 : ℝ) * center.y + (-721 / 1250 : ℝ))
  | 9 => 0 ≤ ((1 / 50 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-369 / 250 : ℝ)) ∧ 0 ≤ ((-17 / 50 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (513 / 250 : ℝ)) ∧ 0 ≤ ((8 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (-8 / 25 : ℝ))
  | 10 => 0 ≤ ((-7 / 25 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-21 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (183 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (-27 / 20 : ℝ))
  | 11 => 0 ≤ ((-27 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((14 / 25 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (63 / 250 : ℝ)) ∧ 0 ≤ ((-1 / 50 : ℝ) * center.x + (7 / 10 : ℝ) * center.y + (-153 / 125 : ℝ))
  | 12 => 0 ≤ ((-27 / 50 : ℝ) * center.x + (0 : ℝ) * center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((11 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (63 / 100 : ℝ)) ∧ 0 ≤ ((8 / 25 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-171 / 100 : ℝ))
  | 13 => 0 ≤ ((-1 / 25 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-81 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (18 / 25 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (21 / 100 : ℝ))
  | 14 => 0 ≤ ((41 / 50 : ℝ) * center.x + (-1 / 5 : ℝ) * center.y + (-843 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (3 / 4 : ℝ) * center.y + (-3 / 4 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (-11 / 20 : ℝ) * center.y + (3051 / 1000 : ℝ))
  | 15 => 0 ≤ ((1 / 50 : ℝ) * center.x + (-7 / 10 : ℝ) * center.y + (153 / 125 : ℝ)) ∧ 0 ≤ ((4 / 5 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-117 / 50 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * center.x + (1 / 5 : ℝ) * center.y + (843 / 500 : ℝ))
  | 16 => 0 ≤ ((41 / 50 : ℝ) * center.x + (11 / 20 : ℝ) * center.y + (-3051 / 1000 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * center.x + (-1 / 20 : ℝ) * center.y + (2673 / 1000 : ℝ)) ∧ 0 ≤ ((1 / 25 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (81 / 100 : ℝ))
  | 17 => 0 ≤ ((13 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-183 / 100 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * center.x + (1 / 10 : ℝ) * center.y + (249 / 100 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (-23 / 125 : ℝ))
  | 18 => 0 ≤ ((-16 / 25 : ℝ) * center.x + (-1 / 5 : ℝ) * center.y + (259 / 125 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * center.x + (-3 / 10 : ℝ) * center.y + (-539 / 500 : ℝ)) ∧ 0 ≤ ((-11 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-63 / 100 : ℝ))
  | 19 => 0 ≤ ((-16 / 25 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (23 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * center.x + (1 / 5 : ℝ) * center.y + (-259 / 125 : ℝ))
  | 20 => 0 ≤ ((-17 / 50 : ℝ) * center.x + (1 / 5 : ℝ) * center.y + (63 / 250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (107 / 50 : ℝ)) ∧ 0 ≤ ((17 / 50 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-513 / 250 : ℝ))
  | 21 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (279 / 100 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * center.x + (-1 / 2 : ℝ) * center.y + (21 / 100 : ℝ))
  | 22 => 0 ≤ ((-43 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-21 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-11 / 20 : ℝ) * center.y + (33 / 20 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * center.x + (1 / 20 : ℝ) * center.y + (-967 / 1000 : ℝ))
  | 23 => 0 ≤ ((-43 / 50 : ℝ) * center.x + (3 / 10 : ℝ) * center.y + (539 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * center.x + (1 / 2 : ℝ) * center.y + (-279 / 100 : ℝ))
  | 24 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 25 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-147 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (217 / 100 : ℝ))
  | 26 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-41 / 100 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (111 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-161 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (231 / 100 : ℝ))
  | 27 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-61 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 28 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-29 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (43 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-29 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (43 / 20 : ℝ))
  | 29 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-179 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (249 / 100 : ℝ))
  | 30 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (19 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))
  | 31 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))
  | 32 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-7 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * center.x + (-47 / 100 : ℝ) * center.y + (403 / 500 : ℝ))
  | 33 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-3 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (23 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (4 / 5 : ℝ))
  | 34 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-27 / 125 : ℝ) * center.y + (27 / 125 : ℝ))
  | 35 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (7 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-243 / 500 : ℝ) * center.y + (243 / 500 : ℝ))
  | 36 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-23 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (61 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-3 / 4 : ℝ) * center.y + (3 / 4 : ℝ))
  | 37 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * center.x + (0 : ℝ) * center.y + (27 / 125 : ℝ))
  | 38 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * center.x + (0 : ℝ) * center.y + (69 / 100 : ℝ))
  | 39 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (49 / 25 : ℝ)) ∧ 0 ≤ ((-7 / 50 : ℝ) * center.x + (-6 / 25 : ℝ) * center.y + (721 / 1250 : ℝ))
  | 40 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (107 / 50 : ℝ)) ∧ 0 ≤ ((-8 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (8 / 25 : ℝ))
  | 41 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * center.x + (-1 / 20 : ℝ) * center.y + (967 / 1000 : ℝ))
  | 42 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-19 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (11 / 20 : ℝ) * center.y + (-33 / 20 : ℝ))
  | 43 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-3 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (23 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-12 / 5 : ℝ))
  | 44 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-23 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-12 / 5 : ℝ))
  | 45 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-21 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * center.x + (-1 / 10 : ℝ) * center.y + (-249 / 100 : ℝ))
  | 46 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-93 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (21 / 10 : ℝ)) ∧ 0 ≤ ((6 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (-18 / 25 : ℝ))
  | _ => 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (93 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * center.x + (1 / 20 : ℝ) * center.y + (-2673 / 1000 : ℝ))

set_option maxHeartbeats 4000000 in
theorem adjacentR3_hit_boundary (square : PlacedSquare) (fits : square.Fits 4)
    (index : Fin 48) (membership : adjacentR3Region index square.center) :
    adjacentR3Outcome square := by
  fin_cases index
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (49 / 100 : ℝ)) at membership
    norm_num at membership
    exfalso
    have bounds := center_inside_half_margin fits
    linarith [bounds.1, bounds.2.1, bounds.2.2.1, bounds.2.2.2]
  · change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![0, 3, 8]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![1, 5, 4]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (47 / 100 : ℝ) * square.center.y + (-403 / 500 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (43 / 100 : ℝ) * square.center.y + (61 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![2, 5, 13]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (18 / 25 : ℝ)) ∧ 0 ≤ ((-1 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (369 / 250 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-387 / 250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![2, 15, 8]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-9 / 10 : ℝ)) ∧ 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) ∧ 0 ≤ ((4 / 5 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-18 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![2, 13, 15]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![3, 8, 6]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ)) ∧ 0 ≤ ((-1 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (369 / 250 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![3, 15, 8]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-8 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 25 : ℝ)) ∧ 0 ≤ ((9 / 50 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (417 / 1250 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-721 / 1250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![8, 17, 9]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((1 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-369 / 250 : ℝ)) ∧ 0 ≤ ((-17 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (513 / 250 : ℝ)) ∧ 0 ≤ ((8 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![8, 15, 17]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (183 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![10, 12, 11]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((14 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (63 / 250 : ℝ)) ∧ 0 ≤ ((-1 / 50 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-153 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![10, 11, 15]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((11 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (63 / 100 : ℝ)) ∧ 0 ≤ ((8 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-171 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![10, 11, 18]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-1 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-81 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (18 / 25 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![10, 16, 12]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-843 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (3 / 4 : ℝ) * square.center.y + (-3 / 4 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (3051 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![10, 13, 14]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((1 / 50 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (153 / 125 : ℝ)) ∧ 0 ≤ ((4 / 5 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-117 / 50 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (843 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![10, 15, 13]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((41 / 50 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-3051 / 1000 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 20 : ℝ) * square.center.y + (2673 / 1000 : ℝ)) ∧ 0 ≤ ((1 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (81 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![10, 14, 16]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-183 / 100 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (249 / 100 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-23 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![11, 12, 22]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (259 / 125 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-539 / 500 : ℝ)) ∧ 0 ≤ ((-11 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-63 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![11, 21, 18]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (23 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-259 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![11, 22, 21]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-17 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (63 / 250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) ∧ 0 ≤ ((17 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-513 / 250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![15, 18, 17]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (279 / 100 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![17, 18, 20]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (33 / 20 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (1 / 20 : ℝ) * square.center.y + (-967 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![17, 20, 19]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (539 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    apply square.contains_indexed_triangleVertex adjacentR3Points ![18, 21, 20]
    all_goals norm_num [adjacentR3Points, Point.orientedArea, Matrix.cons_val_two]
    all_goals linarith
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := square.contains_cornerPoint (targetX := (457 / 500 : ℝ)) (targetY := (1 : ℝ)) fits (by norm_num) (by norm_num)
      (by linarith) (by linarith)
    refine ⟨6, ?_⟩
    convert contained using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-147 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (217 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨8, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR3Points]; linarith)
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-41 / 100 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (111 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-161 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (231 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨9, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR3Points]; linarith)
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-61 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := (square.reflectX 4).contains_cornerPoint (targetX := (19 / 20 : ℝ)) (targetY := (1 : ℝ)) ((square.reflectX_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by change (4 - square.center.x) ≤ (19 / 20 : ℝ); linarith) (by change square.center.y ≤ (1 : ℝ); linarith)
    refine ⟨14, ?_⟩
    apply (square.reflectX_contains_iff 4 (adjacentR3Points 14)).1
    convert contained using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-29 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (43 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-29 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (43 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨15, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR3Points]; linarith)
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-179 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (249 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2, plane_3⟩ := membership
    refine ⟨17, contains_of_center_box (horizontalRadius := (7 / 20 : ℝ)) (verticalRadius := (7 / 20 : ℝ)) (by norm_num) ?_ ?_ ?_ ?_⟩
    all_goals (norm_num [adjacentR3Points]; linarith)
  · change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := (square.reflectY 4).contains_cornerPoint (targetX := (19 / 20 : ℝ)) (targetY := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by change square.center.x ≤ (19 / 20 : ℝ); linarith) (by change (4 - square.center.y) ≤ (1 : ℝ); linarith)
    refine ⟨19, ?_⟩
    apply (square.reflectY_contains_iff 4 (adjacentR3Points 19)).1
    convert contained using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1⟩ := membership
    have contained := ((square.reflectX 4).reflectY 4).contains_cornerPoint (targetX := (9 / 10 : ℝ)) (targetY := (1 : ℝ)) (((square.reflectX 4).reflectY_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num)
      (by change (4 - square.center.x) ≤ (9 / 10 : ℝ); linarith) (by change (4 - square.center.y) ≤ (1 : ℝ); linarith)
    refine ⟨22, ?_⟩
    apply (square.reflectX_contains_iff 4 (adjacentR3Points 22)).1
    apply ((square.reflectX 4).reflectY_contains_iff 4 ((adjacentR3Points 22).reflectX 4)).1
    convert contained using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-47 / 100 : ℝ) * square.center.y + (403 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (7 / 5 : ℝ)) (width := (47 / 100 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (19 / 25 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨2, ?_⟩
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨5, ?_⟩
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (3 / 2 : ℝ)) (width := (4 / 5 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨3, ?_⟩
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨13, ?_⟩
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (457 / 500 : ℝ)) (width := (27 / 125 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨6, ?_⟩
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨1, ?_⟩
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-243 / 500 : ℝ) * square.center.y + (243 / 500 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (457 / 500 : ℝ)) (width := (243 / 500 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨6, ?_⟩
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨2, ?_⟩
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (61 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-3 / 4 : ℝ) * square.center.y + (3 / 4 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square) (left := (23 / 10 : ℝ)) (width := (3 / 4 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) fits
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith) (by linarith) (by linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨13, ?_⟩
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨14, ?_⟩
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 125 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (457 / 500 : ℝ)) (width := (27 / 125 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (457 / 500 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (457 / 500 : ℝ) + (27 / 125 : ℝ); linarith) (by change (27 / 125 : ℝ) * square.center.x ≤ (27 / 125 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (457 / 500 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨0, ?_⟩
      apply (square.swap_contains_iff (adjacentR3Points 0)).1
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨7, ?_⟩
      apply (square.swap_contains_iff (adjacentR3Points 7)).1
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (113 / 100 : ℝ)) (width := (69 / 100 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (113 / 100 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (113 / 100 : ℝ) + (69 / 100 : ℝ); linarith) (by change (69 / 100 : ℝ) * square.center.x ≤ (69 / 100 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (113 / 100 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨7, ?_⟩
      apply (square.swap_contains_iff (adjacentR3Points 7)).1
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨8, ?_⟩
      apply (square.swap_contains_iff (adjacentR3Points 8)).1
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (49 / 25 : ℝ)) ∧ 0 ≤ ((-7 / 50 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (721 / 1250 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (91 / 50 : ℝ)) (width := (7 / 50 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (19 / 25 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (91 / 50 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (91 / 50 : ℝ) + (7 / 50 : ℝ); linarith) (by change (7 / 50 : ℝ) * square.center.x ≤ (7 / 50 : ℝ) * (1 : ℝ) + ((19 / 25 : ℝ) - (1 : ℝ)) * (square.center.y - (91 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨8, ?_⟩
      apply (square.swap_contains_iff (adjacentR3Points 8)).1
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨9, ?_⟩
      apply (square.swap_contains_iff (adjacentR3Points 9)).1
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) ∧ 0 ≤ ((-8 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := square.swap) (left := (91 / 50 : ℝ)) (width := (8 / 25 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (91 / 50 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (91 / 50 : ℝ) + (8 / 25 : ℝ); linarith) (by change (8 / 25 : ℝ) * square.center.x ≤ (8 / 25 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (91 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨8, ?_⟩
      apply (square.swap_contains_iff (adjacentR3Points 8)).1
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨17, ?_⟩
      apply (square.swap_contains_iff (adjacentR3Points 17)).1
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 20 : ℝ) * square.center.y + (967 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Bentz.contains_descending_pair (square := square.swap) (left := (107 / 50 : ℝ)) (width := (43 / 50 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (19 / 20 : ℝ)) ((square.swap_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Bentz.weighted_bound_r3 (by norm_num) (by norm_num))
      (by change (107 / 50 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (107 / 50 : ℝ) + (43 / 50 : ℝ); linarith) (by change (43 / 50 : ℝ) * square.center.x ≤ (43 / 50 : ℝ) * (1 : ℝ) + ((19 / 20 : ℝ) - (1 : ℝ)) * (square.center.y - (107 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨17, ?_⟩
      apply (square.swap_contains_iff (adjacentR3Points 17)).1
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨19, ?_⟩
      apply (square.swap_contains_iff (adjacentR3Points 19)).1
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-33 / 20 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (19 / 20 : ℝ)) (width := (11 / 20 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (19 / 20 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (19 / 20 : ℝ) + (11 / 20 : ℝ); linarith) (by change (11 / 20 : ℝ) * (4 - square.center.y) ≤ (11 / 20 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.x - (19 / 20 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨19, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR3Points 19)).1
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨20, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR3Points 20)).1
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (3 / 2 : ℝ)) (width := (4 / 5 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (3 / 2 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (3 / 2 : ℝ) + (4 / 5 : ℝ); linarith) (by change (4 / 5 : ℝ) * (4 - square.center.y) ≤ (4 / 5 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.x - (3 / 2 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨20, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR3Points 20)).1
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨21, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR3Points 21)).1
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4)) (left := (23 / 10 : ℝ)) (width := (4 / 5 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (23 / 10 : ℝ) ≤ square.center.x; linarith) (by change square.center.x ≤ (23 / 10 : ℝ) + (4 / 5 : ℝ); linarith) (by change (4 / 5 : ℝ) * (4 - square.center.y) ≤ (4 / 5 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.x - (23 / 10 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨21, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR3Points 21)).1
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨22, ?_⟩
      apply (square.reflectY_contains_iff 4 (adjacentR3Points 22)).1
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-21 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (-249 / 100 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Bentz.contains_descending_pair (square := (square.reflectX 4).swap) (left := (21 / 10 : ℝ)) (width := (9 / 10 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (9 / 10 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Bentz.weighted_bound_second (by norm_num) (by norm_num))
      (by change (21 / 10 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (21 / 10 : ℝ) + (9 / 10 : ℝ); linarith) (by change (9 / 10 : ℝ) * (4 - square.center.x) ≤ (9 / 10 : ℝ) * (1 : ℝ) + ((9 / 10 : ℝ) - (1 : ℝ)) * (square.center.y - (21 / 10 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨12, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR3Points 12)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR3Points 12).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨22, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR3Points 22)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR3Points 22).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-93 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ)) ∧ 0 ≤ ((6 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-18 / 25 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectX 4).swap) (left := (93 / 50 : ℝ)) (width := (6 / 25 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ)) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by change (93 / 50 : ℝ) ≤ square.center.y; linarith) (by change square.center.y ≤ (93 / 50 : ℝ) + (6 / 25 : ℝ); linarith) (by change (6 / 25 : ℝ) * (4 - square.center.x) ≤ (6 / 25 : ℝ) * (1 : ℝ) + ((1 : ℝ) - (1 : ℝ)) * (square.center.y - (93 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨16, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR3Points 16)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR3Points 16).reflectX 4)).1
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨12, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR3Points 12)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR3Points 12).reflectX 4)).1
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
  · change 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (93 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (1 / 20 : ℝ) * square.center.y + (-2673 / 1000 : ℝ)) at membership
    norm_num at membership
    obtain ⟨plane_0, plane_1, plane_2⟩ := membership
    have pair := Bentz.contains_descending_pair (square := ((square.reflectX 4).swap.reflectX 4)) (left := (107 / 50 : ℝ)) (width := (43 / 50 : ℝ)) (firstHeight := (1 : ℝ)) (secondHeight := (19 / 20 : ℝ)) (((square.reflectX 4).swap.reflectX_fits_iff 4).2 (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Bentz.weighted_bound_r3 (by norm_num) (by norm_num))
      (by change (107 / 50 : ℝ) ≤ (4 - square.center.y); linarith) (by change (4 - square.center.y) ≤ (107 / 50 : ℝ) + (43 / 50 : ℝ); linarith) (by change (43 / 50 : ℝ) * (4 - square.center.x) ≤ (43 / 50 : ℝ) * (1 : ℝ) + ((19 / 20 : ℝ) - (1 : ℝ)) * ((4 - square.center.y) - (107 / 50 : ℝ)); linarith)
    rcases pair with first_mem | second_mem
    · refine ⟨16, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR3Points 16)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR3Points 16).reflectX 4)).1
      apply (((square.reflectX 4).swap).reflectX_contains_iff 4 (((adjacentR3Points 16).reflectX 4).swap)).1
      convert first_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]
    · refine ⟨14, ?_⟩
      apply (square.reflectX_contains_iff 4 (adjacentR3Points 14)).1
      apply ((square.reflectX 4).swap_contains_iff ((adjacentR3Points 14).reflectX 4)).1
      apply (((square.reflectX 4).swap).reflectX_contains_iff 4 (((adjacentR3Points 14).reflectX 4).swap)).1
      convert second_mem using 1; norm_num [adjacentR3Points, Point.orientedArea, Point.reflectX, Point.reflectY, Point.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, PlacedSquare.swap]

end SquarePackingArchive.BentzThirteen
