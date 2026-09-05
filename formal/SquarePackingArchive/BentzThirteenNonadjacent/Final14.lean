import SquarePackingArchive.BentzThirteenNonadjacentData

namespace SquarePackingArchive.BentzThirteen.Nonadjacent

noncomputable def final14Points : Fin 15 → Point := finalPoints (choicePattern 14)

def final14Region (index : Fin 34) (center : Point) : Prop :=
  match index.val with
  | 0 => 0 ≤ ((0 : ℝ) * center.x + (33 / 50 : ℝ) * center.y + (-33 / 50 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (-12 / 25 : ℝ) * center.y + (5381 / 2500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (-9 / 50 : ℝ) * center.y + (-251 / 250 : ℝ))
  | 1 => 0 ≤ ((-37 / 50 : ℝ) * center.x + (9 / 50 : ℝ) * center.y + (251 / 250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-39 / 50 : ℝ) * center.y + (3393 / 2500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-223 / 125 : ℝ))
  | 2 => 0 ≤ ((-37 / 50 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (223 / 125 : ℝ)) ∧ 0 ≤ ((413 / 500 : ℝ) * center.x + (0 : ℝ) * center.y + (-413 / 500 : ℝ)) ∧ 0 ≤ ((-43 / 500 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-289 / 625 : ℝ))
  | 3 => 0 ≤ ((-3 / 5 : ℝ) * center.x + (37 / 50 : ℝ) * center.y + (77 / 125 : ℝ)) ∧ 0 ≤ ((-2 / 5 : ℝ) * center.x + (-37 / 50 : ℝ) * center.y + (298 / 125 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-113 / 50 : ℝ))
  | 4 => 0 ≤ ((0 : ℝ) * center.x + (413 / 500 : ℝ) * center.y + (-413 / 500 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (1211 / 625 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * center.x + (-37 / 50 : ℝ) * center.y + (-77 / 125 : ℝ))
  | 5 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((13 / 50 : ℝ) * center.x + (-12 / 25 : ℝ) * center.y + (931 / 2500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (12 / 25 : ℝ) * center.y + (-5381 / 2500 : ℝ))
  | 6 => 0 ≤ ((-4 / 5 : ℝ) * center.x + (0 : ℝ) * center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * center.x + (-37 / 50 : ℝ) * center.y + (72 / 125 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * center.x + (37 / 50 : ℝ) * center.y + (-298 / 125 : ℝ))
  | 7 => 0 ≤ ((0 : ℝ) * center.x + (39 / 50 : ℝ) * center.y + (-3393 / 2500 : ℝ)) ∧ 0 ≤ ((-13 / 25 : ℝ) * center.x + (-39 / 50 : ℝ) * center.y + (5707 / 2500 : ℝ)) ∧ 0 ≤ ((13 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (-13 / 25 : ℝ))
  | 8 => 0 ≤ ((0 : ℝ) * center.x + (39 / 50 : ℝ) * center.y + (-3393 / 2500 : ℝ)) ∧ 0 ≤ ((-13 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (1157 / 1250 : ℝ)) ∧ 0 ≤ ((13 / 25 : ℝ) * center.x + (-39 / 50 : ℝ) * center.y + (2093 / 2500 : ℝ))
  | 9 => 0 ≤ ((-13 / 25 : ℝ) * center.x + (39 / 50 : ℝ) * center.y + (-2093 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-39 / 50 : ℝ) * center.y + (4407 / 2500 : ℝ)) ∧ 0 ≤ ((13 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (-13 / 25 : ℝ))
  | 10 => 0 ≤ ((-13 / 50 : ℝ) * center.x + (12 / 25 : ℝ) * center.y + (-931 / 2500 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * center.x + (-12 / 25 : ℝ) * center.y + (3869 / 2500 : ℝ)) ∧ 0 ≤ ((13 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (-1157 / 1250 : ℝ))
  | 11 => 0 ≤ ((-13 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (1157 / 1250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-39 / 50 : ℝ) * center.y + (4407 / 2500 : ℝ)) ∧ 0 ≤ ((13 / 25 : ℝ) * center.x + (39 / 50 : ℝ) * center.y + (-5707 / 2500 : ℝ))
  | 12 => 0 ≤ ((-2 / 5 : ℝ) * center.x + (37 / 50 : ℝ) * center.y + (-72 / 125 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * center.x + (-37 / 50 : ℝ) * center.y + (447 / 125 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-113 / 50 : ℝ))
  | 13 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (-12 / 25 : ℝ) * center.y + (-581 / 2500 : ℝ)) ∧ 0 ≤ ((13 / 50 : ℝ) * center.x + (12 / 25 : ℝ) * center.y + (-3869 / 2500 : ℝ))
  | 14 => 0 ≤ ((37 / 50 : ℝ) * center.x + (9 / 50 : ℝ) * center.y + (-431 / 250 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (12 / 25 : ℝ) * center.y + (581 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-33 / 50 : ℝ) * center.y + (99 / 50 : ℝ))
  | 15 => 0 ≤ ((37 / 50 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (77 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (39 / 50 : ℝ) * center.y + (-4407 / 2500 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (-9 / 50 : ℝ) * center.y + (431 / 250 : ℝ))
  | 16 => 0 ≤ ((0 : ℝ) * center.x + (-343 / 500 : ℝ) * center.y + (1029 / 500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (-23359 / 25000 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-77 / 125 : ℝ))
  | 17 => 0 ≤ ((3 / 5 : ℝ) * center.x + (37 / 50 : ℝ) * center.y + (-447 / 125 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (996 / 625 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-413 / 500 : ℝ) * center.y + (1239 / 500 : ℝ))
  | 18 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-33 / 50 : ℝ) * center.y + (33 / 50 : ℝ))
  | 19 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-413 / 500 : ℝ) * center.y + (413 / 500 : ℝ))
  | 20 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (289 / 625 : ℝ))
  | 21 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((-13 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (13 / 25 : ℝ))
  | 22 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (23359 / 25000 : ℝ))
  | 23 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (87 / 50 : ℝ)) ∧ 0 ≤ ((-413 / 500 : ℝ) * center.x + (0 : ℝ) * center.y + (413 / 500 : ℝ))
  | 24 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (33 / 50 : ℝ) * center.y + (-99 / 50 : ℝ))
  | 25 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (413 / 500 : ℝ) * center.y + (-1239 / 500 : ℝ))
  | 26 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (343 / 500 : ℝ) * center.y + (-1029 / 500 : ℝ))
  | 27 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((4 / 5 : ℝ) * center.x + (0 : ℝ) * center.y + (-12 / 5 : ℝ))
  | 28 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (-996 / 625 : ℝ))
  | 29 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (-1211 / 625 : ℝ))
  | 30 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (457 / 500 : ℝ))
  | 31 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 32 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))
  | _ => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))

set_option maxHeartbeats 4000000 in
lemma final14_hit_boundary (square : PlacedSquare) (fits : square.Fits 4)
    (index : Fin 34) (membership : final14Region index square.center) :
    (∃ index, square.Contains (final14Points index)) := by
  fin_cases index
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 0) (final14Points 1) (final14Points 4)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨0, first_inside⟩
    · exact ⟨1, second_inside⟩
    · exact ⟨4, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 0) (final14Points 4) (final14Points 3)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨0, first_inside⟩
    · exact ⟨4, second_inside⟩
    · exact ⟨3, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 0) (final14Points 3) (final14Points 11)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨0, first_inside⟩
    · exact ⟨3, second_inside⟩
    · exact ⟨11, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 1) (final14Points 2) (final14Points 5)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨1, first_inside⟩
    · exact ⟨2, second_inside⟩
    · exact ⟨5, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 1) (final14Points 12) (final14Points 2)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨1, first_inside⟩
    · exact ⟨12, second_inside⟩
    · exact ⟨2, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 1) (final14Points 5) (final14Points 4)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨1, first_inside⟩
    · exact ⟨5, second_inside⟩
    · exact ⟨4, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 2) (final14Points 8) (final14Points 5)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨2, first_inside⟩
    · exact ⟨8, second_inside⟩
    · exact ⟨5, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 3) (final14Points 4) (final14Points 9)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨3, first_inside⟩
    · exact ⟨4, second_inside⟩
    · exact ⟨9, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 3) (final14Points 4) (final14Points 10)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨3, first_inside⟩
    · exact ⟨4, second_inside⟩
    · exact ⟨10, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 3) (final14Points 10) (final14Points 9)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨3, first_inside⟩
    · exact ⟨10, second_inside⟩
    · exact ⟨9, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 4) (final14Points 5) (final14Points 10)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨4, first_inside⟩
    · exact ⟨5, second_inside⟩
    · exact ⟨10, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 4) (final14Points 10) (final14Points 9)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨4, first_inside⟩
    · exact ⟨10, second_inside⟩
    · exact ⟨9, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 5) (final14Points 8) (final14Points 7)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨5, first_inside⟩
    · exact ⟨8, second_inside⟩
    · exact ⟨7, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 5) (final14Points 7) (final14Points 10)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨5, first_inside⟩
    · exact ⟨7, second_inside⟩
    · exact ⟨10, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 6) (final14Points 10) (final14Points 7)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨6, first_inside⟩
    · exact ⟨10, second_inside⟩
    · exact ⟨7, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 6) (final14Points 9) (final14Points 10)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨6, first_inside⟩
    · exact ⟨9, second_inside⟩
    · exact ⟨10, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 6) (final14Points 13) (final14Points 9)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨6, first_inside⟩
    · exact ⟨13, second_inside⟩
    · exact ⟨9, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (final14Points 7) (final14Points 8) (final14Points 14)
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨7, first_inside⟩
    · exact ⟨8, second_inside⟩
    · exact ⟨14, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := Stromquist.TenPoints.contains_short_pair (square := square)
      (left := (8 / 5 : ℝ)) (width := (33 / 50 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      fits (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [bound_0])
      (by linarith only [bound_1])
      (by linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨0, ?_⟩
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨1, ?_⟩
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := square.contains_bottomSharpPair (left := (113 / 50 : ℝ))
      (gap := (413 / 500 : ℝ)) (targetHeight := 1) fits (by norm_num) (by norm_num)
      (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)])
      (by linarith only [bound_0])
      (by linarith only [bound_1])
      (by linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨1, ?_⟩
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨12, ?_⟩
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := Stromquist.TenPoints.contains_short_pair (square := square)
      (left := (1 : ℝ)) (width := (3 / 5 : ℝ))
      (firstHeight := (457 / 500 : ℝ)) (secondHeight := (1 : ℝ))
      fits (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [bound_0])
      (by linarith only [bound_1])
      (by linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨11, ?_⟩
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨0, ?_⟩
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.swap))
      (left := (87 / 50 : ℝ)) (width := (13 / 25 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      ((square.swap_fits_iff 4).2 fits) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨3, ?_⟩
      apply (square.swap_contains_iff (final14Points 3)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨9, ?_⟩
      apply (square.swap_contains_iff (final14Points 9)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.swap))
      (left := (113 / 50 : ℝ)) (width := (37 / 50 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (457 / 500 : ℝ))
      ((square.swap_fits_iff 4).2 fits) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨9, ?_⟩
      apply (square.swap_contains_iff (final14Points 9)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨13, ?_⟩
      apply (square.swap_contains_iff (final14Points 13)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := (square.swap).contains_bottomSharpPair (left := (457 / 500 : ℝ))
      (gap := (413 / 500 : ℝ)) (targetHeight := 1) ((square.swap_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨11, ?_⟩
      apply (square.swap_contains_iff (final14Points 11)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨3, ?_⟩
      apply (square.swap_contains_iff (final14Points 3)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4))
      (left := (8 / 5 : ℝ)) (width := (33 / 50 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨6, ?_⟩
      apply (square.reflectY_contains_iff 4 (final14Points 6)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨7, ?_⟩
      apply (square.reflectY_contains_iff 4 (final14Points 7)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := (square.reflectY 4).contains_bottomSharpPair (left := (113 / 50 : ℝ))
      (gap := (413 / 500 : ℝ)) (targetHeight := 1) ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨7, ?_⟩
      apply (square.reflectY_contains_iff 4 (final14Points 7)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨14, ?_⟩
      apply (square.reflectY_contains_iff 4 (final14Points 14)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4))
      (left := (457 / 500 : ℝ)) (width := (343 / 500 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨13, ?_⟩
      apply (square.reflectY_contains_iff 4 (final14Points 13)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨6, ?_⟩
      apply (square.reflectY_contains_iff 4 (final14Points 6)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := Stromquist.TenPoints.contains_short_pair (square := ((square.reflectX 4).swap))
      (left := (8 / 5 : ℝ)) (width := (4 / 5 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨2, ?_⟩
      apply (square.reflectX_contains_iff 4 (final14Points 2)).1
      apply ((square.reflectX 4).swap_contains_iff ((final14Points 2).reflectX 4)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨8, ?_⟩
      apply (square.reflectX_contains_iff 4 (final14Points 8)).1
      apply ((square.reflectX 4).swap_contains_iff ((final14Points 8).reflectX 4)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := Stromquist.TenPoints.contains_short_pair (square := ((square.reflectX 4).swap))
      (left := (12 / 5 : ℝ)) (width := (3 / 5 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (457 / 500 : ℝ))
      (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨8, ?_⟩
      apply (square.reflectX_contains_iff 4 (final14Points 8)).1
      apply ((square.reflectX 4).swap_contains_iff ((final14Points 8).reflectX 4)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨14, ?_⟩
      apply (square.reflectX_contains_iff 4 (final14Points 14)).1
      apply ((square.reflectX 4).swap_contains_iff ((final14Points 14).reflectX 4)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    have pair := Stromquist.TenPoints.contains_short_pair (square := ((square.reflectX 4).swap))
      (left := (1 : ℝ)) (width := (3 / 5 : ℝ))
      (firstHeight := (457 / 500 : ℝ)) (secondHeight := (1 : ℝ))
      (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨12, ?_⟩
      apply (square.reflectX_contains_iff 4 (final14Points 12)).1
      apply ((square.reflectX 4).swap_contains_iff ((final14Points 12).reflectX 4)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨2, ?_⟩
      apply (square.reflectX_contains_iff 4 (final14Points 2)).1
      apply ((square.reflectX 4).swap_contains_iff ((final14Points 2).reflectX 4)).1
      norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1⟩
    have inside := square.contains_cornerPoint (targetX := (1 : ℝ))
      (targetY := (457 / 500 : ℝ)) fits (by norm_num) (by norm_num)
      (by linarith only [bound_0])
      (by linarith only [bound_1])
    refine ⟨11, ?_⟩
    norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at inside ⊢
    exact inside
  · rcases membership with ⟨bound_0, bound_1⟩
    have inside := (square.reflectX 4).contains_cornerPoint (targetX := (457 / 500 : ℝ))
      (targetY := (1 : ℝ)) ((square.reflectX_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_1])
    refine ⟨12, ?_⟩
    apply (square.reflectX_contains_iff 4 (final14Points 12)).1
    norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at inside ⊢
    exact inside
  · rcases membership with ⟨bound_0, bound_1⟩
    have inside := (square.reflectY 4).contains_cornerPoint (targetX := (457 / 500 : ℝ))
      (targetY := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_1])
    refine ⟨13, ?_⟩
    apply (square.reflectY_contains_iff 4 (final14Points 13)).1
    norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at inside ⊢
    exact inside
  · rcases membership with ⟨bound_0, bound_1⟩
    have inside := ((square.reflectX 4).reflectY 4).contains_cornerPoint (targetX := (457 / 500 : ℝ))
      (targetY := (1 : ℝ)) (((square.reflectX 4).reflectY_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_1])
    refine ⟨14, ?_⟩
    apply (square.reflectX_contains_iff 4 (final14Points 14)).1
    apply ((square.reflectX 4).reflectY_contains_iff 4 ((final14Points 14).reflectX 4)).1
    norm_num [final14Points, finalPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at inside ⊢
    exact inside

set_option maxHeartbeats 4000000 in
theorem final14_cover : ∀ square : PlacedSquare, square.Fits 4 → (∃ index, square.Contains (final14Points index)) := by
  intro square fits
  have center_inside : square.Contains square.center := by
    refine ⟨0, 0, by norm_num, by norm_num, ?_⟩
    simp [PlacedSquare.point, Frame.place]
  have container_bounds := fits center_inside
  have container_0 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (0 : ℝ)) := by
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  have container_1 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) := by
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  have container_2 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) := by
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  have container_3 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (4 : ℝ)) := by
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  by_cases branch_0 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 50 : ℝ))
  ·
    by_cases branch_1 : 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (298 / 125 : ℝ))
    ·
      by_cases branch_2 : 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (77 / 125 : ℝ))
      ·
        apply final14_hit_boundary square fits 3
        change 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (77 / 125 : ℝ)) ∧ 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (298 / 125 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 50 : ℝ))
        refine ⟨?_ , ?_ , ?_ ⟩
        ·
          exact branch_2
        ·
          exact branch_1
        ·
          exact branch_0
      ·
        have branch_2_negative : 0 < ((3 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (-77 / 125 : ℝ)) := by linarith only [branch_2]
        by_cases branch_3 : 0 ≤ ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-33 / 50 : ℝ))
        ·
          by_cases branch_4 : 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (1211 / 625 : ℝ))
          ·
            apply final14_hit_boundary square fits 4
            change 0 ≤ ((0 : ℝ) * square.center.x + (413 / 500 : ℝ) * square.center.y + (-413 / 500 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (1211 / 625 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (-77 / 125 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (413 / 500 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (413 / 500 : ℝ)) branch_3
              have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
              have identity : (413 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-33 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (413 / 500 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_4
            ·
              exact branch_2_negative.le
          ·
            have branch_4_negative : 0 < ((3 / 5 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-1211 / 625 : ℝ)) := by linarith only [branch_4]
            apply final14_hit_boundary square fits 29
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-1211 / 625 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_3
              have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-33 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-8 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 5 : ℝ)) branch_1
              have weighted_1 := mul_pos (by norm_num : 0 < (2 / 5 : ℝ)) branch_2_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) negative
              have identity : (3 / 5 : ℝ) * ((-2 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (298 / 125 : ℝ)) + (2 / 5 : ℝ) * ((3 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (-77 / 125 : ℝ)) + (37 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-8 / 5 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_4_negative.le
        ·
          have branch_3_negative : 0 < ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (33 / 50 : ℝ)) := by linarith only [branch_3]
          by_cases branch_5 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1543 / 500 : ℝ))
          ·
            apply final14_hit_boundary square fits 19
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (413 / 500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_0
            ·
              exact branch_5
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (413 / 500 : ℝ) * square.center.y + (-413 / 500 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) branch_3_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
              have identity : (413 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (33 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (413 / 500 : ℝ) * square.center.y + (-413 / 500 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_5_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1543 / 500 : ℝ)) := by linarith only [branch_5]
            apply final14_hit_boundary square fits 31
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
            refine ⟨?_ , ?_ ⟩
            ·
              exact branch_5_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_3_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (33 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
    ·
      have branch_1_negative : 0 < ((2 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-298 / 125 : ℝ)) := by linarith only [branch_1]
      by_cases branch_6 : 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (72 / 125 : ℝ))
      ·
        by_cases branch_7 : 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ))
        ·
          apply final14_hit_boundary square fits 6
          change 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (72 / 125 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-298 / 125 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_7
          ·
            exact branch_6
          ·
            exact branch_1_negative.le
        ·
          have branch_7_negative : 0 < ((4 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_7]
          by_cases branch_8 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-8 / 5 : ℝ))
          ·
            by_cases branch_9 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (12 / 5 : ℝ))
            ·
              apply final14_hit_boundary square fits 27
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((4 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_8
              ·
                exact branch_9
              ·
                exact branch_7_negative.le
            ·
              have branch_9_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_9]
              apply final14_hit_boundary square fits 28
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-996 / 625 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_9_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) container_1
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_6
                have weighted_2 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) negative
                have identity : (2 / 5 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 : ℝ) * ((2 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (72 / 125 : ℝ)) + (37 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (-11 / 250 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (11 / 250 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((-3 / 5 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (996 / 625 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (43 / 625 : ℝ)) branch_6
                have weighted_1 := mul_pos (by norm_num : 0 < (256 / 625 : ℝ)) branch_7_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (74 / 125 : ℝ)) negative
                have identity : (43 / 625 : ℝ) * ((2 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (72 / 125 : ℝ)) + (256 / 625 : ℝ) * ((4 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (74 / 125 : ℝ) * ((-3 / 5 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (996 / 625 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_8_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (8 / 5 : ℝ)) := by linarith only [branch_8]
            apply final14_hit_boundary square fits 29
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-1211 / 625 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) container_1
              have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_1_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) negative
              have identity : (2 / 5 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 : ℝ) * ((2 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-298 / 125 : ℝ)) + (37 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (-11 / 250 : ℝ) := by
                ring
              have constant_negative := (by norm_num : 0 < (11 / 250 : ℝ))
              nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
            ·
              exact branch_8_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((-3 / 5 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (1211 / 625 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (43 / 625 : ℝ)) branch_1_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (256 / 625 : ℝ)) branch_7_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (74 / 125 : ℝ)) negative
              have identity : (43 / 625 : ℝ) * ((2 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-298 / 125 : ℝ)) + (256 / 625 : ℝ) * ((4 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (74 / 125 : ℝ) * ((-3 / 5 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (1211 / 625 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
      ·
        have branch_6_negative : 0 < ((-2 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-72 / 125 : ℝ)) := by linarith only [branch_6]
        by_cases branch_10 : 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (447 / 125 : ℝ))
        ·
          apply final14_hit_boundary square fits 12
          change 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-72 / 125 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (447 / 125 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 50 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_6_negative.le
          ·
            exact branch_10
          ·
            exact branch_0
        ·
          have branch_10_negative : 0 < ((3 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-447 / 125 : ℝ)) := by linarith only [branch_10]
          by_cases branch_11 : 0 ≤ ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (99 / 50 : ℝ))
          ·
            by_cases branch_12 : 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (996 / 625 : ℝ))
            ·
              apply final14_hit_boundary square fits 17
              change 0 ≤ ((3 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-447 / 125 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (996 / 625 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (1239 / 500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_10_negative.le
              ·
                exact branch_12
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (413 / 500 : ℝ) * square.center.y + (-1239 / 500 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (413 / 500 : ℝ)) branch_11
                have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
                have identity : (413 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (99 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (413 / 500 : ℝ) * square.center.y + (-1239 / 500 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_12_negative : 0 < ((3 / 5 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-996 / 625 : ℝ)) := by linarith only [branch_12]
              apply final14_hit_boundary square fits 28
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-996 / 625 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (12 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_6_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (2 / 5 : ℝ)) branch_10_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) negative
                have identity : (3 / 5 : ℝ) * ((-2 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-72 / 125 : ℝ)) + (2 / 5 : ℝ) * ((3 / 5 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-447 / 125 : ℝ)) + (37 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (12 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_11
                have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (99 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_12_negative.le
          ·
            have branch_11_negative : 0 < ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-99 / 50 : ℝ)) := by linarith only [branch_11]
            by_cases branch_13 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1543 / 500 : ℝ))
            ·
              apply final14_hit_boundary square fits 25
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (413 / 500 : ℝ) * square.center.y + (-1239 / 500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_0
              ·
                exact branch_13
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (1239 / 500 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) branch_11_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
                have identity : (413 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-99 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (1239 / 500 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_13_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1543 / 500 : ℝ)) := by linarith only [branch_13]
              apply final14_hit_boundary square fits 33
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                exact branch_13_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_11_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-99 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
  ·
    have branch_0_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 50 : ℝ)) := by linarith only [branch_0]
    by_cases branch_14 : 0 ≤ ((0 : ℝ) * square.center.x + (-39 / 50 : ℝ) * square.center.y + (3393 / 2500 : ℝ))
    ·
      by_cases branch_15 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-9 / 50 : ℝ) * square.center.y + (-251 / 250 : ℝ))
      ·
        by_cases branch_16 : 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (5381 / 2500 : ℝ))
        ·
          by_cases branch_17 : 0 ≤ ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-33 / 50 : ℝ))
          ·
            apply final14_hit_boundary square fits 0
            change 0 ≤ ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-33 / 50 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (5381 / 2500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-9 / 50 : ℝ) * square.center.y + (-251 / 250 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_17
            ·
              exact branch_16
            ·
              exact branch_15
          ·
            have branch_17_negative : 0 < ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (33 / 50 : ℝ)) := by linarith only [branch_17]
            by_cases branch_18 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ))
            ·
              apply final14_hit_boundary square fits 18
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (33 / 50 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_18
              ·
                exact branch_0_negative.le
              ·
                exact branch_17_negative.le
            ·
              have branch_18_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) := by linarith only [branch_18]
              apply final14_hit_boundary square fits 20
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (289 / 625 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (9 / 50 : ℝ)) container_2
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_15
                have weighted_2 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) negative
                have identity : (9 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + (1 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (-9 / 50 : ℝ) * square.center.y + (-251 / 250 : ℝ)) + (37 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (-33 / 125 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (33 / 125 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                exact branch_18_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-289 / 625 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1419 / 25000 : ℝ)) branch_15
                have weighted_1 := mul_pos (by norm_num : 0 < (10713 / 25000 : ℝ)) branch_17_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1221 / 2500 : ℝ)) negative
                have identity : (1419 / 25000 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (-9 / 50 : ℝ) * square.center.y + (-251 / 250 : ℝ)) + (10713 / 25000 : ℝ) * ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (33 / 50 : ℝ)) + (1221 / 2500 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-289 / 625 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
        ·
          have branch_16_negative : 0 < ((37 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (-5381 / 2500 : ℝ)) := by linarith only [branch_16]
          apply final14_hit_boundary square fits 5
          change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((13 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (931 / 2500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (-5381 / 2500 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_0_negative.le
          ·
            by_contra! failed
            have negative : 0 < ((-13 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (-931 / 2500 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (771 / 2500 : ℝ)) branch_14
            have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (507 / 2500 : ℝ)) branch_15
            have weighted_2 := mul_pos (by norm_num : 0 < (1443 / 2500 : ℝ)) negative
            have identity : (771 / 2500 : ℝ) * ((0 : ℝ) * square.center.x + (-39 / 50 : ℝ) * square.center.y + (3393 / 2500 : ℝ)) + (507 / 2500 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (-9 / 50 : ℝ) * square.center.y + (-251 / 250 : ℝ)) + (1443 / 2500 : ℝ) * ((-13 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (-931 / 2500 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            exact branch_16_negative.le
      ·
        have branch_15_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (9 / 50 : ℝ) * square.center.y + (251 / 250 : ℝ)) := by linarith only [branch_15]
        by_cases branch_19 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-223 / 125 : ℝ))
        ·
          apply final14_hit_boundary square fits 1
          change 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (9 / 50 : ℝ) * square.center.y + (251 / 250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-39 / 50 : ℝ) * square.center.y + (3393 / 2500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-223 / 125 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_15_negative.le
          ·
            exact branch_14
          ·
            exact branch_19
        ·
          have branch_19_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (223 / 125 : ℝ)) := by linarith only [branch_19]
          by_cases branch_20 : 0 ≤ ((413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-413 / 500 : ℝ))
          ·
            by_cases branch_21 : 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-289 / 625 : ℝ))
            ·
              apply final14_hit_boundary square fits 2
              change 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (223 / 125 : ℝ)) ∧ 0 ≤ ((413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-413 / 500 : ℝ)) ∧ 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-289 / 625 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_19_negative.le
              ·
                exact branch_20
              ·
                exact branch_21
            ·
              have branch_21_negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (289 / 625 : ℝ)) := by linarith only [branch_21]
              apply final14_hit_boundary square fits 20
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (289 / 625 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_20
                have weighted_1 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) negative
                have identity : (1 : ℝ) * ((413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-413 / 500 : ℝ)) + (413 / 500 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_15_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (9 / 50 : ℝ)) branch_19_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1443 / 2500 : ℝ)) negative
                have identity : (3 / 5 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (9 / 50 : ℝ) * square.center.y + (251 / 250 : ℝ)) + (9 / 50 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (223 / 125 : ℝ)) + (1443 / 2500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_21_negative.le
          ·
            have branch_20_negative : 0 < ((-413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (413 / 500 : ℝ)) := by linarith only [branch_20]
            by_cases branch_22 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ))
            ·
              apply final14_hit_boundary square fits 23
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (87 / 50 : ℝ)) ∧ 0 ≤ ((-413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (413 / 500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_22
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-87 / 50 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_14
                have weighted_1 := mul_pos (by norm_num : 0 < (39 / 50 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-39 / 50 : ℝ) * square.center.y + (3393 / 2500 : ℝ)) + (39 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-87 / 50 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_20_negative.le
            ·
              have branch_22_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [branch_22]
              apply final14_hit_boundary square fits 30
              change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_20_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) negative
                have identity : (1 : ℝ) * ((-413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (413 / 500 : ℝ)) + (413 / 500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_22_negative.le
    ·
      have branch_14_negative : 0 < ((0 : ℝ) * square.center.x + (39 / 50 : ℝ) * square.center.y + (-3393 / 2500 : ℝ)) := by linarith only [branch_14]
      by_cases branch_23 : 0 ≤ ((0 : ℝ) * square.center.x + (-39 / 50 : ℝ) * square.center.y + (4407 / 2500 : ℝ))
      ·
        by_cases branch_24 : 0 ≤ ((-13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1157 / 1250 : ℝ))
        ·
          by_cases branch_25 : 0 ≤ ((-13 / 25 : ℝ) * square.center.x + (-39 / 50 : ℝ) * square.center.y + (5707 / 2500 : ℝ))
          ·
            by_cases branch_26 : 0 ≤ ((413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-413 / 500 : ℝ))
            ·
              apply final14_hit_boundary square fits 7
              change 0 ≤ ((0 : ℝ) * square.center.x + (39 / 50 : ℝ) * square.center.y + (-3393 / 2500 : ℝ)) ∧ 0 ≤ ((-13 / 25 : ℝ) * square.center.x + (-39 / 50 : ℝ) * square.center.y + (5707 / 2500 : ℝ)) ∧ 0 ≤ ((13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-13 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_14_negative.le
              ·
                exact branch_25
              ·
                by_contra! failed
                have negative : 0 < ((-13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (13 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 25 : ℝ)) branch_26
                have weighted_1 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) negative
                have identity : (13 / 25 : ℝ) * ((413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-413 / 500 : ℝ)) + (413 / 500 : ℝ) * ((-13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (13 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_26_negative : 0 < ((-413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (413 / 500 : ℝ)) := by linarith only [branch_26]
              apply final14_hit_boundary square fits 21
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((-13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (13 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_14_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (39 / 50 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (39 / 50 : ℝ) * square.center.y + (-3393 / 2500 : ℝ)) + (39 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 50 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_23
                have weighted_1 := mul_pos (by norm_num : 0 < (39 / 50 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-39 / 50 : ℝ) * square.center.y + (4407 / 2500 : ℝ)) + (39 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 50 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-13 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (13 / 25 : ℝ)) branch_26_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) negative
                have identity : (13 / 25 : ℝ) * ((-413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (413 / 500 : ℝ)) + (413 / 500 : ℝ) * ((13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-13 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_25_negative : 0 < ((13 / 25 : ℝ) * square.center.x + (39 / 50 : ℝ) * square.center.y + (-5707 / 2500 : ℝ)) := by linarith only [branch_25]
            apply final14_hit_boundary square fits 11
            change 0 ≤ ((-13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1157 / 1250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-39 / 50 : ℝ) * square.center.y + (4407 / 2500 : ℝ)) ∧ 0 ≤ ((13 / 25 : ℝ) * square.center.x + (39 / 50 : ℝ) * square.center.y + (-5707 / 2500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_24
            ·
              exact branch_23
            ·
              exact branch_25_negative.le
        ·
          have branch_24_negative : 0 < ((13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1157 / 1250 : ℝ)) := by linarith only [branch_24]
          by_cases branch_27 : 0 ≤ ((13 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (931 / 2500 : ℝ))
          ·
            apply final14_hit_boundary square fits 5
            change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((13 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (931 / 2500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (-5381 / 2500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_0_negative.le
            ·
              exact branch_27
            ·
              by_contra! failed
              have negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (5381 / 2500 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (156 / 625 : ℝ)) branch_14_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (1443 / 2500 : ℝ)) branch_24_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (507 / 1250 : ℝ)) negative
              have identity : (156 / 625 : ℝ) * ((0 : ℝ) * square.center.x + (39 / 50 : ℝ) * square.center.y + (-3393 / 2500 : ℝ)) + (1443 / 2500 : ℝ) * ((13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1157 / 1250 : ℝ)) + (507 / 1250 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (5381 / 2500 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_27_negative : 0 < ((-13 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (-931 / 2500 : ℝ)) := by linarith only [branch_27]
            by_cases branch_28 : 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (3869 / 2500 : ℝ))
            ·
              apply final14_hit_boundary square fits 10
              change 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (-931 / 2500 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (3869 / 2500 : ℝ)) ∧ 0 ≤ ((13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1157 / 1250 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_27_negative.le
              ·
                exact branch_28
              ·
                exact branch_24_negative.le
            ·
              have branch_28_negative : 0 < ((13 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (-3869 / 2500 : ℝ)) := by linarith only [branch_28]
              apply final14_hit_boundary square fits 13
              change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (-581 / 2500 : ℝ)) ∧ 0 ≤ ((13 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (-3869 / 2500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_0_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (581 / 2500 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (156 / 625 : ℝ)) branch_23
                have weighted_1 := mul_pos (by norm_num : 0 < (1443 / 2500 : ℝ)) branch_24_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (507 / 1250 : ℝ)) negative
                have identity : (156 / 625 : ℝ) * ((0 : ℝ) * square.center.x + (-39 / 50 : ℝ) * square.center.y + (4407 / 2500 : ℝ)) + (1443 / 2500 : ℝ) * ((13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1157 / 1250 : ℝ)) + (507 / 1250 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (581 / 2500 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_28_negative.le
      ·
        have branch_23_negative : 0 < ((0 : ℝ) * square.center.x + (39 / 50 : ℝ) * square.center.y + (-4407 / 2500 : ℝ)) := by linarith only [branch_23]
        by_cases branch_29 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (9 / 50 : ℝ) * square.center.y + (-431 / 250 : ℝ))
        ·
          by_cases branch_30 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (-581 / 2500 : ℝ))
          ·
            apply final14_hit_boundary square fits 13
            change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (-581 / 2500 : ℝ)) ∧ 0 ≤ ((13 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (-3869 / 2500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_0_negative.le
            ·
              exact branch_30
            ·
              by_contra! failed
              have negative : 0 < ((-13 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (3869 / 2500 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (771 / 2500 : ℝ)) branch_23_negative
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (507 / 2500 : ℝ)) branch_29
              have weighted_2 := mul_pos (by norm_num : 0 < (1443 / 2500 : ℝ)) negative
              have identity : (771 / 2500 : ℝ) * ((0 : ℝ) * square.center.x + (39 / 50 : ℝ) * square.center.y + (-4407 / 2500 : ℝ)) + (507 / 2500 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (9 / 50 : ℝ) * square.center.y + (-431 / 250 : ℝ)) + (1443 / 2500 : ℝ) * ((-13 / 50 : ℝ) * square.center.x + (-12 / 25 : ℝ) * square.center.y + (3869 / 2500 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_30_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (581 / 2500 : ℝ)) := by linarith only [branch_30]
            by_cases branch_31 : 0 ≤ ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (99 / 50 : ℝ))
            ·
              apply final14_hit_boundary square fits 14
              change 0 ≤ ((37 / 50 : ℝ) * square.center.x + (9 / 50 : ℝ) * square.center.y + (-431 / 250 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (12 / 25 : ℝ) * square.center.y + (581 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (99 / 50 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_29
              ·
                exact branch_30_negative.le
              ·
                exact branch_31
            ·
              have branch_31_negative : 0 < ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-99 / 50 : ℝ)) := by linarith only [branch_31]
              by_cases branch_32 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ))
              ·
                apply final14_hit_boundary square fits 24
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-99 / 50 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_32
                ·
                  exact branch_0_negative.le
                ·
                  exact branch_31_negative.le
              ·
                have branch_32_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) := by linarith only [branch_32]
                apply final14_hit_boundary square fits 26
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (9 / 50 : ℝ)) container_3
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_29
                  have weighted_2 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) negative
                  have identity : (9 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (4 : ℝ)) + (1 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (9 / 50 : ℝ) * square.center.y + (-431 / 250 : ℝ)) + (37 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) = (-8191 / 25000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (8191 / 25000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_32_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) branch_31_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
                  have identity : (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-99 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_29_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (-9 / 50 : ℝ) * square.center.y + (431 / 250 : ℝ)) := by linarith only [branch_29]
          by_cases branch_33 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (77 / 125 : ℝ))
          ·
            apply final14_hit_boundary square fits 15
            change 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (77 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (39 / 50 : ℝ) * square.center.y + (-4407 / 2500 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-9 / 50 : ℝ) * square.center.y + (431 / 250 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_33
            ·
              exact branch_23_negative.le
            ·
              exact branch_29_negative.le
          ·
            have branch_33_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-77 / 125 : ℝ)) := by linarith only [branch_33]
            by_cases branch_34 : 0 ≤ ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (99 / 50 : ℝ))
            ·
              by_cases branch_35 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-23359 / 25000 : ℝ))
              ·
                apply final14_hit_boundary square fits 16
                change 0 ≤ ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-23359 / 25000 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-77 / 125 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (343 / 500 : ℝ)) branch_34
                  have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
                  have identity : (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (99 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  exact branch_35
                ·
                  exact branch_33_negative.le
              ·
                have branch_35_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (23359 / 25000 : ℝ)) := by linarith only [branch_35]
                apply final14_hit_boundary square fits 22
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (23359 / 25000 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 50 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_23_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (39 / 50 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (39 / 50 : ℝ) * square.center.y + (-4407 / 2500 : ℝ)) + (39 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 50 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_34
                  have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (99 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  exact branch_35_negative.le
            ·
              have branch_34_negative : 0 < ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-99 / 50 : ℝ)) := by linarith only [branch_34]
              by_cases branch_36 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ))
              ·
                apply final14_hit_boundary square fits 26
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_36
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_29_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (9 / 50 : ℝ)) branch_33_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (1443 / 2500 : ℝ)) negative
                  have identity : (3 / 5 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (-9 / 50 : ℝ) * square.center.y + (431 / 250 : ℝ)) + (9 / 50 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-77 / 125 : ℝ)) + (1443 / 2500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) branch_34_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
                  have identity : (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-99 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_36_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [branch_36]
                apply final14_hit_boundary square fits 32
                change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
                refine ⟨?_ , ?_ ⟩
                ·
                  exact branch_36_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_34_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (33 / 50 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (-99 / 50 : ℝ)) + (33 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]

end SquarePackingArchive.BentzThirteen.Nonadjacent
