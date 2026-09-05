import SquarePackingArchive.BentzThirteenNonadjacentData

namespace SquarePackingArchive.BentzThirteen.Nonadjacent

noncomputable def initial13Points : Fin 14 → Point := initialPoints (choicePattern 13)

def initial13Region (index : Fin 28) (center : Point) : Prop :=
  match index.val with
  | 0 => 0 ≤ ((37 / 50 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-223 / 125 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (2 / 5 : ℝ) * center.y + (98 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (87 / 50 : ℝ))
  | 1 => 0 ≤ ((37 / 50 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (-14759 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (343 / 500 : ℝ) * center.y + (-343 / 500 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (223 / 125 : ℝ))
  | 2 => 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (87 / 50 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (2 / 5 : ℝ) * center.y + (-272 / 125 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (147 / 125 : ℝ))
  | 3 => 0 ≤ ((37 / 50 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (-147 / 125 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-504 / 625 : ℝ)) ∧ 0 ≤ ((-413 / 500 : ℝ) * center.x + (0 : ℝ) * center.y + (1239 / 500 : ℝ))
  | 4 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (-2 / 5 : ℝ) * center.y + (298 / 125 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (77 / 125 : ℝ))
  | 5 => 0 ≤ ((-37 / 50 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-77 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-343 / 500 : ℝ) * center.y + (1029 / 500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (-23359 / 25000 : ℝ))
  | 6 => 0 ≤ ((-37 / 50 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (447 / 125 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (-2 / 5 : ℝ) * center.y + (-72 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-113 / 50 : ℝ))
  | 7 => 0 ≤ ((-37 / 50 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (50641 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-343 / 500 : ℝ) * center.y + (1029 / 500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (3 / 5 : ℝ) * center.y + (-447 / 125 : ℝ))
  | 8 => 0 ≤ ((37 / 50 : ℝ) * center.x + (-2 / 5 : ℝ) * center.y + (-98 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-4 / 5 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (-2 / 5 : ℝ) * center.y + (272 / 125 : ℝ))
  | 9 => 0 ≤ ((-37 / 50 : ℝ) * center.x + (2 / 5 : ℝ) * center.y + (72 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (2 / 5 : ℝ) * center.y + (-298 / 125 : ℝ))
  | 10 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-4 / 5 : ℝ) * center.y + (4 / 5 : ℝ))
  | 11 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-12 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((-43 / 500 : ℝ) * center.x + (-3 / 5 : ℝ) * center.y + (504 / 625 : ℝ))
  | 12 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-343 / 500 : ℝ) * center.y + (343 / 500 : ℝ))
  | 13 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((-13 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (13 / 25 : ℝ))
  | 14 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (23359 / 25000 : ℝ))
  | 15 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (87 / 50 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * center.x + (43 / 500 : ℝ) * center.y + (14759 / 25000 : ℝ))
  | 16 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (4 / 5 : ℝ) * center.y + (-12 / 5 : ℝ))
  | 17 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-12 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (343 / 500 : ℝ) * center.y + (-1029 / 500 : ℝ))
  | 18 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (343 / 500 : ℝ) * center.y + (-1029 / 500 : ℝ))
  | 19 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((13 / 25 : ℝ) * center.x + (0 : ℝ) * center.y + (-39 / 25 : ℝ))
  | 20 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * center.x + (-43 / 500 : ℝ) * center.y + (-50641 / 25000 : ℝ))
  | 21 => 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (87 / 50 : ℝ)) ∧ 0 ≤ ((413 / 500 : ℝ) * center.x + (0 : ℝ) * center.y + (-1239 / 500 : ℝ))
  | 22 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (1 : ℝ))
  | 23 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (457 / 500 : ℝ))
  | 24 => 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))
  | 25 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-3 : ℝ))
  | 26 => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (113 / 50 : ℝ))
  | _ => 0 ≤ ((1 : ℝ) * center.x + (0 : ℝ) * center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * center.x + (0 : ℝ) * center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (1 : ℝ) * center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * center.x + (-1 : ℝ) * center.y + (113 / 50 : ℝ))

set_option maxHeartbeats 4000000 in
lemma initial13_hit_boundary (square : PlacedSquare) (fits : square.Fits 4)
    (index : Fin 28) (membership : initial13Region index square.center) :
    (∃ index, square.Contains (initial13Points index)) ∨ Hole square.center := by
  fin_cases index
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (initial13Points 0) (initial13Points 6) (initial13Points 4)
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨0, first_inside⟩
    · exact ⟨6, second_inside⟩
    · exact ⟨4, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (initial13Points 0) (initial13Points 10) (initial13Points 6)
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨0, first_inside⟩
    · exact ⟨10, second_inside⟩
    · exact ⟨6, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (initial13Points 1) (initial13Points 4) (initial13Points 7)
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨1, first_inside⟩
    · exact ⟨4, second_inside⟩
    · exact ⟨7, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (initial13Points 1) (initial13Points 7) (initial13Points 11)
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨1, first_inside⟩
    · exact ⟨7, second_inside⟩
    · exact ⟨11, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (initial13Points 2) (initial13Points 5) (initial13Points 8)
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨2, first_inside⟩
    · exact ⟨5, second_inside⟩
    · exact ⟨8, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (initial13Points 2) (initial13Points 8) (initial13Points 12)
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨2, first_inside⟩
    · exact ⟨8, second_inside⟩
    · exact ⟨12, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (initial13Points 3) (initial13Points 9) (initial13Points 5)
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨3, first_inside⟩
    · exact ⟨9, second_inside⟩
    · exact ⟨5, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (initial13Points 3) (initial13Points 13) (initial13Points 9)
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨3, first_inside⟩
    · exact ⟨13, second_inside⟩
    · exact ⟨9, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (initial13Points 4) (initial13Points 6) (initial13Points 7)
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨4, first_inside⟩
    · exact ⟨6, second_inside⟩
    · exact ⟨7, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    rcases square.contains_triangleVertex_of_cross_nonnegative
      (initial13Points 5) (initial13Points 9) (initial13Points 8)
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_0])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_1])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap, Point.orientedArea]; linarith only [bound_2])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap])
      (by norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap]) with first_inside | second_inside | third_inside
    · exact ⟨5, first_inside⟩
    · exact ⟨9, second_inside⟩
    · exact ⟨8, third_inside⟩
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := square)
      (left := (8 / 5 : ℝ)) (width := (4 / 5 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      fits (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [bound_0])
      (by linarith only [bound_1])
      (by linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨6, ?_⟩
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨7, ?_⟩
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := square)
      (left := (12 / 5 : ℝ)) (width := (3 / 5 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (457 / 500 : ℝ))
      fits (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [bound_0])
      (by linarith only [bound_1])
      (by linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨7, ?_⟩
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨11, ?_⟩
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := square)
      (left := (457 / 500 : ℝ)) (width := (343 / 500 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      fits (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [bound_0])
      (by linarith only [bound_1])
      (by linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨10, ?_⟩
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨6, ?_⟩
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.swap))
      (left := (87 / 50 : ℝ)) (width := (13 / 25 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      ((square.swap_fits_iff 4).2 fits) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨0, ?_⟩
      apply (square.swap_contains_iff (initial13Points 0)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨2, ?_⟩
      apply (square.swap_contains_iff (initial13Points 2)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.swap))
      (left := (113 / 50 : ℝ)) (width := (37 / 50 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (457 / 500 : ℝ))
      ((square.swap_fits_iff 4).2 fits) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨2, ?_⟩
      apply (square.swap_contains_iff (initial13Points 2)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨12, ?_⟩
      apply (square.swap_contains_iff (initial13Points 12)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.swap))
      (left := (1 : ℝ)) (width := (37 / 50 : ℝ))
      (firstHeight := (457 / 500 : ℝ)) (secondHeight := (1 : ℝ))
      ((square.swap_fits_iff 4).2 fits) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨10, ?_⟩
      apply (square.swap_contains_iff (initial13Points 10)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨0, ?_⟩
      apply (square.swap_contains_iff (initial13Points 0)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4))
      (left := (8 / 5 : ℝ)) (width := (4 / 5 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨8, ?_⟩
      apply (square.reflectY_contains_iff 4 (initial13Points 8)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨9, ?_⟩
      apply (square.reflectY_contains_iff 4 (initial13Points 9)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4))
      (left := (12 / 5 : ℝ)) (width := (343 / 500 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨9, ?_⟩
      apply (square.reflectY_contains_iff 4 (initial13Points 9)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨13, ?_⟩
      apply (square.reflectY_contains_iff 4 (initial13Points 13)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := (square.reflectY 4))
      (left := (457 / 500 : ℝ)) (width := (343 / 500 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨12, ?_⟩
      apply (square.reflectY_contains_iff 4 (initial13Points 12)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨8, ?_⟩
      apply (square.reflectY_contains_iff 4 (initial13Points 8)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := ((square.reflectX 4).swap))
      (left := (87 / 50 : ℝ)) (width := (13 / 25 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (1 : ℝ))
      (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨1, ?_⟩
      apply (square.reflectX_contains_iff 4 (initial13Points 1)).1
      apply ((square.reflectX 4).swap_contains_iff ((initial13Points 1).reflectX 4)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨3, ?_⟩
      apply (square.reflectX_contains_iff 4 (initial13Points 3)).1
      apply ((square.reflectX 4).swap_contains_iff ((initial13Points 3).reflectX 4)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := Stromquist.TenPoints.contains_short_pair (square := ((square.reflectX 4).swap))
      (left := (113 / 50 : ℝ)) (width := (37 / 50 : ℝ))
      (firstHeight := (1 : ℝ)) (secondHeight := (457 / 500 : ℝ))
      (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨3, ?_⟩
      apply (square.reflectX_contains_iff 4 (initial13Points 3)).1
      apply ((square.reflectX 4).swap_contains_iff ((initial13Points 3).reflectX 4)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨13, ?_⟩
      apply (square.reflectX_contains_iff 4 (initial13Points 13)).1
      apply ((square.reflectX 4).swap_contains_iff ((initial13Points 13).reflectX 4)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1, bound_2⟩
    apply Or.inl
    have pair := ((square.reflectX 4).swap).contains_bottomSharpPair (left := (457 / 500 : ℝ))
      (gap := (413 / 500 : ℝ)) (targetHeight := 1) (((square.reflectX 4).swap_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num)
      (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_1])
      (by dsimp [PlacedSquare.swap, PlacedSquare.reflectX, PlacedSquare.reflectY, Point.swap, Point.reflectX, Point.reflectY]; linarith only [bound_2])
    rcases pair with first_inside | second_inside
    ·
      refine ⟨11, ?_⟩
      apply (square.reflectX_contains_iff 4 (initial13Points 11)).1
      apply ((square.reflectX 4).swap_contains_iff ((initial13Points 11).reflectX 4)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at first_inside ⊢
      exact first_inside
    ·
      refine ⟨1, ?_⟩
      apply (square.reflectX_contains_iff 4 (initial13Points 1)).1
      apply ((square.reflectX 4).swap_contains_iff ((initial13Points 1).reflectX 4)).1
      norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at second_inside ⊢
      exact second_inside
  · rcases membership with ⟨bound_0, bound_1⟩
    apply Or.inl
    have inside := square.contains_cornerPoint (targetX := (457 / 500 : ℝ))
      (targetY := (1 : ℝ)) fits (by norm_num) (by norm_num)
      (by linarith only [bound_0])
      (by linarith only [bound_1])
    refine ⟨10, ?_⟩
    norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at inside ⊢
    exact inside
  · rcases membership with ⟨bound_0, bound_1⟩
    apply Or.inl
    have inside := (square.reflectX 4).contains_cornerPoint (targetX := (1 : ℝ))
      (targetY := (457 / 500 : ℝ)) ((square.reflectX_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_1])
    refine ⟨11, ?_⟩
    apply (square.reflectX_contains_iff 4 (initial13Points 11)).1
    norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at inside ⊢
    exact inside
  · rcases membership with ⟨bound_0, bound_1⟩
    apply Or.inl
    have inside := (square.reflectY 4).contains_cornerPoint (targetX := (457 / 500 : ℝ))
      (targetY := (1 : ℝ)) ((square.reflectY_fits_iff 4).2 fits) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_1])
    refine ⟨12, ?_⟩
    apply (square.reflectY_contains_iff 4 (initial13Points 12)).1
    norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at inside ⊢
    exact inside
  · rcases membership with ⟨bound_0, bound_1⟩
    apply Or.inl
    have inside := ((square.reflectX 4).reflectY 4).contains_cornerPoint (targetX := (457 / 500 : ℝ))
      (targetY := (1 : ℝ)) (((square.reflectX 4).reflectY_fits_iff 4).2 ((square.reflectX_fits_iff 4).2 fits)) (by norm_num) (by norm_num)
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_0])
      (by dsimp [PlacedSquare.reflectX, PlacedSquare.reflectY, Point.reflectX, Point.reflectY]; linarith only [bound_1])
    refine ⟨13, ?_⟩
    apply (square.reflectX_contains_iff 4 (initial13Points 13)).1
    apply ((square.reflectX 4).reflectY_contains_iff 4 ((initial13Points 13).reflectX 4)).1
    norm_num [initial13Points, initialPoints, cornerAlternative, choicePattern, Point.reflectX, Point.reflectY, Point.swap] at inside ⊢
    exact inside
  · rcases membership with ⟨bound_0, bound_1, bound_2, bound_3⟩
    apply Or.inr
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [bound_0, bound_1, bound_2, bound_3]
  · rcases membership with ⟨bound_0, bound_1, bound_2, bound_3⟩
    apply Or.inr
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [bound_0, bound_1, bound_2, bound_3]

set_option maxHeartbeats 4000000 in
theorem initial13_cover : ∀ square : PlacedSquare, square.Fits 4 → (∃ index, square.Contains (initial13Points index)) ∨ Hole square.center := by
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
  by_cases branch_0 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (87 / 50 : ℝ))
  ·
    by_cases branch_1 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ))
    ·
      by_cases branch_2 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-223 / 125 : ℝ))
      ·
        by_cases branch_3 : 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (98 / 125 : ℝ))
        ·
          apply initial13_hit_boundary square fits 0
          change 0 ≤ ((37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-223 / 125 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (98 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (87 / 50 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_2
          ·
            exact branch_3
          ·
            exact branch_0
        ·
          have branch_3_negative : 0 < ((37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-98 / 125 : ℝ)) := by linarith only [branch_3]
          by_cases branch_4 : 0 ≤ ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-343 / 500 : ℝ))
          ·
            apply initial13_hit_boundary square fits 8
            change 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-98 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (272 / 125 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_3_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (4 / 5 : ℝ)) branch_4
              have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
              have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-343 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              by_contra! failed
              have negative : 0 < ((37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-272 / 125 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) branch_0
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (37 / 50 : ℝ)) branch_1
              have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
              have identity : (2 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (87 / 50 : ℝ)) + (37 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) + (1 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-272 / 125 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_4_negative : 0 < ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (343 / 500 : ℝ)) := by linarith only [branch_4]
            apply initial13_hit_boundary square fits 10
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) branch_2
              have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_3_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) negative
              have identity : (2 / 5 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-223 / 125 : ℝ)) + (3 / 5 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-98 / 125 : ℝ)) + (37 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              by_contra! failed
              have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_1
              have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
              have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) = (-2 / 5 : ℝ) := by
                ring
              have constant_negative := (by norm_num : 0 < (2 / 5 : ℝ))
              nlinarith only [weighted_0, weighted_1, constant_negative, identity]
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) branch_4_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
              have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (343 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_2_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (223 / 125 : ℝ)) := by linarith only [branch_2]
        by_cases branch_5 : 0 ≤ ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-343 / 500 : ℝ))
        ·
          by_cases branch_6 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-14759 / 25000 : ℝ))
          ·
            apply initial13_hit_boundary square fits 1
            change 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-14759 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-343 / 500 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (223 / 125 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_6
            ·
              exact branch_5
            ·
              exact branch_2_negative.le
          ·
            have branch_6_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (14759 / 25000 : ℝ)) := by linarith only [branch_6]
            apply initial13_hit_boundary square fits 15
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (87 / 50 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (14759 / 25000 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_5
              have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-343 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_0
            ·
              exact branch_6_negative.le
        ·
          have branch_5_negative : 0 < ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (343 / 500 : ℝ)) := by linarith only [branch_5]
          by_cases branch_7 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ))
          ·
            by_cases branch_8 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ))
            ·
              apply initial13_hit_boundary square fits 10
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_8
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_1
                have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) = (-2 / 5 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (2 / 5 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) branch_5_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
                have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (343 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_8_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) := by linarith only [branch_8]
              apply initial13_hit_boundary square fits 12
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (343 / 500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_7
              ·
                exact branch_8_negative.le
              ·
                exact branch_5_negative.le
          ·
            have branch_7_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [branch_7]
            apply initial13_hit_boundary square fits 22
            change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
            refine ⟨?_ , ?_ ⟩
            ·
              exact branch_7_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_5_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (343 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
    ·
      have branch_1_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) := by linarith only [branch_1]
      by_cases branch_9 : 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (147 / 125 : ℝ))
      ·
        by_cases branch_10 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-272 / 125 : ℝ))
        ·
          apply initial13_hit_boundary square fits 2
          change 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (87 / 50 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-272 / 125 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (147 / 125 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_0
          ·
            exact branch_10
          ·
            exact branch_9
        ·
          have branch_10_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (272 / 125 : ℝ)) := by linarith only [branch_10]
          by_cases branch_11 : 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ))
          ·
            apply initial13_hit_boundary square fits 8
            change 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-98 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (272 / 125 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (98 / 125 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) branch_0
              have weighted_1 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) branch_1_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
              have identity : (2 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (87 / 50 : ℝ)) + (37 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) + (1 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (98 / 125 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_11
            ·
              exact branch_10_negative.le
          ·
            have branch_11_negative : 0 < ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ)) := by linarith only [branch_11]
            apply initial13_hit_boundary square fits 10
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_1_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
              have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) = (-2 / 5 : ℝ) := by
                ring
              have constant_negative := (by norm_num : 0 < (2 / 5 : ℝ))
              nlinarith only [weighted_0, weighted_1, constant_negative, identity]
            ·
              by_contra! failed
              have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) branch_9
              have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_10_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) negative
              have identity : (2 / 5 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (147 / 125 : ℝ)) + (3 / 5 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (272 / 125 : ℝ)) + (37 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_11_negative.le
      ·
        have branch_9_negative : 0 < ((37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-147 / 125 : ℝ)) := by linarith only [branch_9]
        by_cases branch_12 : 0 ≤ ((-413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1239 / 500 : ℝ))
        ·
          by_cases branch_13 : 0 ≤ ((43 / 500 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-504 / 625 : ℝ))
          ·
            apply initial13_hit_boundary square fits 3
            change 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-147 / 125 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-504 / 625 : ℝ)) ∧ 0 ≤ ((-413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1239 / 500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_9_negative.le
            ·
              exact branch_13
            ·
              exact branch_12
          ·
            have branch_13_negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (504 / 625 : ℝ)) := by linarith only [branch_13]
            by_cases branch_14 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ))
            ·
              apply initial13_hit_boundary square fits 10
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_1_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) = (-2 / 5 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (2 / 5 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                exact branch_14
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (43 / 625 : ℝ)) branch_9_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (74 / 125 : ℝ)) branch_13_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1239 / 2500 : ℝ)) negative
                have identity : (43 / 625 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-147 / 125 : ℝ)) + (74 / 125 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (504 / 625 : ℝ)) + (1239 / 2500 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_14_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_14]
              apply initial13_hit_boundary square fits 11
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (504 / 625 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_14_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_12
                have weighted_1 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) negative
                have identity : (1 : ℝ) * ((-413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1239 / 500 : ℝ)) + (413 / 500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_13_negative.le
        ·
          have branch_12_negative : 0 < ((413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1239 / 500 : ℝ)) := by linarith only [branch_12]
          by_cases branch_15 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ))
          ·
            apply initial13_hit_boundary square fits 21
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (87 / 50 : ℝ)) ∧ 0 ≤ ((413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1239 / 500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_15
            ·
              exact branch_0
            ·
              exact branch_12_negative.le
          ·
            have branch_15_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [branch_15]
            apply initial13_hit_boundary square fits 23
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ))
            refine ⟨?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_12_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) negative
              have identity : (1 : ℝ) * ((413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1239 / 500 : ℝ)) + (413 / 500 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_15_negative.le
  ·
    have branch_0_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-87 / 50 : ℝ)) := by linarith only [branch_0]
    by_cases branch_16 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 50 : ℝ))
    ·
      by_cases branch_17 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ))
      ·
        by_cases branch_18 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (77 / 125 : ℝ))
        ·
          by_cases branch_19 : 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (298 / 125 : ℝ))
          ·
            apply initial13_hit_boundary square fits 4
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (298 / 125 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (77 / 125 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_16
            ·
              exact branch_19
            ·
              exact branch_18
          ·
            have branch_19_negative : 0 < ((37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-298 / 125 : ℝ)) := by linarith only [branch_19]
            by_cases branch_20 : 0 ≤ ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ))
            ·
              apply initial13_hit_boundary square fits 9
              change 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (72 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-298 / 125 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-72 / 125 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) branch_16
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (37 / 50 : ℝ)) branch_17
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (2 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 50 : ℝ)) + (37 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) + (1 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-72 / 125 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (4 / 5 : ℝ)) branch_20
                have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
                have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_19_negative.le
            ·
              have branch_20_negative : 0 < ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) := by linarith only [branch_20]
              apply initial13_hit_boundary square fits 16
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) branch_18
                have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_19_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) negative
                have identity : (2 / 5 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (77 / 125 : ℝ)) + (3 / 5 : ℝ) * ((37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-298 / 125 : ℝ)) + (37 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_17
                have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) = (-2 / 5 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (2 / 5 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) branch_20_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
                have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_18_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-77 / 125 : ℝ)) := by linarith only [branch_18]
          by_cases branch_21 : 0 ≤ ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ))
          ·
            by_cases branch_22 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-23359 / 25000 : ℝ))
            ·
              apply initial13_hit_boundary square fits 5
              change 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-77 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-23359 / 25000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_18_negative.le
              ·
                exact branch_21
              ·
                exact branch_22
            ·
              have branch_22_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (23359 / 25000 : ℝ)) := by linarith only [branch_22]
              apply initial13_hit_boundary square fits 14
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (23359 / 25000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_16
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_21
                have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_22_negative.le
          ·
            have branch_21_negative : 0 < ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) := by linarith only [branch_21]
            by_cases branch_23 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ))
            ·
              by_cases branch_24 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ))
              ·
                apply initial13_hit_boundary square fits 16
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_24
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_17
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) = (-2 / 5 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (2 / 5 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) branch_21_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
                  have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_24_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) := by linarith only [branch_24]
                apply initial13_hit_boundary square fits 18
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_23
                ·
                  exact branch_24_negative.le
                ·
                  exact branch_21_negative.le
            ·
              have branch_23_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [branch_23]
              apply initial13_hit_boundary square fits 24
              change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                exact branch_23_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_21_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_17_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) := by linarith only [branch_17]
        by_cases branch_25 : 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (447 / 125 : ℝ))
        ·
          by_cases branch_26 : 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-72 / 125 : ℝ))
          ·
            apply initial13_hit_boundary square fits 6
            change 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (447 / 125 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-72 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 50 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_25
            ·
              exact branch_26
            ·
              exact branch_16
          ·
            have branch_26_negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (72 / 125 : ℝ)) := by linarith only [branch_26]
            by_cases branch_27 : 0 ≤ ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ))
            ·
              apply initial13_hit_boundary square fits 9
              change 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (72 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-298 / 125 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_26_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (4 / 5 : ℝ)) branch_27
                have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
                have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((-37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (298 / 125 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) branch_16
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) branch_17_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (2 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 50 : ℝ)) + (37 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) + (1 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (298 / 125 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_27_negative : 0 < ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) := by linarith only [branch_27]
              apply initial13_hit_boundary square fits 16
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_17_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) = (-2 / 5 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (2 / 5 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) branch_25
                have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_26_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (37 / 50 : ℝ)) negative
                have identity : (2 / 5 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (447 / 125 : ℝ)) + (3 / 5 : ℝ) * ((-37 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (72 / 125 : ℝ)) + (37 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) branch_27_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
                have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_25_negative : 0 < ((37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-447 / 125 : ℝ)) := by linarith only [branch_25]
          by_cases branch_28 : 0 ≤ ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ))
          ·
            by_cases branch_29 : 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (50641 / 25000 : ℝ))
            ·
              apply initial13_hit_boundary square fits 7
              change 0 ≤ ((-37 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (50641 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-447 / 125 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_29
              ·
                exact branch_28
              ·
                exact branch_25_negative.le
            ·
              have branch_29_negative : 0 < ((37 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-50641 / 25000 : ℝ)) := by linarith only [branch_29]
              apply initial13_hit_boundary square fits 20
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((37 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-50641 / 25000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_16
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_28
                have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-343 / 500 : ℝ) * square.center.y + (1029 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_29_negative.le
          ·
            have branch_28_negative : 0 < ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) := by linarith only [branch_28]
            by_cases branch_30 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1543 / 500 : ℝ))
            ·
              by_cases branch_31 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ))
              ·
                apply initial13_hit_boundary square fits 16
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_17_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 5 : ℝ)) = (-2 / 5 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (2 / 5 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_31
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) branch_28_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
                  have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_31_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_31]
                apply initial13_hit_boundary square fits 17
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-12 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_31_negative.le
                ·
                  exact branch_30
                ·
                  exact branch_28_negative.le
            ·
              have branch_30_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1543 / 500 : ℝ)) := by linarith only [branch_30]
              apply initial13_hit_boundary square fits 25
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1543 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                exact branch_30_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_28_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (343 / 500 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (343 / 500 : ℝ) * square.center.y + (-1029 / 500 : ℝ)) + (343 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
    ·
      have branch_16_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 50 : ℝ)) := by linarith only [branch_16]
      by_cases branch_32 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ))
      ·
        by_cases branch_33 : 0 ≤ ((-13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (13 / 25 : ℝ))
        ·
          apply initial13_hit_boundary square fits 13
          change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((-13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (13 / 25 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_0_negative.le
          ·
            exact branch_16_negative.le
          ·
            exact branch_33
        ·
          have branch_33_negative : 0 < ((13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-13 / 25 : ℝ)) := by linarith only [branch_33]
          apply initial13_hit_boundary square fits 26
          change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 50 : ℝ))
          refine ⟨?_ , ?_ , ?_ , ?_ ⟩
          ·
            by_contra! failed
            have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_33_negative
            have weighted_1 := mul_pos (by norm_num : 0 < (13 / 25 : ℝ)) negative
            have identity : (1 : ℝ) * ((13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-13 / 25 : ℝ)) + (13 / 25 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          ·
            exact branch_32
          ·
            exact branch_0_negative.le
          ·
            exact branch_16_negative.le
      ·
        have branch_32_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) := by linarith only [branch_32]
        by_cases branch_34 : 0 ≤ ((-413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1239 / 500 : ℝ))
        ·
          apply initial13_hit_boundary square fits 27
          change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 50 : ℝ))
          refine ⟨?_ , ?_ , ?_ , ?_ ⟩
          ·
            exact branch_32_negative.le
          ·
            by_contra! failed
            have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_34
            have weighted_1 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) negative
            have identity : (1 : ℝ) * ((-413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1239 / 500 : ℝ)) + (413 / 500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          ·
            exact branch_0_negative.le
          ·
            exact branch_16_negative.le
        ·
          have branch_34_negative : 0 < ((413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1239 / 500 : ℝ)) := by linarith only [branch_34]
          apply initial13_hit_boundary square fits 19
          change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 50 : ℝ)) ∧ 0 ≤ ((13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 25 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_0_negative.le
          ·
            exact branch_16_negative.le
          ·
            by_contra! failed
            have negative : 0 < ((-13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 25 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_pos (by norm_num : 0 < (13 / 25 : ℝ)) branch_34_negative
            have weighted_1 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) negative
            have identity : (13 / 25 : ℝ) * ((413 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1239 / 500 : ℝ)) + (413 / 500 : ℝ) * ((-13 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 25 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]

end SquarePackingArchive.BentzThirteen.Nonadjacent
