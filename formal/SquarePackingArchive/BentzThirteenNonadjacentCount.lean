import SquarePackingArchive.BentzThirteenNonadjacentData
import SquarePackingArchive.BentzThirteenSymmetry
import SquarePackingArchive.BentzRectangleMidpoints

namespace SquarePackingArchive.BentzThirteen.Nonadjacent

def anchorIndex (anchor : Fin 8) : Fin 16 := ⟨anchor.val, by omega⟩

def selectedChoices (first second : Fin 8) (corner : Fin 4) : Bool :=
  if corner.val = first.val / 2 then decide (first.val % 2 = 1)
  else decide (second.val % 2 = 1)

def Selected (choices : Fin 4 → Bool) (anchor : Fin 8) : Prop :=
  cornerAlternative choices ⟨anchor.val / 2, by omega⟩ =
    Records.Square13.initialPoints (anchorIndex anchor)

theorem selectedChoices_first (first second : Fin 8) :
    Selected (selectedChoices first second) first := by
  fin_cases first <;> norm_num [Selected, selectedChoices, cornerAlternative, anchorIndex,
    Records.Square13.initialPoints, Point.reflectX, Point.reflectY]

theorem selectedChoices_second (first second : Fin 8)
    (different : first.val / 2 ≠ second.val / 2) :
    Selected (selectedChoices first second) second := by
  fin_cases first <;> fin_cases second <;> norm_num at different <;>
    norm_num [Selected, selectedChoices, cornerAlternative, anchorIndex,
      Records.Square13.initialPoints, Point.reflectX, Point.reflectY]

def initialReplacement : Fin 8 → Fin 14
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 7
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 8
  | ⟨5, _⟩ => 2
  | ⟨6, _⟩ => 9
  | _ => 3

def finalReplacement : Fin 8 → Fin 15
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 6
  | ⟨5, _⟩ => 9
  | ⟨6, _⟩ => 7
  | _ => 8

theorem initial_replacement_inside {family : Family} {owner : Fin 13} {anchor : Fin 8}
    (restricted : family.Restricted owner (anchorIndex anchor)) (choices : Fin 4 → Bool) :
    (family.squares owner).Contains (initialPoints choices (initialReplacement anchor)) := by
  have short := restricted.corner_segment (show (anchorIndex anchor).val < 8 from anchor.isLt)
    (horizontal := 8 / 5) (by norm_num)
  have long := restricted.corner_segment (show (anchorIndex anchor).val < 8 from anchor.isLt)
    (horizontal := 87 / 50) (by norm_num)
  fin_cases anchor <;>
    norm_num [initialPoints, initialReplacement, anchorIndex, Family.unorientPoint,
      Point.reflectX, Point.reflectY, Point.swap] at short long ⊢ <;> assumption

theorem final_replacement_inside {family : Family} {owner : Fin 13} {anchor : Fin 8}
    (restricted : family.Restricted owner (anchorIndex anchor)) (choices : Fin 4 → Bool) :
    (family.squares owner).Contains (finalPoints choices (finalReplacement anchor)) := by
  have short := restricted.corner_segment (show (anchorIndex anchor).val < 8 from anchor.isLt)
    (horizontal := 8 / 5) (by norm_num)
  have long := restricted.corner_segment (show (anchorIndex anchor).val < 8 from anchor.isLt)
    (horizontal := 87 / 50) (by norm_num)
  fin_cases anchor <;>
    norm_num [finalPoints, finalReplacement, anchorIndex, Family.unorientPoint,
      Point.reflectX, Point.reflectY, Point.swap] at short long ⊢ <;> assumption

theorem covered_double_of_pair {count : ℕ} (family : Family) (points : Fin count → Point)
    (owner : Fin 13) (first second : Fin count) (different : first ≠ second)
    (first_inside : (family.squares owner).Contains (points first))
    (second_inside : (family.squares owner).Contains (points second)) :
    2 ≤ (family.covered points owner).card := by
  have bound := family.covered_card_lower points owner {first, second} (by
    intro index member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact first_inside
    · exact second_inside)
  simpa [different] using bound

theorem initial_corner_double {family : Family} {owner : Fin 13} {anchor : Fin 8}
    (restricted : family.Restricted owner (anchorIndex anchor))
    {choices : Fin 4 → Bool} (selected : Selected choices anchor) :
    2 ≤ (family.covered (initialPoints choices) owner).card := by
  apply covered_double_of_pair family (initialPoints choices) owner
    ⟨10 + anchor.val / 2, by omega⟩ (initialReplacement anchor)
  · fin_cases anchor <;> decide
  · have point_eq : initialPoints choices ⟨10 + anchor.val / 2, by omega⟩ =
        cornerAlternative choices ⟨anchor.val / 2, by omega⟩ := by
      fin_cases anchor <;> rfl
    rw [point_eq, selected]
    exact (restricted _).mpr rfl
  · exact initial_replacement_inside restricted choices

theorem final_corner_double {family : Family} {owner : Fin 13} {anchor : Fin 8}
    (restricted : family.Restricted owner (anchorIndex anchor))
    {choices : Fin 4 → Bool} (selected : Selected choices anchor) :
    2 ≤ (family.covered (finalPoints choices) owner).card := by
  apply covered_double_of_pair family (finalPoints choices) owner
    ⟨11 + anchor.val / 2, by omega⟩ (finalReplacement anchor)
  · fin_cases anchor <;> decide
  · have point_eq : finalPoints choices ⟨11 + anchor.val / 2, by omega⟩ =
        cornerAlternative choices ⟨anchor.val / 2, by omega⟩ := by
      fin_cases anchor <;> rfl
    rw [point_eq, selected]
    exact (restricted _).mpr rfl
  · exact final_replacement_inside restricted choices

theorem rectangle_points_of_initial_missing
    {square : PlacedSquare} {choices : Fin 4 → Bool}
    (missing : ∀ index, ¬ square.Contains (initialPoints choices index))
    (hole : Hole square.center) (center_left : square.center.x ≤ 2) :
    square.Contains ⟨89 / 50, 87 / 50⟩ ∧ square.Contains ⟨89 / 50, 113 / 50⟩ := by
  have pair := Bentz.both_offset_points_of_missed_rectangle_corners square
    (left := 1) (bottom := 87 / 50) (height := 13 / 25) (offset := 39 / 50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hole.1 (by linarith) hole.2.2.1 (by linarith [hole.2.2.2]) (by
      intro column row
      fin_cases column <;> fin_cases row
      · convert missing 0 using 1; norm_num [initialPoints]
      · convert missing 2 using 1; norm_num [initialPoints]
      · convert missing 4 using 1; norm_num [initialPoints]
      · convert missing 5 using 1; norm_num [initialPoints])
  norm_num at pair
  exact pair

theorem reflected_rectangle_points_of_initial_missing
    {square : PlacedSquare} {choices : Fin 4 → Bool}
    (missing : ∀ index, ¬ square.Contains (initialPoints choices index))
    (hole : Hole square.center) (center_right : 2 ≤ square.center.x) :
    (square.reflectX 4).Contains ⟨89 / 50, 87 / 50⟩ ∧
      (square.reflectX 4).Contains ⟨89 / 50, 113 / 50⟩ := by
  have pair := Bentz.both_offset_points_of_missed_rectangle_corners (square.reflectX 4)
    (left := 1) (bottom := 87 / 50) (height := 13 / 25) (offset := 39 / 50)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by change 1 ≤ 4 - square.center.x; linarith [hole.2.1])
    (by change 4 - square.center.x ≤ 1 + 1; linarith)
    hole.2.2.1 (by change square.center.y ≤ _; linarith [hole.2.2.2]) (by
      intro column row inside
      have original := (square.reflectX_contains_iff 4
        ((⟨1 + (column : ℝ), 87 / 50 + 13 / 25 * (row : ℝ)⟩ : Point).reflectX 4)).mp
        (by simpa using inside)
      fin_cases column <;> fin_cases row
      · exact missing 1 (by convert original using 1; norm_num [initialPoints, Point.reflectX])
      · exact missing 3 (by convert original using 1; norm_num [initialPoints, Point.reflectX])
      · exact missing 4 (by convert original using 1; norm_num [initialPoints, Point.reflectX])
      · exact missing 5 (by convert original using 1; norm_num [initialPoints, Point.reflectX]))
  norm_num at pair
  exact pair

theorem rectangle_points_doubleton
    (family : Family) (choices : Fin 4 → Bool) (owner : Fin 13)
    (pair : (family.squares owner).Contains ⟨89 / 50, 87 / 50⟩ ∧
      (family.squares owner).Contains ⟨89 / 50, 113 / 50⟩) :
    2 ≤ (family.covered (finalPoints choices) owner).card := by
  have bound := family.covered_card_lower (finalPoints choices) owner {4, 10} (by
    intro index member
    simp only [Finset.mem_insert, Finset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact pair.1
    · exact pair.2)
  exact bound

def reflectAnchor : Fin 8 → Fin 8
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 6
  | ⟨5, _⟩ => 7
  | ⟨6, _⟩ => 4
  | _ => 5

theorem reflected_restricted {family : Family} {owner : Fin 13} {anchor : Fin 8}
    (restricted : family.Restricted owner (anchorIndex anchor)) :
    family.reflectX.Restricted owner (anchorIndex (reflectAnchor anchor)) := by
  have transformed := restricted.reflectX
  have index_eq : Records.Square13.reflectXIndex (anchorIndex anchor) =
      anchorIndex (reflectAnchor anchor) := by
    fin_cases anchor <;> rfl
  rwa [index_eq] at transformed

theorem reflected_corners_different {first second : Fin 8}
    (different : first.val / 2 ≠ second.val / 2) :
    (reflectAnchor first).val / 2 ≠ (reflectAnchor second).val / 2 := by
  revert first second
  decide +kernel

theorem contradiction_of_rectangle_pair
    (final_cover : ∀ choices, Unavoidable (finalPoints choices) 4)
    {family : Family} {first second third : Fin 13} {firstAnchor secondAnchor : Fin 8}
    (first_restricted : family.Restricted first (anchorIndex firstAnchor))
    (second_restricted : family.Restricted second (anchorIndex secondAnchor))
    (corners_different : firstAnchor.val / 2 ≠ secondAnchor.val / 2)
    (third_first : third ≠ first) (third_second : third ≠ second)
    (pair : (family.squares third).Contains ⟨89 / 50, 87 / 50⟩ ∧
      (family.squares third).Contains ⟨89 / 50, 113 / 50⟩) : False := by
  let choices := selectedChoices firstAnchor secondAnchor
  have first_second : first ≠ second :=
    family.restricted_owner_ne first_restricted second_restricted (by
      intro equal
      have values := congrArg Fin.val equal
      apply corners_different
      dsimp [anchorIndex] at values
      rw [values])
  exact family.contradiction_of_three_doubletons (finalPoints choices) (by norm_num)
    (final_cover choices) first second third first_second third_first.symm third_second.symm
    (final_corner_double first_restricted (selectedChoices_first firstAnchor secondAnchor))
    (final_corner_double second_restricted
      (selectedChoices_second firstAnchor secondAnchor corners_different))
    (rectangle_points_doubleton family choices third pair)

theorem contradiction_of_nonadjacent
    (initial_cover : ∀ choices (square : PlacedSquare), square.Fits 4 →
      (∃ index, square.Contains (initialPoints choices index)) ∨ Hole square.center)
    (final_cover : ∀ choices, Unavoidable (finalPoints choices) 4)
    {family : Family} {first second : Fin 13} {firstAnchor secondAnchor : Fin 8}
    (first_restricted : family.Restricted first (anchorIndex firstAnchor))
    (second_restricted : family.Restricted second (anchorIndex secondAnchor))
    (corners_different : firstAnchor.val / 2 ≠ secondAnchor.val / 2) : False := by
  let choices := selectedChoices firstAnchor secondAnchor
  have first_second : first ≠ second :=
    family.restricted_owner_ne first_restricted second_restricted (by
      intro equal
      have values := congrArg Fin.val equal
      apply corners_different
      dsimp [anchorIndex] at values
      rw [values])
  obtain ⟨third, third_first, third_second, missing⟩ :=
    family.exists_uncovered_of_two_doubletons (initialPoints choices) (by norm_num)
      first second first_second
      (initial_corner_double first_restricted (selectedChoices_first firstAnchor secondAnchor))
      (initial_corner_double second_restricted
        (selectedChoices_second firstAnchor secondAnchor corners_different))
  have hole : Hole (family.squares third).center := by
    obtain ⟨index, inside⟩ | hole := initial_cover choices (family.squares third) (family.fits third)
    · exact (missing index inside).elim
    · exact hole
  by_cases center_left : (family.squares third).center.x ≤ 2
  · exact contradiction_of_rectangle_pair final_cover first_restricted second_restricted
      corners_different third_first third_second
      (rectangle_points_of_initial_missing missing hole center_left)
  · exact contradiction_of_rectangle_pair final_cover
      (reflected_restricted first_restricted) (reflected_restricted second_restricted)
      (reflected_corners_different corners_different) third_first third_second
      (reflected_rectangle_points_of_initial_missing missing hole (by linarith))

theorem contradiction_of_normalized_nonadjacent
    (initial_cover : ∀ choices (square : PlacedSquare), square.Fits 4 →
      (∃ index, square.Contains (initialPoints choices index)) ∨ Hole square.center)
    (final_cover : ∀ choices, Unavoidable (finalPoints choices) 4)
    {family : Family} {first second : Fin 13} {other : Fin 16}
    (first_restricted : family.Restricted first 0)
    (second_restricted : family.Restricted second other)
    (other_lower : 2 ≤ other.val) (other_upper : other.val < 8) : False := by
  exact contradiction_of_nonadjacent initial_cover final_cover
    (firstAnchor := 0) (secondAnchor := ⟨other.val, other_upper⟩)
    first_restricted second_restricted (by dsimp; omega)

end SquarePackingArchive.BentzThirteen.Nonadjacent
