import SquarePackingArchive.Records.Square5

namespace SquarePackingArchive.Records.Square10

open Square5 (diagonal axisFrame)

noncomputable def side : ℝ := 3 + diagonal

noncomputable def addedSquares : Fin 5 → PlacedSquare := ![
  { center := ⟨1 / 2, 5 / 2 + diagonal⟩, frame := axisFrame },
  { center := ⟨3 / 2, 5 / 2 + diagonal⟩, frame := axisFrame },
  { center := ⟨5 / 2, 5 / 2 + diagonal⟩, frame := axisFrame },
  { center := ⟨5 / 2 + diagonal, 1 / 2⟩, frame := axisFrame },
  { center := ⟨5 / 2 + diagonal, 3 / 2⟩, frame := axisFrame }
]

noncomputable def squares : Fin 10 → PlacedSquare :=
  fun index => Fin.addCases (m := 5) (n := 5) Square5.squares addedSquares index

lemma added_fits (index : Fin 5) : (addedSquares index).Fits side := by
  intro point point_mem
  rcases point_mem with ⟨localX, localY, localX_le, localY_le, rfl⟩
  rcases abs_le.mp localX_le with ⟨localX_lower, localX_upper⟩
  rcases abs_le.mp localY_le with ⟨localY_lower, localY_upper⟩
  have diagonal_nonnegative := Square5.diagonal_positive.le
  fin_cases index <;>
    simp [addedSquares, PlacedSquare.point, Frame.place, axisFrame,
      Container.Contains, side] <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma added_disjoint (left right : Fin 5) (different : left ≠ right) :
    (addedSquares left).InteriorDisjoint (addedSquares right) := by
  intro point shared
  rcases shared.1 with ⟨leftX, leftY, leftX_lt, leftY_lt, left_eq⟩
  rcases shared.2 with ⟨rightX, rightY, rightX_lt, rightY_lt, right_eq⟩
  have horizontal := congrArg Point.x (left_eq.symm.trans right_eq)
  have vertical := congrArg Point.y (left_eq.symm.trans right_eq)
  rcases abs_lt.mp leftX_lt with ⟨leftX_lower, leftX_upper⟩
  rcases abs_lt.mp leftY_lt with ⟨leftY_lower, leftY_upper⟩
  rcases abs_lt.mp rightX_lt with ⟨rightX_lower, rightX_upper⟩
  rcases abs_lt.mp rightY_lt with ⟨rightY_lower, rightY_upper⟩
  have diagonal_nonnegative := Square5.diagonal_positive.le
  fin_cases left <;> fin_cases right <;> simp at different <;>
    simp [addedSquares, PlacedSquare.point, Frame.place, axisFrame] at horizontal vertical <;>
    linarith

lemma original_added_disjoint (original added : Fin 5) :
    (Square5.squares original).InteriorDisjoint (addedSquares added) := by
  intro point shared
  have original_mem : (Square5.squares original).Contains point := by
    rcases shared.1 with ⟨localX, localY, localX_lt, localY_lt, equality⟩
    exact ⟨localX, localY, localX_lt.le, localY_lt.le, equality⟩
  have original_bounds := Square5.square_fits original original_mem
  rcases shared.2 with ⟨localX, localY, localX_lt, localY_lt, rfl⟩
  rcases abs_lt.mp localX_lt with ⟨localX_lower, localX_upper⟩
  rcases abs_lt.mp localY_lt with ⟨localY_lower, localY_upper⟩
  fin_cases added <;>
    simp [Container.Contains, Square5.side, addedSquares, PlacedSquare.point,
      Frame.place, axisFrame] at original_bounds <;>
    linarith [original_bounds.2.1, original_bounds.2.2.2]

lemma square_fits (index : Fin 10) : (squares index).Fits side := by
  refine Fin.addCases (m := 5) (n := 5)
    (motive := fun index => (squares index).Fits side)
    (fun original => ?_) (fun added => ?_) index
  · simpa only [squares, Fin.addCases_left, Packing.enlarge, Square5.packing] using
      (Square5.packing.enlarge (largerSide := side)
        (by dsimp [Square5.side, side]; linarith)).fits original
  · simpa only [squares, Fin.addCases_right] using added_fits added

lemma square_disjoint (left right : Fin 10) (different : left ≠ right) :
    (squares left).InteriorDisjoint (squares right) := by
  revert different
  refine Fin.addCases (m := 5) (n := 5)
    (motive := fun left => left ≠ right → (squares left).InteriorDisjoint (squares right))
    (fun originalLeft => ?_) (fun addedLeft => ?_) left
  · refine Fin.addCases (m := 5) (n := 5)
      (motive := fun right => Fin.castAdd 5 originalLeft ≠ right →
        (squares (Fin.castAdd 5 originalLeft)).InteriorDisjoint (squares right))
      (fun originalRight => ?_) (fun addedRight => ?_) right
    · intro different
      simpa only [squares, Fin.addCases_left] using Square5.square_disjoint originalLeft originalRight
        (fun equal => different (congrArg (Fin.castAdd 5) equal))
    · intro _
      simpa only [squares, Fin.addCases_left, Fin.addCases_right] using
        original_added_disjoint originalLeft addedRight
  · refine Fin.addCases (m := 5) (n := 5)
      (motive := fun right => Fin.natAdd 5 addedLeft ≠ right →
        (squares (Fin.natAdd 5 addedLeft)).InteriorDisjoint (squares right))
      (fun originalRight => ?_) (fun addedRight => ?_) right
    · intro _
      simpa only [squares, Fin.addCases_left, Fin.addCases_right] using
        (original_added_disjoint originalRight addedLeft).symm
    · intro different
      simpa only [squares, Fin.addCases_right] using added_disjoint addedLeft addedRight
        (fun equal => different (congrArg (Fin.natAdd 5) equal))

noncomputable def packing : Packing 10 side where
  squares := squares
  side_nonnegative := by dsimp [side]; linarith [Square5.diagonal_positive]
  fits := square_fits
  disjoint := square_disjoint

theorem s10_le_goebel : HasPacking 10 (3 + Real.sqrt 2 / 2) := by
  exact ⟨packing⟩

end SquarePackingArchive.Records.Square10
