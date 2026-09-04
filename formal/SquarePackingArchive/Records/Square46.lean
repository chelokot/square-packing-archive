import SquarePackingArchive.BoundaryUnavoidable
import SquarePackingArchive.FriedmanStrip
import SquarePackingArchive.Records.SquareNumbers

namespace SquarePackingArchive.Records.Square46

abbrev LatticeIndex := (Fin 4 × Fin 6) ⊕ (Fin 3 × Fin 7)

noncomputable def latticePoint : LatticeIndex → Point
  | .inl (row, column) =>
      ⟨(column : ℝ) + 1, 451 / 500 + 2 * (row : ℝ) * (433 / 500)⟩
  | .inr (row, column) =>
      ⟨(column : ℝ) + 1 / 2, 451 / 500 + (2 * (row : ℝ) + 1) * (433 / 500)⟩

def HasLatticePoint (square : PlacedSquare) : Prop :=
  ∃ index : LatticeIndex, square.Contains (latticePoint index)

lemma even_point
    {square : PlacedSquare} (strict : square.StrictFits 7)
    (row : Fin 4) (column : Fin 8)
    (contained : square.Contains
      ⟨(column : ℝ), 451 / 500 + 2 * (row : ℝ) * (433 / 500)⟩) :
    HasLatticePoint square := by
  have bounds := strict contained
  by_cases first : column.val = 0
  · have : (column : ℝ) = 0 := by exact_mod_cast first
    exact False.elim (by simpa [this] using bounds.1)
  by_cases last : column.val = 7
  · have : (column : ℝ) = 7 := by exact_mod_cast last
    exact False.elim (by simpa [this] using bounds.2.1)
  let inner : Fin 6 := ⟨column.val - 1, by omega⟩
  have horizontal : (inner : ℝ) + 1 = (column : ℝ) := by
    dsimp [inner]
    rw [Nat.cast_sub (by omega)]
    norm_num
  exact ⟨.inl (row, inner), by simpa [latticePoint, horizontal] using contained⟩

lemma odd_point
    {square : PlacedSquare} (strict : square.StrictFits 7)
    (row : Fin 3) (column : Fin 9)
    (contained : square.Contains
      ⟨(column : ℝ) - 1 / 2, 451 / 500 + (2 * (row : ℝ) + 1) * (433 / 500)⟩) :
    HasLatticePoint square := by
  have bounds := strict contained
  by_cases first : column.val = 0
  · have : (column : ℝ) = 0 := by exact_mod_cast first
    exact False.elim (by norm_num [this] at bounds)
  by_cases last : column.val = 8
  · have : (column : ℝ) = 8 := by exact_mod_cast last
    exact False.elim (by norm_num [this] at bounds)
  let inner : Fin 7 := ⟨column.val - 1, by omega⟩
  have horizontal : (inner : ℝ) + 1 / 2 = (column : ℝ) - 1 / 2 := by
    dsimp [inner]
    rw [Nat.cast_sub (by omega)]
    norm_num
    ring
  refine ⟨.inr (row, inner), ?_⟩
  change square.Contains ⟨(inner : ℝ) + 1 / 2, _⟩
  rw [horizontal]
  exact contained

lemma triangle_band
    (square : PlacedSquare) (base evenHeight oddHeight position : ℝ)
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1)
    (horizontal_lower : base ≤ square.center.x)
    (horizontal_upper : square.center.x ≤ base + 1)
    (vertical_position : square.center.y =
      (1 - position) * evenHeight + position * oddHeight)
    (height_bound : (evenHeight - oddHeight) ^ 2 ≤ 3 / 4) :
    square.Contains ⟨base, evenHeight⟩ ∨
      square.Contains ⟨base + 1, evenHeight⟩ ∨
      square.Contains ⟨base - 1 / 2, oddHeight⟩ ∨
      square.Contains ⟨base + 1 / 2, oddHeight⟩ ∨
      square.Contains ⟨base + 3 / 2, oddHeight⟩ := by
  by_cases left_region : square.center.x - base ≤ position / 2
  · have covered := square.contains_triangleVertex
      ⟨base, evenHeight⟩ ⟨base - 1 / 2, oddHeight⟩
      ⟨base + 1 / 2, oddHeight⟩
      (1 - position) (position / 2 - (square.center.x - base))
      (position / 2 + (square.center.x - base))
      (by linarith) (by linarith) (by linarith) (by ring)
      (by dsimp; ring) (by dsimp; nlinarith [vertical_position])
      (by dsimp; nlinarith) (by dsimp; nlinarith) (by dsimp; ring_nf; norm_num)
    tauto
  · by_cases right_region : base + 1 - square.center.x ≤ position / 2
    · have covered := square.contains_triangleVertex
        ⟨base + 1, evenHeight⟩ ⟨base + 1 / 2, oddHeight⟩
        ⟨base + 3 / 2, oddHeight⟩
        (1 - position) (position / 2 + (base + 1 - square.center.x))
        (position / 2 - (base + 1 - square.center.x))
        (by linarith) (by linarith) (by linarith) (by ring)
        (by dsimp; ring) (by dsimp; nlinarith [vertical_position])
        (by dsimp; nlinarith) (by dsimp; nlinarith) (by dsimp; ring_nf; norm_num)
      tauto
    · have covered := square.contains_triangleVertex
        ⟨base, evenHeight⟩ ⟨base + 1, evenHeight⟩
        ⟨base + 1 / 2, oddHeight⟩
        (base + 1 - square.center.x - position / 2)
        (square.center.x - base - position / 2) position
        (by linarith) (by linarith) position_lower (by ring)
        (by dsimp; ring) (by dsimp; nlinarith [vertical_position])
        (by dsimp; ring_nf; norm_num) (by dsimp; nlinarith) (by dsimp; nlinarith)
      tauto

lemma band_has_latticePoint
    {square : PlacedSquare} (strict : square.StrictFits 7)
    (evenRow : Fin 4) (oddRow : Fin 3) (position : ℝ)
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1)
    (vertical_position : square.center.y =
      (1 - position) * (451 / 500 + 2 * (evenRow : ℝ) * (433 / 500)) +
        position * (451 / 500 + (2 * (oddRow : ℝ) + 1) * (433 / 500)))
    (height_bound :
      ((451 / 500 + 2 * (evenRow : ℝ) * (433 / 500)) -
        (451 / 500 + (2 * (oddRow : ℝ) + 1) * (433 / 500))) ^ 2 ≤ 3 / 4) :
    HasLatticePoint square := by
  have center_mem : square.Contains square.center :=
    ⟨0, 0, by norm_num, by norm_num, by simp [PlacedSquare.point, Frame.place]⟩
  have center_bounds := strict center_mem
  let column : Fin 7 :=
    ⟨⌊square.center.x⌋₊, (Nat.floor_lt center_bounds.1.le).2 center_bounds.2.1⟩
  have lower : (column : ℝ) ≤ square.center.x := Nat.floor_le center_bounds.1.le
  have upper : square.center.x ≤ (column : ℝ) + 1 :=
    (Nat.lt_floor_add_one square.center.x).le
  obtain contained | contained | contained | contained | contained :=
    triangle_band square (column : ℝ)
      (451 / 500 + 2 * (evenRow : ℝ) * (433 / 500))
      (451 / 500 + (2 * (oddRow : ℝ) + 1) * (433 / 500)) position
      position_lower position_upper lower upper vertical_position height_bound
  · exact even_point strict evenRow ⟨column.val, by omega⟩ contained
  · apply even_point strict evenRow ⟨column.val + 1, by omega⟩
    simpa using contained
  · exact odd_point strict oddRow ⟨column.val, by omega⟩ contained
  · apply odd_point strict oddRow ⟨column.val + 1, by omega⟩
    convert contained using 1
    simp
    ring
  · apply odd_point strict oddRow ⟨column.val + 2, by omega⟩
    convert contained using 1
    simp
    ring

lemma HasLatticePoint.of_reflectY
    {square : PlacedSquare} (covered : HasLatticePoint (square.reflectY 7)) :
    HasLatticePoint square := by
  obtain ⟨index, contained⟩ := covered
  have source : square.Contains ((latticePoint index).reflectY 7) :=
    (square.reflectY_contains_iff 7 ((latticePoint index).reflectY 7)).mp
      (by simpa using contained)
  rcases index with ⟨row, column⟩ | ⟨row, column⟩
  · refine ⟨.inl (row.rev, column), ?_⟩
    convert source using 1
    fin_cases row <;> simp [latticePoint, Point.reflectY] <;> ring
  · refine ⟨.inr (row.rev, column), ?_⟩
    convert source using 1
    fin_cases row <;> simp [latticePoint, Point.reflectY] <;> ring

lemma bottom_has_latticePoint
    {square : PlacedSquare} (strict : square.StrictFits 7)
    (center_y_upper : square.center.y ≤ 451 / 500) :
    HasLatticePoint square := by
  by_cases left : square.center.x ≤ 1
  · have contained := square.contains_cornerPoint strict.fits
      (show (1 : ℝ) ≤ 1 by norm_num) (by norm_num : (451 : ℝ) / 500 ≤ 1)
      left center_y_upper
    exact ⟨.inl (0, 0), by simpa [latticePoint] using contained⟩
  by_cases right : 6 ≤ square.center.x
  · have contained := (square.reflectX 7).contains_cornerPoint
      ((square.reflectX_fits_iff 7).2 strict.fits)
      (show (1 : ℝ) ≤ 1 by norm_num) (by norm_num : (451 : ℝ) / 500 ≤ 1)
      (by simp [PlacedSquare.reflectX, Point.reflectX]; linarith)
      (by simpa [PlacedSquare.reflectX, Point.reflectX] using center_y_upper)
    refine ⟨.inl (0, 5), ?_⟩
    apply (square.reflectX_contains_iff 7 _).mp
    convert contained using 1
    norm_num [latticePoint, Point.reflectX]
  have center_nonnegative : 0 ≤ square.center.x := by linarith
  let column : Fin 6 := ⟨⌊square.center.x⌋₊,
    (Nat.floor_lt center_nonnegative).2 (by norm_num; linarith)⟩
  obtain contained | contained := square.contains_bottomUnitPair strict.fits
    rationalStripHeight_le_sqrt_two_sub_half
    (Nat.floor_le center_nonnegative) (Nat.lt_floor_add_one square.center.x).le
    center_y_upper
  · apply even_point strict 0 ⟨column.val, by omega⟩
    simpa [column] using contained
  · apply even_point strict 0 ⟨column.val + 1, by omega⟩
    simpa [column] using contained

lemma strict_unavoidable
    (square : PlacedSquare) (strict : square.StrictFits 7) :
    HasLatticePoint square := by
  by_cases bottom : square.center.y ≤ 451 / 500
  · exact bottom_has_latticePoint strict bottom
  by_cases top : 7 - 451 / 500 ≤ square.center.y
  · apply HasLatticePoint.of_reflectY
    apply bottom_has_latticePoint strict.reflectY
    simp [PlacedSquare.reflectY, Point.reflectY]
    linarith
  by_cases first_band : square.center.y ≤ 884 / 500
  · apply band_has_latticePoint strict 0 0 ((square.center.y - 451 / 500) / (433 / 500))
    all_goals norm_num <;> linarith
  by_cases second_band : square.center.y ≤ 1317 / 500
  · apply band_has_latticePoint strict 1 0 ((1317 / 500 - square.center.y) / (433 / 500))
    all_goals norm_num <;> linarith
  by_cases third_band : square.center.y ≤ 7 / 2
  · apply band_has_latticePoint strict 1 1 ((square.center.y - 1317 / 500) / (433 / 500))
    all_goals norm_num <;> linarith
  by_cases fourth_band : square.center.y ≤ 2183 / 500
  · apply band_has_latticePoint strict 2 1 ((2183 / 500 - square.center.y) / (433 / 500))
    all_goals norm_num <;> linarith
  by_cases fifth_band : square.center.y ≤ 2616 / 500
  · apply band_has_latticePoint strict 2 2 ((square.center.y - 2183 / 500) / (433 / 500))
    all_goals norm_num <;> linarith
  · apply band_has_latticePoint strict 3 2 ((3049 / 500 - square.center.y) / (433 / 500))
    all_goals norm_num <;> linarith

noncomputable def points : Fin 45 → Point := fun index =>
  latticePoint ((Fintype.equivFin LatticeIndex).symm (Fin.cast (by norm_num) index))

theorem s46_ge_seven : IsLowerBound 46 7 := by
  apply lowerBound_succ_of_strict_unavoidable (points := points)
  intro square strict
  obtain ⟨index, contained⟩ := strict_unavoidable square strict
  refine ⟨Fin.cast (by norm_num) ((Fintype.equivFin LatticeIndex) index), ?_⟩
  simpa [points] using contained

theorem s_eq_seven {squareCount : ℕ}
    (lower : 46 ≤ squareCount) (upper : squareCount ≤ 49) :
    IsMinimumSide squareCount 7 := by
  exact ⟨SquareNumbers.s49_eq_seven.1.mono upper,
    fun candidateSide packing => s46_ge_seven candidateSide (packing.mono lower)⟩

theorem s46_eq_seven : IsMinimumSide 46 7 :=
  s_eq_seven (by norm_num) (by norm_num)

theorem s47_eq_seven : IsMinimumSide 47 7 :=
  s_eq_seven (by norm_num) (by norm_num)

theorem s48_eq_seven : IsMinimumSide 48 7 :=
  s_eq_seven (by norm_num) (by norm_num)

end SquarePackingArchive.Records.Square46
