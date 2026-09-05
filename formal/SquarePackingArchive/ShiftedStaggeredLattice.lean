import SquarePackingArchive.BentzHorizontal

namespace SquarePackingArchive

structure ShiftedStaggeredLattice (width evenRows oddRows : ℕ) extends
    StaggeredLattice width evenRows oddRows where
  oddOffset : Fin oddRows → ℝ

namespace ShiftedStaggeredLattice

variable {width evenRows oddRows : ℕ}

noncomputable def point (lattice : ShiftedStaggeredLattice width evenRows oddRows) :
    StaggeredLattice.Index width evenRows oddRows → Point
  | .inl (row, column) => ⟨(column : ℝ) + 1, lattice.evenHeight row⟩
  | .inr (row, column) => ⟨(column : ℝ) + lattice.oddOffset row, lattice.oddHeight row⟩

def HasPoint (lattice : ShiftedStaggeredLattice width evenRows oddRows) (square : PlacedSquare) : Prop :=
  ∃ index, square.Contains (lattice.point index)

variable (lattice : ShiftedStaggeredLattice width evenRows oddRows)

lemma even_point
    {square : PlacedSquare} (strict : square.StrictFits ((width : ℝ) + 1))
    (row : Fin evenRows) (column : Fin (width + 2))
    (contained : square.Contains ⟨(column : ℝ), lattice.evenHeight row⟩) :
    lattice.HasPoint square := by
  have bounds := strict contained
  by_cases first : column.val = 0
  · have : (column : ℝ) = 0 := by exact_mod_cast first
    exact False.elim (by simpa [this] using bounds.1)
  by_cases last : column.val = width + 1
  · have : (column : ℝ) = (width : ℝ) + 1 := by exact_mod_cast last
    exact False.elim (by simpa [this] using bounds.2.1)
  let inner : Fin width := ⟨column.val - 1, by omega⟩
  have horizontal : (inner : ℝ) + 1 = (column : ℝ) := by
    dsimp [inner]
    rw [Nat.cast_sub (by omega)]
    norm_num
  exact ⟨.inl (row, inner), by simpa [point, horizontal] using contained⟩

lemma odd_point
    {square : PlacedSquare} (strict : square.StrictFits ((width : ℝ) + 1))
    (row : Fin oddRows) (column : Fin (width + 3))
    (offset_positive : 0 < lattice.oddOffset row) (offset_lt_one : lattice.oddOffset row < 1)
    (contained : square.Contains ⟨(column : ℝ) + lattice.oddOffset row - 1, lattice.oddHeight row⟩) :
    lattice.HasPoint square := by
  have bounds := strict contained
  by_cases first : column.val = 0
  · have : (column : ℝ) = 0 := by exact_mod_cast first
    have outside := bounds.1
    change 0 < (column : ℝ) + lattice.oddOffset row - 1 at outside
    rw [this] at outside
    exact False.elim (by linarith)
  by_cases last : column.val = width + 2
  · have : (column : ℝ) = (width : ℝ) + 2 := by exact_mod_cast last
    have outside := bounds.2.1
    change (column : ℝ) + lattice.oddOffset row - 1 < (width : ℝ) + 1 at outside
    rw [this] at outside
    exact False.elim (by linarith)
  let inner : Fin (width + 1) := ⟨column.val - 1, by omega⟩
  have horizontal : (inner : ℝ) + lattice.oddOffset row = (column : ℝ) + lattice.oddOffset row - 1 := by
    dsimp [inner]
    rw [Nat.cast_sub (by omega)]
    norm_num
    ring
  exact ⟨.inr (row, inner), by simpa [point, horizontal] using contained⟩

lemma band_has_point
    {square : PlacedSquare} (strict : square.StrictFits ((width : ℝ) + 1))
    (evenRow : Fin evenRows) (oddRow : Fin oddRows) (position : ℝ)
    (offset_positive : 0 < lattice.oddOffset oddRow) (offset_lt_one : lattice.oddOffset oddRow < 1)
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1)
    (vertical_position : square.center.y =
      (1 - position) * lattice.evenHeight evenRow + position * lattice.oddHeight oddRow)
    (left_distance : (lattice.oddOffset oddRow) ^ 2 +
      (lattice.evenHeight evenRow - lattice.oddHeight oddRow) ^ 2 ≤ 1)
    (right_distance : (1 - lattice.oddOffset oddRow) ^ 2 +
      (lattice.evenHeight evenRow - lattice.oddHeight oddRow) ^ 2 ≤ 1) :
    lattice.HasPoint square := by
  have center_mem : square.Contains square.center :=
    ⟨0, 0, by norm_num, by norm_num, by simp [PlacedSquare.point, Frame.place]⟩
  have center_bounds := strict center_mem
  let column : Fin (width + 1) := ⟨⌊square.center.x⌋₊,
    (Nat.floor_lt center_bounds.1.le).2 (by simpa using center_bounds.2.1)⟩
  have lower : (column : ℝ) ≤ square.center.x := Nat.floor_le center_bounds.1.le
  have upper : square.center.x ≤ (column : ℝ) + 1 := (Nat.lt_floor_add_one square.center.x).le
  obtain contained | contained | contained | contained | contained :=
    square.contains_shifted_triangle_band (column : ℝ) (lattice.evenHeight evenRow)
      (lattice.oddHeight oddRow) (lattice.oddOffset oddRow) position
      position_lower position_upper lower upper vertical_position left_distance right_distance
  · exact lattice.even_point strict evenRow ⟨column.val, by omega⟩ contained
  · apply lattice.even_point strict evenRow ⟨column.val + 1, by omega⟩
    simpa using contained
  · exact lattice.odd_point strict oddRow ⟨column.val, by omega⟩ offset_positive offset_lt_one contained
  · apply lattice.odd_point strict oddRow ⟨column.val + 1, by omega⟩ offset_positive offset_lt_one
    convert contained using 1
    simp
    ring
  · apply lattice.odd_point strict oddRow ⟨column.val + 2, by omega⟩ offset_positive offset_lt_one
    convert contained using 1
    simp
    ring

lemma band_from_below
    {square : PlacedSquare} (strict : square.StrictFits ((width : ℝ) + 1))
    (evenRow : Fin evenRows) (oddRow : Fin oddRows)
    (offset_positive : 0 < lattice.oddOffset oddRow) (offset_lt_one : lattice.oddOffset oddRow < 1)
    (gap_positive : 0 < lattice.oddHeight oddRow - lattice.evenHeight evenRow)
    (left_distance : (lattice.oddOffset oddRow) ^ 2 +
      (lattice.evenHeight evenRow - lattice.oddHeight oddRow) ^ 2 ≤ 1)
    (right_distance : (1 - lattice.oddOffset oddRow) ^ 2 +
      (lattice.evenHeight evenRow - lattice.oddHeight oddRow) ^ 2 ≤ 1)
    (center_lower : lattice.evenHeight evenRow ≤ square.center.y)
    (center_upper : square.center.y ≤ lattice.oddHeight oddRow) : lattice.HasPoint square := by
  apply lattice.band_has_point strict evenRow oddRow
    ((square.center.y - lattice.evenHeight evenRow) /
      (lattice.oddHeight oddRow - lattice.evenHeight evenRow))
    offset_positive offset_lt_one
  · exact div_nonneg (sub_nonneg.mpr center_lower) gap_positive.le
  · exact (div_le_one gap_positive).2 (by linarith)
  · field_simp
    ring
  · exact left_distance
  · exact right_distance

lemma band_from_above
    {square : PlacedSquare} (strict : square.StrictFits ((width : ℝ) + 1))
    (evenRow : Fin evenRows) (oddRow : Fin oddRows)
    (offset_positive : 0 < lattice.oddOffset oddRow) (offset_lt_one : lattice.oddOffset oddRow < 1)
    (gap_positive : 0 < lattice.evenHeight evenRow - lattice.oddHeight oddRow)
    (left_distance : (lattice.oddOffset oddRow) ^ 2 +
      (lattice.evenHeight evenRow - lattice.oddHeight oddRow) ^ 2 ≤ 1)
    (right_distance : (1 - lattice.oddOffset oddRow) ^ 2 +
      (lattice.evenHeight evenRow - lattice.oddHeight oddRow) ^ 2 ≤ 1)
    (center_lower : lattice.oddHeight oddRow ≤ square.center.y)
    (center_upper : square.center.y ≤ lattice.evenHeight evenRow) : lattice.HasPoint square := by
  apply lattice.band_has_point strict evenRow oddRow
    ((lattice.evenHeight evenRow - square.center.y) /
      (lattice.evenHeight evenRow - lattice.oddHeight oddRow))
    offset_positive offset_lt_one
  · exact div_nonneg (sub_nonneg.mpr center_upper) gap_positive.le
  · exact (div_le_one gap_positive).2 (by linarith)
  · field_simp
    ring
  · exact left_distance
  · exact right_distance

lemma bottom_even
    {square : PlacedSquare} (fits : square.Fits ((width : ℝ) + 1))
    (width_positive : 0 < width) (row : Fin evenRows)
    (height_upper : lattice.evenHeight row ≤ Real.sqrt 2 - 1 / 2)
    (center_below : square.center.y ≤ lattice.evenHeight row) : lattice.HasPoint square := by
  obtain ⟨column, contained⟩ := square.contains_bottomSpacedRow (width - 1) fits
    (left := 1) (by norm_num)
    (by rw [Nat.cast_sub width_positive]; norm_num) height_upper center_below
  exact ⟨.inl (row, Fin.cast (Nat.sub_add_cancel width_positive) column),
    by simpa [point, add_comm] using contained⟩

lemma top_odd
    {square : PlacedSquare} (fits : square.Fits ((width : ℝ) + 1))
    (row : Fin oddRows)
    (offset_nonnegative : 0 ≤ lattice.oddOffset row) (offset_at_most_one : lattice.oddOffset row ≤ 1)
    (height_lower : (width : ℝ) + 1 - lattice.oddHeight row ≤ Real.sqrt 2 - 1 / 2)
    (center_above : lattice.oddHeight row ≤ square.center.y) : lattice.HasPoint square := by
  obtain ⟨column, contained⟩ := square.contains_topSpacedRow width fits
    (left := lattice.oddOffset row) offset_at_most_one (by linarith) height_lower center_above
  exact ⟨.inr (row, column), by simpa [point, add_comm] using contained⟩

noncomputable def points : Fin (evenRows * width + oddRows * (width + 1)) → Point :=
  fun index => lattice.point ((Fintype.equivFin (StaggeredLattice.Index width evenRows oddRows)).symm
    (Fin.cast (by simp [StaggeredLattice.Index]) index))

end ShiftedStaggeredLattice

end SquarePackingArchive
