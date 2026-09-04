import SquarePackingArchive.BoundaryUnavoidable
import SquarePackingArchive.FriedmanStrip

namespace SquarePackingArchive

structure StaggeredLattice (width evenRows oddRows : ℕ) where
  evenHeight : Fin evenRows → ℝ
  oddHeight : Fin oddRows → ℝ

namespace StaggeredLattice

abbrev Index (width evenRows oddRows : ℕ) :=
  (Fin evenRows × Fin width) ⊕ (Fin oddRows × Fin (width + 1))

variable {width evenRows oddRows : ℕ}

noncomputable def point (lattice : StaggeredLattice width evenRows oddRows) :
    Index width evenRows oddRows → Point
  | .inl (row, column) => ⟨(column : ℝ) + 1, lattice.evenHeight row⟩
  | .inr (row, column) => ⟨(column : ℝ) + 1 / 2, lattice.oddHeight row⟩

def HasPoint (lattice : StaggeredLattice width evenRows oddRows) (square : PlacedSquare) : Prop :=
  ∃ index, square.Contains (lattice.point index)

variable (lattice : StaggeredLattice width evenRows oddRows)

lemma even_point
    {square : PlacedSquare} (strict : square.StrictFits ((width : ℝ) + 1))
    (row : Fin evenRows) (column : Fin (width + 2))
    (contained : square.Contains
      ⟨(column : ℝ), lattice.evenHeight row⟩) :
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
    (contained : square.Contains
      ⟨(column : ℝ) - 1 / 2, lattice.oddHeight row⟩) :
    lattice.HasPoint square := by
  have bounds := strict contained
  by_cases first : column.val = 0
  · have : (column : ℝ) = 0 := by exact_mod_cast first
    exact False.elim (by norm_num [this] at bounds)
  by_cases last : column.val = width + 2
  · have : (column : ℝ) = (width : ℝ) + 2 := by exact_mod_cast last
    have outside := bounds.2.1
    change (column : ℝ) - 1 / 2 < (width : ℝ) + 1 at outside
    rw [this] at outside
    exact False.elim (by linarith)
  let inner : Fin (width + 1) := ⟨column.val - 1, by omega⟩
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
    {square : PlacedSquare} (strict : square.StrictFits ((width : ℝ) + 1))
    (evenRow : Fin evenRows) (oddRow : Fin oddRows) (position : ℝ)
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1)
    (vertical_position : square.center.y =
      (1 - position) * (lattice.evenHeight evenRow) +
        position * (lattice.oddHeight oddRow))
    (height_bound :
      ((lattice.evenHeight evenRow) -
        (lattice.oddHeight oddRow)) ^ 2 ≤ 3 / 4) :
    lattice.HasPoint square := by
  have center_mem : square.Contains square.center :=
    ⟨0, 0, by norm_num, by norm_num, by simp [PlacedSquare.point, Frame.place]⟩
  have center_bounds := strict center_mem
  let column : Fin (width + 1) :=
    ⟨⌊square.center.x⌋₊,
      (Nat.floor_lt center_bounds.1.le).2 (by simpa using center_bounds.2.1)⟩
  have lower : (column : ℝ) ≤ square.center.x := Nat.floor_le center_bounds.1.le
  have upper : square.center.x ≤ (column : ℝ) + 1 :=
    (Nat.lt_floor_add_one square.center.x).le
  obtain contained | contained | contained | contained | contained :=
    triangle_band square (column : ℝ)
      (lattice.evenHeight evenRow)
      (lattice.oddHeight oddRow) position
      position_lower position_upper lower upper vertical_position height_bound
  · exact lattice.even_point strict evenRow ⟨column.val, by omega⟩ contained
  · apply lattice.even_point strict evenRow ⟨column.val + 1, by omega⟩
    simpa using contained
  · exact lattice.odd_point strict oddRow ⟨column.val, by omega⟩ contained
  · apply lattice.odd_point strict oddRow ⟨column.val + 1, by omega⟩
    convert contained using 1
    simp
    ring
  · apply lattice.odd_point strict oddRow ⟨column.val + 2, by omega⟩
    convert contained using 1
    simp
    ring


lemma bottom_even
    {square : PlacedSquare} (fits : square.Fits ((width : ℝ) + 1))
    (width_positive : 0 < width) (row : Fin evenRows)
    (height_upper : lattice.evenHeight row ≤ Real.sqrt 2 - 1 / 2)
    (center_below : square.center.y ≤ lattice.evenHeight row) :
    lattice.HasPoint square := by
  have width_at_least_one : 1 ≤ width := width_positive
  obtain ⟨column, contained⟩ := square.contains_bottomSpacedRow (width - 1)
    fits (left := 1) (by norm_num)
    (by rw [Nat.cast_sub width_at_least_one]; norm_num)
    height_upper center_below
  refine ⟨.inl (row, Fin.cast (Nat.sub_add_cancel width_at_least_one) column), ?_⟩
  simpa [point, add_comm] using contained

lemma top_even
    {square : PlacedSquare} (fits : square.Fits ((width : ℝ) + 1))
    (width_positive : 0 < width) (row : Fin evenRows)
    (height_lower : (width : ℝ) + 1 - lattice.evenHeight row ≤ Real.sqrt 2 - 1 / 2)
    (center_above : lattice.evenHeight row ≤ square.center.y) :
    lattice.HasPoint square := by
  have width_at_least_one : 1 ≤ width := width_positive
  obtain ⟨column, contained⟩ := square.contains_topSpacedRow (width - 1)
    fits (left := 1) (by norm_num)
    (by rw [Nat.cast_sub width_at_least_one]; norm_num)
    height_lower center_above
  refine ⟨.inl (row, Fin.cast (Nat.sub_add_cancel width_at_least_one) column), ?_⟩
  simpa [point, add_comm] using contained

lemma top_odd
    {square : PlacedSquare} (fits : square.Fits ((width : ℝ) + 1))
    (row : Fin oddRows)
    (height_lower : (width : ℝ) + 1 - lattice.oddHeight row ≤ Real.sqrt 2 - 1 / 2)
    (center_above : lattice.oddHeight row ≤ square.center.y) :
    lattice.HasPoint square := by
  obtain ⟨column, contained⟩ := square.contains_topSpacedRow width
    fits (left := 1 / 2) (by norm_num) (by linarith) height_lower center_above
  exact ⟨.inr (row, column), by simpa [point, add_comm] using contained⟩

noncomputable def points : Fin (evenRows * width + oddRows * (width + 1)) → Point :=
  fun index => lattice.point ((Fintype.equivFin (Index width evenRows oddRows)).symm
    (Fin.cast (by simp [Index]) index))

theorem lowerBound
    (unavoidable : ∀ square : PlacedSquare, square.StrictFits ((width : ℝ) + 1) →
      lattice.HasPoint square) :
    IsLowerBound (evenRows * width + oddRows * (width + 1) + 1) ((width : ℝ) + 1) := by
  apply lowerBound_succ_of_strict_unavoidable (points := lattice.points)
  intro square strict
  obtain ⟨index, contained⟩ := unavoidable square strict
  refine ⟨Fin.cast (by simp [Index]) ((Fintype.equivFin (Index width evenRows oddRows)) index), ?_⟩
  simpa [points] using contained

end StaggeredLattice

end SquarePackingArchive
