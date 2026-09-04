import Mathlib.Algebra.Order.Round
import SquarePackingArchive.Unavoidable

namespace SquarePackingArchive

def PlacedSquare.AxisAligned (square : PlacedSquare) : Prop :=
  square.frame.cosine = 0 ∨ square.frame.sine = 0

lemma PlacedSquare.AxisAligned.frame_cases {square : PlacedSquare}
    (aligned : square.AxisAligned) :
    (square.frame.cosine = 0 ∧ (square.frame.sine = 1 ∨ square.frame.sine = -1)) ∨
      (square.frame.sine = 0 ∧ (square.frame.cosine = 1 ∨ square.frame.cosine = -1)) := by
  rcases aligned with cosine_zero | sine_zero
  · exact Or.inl ⟨cosine_zero, sq_eq_one_iff.mp (by nlinarith [square.frame.unit])⟩
  · exact Or.inr ⟨sine_zero, sq_eq_one_iff.mp (by nlinarith [square.frame.unit])⟩

lemma PlacedSquare.AxisAligned.contains_iff {square : PlacedSquare}
    (aligned : square.AxisAligned) (point : Point) :
    square.Contains point ↔
      |point.x - square.center.x| ≤ 1 / 2 ∧ |point.y - square.center.y| ≤ 1 / 2 := by
  rw [square.contains_iff_localCoordinates]
  rcases aligned.frame_cases with ⟨cosine_zero, sine_one | sine_neg_one⟩ |
    ⟨sine_zero, cosine_one | cosine_neg_one⟩ <;>
    simp_all [PlacedSquare.localX, PlacedSquare.localY, and_comm, abs_sub_comm]

lemma PlacedSquare.AxisAligned.interiorContains {square : PlacedSquare}
    (aligned : square.AxisAligned) {point : Point}
    (horizontal : |point.x - square.center.x| < 1 / 2)
    (vertical : |point.y - square.center.y| < 1 / 2) :
    square.InteriorContains point := by
  refine ⟨square.localX point, square.localY point, ?_, ?_, ?_⟩
  · rcases aligned.frame_cases with ⟨cosine_zero, sine_one | sine_neg_one⟩ |
      ⟨sine_zero, cosine_one | cosine_neg_one⟩ <;>
      simp_all [PlacedSquare.localX, abs_sub_comm]
  · rcases aligned.frame_cases with ⟨cosine_zero, sine_one | sine_neg_one⟩ |
      ⟨sine_zero, cosine_one | cosine_neg_one⟩ <;>
      simp_all [PlacedSquare.localY, abs_sub_comm]
  · rw [Point.mk.injEq]
    constructor <;> dsimp [PlacedSquare.localX, PlacedSquare.localY,
      PlacedSquare.point, Frame.place]
    · linear_combination -(point.x - square.center.x) * square.frame.unit
    · linear_combination -(point.y - square.center.y) * square.frame.unit

lemma PlacedSquare.AxisAligned.center_bounds {square : PlacedSquare} {side : ℝ}
    (aligned : square.AxisAligned) (fits : square.Fits side) :
    (1 / 2 ≤ square.center.x ∧ square.center.x ≤ side - 1 / 2) ∧
      (1 / 2 ≤ square.center.y ∧ square.center.y ≤ side - 1 / 2) := by
  have lower := fits ((aligned.contains_iff
    ⟨square.center.x - 1 / 2, square.center.y - 1 / 2⟩).2 (by norm_num))
  have upper := fits ((aligned.contains_iff
    ⟨square.center.x + 1 / 2, square.center.y + 1 / 2⟩).2 (by norm_num))
  dsimp [Container.Contains] at lower upper
  exact ⟨⟨by linarith [lower.1], by linarith [upper.2.1]⟩,
    ⟨by linarith [lower.2.2.1], by linarith [upper.2.2.2]⟩⟩

lemma exists_nearby_interior_grid_coordinate {size : ℕ} {side coordinate : ℝ}
    (side_positive : 0 < side) (side_lt_size : side < size)
    (coordinate_lower : 1 / 2 ≤ coordinate)
    (coordinate_upper : coordinate ≤ side - 1 / 2) :
    ∃ index : Fin (size - 1),
      |((index.val + 1 : ℕ) : ℝ) * (side / size) - coordinate| < 1 / 2 := by
  have size_positive_real : 0 < (size : ℝ) := side_positive.trans side_lt_size
  have size_positive : 0 < size := by exact_mod_cast size_positive_real
  let spacing := side / size
  have spacing_positive : 0 < spacing := div_pos side_positive size_positive_real
  have spacing_lt_one : spacing < 1 := (div_lt_one size_positive_real).2 side_lt_size
  have spacing_mul_size : spacing * size = side := by
    dsimp [spacing]
    field_simp
  let nearest := round (coordinate / spacing)
  have nearest_distance := abs_sub_round (coordinate / spacing)
  change |coordinate / spacing - (nearest : ℝ)| ≤ 1 / 2 at nearest_distance
  have distance_bound : |coordinate - (nearest : ℝ) * spacing| ≤ spacing / 2 := by
    have multiplied := mul_le_mul_of_nonneg_right nearest_distance spacing_positive.le
    have identity : (coordinate / spacing - (nearest : ℝ)) * spacing =
        coordinate - (nearest : ℝ) * spacing := by field_simp
    calc
      _ = |(coordinate / spacing - (nearest : ℝ)) * spacing| := by rw [identity]
      _ = |coordinate / spacing - (nearest : ℝ)| * spacing := by
        rw [abs_mul, abs_of_pos spacing_positive]
      _ ≤ 1 / 2 * spacing := multiplied
      _ = spacing / 2 := by ring
  have distance_bounds := abs_le.mp distance_bound
  have nearest_positive_real : 0 < (nearest : ℝ) := by
    nlinarith
  have nearest_below_size_real : (nearest : ℝ) < size := by
    nlinarith
  have nearest_positive : 0 < nearest := by exact_mod_cast nearest_positive_real
  have nearest_below_size : nearest < size := by exact_mod_cast nearest_below_size_real
  let index : Fin (size - 1) := ⟨nearest.toNat - 1, by omega⟩
  refine ⟨index, ?_⟩
  have index_identity : ((index.val + 1 : ℕ) : ℝ) = nearest := by
    have integer_identity : (index.val + 1 : ℕ) = nearest.toNat := by dsimp [index]; omega
    rw [integer_identity]
    exact_mod_cast Int.toNat_of_nonneg nearest_positive.le
  rw [index_identity, abs_sub_comm]
  exact distance_bound.trans_lt (by linarith)

noncomputable def interiorGridPoint (size : ℕ) (side : ℝ)
    (index : Fin (size - 1) × Fin (size - 1)) : Point :=
  ⟨((index.1.val + 1 : ℕ) : ℝ) * (side / size),
    ((index.2.val + 1 : ℕ) : ℝ) * (side / size)⟩

theorem PlacedSquare.AxisAligned.contains_interiorGridPoint
    {square : PlacedSquare} {size : ℕ} {side : ℝ}
    (aligned : square.AxisAligned) (fits : square.Fits side)
    (side_positive : 0 < side) (side_lt_size : side < size) :
    ∃ index, square.InteriorContains (interiorGridPoint size side index) := by
  obtain ⟨horizontal_bounds, vertical_bounds⟩ := aligned.center_bounds fits
  obtain ⟨column, horizontal_close⟩ := exists_nearby_interior_grid_coordinate
    side_positive side_lt_size horizontal_bounds.1 horizontal_bounds.2
  obtain ⟨row, vertical_close⟩ := exists_nearby_interior_grid_coordinate
    side_positive side_lt_size vertical_bounds.1 vertical_bounds.2
  exact ⟨(column, row), aligned.interiorContains horizontal_close vertical_close⟩

open scoped Classical in
theorem Packing.covered_square_count_le_point_count
    {squareCount : ℕ} {side : ℝ} {PointIndex : Type*} [Fintype PointIndex]
    (packing : Packing squareCount side) (points : PointIndex → Point) :
    Fintype.card {squareIndex : Fin squareCount //
      ∃ pointIndex, (packing.squares squareIndex).InteriorContains (points pointIndex)} ≤
      Fintype.card PointIndex := by
  classical
  let assignedPoint : {squareIndex : Fin squareCount //
      ∃ pointIndex, (packing.squares squareIndex).InteriorContains (points pointIndex)} →
      PointIndex := fun squareIndex => squareIndex.property.choose
  apply Fintype.card_le_of_injective assignedPoint
  intro left right same_point
  apply Subtype.ext
  by_contra different
  apply packing.disjoint left.val right.val different (points (assignedPoint left))
  exact ⟨left.property.choose_spec, by
    rw [same_point]
    exact right.property.choose_spec⟩

noncomputable def Packing.gridAvoidingSquares
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side) (size : ℕ) :
    Finset (Fin squareCount) := by
  classical
  exact Finset.univ.filter fun squareIndex =>
    ¬ ∃ index, (packing.squares squareIndex).InteriorContains (interiorGridPoint size side index)

noncomputable def Packing.tiltedSquares
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side) :
    Finset (Fin squareCount) := by
  classical
  exact Finset.univ.filter fun squareIndex => ¬ (packing.squares squareIndex).AxisAligned

theorem Packing.gridAvoidingSquares_card_lower_bound
    {squareCount size : ℕ} {side : ℝ} (packing : Packing squareCount side) :
    squareCount - (size - 1) * (size - 1) ≤ (packing.gridAvoidingSquares size).card := by
  classical
  have covered_bound := packing.covered_square_count_le_point_count (interiorGridPoint size side)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype] at covered_bound
  have partition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin squareCount)))
    (fun squareIndex => ∃ index,
      (packing.squares squareIndex).InteriorContains (interiorGridPoint size side index))
  simp only [Finset.card_univ, Fintype.card_fin] at partition
  unfold Packing.gridAvoidingSquares
  omega

theorem Packing.gridAvoidingSquares_subset_tiltedSquares
    {squareCount size : ℕ} {side : ℝ} (packing : Packing squareCount side)
    (side_positive : 0 < side) (side_lt_size : side < size) :
    packing.gridAvoidingSquares size ⊆ packing.tiltedSquares := by
  classical
  intro squareIndex avoids_grid
  simp only [Packing.gridAvoidingSquares, Finset.mem_filter, Finset.mem_univ,
    true_and] at avoids_grid
  simp only [Packing.tiltedSquares, Finset.mem_filter, Finset.mem_univ, true_and]
  intro aligned
  exact avoids_grid (aligned.contains_interiorGridPoint
    (packing.fits squareIndex) side_positive side_lt_size)

theorem Packing.tiltedSquares_card_lower_bound
    {squareCount size : ℕ} {side : ℝ} (packing : Packing squareCount side)
    (squareCount_positive : 0 < squareCount) (side_lt_size : side < size) :
    squareCount - (size - 1) * (size - 1) ≤ packing.tiltedSquares.card := by
  exact packing.gridAvoidingSquares_card_lower_bound.trans
    (Finset.card_le_card (packing.gridAvoidingSquares_subset_tiltedSquares
      (packing.side_positive squareCount_positive) side_lt_size))

theorem Packing.sixtyTwo_requires_thirteen_tilted
    {side : ℝ} (packing : Packing 62 side) (side_lt_eight : side < 8) :
    13 ≤ packing.tiltedSquares.card := by
  have bound := packing.tiltedSquares_card_lower_bound
    (size := 8) (by omega) (by exact_mod_cast side_lt_eight)
  norm_num at bound
  exact bound

theorem Packing.squareMinusTwo_requires_many_tilted
    {size : ℕ} {side : ℝ} (packing : Packing (size * size - 2) side)
    (size_at_least_two : 2 ≤ size) (side_lt_size : side < size) :
    2 * size - 3 ≤ packing.tiltedSquares.card := by
  have square_size_lower : 4 ≤ size * size :=
    Nat.mul_le_mul size_at_least_two size_at_least_two
  have bound := packing.tiltedSquares_card_lower_bound (by omega) side_lt_size
  have size_identity : size - 1 + 1 = size := by omega
  have expansion : (size - 1) * (size - 1) + 2 * size = size * size + 1 := by
    nlinarith
  omega

end SquarePackingArchive
