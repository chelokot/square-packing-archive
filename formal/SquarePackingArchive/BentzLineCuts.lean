import SquarePackingArchive.NagamochiGridSections
import SquarePackingArchive.Records.Square7

namespace SquarePackingArchive.Bentz

open Set MeasureTheory

lemma low_point_offset_bound {cosine sine center : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (center_lower : (cosine + sine) / 2 ≤ center)
    (center_upper : center ≤ 2 / 5 + (cosine + sine) / 2) :
    |451 / 500 - center| < (cosine + sine) / 2 - cosine * sine := by
  have product_nonnegative := mul_nonneg cosine_nonnegative sine_nonnegative
  have sum_lower : 1 ≤ cosine + sine := by nlinarith
  have sum_upper : cosine + sine < 10 / 7 := by nlinarith [sq_nonneg (cosine - sine)]
  have interval_product := mul_nonneg (show 0 ≤ cosine + sine - 1 by linarith)
    (show 0 ≤ 10 / 7 - (cosine + sine) by linarith)
  have sum_sub_product : 451 / 500 < cosine + sine - cosine * sine := by nlinarith
  have product_upper : cosine * sine ≤ 1 / 2 := by nlinarith [sq_nonneg (cosine - sine)]
  rw [abs_lt]
  constructor <;> linarith

theorem horizontal_unit_chord_of_low_point
    (square : PlacedSquare) {side : ℝ} {point : Point}
    (fits : square.Fits side) (point_mem : square.Contains point)
    (point_low : point.y ≤ 2 / 5) :
    ∃ intervalStart intervalEnd : ℝ, 1 ≤ intervalEnd - intervalStart ∧
      ∀ horizontal ∈ Ioo intervalStart intervalEnd,
        square.InteriorContains ⟨horizontal, 451 / 500⟩ := by
  let normalized := square.firstQuadrant
  have normalized_fits : normalized.Fits side := (square.firstQuadrant_fits_iff side).2 fits
  have cosine_nonnegative : 0 ≤ normalized.frame.cosine := square.firstQuadrant_cosine_nonnegative
  have sine_nonnegative : 0 ≤ normalized.frame.sine := square.firstQuadrant_sine_nonnegative
  have normalized_mem : normalized.Contains point := (square.firstQuadrant_contains_iff point).2 point_mem
  have center_lower := (normalized.center_bounds normalized_fits).2.2.1
  simp only [frameExtent, abs_of_nonneg cosine_nonnegative, abs_of_nonneg sine_nonnegative] at center_lower
  have center_upper : normalized.center.y ≤ 2 / 5 +
      (normalized.frame.cosine + normalized.frame.sine) / 2 := by
    obtain ⟨localX, localY, horizontal_bound, vertical_bound, point_eq⟩ := normalized_mem
    have vertical_eq := congrArg Point.y point_eq
    dsimp [PlacedSquare.point, Frame.place] at vertical_eq
    have horizontal_lower := (abs_le.1 horizontal_bound).1
    have vertical_lower := (abs_le.1 vertical_bound).1
    nlinarith [mul_nonneg (show 0 ≤ localX + 1 / 2 by linarith) sine_nonnegative,
      mul_nonneg (show 0 ≤ localY + 1 / 2 by linarith) cosine_nonnegative]
  have offset := low_point_offset_bound cosine_nonnegative sine_nonnegative normalized.frame.unit
    center_lower center_upper
  have chord : ∃ intervalStart intervalEnd : ℝ, 1 ≤ intervalEnd - intervalStart ∧
      ∀ horizontal ∈ Ioo intervalStart intervalEnd,
        ![horizontal, (451 / 500 : ℝ)] ∈ normalized.dilatedInteriorRegion 1 := by
    by_cases axis_aligned : normalized.frame.cosine = 0 ∨ normalized.frame.sine = 0
    · have anchor : ![normalized.center.x, (451 / 500 : ℝ)] ∈ normalized.dilatedInteriorRegion 1 := by
        apply normalized.mem_dilatedInteriorRegion_of_inverse_bounds (by norm_num)
        all_goals
          rcases axis_aligned with cosine_zero | sine_zero
          all_goals
            have other_one : normalized.frame.cosine = 1 ∨ normalized.frame.sine = 1 := by
              first
              | right; nlinarith [normalized.frame.unit]
              | left; nlinarith [normalized.frame.unit]
            rcases other_one with cosine_one | sine_one <;>
              simp_all [PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY, Plane.toPoint]
      exact Nagamochi.exists_horizontal_chord_of_axis_aligned normalized (by norm_num)
        cosine_nonnegative sine_nonnegative axis_aligned ⟨_, by simpa using anchor⟩
    · push Not at axis_aligned
      obtain ⟨intervalStart, intervalEnd, length_bound, inside⟩ :=
        Nagamochi.horizontal_chord_longer_than_side_of_offset_bound normalized (factor := 1)
          (by norm_num) (lt_of_le_of_ne cosine_nonnegative axis_aligned.1.symm)
          (lt_of_le_of_ne sine_nonnegative axis_aligned.2.symm) (by simpa using offset)
      exact ⟨intervalStart, intervalEnd, length_bound.le, inside⟩
  obtain ⟨intervalStart, intervalEnd, length_bound, inside⟩ := chord
  refine ⟨intervalStart, intervalEnd, length_bound, ?_⟩
  intro horizontal horizontal_mem
  have normalized_inside := inside horizontal horizontal_mem
  rw [PlacedSquare.dilatedInteriorRegion_one] at normalized_inside
  apply (square.firstQuadrant_interiorContains_iff _).1
  exact (normalized.mem_interiorRegion_iff _).1 normalized_inside

theorem vertical_unit_chord_of_left_point
    (square : PlacedSquare) {side : ℝ} {point : Point}
    (fits : square.Fits side) (point_mem : square.Contains point)
    (point_left : point.x ≤ 2 / 5) :
    ∃ intervalStart intervalEnd : ℝ, 1 ≤ intervalEnd - intervalStart ∧
      ∀ vertical ∈ Ioo intervalStart intervalEnd,
        square.InteriorContains ⟨451 / 500, vertical⟩ := by
  obtain ⟨intervalStart, intervalEnd, length_bound, inside⟩ :=
    horizontal_unit_chord_of_low_point square.swap ((square.swap_fits_iff side).2 fits)
      ((square.swap_contains_iff point).2 point_mem) point_left
  refine ⟨intervalStart, intervalEnd, length_bound, ?_⟩
  intro vertical vertical_mem
  exact (square.interiorContains_swap_iff ⟨451 / 500, vertical⟩).1 (inside vertical vertical_mem)

theorem count_le_side_of_vertical_unit_chords
    {count selectedCount : ℕ} {side line : ℝ} (packing : Packing count side)
    (owners : Fin selectedCount ↪ Fin count)
    (chords : ∀ selected, ∃ intervalStart intervalEnd : ℝ,
      1 ≤ intervalEnd - intervalStart ∧
      ∀ vertical ∈ Ioo intervalStart intervalEnd,
        (packing.squares (owners selected)).InteriorContains ⟨line, vertical⟩) :
    (selectedCount : ℝ) ≤ side := by
  classical
  choose lower upper length_bound inside using chords
  let intervals := fun selected => Ioo (lower selected) (upper selected)
  have intervals_disjoint : (↑(Finset.univ : Finset (Fin selectedCount)) : Set (Fin selectedCount)).PairwiseDisjoint intervals := by
    intro first _ second _ different
    apply Set.disjoint_left.2
    intro vertical first_mem second_mem
    exact packing.disjoint (owners first) (owners second) (fun same => different (owners.injective same))
      ⟨line, vertical⟩ ⟨inside first vertical first_mem, inside second vertical second_mem⟩
  have union_subset : (⋃ selected ∈ (Finset.univ : Finset (Fin selectedCount)), intervals selected) ⊆ Icc 0 side := by
    intro vertical vertical_mem
    obtain ⟨selected, _, selected_mem⟩ := Set.mem_iUnion₂.1 vertical_mem
    have square_mem := inside selected vertical selected_mem
    obtain ⟨localX, localY, horizontal_bound, vertical_bound, equality⟩ := square_mem
    have bounds := packing.fits (owners selected)
      ⟨localX, localY, horizontal_bound.le, vertical_bound.le, equality⟩
    exact ⟨bounds.2.2.1, bounds.2.2.2⟩
  have sum_volume : ∑ selected, volume (intervals selected) ≤ volume (Icc (0 : ℝ) side) := by
    rw [← measure_biUnion_finset intervals_disjoint (fun _ _ => measurableSet_Ioo)]
    exact measure_mono union_subset
  have count_bound : (selectedCount : ENNReal) ≤ ∑ selected, volume (intervals selected) := by
    calc
      (selectedCount : ENNReal) = ∑ _selected : Fin selectedCount, (1 : ENNReal) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun selected _ => by
        rw [show volume (intervals selected) = ENNReal.ofReal (upper selected - lower selected) by
          exact Real.volume_Ioo]
        exact_mod_cast (ENNReal.ofReal_le_ofReal (length_bound selected)))
  have bound := count_bound.trans sum_volume
  rw [Real.volume_Icc, sub_zero] at bound
  have real_bound := ENNReal.toReal_mono (by simp : ENNReal.ofReal side ≠ ⊤) bound
  simpa [ENNReal.toReal_ofReal packing.side_nonnegative] using real_bound

theorem count_le_side_of_left_points
    {count selectedCount : ℕ} {side : ℝ} (packing : Packing count side)
    (owners : Fin selectedCount ↪ Fin count)
    (points : Fin selectedCount → Point)
    (points_inside : ∀ selected, (packing.squares (owners selected)).Contains (points selected))
    (points_left : ∀ selected, (points selected).x ≤ 2 / 5) :
    (selectedCount : ℝ) ≤ side := by
  apply count_le_side_of_vertical_unit_chords packing owners (line := 451 / 500)
  intro selected
  exact vertical_unit_chord_of_left_point _ (packing.fits (owners selected))
    (points_inside selected) (points_left selected)

end SquarePackingArchive.Bentz
