import SquarePackingArchive.BentzLineCuts
import SquarePackingArchive.PackingSymmetry

namespace SquarePackingArchive

lemma PlacedSquare.interiorContains_vertical_between
    (square : PlacedSquare) {line lower middle upper : ℝ}
    (lower_inside : square.InteriorContains ⟨line, lower⟩)
    (upper_inside : square.InteriorContains ⟨line, upper⟩)
    (lower_bound : lower ≤ middle) (upper_bound : middle ≤ upper) :
    square.InteriorContains ⟨line, middle⟩ := by
  rcases lt_or_eq_of_le lower_bound with lower_lt | lower_eq
  · rcases lt_or_eq_of_le upper_bound with upper_lt | upper_eq
    · exact (square.mem_interiorRegion_iff ![line, middle]).1
        (vertical_openSegment_subset_of_convex square.convex_interiorRegion
          (lower_lt.trans upper_lt)
          ((square.mem_interiorRegion_iff _).2 lower_inside)
          ((square.mem_interiorRegion_iff _).2 upper_inside)
          middle ⟨lower_lt, upper_lt⟩)
    · simpa [upper_eq] using upper_inside
  · simpa [← lower_eq] using lower_inside

lemma PlacedSquare.exists_lower_vertical_interior
    (square : PlacedSquare) {line height : ℝ}
    (inside : square.InteriorContains ⟨line, height⟩) :
    ∃ lower, lower < height ∧ square.InteriorContains ⟨line, lower⟩ := by
  let verticalSection : Set ℝ := (fun vertical : ℝ => (![line, vertical] : Plane)) ⁻¹' square.interiorRegion
  have section_open : IsOpen verticalSection := square.isOpen_interiorRegion.preimage (by fun_prop)
  have height_mem : height ∈ verticalSection := (square.mem_interiorRegion_iff _).2 inside
  obtain ⟨lower, upper, bounds, subset⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 (section_open.mem_nhds height_mem)
  refine ⟨(lower + height) / 2, by linarith [bounds.1], ?_⟩
  exact (square.mem_interiorRegion_iff _).1 (subset (by
    constructor <;> linarith [bounds.1, bounds.2]))

namespace Bentz

theorem count_lt_cutoff_of_unit_chords_below
    {count selectedCount : ℕ} {side line cutoff : ℝ} (packing : Packing count side)
    (owners : Fin selectedCount ↪ Fin count) (target : Fin count)
    (target_different : ∀ selected, owners selected ≠ target)
    (anchors : Fin selectedCount → ℝ)
    (anchor_inside : ∀ selected, (packing.squares (owners selected)).InteriorContains ⟨line, anchors selected⟩)
    (anchors_below : ∀ selected, anchors selected < cutoff)
    (chords : ∀ selected, ∃ intervalStart intervalEnd : ℝ,
      1 ≤ intervalEnd - intervalStart ∧
      ∀ vertical ∈ Set.Ioo intervalStart intervalEnd,
        (packing.squares (owners selected)).InteriorContains ⟨line, vertical⟩)
    (target_inside : (packing.squares target).InteriorContains ⟨line, cutoff⟩) :
    (selectedCount : ℝ) < cutoff := by
  classical
  obtain ⟨threshold, threshold_lt, threshold_inside⟩ :=
    (packing.squares target).exists_lower_vertical_interior target_inside
  have threshold_nonnegative : 0 ≤ threshold := by
    obtain ⟨localX, localY, horizontal, vertical, equality⟩ := threshold_inside
    exact (packing.fits target ⟨localX, localY, horizontal.le, vertical.le, equality⟩).2.2.1
  have all_below (selected : Fin selectedCount) (vertical : ℝ)
      (inside : (packing.squares (owners selected)).InteriorContains ⟨line, vertical⟩) :
      vertical < threshold := by
    have below_cutoff : vertical < cutoff := by
      by_contra! above
      exact packing.disjoint (owners selected) target (target_different selected) ⟨line, cutoff⟩
        ⟨(packing.squares (owners selected)).interiorContains_vertical_between
          (anchor_inside selected) inside (anchors_below selected).le above, target_inside⟩
    by_contra! above_threshold
    exact packing.disjoint (owners selected) target (target_different selected) ⟨line, vertical⟩
      ⟨inside, (packing.squares target).interiorContains_vertical_between
        threshold_inside target_inside above_threshold below_cutoff.le⟩
  choose lower upper length_bound inside using chords
  have intervals_disjoint : (↑(Finset.univ : Finset (Fin selectedCount)) : Set (Fin selectedCount)).PairwiseDisjoint
      (fun selected => Set.Ioo (lower selected) (upper selected)) := by
    intro first _ second _ different
    apply Set.disjoint_left.2
    intro vertical first_mem second_mem
    exact packing.disjoint (owners first) (owners second) (fun same => different (owners.injective same))
      ⟨line, vertical⟩ ⟨inside first vertical first_mem, inside second vertical second_mem⟩
  have union_subset : (⋃ selected ∈ (Finset.univ : Finset (Fin selectedCount)),
      Set.Ioo (lower selected) (upper selected)) ⊆ Set.Icc 0 threshold := by
    intro vertical vertical_mem
    obtain ⟨selected, _, selected_mem⟩ := Set.mem_iUnion₂.1 vertical_mem
    have square_inside := inside selected vertical selected_mem
    refine ⟨?_, (all_below selected vertical square_inside).le⟩
    obtain ⟨localX, localY, horizontal_bound, vertical_bound, equality⟩ := square_inside
    exact (packing.fits (owners selected)
      ⟨localX, localY, horizontal_bound.le, vertical_bound.le, equality⟩).2.2.1
  exact (count_le_of_disjoint_unit_intervals lower upper threshold_nonnegative
    length_bound intervals_disjoint union_subset).trans_lt threshold_lt

theorem count_lt_remaining_of_unit_chords_above
    {count selectedCount : ℕ} {side line cutoff : ℝ} (packing : Packing count side)
    (owners : Fin selectedCount ↪ Fin count) (target : Fin count)
    (target_different : ∀ selected, owners selected ≠ target)
    (anchors : Fin selectedCount → ℝ)
    (anchor_inside : ∀ selected, (packing.squares (owners selected)).InteriorContains ⟨line, anchors selected⟩)
    (anchors_above : ∀ selected, cutoff < anchors selected)
    (chords : ∀ selected, ∃ intervalStart intervalEnd : ℝ,
      1 ≤ intervalEnd - intervalStart ∧
      ∀ vertical ∈ Set.Ioo intervalStart intervalEnd,
        (packing.squares (owners selected)).InteriorContains ⟨line, vertical⟩)
    (target_inside : (packing.squares target).InteriorContains ⟨line, cutoff⟩) :
    (selectedCount : ℝ) < side - cutoff := by
  apply count_lt_cutoff_of_unit_chords_below packing.reflectY owners target target_different
    (fun selected => side - anchors selected)
  · intro selected
    exact ((packing.squares (owners selected)).interiorContains_reflectY_iff side
      ⟨line, anchors selected⟩).2 (anchor_inside selected)
  · intro selected
    linarith [anchors_above selected]
  · intro selected
    obtain ⟨lower, upper, length_bound, inside⟩ := chords selected
    refine ⟨side - upper, side - lower, by linarith, ?_⟩
    intro vertical vertical_mem
    have original := inside (side - vertical) (by
      constructor <;> linarith [vertical_mem.1, vertical_mem.2])
    have reflected := ((packing.squares (owners selected)).interiorContains_reflectY_iff side
      ⟨line, side - vertical⟩).2 original
    simpa [Point.reflectY] using reflected
  · exact ((packing.squares target).interiorContains_reflectY_iff side ⟨line, cutoff⟩).2 target_inside

end Bentz

end SquarePackingArchive
