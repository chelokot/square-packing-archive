import SquarePackingArchive.NagamochiChainContinuation
import SquarePackingArchive.NagamochiPackingConstraints
import SquarePackingArchive.BoundaryUnavoidable

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma axis_aligned_bottom_owner_contains_band
    (square : PlacedSquare) {side factor horizontal height : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (axis_aligned : square.frame.cosine = 0 ∨ square.frame.sine = 0)
    (anchor : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (height_mem : height ∈ Icc (9 / 10 : ℝ) 1) :
    ![horizontal, height] ∈ square.dilatedInteriorRegion factor := by
  have factor_positive : 0 < factor := by linarith
  have bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive anchor
  rw [abs_lt, abs_lt] at bounds
  have bottom := (square.center_bounds fits).2.2.1
  simp only [frameExtent, abs_of_nonneg cosine_nonnegative,
    abs_of_nonneg sine_nonnegative] at bottom
  have scaled_bottom := mul_le_mul_of_nonneg_left bottom factor_positive.le
  have unit := square.frame.unit
  apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
  all_goals rw [abs_lt]
  all_goals rcases axis_aligned with cosine_zero | sine_zero
  all_goals dsimp [PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY, Plane.toPoint] at bounds ⊢
  · have sine_one : square.frame.sine = 1 := by nlinarith
    simp only [cosine_zero, sine_one] at bounds scaled_bottom ⊢
    constructor <;> nlinarith [height_mem.1, height_mem.2]
  · have cosine_one : square.frame.cosine = 1 := by nlinarith
    simpa [sine_zero, cosine_one] using bounds.1
  · have sine_one : square.frame.sine = 1 := by nlinarith
    simpa [cosine_zero, sine_one] using bounds.2
  · have cosine_one : square.frame.cosine = 1 := by nlinarith
    simp only [sine_zero, cosine_one] at bounds scaled_bottom ⊢
    constructor <;> nlinarith [height_mem.1, height_mem.2]

lemma dilated_region_horizontal_lt
    (square : PlacedSquare) {side factor horizontal height limit : ℝ}
    (fits : square.Fits side) (factor_positive : 0 < factor)
    (scaled_side_le : factor * side ≤ limit)
    (contained : ![horizontal, height] ∈ square.dilatedInteriorRegion factor) :
    horizontal < limit := by
  obtain ⟨point, point_mem, equality⟩ := contained
  have bounds := square.interiorContains_strict_bounds fits
    ((square.mem_interiorRegion_iff point).1 point_mem)
  have coordinate := congrFun equality 0
  simp only [dilatePlane, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] at coordinate
  have strict := mul_lt_mul_of_pos_left bounds.2.1 factor_positive
  change factor * point 0 < factor * side at strict
  linarith

lemma bottom_marked_point_has_owner
    {size coordinate : ℕ} {side factor : ℝ} (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (coordinate_mem : coordinate ∈ Finset.Icc 1 (size - 1)) :
    ∃ owner, ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈
      (packing.squares owner).dilatedInteriorRegion factor := by
  by_cases first : coordinate = 1
  · simpa [first, NagamochiResource.cornerPoint] using
      packing.squareMinusTwo_cornerPoint_has_owner size_lower factor_gt_one factor_at_most
        scaled_side_le .leftBottom
  by_cases last : coordinate = size - 1
  · have cast_last : (coordinate : ℝ) = (size : ℝ) - 1 := by
      rw [last, Nat.cast_sub (by omega)]
      norm_num
    simpa [cast_last, NagamochiResource.cornerPoint] using
      packing.squareMinusTwo_cornerPoint_has_owner size_lower factor_gt_one factor_at_most
        scaled_side_le .rightBottom
  · have interior_mem : coordinate ∈ Finset.Icc 2 (size - 2) := by
      simp only [Finset.mem_Icc] at coordinate_mem ⊢
      omega
    exact packing.squareMinusTwo_edgePoint_has_owner size_lower factor_gt_one factor_at_most
      scaled_side_le interior_mem .bottom

def BoundaryChainTerminal (square : PlacedSquare) (factor horizontal height : ℝ) : Prop :=
  0 < square.firstQuadrant.frame.cosine ∧
  0 < square.firstQuadrant.frame.sine ∧
  ((factor / 2 ≤ square.firstQuadrant.dilatedLocalY factor ⟨horizontal, height⟩ ∧
    factor * square.center.y + factor *
      (square.firstQuadrant.frame.sine - square.firstQuadrant.frame.cosine) / 2 < 9 / 10) ∨
   (factor / 2 ≤ square.firstQuadrant.dilatedLocalX factor ⟨horizontal, height⟩ ∧
    factor * square.center.y + factor *
      (square.firstQuadrant.frame.cosine - square.firstQuadrant.frame.sine) / 2 < 9 / 10))

theorem chain_owner_continues_or_stops_any_frame
    (square : PlacedSquare) {previousRegion : Set Plane} {side factor horizontal height : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (previous_convex : Convex ℝ previousRegion)
    (regions_disjoint : Disjoint previousRegion (square.dilatedInteriorRegion factor))
    (previous_anchor : ![horizontal - 1, (9 / 10 : ℝ)] ∈ previousRegion)
    (previous_crossing : ![horizontal, height] ∈ previousRegion)
    (anchor : ![horizontal, (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (height_mem : height ∈ Icc (9 / 10 : ℝ) 1) :
    (∃ nextHeight ∈ Icc (9 / 10 : ℝ) height,
      ![horizontal + 1, nextHeight] ∈ square.dilatedInteriorRegion factor) ∨
    BoundaryChainTerminal square factor horizontal height := by
  have factor_positive : 0 < factor := by linarith
  have canonical_fits : square.firstQuadrant.Fits side := by simpa using fits
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq factor_positive
  have canonical_anchor : ![horizontal, (9 / 10 : ℝ)] ∈
      square.firstQuadrant.dilatedInteriorRegion factor := by rwa [region_eq]
  have canonical_disjoint : Disjoint previousRegion
      (square.firstQuadrant.dilatedInteriorRegion factor) := by rwa [region_eq]
  have cosine_positive : 0 < square.firstQuadrant.frame.cosine := by
    by_contra! not_positive
    have zero_cosine := le_antisymm not_positive square.firstQuadrant_cosine_nonnegative
    have crossing := axis_aligned_bottom_owner_contains_band square.firstQuadrant canonical_fits
      factor_gt_one square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
      (Or.inl zero_cosine) canonical_anchor height_mem
    exact Set.disjoint_left.mp canonical_disjoint previous_crossing crossing
  have sine_positive : 0 < square.firstQuadrant.frame.sine := by
    by_contra! not_positive
    have zero_sine := le_antisymm not_positive square.firstQuadrant_sine_nonnegative
    have crossing := axis_aligned_bottom_owner_contains_band square.firstQuadrant canonical_fits
      factor_gt_one square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
      (Or.inr zero_sine) canonical_anchor height_mem
    exact Set.disjoint_left.mp canonical_disjoint previous_crossing crossing
  rcases chain_owner_continues_or_stops square.firstQuadrant canonical_fits factor_gt_one
    cosine_positive sine_positive previous_convex canonical_disjoint previous_anchor
    previous_crossing canonical_anchor height_mem with continuation | terminal
  · exact Or.inl (by simpa [region_eq] using continuation)
  · exact Or.inr ⟨cosine_positive, sine_positive, by simpa using terminal⟩

theorem finite_bottom_owner_chain_reaches_terminal_or_shared_owner
    {size : ℕ} {side factor initialHeight : ℝ}
    (packing : Packing (size * size - 2) side)
    (size_lower : 3 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size)
    (initial_owner : Fin (size * size - 2))
    (initial_anchor : ![(1 : ℝ), (9 / 10 : ℝ)] ∈
      (packing.squares initial_owner).dilatedInteriorRegion factor)
    (initial_crossing : ![(2 : ℝ), initialHeight] ∈
      (packing.squares initial_owner).dilatedInteriorRegion factor)
    (initial_height_mem : initialHeight ∈ Icc (9 / 10 : ℝ) 1) :
    (∃ coordinate ∈ Finset.Icc 2 (size - 1), ∃ owner height,
      height ∈ Icc (9 / 10 : ℝ) initialHeight ∧
      ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈
        (packing.squares owner).dilatedInteriorRegion factor ∧
      BoundaryChainTerminal (packing.squares owner) factor coordinate height) ∨
    (∃ coordinate ∈ Finset.Icc 1 (size - 2), ∃ owner,
      ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈
        (packing.squares owner).dilatedInteriorRegion factor ∧
      ![(coordinate : ℝ) + 1, (9 / 10 : ℝ)] ∈
        (packing.squares owner).dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := by linarith
  let conclusion :=
    (∃ coordinate ∈ Finset.Icc 2 (size - 1), ∃ owner height,
      height ∈ Icc (9 / 10 : ℝ) initialHeight ∧
      ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈
        (packing.squares owner).dilatedInteriorRegion factor ∧
      BoundaryChainTerminal (packing.squares owner) factor coordinate height) ∨
    (∃ coordinate ∈ Finset.Icc 1 (size - 2), ∃ owner,
      ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈
        (packing.squares owner).dilatedInteriorRegion factor ∧
      ![(coordinate : ℝ) + 1, (9 / 10 : ℝ)] ∈
        (packing.squares owner).dilatedInteriorRegion factor)
  have descend : ∀ fuel coordinate : ℕ, coordinate + fuel = size → 2 ≤ coordinate →
      ∀ (previous : Fin (size * size - 2)) (height : ℝ),
      ![(coordinate : ℝ) - 1, (9 / 10 : ℝ)] ∈
        (packing.squares previous).dilatedInteriorRegion factor →
      ![(coordinate : ℝ), height] ∈
        (packing.squares previous).dilatedInteriorRegion factor →
      height ∈ Icc (9 / 10 : ℝ) initialHeight → conclusion := by
    intro fuel
    induction fuel with
    | zero =>
      intro coordinate endpoint coordinate_lower previous height previous_anchor previous_crossing height_mem
      have beyond := dilated_region_horizontal_lt (packing.squares previous)
        (packing.fits previous) factor_positive scaled_side_le previous_crossing
      have coordinate_eq : coordinate = size := by omega
      rw [coordinate_eq] at beyond
      exact False.elim (lt_irrefl _ beyond)
    | succ fuel induction_hypothesis =>
      intro coordinate endpoint coordinate_lower previous height previous_anchor previous_crossing height_mem
      have coordinate_upper : coordinate ≤ size - 1 := by omega
      obtain ⟨owner, anchor⟩ := bottom_marked_point_has_owner packing size_lower factor_gt_one
        factor_at_most scaled_side_le
        (show coordinate ∈ Finset.Icc 1 (size - 1) by
          simp only [Finset.mem_Icc]
          omega)
      by_cases same_owner : previous = owner
      · apply Or.inr
        refine ⟨coordinate - 1, ?_, owner, ?_, ?_⟩
        · simp only [Finset.mem_Icc]
          omega
        · rw [Nat.cast_sub (by omega : 1 ≤ coordinate), Nat.cast_one]
          simpa [same_owner] using previous_anchor
        · simpa [Nat.cast_sub (by omega : 1 ≤ coordinate)] using anchor
      · have disjoint_regions := PlacedSquare.disjoint_dilatedInteriorRegion
          (packing.disjoint previous owner same_owner) factor_positive.ne'
        rcases chain_owner_continues_or_stops_any_frame (packing.squares owner)
          (packing.fits owner) factor_gt_one
          ((packing.squares previous).convex_dilatedInteriorRegion factor)
          disjoint_regions previous_anchor previous_crossing anchor
          ⟨height_mem.1, height_mem.2.trans initial_height_mem.2⟩ with continuation | terminal
        · obtain ⟨nextHeight, next_height_mem, next_crossing⟩ := continuation
          apply induction_hypothesis (coordinate + 1) (by omega) (by omega) owner nextHeight
          · simpa using anchor
          · simpa only [Nat.cast_add, Nat.cast_one] using next_crossing
          · exact ⟨next_height_mem.1, next_height_mem.2.trans height_mem.2⟩
        · exact Or.inl ⟨coordinate, by simp only [Finset.mem_Icc]; omega,
            owner, height, height_mem, anchor, terminal⟩
  apply descend (size - 2) 2 (by omega) (by omega) initial_owner initialHeight
  · norm_num
    exact initial_anchor
  · simpa using initial_crossing
  · exact ⟨initial_height_mem.1, le_rfl⟩

end SquarePackingArchive.Nagamochi
