import SquarePackingArchive.NagamochiGlobalBadSquare
import SquarePackingArchive.NagamochiPackingConstraints

namespace SquarePackingArchive

open Set

noncomputable def Packing.badSquares
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side)
    (size : ℕ) (factor : ℝ) : Finset (Fin squareCount) := by
  classical
  exact Finset.univ.filter fun index =>
    NagamochiResource.measure size ((packing.squares index).dilatedInteriorRegion factor) ≤ 1

theorem Packing.badSquares_corner_embedding
    {squareCount size : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size) :
    ∃ assigned : packing.badSquares size factor → NagamochiResource.cornerPointKinds,
      Function.Injective assigned ∧ ∀ origin,
        NagamochiResource.cornerPoint size (assigned origin).val ∈
          (packing.squares origin.val).dilatedInteriorRegion factor := by
  classical
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have side_bound : side ≤ (size : ℝ) / factor := by
    rw [le_div_iff₀ factor_positive]
    nlinarith
  have assigned_corner_exists (index : packing.badSquares size factor) :
      ∃ kind, NagamochiResource.cornerPoint size kind ∈
        (packing.squares index.val).dilatedInteriorRegion factor := by
    have fits : (packing.squares index.val).Fits ((size : ℝ) / factor) := by
      intro point contained
      have bounds := packing.fits index.val contained
      exact ⟨bounds.1, bounds.2.1.trans side_bound, bounds.2.2.1, bounds.2.2.2.trans side_bound⟩
    have bad : NagamochiResource.measure size ((packing.squares index.val).dilatedInteriorRegion factor) ≤ 1 := by
      simpa [Packing.badSquares] using index.property
    exact (Nagamochi.bad_square_has_exactly_one_corner_and_no_edge_points
      (packing.squares index.val) fits size_lower factor_gt_one factor_at_most
      ((packing.squares index.val).dilatedInteriorRegion_subset_containerRegion
        (packing.fits index.val) factor_positive.le scaled_side_le) bad).1.exists
  let assigned : packing.badSquares size factor → NagamochiResource.cornerPointKinds :=
    fun index => ⟨(assigned_corner_exists index).choose, NagamochiResource.mem_cornerPointKinds _⟩
  have assigned_mem (index : packing.badSquares size factor) :
      NagamochiResource.cornerPoint size (assigned index).val ∈
        (packing.squares index.val).dilatedInteriorRegion factor :=
    (assigned_corner_exists index).choose_spec
  have injective : Function.Injective assigned := by
    intro first second same
    have same_kind := congrArg Subtype.val same
    apply Subtype.ext
    apply packing.dilatedPoint_owner_unique factor_positive (assigned_mem first)
    rw [same_kind]
    exact assigned_mem second
  exact ⟨assigned, injective, assigned_mem⟩

theorem Packing.badSquares_card_le_eight
    {squareCount size : ℕ} {side factor : ℝ} (packing : Packing squareCount side)
    (size_lower : 4 ≤ size) (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100) (scaled_side_le : factor * side ≤ size) :
    (packing.badSquares size factor).card ≤ 8 := by
  obtain ⟨_assigned, injective, _owns_corner⟩ := packing.badSquares_corner_embedding
    size_lower factor_gt_one factor_at_most scaled_side_le
  have cardinal_bound := Finset.card_le_card_of_injective injective
  exact cardinal_bound.trans_eq (by decide : NagamochiResource.cornerPointKinds.card = 8)

end SquarePackingArchive
