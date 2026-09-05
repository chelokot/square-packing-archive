import SquarePackingArchive.StromquistStepTwoCover
import SquarePackingArchive.StromquistTenCover
import SquarePackingArchive.StromquistStepThree
import SquarePackingArchive.StromquistStepFourCover
import SquarePackingArchive.StromquistRingOwnership
import SquarePackingArchive.StromquistRingCover

namespace SquarePackingArchive.Stromquist.TenPoints

theorem NamedFamily.bottom_rightSegment (family : NamedFamily) :
    RightSegmentHit (family.squares 7) := by
  rcases family.corner_contains_pair_of_stepTwo_unavoidable stepTwo_unavoidable with corner_low | corner_right
  · exact family.bottom_rightSegment_of_stepFour_cover stepFour_cover corner_low
  · have inside := family.bottom_contains_right_point_of_stepThree_unavoidable
      stepThree_unavoidable corner_right
    exact ⟨0, by norm_num, by norm_num, by simpa using inside⟩

theorem NamedFamily.exists_ring_parameters (family : NamedFamily) :
    ∃ parameters : Fin 8 → ℝ, RingParametersValid parameters ∧
      ∀ index, (family.squares (ringOwner index)).Contains (ringPoint index (parameters index)) := by
  classical
  have existence := family.ring_ownership_of_rightSegment NamedFamily.bottom_rightSegment
  let parameters := fun index => (existence index).choose
  exact ⟨parameters, fun index => ⟨(existence index).choose_spec.1,
    (existence index).choose_spec.2.1⟩, fun index => (existence index).choose_spec.2.2⟩

lemma NamedFamily.ring_archive_outer_ownership
    (family : NamedFamily) (parameters : Fin 8 → ℝ)
    (ring_inside : ∀ index,
      (family.squares (ringOwner index)).Contains (ringPoint index (parameters index)))
    (pointIndex : Fin 12) :
    ∃ owner : Fin 10, owner.val < 8 ∧
      (family.squares owner).Contains (ringArchivePoints parameters (pointIndex.castLE (by decide))) := by
  fin_cases pointIndex
  · exact ⟨7, by norm_num, ring_inside 0⟩
  · exact ⟨5, by norm_num, ring_inside 1⟩
  · exact ⟨5, by norm_num, ring_inside 2⟩
  · exact ⟨3, by norm_num, ring_inside 3⟩
  · exact ⟨3, by norm_num, ring_inside 4⟩
  · exact ⟨1, by norm_num, ring_inside 5⟩
  · exact ⟨1, by norm_num, ring_inside 6⟩
  · exact ⟨7, by norm_num, ring_inside 7⟩
  · exact ⟨6, by norm_num, family.contains_named_point 6⟩
  · exact ⟨4, by norm_num, family.contains_named_point 4⟩
  · exact ⟨2, by norm_num, family.contains_named_point 2⟩
  · exact ⟨0, by norm_num, family.contains_named_point 0⟩

lemma NamedFamily.inner_contains_ringCenter_of_unavoidable
    (family : NamedFamily) (parameters : Fin 8 → ℝ)
    (ring_inside : ∀ index,
      (family.squares (ringOwner index)).Contains (ringPoint index (parameters index)))
    (coverage : Unavoidable (ringArchivePoints parameters) side)
    (inner : Fin 10) (inner_lower : 8 ≤ inner.val) :
    (family.squares inner).Contains ringCenter := by
  obtain ⟨pointIndex, inside⟩ := coverage (family.squares inner) (family.fits inner)
  by_cases outer : pointIndex.val < 12
  · obtain ⟨owner, owner_upper, owner_inside⟩ :=
      family.ring_archive_outer_ownership parameters ring_inside ⟨pointIndex.val, outer⟩
    have different : inner ≠ owner := by
      intro equality
      have values := congrArg Fin.val equality
      omega
    exact False.elim (family.excludes_other different owner_inside inside)
  · have center_index : pointIndex = 12 := by apply Fin.ext; have bound := pointIndex.isLt; norm_num; omega
    subst pointIndex
    exact inside

theorem false_of_namedFamily_of_ring_unavoidable
    (coverage : ∀ parameters : Fin 8 → ℝ, RingParametersValid parameters →
      Unavoidable (ringArchivePoints parameters) side)
    (family : NamedFamily) : False := by
  obtain ⟨parameters, valid, ring_inside⟩ := family.exists_ring_parameters
  have first_center := family.inner_contains_ringCenter_of_unavoidable parameters ring_inside
    (coverage parameters valid) 8 (by norm_num)
  have second_center := family.inner_contains_ringCenter_of_unavoidable parameters ring_inside
    (coverage parameters valid) 9 (by norm_num)
  exact family.disjoint 8 9 (by decide) ringCenter ⟨first_center, second_center⟩

end SquarePackingArchive.Stromquist.TenPoints
