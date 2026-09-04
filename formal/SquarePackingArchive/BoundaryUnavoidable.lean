import SquarePackingArchive.Unavoidable

namespace SquarePackingArchive

def PlacedSquare.StrictFits (square : PlacedSquare) (side : ℝ) : Prop :=
  ∀ ⦃point⦄, square.Contains point →
    0 < point.x ∧ point.x < side ∧ 0 < point.y ∧ point.y < side

lemma PlacedSquare.StrictFits.fits
    {square : PlacedSquare} {side : ℝ} (strict : square.StrictFits side) :
    square.Fits side := by
  intro point point_mem
  obtain ⟨left, right, bottom, top⟩ := strict point_mem
  exact ⟨left.le, right.le, bottom.le, top.le⟩

lemma PlacedSquare.StrictFits.reflectY
    {square : PlacedSquare} {side : ℝ} (strict : square.StrictFits side) :
    (square.reflectY side).StrictFits side := by
  intro point point_mem
  have source_mem : square.Contains (point.reflectY side) :=
    (square.reflectY_contains_iff side (point.reflectY side)).mp (by simpa using point_mem)
  obtain ⟨left, right, bottom, top⟩ := strict source_mem
  simp only [Point.reflectY] at left right bottom top
  exact ⟨left, right, by linarith, by linarith⟩

lemma PlacedSquare.interiorContains_strict_bounds
    {square : PlacedSquare} {side : ℝ} {point : Point}
    (fits : square.Fits side) (point_mem : square.InteriorContains point) :
    0 < point.x ∧ point.x < side ∧ 0 < point.y ∧ point.y < side := by
  have region_mem : point.toPlane ∈ square.interiorRegion := by
    exact (square.mem_interiorRegion_iff point.toPlane).2 point_mem
  have interior_mem : point.toPlane ∈ interior (containerRegion side) :=
    square.isOpen_interiorRegion.subset_interior_iff.mpr
      (square.interiorRegion_subset_containerRegion fits) region_mem
  have container_pi : containerRegion side =
      Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) side) := by
    ext coordinates
    simp [containerRegion, Set.mem_Icc, Pi.le_def]
  rw [container_pi, interior_pi_set Set.finite_univ] at interior_mem
  simp only [interior_Icc, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Ioo] at interior_mem
  exact ⟨(interior_mem 0).1, (interior_mem 0).2,
    (interior_mem 1).1, (interior_mem 1).2⟩

lemma PlacedSquare.scaleCenter_strictFits
    {square : PlacedSquare} {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor) :
    (square.scaleCenter factor).StrictFits (factor * side) := by
  intro point point_mem
  have source_bounds := square.interiorContains_strict_bounds fits
    (square.interiorContains_scaled_of_scaleCenter_contains factor_gt_one point_mem)
  have factor_positive : 0 < factor := by linarith
  simp only [Point.scale_x, Point.scale_y, one_div_mul_eq_div] at source_bounds
  exact ⟨(div_pos_iff_of_pos_right factor_positive).mp source_bounds.1,
    by simpa [mul_comm] using (div_lt_iff₀ factor_positive).mp source_bounds.2.1,
    (div_pos_iff_of_pos_right factor_positive).mp source_bounds.2.2.1,
    by simpa [mul_comm] using (div_lt_iff₀ factor_positive).mp source_bounds.2.2.2⟩

theorem lowerBound_succ_of_strict_unavoidable
    {pointCount : ℕ} {points : Fin pointCount → Point} {side : ℝ}
    (unavoidable : ∀ square : PlacedSquare, square.StrictFits side →
      ∃ index, square.Contains (points index)) :
    IsLowerBound (pointCount + 1) side := by
  apply lowerBound_succ_of_interiorUnavoidable_below
  intro candidateSide candidate_positive candidate_lt_side
  let factor := side / candidateSide
  have factor_gt_one : 1 < factor := by
    dsimp [factor]
    exact (lt_div_iff₀ candidate_positive).2 (by simpa using candidate_lt_side)
  refine ⟨fun index => (points index).scale (1 / factor), ?_⟩
  intro square fits
  have strict : (square.scaleCenter factor).StrictFits side := by
    simpa [factor, candidate_positive.ne'] using
      square.scaleCenter_strictFits fits factor_gt_one
  obtain ⟨index, point_mem⟩ := unavoidable (square.scaleCenter factor) strict
  exact ⟨index,
    square.interiorContains_scaled_of_scaleCenter_contains factor_gt_one point_mem⟩

end SquarePackingArchive
