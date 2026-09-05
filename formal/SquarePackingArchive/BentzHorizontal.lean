import SquarePackingArchive.BentzSixRows

namespace SquarePackingArchive

lemma PlacedSquare.contains_shifted_triangle_band
    (square : PlacedSquare) (base evenHeight oddHeight shift position : ℝ)
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1)
    (horizontal_lower : base ≤ square.center.x)
    (horizontal_upper : square.center.x ≤ base + 1)
    (vertical_position : square.center.y = (1 - position) * evenHeight + position * oddHeight)
    (left_distance : shift ^ 2 + (evenHeight - oddHeight) ^ 2 ≤ 1)
    (right_distance : (1 - shift) ^ 2 + (evenHeight - oddHeight) ^ 2 ≤ 1) :
    square.Contains ⟨base, evenHeight⟩ ∨
      square.Contains ⟨base + 1, evenHeight⟩ ∨
      square.Contains ⟨base + shift - 1, oddHeight⟩ ∨
      square.Contains ⟨base + shift, oddHeight⟩ ∨
      square.Contains ⟨base + shift + 1, oddHeight⟩ := by
  by_cases left_region : square.center.x - base ≤ position * shift
  · have covered := square.contains_triangleVertex
      ⟨base, evenHeight⟩ ⟨base + shift - 1, oddHeight⟩ ⟨base + shift, oddHeight⟩
      (1 - position) (position * shift - (square.center.x - base))
      (position * (1 - shift) + (square.center.x - base))
      (by linarith) (by linarith)
      (by
        have shift_upper : shift ≤ 1 := by nlinarith [sq_nonneg (evenHeight - oddHeight)]
        nlinarith)
      (by ring) (by dsimp; ring) (by dsimp; nlinarith [vertical_position])
      (by dsimp; nlinarith) (by dsimp; nlinarith) (by dsimp; ring_nf; norm_num)
    tauto
  by_cases right_region : base + 1 - square.center.x ≤ position * (1 - shift)
  · have covered := square.contains_triangleVertex
      ⟨base + 1, evenHeight⟩ ⟨base + shift, oddHeight⟩ ⟨base + shift + 1, oddHeight⟩
      (1 - position) (position * shift + (base + 1 - square.center.x))
      (position * (1 - shift) - (base + 1 - square.center.x))
      (by linarith)
      (by
        have shift_lower : 0 ≤ shift := by nlinarith [sq_nonneg (evenHeight - oddHeight)]
        nlinarith)
      (by linarith) (by ring) (by dsimp; ring) (by dsimp; nlinarith [vertical_position])
      (by dsimp; nlinarith) (by dsimp; nlinarith) (by dsimp; ring_nf; norm_num)
    tauto
  · have covered := square.contains_triangleVertex
      ⟨base, evenHeight⟩ ⟨base + 1, evenHeight⟩ ⟨base + shift, oddHeight⟩
      (base + 1 - square.center.x - position * (1 - shift))
      (square.center.x - base - position * shift) position
      (by linarith) (by linarith) position_lower (by ring)
      (by dsimp; ring) (by dsimp; nlinarith [vertical_position])
      (by dsimp; ring_nf; norm_num) (by dsimp; nlinarith) (by dsimp; nlinarith)
    tauto

lemma PlacedSquare.contains_horizontal_between_half_and_one
    (square : PlacedSquare) {height inset : ℝ}
    (half_mem : square.Contains ⟨1 / 2, height⟩)
    (one_mem : square.Contains ⟨1, height⟩)
    (inset_lower : 1 / 2 ≤ inset) (inset_upper : inset ≤ 1) :
    square.Contains ⟨inset, height⟩ := by
  have half_bounds := (square.contains_iff_localCoordinates _).1 half_mem
  have one_bounds := (square.contains_iff_localCoordinates _).1 one_mem
  rw [square.contains_iff_localCoordinates]
  have interpolated (left right : ℝ) (left_bound : |left| ≤ 1 / 2)
      (right_bound : |right| ≤ 1 / 2) :
      |(2 - 2 * inset) * left + (2 * inset - 1) * right| ≤ 1 / 2 := by
    have in_interval := (convex_Icc (-(1 / 2) : ℝ) (1 / 2))
      (abs_le.mp left_bound) (abs_le.mp right_bound)
      (by linarith : 0 ≤ 2 - 2 * inset) (by linarith : 0 ≤ 2 * inset - 1)
      (by ring : (2 - 2 * inset) + (2 * inset - 1) = 1)
    have lower := in_interval.1
    have upper := in_interval.2
    simp only [smul_eq_mul] at lower upper
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  constructor
  · convert interpolated _ _ half_bounds.1 one_bounds.1 using 1
    congr 1
    dsimp [PlacedSquare.localX]
    ring
  · convert interpolated _ _ half_bounds.2 one_bounds.2 using 1
    congr 1
    dsimp [PlacedSquare.localY]
    ring

lemma PlacedSquare.contains_leftPair_of_gap_le_four_fifths
    {square : PlacedSquare} {side lowerHeight upperHeight : ℝ}
    (fits : square.Fits side)
    (gap_positive : 0 < upperHeight - lowerHeight)
    (gap_upper : upperHeight - lowerHeight ≤ 4 / 5)
    (center_left : square.center.x ≤ 1)
    (center_lower : lowerHeight ≤ square.center.y)
    (center_upper : square.center.y ≤ upperHeight) :
    square.Contains ⟨1, lowerHeight⟩ ∨ square.Contains ⟨1, upperHeight⟩ := by
  have pair := square.swap.contains_bottomPairWith
    ((square.swap_fits_iff side).2 fits) (by norm_num : (1 : ℝ) ≤ 1)
    gap_positive (by linarith : upperHeight - lowerHeight ≤ 1)
    (fun frame cosine_nonnegative sine_nonnegative =>
      frame.height_add_gap_product_le_sum_of_gap_le_four_fifths
        cosine_nonnegative sine_nonnegative (by norm_num) gap_upper)
    (left := lowerHeight)
    (by simpa [PlacedSquare.swap, Point.swap] using center_lower)
    (by simpa [PlacedSquare.swap, Point.swap] using center_upper)
    (by simpa [PlacedSquare.swap, Point.swap] using center_left)
  rcases pair with lower_mem | upper_mem
  · exact Or.inl ((square.swap_contains_iff ⟨1, lowerHeight⟩).1 lower_mem)
  · exact Or.inr ((square.swap_contains_iff ⟨1, upperHeight⟩).1 (by
      simpa [Point.swap] using upper_mem))

lemma PlacedSquare.contains_leftTrapezoid_pair
    {square : PlacedSquare} {side evenHeight oddHeight inset position : ℝ}
    (strict : square.StrictFits side)
    (height_different : evenHeight ≠ oddHeight)
    (height_bound : (evenHeight - oddHeight) ^ 2 ≤ (4 / 5) ^ 2)
    (inset_lower : 1 / 2 ≤ inset) (inset_upper : inset ≤ 1)
    (position_lower : 0 ≤ position) (position_upper : position ≤ 1)
    (vertical_position : square.center.y = (1 - position) * evenHeight + position * oddHeight)
    (center_left : square.center.x ≤ (1 - position) + position * inset) :
    square.Contains ⟨1, evenHeight⟩ ∨ square.Contains ⟨inset, oddHeight⟩ := by
  have center_mem : square.Contains square.center :=
    ⟨0, 0, by norm_num, by norm_num, by simp [PlacedSquare.point, Frame.place]⟩
  have center_positive := (strict center_mem).1
  have outside (height : ℝ) : ¬ square.Contains ⟨0, height⟩ := by
    intro contained
    exact (lt_irrefl (0 : ℝ)) (strict contained).1
  have preliminary : square.Contains ⟨1, evenHeight⟩ ∨
      square.Contains ⟨1 / 2, oddHeight⟩ ∨ square.Contains ⟨inset, oddHeight⟩ := by
    by_cases left_region : square.center.x ≤ position / 2
    · have vertex := square.contains_triangleVertex
        ⟨0, evenHeight⟩ ⟨0, oddHeight⟩ ⟨1 / 2, oddHeight⟩
        (1 - position) (position - 2 * square.center.x) (2 * square.center.x)
        (by linarith) (by linarith) (by linarith) (by ring)
        (by dsimp; ring) (by dsimp; nlinarith [vertical_position])
        (by dsimp; nlinarith) (by dsimp; nlinarith) (by dsimp; norm_num)
      exact Or.inr (Or.inl (vertex.resolve_left (outside evenHeight) |>.resolve_left (outside oddHeight)))
    by_cases middle_region : square.center.x ≤ 1 - position / 2
    · have vertex := square.contains_triangleVertex
        ⟨0, evenHeight⟩ ⟨1, evenHeight⟩ ⟨1 / 2, oddHeight⟩
        (1 - square.center.x - position / 2) (square.center.x - position / 2) position
        (by linarith) (by linarith) position_lower (by ring)
        (by dsimp; ring) (by dsimp; nlinarith [vertical_position])
        (by dsimp; norm_num) (by dsimp; nlinarith) (by dsimp; nlinarith)
      exact (vertex.resolve_left (outside evenHeight)).imp_right Or.inl
    · have inset_gt_half : 1 / 2 < inset := by nlinarith
      let rightWeight := (square.center.x - 1 + position / 2) / (inset - 1 / 2)
      have right_nonnegative : 0 ≤ rightWeight := by
        dsimp [rightWeight]
        exact div_nonneg (by linarith) (by linarith)
      have right_upper : rightWeight ≤ position := by
        dsimp [rightWeight]
        apply (div_le_iff₀ (by linarith : 0 < inset - 1 / 2)).2
        nlinarith
      have right_eq : rightWeight * (inset - 1 / 2) = square.center.x - 1 + position / 2 := by
        dsimp [rightWeight]
        exact div_mul_cancel₀ _ (by linarith)
      have vertex := square.contains_triangleVertex
        ⟨1, evenHeight⟩ ⟨1 / 2, oddHeight⟩ ⟨inset, oddHeight⟩
        (1 - position) (position - rightWeight) rightWeight
        (by linarith) (by linarith) right_nonnegative (by ring)
        (by dsimp; nlinarith [right_eq]) (by dsimp; nlinarith [vertical_position])
        (by dsimp; nlinarith) (by dsimp; nlinarith [sq_nonneg (1 - inset)])
        (by dsimp; nlinarith [sq_nonneg (inset - 1 / 2)])
      exact vertex
  rcases preliminary with even_mem | half_mem | odd_mem
  · exact Or.inl even_mem
  · have center_at_most_one : square.center.x ≤ 1 := by nlinarith
    have pair : square.Contains ⟨1, evenHeight⟩ ∨ square.Contains ⟨1, oddHeight⟩ := by
      rcases lt_or_gt_of_ne height_different with increasing | decreasing
      · apply square.contains_leftPair_of_gap_le_four_fifths strict.fits
          (by linarith) (by nlinarith) center_at_most_one
        · nlinarith [vertical_position]
        · nlinarith [vertical_position]
      · have reversed := square.contains_leftPair_of_gap_le_four_fifths strict.fits
          (lowerHeight := oddHeight) (upperHeight := evenHeight)
          (by linarith) (by nlinarith) center_at_most_one
          (by nlinarith [vertical_position]) (by nlinarith [vertical_position])
        exact reversed.symm
    rcases pair with even_mem | one_mem
    · exact Or.inl even_mem
    · exact Or.inr (square.contains_horizontal_between_half_and_one half_mem one_mem inset_lower inset_upper)
  · exact Or.inr odd_mem

end SquarePackingArchive
