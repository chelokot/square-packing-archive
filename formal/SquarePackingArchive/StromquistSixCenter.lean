import SquarePackingArchive.StromquistSixLemma8

namespace SquarePackingArchive.StromquistSix

theorem center_pair_local_bounds {cosine sine horizontal vertical : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (cosine_le_one : cosine ≤ 1) (sine_le_one : sine ≤ 1)
    (sine_le_cosine : sine ≤ cosine)
    (center_mem : |horizontal| ≤ 1 / 2 ∧ |vertical| ≤ 1 / 2)
    (north_mem : |horizontal + sine / 2| ≤ 1 / 2 ∧ |vertical + cosine / 2| ≤ 1 / 2)
    (west_missing : ¬ (|horizontal - cosine / 2| ≤ 1 / 2 ∧ |vertical + sine / 2| ≤ 1 / 2))
    (east_missing : ¬ (|horizontal + cosine / 2| ≤ 1 / 2 ∧ |vertical - sine / 2| ≤ 1 / 2))
    (northwest_missing : ¬ (|horizontal - cosine / 2 + sine / 2| ≤ 1 / 2 ∧
      |vertical + sine / 2 + cosine / 2| ≤ 1 / 2))
    (northeast_missing : ¬ (|horizontal + cosine / 2 + sine / 2| ≤ 1 / 2 ∧
      |vertical - sine / 2 + cosine / 2| ≤ 1 / 2)) :
    (1 - cosine - sine) / 2 < horizontal ∧ horizontal < (cosine - 1) / 2 ∧
    (1 - cosine - sine) / 2 < vertical ∧ vertical < (sine - 1) / 2 := by
  simp only [abs_le] at center_mem north_mem
  simp only [abs_le, not_and_or, not_le] at west_missing east_missing northwest_missing northeast_missing
  have horizontal_upper : horizontal < (cosine - 1) / 2 := by
    rcases west_missing with (missing | missing) | (missing | missing) <;> linarith
  have vertical_upper : vertical < (sine - 1) / 2 := by
    rcases east_missing with (missing | missing) | (missing | missing) <;> linarith
  have horizontal_lower : (1 - cosine - sine) / 2 < horizontal := by
    rcases northeast_missing with (missing | missing) | (missing | missing) <;> linarith
  have vertical_lower : (1 - cosine - sine) / 2 < vertical := by
    rcases northwest_missing with (missing | missing) | (missing | missing) <;> linarith
  exact ⟨horizontal_lower, horizontal_upper, vertical_lower, vertical_upper⟩

theorem center_pair_forces_extra_points_local_ordered {cosine sine horizontal vertical : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1) (sine_le_cosine : sine ≤ cosine)
    (center_mem : |horizontal| ≤ 1 / 2 ∧ |vertical| ≤ 1 / 2)
    (north_mem : |horizontal + sine / 2| ≤ 1 / 2 ∧ |vertical + cosine / 2| ≤ 1 / 2)
    (west_missing : ¬ (|horizontal - cosine / 2| ≤ 1 / 2 ∧ |vertical + sine / 2| ≤ 1 / 2))
    (east_missing : ¬ (|horizontal + cosine / 2| ≤ 1 / 2 ∧ |vertical - sine / 2| ≤ 1 / 2))
    (northwest_missing : ¬ (|horizontal - cosine / 2 + sine / 2| ≤ 1 / 2 ∧
      |vertical + sine / 2 + cosine / 2| ≤ 1 / 2))
    (northeast_missing : ¬ (|horizontal + cosine / 2 + sine / 2| ≤ 1 / 2 ∧
      |vertical - sine / 2 + cosine / 2| ≤ 1 / 2)) :
    (|horizontal - cosine / 2 + sine / 5| ≤ 1 / 2 ∧
      |vertical + sine / 2 + cosine / 5| ≤ 1 / 2) ∧
    (|horizontal + cosine / 2 + sine / 5| ≤ 1 / 2 ∧
      |vertical - sine / 2 + cosine / 5| ≤ 1 / 2) := by
  have cosine_le_one : cosine ≤ 1 := by nlinarith [sq_nonneg sine]
  have sine_le_one : sine ≤ 1 := by nlinarith [sq_nonneg cosine]
  have bounds := center_pair_local_bounds cosine_nonnegative sine_nonnegative cosine_le_one sine_le_one
    sine_le_cosine center_mem north_mem west_missing east_missing northwest_missing northeast_missing
  have large_sum : 2 < cosine + 2 * sine := by linarith [bounds.2.2.1, bounds.2.2.2]
  have sine_lower : 3 / 5 ≤ sine := by
    by_contra! too_small
    have weighted := mul_pos (show 0 < cosine + 2 * sine - 2 by linarith)
      (show 0 < cosine + 2 - 2 * sine by linarith)
    nlinarith [mul_pos (show 0 < 3 / 5 - sine by linarith) (show 0 < 1 - sine by linarith)]
  have tangent : 4 / 5 * cosine + 3 / 5 * sine ≤ 1 := by
    nlinarith [sq_nonneg (cosine - 4 / 5), sq_nonneg (sine - 3 / 5)]
  have first_bound : cosine + 3 / 10 * sine ≤ 1 := by linarith
  have second_bound : sine + 3 / 10 * cosine ≤ 1 := by linarith
  simp only [abs_le] at center_mem north_mem ⊢
  exact ⟨⟨⟨by linarith [bounds.1], by linarith⟩,
      ⟨by linarith, by linarith [bounds.2.2.2]⟩⟩,
    ⟨⟨by linarith, by linarith [bounds.2.1]⟩,
      ⟨by linarith [bounds.2.2.1], by linarith⟩⟩⟩

theorem center_pair_forces_extra_points_local {cosine sine horizontal vertical : ℝ}
    (cosine_nonnegative : 0 ≤ cosine) (sine_nonnegative : 0 ≤ sine)
    (unit : cosine ^ 2 + sine ^ 2 = 1)
    (center_mem : |horizontal| ≤ 1 / 2 ∧ |vertical| ≤ 1 / 2)
    (north_mem : |horizontal + sine / 2| ≤ 1 / 2 ∧ |vertical + cosine / 2| ≤ 1 / 2)
    (west_missing : ¬ (|horizontal - cosine / 2| ≤ 1 / 2 ∧ |vertical + sine / 2| ≤ 1 / 2))
    (east_missing : ¬ (|horizontal + cosine / 2| ≤ 1 / 2 ∧ |vertical - sine / 2| ≤ 1 / 2))
    (northwest_missing : ¬ (|horizontal - cosine / 2 + sine / 2| ≤ 1 / 2 ∧
      |vertical + sine / 2 + cosine / 2| ≤ 1 / 2))
    (northeast_missing : ¬ (|horizontal + cosine / 2 + sine / 2| ≤ 1 / 2 ∧
      |vertical - sine / 2 + cosine / 2| ≤ 1 / 2)) :
    (|horizontal - cosine / 2 + sine / 5| ≤ 1 / 2 ∧
      |vertical + sine / 2 + cosine / 5| ≤ 1 / 2) ∧
    (|horizontal + cosine / 2 + sine / 5| ≤ 1 / 2 ∧
      |vertical - sine / 2 + cosine / 5| ≤ 1 / 2) := by
  by_cases order : sine ≤ cosine
  · exact center_pair_forces_extra_points_local_ordered cosine_nonnegative sine_nonnegative unit order
      center_mem north_mem west_missing east_missing northwest_missing northeast_missing
  · have result := center_pair_forces_extra_points_local_ordered sine_nonnegative cosine_nonnegative
      (by linarith : sine ^ 2 + cosine ^ 2 = 1) (le_of_not_ge order)
      center_mem.symm north_mem.symm
      (by simpa only [and_comm] using east_missing)
      (by simpa only [and_comm] using west_missing)
      (by simpa only [and_comm] using northeast_missing)
      (by simpa only [and_comm] using northwest_missing)
    exact ⟨result.2.symm, result.1.symm⟩

theorem contains_iff_relative (square : PlacedSquare) (point anchor : Point) :
    square.Contains point ↔
    |square.localX anchor + square.frame.cosine * (point.x - anchor.x) +
      square.frame.sine * (point.y - anchor.y)| ≤ 1 / 2 ∧
    |square.localY anchor - square.frame.sine * (point.x - anchor.x) +
      square.frame.cosine * (point.y - anchor.y)| ≤ 1 / 2 := by
  rw [square.contains_iff_localCoordinates, localX_relative square point anchor,
    localY_relative square point anchor]

theorem center_pair_forces_extra_points_nonnegative_frame {square : PlacedSquare}
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (center_mem : square.Contains ⟨3 / 2, 3 / 2⟩)
    (north_mem : square.Contains ⟨3 / 2, 2⟩)
    (west_missing : ¬ square.Contains ⟨1, 3 / 2⟩)
    (east_missing : ¬ square.Contains ⟨2, 3 / 2⟩)
    (northwest_missing : ¬ square.Contains ⟨1, 2⟩)
    (northeast_missing : ¬ square.Contains ⟨2, 2⟩) :
    square.Contains ⟨1, 17 / 10⟩ ∧ square.Contains ⟨2, 17 / 10⟩ := by
  rw [square.contains_iff_localCoordinates] at center_mem
  rw [contains_iff_relative square _ ⟨3 / 2, 3 / 2⟩] at north_mem west_missing east_missing northwest_missing northeast_missing
  dsimp only at north_mem west_missing east_missing northwest_missing northeast_missing
  ring_nf at north_mem west_missing east_missing northwest_missing northeast_missing
  have result := center_pair_forces_extra_points_local cosine_nonnegative sine_nonnegative
    square.frame.unit center_mem
    (by convert north_mem using 1 <;> ring_nf)
    (by convert west_missing using 1; ring_nf)
    (by convert east_missing using 1; ring_nf)
    (by convert northwest_missing using 1; ring_nf)
    (by convert northeast_missing using 1; ring_nf)
  rw [contains_iff_relative square _ ⟨3 / 2, 3 / 2⟩, contains_iff_relative square _ ⟨3 / 2, 3 / 2⟩]
  norm_num
  convert result using 3 <;> congr 1 <;> ring

theorem center_pair_forces_extra_points {square : PlacedSquare}
    (center_mem : square.Contains ⟨3 / 2, 3 / 2⟩)
    (north_mem : square.Contains ⟨3 / 2, 2⟩)
    (west_missing : ¬ square.Contains ⟨1, 3 / 2⟩)
    (east_missing : ¬ square.Contains ⟨2, 3 / 2⟩)
    (northwest_missing : ¬ square.Contains ⟨1, 2⟩)
    (northeast_missing : ¬ square.Contains ⟨2, 2⟩) :
    square.Contains ⟨1, 17 / 10⟩ ∧ square.Contains ⟨2, 17 / 10⟩ := by
  have result := center_pair_forces_extra_points_nonnegative_frame
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    ((square.firstQuadrant_contains_iff _).2 center_mem)
    ((square.firstQuadrant_contains_iff _).2 north_mem)
    (by simpa only [PlacedSquare.firstQuadrant_contains_iff] using west_missing)
    (by simpa only [PlacedSquare.firstQuadrant_contains_iff] using east_missing)
    (by simpa only [PlacedSquare.firstQuadrant_contains_iff] using northwest_missing)
    (by simpa only [PlacedSquare.firstQuadrant_contains_iff] using northeast_missing)
  simpa only [PlacedSquare.firstQuadrant_contains_iff] using result

end SquarePackingArchive.StromquistSix
