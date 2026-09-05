import SquarePackingArchive.BentzSixRowsShift

namespace SquarePackingArchive.BentzSixRows

lemma half_point_forces_one_of_center_right_normalized
    (square : PlacedSquare) {height : ℝ}
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (point_mem : square.Contains ⟨1 / 2, height⟩)
    (center_right : 1 ≤ square.center.x) :
    square.Contains ⟨1, height⟩ := by
  have bounds := (square.contains_iff_localCoordinates _).1 point_mem
  rcases abs_le.1 bounds.1 with ⟨horizontal_lower, horizontal_upper⟩
  rcases abs_le.1 bounds.2 with ⟨vertical_lower, vertical_upper⟩
  have inverse : square.localX ⟨1 / 2, height⟩ * square.frame.cosine -
      square.localY ⟨1 / 2, height⟩ * square.frame.sine = 1 / 2 - square.center.x := by
    dsimp [PlacedSquare.localX, PlacedSquare.localY]
    linear_combination (1 / 2 - square.center.x) * square.frame.unit
  have sum_lower : 1 ≤ square.frame.cosine + square.frame.sine := by
    nlinarith [mul_nonneg cosine_nonnegative sine_nonnegative, square.frame.unit]
  have horizontal_new : |square.localX ⟨1 / 2, height⟩ + square.frame.cosine / 2| ≤ 1 / 2 := by
    apply abs_le.2
    constructor
    · linarith
    · by_contra! outside
      have cosine_positive : 0 < square.frame.cosine := by nlinarith
      have mixed := mul_pos cosine_positive (show 0 <
        square.localX ⟨1 / 2, height⟩ + square.frame.cosine / 2 - 1 / 2 by linarith)
      have vertical_product := mul_nonneg sine_nonnegative
        (show 0 ≤ 1 / 2 - square.localY ⟨1 / 2, height⟩ by linarith)
      nlinarith [square.frame.unit, sq_nonneg (square.frame.sine - 1)]
  have vertical_new : |square.localY ⟨1 / 2, height⟩ - square.frame.sine / 2| ≤ 1 / 2 := by
    apply abs_le.2
    constructor
    · by_contra! outside
      have sine_positive : 0 < square.frame.sine := by nlinarith
      have mixed := mul_pos sine_positive (show 0 <
        -(1 / 2) - (square.localY ⟨1 / 2, height⟩ - square.frame.sine / 2) by linarith)
      have horizontal_product := mul_nonneg cosine_nonnegative
        (show 0 ≤ square.localX ⟨1 / 2, height⟩ + 1 / 2 by linarith)
      nlinarith [square.frame.unit, sq_nonneg (square.frame.cosine - 1)]
    · linarith
  rw [square.contains_iff_localCoordinates]
  constructor
  · convert horizontal_new using 1
    congr 1
    dsimp [PlacedSquare.localX]
    ring
  · convert vertical_new using 1
    congr 1
    dsimp [PlacedSquare.localY]
    ring

theorem half_point_forces_one_of_center_right
    (square : PlacedSquare) {height : ℝ}
    (point_mem : square.Contains ⟨1 / 2, height⟩)
    (center_right : 1 ≤ square.center.x) :
    square.Contains ⟨1, height⟩ := by
  apply (square.firstQuadrant_contains_iff _).1
  exact half_point_forces_one_of_center_right_normalized square.firstQuadrant
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    ((square.firstQuadrant_contains_iff _).2 point_mem) (by simpa using center_right)

lemma center_height_close_to_contained_point
    (square : PlacedSquare) {point : Point} (point_mem : square.Contains point) :
    point.y - 4 / 5 < square.center.y ∧ square.center.y < point.y + 4 / 5 := by
  obtain ⟨localX, localY, horizontal_bound, vertical_bound, equality⟩ := point_mem
  have horizontal_sq : localX ^ 2 ≤ 1 / 4 := by
    rcases abs_le.1 horizontal_bound with ⟨lower, upper⟩
    nlinarith
  have vertical_sq : localY ^ 2 ≤ 1 / 4 := by
    rcases abs_le.1 vertical_bound with ⟨lower, upper⟩
    nlinarith
  have height_eq := congrArg Point.y equality
  dsimp [PlacedSquare.point, Frame.place] at height_eq
  have cauchy := sq_nonneg (localX * square.frame.cosine - localY * square.frame.sine)
  have unit_scaled :
      (localX ^ 2 + localY ^ 2) * (square.frame.cosine ^ 2 + square.frame.sine ^ 2) =
        localX ^ 2 + localY ^ 2 := by rw [square.frame.unit]; ring
  constructor <;> nlinarith [sq_nonneg (point.y - square.center.y)]

theorem middle_endpoint_forced
    (square : PlacedSquare) {side height : ℝ} (fits : square.Fits side)
    (point_mem : square.Contains ⟨1 / 2, height⟩)
    (below_missing : ¬ square.Contains ⟨1, height - 4 / 5⟩)
    (above_missing : ¬ square.Contains ⟨1, height + 4 / 5⟩) :
    square.Contains ⟨1, height⟩ := by
  by_cases center_right : 1 ≤ square.center.x
  · exact half_point_forces_one_of_center_right square point_mem center_right
  have height_bounds := center_height_close_to_contained_point square point_mem
  by_cases below : square.center.y ≤ height
  · have pair := square.contains_leftPair_of_gap_le_four_fifths fits
      (lowerHeight := height - 4 / 5) (upperHeight := height)
      (by norm_num) (by linarith) (by linarith) height_bounds.1.le below
    exact pair.resolve_left below_missing
  · have pair := square.contains_leftPair_of_gap_le_four_fifths fits
      (lowerHeight := height) (upperHeight := height + 4 / 5)
      (by norm_num) (by linarith) (by linarith) (by linarith) height_bounds.2.le
    exact pair.resolve_right above_missing

theorem top_endpoint_forced
    (square : PlacedSquare) (fits : square.Fits 6)
    (point_mem : square.Contains ⟨1 / 2, 2549 / 500⟩)
    (below_missing : ¬ square.Contains ⟨1, 2149 / 500⟩) :
    square.Contains ⟨1, 2549 / 500⟩ := by
  by_cases center_right : 1 ≤ square.center.x
  · exact half_point_forces_one_of_center_right square point_mem center_right
  have height_bounds := center_height_close_to_contained_point square point_mem
  by_cases below : square.center.y ≤ 2549 / 500
  · have pair := square.contains_leftPair_of_gap_le_four_fifths fits
      (lowerHeight := 2149 / 500) (upperHeight := 2549 / 500)
      (by norm_num) (by norm_num) (by linarith) (by dsimp at height_bounds; linarith) below
    exact pair.resolve_left below_missing
  · have reflected := (square.reflectY 6).contains_cornerPoint
      ((square.reflectY_fits_iff 6).2 fits)
      (targetX := 1) (targetY := 451 / 500)
      (by norm_num) (by norm_num)
      (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
      (by simp [PlacedSquare.reflectY, Point.reflectY]; linarith)
    apply (square.reflectY_contains_iff 6 _).1
    convert reflected using 1
    norm_num [Point.reflectY]

theorem compressed_odd_endpoint_forced
    (selected : Fin 3) (square : PlacedSquare) (fits : square.Fits 6)
    (point_mem : square.Contains (rowPoint (compressedHeights (oddRowIndex selected)) (oddRowIndex selected)))
    (others_missing : ∀ row, row ≠ oddRowIndex selected →
      ¬ square.Contains (rowPoint (compressedHeights (oddRowIndex selected)) row)) :
    square.Contains ⟨1, compressedHeights (oddRowIndex selected) (oddRowIndex selected)⟩ := by
  fin_cases selected
  · apply middle_endpoint_forced square fits
    · simpa [rowPoint, oddRowIndex] using point_mem
    · convert others_missing 0 (by decide) using 1
      norm_num [rowPoint, oddRowIndex, compressedHeights, Matrix.cons_val_two, Matrix.cons_val_four]
    · convert others_missing 2 (by decide) using 1
      norm_num [rowPoint, oddRowIndex, compressedHeights, Matrix.cons_val_two, Matrix.cons_val_four]
  · apply middle_endpoint_forced square fits
    · simpa [rowPoint, oddRowIndex] using point_mem
    · convert others_missing 2 (by decide) using 1
      norm_num [rowPoint, oddRowIndex, compressedHeights, Matrix.cons_val_two, Matrix.cons_val_four]
    · convert others_missing 4 (by decide) using 1
      norm_num [rowPoint, oddRowIndex, compressedHeights, Matrix.cons_val_two, Matrix.cons_val_four]
  · convert top_endpoint_forced square fits ?_ ?_ using 1 <;> norm_num [oddRowIndex, compressedHeights]
    · convert point_mem using 1
      norm_num [rowPoint, oddRowIndex, compressedHeights, Matrix.cons_val_two, Matrix.cons_val_four]
    · convert others_missing 4 (by decide) using 1
      norm_num [rowPoint, oddRowIndex, compressedHeights, Matrix.cons_val_two, Matrix.cons_val_four]

noncomputable def endpointPoints (selected : Fin 3) : Fin 33 → Point :=
  Function.update (lattice (compressedHeights (oddRowIndex selected))).points
    (rowPointIndex (oddRowIndex selected))
    ⟨1, compressedHeights (oddRowIndex selected) (oddRowIndex selected)⟩

theorem endpoint_strict_unavoidable
    (selected : Fin 3) (square : PlacedSquare) (strict : square.StrictFits 6) :
    ∃ index, square.Contains (endpointPoints selected index) := by
  classical
  let heights := compressedHeights (oddRowIndex selected)
  by_cases retained : ∃ index, index ≠ rowPointIndex (oddRowIndex selected) ∧
      square.Contains ((lattice heights).points index)
  · obtain ⟨index, different, contained⟩ := retained
    exact ⟨index, by simpa [endpointPoints, Function.update_of_ne different, heights] using contained⟩
  have unique_index (index : Fin 33) (contained : square.Contains ((lattice heights).points index)) :
      index = rowPointIndex (oddRowIndex selected) := by
    by_contra different
    exact retained ⟨index, different, contained⟩
  obtain ⟨latticeIndex, contained⟩ := strict_unavoidable (compressedHeights_admissible (oddRowIndex selected)) square
    (by norm_num only [Nat.cast_ofNat]; exact strict)
  have old_inside : square.Contains ((lattice heights).points (pointIndex latticeIndex)) := by
    simpa only [points_at_pointIndex] using contained
  have index_eq := unique_index _ old_inside
  rw [index_eq, points_at_rowPointIndex] at old_inside
  have others_missing : ∀ row, row ≠ oddRowIndex selected →
      ¬ square.Contains (rowPoint heights row) := by
    intro row different row_inside
    have equality := unique_index (rowPointIndex row) (by simpa only [points_at_rowPointIndex] using row_inside)
    exact different (rowPointIndex_injective equality)
  refine ⟨rowPointIndex (oddRowIndex selected), ?_⟩
  simpa [endpointPoints] using compressed_odd_endpoint_forced selected square strict.fits old_inside others_missing

theorem endpoint_interior_unavoidable
    (selected : Fin 3) {side : ℝ} (side_positive : 0 < side) (side_lt_six : side < 6) :
    InteriorUnavoidable (fun index => (endpointPoints selected index).scale (side / 6)) side := by
  exact strictUnavoidable_interior_scaled side_positive side_lt_six (endpoint_strict_unavoidable selected)

theorem odd_row_endpoint_same_owner
    {side : ℝ} (packing : Packing 33 side)
    (side_positive : 0 < side) (side_lt_six : side < 6)
    (selected : Fin 3) (owner : Fin 33)
    (initially_inside : (packing.squares owner).InteriorContains
      ((rowPoint initialHeights (oddRowIndex selected)).scale (side / 6))) :
    (packing.squares owner).InteriorContains
      ((Point.mk 1 (compressedHeights (oddRowIndex selected) (oddRowIndex selected))).scale (side / 6)) := by
  have compressed := compressed_row_same_owner packing side_positive side_lt_six (oddRowIndex selected) owner initially_inside
  have old_unavoidable := compressionPoints_interior_unavoidable (oddRowIndex selected)
    (position := 1) (by norm_num) (by norm_num) side_positive side_lt_six
  simp only [compressionPoints, interpolate_one] at old_unavoidable
  obtain ⟨index, inside⟩ := endpoint_interior_unavoidable selected side_positive side_lt_six
    (packing.squares owner) (packing.fits owner)
  by_cases same : index = rowPointIndex (oddRowIndex selected)
  · simpa [endpointPoints, same] using inside
  · have old_inside : (packing.squares owner).InteriorContains
        (((lattice (compressedHeights (oddRowIndex selected))).points index).scale (side / 6)) := by
      simpa [endpointPoints, Function.update_of_ne same] using inside
    have equality := packing.interiorUnavoidable_same_owner_same_point_index _ old_unavoidable owner
      index (rowPointIndex (oddRowIndex selected)) old_inside
      (by simpa only [points_at_rowPointIndex] using compressed)
    exact (same equality).elim

end SquarePackingArchive.BentzSixRows
