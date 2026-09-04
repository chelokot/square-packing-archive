import SquarePackingArchive.NagamochiEndpointResource
import SquarePackingArchive.NagamochiFiniteChain
import SquarePackingArchive.NagamochiResourceSymmetry

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

theorem endpoint_two_height_score_budget_of_upperX_facet
    (square : PlacedSquare) {size coordinate : ℕ} {factor firstHeight secondHeight : ℝ}
    (fits : square.Fits (size / factor)) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (grid_point_mem : ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (previous_point_missing : ![(coordinate : ℝ) - 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (first_upper_facet : factor / 2 ≤ square.dilatedLocalX factor ⟨coordinate, firstHeight⟩)
    (second_upper_facet : factor / 2 ≤ square.dilatedLocalX factor ⟨coordinate, secondHeight⟩)
    (first_at_most : firstHeight ≤ 1) (second_at_most : secondHeight ≤ 1)
    (vertex_below_grid : factor * square.center.y +
      factor * (square.frame.cosine - square.frame.sine) / 2 ≤ 9 / 10) :
    ENNReal.ofReal (1 + (1 - firstHeight) / 2 + (1 - secondHeight) / 2) <
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have scaled_side : factor * ((size : ℝ) / factor) = size := by field_simp
  have coordinate_bounds := Finset.mem_Icc.mp coordinate_mem
  have reflected_coordinate : (size - coordinate : ℕ) ∈ Finset.Icc 2 (size - 2) := by
    simp only [Finset.mem_Icc]
    omega
  have reflected_coordinate_real : ((size - coordinate : ℕ) : ℝ) = (size : ℝ) - coordinate :=
    Nat.cast_sub (by omega)
  let canonical := (square.reflectX (size / factor)).firstQuadrant
  have canonical_eq : canonical = (square.reflectX (size / factor)).rotateThreeQuarter := by
    dsimp [canonical, PlacedSquare.firstQuadrant]
    rw [if_neg (show ¬0 ≤ (square.reflectX (size / factor)).frame.cosine by
      change ¬0 ≤ -square.frame.cosine
      linarith)]
    rw [if_pos (show 0 ≤ (square.reflectX (size / factor)).frame.sine from sine_positive.le)]
  have canonical_cosine : canonical.frame.cosine = square.frame.sine := by
    rw [canonical_eq]
    simp [PlacedSquare.rotateThreeQuarter, PlacedSquare.rotateHalf, PlacedSquare.rotateQuarter,
      PlacedSquare.reflectX, Frame.rotateQuarter, Frame.reflectX]
  have canonical_sine : canonical.frame.sine = square.frame.cosine := by
    rw [canonical_eq]
    simp [PlacedSquare.rotateThreeQuarter, PlacedSquare.rotateHalf, PlacedSquare.rotateQuarter,
      PlacedSquare.reflectX, Frame.rotateQuarter, Frame.reflectX]
  have canonical_center : canonical.center = ⟨(size : ℝ) / factor - square.center.x, square.center.y⟩ := by
    simp [canonical, PlacedSquare.reflectX, Point.reflectX]
  have canonical_fits : canonical.Fits (size / factor) := by simpa [canonical] using fits
  have region_eq : canonical.dilatedInteriorRegion factor =
      (square.reflectX (size / factor)).dilatedInteriorRegion factor :=
    (square.reflectX (size / factor)).firstQuadrant_dilatedInteriorRegion_eq factor_positive
  have canonical_point : ![((size - coordinate : ℕ) : ℝ), (9 / 10 : ℝ)] ∈
      canonical.dilatedInteriorRegion factor := by
    rw [region_eq, reflected_coordinate_real]
    simpa [scaled_side, Plane.reflectX] using
      (square.mem_reflectX_dilatedInteriorRegion_iff (coordinateSum := size / factor) factor_positive
        ![(coordinate : ℝ), (9 / 10 : ℝ)]).2 grid_point_mem
  have canonical_next_missing : ![((size - coordinate : ℕ) : ℝ) + 1, (9 / 10 : ℝ)] ∉
      canonical.dilatedInteriorRegion factor := by
    intro point_mem
    apply previous_point_missing
    apply (square.mem_reflectX_dilatedInteriorRegion_iff (coordinateSum := size / factor) factor_positive
      ![(coordinate : ℝ) - 1, (9 / 10 : ℝ)]).1
    rw [region_eq, reflected_coordinate_real] at point_mem
    convert point_mem using 1
    simp [Plane.reflectX, scaled_side]
    ring
  have canonical_facet (height : ℝ)
      (facet : factor / 2 ≤ square.dilatedLocalX factor ⟨coordinate, height⟩) :
      factor / 2 ≤ canonical.dilatedLocalY factor ⟨(size - coordinate : ℕ), height⟩ := by
    dsimp [PlacedSquare.dilatedLocalY]
    rw [canonical_cosine, canonical_sine, canonical_center, reflected_coordinate_real]
    dsimp [PlacedSquare.dilatedLocalX] at facet
    nlinarith
  have canonical_vertex : factor * canonical.center.y +
      factor * (canonical.frame.sine - canonical.frame.cosine) / 2 ≤ 9 / 10 := by
    rw [canonical_cosine, canonical_sine, canonical_center]
    exact vertex_below_grid
  have result := endpoint_two_height_score_budget_of_fits canonical canonical_fits size_lower
    factor_gt_one factor_at_most (by rwa [canonical_cosine]) (by rwa [canonical_sine])
    reflected_coordinate canonical_point canonical_next_missing
    (canonical_facet firstHeight first_upper_facet) (canonical_facet secondHeight second_upper_facet)
    first_at_most second_at_most canonical_vertex
  have reflected_region_eq : (square.reflectX (size / factor)).dilatedInteriorRegion factor =
      Plane.reflectX size ⁻¹' square.dilatedInteriorRegion factor := by
    ext point
    simpa [scaled_side] using square.mem_reflectX_dilatedInteriorRegion_iff
      (coordinateSum := size / factor) factor_positive (point.reflectX size)
  rw [region_eq, reflected_region_eq, resourceMeasure_preimage_reflectX size
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')] at result
  exact result

theorem terminal_two_height_score_budget_of_ordered_stop
    (square : PlacedSquare) {size coordinate : ℕ} {factor firstHeight secondHeight : ℝ}
    (fits : square.Fits (size / factor)) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (grid_point_mem : ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (previous_point_missing : ![(coordinate : ℝ) - 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (next_point_missing : ![(coordinate : ℝ) + 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (first_terminal : BoundaryChainTerminal square factor coordinate firstHeight)
    (height_order : firstHeight ≤ secondHeight)
    (first_at_most : firstHeight ≤ 1) (second_at_most : secondHeight ≤ 1) :
    ENNReal.ofReal (1 + (1 - firstHeight) / 2 + (1 - secondHeight) / 2) <
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  obtain ⟨cosine_positive, sine_positive, terminal⟩ := first_terminal
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq factor_positive
  have normalized_fits := (square.firstQuadrant_fits_iff _).2 fits
  have normalized_point := region_eq.symm ▸ grid_point_mem
  rcases terminal with ⟨first_facet, low_vertex⟩ | ⟨first_facet, low_vertex⟩
  · have second_facet : factor / 2 ≤ square.firstQuadrant.dilatedLocalY factor ⟨coordinate, secondHeight⟩ := by
      dsimp [PlacedSquare.dilatedLocalY] at first_facet ⊢
      nlinarith
    have normalized_low : factor * square.firstQuadrant.center.y +
        factor * (square.firstQuadrant.frame.sine - square.firstQuadrant.frame.cosine) / 2 ≤ 9 / 10 := by
      simpa using low_vertex.le
    have result := endpoint_two_height_score_budget_of_fits square.firstQuadrant normalized_fits size_lower
      factor_gt_one factor_at_most cosine_positive sine_positive coordinate_mem normalized_point
      (region_eq.symm ▸ next_point_missing) first_facet second_facet first_at_most second_at_most normalized_low
    rwa [region_eq] at result
  · have second_facet : factor / 2 ≤ square.firstQuadrant.dilatedLocalX factor ⟨coordinate, secondHeight⟩ := by
      dsimp [PlacedSquare.dilatedLocalX] at first_facet ⊢
      nlinarith
    have normalized_low : factor * square.firstQuadrant.center.y +
        factor * (square.firstQuadrant.frame.cosine - square.firstQuadrant.frame.sine) / 2 ≤ 9 / 10 := by
      simpa using low_vertex.le
    have result := endpoint_two_height_score_budget_of_upperX_facet square.firstQuadrant normalized_fits size_lower
      factor_gt_one factor_at_most cosine_positive sine_positive coordinate_mem normalized_point
      (region_eq.symm ▸ previous_point_missing) first_facet second_facet first_at_most second_at_most normalized_low
    rwa [region_eq] at result

theorem terminal_two_height_score_repays
    (square : PlacedSquare) {size coordinate : ℕ} {side factor firstHeight secondHeight : ℝ}
    (fits : square.Fits side) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (scaled_side_le : factor * side ≤ size)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (grid_point_mem : ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (previous_point_missing : ![(coordinate : ℝ) - 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (next_point_missing : ![(coordinate : ℝ) + 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (first_terminal : BoundaryChainTerminal square factor coordinate firstHeight)
    (second_terminal : BoundaryChainTerminal square factor coordinate secondHeight)
    (first_height_mem : firstHeight ∈ Icc (9 / 10 : ℝ) 1)
    (second_height_mem : secondHeight ∈ Icc (9 / 10 : ℝ) 1) :
    ENNReal.ofReal (1 + (1 - firstHeight) / 2 + (1 - secondHeight) / 2) <
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have side_le : side ≤ (size : ℝ) / factor := by
    apply (le_div_iff₀ (zero_lt_one.trans factor_gt_one)).mpr
    simpa only [mul_comm] using scaled_side_le
  have enlarged_fits : square.Fits (size / factor) := by
    intro point point_mem
    have bounds := fits point_mem
    exact ⟨bounds.1, bounds.2.1.trans side_le, bounds.2.2.1, bounds.2.2.2.trans side_le⟩
  by_cases height_order : firstHeight ≤ secondHeight
  · exact terminal_two_height_score_budget_of_ordered_stop square enlarged_fits size_lower factor_gt_one
      factor_at_most coordinate_mem grid_point_mem previous_point_missing next_point_missing first_terminal
      height_order first_height_mem.2 second_height_mem.2
  · have result := terminal_two_height_score_budget_of_ordered_stop square enlarged_fits size_lower factor_gt_one
      factor_at_most coordinate_mem grid_point_mem previous_point_missing next_point_missing second_terminal
      (le_of_not_ge height_order) second_height_mem.2 first_height_mem.2
    simpa only [add_comm, add_left_comm, add_assoc] using result

theorem terminal_one_height_score_repays
    (square : PlacedSquare) {size coordinate : ℕ} {side factor height : ℝ}
    (fits : square.Fits side) (size_lower : 4 ≤ size)
    (factor_gt_one : 1 < factor) (factor_at_most : factor ≤ 101 / 100)
    (scaled_side_le : factor * side ≤ size)
    (coordinate_mem : coordinate ∈ Finset.Icc 2 (size - 2))
    (grid_point_mem : ![(coordinate : ℝ), (9 / 10 : ℝ)] ∈ square.dilatedInteriorRegion factor)
    (previous_point_missing : ![(coordinate : ℝ) - 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (next_point_missing : ![(coordinate : ℝ) + 1, (9 / 10 : ℝ)] ∉ square.dilatedInteriorRegion factor)
    (terminal : BoundaryChainTerminal square factor coordinate height)
    (height_mem : height ∈ Icc (9 / 10 : ℝ) 1) :
    ENNReal.ofReal (1 + (1 - height) / 2) <
      NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have result := terminal_two_height_score_repays square fits size_lower factor_gt_one factor_at_most
    scaled_side_le coordinate_mem grid_point_mem previous_point_missing next_point_missing terminal terminal
    height_mem height_mem
  exact (ENNReal.ofReal_le_ofReal (by linarith [height_mem.2])).trans_lt result

end SquarePackingArchive.Nagamochi
