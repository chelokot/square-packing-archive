import SquarePackingArchive.NagamochiBoundaryPropagation

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma unit_corner_mem_of_adjacent_marked_points_nonnegative_frame
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (vertical_point_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (horizontal_point_mem : ![(9 / 10 : ℝ), 1] ∈ square.dilatedInteriorRegion factor) :
    ![(1 : ℝ), 1] ∈ square.dilatedInteriorRegion factor := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  have vertical_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive vertical_point_mem
  have horizontal_bounds := inverse_bounds_of_dilatedInteriorRegion_mem square factor_positive horizontal_point_mem
  rw [abs_lt, abs_lt] at vertical_bounds horizontal_bounds
  apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
  · rw [abs_lt]
    refine ⟨?_, unit_corner_localX_lt_half_factor square fits factor_gt_one
      cosine_nonnegative sine_nonnegative⟩
    have lower_bound := vertical_bounds.1.1
    dsimp [PlacedSquare.dilatedLocalX, Plane.toPoint] at lower_bound ⊢
    linarith
  · rw [abs_lt]
    constructor
    · have lower_bound := vertical_bounds.2.1
      dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at lower_bound ⊢
      linarith
    · have upper_bound := horizontal_bounds.2.2
      dsimp [PlacedSquare.dilatedLocalY, Plane.toPoint] at upper_bound ⊢
      linarith

theorem unit_corner_mem_of_adjacent_marked_points
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (vertical_point_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (horizontal_point_mem : ![(9 / 10 : ℝ), 1] ∈ square.dilatedInteriorRegion factor) :
    ![(1 : ℝ), 1] ∈ square.dilatedInteriorRegion factor := by
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq (zero_lt_one.trans factor_gt_one)
  have normalized := unit_corner_mem_of_adjacent_marked_points_nonnegative_frame square.firstQuadrant
    ((square.firstQuadrant_fits_iff side).2 fits) factor_gt_one
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    (by rwa [region_eq]) (by rwa [region_eq])
  rwa [region_eq] at normalized

lemma corner_segments_mem_of_convex
    {region : Set Plane} (convex_region : Convex ℝ region)
    (vertical_point_mem : ![(1 : ℝ), 9 / 10] ∈ region)
    (horizontal_point_mem : ![(9 / 10 : ℝ), 1] ∈ region)
    (corner_mem : ![(1 : ℝ), 1] ∈ region) :
    ∀ coordinate ∈ Icc (9 / 10 : ℝ) 1,
      ![(1 : ℝ), coordinate] ∈ region ∧ ![coordinate, (1 : ℝ)] ∈ region := by
  intro coordinate coordinate_bounds
  have first_nonnegative : 0 ≤ 10 - 10 * coordinate := by linarith [coordinate_bounds.2]
  have second_nonnegative : 0 ≤ 10 * coordinate - 9 := by linarith [coordinate_bounds.1]
  have sum_eq : (10 - 10 * coordinate) + (10 * coordinate - 9) = 1 := by ring
  constructor
  · have combination := convex_region vertical_point_mem corner_mem
      first_nonnegative second_nonnegative sum_eq
    convert combination using 1
    ext component
    fin_cases component <;> simp <;> ring
  · have combination := convex_region horizontal_point_mem corner_mem
      first_nonnegative second_nonnegative sum_eq
    convert combination using 1
    ext component
    fin_cases component <;> simp <;> ring

theorem corner_segments_mem_of_adjacent_marked_points
    (square : PlacedSquare) {side factor : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (vertical_point_mem : ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor)
    (horizontal_point_mem : ![(9 / 10 : ℝ), 1] ∈ square.dilatedInteriorRegion factor) :
    ∀ coordinate ∈ Icc (9 / 10 : ℝ) 1,
      ![(1 : ℝ), coordinate] ∈ square.dilatedInteriorRegion factor ∧
        ![coordinate, (1 : ℝ)] ∈ square.dilatedInteriorRegion factor :=
  corner_segments_mem_of_convex (square.convex_dilatedInteriorRegion factor)
    vertical_point_mem horizontal_point_mem
    (unit_corner_mem_of_adjacent_marked_points square fits factor_gt_one
      vertical_point_mem horizontal_point_mem)

theorem not_adjacent_marked_points_of_missing_corner_segment
    (square : PlacedSquare) {side factor coordinate : ℝ}
    (fits : square.Fits side) (factor_gt_one : 1 < factor)
    (coordinate_bounds : coordinate ∈ Icc (9 / 10 : ℝ) 1)
    (point_missing : ![(1 : ℝ), coordinate] ∉ square.dilatedInteriorRegion factor ∨
      ![coordinate, (1 : ℝ)] ∉ square.dilatedInteriorRegion factor) :
    ¬ (![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor ∧
      ![(9 / 10 : ℝ), 1] ∈ square.dilatedInteriorRegion factor) := by
  rintro ⟨vertical_point_mem, horizontal_point_mem⟩
  have contained := corner_segments_mem_of_adjacent_marked_points square fits factor_gt_one
    vertical_point_mem horizontal_point_mem coordinate coordinate_bounds
  exact point_missing.elim (fun missing => missing contained.1) (fun missing => missing contained.2)

end SquarePackingArchive.Nagamochi
