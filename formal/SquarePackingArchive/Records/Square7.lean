import SquarePackingArchive.Records.Square8
import SquarePackingArchive.PackingSymmetry

namespace SquarePackingArchive

lemma PlacedSquare.interiorContains_iff_localCoordinates
    (square : PlacedSquare) (point : Point) :
    square.InteriorContains point ↔ |square.localX point| < 1 / 2 ∧ |square.localY point| < 1 / 2 := by
  constructor
  · rintro ⟨localX, localY, horizontal_bound, vertical_bound, rfl⟩
    have horizontal_eq : square.localX (square.point localX localY) = localX := by
      dsimp [PlacedSquare.localX, PlacedSquare.point, Frame.place]
      linear_combination localX * square.frame.unit
    have vertical_eq : square.localY (square.point localX localY) = localY := by
      dsimp [PlacedSquare.localY, PlacedSquare.point, Frame.place]
      linear_combination localY * square.frame.unit
    rw [horizontal_eq, vertical_eq]
    exact ⟨horizontal_bound, vertical_bound⟩
  · rintro ⟨horizontal_bound, vertical_bound⟩
    refine ⟨square.localX point, square.localY point, horizontal_bound, vertical_bound, ?_⟩
    rw [Point.mk.injEq]
    constructor
    · dsimp [PlacedSquare.localX, PlacedSquare.localY, PlacedSquare.point, Frame.place]
      linear_combination -(point.x - square.center.x) * square.frame.unit
    · dsimp [PlacedSquare.localX, PlacedSquare.localY, PlacedSquare.point, Frame.place]
      linear_combination -(point.y - square.center.y) * square.frame.unit

lemma PlacedSquare.firstQuadrant_interiorContains_iff
    (square : PlacedSquare) (point : Point) :
    square.firstQuadrant.InteriorContains point ↔ square.InteriorContains point := by
  have region_eq := square.firstQuadrant_dilatedInteriorRegion_eq (by norm_num : (0 : ℝ) < 1)
  rw [PlacedSquare.dilatedInteriorRegion_one, PlacedSquare.dilatedInteriorRegion_one] at region_eq
  have membership := congrArg (fun region => point.toPlane ∈ region) region_eq
  simpa [PlacedSquare.mem_interiorRegion_iff] using membership

lemma PlacedSquare.interiorContains_one_cross_point_nonnegative_frame
    (square : PlacedSquare) {point : Point} {radius : ℝ}
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (radius_nonnegative : 0 ≤ radius) (radius_lt_half : radius < 1 / 2)
    (point_mem : square.InteriorContains point) :
    square.InteriorContains ⟨point.x + radius, point.y⟩ ∨
      square.InteriorContains ⟨point.x - radius, point.y⟩ ∨
      square.InteriorContains ⟨point.x, point.y + radius⟩ ∨
      square.InteriorContains ⟨point.x, point.y - radius⟩ := by
  have local_bounds := (square.interiorContains_iff_localCoordinates point).1 point_mem
  rw [abs_lt, abs_lt] at local_bounds
  have cosine_at_most := square.frame.cosine_le_one cosine_nonnegative
  have sine_at_most := square.frame.sine_le_one sine_nonnegative
  have horizontal_nonnegative : 0 ≤ radius * square.frame.cosine := mul_nonneg radius_nonnegative cosine_nonnegative
  have vertical_nonnegative : 0 ≤ radius * square.frame.sine := mul_nonneg radius_nonnegative sine_nonnegative
  have horizontal_small : radius * square.frame.cosine < 1 / 2 := by nlinarith
  have vertical_small : radius * square.frame.sine < 1 / 2 := by nlinarith
  by_cases horizontal_sign : 0 ≤ square.localX point
  · by_cases vertical_sign : 0 ≤ square.localY point
    · apply Or.inr (Or.inr (Or.inr ?_))
      rw [square.interiorContains_iff_localCoordinates, abs_lt, abs_lt]
      dsimp [PlacedSquare.localX, PlacedSquare.localY] at local_bounds horizontal_sign vertical_sign ⊢
      constructor <;> constructor <;> linarith
    · apply Or.inr (Or.inl ?_)
      rw [square.interiorContains_iff_localCoordinates, abs_lt, abs_lt]
      dsimp [PlacedSquare.localX, PlacedSquare.localY] at local_bounds horizontal_sign vertical_sign ⊢
      constructor <;> constructor <;> linarith
  · by_cases vertical_sign : 0 ≤ square.localY point
    · apply Or.inl
      rw [square.interiorContains_iff_localCoordinates, abs_lt, abs_lt]
      dsimp [PlacedSquare.localX, PlacedSquare.localY] at local_bounds horizontal_sign vertical_sign ⊢
      constructor <;> constructor <;> linarith
    · apply Or.inr (Or.inr (Or.inl ?_))
      rw [square.interiorContains_iff_localCoordinates, abs_lt, abs_lt]
      dsimp [PlacedSquare.localX, PlacedSquare.localY] at local_bounds horizontal_sign vertical_sign ⊢
      constructor <;> constructor <;> linarith

lemma PlacedSquare.interiorContains_one_cross_point
    (square : PlacedSquare) {point : Point} {radius : ℝ}
    (radius_nonnegative : 0 ≤ radius) (radius_lt_half : radius < 1 / 2)
    (point_mem : square.InteriorContains point) :
    square.InteriorContains ⟨point.x + radius, point.y⟩ ∨
      square.InteriorContains ⟨point.x - radius, point.y⟩ ∨
      square.InteriorContains ⟨point.x, point.y + radius⟩ ∨
      square.InteriorContains ⟨point.x, point.y - radius⟩ := by
  have result := square.firstQuadrant.interiorContains_one_cross_point_nonnegative_frame
    square.firstQuadrant_cosine_nonnegative square.firstQuadrant_sine_nonnegative
    radius_nonnegative radius_lt_half ((square.firstQuadrant_interiorContains_iff point).2 point_mem)
  simpa only [PlacedSquare.firstQuadrant_interiorContains_iff] using result

theorem Packing.interiorUnavoidable_bijective_assignment
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin count → Point) (unavoidable : InteriorUnavoidable points side) :
    ∃ assigned : Fin count → Fin count, Function.Bijective assigned ∧
      ∀ owner, (packing.squares owner).InteriorContains (points (assigned owner)) := by
  classical
  have some_point (owner : Fin count) := unavoidable (packing.squares owner) (packing.fits owner)
  let assigned := fun owner => (some_point owner).choose
  have contained (owner : Fin count) :
      (packing.squares owner).InteriorContains (points (assigned owner)) := (some_point owner).choose_spec
  have injective : Function.Injective assigned := by
    intro first second same
    by_contra different
    exact packing.disjoint first second different (points (assigned first))
      ⟨contained first, by rw [same]; exact contained second⟩
  exact ⟨assigned, ⟨injective, Finite.surjective_of_injective injective⟩, contained⟩

theorem Packing.interiorUnavoidable_same_owner_same_point_index
    {count : ℕ} {side : ℝ} (packing : Packing count side)
    (points : Fin count → Point) (unavoidable : InteriorUnavoidable points side)
    (owner first second : Fin count)
    (first_mem : (packing.squares owner).InteriorContains (points first))
    (second_mem : (packing.squares owner).InteriorContains (points second)) : first = second := by
  obtain ⟨assigned, bijective, contained⟩ := packing.interiorUnavoidable_bijective_assignment points unavoidable
  have index_eq (index : Fin count) (point_mem : (packing.squares owner).InteriorContains (points index)) :
      index = assigned owner := by
    obtain ⟨selected, selected_eq⟩ := bijective.2 index
    have owner_eq : selected = owner := by
      by_contra different
      exact packing.disjoint selected owner different (points index)
        ⟨by rw [← selected_eq]; exact contained selected, point_mem⟩
    simpa [owner_eq] using selected_eq.symm
  exact (index_eq first first_mem).trans (index_eq second second_mem).symm

end SquarePackingArchive

namespace SquarePackingArchive.Records.Square7

theorem transposed_points_unavoidable :
    Unavoidable (fun index => (Square8.points index).swap) 3 := by
  intro square fits
  obtain ⟨index, contained⟩ := Square8.points_unavoidable square.swap ((square.swap_fits_iff 3).2 fits)
  refine ⟨index, ?_⟩
  exact (square.swap_contains_iff (Square8.points index).swap).1 (by simpa using contained)

theorem s7_lower_bound : IsLowerBound 7 3 := by
  intro side has_packing
  by_contra! side_lt_three
  let packing := has_packing.some
  have side_positive : 0 < side := packing.side_positive (by norm_num)
  let factor : ℝ := 3 / side
  have factor_gt_one : 1 < factor := by
    dsimp [factor]
    rw [lt_div_iff₀ side_positive]
    linarith
  let ratio : ℝ := 1 / factor
  have ratio_positive : 0 < ratio := by dsimp [ratio]; positivity
  have ratio_lt_one : ratio < 1 := by
    dsimp [ratio]
    rw [div_lt_one (by linarith : 0 < factor)]
    exact factor_gt_one
  let green : Fin 7 → Point := fun index => (Square8.points index).scale ratio
  let red : Fin 7 → Point := fun index => (Square8.points index).swap.scale ratio
  have green_unavoidable : InteriorUnavoidable green side := by
    apply Unavoidable.interior_scaled (factor := factor) _ factor_gt_one
    simpa [factor, side_positive.ne'] using Square8.points_unavoidable
  have red_unavoidable : InteriorUnavoidable red side := by
    apply Unavoidable.interior_scaled (factor := factor) _ factor_gt_one
    simpa [factor, side_positive.ne'] using transposed_points_unavoidable
  obtain ⟨assigned, bijective, contained⟩ := packing.interiorUnavoidable_bijective_assignment green green_unavoidable
  obtain ⟨owner, center_index⟩ := bijective.2 3
  have center_mem : (packing.squares owner).InteriorContains (green 3) := by
    rw [← center_index]
    exact contained owner
  have common_center : green 3 = red 3 := by
    simp [green, red, Point.swap, Point.scale]
  have cross := (packing.squares owner).interiorContains_one_cross_point
    (radius := ratio / 2) (by positivity) (by linarith) center_mem
  have east_eq : Point.mk ((green 3).x + ratio / 2) (green 3).y = red 5 := by
    simp [green, red, Point.swap, Point.scale]
    ring
  have west_eq : Point.mk ((green 3).x - ratio / 2) (green 3).y = red 1 := by
    simp [green, red, Point.swap, Point.scale]
    ring
  have north_eq : Point.mk (green 3).x ((green 3).y + ratio / 2) = green 5 := by
    simp [green, Point.scale]
    ring
  have south_eq : Point.mk (green 3).x ((green 3).y - ratio / 2) = green 1 := by
    simp [green, Point.scale]
    ring
  rw [east_eq, west_eq, north_eq, south_eq] at cross
  rcases cross with east_mem | west_mem | north_mem | south_mem
  · have impossible := packing.interiorUnavoidable_same_owner_same_point_index red red_unavoidable owner
      3 5 (common_center ▸ center_mem) east_mem
    exact (by decide : (3 : Fin 7) ≠ 5) impossible
  · have impossible := packing.interiorUnavoidable_same_owner_same_point_index red red_unavoidable owner
      3 1 (common_center ▸ center_mem) west_mem
    exact (by decide : (3 : Fin 7) ≠ 1) impossible
  · have impossible := packing.interiorUnavoidable_same_owner_same_point_index green green_unavoidable owner
      3 5 center_mem north_mem
    exact (by decide : (3 : Fin 7) ≠ 5) impossible
  · have impossible := packing.interiorUnavoidable_same_owner_same_point_index green green_unavoidable owner
      3 1 center_mem south_mem
    exact (by decide : (3 : Fin 7) ≠ 1) impossible

theorem s7_eq_three : IsMinimumSide 7 3 :=
  ⟨by simpa using NearSquare.squareMinusTwo_hasPacking 3, s7_lower_bound⟩

end SquarePackingArchive.Records.Square7
