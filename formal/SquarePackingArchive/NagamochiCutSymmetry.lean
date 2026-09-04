import SquarePackingArchive.NagamochiCut

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

lemma measurePreserving_swapPlane : MeasurePreserving Plane.swap volume volume := by
  convert volume_measurePreserving_piCongrLeft (fun _ : Fin 2 => ℝ)
    (Equiv.swap (0 : Fin 2) 1) using 1
  funext point coordinate
  fin_cases coordinate <;>
    simp [Plane.swap, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

lemma measurePreserving_reflectYZero :
    MeasurePreserving (Plane.reflectY 0) volume volume := by
  let componentMap : Fin 2 → ℝ → ℝ := ![id, fun value => -value]
  have components_preserving :
      ∀ coordinate, MeasurePreserving (componentMap coordinate) volume volume := by
    intro coordinate
    fin_cases coordinate
    · exact MeasurePreserving.id volume
    · exact volume.measurePreserving_neg
  convert volume_preserving_pi components_preserving using 1 <;> try rfl
  funext point coordinate
  fin_cases coordinate <;> simp [Plane.reflectY, componentMap]

def InnerBoundarySide.canonicalPoint : InnerBoundarySide → Plane → Plane
  | .bottom => id
  | .top => Plane.reflectY 0
  | .left => Plane.swap
  | .right => fun point => (point.swap).reflectY 0

noncomputable def InnerBoundarySide.canonicalSquare
    (side : InnerBoundarySide) (square : PlacedSquare) : PlacedSquare :=
  (match side with
    | .bottom => square
    | .top => square.reflectY 0
    | .left => square.swap
    | .right => square.swap.reflectY 0).firstQuadrant

lemma InnerBoundarySide.measurePreserving_canonicalPoint (side : InnerBoundarySide) :
    MeasurePreserving side.canonicalPoint volume volume := by
  cases side with
  | bottom => exact MeasurePreserving.id volume
  | top => exact measurePreserving_reflectYZero
  | left => exact measurePreserving_swapPlane
  | right => exact measurePreserving_reflectYZero.comp measurePreserving_swapPlane

lemma InnerBoundarySide.canonicalPoint_vertical
    (side : InnerBoundarySide) (point : Plane) :
    side.canonicalPoint point 1 = side.inwardNormal point := by
  cases side <;> simp [InnerBoundarySide.canonicalPoint, InnerBoundarySide.inwardNormal,
    Plane.reflectY, Plane.swap]

lemma InnerBoundarySide.canonicalPoint_boundaryPoint
    (side : InnerBoundarySide) (size : ℕ) (coordinate : ℝ) :
    side.canonicalPoint (side.toBoundarySide.pointAt size coordinate) =
      ![coordinate, side.inwardThreshold size] := by
  funext axis
  cases side <;> fin_cases axis <;>
    simp [InnerBoundarySide.canonicalPoint, InnerBoundarySide.inwardThreshold,
      InnerBoundarySide.toBoundarySide, NagamochiResource.BoundarySide.pointAt,
      Plane.reflectY, Plane.swap]

lemma InnerBoundarySide.mem_canonicalSquare_iff
    (side : InnerBoundarySide) (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor) (point : Plane) :
    side.canonicalPoint point ∈ (side.canonicalSquare square).dilatedInteriorRegion factor ↔
      point ∈ square.dilatedInteriorRegion factor := by
  cases side with
  | bottom =>
      exact congrArg (point ∈ ·) (square.firstQuadrant_dilatedInteriorRegion_eq factor_positive)
        |>.to_iff
  | top =>
      dsimp only [InnerBoundarySide.canonicalPoint, InnerBoundarySide.canonicalSquare]
      rw [(square.reflectY 0).firstQuadrant_dilatedInteriorRegion_eq factor_positive]
      simpa only [mul_zero] using square.mem_reflectY_dilatedInteriorRegion_iff
        (coordinateSum := 0) factor_positive point
  | left =>
      dsimp only [InnerBoundarySide.canonicalPoint, InnerBoundarySide.canonicalSquare]
      rw [square.swap.firstQuadrant_dilatedInteriorRegion_eq factor_positive]
      exact square.mem_swap_dilatedInteriorRegion_iff factor_positive point
  | right =>
      dsimp only [InnerBoundarySide.canonicalPoint, InnerBoundarySide.canonicalSquare]
      rw [(square.swap.reflectY 0).firstQuadrant_dilatedInteriorRegion_eq factor_positive]
      have reflected_equivalence := square.swap.mem_reflectY_dilatedInteriorRegion_iff
        (coordinateSum := 0) factor_positive point.swap
      simpa only [mul_zero, square.mem_swap_dilatedInteriorRegion_iff factor_positive] using
        reflected_equivalence

def boundaryCutRegion
    (side : InnerBoundarySide) (size : ℕ) (region : Set Plane) : Set Plane :=
  region ∩ {point | side.inwardNormal point < side.inwardThreshold size}

lemma boundaryCutRegion_volume_eq_canonical
    {size : ℕ} (side : InnerBoundarySide) (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor) :
    volume (boundaryCutRegion side size (square.dilatedInteriorRegion factor)) =
      volume ((side.canonicalSquare square).dilatedInteriorRegion factor ∩
        {point | point 1 < side.inwardThreshold size}) := by
  have preimage_identity :
      side.canonicalPoint ⁻¹'
          ((side.canonicalSquare square).dilatedInteriorRegion factor ∩
            {point | point 1 < side.inwardThreshold size}) =
        boundaryCutRegion side size (square.dilatedInteriorRegion factor) := by
    ext point
    simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, boundaryCutRegion,
      side.mem_canonicalSquare_iff square factor_positive,
      side.canonicalPoint_vertical]
  rw [← preimage_identity]
  apply side.measurePreserving_canonicalPoint.measure_preimage
  exact ((side.canonicalSquare square).measurableSet_dilatedInteriorRegion
    factor_positive.ne').inter (measurableSet_lt (measurable_pi_apply 1) measurable_const)
    |>.nullMeasurableSet

lemma boundaryLine_eq_canonical
    {size : ℕ} (side : InnerBoundarySide) (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor) :
    NagamochiResource.boundaryLine size side.toBoundarySide
        (square.dilatedInteriorRegion factor) =
      horizontalSegmentMeasure (9 / 10) ((size : ℝ) - 9 / 10)
        (side.inwardThreshold size) ((side.canonicalSquare square).dilatedInteriorRegion factor) := by
  have point_equivalence :
      ∀ coordinate : ℝ,
        side.toBoundarySide.pointAt size coordinate ∈ square.dilatedInteriorRegion factor ↔
          ![coordinate, side.inwardThreshold size] ∈
            (side.canonicalSquare square).dilatedInteriorRegion factor := by
    intro coordinate
    rw [← side.canonicalPoint_boundaryPoint size coordinate]
    exact (side.mem_canonicalSquare_iff square factor_positive _).symm
  have region_measurable := square.measurableSet_dilatedInteriorRegion factor_positive.ne'
  have canonical_measurable :=
    (side.canonicalSquare square).measurableSet_dilatedInteriorRegion factor_positive.ne'
  cases side <;>
    simp only [InnerBoundarySide.toBoundarySide, NagamochiResource.boundaryLine] <;>
    rw [horizontalSegmentMeasure_apply canonical_measurable]
  all_goals
    first
    | rw [horizontalSegmentMeasure_apply region_measurable]
    | rw [verticalSegmentMeasure_apply region_measurable]
    congr 1
    ext coordinate
    exact and_congr_right fun _ => point_equivalence coordinate

structure AdjacentBoundaryCut
    (size : ℕ) (square : PlacedSquare) (factor : ℝ) (side : InnerBoundarySide) : Prop where
  cosine_positive : 0 < (side.canonicalSquare square).frame.cosine
  sine_positive : 0 < (side.canonicalSquare square).frame.sine
  cap_positive :
    0 < horizontalCapHeight (side.canonicalSquare square) factor (side.inwardThreshold size)
  cap_le_cosine :
    horizontalCapHeight (side.canonicalSquare square) factor (side.inwardThreshold size) ≤
      factor * (side.canonicalSquare square).frame.cosine
  cap_le_sine :
    horizontalCapHeight (side.canonicalSquare square) factor (side.inwardThreshold size) ≤
      factor * (side.canonicalSquare square).frame.sine
  chord_inside_segment :
    Ioo ((side.canonicalSquare square).horizontalAdjacentChordStart factor
          (side.inwardThreshold size))
        ((side.canonicalSquare square).horizontalAdjacentChordEnd factor
          (side.inwardThreshold size)) ⊆
      Icc (9 / 10) ((size : ℝ) - 9 / 10)

lemma boundaryCut_compensated_of_adjacent
    {size : ℕ} (square : PlacedSquare) {factor : ℝ} (side : InnerBoundarySide)
    (factor_positive : 0 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (geometry : AdjacentBoundaryCut size square factor side) :
    volume (boundaryCutRegion side size (square.dilatedInteriorRegion factor)) ≤
      (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size side.toBoundarySide
        (square.dilatedInteriorRegion factor) := by
  rw [boundaryCutRegion_volume_eq_canonical side square factor_positive,
    boundaryLine_eq_canonical side square factor_positive]
  exact horizontalLowerCap_compensated (side.canonicalSquare square)
    factor_positive factor_at_most geometry.cosine_positive geometry.sine_positive
    geometry.cap_positive geometry.cap_le_cosine geometry.cap_le_sine
    geometry.chord_inside_segment

lemma boundaryCut_compensated_of_inside_or_adjacent
    {size : ℕ} (square : PlacedSquare) {factor : ℝ} (side : InnerBoundarySide)
    (factor_positive : 0 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (geometry :
      (∀ point ∈ square.dilatedInteriorRegion factor,
        side.inwardThreshold size ≤ side.inwardNormal point) ∨
      AdjacentBoundaryCut size square factor side) :
    volume (boundaryCutRegion side size (square.dilatedInteriorRegion factor)) ≤
      (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size side.toBoundarySide
        (square.dilatedInteriorRegion factor) := by
  rcases geometry with contained | adjacent
  · have empty_cut : boundaryCutRegion side size (square.dilatedInteriorRegion factor) = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro point point_mem
      exact not_lt_of_ge (contained point point_mem.1) point_mem.2
    rw [empty_cut, measure_empty]
    exact bot_le
  · exact boundaryCut_compensated_of_adjacent square side
      factor_positive factor_at_most adjacent

def boundarySideToInner : NagamochiResource.BoundarySide → InnerBoundarySide
  | .bottom => .bottom
  | .top => .top
  | .left => .left
  | .right => .right

@[simp] lemma boundarySideToInner_toBoundarySide (side : NagamochiResource.BoundarySide) :
    (boundarySideToInner side).toBoundarySide = side := by cases side <;> rfl

@[simp] lemma toBoundarySide_boundarySideToInner (side : InnerBoundarySide) :
    boundarySideToInner side.toBoundarySide = side := by cases side <;> rfl

lemma innerArea_add_boundaryCuts_covers_square
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_positive : 0 < factor) :
    ENNReal.ofReal (factor ^ 2) ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        ∑ side ∈ NagamochiResource.boundarySides,
          volume (boundaryCutRegion (boundarySideToInner side) size
            (square.dilatedInteriorRegion factor)) := by
  let region := square.dilatedInteriorRegion factor
  let cuts := fun side => boundaryCutRegion (boundarySideToInner side) size region
  have covered :
      region ⊆ (region ∩ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) ∪
        ⋃ side ∈ NagamochiResource.boundarySides, cuts side := by
    intro point point_mem
    by_cases point_inner : point ∈ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)
    · exact Or.inl ⟨point_mem, point_inner⟩
    · right
      have not_all_bounds :
          ¬ ∀ side : InnerBoundarySide,
            side.inwardThreshold size ≤ side.inwardNormal point := by
        exact fun all_bounds => point_inner
          ((mem_innerRectangle_iff_inward_bounds size point).2 all_bounds)
      obtain ⟨side, violated⟩ := not_forall.mp not_all_bounds
      apply mem_iUnion.2 ⟨side.toBoundarySide, ?_⟩
      apply mem_iUnion.2 ⟨NagamochiResource.mem_boundarySides side.toBoundarySide, ?_⟩
      change point ∈ boundaryCutRegion (boundarySideToInner side.toBoundarySide) size region
      rw [toBoundarySide_boundarySideToInner]
      exact ⟨point_mem, lt_of_not_ge violated⟩
  rw [← square.volume_dilatedInteriorRegion factor_positive.le,
    NagamochiResource.innerArea, Measure.restrict_apply
      (square.measurableSet_dilatedInteriorRegion factor_positive.ne')]
  exact (measure_mono covered).trans
    ((measure_union_le _ _).trans
      (add_le_add le_rfl (measure_biUnion_finset_le NagamochiResource.boundarySides cuts)))

lemma score_gt_one_of_adjacent_boundary_cuts
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (geometry : ∀ side : InnerBoundarySide,
      (∀ point ∈ square.dilatedInteriorRegion factor,
        side.inwardThreshold size ≤ side.inwardNormal point) ∨
      AdjacentBoundaryCut size square factor side) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  let region := square.dilatedInteriorRegion factor
  have cut_bounds : ∀ side : NagamochiResource.BoundarySide,
      volume (boundaryCutRegion (boundarySideToInner side) size region) ≤
        (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size side region := by
    intro side
    simpa only [boundarySideToInner_toBoundarySide] using
      boundaryCut_compensated_of_inside_or_adjacent square (boundarySideToInner side)
        factor_positive factor_at_most (geometry (boundarySideToInner side))
  apply score_gt_one_of_compensated_inner_area factor_gt_one
    (innerArea_add_boundaryCuts_covers_square square factor_positive)
  change (∑ side ∈ NagamochiResource.boundarySides,
      volume (boundaryCutRegion (boundarySideToInner side) size region)) ≤
    (1 / 2 : ENNReal) *
      ∑ side ∈ NagamochiResource.boundarySides, NagamochiResource.boundaryLine size side region
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun side _ => cut_bounds side

lemma innerHalfArea_add_otherBoundaryCuts_covers_square
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (exceptionalSide : NagamochiResource.BoundarySide)
    (factor_positive : 0 < factor)
    (center_inside :
      (boundarySideToInner exceptionalSide).inwardThreshold size ≤
        (boundarySideToInner exceptionalSide).inwardNormal (factor • square.center.toPlane)) :
    (1 / 2 : ENNReal) * ENNReal.ofReal (factor ^ 2) ≤
      NagamochiResource.innerArea size (square.dilatedInteriorRegion factor) +
        ∑ side ∈ NagamochiResource.boundarySides.erase exceptionalSide,
          volume (boundaryCutRegion (boundarySideToInner side) size
            (square.dilatedInteriorRegion factor)) := by
  classical
  let region := square.dilatedInteriorRegion factor
  let cuts := fun side => boundaryCutRegion (boundarySideToInner side) size region
  let halfSpace := {point : Plane |
    (boundarySideToInner exceptionalSide).inwardThreshold size ≤
      (boundarySideToInner exceptionalSide).inwardNormal point}
  have covered :
      region ∩ halfSpace ⊆ (region ∩ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)) ∪
        ⋃ side ∈ NagamochiResource.boundarySides.erase exceptionalSide, cuts side := by
    intro point point_mem
    by_cases point_inner : point ∈ Icc (fun _ => 1) (fun _ => (size : ℝ) - 1)
    · exact Or.inl ⟨point_mem.1, point_inner⟩
    · right
      have not_all_bounds : ¬ ∀ side : InnerBoundarySide,
          side.inwardThreshold size ≤ side.inwardNormal point := by
        exact fun all_bounds => point_inner
          ((mem_innerRectangle_iff_inward_bounds size point).2 all_bounds)
      obtain ⟨side, violated⟩ := not_forall.mp not_all_bounds
      have different : side.toBoundarySide ≠ exceptionalSide := by
        intro equality
        have side_equality : side = boundarySideToInner exceptionalSide := by
          rw [← equality, toBoundarySide_boundarySideToInner]
        exact violated (side_equality ▸ point_mem.2)
      apply mem_iUnion.2 ⟨side.toBoundarySide, ?_⟩
      apply mem_iUnion.2 ⟨Finset.mem_erase.mpr
        ⟨different, NagamochiResource.mem_boundarySides side.toBoundarySide⟩, ?_⟩
      change point ∈ boundaryCutRegion (boundarySideToInner side.toBoundarySide) size region
      rw [toBoundarySide_boundarySideToInner]
      exact ⟨point_mem.1, lt_of_not_ge violated⟩
  have half_bound := square.half_volume_le_volume_innerHalfSpace
    (boundarySideToInner exceptionalSide).inwardNormal factor_positive center_inside
  rw [NagamochiResource.innerArea, Measure.restrict_apply
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne')]
  exact half_bound.trans ((measure_mono covered).trans
    ((measure_union_le _ _).trans (add_le_add le_rfl
      (measure_biUnion_finset_le (NagamochiResource.boundarySides.erase exceptionalSide) cuts))))

lemma score_gt_one_of_long_chord_and_adjacent_boundary_cuts
    {size : ℕ} (square : PlacedSquare) {factor : ℝ}
    (exceptionalSide : NagamochiResource.BoundarySide)
    (factor_gt_one : 1 < factor)
    (factor_at_most : factor ≤ 101 / 100)
    (center_inside :
      (boundarySideToInner exceptionalSide).inwardThreshold size ≤
        (boundarySideToInner exceptionalSide).inwardNormal (factor • square.center.toPlane))
    (chord : NagamochiResource.HasBoundaryChord size exceptionalSide
      (square.dilatedInteriorRegion factor) factor)
    (other_geometry : ∀ side : NagamochiResource.BoundarySide, side ≠ exceptionalSide →
      (∀ point ∈ square.dilatedInteriorRegion factor,
        (boundarySideToInner side).inwardThreshold size ≤
          (boundarySideToInner side).inwardNormal point) ∨
      AdjacentBoundaryCut size square factor (boundarySideToInner side)) :
    1 < NagamochiResource.measure size (square.dilatedInteriorRegion factor) := by
  classical
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  let region := square.dilatedInteriorRegion factor
  let otherSides := NagamochiResource.boundarySides.erase exceptionalSide
  let loss := ∑ side ∈ otherSides,
    volume (boundaryCutRegion (boundarySideToInner side) size region)
  have loss_bound : loss ≤ (1 / 2 : ENNReal) *
      ∑ side ∈ otherSides, NagamochiResource.boundaryLine size side region := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro side side_mem
    simpa only [boundarySideToInner_toBoundarySide] using
      boundaryCut_compensated_of_inside_or_adjacent square (boundarySideToInner side)
        factor_positive factor_at_most
        (other_geometry side (Finset.mem_erase.mp side_mem).1)
  have half_bound : (1 / 2 : ENNReal) * ENNReal.ofReal factor ≤
      NagamochiResource.innerArea size region + loss :=
    (mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (by nlinarith)) bot_le bot_le).trans
      (innerHalfArea_add_otherBoundaryCuts_covers_square square exceptionalSide
        factor_positive center_inside)
  have chord_bound := NagamochiResource.boundaryLine_lower_bound_of_chord
    (square.measurableSet_dilatedInteriorRegion factor_positive.ne') chord
  have half_twice : (1 / 2 : ENNReal) * 2 = 1 := by
    rw [one_div]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  calc
    1 < ENNReal.ofReal factor := ENNReal.one_lt_ofReal.mpr factor_gt_one
    _ = (1 / 2 : ENNReal) * ENNReal.ofReal factor +
        (1 / 2 : ENNReal) * ENNReal.ofReal factor := by
      calc
        _ = ((1 / 2 : ENNReal) * 2) * ENNReal.ofReal factor := by rw [half_twice, one_mul]
        _ = _ := by ring
    _ ≤ (NagamochiResource.innerArea size region + loss) +
        (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size exceptionalSide region :=
      add_le_add half_bound (mul_le_mul le_rfl chord_bound bot_le bot_le)
    _ ≤ (NagamochiResource.innerArea size region +
        (1 / 2 : ENNReal) * ∑ side ∈ otherSides, NagamochiResource.boundaryLine size side region) +
        (1 / 2 : ENNReal) * NagamochiResource.boundaryLine size exceptionalSide region :=
      add_le_add (add_le_add le_rfl loss_bound) le_rfl
    _ = NagamochiResource.innerArea size region +
        NagamochiResource.boundaryLines size region := by
      change _ = NagamochiResource.innerArea size region +
        (1 / 2 : ENNReal) * ∑ side ∈ NagamochiResource.boundarySides,
          NagamochiResource.boundaryLine size side region
      rw [← Finset.sum_erase_add _ _ (NagamochiResource.mem_boundarySides exceptionalSide)]
      dsimp only [otherSides]
      ring
    _ ≤ NagamochiResource.measure size region :=
      NagamochiResource.innerArea_add_boundaryLines_le_measure size region

end SquarePackingArchive.Nagamochi
