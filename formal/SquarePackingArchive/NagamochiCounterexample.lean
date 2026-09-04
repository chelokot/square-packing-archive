import SquarePackingArchive.NagamochiCutSymmetry
import SquarePackingArchive.Nagamochi

namespace SquarePackingArchive.Nagamochi

open MeasureTheory Set

noncomputable section

def deformationCounterexampleFactor : ℝ := 10001 / 10000

def deformationCounterexampleFrame : Frame where
  cosine := 80 / 1601
  sine := 1599 / 1601
  unit := by norm_num

def deformationCounterexampleVertexX : ℝ := 10419467 / 5330000

def deformationCounterexampleSquare : PlacedSquare where
  center :=
    ⟨(deformationCounterexampleVertexX + deformationCounterexampleFactor *
        ((80 / 1601 : ℝ) - 1599 / 1601) / 2) / deformationCounterexampleFactor,
      ((80 / 1601 : ℝ) + 1599 / 1601) / 2⟩
  frame := deformationCounterexampleFrame

def deformationCounterexampleRegion : Set Plane :=
  deformationCounterexampleSquare.dilatedInteriorRegion deformationCounterexampleFactor

lemma deformationCounterexample_factor_positive : 0 < deformationCounterexampleFactor := by
  norm_num [deformationCounterexampleFactor]

lemma deformationCounterexample_mem_iff (point : Plane) :
    point ∈ deformationCounterexampleRegion ↔
      (0 < 80 * (point 0 - deformationCounterexampleVertexX) + 1599 * point 1 ∧
        80 * (point 0 - deformationCounterexampleVertexX) + 1599 * point 1 <
          1601 * deformationCounterexampleFactor) ∧
      (0 < -1599 * (point 0 - deformationCounterexampleVertexX) + 80 * point 1 ∧
        -1599 * (point 0 - deformationCounterexampleVertexX) + 80 * point 1 <
          1601 * deformationCounterexampleFactor) := by
  constructor
  · intro point_mem
    obtain ⟨localX, localY, localX_bound, localY_bound, point_eq⟩ :=
      (deformationCounterexampleSquare.mem_dilatedInteriorRegion_iff
        deformationCounterexample_factor_positive point).1 point_mem
    have horizontal_eq := congrArg Point.x point_eq
    have vertical_eq := congrArg Point.y point_eq
    norm_num [Plane.toPoint, PlacedSquare.dilatedPoint, Frame.place,
      deformationCounterexampleSquare, deformationCounterexampleFrame,
      deformationCounterexampleFactor, deformationCounterexampleVertexX] at horizontal_eq vertical_eq localX_bound localY_bound ⊢
    rw [abs_lt] at localX_bound localY_bound
    constructor <;> constructor <;> linarith
  · intro bounds
    apply deformationCounterexampleSquare.mem_dilatedInteriorRegion_of_inverse_bounds
      deformationCounterexample_factor_positive
    all_goals
      norm_num [PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY,
        Plane.toPoint, deformationCounterexampleSquare, deformationCounterexampleFrame,
        deformationCounterexampleFactor, deformationCounterexampleVertexX] at bounds ⊢
      rw [abs_lt]
      constructor <;> linarith [bounds.1.1, bounds.1.2, bounds.2.1, bounds.2.2]

lemma deformationCounterexample_measurable : MeasurableSet deformationCounterexampleRegion :=
  deformationCounterexampleSquare.measurableSet_dilatedInteriorRegion
    deformationCounterexample_factor_positive.ne'

lemma deformationCounterexample_inside_container :
    deformationCounterexampleRegion ⊆ containerRegion 4 := by
  intro point point_mem
  have bounds := (deformationCounterexample_mem_iff point).1 point_mem
  rw [mem_containerRegion_iff]
  norm_num [Container.Contains, Plane.toPoint, deformationCounterexampleFactor,
    deformationCounterexampleVertexX] at bounds ⊢
  constructor
  · linarith [bounds.1.1, bounds.1.2, bounds.2.1, bounds.2.2]
  constructor
  · linarith [bounds.1.1, bounds.1.2, bounds.2.1, bounds.2.2]
  constructor <;> linarith [bounds.1.1, bounds.1.2, bounds.2.1, bounds.2.2]

lemma deformationCounterexample_closed_dilation_fits
    (localX localY : ℝ)
    (localX_bound : |localX| ≤ deformationCounterexampleFactor / 2)
    (localY_bound : |localY| ≤ deformationCounterexampleFactor / 2) :
    Container.Contains 4 (deformationCounterexampleSquare.dilatedPoint
      deformationCounterexampleFactor localX localY) := by
  rw [abs_le] at localX_bound localY_bound
  norm_num [Container.Contains, PlacedSquare.dilatedPoint, Frame.place,
    deformationCounterexampleSquare, deformationCounterexampleFrame,
    deformationCounterexampleFactor, deformationCounterexampleVertexX] at localX_bound localY_bound ⊢
  constructor
  · linarith [localX_bound.1, localY_bound.2]
  constructor
  · linarith [localX_bound.2, localY_bound.1]
  constructor
  · linarith [localX_bound.1, localY_bound.1]
  · linarith [localX_bound.2, localY_bound.2]

lemma deformationCounterexample_fits :
    deformationCounterexampleSquare.Fits ((4 : ℝ) / deformationCounterexampleFactor) := by
  intro point point_mem
  obtain ⟨localX, localY, localX_bound, localY_bound, rfl⟩ := point_mem
  rw [abs_le] at localX_bound localY_bound
  norm_num [Container.Contains, PlacedSquare.point, Frame.place,
    deformationCounterexampleSquare, deformationCounterexampleFrame,
    deformationCounterexampleFactor, deformationCounterexampleVertexX] at localX_bound localY_bound ⊢
  constructor
  · linarith [localX_bound.1, localY_bound.2]
  constructor
  · linarith [localX_bound.2, localY_bound.1]
  constructor
  · linarith [localX_bound.1, localY_bound.1]
  · linarith [localX_bound.2, localY_bound.2]

lemma deformationCounterexample_corner_points :
    NagamochiResource.cornerPoints 4 deformationCounterexampleRegion = 9 / 20 := by
  simp [NagamochiResource.cornerPoints, NagamochiResource.cornerPointKinds,
    Measure.dirac_apply' _ deformationCounterexample_measurable,
    NagamochiResource.cornerPoint]
  norm_num [Set.indicator_apply, deformationCounterexample_mem_iff,
    deformationCounterexampleFactor, deformationCounterexampleVertexX]

lemma deformationCounterexample_edge_points :
    NagamochiResource.edgePoints 4 deformationCounterexampleRegion = 0 := by
  norm_num [NagamochiResource.edgePoints, NagamochiResource.edgePointCluster,
    NagamochiResource.edgePointKinds,
    Measure.dirac_apply' _ deformationCounterexample_measurable,
    Set.indicator_apply, deformationCounterexample_mem_iff, NagamochiResource.edgePoint,
    deformationCounterexampleFactor, deformationCounterexampleVertexX]

lemma deformationCounterexample_bottom_line :
    NagamochiResource.boundaryLine 4 .bottom deformationCounterexampleRegion ≤ 1 := by
  rw [NagamochiResource.boundaryLine,
    horizontalSegmentMeasure_apply deformationCounterexample_measurable]
  have subset_interval :
      Icc (9 / 10 : ℝ) (4 - 9 / 10) ∩
        (fun coordinate : ℝ => ![coordinate, 1]) ⁻¹' deformationCounterexampleRegion ⊆
      Icc (1 : ℝ) 2 := by
    intro coordinate coordinate_mem
    have bounds := (deformationCounterexample_mem_iff ![coordinate, 1]).1 coordinate_mem.2
    norm_num [deformationCounterexampleFactor, deformationCounterexampleVertexX] at bounds
    constructor <;> linarith [bounds.1.1, bounds.1.2, bounds.2.1, bounds.2.2]
  calc
    _ ≤ volume (Icc (1 : ℝ) 2) := measure_mono subset_interval
    _ = 1 := by norm_num [Real.volume_Icc]

lemma deformationCounterexample_left_line :
    NagamochiResource.boundaryLine 4 .left deformationCounterexampleRegion ≤ 3 / 100 := by
  rw [NagamochiResource.boundaryLine,
    verticalSegmentMeasure_apply deformationCounterexample_measurable]
  have subset_interval :
      Icc (9 / 10 : ℝ) (4 - 9 / 10) ∩
        (fun coordinate : ℝ => ![1, coordinate]) ⁻¹' deformationCounterexampleRegion ⊆
      Icc (9 / 10 : ℝ) (93 / 100) := by
    intro coordinate coordinate_mem
    have bounds := (deformationCounterexample_mem_iff ![1, coordinate]).1 coordinate_mem.2
    norm_num [deformationCounterexampleFactor, deformationCounterexampleVertexX] at bounds
    exact ⟨coordinate_mem.1.1, by linarith [bounds.2.2]⟩
  calc
    _ ≤ volume (Icc (9 / 10 : ℝ) (93 / 100)) := measure_mono subset_interval
    _ = 3 / 100 := by norm_num [Real.volume_Icc, ENNReal.ofReal_div_of_pos]

lemma deformationCounterexample_top_line :
    NagamochiResource.boundaryLine 4 .top deformationCounterexampleRegion = 0 := by
  rw [NagamochiResource.boundaryLine,
    horizontalSegmentMeasure_apply deformationCounterexample_measurable]
  have empty_intersection :
      Icc (9 / 10 : ℝ) (4 - 9 / 10) ∩
        (fun coordinate : ℝ => ![coordinate, 4 - 1]) ⁻¹' deformationCounterexampleRegion =
      ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro coordinate coordinate_mem
    have bounds := (deformationCounterexample_mem_iff ![coordinate, 4 - 1]).1 coordinate_mem.2
    norm_num [deformationCounterexampleFactor, deformationCounterexampleVertexX] at bounds
    linarith [bounds.1.1, bounds.1.2, bounds.2.1, bounds.2.2]
  norm_num only [Nat.cast_ofNat, show (4 : ℝ) - 1 = 3 by norm_num] at empty_intersection ⊢
  rw [empty_intersection, measure_empty]

lemma deformationCounterexample_right_line :
    NagamochiResource.boundaryLine 4 .right deformationCounterexampleRegion = 0 := by
  rw [NagamochiResource.boundaryLine,
    verticalSegmentMeasure_apply deformationCounterexample_measurable]
  have empty_intersection :
      Icc (9 / 10 : ℝ) (4 - 9 / 10) ∩
        (fun coordinate : ℝ => ![4 - 1, coordinate]) ⁻¹' deformationCounterexampleRegion =
      ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro coordinate coordinate_mem
    have bounds := (deformationCounterexample_mem_iff ![4 - 1, coordinate]).1 coordinate_mem.2
    norm_num [deformationCounterexampleFactor, deformationCounterexampleVertexX] at bounds
    linarith [bounds.1.1, bounds.1.2, bounds.2.1, bounds.2.2]
  norm_num only [Nat.cast_ofNat, show (4 : ℝ) - 1 = 3 by norm_num] at empty_intersection ⊢
  rw [empty_intersection, measure_empty]

lemma deformationCounterexample_inner_area :
    NagamochiResource.innerArea 4 deformationCounterexampleRegion ≤ 3 / 100 := by
  let canonical := InnerBoundarySide.top.canonicalSquare deformationCounterexampleSquare
  have canonical_cosine : canonical.frame.cosine = 1599 / 1601 := by
    norm_num [canonical, InnerBoundarySide.canonicalSquare, PlacedSquare.firstQuadrant,
      PlacedSquare.reflectY, Frame.reflectY, PlacedSquare.rotateQuarter, Frame.rotateQuarter,
      deformationCounterexampleSquare, deformationCounterexampleFrame]
  have canonical_sine : canonical.frame.sine = 80 / 1601 := by
    norm_num [canonical, InnerBoundarySide.canonicalSquare, PlacedSquare.firstQuadrant,
      PlacedSquare.reflectY, Frame.reflectY, PlacedSquare.rotateQuarter, Frame.rotateQuarter,
      deformationCounterexampleSquare, deformationCounterexampleFrame]
  have canonical_center : canonical.center.y = -1679 / 3202 := by
    norm_num [canonical, InnerBoundarySide.canonicalSquare, PlacedSquare.firstQuadrant,
      PlacedSquare.reflectY, Frame.reflectY, PlacedSquare.rotateQuarter, Frame.rotateQuarter,
      Point.reflectY, deformationCounterexampleSquare, deformationCounterexampleFrame]
  let cap := canonical.dilatedInteriorRegion deformationCounterexampleFactor ∩
    {point | point 1 < (-999 / 1000 : ℝ)}
  have cap_measurable : MeasurableSet cap :=
    (canonical.measurableSet_dilatedInteriorRegion
      deformationCounterexample_factor_positive.ne').inter
      (measurableSet_lt (measurable_pi_apply 1) measurable_const)
  have subset_cap :
      deformationCounterexampleRegion ∩ Icc (fun _ => (1 : ℝ)) (fun _ => (4 : ℝ) - 1) ⊆
      InnerBoundarySide.top.canonicalPoint ⁻¹' cap := by
    intro point point_mem
    refine ⟨(InnerBoundarySide.top.mem_canonicalSquare_iff deformationCounterexampleSquare
      deformationCounterexample_factor_positive point).2 point_mem.1, ?_⟩
    have vertical_lower := point_mem.2.1 (1 : Fin 2)
    change 1 ≤ point 1 at vertical_lower
    change InnerBoundarySide.top.canonicalPoint point 1 < (-999 / 1000 : ℝ)
    simp only [InnerBoundarySide.canonicalPoint, Plane.reflectY, Matrix.cons_val_one,
      Matrix.cons_val_zero, zero_sub]
    linarith
  have cosine_positive : 0 < canonical.frame.cosine := by rw [canonical_cosine]; norm_num
  have sine_positive : 0 < canonical.frame.sine := by rw [canonical_sine]; norm_num
  have cap_positive :
      0 < horizontalCapHeight canonical deformationCounterexampleFactor (-999 / 1000) := by
    norm_num [horizontalCapHeight, canonical_center, canonical_cosine, canonical_sine,
      deformationCounterexampleFactor]
  rw [NagamochiResource.innerArea,
    Measure.restrict_apply deformationCounterexample_measurable]
  calc
    _ ≤ volume (InnerBoundarySide.top.canonicalPoint ⁻¹' cap) := measure_mono subset_cap
    _ = volume cap := InnerBoundarySide.top.measurePreserving_canonicalPoint.measure_preimage
      cap_measurable.nullMeasurableSet
    _ ≤ ENNReal.ofReal
        ((horizontalCapHeight canonical deformationCounterexampleFactor (-999 / 1000) /
            canonical.frame.sine) *
          (horizontalCapHeight canonical deformationCounterexampleFactor (-999 / 1000) /
            canonical.frame.cosine) / 2) :=
      volume_horizontalLowerCap_le canonical deformationCounterexample_factor_positive
        cosine_positive sine_positive cap_positive
    _ ≤ 3 / 100 := by
      have rational_bound : ENNReal.ofReal
          ((horizontalCapHeight canonical deformationCounterexampleFactor (-999 / 1000) /
              canonical.frame.sine) *
            (horizontalCapHeight canonical deformationCounterexampleFactor (-999 / 1000) /
              canonical.frame.cosine) / 2) ≤ ENNReal.ofReal (3 / 100 : ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        norm_num [horizontalCapHeight, canonical_center, canonical_cosine, canonical_sine,
          deformationCounterexampleFactor]
      simpa [ENNReal.ofReal_div_of_pos] using rational_bound

lemma deformationCounterexample_boundary_lines :
    NagamochiResource.boundaryLines 4 deformationCounterexampleRegion ≤
      ENNReal.ofReal (103 / 200 : ℝ) := by
  have bottom_bound : NagamochiResource.boundaryLine 4 .bottom
      deformationCounterexampleRegion ≤ ENNReal.ofReal (1 : ℝ) := by
    simpa using deformationCounterexample_bottom_line
  have left_bound : NagamochiResource.boundaryLine 4 .left
      deformationCounterexampleRegion ≤ ENNReal.ofReal (3 / 100 : ℝ) := by
    simpa [ENNReal.ofReal_div_of_pos] using deformationCounterexample_left_line
  have boundary_eq : NagamochiResource.boundaryLines 4 deformationCounterexampleRegion =
      ENNReal.ofReal (1 / 2 : ℝ) *
        (NagamochiResource.boundaryLine 4 .bottom deformationCounterexampleRegion +
          NagamochiResource.boundaryLine 4 .left deformationCounterexampleRegion) := by
    simp [NagamochiResource.boundaryLines, NagamochiResource.boundarySides,
      deformationCounterexample_top_line, deformationCounterexample_right_line,
      mul_add]
  rw [boundary_eq]
  calc
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) *
        (ENNReal.ofReal (1 : ℝ) + ENNReal.ofReal (3 / 100 : ℝ)) :=
      mul_le_mul le_rfl (add_le_add bottom_bound left_bound) bot_le bot_le
    _ = ENNReal.ofReal (103 / 200 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

theorem deformationCounterexample_score_le :
    NagamochiResource.measure 4 deformationCounterexampleRegion ≤
      ENNReal.ofReal (199 / 200 : ℝ) := by
  have area_bound : NagamochiResource.innerArea 4 deformationCounterexampleRegion ≤
      ENNReal.ofReal (3 / 100 : ℝ) := by
    simpa [ENNReal.ofReal_div_of_pos] using deformationCounterexample_inner_area
  have corners_eq : NagamochiResource.cornerPoints 4 deformationCounterexampleRegion =
      ENNReal.ofReal (9 / 20 : ℝ) := by
    simpa [ENNReal.ofReal_div_of_pos] using deformationCounterexample_corner_points
  simp only [NagamochiResource.measure, Measure.coe_add, Pi.add_apply,
    deformationCounterexample_edge_points, add_zero, corners_eq]
  calc
    _ ≤ ENNReal.ofReal (3 / 100 : ℝ) + ENNReal.ofReal (103 / 200 : ℝ) +
        ENNReal.ofReal (9 / 20 : ℝ) :=
      add_le_add (add_le_add area_bound deformationCounterexample_boundary_lines) le_rfl
    _ = ENNReal.ofReal (199 / 200 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num

theorem not_scoresDilatedSquares_four : ¬ NagamochiResource.ScoresDilatedSquares 4 := by
  intro scores
  have lower := scores deformationCounterexampleFactor deformationCounterexampleSquare
    (by norm_num [deformationCounterexampleFactor])
    (by norm_num [deformationCounterexampleFactor]) deformationCounterexample_inside_container
  have upper : NagamochiResource.measure 4 deformationCounterexampleRegion < 1 :=
    deformationCounterexample_score_le.trans_lt (by
      rw [ENNReal.ofReal_lt_one]
      norm_num)
  exact (lt_asymm lower upper)

end

end SquarePackingArchive.Nagamochi
