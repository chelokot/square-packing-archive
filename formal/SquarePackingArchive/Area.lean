import SquarePackingArchive.Geometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace SquarePackingArchive

open Function MeasureTheory Set
open scoped Pointwise

abbrev Plane := Fin 2 → ℝ

def Frame.rotationMatrix (frame : Frame) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![frame.cosine, -frame.sine; frame.sine, frame.cosine]

def Frame.rotation (frame : Frame) : Plane →ₗ[ℝ] Plane :=
  Matrix.toLin' frame.rotationMatrix

lemma Frame.rotation_apply_zero (frame : Frame) (point : Plane) :
    frame.rotation point 0 = point 0 * frame.cosine - point 1 * frame.sine := by
  simp [Frame.rotation, Frame.rotationMatrix, Matrix.toLin'_apply,
    Matrix.vecHead, Matrix.vecTail, Function.comp_def]
  ring

lemma Frame.rotation_apply_one (frame : Frame) (point : Plane) :
    frame.rotation point 1 = point 0 * frame.sine + point 1 * frame.cosine := by
  simp [Frame.rotation, Frame.rotationMatrix, Matrix.toLin'_apply,
    Matrix.vecHead, Matrix.vecTail, Function.comp_def]
  ring

lemma Frame.rotation_det (frame : Frame) :
    LinearMap.det frame.rotation = 1 := by
  simp [Frame.rotation, Frame.rotationMatrix, Matrix.det_fin_two]
  nlinarith [frame.unit]

lemma Frame.map_rotation_volume (frame : Frame) :
    Measure.map frame.rotation volume = volume := by
  rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi]
  · rw [frame.rotation_det]
    norm_num
  · rw [frame.rotation_det]
    norm_num

def Point.toPlane (point : Point) : Plane :=
  ![point.x, point.y]

def Plane.toPoint (plane : Plane) : Point :=
  ⟨plane 0, plane 1⟩

@[simp] lemma Point.toPoint_toPlane (point : Point) :
    point.toPlane.toPoint = point := by
  rfl

@[simp] lemma Plane.toPlane_toPoint (plane : Plane) :
    plane.toPoint.toPlane = plane := by
  funext coordinate
  fin_cases coordinate <;> rfl

lemma Plane.toPoint_injective : Function.Injective Plane.toPoint := by
  intro left right equality
  rw [← left.toPlane_toPoint, equality, right.toPlane_toPoint]

def PlacedSquare.transform (square : PlacedSquare) (point : Plane) : Plane :=
  square.center.toPlane + square.frame.rotation point

lemma Frame.measurable_rotation (frame : Frame) :
    Measurable frame.rotation := by
  exact LinearMap.continuous_on_pi frame.rotation |>.measurable

lemma Frame.rotation_injective (frame : Frame) :
    Function.Injective frame.rotation := by
  intro left right equality
  have horizontal := congrFun equality 0
  have vertical := congrFun equality 1
  rw [frame.rotation_apply_zero, frame.rotation_apply_zero] at horizontal
  rw [frame.rotation_apply_one, frame.rotation_apply_one] at vertical
  funext coordinate
  fin_cases coordinate
  · change left 0 = right 0
    linear_combination
      frame.cosine * horizontal + frame.sine * vertical -
        (left 0 - right 0) * frame.unit
  · change left 1 = right 1
    linear_combination
      -frame.sine * horizontal + frame.cosine * vertical -
        (left 1 - right 1) * frame.unit

lemma Frame.isOpenMap_rotation (frame : Frame) :
    IsOpenMap frame.rotation := by
  apply LinearMap.isOpenMap_of_finiteDimensional
  exact LinearMap.injective_iff_surjective.mp frame.rotation_injective

lemma PlacedSquare.measurable_transform (square : PlacedSquare) :
    Measurable square.transform := by
  exact measurable_const.add square.frame.measurable_rotation

lemma PlacedSquare.transform_injective (square : PlacedSquare) :
    Function.Injective square.transform := by
  intro left right equality
  apply square.frame.rotation_injective
  exact add_left_cancel equality

lemma PlacedSquare.isOpenMap_transform (square : PlacedSquare) :
    IsOpenMap square.transform := by
  rw [show square.transform =
      (fun point => square.center.toPlane + point) ∘ square.frame.rotation by
        funext point
        rfl]
  exact (isOpenMap_add_left square.center.toPlane).comp square.frame.isOpenMap_rotation

lemma PlacedSquare.map_transform_volume (square : PlacedSquare) :
    Measure.map square.transform volume = volume := by
  rw [show square.transform =
      (fun point => square.center.toPlane + point) ∘ square.frame.rotation by
        funext point
        rfl]
  rw [← Measure.map_map]
  · rw [square.frame.map_rotation_volume]
    exact map_add_left_eq_self volume square.center.toPlane
  · exact measurable_const.add measurable_id
  · exact square.frame.measurable_rotation

def unitSquareInterior : Set Plane :=
  Set.pi univ fun _ => Ioo (-(1 / 2)) (1 / 2)

lemma isOpen_unitSquareInterior : IsOpen unitSquareInterior := by
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo

lemma volume_unitSquareInterior : volume unitSquareInterior = 1 := by
  rw [unitSquareInterior, Real.volume_pi_Ioo]
  norm_num

def PlacedSquare.interiorRegion (square : PlacedSquare) : Set Plane :=
  square.transform '' unitSquareInterior

lemma PlacedSquare.isOpen_interiorRegion (square : PlacedSquare) :
    IsOpen square.interiorRegion := by
  exact square.isOpenMap_transform unitSquareInterior isOpen_unitSquareInterior

lemma PlacedSquare.measurableSet_interiorRegion (square : PlacedSquare) :
    MeasurableSet square.interiorRegion :=
  square.isOpen_interiorRegion.measurableSet

lemma PlacedSquare.volume_interiorRegion (square : PlacedSquare) :
    volume square.interiorRegion = 1 := by
  have mapped := congrArg
    (fun measure : Measure Plane => measure square.interiorRegion)
    square.map_transform_volume
  rw [Measure.map_apply square.measurable_transform
    square.measurableSet_interiorRegion] at mapped
  simp only [PlacedSquare.interiorRegion] at mapped
  rw [square.transform_injective.preimage_image unitSquareInterior] at mapped
  rw [volume_unitSquareInterior] at mapped
  exact mapped.symm

lemma PlacedSquare.transform_toPoint (square : PlacedSquare) (coordinates : Plane) :
    (square.transform coordinates).toPoint =
      square.point (coordinates 0) (coordinates 1) := by
  simp [Plane.toPoint, PlacedSquare.transform, Point.toPlane,
    PlacedSquare.point, Frame.place, Frame.rotation_apply_zero,
    Frame.rotation_apply_one]

lemma PlacedSquare.mem_interiorRegion_iff
    (square : PlacedSquare) (point : Plane) :
    point ∈ square.interiorRegion ↔ square.InteriorContains point.toPoint := by
  constructor
  · rintro ⟨coordinates, coordinates_mem, rfl⟩
    refine ⟨coordinates 0, coordinates 1, ?_, ?_, square.transform_toPoint coordinates⟩
    · rw [abs_lt]
      exact coordinates_mem 0 (mem_univ 0)
    · rw [abs_lt]
      exact coordinates_mem 1 (mem_univ 1)
  · rintro ⟨localX, localY, localX_lt, localY_lt, point_eq⟩
    let coordinates : Plane := ![localX, localY]
    refine ⟨coordinates, ?_, ?_⟩
    · intro coordinate coordinate_mem
      fin_cases coordinate
      · exact abs_lt.mp localX_lt
      · exact abs_lt.mp localY_lt
    · apply Plane.toPoint_injective
      rw [square.transform_toPoint]
      simpa [coordinates] using point_eq.symm

lemma PlacedSquare.disjoint_interiorRegion
    {left right : PlacedSquare} (disjoint : left.InteriorDisjoint right) :
    Disjoint left.interiorRegion right.interiorRegion := by
  rw [Set.disjoint_left]
  intro point left_mem right_mem
  exact disjoint point.toPoint ⟨
    (left.mem_interiorRegion_iff point).mp left_mem,
    (right.mem_interiorRegion_iff point).mp right_mem⟩

def dilatePlane (factor : ℝ) (point : Plane) : Plane :=
  factor • point

lemma dilatePlane_injective {factor : ℝ} (factor_nonzero : factor ≠ 0) :
    Function.Injective (dilatePlane factor) := by
  intro left right equality
  funext coordinate
  have coordinate_equality := congrFun equality coordinate
  simp only [dilatePlane, Pi.smul_apply, smul_eq_mul] at coordinate_equality
  exact mul_left_cancel₀ factor_nonzero coordinate_equality

def PlacedSquare.dilatedInteriorRegion
    (square : PlacedSquare) (factor : ℝ) : Set Plane :=
  dilatePlane factor '' square.interiorRegion

lemma PlacedSquare.isOpen_dilatedInteriorRegion
    (square : PlacedSquare) {factor : ℝ} (factor_nonzero : factor ≠ 0) :
    IsOpen (square.dilatedInteriorRegion factor) := by
  exact (isOpenMap_smul₀ factor_nonzero) square.interiorRegion square.isOpen_interiorRegion

lemma PlacedSquare.measurableSet_dilatedInteriorRegion
    (square : PlacedSquare) {factor : ℝ} (factor_nonzero : factor ≠ 0) :
    MeasurableSet (square.dilatedInteriorRegion factor) :=
  (square.isOpen_dilatedInteriorRegion factor_nonzero).measurableSet

lemma PlacedSquare.volume_dilatedInteriorRegion
    (square : PlacedSquare) {factor : ℝ} (factor_nonnegative : 0 ≤ factor) :
    volume (square.dilatedInteriorRegion factor) = ENNReal.ofReal (factor ^ 2) := by
  rw [show square.dilatedInteriorRegion factor = factor • square.interiorRegion by rfl]
  rw [Measure.addHaar_smul_of_nonneg volume factor_nonnegative]
  rw [show Module.finrank ℝ Plane = 2 by simp [Plane]]
  rw [square.volume_interiorRegion, mul_one]

lemma PlacedSquare.disjoint_dilatedInteriorRegion
    {left right : PlacedSquare} {factor : ℝ}
    (disjoint : left.InteriorDisjoint right) (factor_nonzero : factor ≠ 0) :
    Disjoint (left.dilatedInteriorRegion factor) (right.dilatedInteriorRegion factor) := by
  rw [Set.disjoint_left]
  rintro point ⟨leftPoint, leftPoint_mem, leftPoint_eq⟩
    ⟨rightPoint, rightPoint_mem, rightPoint_eq⟩
  have source_equality : leftPoint = rightPoint :=
    dilatePlane_injective factor_nonzero (leftPoint_eq.trans rightPoint_eq.symm)
  subst rightPoint
  exact Set.disjoint_left.mp (PlacedSquare.disjoint_interiorRegion disjoint)
    leftPoint_mem rightPoint_mem

def containerRegion (side : ℝ) : Set Plane :=
  Icc (fun _ => 0) (fun _ => side)

lemma measurableSet_containerRegion (side : ℝ) :
    MeasurableSet (containerRegion side) := by
  exact measurableSet_Icc

lemma mem_containerRegion_iff (side : ℝ) (point : Plane) :
    point ∈ containerRegion side ↔ Container.Contains side point.toPoint := by
  constructor
  · rintro ⟨lower, upper⟩
    exact ⟨lower 0, upper 0, lower 1, upper 1⟩
  · rintro ⟨x_lower, x_upper, y_lower, y_upper⟩
    constructor <;> intro coordinate <;> fin_cases coordinate
    · exact x_lower
    · exact y_lower
    · exact x_upper
    · exact y_upper

lemma volume_containerRegion_toReal
    {side : ℝ} (side_nonnegative : 0 ≤ side) :
    (volume (containerRegion side)).toReal = side ^ 2 := by
  rw [containerRegion, Real.volume_Icc_pi_toReal]
  · simp
  · intro coordinate
    exact side_nonnegative

lemma PlacedSquare.interiorRegion_subset_containerRegion
    {square : PlacedSquare} {side : ℝ} (fits : square.Fits side) :
    square.interiorRegion ⊆ containerRegion side := by
  intro point point_mem
  rw [mem_containerRegion_iff]
  apply fits
  rcases (square.mem_interiorRegion_iff point).mp point_mem with
    ⟨localX, localY, localX_lt, localY_lt, point_eq⟩
  exact ⟨localX, localY, le_of_lt localX_lt, le_of_lt localY_lt, point_eq⟩

lemma PlacedSquare.dilatedInteriorRegion_subset_containerRegion
    {square : PlacedSquare} {sourceSide targetSide factor : ℝ}
    (fits : square.Fits sourceSide)
    (factor_nonnegative : 0 ≤ factor)
    (scaled_side_at_most : factor * sourceSide ≤ targetSide) :
    square.dilatedInteriorRegion factor ⊆ containerRegion targetSide := by
  intro point point_mem
  rcases point_mem with ⟨sourcePoint, sourcePoint_mem, rfl⟩
  have source_bounds := square.interiorRegion_subset_containerRegion fits sourcePoint_mem
  rcases source_bounds with ⟨source_lower, source_upper⟩
  constructor
  · intro coordinate
    exact mul_nonneg factor_nonnegative (source_lower coordinate)
  · intro coordinate
    exact (mul_le_mul_of_nonneg_left (source_upper coordinate) factor_nonnegative).trans
      scaled_side_at_most

theorem Packing.squareCount_le_side_sq
    {squareCount : ℕ} {side : ℝ} (packing : Packing squareCount side) :
    (squareCount : ℝ) ≤ side ^ 2 := by
  let regions : Fin squareCount → Set Plane :=
    fun index => (packing.squares index).interiorRegion
  have regions_measurable : ∀ index, MeasurableSet (regions index) :=
    fun index => (packing.squares index).measurableSet_interiorRegion
  have regions_disjoint : Pairwise (Disjoint on regions) := by
    intro left right different
    exact PlacedSquare.disjoint_interiorRegion
      (packing.disjoint left right different)
  have regions_subset : (⋃ index, regions index) ⊆ containerRegion side := by
    apply iUnion_subset
    intro index
    exact (packing.squares index).interiorRegion_subset_containerRegion
      (packing.fits index)
  have measure_bound : (squareCount : ENNReal) ≤ volume (containerRegion side) := by
    calc
      (squareCount : ENNReal) = ∑' index, volume (regions index) := by
        simp [regions, PlacedSquare.volume_interiorRegion]
      _ ≤ volume (⋃ index, regions index) :=
        tsum_meas_le_meas_iUnion_of_disjoint volume
          regions_measurable regions_disjoint
      _ ≤ volume (containerRegion side) := measure_mono regions_subset
  have container_ne_top : volume (containerRegion side) ≠ ⊤ := by
    rw [containerRegion, Real.volume_Icc_pi]
    simp
  have real_bound :=
    (ENNReal.toReal_le_toReal (by simp) container_ne_top).mpr measure_bound
  rw [ENNReal.toReal_natCast,
    volume_containerRegion_toReal packing.side_nonnegative] at real_bound
  exact real_bound

end SquarePackingArchive
