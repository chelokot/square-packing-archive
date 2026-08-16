import SquarePackingArchive.Geometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace SquarePackingArchive

open Function MeasureTheory Set
open scoped Pointwise

abbrev Plane := Fin 2 → ℝ

def Plane.swap (point : Plane) : Plane :=
  ![point 1, point 0]

@[simp] lemma Plane.swap_swap (point : Plane) :
    point.swap.swap = point := by
  funext coordinate
  fin_cases coordinate <;> rfl

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

@[simp] lemma Plane.toPoint_swap (plane : Plane) :
    plane.swap.toPoint = plane.toPoint.swap := by
  rfl

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

def PlacedSquare.affineTransform (square : PlacedSquare) : Plane →ᵃ[ℝ] Plane where
  toFun := square.transform
  linear := square.frame.rotation
  map_vadd' := by
    intro point vector
    simp [PlacedSquare.transform, map_add]
    abel

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

lemma convex_unitSquareInterior : Convex ℝ unitSquareInterior := by
  rw [unitSquareInterior]
  apply convex_pi
  intro coordinate coordinate_mem
  exact convex_Ioo _ _

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

lemma PlacedSquare.convex_interiorRegion (square : PlacedSquare) :
    Convex ℝ square.interiorRegion := by
  simpa [PlacedSquare.interiorRegion, PlacedSquare.affineTransform] using
    convex_unitSquareInterior.affine_image square.affineTransform

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

lemma PlacedSquare.convex_dilatedInteriorRegion
    (square : PlacedSquare) (factor : ℝ) :
    Convex ℝ (square.dilatedInteriorRegion factor) := by
  exact square.convex_interiorRegion.smul factor

lemma horizontal_openSegment_subset_of_convex
    {region : Set Plane} (region_convex : Convex ℝ region)
    {left right height : ℝ} (left_lt_right : left < right)
    (left_mem : ![left, height] ∈ region)
    (right_mem : ![right, height] ∈ region) :
    ∀ coordinate ∈ Ioo left right, ![coordinate, height] ∈ region := by
  intro coordinate coordinate_mem
  let ratio := (coordinate - left) / (right - left)
  have denominator_positive : 0 < right - left := sub_pos.mpr left_lt_right
  have ratio_mem : ratio ∈ Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [ratio]
      exact div_nonneg (sub_nonneg.mpr coordinate_mem.1.le)
        denominator_positive.le
    · dsimp [ratio]
      rw [div_le_one denominator_positive]
      linarith [coordinate_mem.2]
  have line_mem := region_convex.lineMap_mem left_mem right_mem ratio_mem
  convert line_mem using 1
  funext index
  fin_cases index
  · simp [AffineMap.lineMap_apply_module, ratio]
    field_simp [ne_of_gt denominator_positive]
    ring
  · simp [AffineMap.lineMap_apply_module]
    ring

lemma vertical_openSegment_subset_of_convex
    {region : Set Plane} (region_convex : Convex ℝ region)
    {bottom top width : ℝ} (bottom_lt_top : bottom < top)
    (bottom_mem : ![width, bottom] ∈ region)
    (top_mem : ![width, top] ∈ region) :
    ∀ coordinate ∈ Ioo bottom top, ![width, coordinate] ∈ region := by
  intro coordinate coordinate_mem
  let ratio := (coordinate - bottom) / (top - bottom)
  have denominator_positive : 0 < top - bottom := sub_pos.mpr bottom_lt_top
  have ratio_mem : ratio ∈ Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [ratio]
      exact div_nonneg (sub_nonneg.mpr coordinate_mem.1.le)
        denominator_positive.le
    · dsimp [ratio]
      rw [div_le_one denominator_positive]
      linarith [coordinate_mem.2]
  have line_mem := region_convex.lineMap_mem bottom_mem top_mem ratio_mem
  convert line_mem using 1
  funext index
  fin_cases index
  · simp [AffineMap.lineMap_apply_module]
    ring
  · simp [AffineMap.lineMap_apply_module, ratio]
    field_simp [ne_of_gt denominator_positive]
    ring

def PlacedSquare.dilatedPoint
    (square : PlacedSquare) (factor localX localY : ℝ) : Point :=
  let offset := square.frame.place localX localY
  ⟨factor * square.center.x + offset.x,
    factor * square.center.y + offset.y⟩

def PlacedSquare.DilatedInteriorContains
    (square : PlacedSquare) (factor : ℝ) (point : Point) : Prop :=
  ∃ localX localY : ℝ,
    |localX| < factor / 2 ∧
      |localY| < factor / 2 ∧
        point = square.dilatedPoint factor localX localY

lemma PlacedSquare.swap_dilatedPoint
    (square : PlacedSquare) (factor localX localY : ℝ) :
    square.swap.dilatedPoint factor localX localY =
      (square.dilatedPoint factor localX (-localY)).swap := by
  rw [Point.mk.injEq]
  constructor
  · simp [PlacedSquare.swap, Point.swap, Frame.swap,
      PlacedSquare.dilatedPoint, Frame.place]
    ring
  · simp [PlacedSquare.swap, Point.swap, Frame.swap,
      PlacedSquare.dilatedPoint, Frame.place]

lemma PlacedSquare.rotateQuarter_dilatedPoint
    (square : PlacedSquare) (factor localX localY : ℝ) :
    square.rotateQuarter.dilatedPoint factor localX localY =
      square.dilatedPoint factor (-localY) localX := by
  rw [Point.mk.injEq]
  constructor
  · simp [PlacedSquare.rotateQuarter, Frame.rotateQuarter,
      PlacedSquare.dilatedPoint, Frame.place]
    ring
  · simp [PlacedSquare.rotateQuarter, Frame.rotateQuarter,
      PlacedSquare.dilatedPoint, Frame.place]
    ring

lemma PlacedSquare.dilatedInteriorContains_swap_iff
    (square : PlacedSquare) (factor : ℝ) (point : Point) :
    square.swap.DilatedInteriorContains factor point.swap ↔
      square.DilatedInteriorContains factor point := by
  constructor
  · rintro ⟨localX, localY, localX_bound, localY_bound, point_eq⟩
    refine ⟨localX, -localY, localX_bound, ?_, ?_⟩
    · simpa only [abs_neg] using localY_bound
    · apply Point.swap_injective
      rw [← square.swap_dilatedPoint]
      exact point_eq
  · rintro ⟨localX, localY, localX_bound, localY_bound, point_eq⟩
    refine ⟨localX, -localY, localX_bound, ?_, ?_⟩
    · simpa only [abs_neg] using localY_bound
    · rw [square.swap_dilatedPoint, neg_neg, point_eq]

lemma PlacedSquare.dilatedInteriorContains_rotateQuarter_iff
    (square : PlacedSquare) (factor : ℝ) (point : Point) :
    square.rotateQuarter.DilatedInteriorContains factor point ↔
      square.DilatedInteriorContains factor point := by
  constructor
  · rintro ⟨localX, localY, localX_bound, localY_bound, point_eq⟩
    refine ⟨-localY, localX, ?_, localX_bound, ?_⟩
    · simpa only [abs_neg] using localY_bound
    · exact point_eq.trans (square.rotateQuarter_dilatedPoint factor localX localY)
  · rintro ⟨localX, localY, localX_bound, localY_bound, point_eq⟩
    refine ⟨localY, -localX, localY_bound, ?_, ?_⟩
    · simpa only [abs_neg] using localX_bound
    · exact point_eq.trans
        (by simpa only [neg_neg] using
          (square.rotateQuarter_dilatedPoint factor localY (-localX)).symm)

lemma PlacedSquare.mem_dilatedInteriorRegion_iff
    (square : PlacedSquare) {factor : ℝ} (factor_positive : 0 < factor)
    (point : Plane) :
    point ∈ square.dilatedInteriorRegion factor ↔
      square.DilatedInteriorContains factor point.toPoint := by
  constructor
  · rintro ⟨sourcePoint, sourcePoint_mem, rfl⟩
    rcases (square.mem_interiorRegion_iff sourcePoint).mp sourcePoint_mem with
      ⟨localX, localY, localX_bound, localY_bound, sourcePoint_eq⟩
    refine ⟨factor * localX, factor * localY, ?_, ?_, ?_⟩
    · rw [abs_mul, abs_of_pos factor_positive]
      nlinarith
    · rw [abs_mul, abs_of_pos factor_positive]
      nlinarith
    · rw [Point.mk.injEq]
      constructor
      · have source_x := congrArg Point.x sourcePoint_eq
        simp only [Plane.toPoint, PlacedSquare.point, Frame.place] at source_x
        simp only [dilatePlane, Pi.smul_apply, smul_eq_mul, Plane.toPoint,
          PlacedSquare.dilatedPoint, Frame.place]
        nlinarith
      · have source_y := congrArg Point.y sourcePoint_eq
        simp only [Plane.toPoint, PlacedSquare.point, Frame.place] at source_y
        simp only [dilatePlane, Pi.smul_apply, smul_eq_mul, Plane.toPoint,
          PlacedSquare.dilatedPoint, Frame.place]
        nlinarith
  · rintro ⟨localX, localY, localX_bound, localY_bound, point_eq⟩
    let sourceX := localX / factor
    let sourceY := localY / factor
    have sourceX_bound : |sourceX| < 1 / 2 := by
      dsimp [sourceX]
      rw [abs_div, abs_of_pos factor_positive]
      rw [div_lt_iff₀ factor_positive]
      nlinarith
    have sourceY_bound : |sourceY| < 1 / 2 := by
      dsimp [sourceY]
      rw [abs_div, abs_of_pos factor_positive]
      rw [div_lt_iff₀ factor_positive]
      nlinarith
    let sourcePoint := square.transform ![sourceX, sourceY]
    have sourcePoint_mem : sourcePoint ∈ square.interiorRegion := by
      rw [square.mem_interiorRegion_iff]
      refine ⟨sourceX, sourceY, sourceX_bound, sourceY_bound, ?_⟩
      exact square.transform_toPoint ![sourceX, sourceY]
    refine ⟨sourcePoint, sourcePoint_mem, ?_⟩
    apply Plane.toPoint_injective
    rw [point_eq]
    rw [Point.mk.injEq]
    constructor
    · simp only [Plane.toPoint, dilatePlane, Pi.smul_apply, smul_eq_mul,
        sourcePoint, PlacedSquare.transform, Point.toPlane,
        PlacedSquare.dilatedPoint, Frame.place]
      dsimp [sourceX, sourceY]
      rw [square.frame.rotation_apply_zero]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp [factor_positive.ne']
    · simp only [Plane.toPoint, dilatePlane, Pi.smul_apply, smul_eq_mul,
        sourcePoint, PlacedSquare.transform, Point.toPlane,
        PlacedSquare.dilatedPoint, Frame.place]
      dsimp [sourceX, sourceY]
      rw [square.frame.rotation_apply_one]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      field_simp [factor_positive.ne']

lemma PlacedSquare.horizontalPoint_mem_swap_iff
    (square : PlacedSquare) {factor coordinate height : ℝ}
    (factor_positive : 0 < factor) :
    ![coordinate, height] ∈ square.swap.dilatedInteriorRegion factor ↔
      ![height, coordinate] ∈ square.dilatedInteriorRegion factor := by
  rw [square.swap.mem_dilatedInteriorRegion_iff factor_positive,
    square.mem_dilatedInteriorRegion_iff factor_positive]
  simpa [Plane.toPoint, Point.swap] using
    square.dilatedInteriorContains_swap_iff factor
      (Plane.toPoint ![height, coordinate])

lemma PlacedSquare.mem_swap_dilatedInteriorRegion_iff
    (square : PlacedSquare) {factor : ℝ} (factor_positive : 0 < factor)
    (point : Plane) :
    point.swap ∈ square.swap.dilatedInteriorRegion factor ↔
      point ∈ square.dilatedInteriorRegion factor := by
  rw [square.swap.mem_dilatedInteriorRegion_iff factor_positive,
    square.mem_dilatedInteriorRegion_iff factor_positive]
  rw [Plane.toPoint_swap]
  exact square.dilatedInteriorContains_swap_iff factor point.toPoint

lemma PlacedSquare.rotateQuarter_dilatedInteriorRegion_eq
    (square : PlacedSquare) {factor : ℝ} (factor_positive : 0 < factor) :
    square.rotateQuarter.dilatedInteriorRegion factor =
      square.dilatedInteriorRegion factor := by
  ext point
  rw [square.rotateQuarter.mem_dilatedInteriorRegion_iff factor_positive,
    square.mem_dilatedInteriorRegion_iff factor_positive]
  exact square.dilatedInteriorContains_rotateQuarter_iff factor point.toPoint

lemma PlacedSquare.rotateHalf_dilatedInteriorRegion_eq
    (square : PlacedSquare) {factor : ℝ} (factor_positive : 0 < factor) :
    square.rotateHalf.dilatedInteriorRegion factor =
      square.dilatedInteriorRegion factor := by
  rw [PlacedSquare.rotateHalf,
    square.rotateQuarter.rotateQuarter_dilatedInteriorRegion_eq factor_positive,
    square.rotateQuarter_dilatedInteriorRegion_eq factor_positive]

lemma PlacedSquare.rotateThreeQuarter_dilatedInteriorRegion_eq
    (square : PlacedSquare) {factor : ℝ} (factor_positive : 0 < factor) :
    square.rotateThreeQuarter.dilatedInteriorRegion factor =
      square.dilatedInteriorRegion factor := by
  rw [PlacedSquare.rotateThreeQuarter,
    square.rotateHalf.rotateQuarter_dilatedInteriorRegion_eq factor_positive,
    square.rotateHalf_dilatedInteriorRegion_eq factor_positive]

lemma PlacedSquare.firstQuadrant_dilatedInteriorRegion_eq
    (square : PlacedSquare) {factor : ℝ} (factor_positive : 0 < factor) :
    square.firstQuadrant.dilatedInteriorRegion factor =
      square.dilatedInteriorRegion factor := by
  simp only [PlacedSquare.firstQuadrant]
  split_ifs
  · rfl
  · exact square.rotateQuarter_dilatedInteriorRegion_eq factor_positive
  · exact square.rotateThreeQuarter_dilatedInteriorRegion_eq factor_positive
  · exact square.rotateHalf_dilatedInteriorRegion_eq factor_positive

def PlacedSquare.dilatedLocalX
    (square : PlacedSquare) (factor : ℝ) (point : Point) : ℝ :=
  (point.x - factor * square.center.x) * square.frame.cosine +
    (point.y - factor * square.center.y) * square.frame.sine

def PlacedSquare.dilatedLocalY
    (square : PlacedSquare) (factor : ℝ) (point : Point) : ℝ :=
  -(point.x - factor * square.center.x) * square.frame.sine +
    (point.y - factor * square.center.y) * square.frame.cosine

lemma PlacedSquare.dilatedPoint_inverseCoordinates
    (square : PlacedSquare) (factor : ℝ) (point : Point) :
    square.dilatedPoint factor
        (square.dilatedLocalX factor point)
        (square.dilatedLocalY factor point) = point := by
  rw [Point.mk.injEq]
  constructor
  · simp only [PlacedSquare.dilatedPoint, Frame.place,
      PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY]
    linear_combination
      (point.x - factor * square.center.x) * square.frame.unit
  · simp only [PlacedSquare.dilatedPoint, Frame.place,
      PlacedSquare.dilatedLocalX, PlacedSquare.dilatedLocalY]
    linear_combination
      (point.y - factor * square.center.y) * square.frame.unit

lemma PlacedSquare.mem_dilatedInteriorRegion_of_inverse_bounds
    (square : PlacedSquare) {factor : ℝ} (factor_positive : 0 < factor)
    (point : Plane)
    (localX_bound : |square.dilatedLocalX factor point.toPoint| < factor / 2)
    (localY_bound : |square.dilatedLocalY factor point.toPoint| < factor / 2) :
    point ∈ square.dilatedInteriorRegion factor := by
  rw [square.mem_dilatedInteriorRegion_iff factor_positive]
  exact ⟨square.dilatedLocalX factor point.toPoint,
    square.dilatedLocalY factor point.toPoint,
    localX_bound, localY_bound,
    (square.dilatedPoint_inverseCoordinates factor point.toPoint).symm⟩

noncomputable def PlacedSquare.horizontalAdjacentChordStart
    (square : PlacedSquare) (factor height : ℝ) : ℝ :=
  factor * square.center.x +
    (-factor / 2 - (height - factor * square.center.y) * square.frame.sine) /
      square.frame.cosine

noncomputable def PlacedSquare.horizontalAdjacentChordEnd
    (square : PlacedSquare) (factor height : ℝ) : ℝ :=
  factor * square.center.x +
    ((height - factor * square.center.y) * square.frame.cosine + factor / 2) /
      square.frame.sine

noncomputable def PlacedSquare.horizontalAdjacentOtherLower
    (square : PlacedSquare) (factor height : ℝ) : ℝ :=
  factor * square.center.x +
    ((height - factor * square.center.y) * square.frame.cosine - factor / 2) /
      square.frame.sine

noncomputable def PlacedSquare.horizontalAdjacentOtherUpper
    (square : PlacedSquare) (factor height : ℝ) : ℝ :=
  factor * square.center.x +
    (factor / 2 - (height - factor * square.center.y) * square.frame.sine) /
      square.frame.cosine

lemma PlacedSquare.horizontalChord_inside_dilatedInteriorRegion
    (square : PlacedSquare) {factor height intervalStart intervalEnd : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (x_lower_at_most :
      square.horizontalAdjacentChordStart factor height ≤ intervalStart)
    (y_lower_at_most :
      square.horizontalAdjacentOtherLower factor height ≤ intervalStart)
    (end_at_most_x_upper :
      intervalEnd ≤ square.horizontalAdjacentOtherUpper factor height)
    (end_at_most_y_upper :
      intervalEnd ≤ square.horizontalAdjacentChordEnd factor height) :
    ∀ coordinate ∈ Ioo intervalStart intervalEnd,
      ![coordinate, height] ∈ square.dilatedInteriorRegion factor := by
  intro coordinate coordinate_mem
  apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
  · rw [abs_lt]
    constructor
    · have lower_lt_coordinate :
          square.horizontalAdjacentChordStart factor height < coordinate :=
        x_lower_at_most.trans_lt coordinate_mem.1
      have divided_bound :
          (-factor / 2 -
              (height - factor * square.center.y) * square.frame.sine) /
              square.frame.cosine <
            coordinate - factor * square.center.x := by
        dsimp [PlacedSquare.horizontalAdjacentChordStart] at lower_lt_coordinate
        linarith
      have multiplied_bound := (div_lt_iff₀ cosine_positive).mp divided_bound
      simp only [PlacedSquare.dilatedLocalX, Plane.toPoint, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      linarith
    · have coordinate_lt_upper :
          coordinate < square.horizontalAdjacentOtherUpper factor height :=
        coordinate_mem.2.trans_le end_at_most_x_upper
      have divided_bound :
          coordinate - factor * square.center.x <
            (factor / 2 -
              (height - factor * square.center.y) * square.frame.sine) /
                square.frame.cosine := by
        dsimp [PlacedSquare.horizontalAdjacentOtherUpper] at coordinate_lt_upper
        linarith
      have multiplied_bound := (lt_div_iff₀ cosine_positive).mp divided_bound
      simp only [PlacedSquare.dilatedLocalX, Plane.toPoint, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      linarith
  · rw [abs_lt]
    constructor
    · have coordinate_lt_upper :
          coordinate < square.horizontalAdjacentChordEnd factor height :=
        coordinate_mem.2.trans_le end_at_most_y_upper
      have divided_bound :
          coordinate - factor * square.center.x <
            ((height - factor * square.center.y) * square.frame.cosine + factor / 2) /
              square.frame.sine := by
        dsimp [PlacedSquare.horizontalAdjacentChordEnd] at coordinate_lt_upper
        linarith
      have multiplied_bound := (lt_div_iff₀ sine_positive).mp divided_bound
      simp only [PlacedSquare.dilatedLocalY, Plane.toPoint, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      linarith
    · have lower_lt_coordinate :
          square.horizontalAdjacentOtherLower factor height < coordinate :=
        y_lower_at_most.trans_lt coordinate_mem.1
      have divided_bound :
          ((height - factor * square.center.y) * square.frame.cosine - factor / 2) /
              square.frame.sine <
            coordinate - factor * square.center.x := by
        dsimp [PlacedSquare.horizontalAdjacentOtherLower] at lower_lt_coordinate
        linarith
      have multiplied_bound := (div_lt_iff₀ sine_positive).mp divided_bound
      simp only [PlacedSquare.dilatedLocalY, Plane.toPoint, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      linarith

lemma PlacedSquare.horizontalAdjacentChord_inside_dilatedInteriorRegion
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (other_lower_at_most :
      square.horizontalAdjacentOtherLower factor height ≤
        square.horizontalAdjacentChordStart factor height)
    (end_at_most_other_upper :
      square.horizontalAdjacentChordEnd factor height ≤
        square.horizontalAdjacentOtherUpper factor height) :
    ∀ coordinate ∈
        Ioo (square.horizontalAdjacentChordStart factor height)
          (square.horizontalAdjacentChordEnd factor height),
      ![coordinate, height] ∈ square.dilatedInteriorRegion factor := by
  exact square.horizontalChord_inside_dilatedInteriorRegion
    factor_positive cosine_positive sine_positive le_rfl other_lower_at_most
    end_at_most_other_upper le_rfl

lemma PlacedSquare.horizontalAdjacentChord_length
    (square : PlacedSquare) {factor height : ℝ}
    (cosine_nonzero : square.frame.cosine ≠ 0)
    (sine_nonzero : square.frame.sine ≠ 0) :
    square.horizontalAdjacentChordEnd factor height -
        square.horizontalAdjacentChordStart factor height =
      (factor * (square.frame.cosine + square.frame.sine) +
        2 * (height - factor * square.center.y)) /
          (2 * square.frame.sine * square.frame.cosine) := by
  dsimp [PlacedSquare.horizontalAdjacentChordEnd,
    PlacedSquare.horizontalAdjacentChordStart]
  field_simp [cosine_nonzero, sine_nonzero]
  linear_combination
    2 * (height - factor * square.center.y) * square.frame.unit

lemma PlacedSquare.horizontalCosineChord_length
    (square : PlacedSquare) {factor height : ℝ}
    (cosine_nonzero : square.frame.cosine ≠ 0) :
    square.horizontalAdjacentOtherUpper factor height -
        square.horizontalAdjacentChordStart factor height =
      factor / square.frame.cosine := by
  dsimp [PlacedSquare.horizontalAdjacentOtherUpper,
    PlacedSquare.horizontalAdjacentChordStart]
  field_simp [cosine_nonzero]
  ring

lemma PlacedSquare.horizontalSineChord_length
    (square : PlacedSquare) {factor height : ℝ}
    (sine_nonzero : square.frame.sine ≠ 0) :
    square.horizontalAdjacentChordEnd factor height -
        square.horizontalAdjacentOtherLower factor height =
      factor / square.frame.sine := by
  dsimp [PlacedSquare.horizontalAdjacentChordEnd,
    PlacedSquare.horizontalAdjacentOtherLower]
  field_simp [sine_nonzero]
  ring

lemma PlacedSquare.horizontalCosineChord_length_at_least_factor
    (square : PlacedSquare) {factor height : ℝ}
    (factor_nonnegative : 0 ≤ factor)
    (cosine_positive : 0 < square.frame.cosine) :
    factor ≤ square.horizontalAdjacentOtherUpper factor height -
      square.horizontalAdjacentChordStart factor height := by
  rw [square.horizontalCosineChord_length (ne_of_gt cosine_positive)]
  apply (le_div_iff₀ cosine_positive).2
  exact mul_le_of_le_one_right factor_nonnegative
    (square.frame.cosine_le_one cosine_positive.le)

lemma PlacedSquare.horizontalSineChord_length_at_least_factor
    (square : PlacedSquare) {factor height : ℝ}
    (factor_nonnegative : 0 ≤ factor)
    (sine_positive : 0 < square.frame.sine) :
    factor ≤ square.horizontalAdjacentChordEnd factor height -
      square.horizontalAdjacentOtherLower factor height := by
  rw [square.horizontalSineChord_length (ne_of_gt sine_positive)]
  apply (le_div_iff₀ sine_positive).2
  exact mul_le_of_le_one_right factor_nonnegative
    (square.frame.sine_le_one sine_positive.le)

lemma PlacedSquare.horizontalCosineChord_inside_dilatedInteriorRegion
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (y_lower_at_most_x_lower :
      square.horizontalAdjacentOtherLower factor height ≤
        square.horizontalAdjacentChordStart factor height)
    (x_upper_at_most_y_upper :
      square.horizontalAdjacentOtherUpper factor height ≤
        square.horizontalAdjacentChordEnd factor height) :
    ∀ coordinate ∈
        Ioo (square.horizontalAdjacentChordStart factor height)
          (square.horizontalAdjacentOtherUpper factor height),
      ![coordinate, height] ∈ square.dilatedInteriorRegion factor := by
  exact square.horizontalChord_inside_dilatedInteriorRegion
    factor_positive cosine_positive sine_positive le_rfl y_lower_at_most_x_lower
    le_rfl x_upper_at_most_y_upper

lemma PlacedSquare.horizontalSineChord_inside_dilatedInteriorRegion
    (square : PlacedSquare) {factor height : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (x_lower_at_most_y_lower :
      square.horizontalAdjacentChordStart factor height ≤
        square.horizontalAdjacentOtherLower factor height)
    (y_upper_at_most_x_upper :
      square.horizontalAdjacentChordEnd factor height ≤
        square.horizontalAdjacentOtherUpper factor height) :
    ∀ coordinate ∈
        Ioo (square.horizontalAdjacentOtherLower factor height)
          (square.horizontalAdjacentChordEnd factor height),
      ![coordinate, height] ∈ square.dilatedInteriorRegion factor := by
  exact square.horizontalChord_inside_dilatedInteriorRegion
    factor_positive cosine_positive sine_positive x_lower_at_most_y_lower le_rfl
    y_upper_at_most_x_upper le_rfl

noncomputable def PlacedSquare.verticalAdjacentChordStart
    (square : PlacedSquare) (factor width : ℝ) : ℝ :=
  square.swap.horizontalAdjacentChordStart factor width

noncomputable def PlacedSquare.verticalAdjacentChordEnd
    (square : PlacedSquare) (factor width : ℝ) : ℝ :=
  square.swap.horizontalAdjacentChordEnd factor width

noncomputable def PlacedSquare.verticalAdjacentOtherLower
    (square : PlacedSquare) (factor width : ℝ) : ℝ :=
  square.swap.horizontalAdjacentOtherLower factor width

noncomputable def PlacedSquare.verticalAdjacentOtherUpper
    (square : PlacedSquare) (factor width : ℝ) : ℝ :=
  square.swap.horizontalAdjacentOtherUpper factor width

lemma PlacedSquare.verticalChord_inside_dilatedInteriorRegion
    (square : PlacedSquare) {factor width intervalStart intervalEnd : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (first_lower_at_most :
      square.verticalAdjacentChordStart factor width ≤ intervalStart)
    (second_lower_at_most :
      square.verticalAdjacentOtherLower factor width ≤ intervalStart)
    (end_at_most_first_upper :
      intervalEnd ≤ square.verticalAdjacentOtherUpper factor width)
    (end_at_most_second_upper :
      intervalEnd ≤ square.verticalAdjacentChordEnd factor width) :
    ∀ coordinate ∈ Ioo intervalStart intervalEnd,
      ![width, coordinate] ∈ square.dilatedInteriorRegion factor := by
  intro coordinate coordinate_mem
  apply (square.horizontalPoint_mem_swap_iff factor_positive).mp
  apply square.swap.horizontalChord_inside_dilatedInteriorRegion
    factor_positive sine_positive cosine_positive
  · exact first_lower_at_most
  · exact second_lower_at_most
  · exact end_at_most_first_upper
  · exact end_at_most_second_upper
  · exact coordinate_mem

lemma PlacedSquare.verticalSineChord_length_at_least_factor
    (square : PlacedSquare) {factor width : ℝ}
    (factor_nonnegative : 0 ≤ factor)
    (sine_positive : 0 < square.frame.sine) :
    factor ≤ square.verticalAdjacentOtherUpper factor width -
      square.verticalAdjacentChordStart factor width := by
  simpa [PlacedSquare.verticalAdjacentOtherUpper,
    PlacedSquare.verticalAdjacentChordStart, PlacedSquare.swap, Frame.swap] using
    square.swap.horizontalCosineChord_length_at_least_factor
      factor_nonnegative sine_positive

lemma PlacedSquare.verticalCosineChord_length_at_least_factor
    (square : PlacedSquare) {factor width : ℝ}
    (factor_nonnegative : 0 ≤ factor)
    (cosine_positive : 0 < square.frame.cosine) :
    factor ≤ square.verticalAdjacentChordEnd factor width -
      square.verticalAdjacentOtherLower factor width := by
  simpa [PlacedSquare.verticalAdjacentChordEnd,
    PlacedSquare.verticalAdjacentOtherLower, PlacedSquare.swap, Frame.swap] using
    square.swap.horizontalSineChord_length_at_least_factor
      factor_nonnegative cosine_positive

lemma PlacedSquare.verticalSineChord_inside_dilatedInteriorRegion
    (square : PlacedSquare) {factor width : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (second_lower_at_most_first_lower :
      square.verticalAdjacentOtherLower factor width ≤
        square.verticalAdjacentChordStart factor width)
    (first_upper_at_most_second_upper :
      square.verticalAdjacentOtherUpper factor width ≤
        square.verticalAdjacentChordEnd factor width) :
    ∀ coordinate ∈
        Ioo (square.verticalAdjacentChordStart factor width)
          (square.verticalAdjacentOtherUpper factor width),
      ![width, coordinate] ∈ square.dilatedInteriorRegion factor := by
  exact square.verticalChord_inside_dilatedInteriorRegion
    factor_positive cosine_positive sine_positive le_rfl
    second_lower_at_most_first_lower le_rfl first_upper_at_most_second_upper

lemma PlacedSquare.verticalCosineChord_inside_dilatedInteriorRegion
    (square : PlacedSquare) {factor width : ℝ}
    (factor_positive : 0 < factor)
    (cosine_positive : 0 < square.frame.cosine)
    (sine_positive : 0 < square.frame.sine)
    (first_lower_at_most_second_lower :
      square.verticalAdjacentChordStart factor width ≤
        square.verticalAdjacentOtherLower factor width)
    (second_upper_at_most_first_upper :
      square.verticalAdjacentChordEnd factor width ≤
        square.verticalAdjacentOtherUpper factor width) :
    ∀ coordinate ∈
        Ioo (square.verticalAdjacentOtherLower factor width)
          (square.verticalAdjacentChordEnd factor width),
      ![width, coordinate] ∈ square.dilatedInteriorRegion factor := by
  exact square.verticalChord_inside_dilatedInteriorRegion
    factor_positive cosine_positive sine_positive
    first_lower_at_most_second_lower le_rfl second_upper_at_most_first_upper le_rfl

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

lemma Plane.swap_mem_containerRegion_iff (side : ℝ) (point : Plane) :
    point.swap ∈ containerRegion side ↔ point ∈ containerRegion side := by
  simp only [containerRegion, mem_Icc, Plane.swap]
  constructor
  · rintro ⟨lower, upper⟩
    constructor <;> intro coordinate <;> fin_cases coordinate
    · exact lower 1
    · exact lower 0
    · exact upper 1
    · exact upper 0
  · rintro ⟨lower, upper⟩
    constructor <;> intro coordinate <;> fin_cases coordinate
    · exact lower 1
    · exact lower 0
    · exact upper 1
    · exact upper 0

lemma PlacedSquare.swap_dilatedInteriorRegion_subset_containerRegion
    {square : PlacedSquare} {factor side : ℝ}
    (factor_positive : 0 < factor)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion side) :
    square.swap.dilatedInteriorRegion factor ⊆ containerRegion side := by
  intro point point_mem
  have swapped_mem : point.swap ∈ square.dilatedInteriorRegion factor := by
    have equivalence :=
      square.mem_swap_dilatedInteriorRegion_iff factor_positive point.swap
    rw [Plane.swap_swap] at equivalence
    exact equivalence.mp point_mem
  exact (point.swap_mem_containerRegion_iff side).mp
    (inside_container swapped_mem)

lemma PlacedSquare.dilatedCenterX_halfExtent_le
    {square : PlacedSquare} {factor side : ℝ}
    (factor_positive : 0 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion side) :
    factor * (square.frame.cosine + square.frame.sine) / 2 ≤
      factor * square.center.x := by
  have component_sum_positive :
      0 < square.frame.cosine + square.frame.sine := by
    by_contra sum_not_positive
    have sum_nonpositive := le_of_not_gt sum_not_positive
    have cosine_zero : square.frame.cosine = 0 := by linarith
    have sine_zero : square.frame.sine = 0 := by linarith
    have unit := square.frame.unit
    rw [cosine_zero, sine_zero] at unit
    norm_num at unit
  let centerPoint := (square.dilatedPoint factor 0 0).toPlane
  have center_point_mem : centerPoint ∈ square.dilatedInteriorRegion factor := by
    rw [square.mem_dilatedInteriorRegion_iff factor_positive]
    refine ⟨0, 0, by simpa using (half_pos factor_positive),
      by simpa using (half_pos factor_positive), ?_⟩
    simp [centerPoint]
  have center_x_nonnegative : 0 ≤ factor * square.center.x := by
    have center_bounds :=
      (mem_containerRegion_iff side centerPoint).mp
        (inside_container center_point_mem)
    simpa [centerPoint, PlacedSquare.dilatedPoint, Frame.place] using center_bounds.1
  by_contra half_extent_not_le
  have center_x_lt_half_extent :
      factor * square.center.x <
        factor * (square.frame.cosine + square.frame.sine) / 2 :=
    lt_of_not_ge half_extent_not_le
  let gap :=
    factor * (square.frame.cosine + square.frame.sine) / 2 -
      factor * square.center.x
  have gap_positive : 0 < gap := by
    dsimp [gap]
    linarith
  have gap_at_most_half_extent :
      gap ≤ factor * (square.frame.cosine + square.frame.sine) / 2 := by
    dsimp [gap]
    linarith
  let delta := gap / (2 * (square.frame.cosine + square.frame.sine))
  have delta_positive : 0 < delta := by
    dsimp [delta]
    positivity
  have delta_lt_half_factor : delta < factor / 2 := by
    dsimp [delta]
    rw [div_lt_iff₀ (by positivity :
      0 < 2 * (square.frame.cosine + square.frame.sine))]
    nlinarith
  let edgeOffset := factor / 2 - delta
  have edge_offset_positive : 0 < edgeOffset := by
    dsimp [edgeOffset]
    linarith
  have edge_offset_lt_half_factor : edgeOffset < factor / 2 := by
    dsimp [edgeOffset]
    linarith
  let testPoint :=
    (square.dilatedPoint factor (-edgeOffset) edgeOffset).toPlane
  have test_point_mem : testPoint ∈ square.dilatedInteriorRegion factor := by
    rw [square.mem_dilatedInteriorRegion_iff factor_positive]
    refine ⟨-edgeOffset, edgeOffset, ?_, ?_, ?_⟩
    · rw [abs_neg, abs_of_pos edge_offset_positive]
      exact edge_offset_lt_half_factor
    · rw [abs_of_pos edge_offset_positive]
      exact edge_offset_lt_half_factor
    · simp [testPoint]
  have test_x_nonnegative : 0 ≤ testPoint 0 := by
    have test_bounds :=
      (mem_containerRegion_iff side testPoint).mp
        (inside_container test_point_mem)
    exact test_bounds.1
  have test_x_eq : testPoint 0 = -gap / 2 := by
    dsimp [testPoint, edgeOffset, delta, gap, PlacedSquare.dilatedPoint,
      Frame.place, Point.toPlane]
    field_simp [ne_of_gt component_sum_positive]
    ring
  rw [test_x_eq] at test_x_nonnegative
  linarith

lemma PlacedSquare.dilatedCenterY_halfExtent_le
    {square : PlacedSquare} {factor side : ℝ}
    (factor_positive : 0 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion side) :
    factor * (square.frame.cosine + square.frame.sine) / 2 ≤
      factor * square.center.y := by
  have swapped_inside :=
    square.swap_dilatedInteriorRegion_subset_containerRegion
      factor_positive inside_container
  have swapped_bound := square.swap.dilatedCenterX_halfExtent_le
    factor_positive sine_nonnegative cosine_nonnegative swapped_inside
  simpa [PlacedSquare.swap, Point.swap, Frame.swap, add_comm] using swapped_bound

lemma Frame.remainingHalfExtent_mul_componentSum_lt_half
    (frame : Frame) {factor : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ frame.cosine)
    (sine_nonnegative : 0 ≤ frame.sine) :
    (1 - factor * (frame.cosine + frame.sine) / 2) *
        (frame.cosine + frame.sine) <
      factor / 2 := by
  let componentSum := frame.cosine + frame.sine
  have component_sum_nonnegative : 0 ≤ componentSum := by
    dsimp [componentSum]
    linarith
  have component_sum_sq : componentSum ^ 2 =
      1 + 2 * frame.cosine * frame.sine := by
    dsimp [componentSum]
    nlinarith [frame.unit]
  have component_sum_sq_at_least_one : 1 ≤ componentSum ^ 2 := by
    rw [component_sum_sq]
    nlinarith [mul_nonneg cosine_nonnegative sine_nonnegative]
  have component_sum_positive : 0 < componentSum := by nlinarith
  have twice_sum_at_most : 2 * componentSum ≤ componentSum ^ 2 + 1 := by
    nlinarith [sq_nonneg (componentSum - 1)]
  have sum_square_plus_one_positive : 0 < componentSum ^ 2 + 1 := by
    nlinarith
  have scaled_sum_square_gt :
      componentSum ^ 2 + 1 < factor * (componentSum ^ 2 + 1) := by
    simpa only [one_mul] using
      mul_lt_mul_of_pos_right factor_gt_one sum_square_plus_one_positive
  change (1 - factor * componentSum / 2) * componentSum < factor / 2
  nlinarith

lemma PlacedSquare.unitCornerPoint_mem_dilatedInteriorRegion_of_center_le_one
    {square : PlacedSquare} {factor side : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion side)
    (center_x_at_most_one : factor * square.center.x ≤ 1)
    (center_y_at_most_one : factor * square.center.y ≤ 1) :
    ![(1 : ℝ), 1] ∈ square.dilatedInteriorRegion factor := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  let componentSum := square.frame.cosine + square.frame.sine
  have component_sum_nonnegative : 0 ≤ componentSum := by
    dsimp [componentSum]
    linarith
  have center_x_at_least_half := square.dilatedCenterX_halfExtent_le
    factor_positive cosine_nonnegative sine_nonnegative inside_container
  have center_y_at_least_half := square.dilatedCenterY_halfExtent_le
    factor_positive cosine_nonnegative sine_nonnegative inside_container
  let remaining := 1 - factor * componentSum / 2
  have remaining_nonnegative : 0 ≤ remaining := by
    dsimp [remaining, componentSum]
    linarith
  have x_gap_nonnegative : 0 ≤ 1 - factor * square.center.x := by linarith
  have y_gap_nonnegative : 0 ≤ 1 - factor * square.center.y := by linarith
  have x_gap_at_most_remaining :
      1 - factor * square.center.x ≤ remaining := by
    dsimp [remaining, componentSum]
    linarith
  have y_gap_at_most_remaining :
      1 - factor * square.center.y ≤ remaining := by
    dsimp [remaining, componentSum]
    linarith
  have remaining_times_sum_lt_half : remaining * componentSum < factor / 2 := by
    simpa [remaining, componentSum] using
      square.frame.remainingHalfExtent_mul_componentSum_lt_half
        factor_gt_one cosine_nonnegative sine_nonnegative
  have x_cosine_at_most :
      (1 - factor * square.center.x) * square.frame.cosine ≤
        remaining * square.frame.cosine :=
    mul_le_mul_of_nonneg_right x_gap_at_most_remaining cosine_nonnegative
  have x_sine_at_most :
      (1 - factor * square.center.x) * square.frame.sine ≤
        remaining * square.frame.sine :=
    mul_le_mul_of_nonneg_right x_gap_at_most_remaining sine_nonnegative
  have y_cosine_at_most :
      (1 - factor * square.center.y) * square.frame.cosine ≤
        remaining * square.frame.cosine :=
    mul_le_mul_of_nonneg_right y_gap_at_most_remaining cosine_nonnegative
  have y_sine_at_most :
      (1 - factor * square.center.y) * square.frame.sine ≤
        remaining * square.frame.sine :=
    mul_le_mul_of_nonneg_right y_gap_at_most_remaining sine_nonnegative
  have remaining_cosine_at_most_sum :
      remaining * square.frame.cosine ≤ remaining * componentSum := by
    apply mul_le_mul_of_nonneg_left _ remaining_nonnegative
    dsimp [componentSum]
    linarith
  have remaining_sine_at_most_sum :
      remaining * square.frame.sine ≤ remaining * componentSum := by
    apply mul_le_mul_of_nonneg_left _ remaining_nonnegative
    dsimp [componentSum]
    linarith
  have x_sine_lt_half :
      (1 - factor * square.center.x) * square.frame.sine < factor / 2 :=
    x_sine_at_most.trans_lt
      (remaining_sine_at_most_sum.trans_lt remaining_times_sum_lt_half)
  have y_cosine_lt_half :
      (1 - factor * square.center.y) * square.frame.cosine < factor / 2 :=
    y_cosine_at_most.trans_lt
      (remaining_cosine_at_most_sum.trans_lt remaining_times_sum_lt_half)
  have x_cosine_nonnegative :
      0 ≤ (1 - factor * square.center.x) * square.frame.cosine :=
    mul_nonneg x_gap_nonnegative cosine_nonnegative
  have x_sine_nonnegative :
      0 ≤ (1 - factor * square.center.x) * square.frame.sine :=
    mul_nonneg x_gap_nonnegative sine_nonnegative
  have y_cosine_nonnegative :
      0 ≤ (1 - factor * square.center.y) * square.frame.cosine :=
    mul_nonneg y_gap_nonnegative cosine_nonnegative
  have y_sine_nonnegative :
      0 ≤ (1 - factor * square.center.y) * square.frame.sine :=
    mul_nonneg y_gap_nonnegative sine_nonnegative
  apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
  · rw [abs_lt]
    constructor
    · simp only [PlacedSquare.dilatedLocalX, Plane.toPoint, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      linarith
    · simp only [PlacedSquare.dilatedLocalX, Plane.toPoint, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      dsimp [componentSum] at remaining_times_sum_lt_half
      linarith
  · rw [abs_lt]
    constructor
    · simp only [PlacedSquare.dilatedLocalY, Plane.toPoint, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      linarith
    · simp only [PlacedSquare.dilatedLocalY, Plane.toPoint, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      linarith

lemma PlacedSquare.case5CornerPoints_mem_dilatedInteriorRegion_of_sine_le_cosine
    {square : PlacedSquare} {factor side : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (sine_at_most_cosine : square.frame.sine ≤ square.frame.cosine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion side)
    (center_x_at_most_one : factor * square.center.x ≤ 1)
    (center_y_at_most_one : factor * square.center.y ≤ 1) :
    ![(9 / 10 : ℝ), 1] ∈ square.dilatedInteriorRegion factor ∧
      ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor := by
  have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
  let componentSum := square.frame.cosine + square.frame.sine
  have component_sum_nonnegative : 0 ≤ componentSum := by
    dsimp [componentSum]
    linarith
  have component_sum_sq : componentSum ^ 2 =
      1 + 2 * square.frame.cosine * square.frame.sine := by
    dsimp [componentSum]
    nlinarith [square.frame.unit]
  have component_sum_sq_at_least_one : 1 ≤ componentSum ^ 2 := by
    rw [component_sum_sq]
    nlinarith [mul_nonneg cosine_nonnegative sine_nonnegative]
  have component_sum_at_least_one : 1 ≤ componentSum := by
    nlinarith
  have center_x_at_least_half := square.dilatedCenterX_halfExtent_le
    factor_positive cosine_nonnegative sine_nonnegative inside_container
  have center_y_at_least_half := square.dilatedCenterY_halfExtent_le
    factor_positive cosine_nonnegative sine_nonnegative inside_container
  let remaining := 1 - factor * componentSum / 2
  have remaining_nonnegative : 0 ≤ remaining := by
    dsimp [remaining, componentSum]
    linarith
  have remaining_lt_half : remaining < 1 / 2 := by
    dsimp [remaining]
    have factor_times_sum_gt_one : 1 < factor * componentSum := by
      have component_sum_positive : 0 < componentSum :=
        zero_lt_one.trans_le component_sum_at_least_one
      have scaled :=
        mul_lt_mul_of_pos_right factor_gt_one component_sum_positive
      exact component_sum_at_least_one.trans_lt (by simpa only [one_mul] using scaled)
    linarith
  have remaining_times_sum_lt_half : remaining * componentSum < factor / 2 := by
    simpa [remaining, componentSum] using
      square.frame.remainingHalfExtent_mul_componentSum_lt_half
        factor_gt_one cosine_nonnegative sine_nonnegative
  have cosine_at_most_one :=
    square.frame.cosine_le_one cosine_nonnegative
  have sine_lt_four_fifths : square.frame.sine < 4 / 5 := by
    by_contra sine_not_lt
    have sine_at_least : 4 / 5 ≤ square.frame.sine := le_of_not_gt sine_not_lt
    have component_difference_nonnegative :
        0 ≤ square.frame.cosine - square.frame.sine :=
      sub_nonneg.mpr sine_at_most_cosine
    have component_sum_nonnegative' :
        0 ≤ square.frame.cosine + square.frame.sine := by linarith
    have cosine_sq_at_least_sine_sq :
        square.frame.sine ^ 2 ≤ square.frame.cosine ^ 2 := by
      nlinarith [mul_nonneg component_difference_nonnegative
        component_sum_nonnegative']
    nlinarith [square.frame.unit]
  have cosine_at_least_fifth : 1 / 5 ≤ square.frame.cosine := by
    by_contra cosine_not_ge
    have cosine_lt : square.frame.cosine < 1 / 5 := lt_of_not_ge cosine_not_ge
    nlinarith [square.frame.unit, sq_nonneg square.frame.cosine,
      sq_nonneg square.frame.sine]
  have easy_sine_bound :
      remaining * square.frame.sine + square.frame.cosine / 10 < factor / 2 := by
    have five_sine_add_cosine_lt_five :
        5 * square.frame.sine + square.frame.cosine < 5 := by
      linarith
    have factor_half_gt_half : 1 / 2 < factor / 2 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr remaining_lt_half.le)
      sine_nonnegative]
  have base_cosine_bound :
      (1 - componentSum / 2) * square.frame.cosine +
          square.frame.sine / 10 ≤
        1 / 2 := by
    have nonnegative_product :
        0 ≤ square.frame.sine * (square.frame.cosine - 1 / 5) :=
      mul_nonneg sine_nonnegative (sub_nonneg.mpr cosine_at_least_fifth)
    dsimp [componentSum]
    nlinarith [square.frame.unit, sq_nonneg (1 - square.frame.cosine)]
  have scaled_cosine_bound :
      remaining * square.frame.cosine + square.frame.sine / 10 < factor / 2 := by
    have gain_positive :
        0 < (factor - 1) * (1 + componentSum * square.frame.cosine) := by
      apply mul_pos (sub_pos.mpr factor_gt_one)
      have product_nonnegative :=
        mul_nonneg component_sum_nonnegative cosine_nonnegative
      linarith
    dsimp [remaining]
    nlinarith
  have x_gap_nonnegative : 0 ≤ 1 - factor * square.center.x := by linarith
  have y_gap_nonnegative : 0 ≤ 1 - factor * square.center.y := by linarith
  have x_gap_at_most_remaining :
      1 - factor * square.center.x ≤ remaining := by
    dsimp [remaining, componentSum]
    linarith
  have y_gap_at_most_remaining :
      1 - factor * square.center.y ≤ remaining := by
    dsimp [remaining, componentSum]
    linarith
  have x_cosine_nonnegative := mul_nonneg x_gap_nonnegative cosine_nonnegative
  have x_sine_nonnegative := mul_nonneg x_gap_nonnegative sine_nonnegative
  have y_cosine_nonnegative := mul_nonneg y_gap_nonnegative cosine_nonnegative
  have y_sine_nonnegative := mul_nonneg y_gap_nonnegative sine_nonnegative
  have x_cosine_at_most :
      (1 - factor * square.center.x) * square.frame.cosine ≤
        remaining * square.frame.cosine :=
    mul_le_mul_of_nonneg_right x_gap_at_most_remaining cosine_nonnegative
  have x_sine_at_most :
      (1 - factor * square.center.x) * square.frame.sine ≤
        remaining * square.frame.sine :=
    mul_le_mul_of_nonneg_right x_gap_at_most_remaining sine_nonnegative
  have y_cosine_at_most :
      (1 - factor * square.center.y) * square.frame.cosine ≤
        remaining * square.frame.cosine :=
    mul_le_mul_of_nonneg_right y_gap_at_most_remaining cosine_nonnegative
  have y_sine_at_most :
      (1 - factor * square.center.y) * square.frame.sine ≤
        remaining * square.frame.sine :=
    mul_le_mul_of_nonneg_right y_gap_at_most_remaining sine_nonnegative
  have remaining_cosine_at_most_sum :
      remaining * square.frame.cosine ≤ remaining * componentSum := by
    apply mul_le_mul_of_nonneg_left _ remaining_nonnegative
    dsimp [componentSum]
    linarith
  have remaining_sine_at_most_sum :
      remaining * square.frame.sine ≤ remaining * componentSum := by
    apply mul_le_mul_of_nonneg_left _ remaining_nonnegative
    dsimp [componentSum]
    linarith
  have cosine_tenth_lt_half : square.frame.cosine / 10 < factor / 2 := by
    nlinarith
  have sine_tenth_lt_half : square.frame.sine / 10 < factor / 2 := by
    have sine_at_most_one := square.frame.sine_le_one sine_nonnegative
    nlinarith
  constructor
  · apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
    · rw [abs_lt]
      constructor <;>
        simp only [PlacedSquare.dilatedLocalX, Plane.toPoint,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;> linarith
    · rw [abs_lt]
      constructor <;>
        simp only [PlacedSquare.dilatedLocalY, Plane.toPoint,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;> linarith
  · apply square.mem_dilatedInteriorRegion_of_inverse_bounds factor_positive
    · rw [abs_lt]
      constructor <;>
        simp only [PlacedSquare.dilatedLocalX, Plane.toPoint,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;> linarith
    · rw [abs_lt]
      constructor <;>
        simp only [PlacedSquare.dilatedLocalY, Plane.toPoint,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;> linarith

lemma PlacedSquare.case5CornerPoints_mem_dilatedInteriorRegion
    {square : PlacedSquare} {factor side : ℝ}
    (factor_gt_one : 1 < factor)
    (cosine_nonnegative : 0 ≤ square.frame.cosine)
    (sine_nonnegative : 0 ≤ square.frame.sine)
    (inside_container :
      square.dilatedInteriorRegion factor ⊆ containerRegion side)
    (center_x_at_most_one : factor * square.center.x ≤ 1)
    (center_y_at_most_one : factor * square.center.y ≤ 1) :
    ![(9 / 10 : ℝ), 1] ∈ square.dilatedInteriorRegion factor ∧
      ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor := by
  by_cases sine_at_most_cosine : square.frame.sine ≤ square.frame.cosine
  · exact square.case5CornerPoints_mem_dilatedInteriorRegion_of_sine_le_cosine
      factor_gt_one cosine_nonnegative sine_nonnegative sine_at_most_cosine
      inside_container center_x_at_most_one center_y_at_most_one
  · have cosine_at_most_sine : square.frame.cosine ≤ square.frame.sine :=
      le_of_lt (lt_of_not_ge sine_at_most_cosine)
    have factor_positive : 0 < factor := zero_lt_one.trans factor_gt_one
    have swapped_inside :=
      square.swap_dilatedInteriorRegion_subset_containerRegion
        factor_positive inside_container
    have swapped_center_x_at_most_one :
        factor * square.swap.center.x ≤ 1 := by
      simpa [PlacedSquare.swap, Point.swap] using center_y_at_most_one
    have swapped_center_y_at_most_one :
        factor * square.swap.center.y ≤ 1 := by
      simpa [PlacedSquare.swap, Point.swap] using center_x_at_most_one
    have swapped_points :=
      square.swap.case5CornerPoints_mem_dilatedInteriorRegion_of_sine_le_cosine
        factor_gt_one sine_nonnegative cosine_nonnegative cosine_at_most_sine
        swapped_inside swapped_center_x_at_most_one swapped_center_y_at_most_one
    have original_left_bottom :
        ![(1 : ℝ), 9 / 10] ∈ square.dilatedInteriorRegion factor :=
      (square.horizontalPoint_mem_swap_iff factor_positive).mp swapped_points.1
    have original_bottom_left :
        ![(9 / 10 : ℝ), 1] ∈ square.dilatedInteriorRegion factor :=
      (square.horizontalPoint_mem_swap_iff factor_positive).mp swapped_points.2
    exact ⟨original_bottom_left, original_left_bottom⟩

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
