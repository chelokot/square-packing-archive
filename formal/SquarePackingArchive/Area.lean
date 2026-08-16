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
