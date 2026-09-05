import SquarePackingArchive.StromquistStepFour
import SquarePackingArchive.PointInterpolation

namespace SquarePackingArchive.Stromquist.TenPoints

noncomputable def ringCenter : Point := ⟨1 + gap, 1 + gap⟩

noncomputable def ringTransform (index : Fin 8) (point : Point) : Point :=
  match index.val with
  | 0 => point
  | 1 => (point.swap.reflectX side).reflectY side
  | 2 => point.swap.reflectX side
  | 3 => point.reflectY side
  | 4 => (point.reflectX side).reflectY side
  | 5 => point.swap
  | 6 => point.swap.reflectY side
  | _ => point.reflectX side

noncomputable def ringStart (index : Fin 8) : Point := ringTransform index ⟨2, 1⟩

noncomputable def ringEnd (index : Fin 8) : Point := ringTransform index ⟨53 / 25, 9 / 10⟩

noncomputable def ringPoint (index : Fin 8) (parameter : ℝ) : Point :=
  (ringStart index).interpolate (ringEnd index) parameter

noncomputable def ringEndpoint (index : Fin 8) (atEnd : Bool) : Point :=
  if atEnd then ringEnd index else ringStart index

set_option maxHeartbeats 1000000 in
lemma ring_neighbor_endpoints (index : Fin 8) (firstEnd secondEnd : Bool) :
    (ringEndpoint index firstEnd).squaredDistance (ringEndpoint (index + 1) secondEnd) ≤ 1 := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  have squared := gap_square
  fin_cases index <;> cases firstEnd <;> cases secondEnd <;>
    norm_num [ringEndpoint, ringStart, ringEnd, ringTransform, Point.swap,
      Point.reflectX, Point.reflectY, Point.squaredDistance, side, Fin.val_add]
  all_goals first | (rw [abs_le]; constructor <;> nlinarith) | nlinarith

set_option maxHeartbeats 1000000 in
lemma ring_radius_endpoints (index : Fin 8) (atEnd : Bool) :
    (ringEndpoint index atEnd).squaredDistance ringCenter ≤ 1 := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  have squared := gap_square
  fin_cases index <;> cases atEnd <;>
    norm_num [ringEndpoint, ringStart, ringEnd, ringTransform, ringCenter, Point.swap,
      Point.reflectX, Point.reflectY, Point.squaredDistance, side] <;> nlinarith

lemma ring_neighbor_distance (index : Fin 8) {firstParameter secondParameter : ℝ}
    (first_nonnegative : 0 ≤ firstParameter) (first_upper : firstParameter ≤ 1)
    (second_nonnegative : 0 ≤ secondParameter) (second_upper : secondParameter ≤ 1) :
    (ringPoint index firstParameter).squaredDistance (ringPoint (index + 1) secondParameter) ≤ 1 := by
  apply Point.interpolate_pair_squaredDistance_le _ _ _ _
    first_nonnegative first_upper second_nonnegative second_upper
  · exact ring_neighbor_endpoints index false false
  · exact ring_neighbor_endpoints index false true
  · exact ring_neighbor_endpoints index true false
  · exact ring_neighbor_endpoints index true true

lemma ring_radius_distance (index : Fin 8) {parameter : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) (parameter_upper : parameter ≤ 1) :
    (ringPoint index parameter).squaredDistance ringCenter ≤ 1 := by
  exact Point.interpolate_squaredDistance_le _ _ _ parameter_nonnegative parameter_upper
    (ring_radius_endpoints index false) (ring_radius_endpoints index true)

noncomputable def ringCorner (index : Fin 4) : Point :=
  match index.val with
  | 0 => points 6
  | 1 => points 4
  | 2 => points 2
  | _ => points 0

def ringCornerEdge (index : Fin 4) : Fin 8 := ⟨2 * index.val, by omega⟩

set_option maxHeartbeats 1000000 in
lemma ring_corner_endpoint_distance (index : Fin 4) (next atEnd : Bool) :
    (ringEndpoint (if next then ringCornerEdge index + 1 else ringCornerEdge index) atEnd).squaredDistance
      (ringCorner index) ≤ 1 := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  have squared := gap_square
  fin_cases index <;> cases next <;> cases atEnd <;>
    norm_num [ringEndpoint, ringStart, ringEnd, ringTransform, ringCorner, ringCornerEdge,
      Point.swap, Point.reflectX, Point.reflectY, Point.squaredDistance, points, side, Fin.val_add]
  all_goals first | (rw [abs_le]; constructor <;> nlinarith) | nlinarith

set_option maxHeartbeats 1000000 in
lemma ring_fan_endpoint_orientation (index : Fin 8) (firstEnd secondEnd : Bool) :
    1 / 5 ≤ Point.orientedArea ringCenter
      (ringEndpoint index firstEnd) (ringEndpoint (index + 1) secondEnd) := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  have squared := gap_square
  fin_cases index <;> cases firstEnd <;> cases secondEnd <;>
    norm_num [ringEndpoint, ringStart, ringEnd, ringTransform, ringCenter,
      Point.swap, Point.reflectX, Point.reflectY, Point.orientedArea, side, Fin.val_add] <;> nlinarith

set_option maxHeartbeats 1000000 in
lemma ring_corner_endpoint_orientation (index : Fin 4) (firstEnd secondEnd : Bool) :
    1 / 5 ≤ Point.orientedArea (ringCorner index)
      (ringEndpoint (ringCornerEdge index + 1) firstEnd) (ringEndpoint (ringCornerEdge index) secondEnd) := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  have squared := gap_square
  fin_cases index <;> cases firstEnd <;> cases secondEnd <;>
    norm_num [ringEndpoint, ringStart, ringEnd, ringTransform, ringCorner, ringCornerEdge,
      Point.swap, Point.reflectX, Point.reflectY, Point.orientedArea, points, side, Fin.val_add] <;> nlinarith

lemma ring_corner_distance (index : Fin 4) (next : Bool) {parameter : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) (parameter_upper : parameter ≤ 1) :
    (ringPoint (if next then ringCornerEdge index + 1 else ringCornerEdge index) parameter).squaredDistance
      (ringCorner index) ≤ 1 := by
  exact Point.interpolate_squaredDistance_le _ _ _ parameter_nonnegative parameter_upper
    (ring_corner_endpoint_distance index next false) (ring_corner_endpoint_distance index next true)

lemma ring_fan_orientation (index : Fin 8) {firstParameter secondParameter : ℝ}
    (first_nonnegative : 0 ≤ firstParameter) (first_upper : firstParameter ≤ 1)
    (second_nonnegative : 0 ≤ secondParameter) (second_upper : secondParameter ≤ 1) :
    1 / 5 ≤ Point.orientedArea ringCenter
      (ringPoint index firstParameter) (ringPoint (index + 1) secondParameter) := by
  exact Point.interpolate_pair_orientedArea_lower _ _ _ _ _
    first_nonnegative first_upper second_nonnegative second_upper
    (ring_fan_endpoint_orientation index false false) (ring_fan_endpoint_orientation index false true)
    (ring_fan_endpoint_orientation index true false) (ring_fan_endpoint_orientation index true true)

lemma ring_corner_orientation (index : Fin 4) {firstParameter secondParameter : ℝ}
    (first_nonnegative : 0 ≤ firstParameter) (first_upper : firstParameter ≤ 1)
    (second_nonnegative : 0 ≤ secondParameter) (second_upper : secondParameter ≤ 1) :
    1 / 5 ≤ Point.orientedArea (ringCorner index)
      (ringPoint (ringCornerEdge index + 1) firstParameter) (ringPoint (ringCornerEdge index) secondParameter) := by
  exact Point.interpolate_pair_orientedArea_lower _ _ _ _ _
    first_nonnegative first_upper second_nonnegative second_upper
    (ring_corner_endpoint_orientation index false false) (ring_corner_endpoint_orientation index false true)
    (ring_corner_endpoint_orientation index true false) (ring_corner_endpoint_orientation index true true)

end SquarePackingArchive.Stromquist.TenPoints
