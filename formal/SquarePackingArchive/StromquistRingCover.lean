import SquarePackingArchive.StromquistRing
import SquarePackingArchive.StromquistRingBoundary

namespace SquarePackingArchive.Stromquist.TenPoints

def RingParametersValid (parameters : Fin 8 → ℝ) : Prop :=
  ∀ index, 0 ≤ parameters index ∧ parameters index ≤ 1

noncomputable def ringArchivePoints (parameters : Fin 8 → ℝ) (index : Fin 13) : Point :=
  match index.val with
  | 0 => ringPoint 0 (parameters 0)
  | 1 => ringPoint 1 (parameters 1)
  | 2 => ringPoint 2 (parameters 2)
  | 3 => ringPoint 3 (parameters 3)
  | 4 => ringPoint 4 (parameters 4)
  | 5 => ringPoint 5 (parameters 5)
  | 6 => ringPoint 6 (parameters 6)
  | 7 => ringPoint 7 (parameters 7)
  | 8 => ringCorner 0
  | 9 => ringCorner 1
  | 10 => ringCorner 2
  | 11 => ringCorner 3
  | _ => ringCenter

lemma ringArchivePoints_ring (parameters : Fin 8 → ℝ) (index : Fin 8) :
    ringArchivePoints parameters (index.castLE (by decide)) = ringPoint index (parameters index) := by
  fin_cases index <;> rfl

lemma ringArchivePoints_corner (parameters : Fin 8 → ℝ) (index : Fin 4) :
    ringArchivePoints parameters ⟨8 + index.val, by omega⟩ = ringCorner index := by
  fin_cases index <;> rfl

lemma ring_hit_fan_triangle
    (parameters : Fin 8 → ℝ) (valid : RingParametersValid parameters)
    (square : PlacedSquare) (index : Fin 8)
    (first_halfplane : 0 ≤ Point.orientedArea ringCenter
      (ringPoint index (parameters index)) square.center)
    (second_halfplane : 0 ≤ Point.orientedArea
      (ringPoint index (parameters index)) (ringPoint (index + 1) (parameters (index + 1))) square.center)
    (third_halfplane : 0 ≤ Point.orientedArea
      (ringPoint (index + 1) (parameters (index + 1))) ringCenter square.center) :
    ∃ pointIndex, square.Contains (ringArchivePoints parameters pointIndex) := by
  have orientation := ring_fan_orientation index
    (valid index).1 (valid index).2 (valid (index + 1)).1 (valid (index + 1)).2
  have first_radius := ring_radius_distance index (valid index).1 (valid index).2
  have second_radius := ring_radius_distance (index + 1) (valid (index + 1)).1 (valid (index + 1)).2
  have edge := ring_neighbor_distance index
    (valid index).1 (valid index).2 (valid (index + 1)).1 (valid (index + 1)).2
  rw [Point.squaredDistance_comm] at first_radius second_radius
  rcases square.contains_triangleVertex_of_cross_nonnegative _ _ _ (by linarith)
    first_halfplane second_halfplane third_halfplane first_radius second_radius edge with
      center_inside | first_inside | second_inside
  · exact ⟨12, center_inside⟩
  · exact ⟨index.castLE (by decide), by rw [ringArchivePoints_ring]; exact first_inside⟩
  · exact ⟨(index + 1).castLE (by decide), by rw [ringArchivePoints_ring]; exact second_inside⟩

lemma ring_hit_corner_triangle
    (parameters : Fin 8 → ℝ) (valid : RingParametersValid parameters)
    (square : PlacedSquare) (index : Fin 4)
    (first_halfplane : 0 ≤ Point.orientedArea (ringCorner index)
      (ringPoint (ringCornerEdge index + 1) (parameters (ringCornerEdge index + 1))) square.center)
    (second_halfplane : 0 ≤ Point.orientedArea
      (ringPoint (ringCornerEdge index + 1) (parameters (ringCornerEdge index + 1)))
      (ringPoint (ringCornerEdge index) (parameters (ringCornerEdge index))) square.center)
    (third_halfplane : 0 ≤ Point.orientedArea
      (ringPoint (ringCornerEdge index) (parameters (ringCornerEdge index))) (ringCorner index) square.center) :
    ∃ pointIndex, square.Contains (ringArchivePoints parameters pointIndex) := by
  have orientation := ring_corner_orientation index
    (valid (ringCornerEdge index + 1)).1 (valid (ringCornerEdge index + 1)).2
    (valid (ringCornerEdge index)).1 (valid (ringCornerEdge index)).2
  have first_radius := ring_corner_distance index true
    (valid (ringCornerEdge index + 1)).1 (valid (ringCornerEdge index + 1)).2
  have second_radius := ring_corner_distance index false
    (valid (ringCornerEdge index)).1 (valid (ringCornerEdge index)).2
  have edge := ring_neighbor_distance (ringCornerEdge index)
    (valid (ringCornerEdge index)).1 (valid (ringCornerEdge index)).2
    (valid (ringCornerEdge index + 1)).1 (valid (ringCornerEdge index + 1)).2
  rw [Point.squaredDistance_comm] at first_radius second_radius edge
  rcases square.contains_triangleVertex_of_cross_nonnegative _ _ _ (by linarith)
    first_halfplane second_halfplane third_halfplane first_radius second_radius edge with
      corner_inside | first_inside | second_inside
  · exact ⟨⟨8 + index.val, by omega⟩, by rw [ringArchivePoints_corner]; exact corner_inside⟩
  · exact ⟨(ringCornerEdge index + 1).castLE (by decide), by rw [ringArchivePoints_ring]; exact first_inside⟩
  · exact ⟨(ringCornerEdge index).castLE (by decide), by rw [ringArchivePoints_ring]; exact second_inside⟩

end SquarePackingArchive.Stromquist.TenPoints
