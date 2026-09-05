import SquarePackingArchive.StromquistRingCover
import SquarePackingArchive.PolygonFan

namespace SquarePackingArchive.Stromquist.TenPoints

private def surroundingIndices (index : Fin 3) : Fin 8 :=
  match index.val with
  | 0 => 0
  | 1 => 3
  | _ => 5

set_option maxHeartbeats 1000000 in
private lemma surrounding_endpoint_orientation (index : Fin 3) (firstEnd secondEnd : Bool) :
    1 / 5 ≤ Point.orientedArea ringCenter
      (ringEndpoint (surroundingIndices index) firstEnd)
      (ringEndpoint (surroundingIndices (index + 1)) secondEnd) := by
  have lower := gap_bounds.1
  have upper := gap_bounds.2
  have squared := gap_square
  fin_cases index <;> cases firstEnd <;> cases secondEnd <;>
    norm_num [surroundingIndices, ringEndpoint, ringStart, ringEnd, ringTransform, ringCenter,
      Point.swap, Point.reflectX, Point.reflectY, Point.orientedArea, side, Fin.val_add] <;> nlinarith

private lemma surrounding_orientation (parameters : Fin 8 → ℝ)
    (valid : RingParametersValid parameters) (index : Fin 3) :
    1 / 5 ≤ Point.orientedArea ringCenter
      (ringPoint (surroundingIndices index) (parameters (surroundingIndices index)))
      (ringPoint (surroundingIndices (index + 1)) (parameters (surroundingIndices (index + 1)))) := by
  exact Point.interpolate_pair_orientedArea_lower _ _ _ _ _
    (valid _).1 (valid _).2 (valid _).1 (valid _).2
    (surrounding_endpoint_orientation index false false)
    (surrounding_endpoint_orientation index false true)
    (surrounding_endpoint_orientation index true false)
    (surrounding_endpoint_orientation index true true)

theorem ring_radial_sector (parameters : Fin 8 → ℝ)
    (valid : RingParametersValid parameters) (point : Point) :
    ∃ index, 0 ≤ Point.orientedArea ringCenter (ringPoint index (parameters index)) point ∧
      Point.orientedArea ringCenter (ringPoint (index + 1) (parameters (index + 1))) point ≤ 0 := by
  have first := surrounding_orientation parameters valid 0
  have second := surrounding_orientation parameters valid 1
  have third := surrounding_orientation parameters valid 2
  change 1 / 5 ≤ Point.orientedArea ringCenter (ringPoint 0 (parameters 0))
    (ringPoint 3 (parameters 3)) at first
  change 1 / 5 ≤ Point.orientedArea ringCenter (ringPoint 3 (parameters 3))
    (ringPoint 5 (parameters 5)) at second
  change 1 / 5 ≤ Point.orientedArea ringCenter (ringPoint 5 (parameters 5))
    (ringPoint 0 (parameters 0)) at third
  have signs := Point.radial_halfplanes_have_both_signs
    (fun index => ringPoint index (parameters index)) ringCenter point 0 3 5
    (by dsimp [Point.orientedArea] at second ⊢; nlinarith)
    (by dsimp [Point.orientedArea] at third ⊢; nlinarith)
    (by dsimp [Point.orientedArea] at first ⊢; nlinarith)
  exact exists_cyclic_weak_sign_transition _ signs.1 signs.2

theorem ring_hit_or_exterior (parameters : Fin 8 → ℝ)
    (valid : RingParametersValid parameters) (square : PlacedSquare) :
    (∃ pointIndex, square.Contains (ringArchivePoints parameters pointIndex)) ∨
      ∃ index, 0 ≤ Point.orientedArea ringCenter (ringPoint index (parameters index)) square.center ∧
        Point.orientedArea ringCenter (ringPoint (index + 1) (parameters (index + 1))) square.center ≤ 0 ∧
        Point.orientedArea (ringPoint index (parameters index))
          (ringPoint (index + 1) (parameters (index + 1))) square.center < 0 := by
  obtain ⟨index, first_halfplane, last_halfplane⟩ := ring_radial_sector parameters valid square.center
  by_cases inside : 0 ≤ Point.orientedArea (ringPoint index (parameters index))
      (ringPoint (index + 1) (parameters (index + 1))) square.center
  · apply Or.inl
    apply ring_hit_fan_triangle parameters valid square index first_halfplane inside
    dsimp [Point.orientedArea] at last_halfplane ⊢
    nlinarith
  · exact Or.inr ⟨index, first_halfplane, last_halfplane, lt_of_not_ge inside⟩

end SquarePackingArchive.Stromquist.TenPoints
