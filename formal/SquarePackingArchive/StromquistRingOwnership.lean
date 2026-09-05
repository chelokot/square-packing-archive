import SquarePackingArchive.StromquistRing

namespace SquarePackingArchive.Stromquist.TenPoints

lemma rightSegment_of_closed_family
    (named_theorem : ∀ family : NamedFamily, RightSegmentHit (family.squares 7))
    (squares : Fin 10 → PlacedSquare)
    (fits : ∀ index, (squares index).Fits side)
    (disjoint : ∀ first second, first ≠ second → ∀ point,
      ¬ ((squares first).Contains point ∧ (squares second).Contains point))
    (owner : Fin 10) (named_inside : (squares owner).Contains (points 7)) :
    RightSegmentHit (squares owner) := by
  classical
  obtain ⟨assigned, bijective, contained⟩ := disjoint_incidence_assignment
    (fun owner index => (squares owner).Contains (points index))
    (fun first second different index => disjoint first second different (points index))
    (fun owner => unavoidable (squares owner) (fits owner))
  let assignment := Equiv.ofBijective assigned bijective
  let family : NamedFamily := {
    squares := fun index => squares (assignment.symm index)
    fits := fun index => fits (assignment.symm index)
    disjoint := fun first second different => disjoint _ _
      (fun equality => different (assignment.symm.injective equality))
    contains_named_point := by
      intro index
      have source := contained (assignment.symm index)
      change (squares (assignment.symm index)).Contains (points (assignment (assignment.symm index))) at source
      simpa using source }
  have same_owner : owner = assignment.symm 7 := by
    by_contra different
    exact disjoint owner (assignment.symm 7) different (points 7)
      ⟨named_inside, family.contains_named_point 7⟩
  rw [same_owner]
  exact named_theorem family

noncomputable def ringSquareTransform (index : Fin 8) (square : PlacedSquare) : PlacedSquare :=
  match index.val with
  | 0 => square
  | 1 => (square.swap.reflectX side).reflectY side
  | 2 => square.swap.reflectX side
  | 3 => square.reflectY side
  | 4 => (square.reflectX side).reflectY side
  | 5 => square.swap
  | 6 => square.swap.reflectY side
  | _ => square.reflectX side

def ringInverse (index : Fin 8) : Fin 8 :=
  if index.val = 2 then 6 else if index.val = 6 then 2 else index

def ringOwner (index : Fin 8) : Fin 10 :=
  match index.val with
  | 0 => 7
  | 1 => 5
  | 2 => 5
  | 3 => 3
  | 4 => 3
  | 5 => 1
  | 6 => 1
  | _ => 7

lemma ringTransform_inverse (index : Fin 8) (point : Point) :
    ringTransform index (ringTransform (ringInverse index) point) = point := by
  fin_cases index <;> simp [ringTransform, ringInverse, Point.reflectX, Point.reflectY, Point.swap]

lemma ringTransform_contains (index : Fin 8) (square : PlacedSquare) (point : Point) :
    (ringSquareTransform index square).Contains (ringTransform index point) ↔ square.Contains point := by
  fin_cases index <;> simp [ringSquareTransform, ringTransform]

lemma ringTransform_fits (index : Fin 8) (square : PlacedSquare) :
    (ringSquareTransform index square).Fits side ↔ square.Fits side := by
  fin_cases index <;> simp [ringSquareTransform]

lemma ringTransform_named (index : Fin 8) :
    ringTransform index (points 7) = points (ringOwner index) := by
  fin_cases index <;>
    norm_num [ringTransform, ringOwner, points, side, Point.swap, Point.reflectX, Point.reflectY] <;>
    ring_nf
  all_goals simp

lemma ringPoint_transform (index : Fin 8) (parameter : ℝ) :
    ringPoint index parameter = ringTransform index ⟨2 + (3 / 25) * parameter, 1 - parameter / 10⟩ := by
  fin_cases index <;>
    simp [ringPoint, ringStart, ringEnd, ringTransform, Point.interpolate,
      Point.swap, Point.reflectX, Point.reflectY, Point.mk.injEq] <;> ring_nf
  all_goals simp

theorem NamedFamily.ring_ownership_of_rightSegment
    (named_theorem : ∀ family : NamedFamily, RightSegmentHit (family.squares 7))
    (family : NamedFamily) (index : Fin 8) :
    ∃ parameter, 0 ≤ parameter ∧ parameter ≤ 1 ∧
      (family.squares (ringOwner index)).Contains (ringPoint index parameter) := by
  let transformed := fun owner => ringSquareTransform (ringInverse index) (family.squares owner)
  have inverse_inverse : ringInverse (ringInverse index) = index := by
    exact (by decide : ∀ index, ringInverse (ringInverse index) = index) index
  have transferred (owner : Fin 10) (point : Point) :
      (transformed owner).Contains point ↔
        (family.squares owner).Contains (ringTransform index point) := by
    have equivalence := ringTransform_contains (ringInverse index) (family.squares owner)
      (ringTransform index point)
    have inverse_point := ringTransform_inverse (ringInverse index) point
    rw [inverse_inverse] at inverse_point
    simpa only [inverse_point] using equivalence
  have result := rightSegment_of_closed_family named_theorem transformed
    (fun owner => (ringTransform_fits _ _).2 (family.fits owner))
    (fun first second different point inside => family.disjoint first second different
      (ringTransform index point) ⟨(transferred first point).1 inside.1, (transferred second point).1 inside.2⟩)
    (ringOwner index)
    ((transferred (ringOwner index) (points 7)).2 (by rw [ringTransform_named]; exact family.contains_named_point _))
  obtain ⟨parameter, nonnegative, upper, inside⟩ := result
  refine ⟨parameter, nonnegative, upper, ?_⟩
  rw [ringPoint_transform]
  exact (transferred _ _).1 inside

end SquarePackingArchive.Stromquist.TenPoints
