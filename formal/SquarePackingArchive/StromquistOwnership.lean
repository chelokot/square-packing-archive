import SquarePackingArchive.StromquistTenPoints
import SquarePackingArchive.PackingPointCapacity

namespace SquarePackingArchive

lemma PlacedSquare.contains_convexCombination
    {square : PlacedSquare} {first second : Point} {parameter : ℝ}
    (parameter_nonnegative : 0 ≤ parameter) (parameter_upper : parameter ≤ 1)
    (first_inside : square.Contains first) (second_inside : square.Contains second) :
    square.Contains ⟨(1 - parameter) * first.x + parameter * second.x,
      (1 - parameter) * first.y + parameter * second.y⟩ := by
  have coordinate_bound (firstCoordinate secondCoordinate : ℝ)
      (first_bound : |firstCoordinate| ≤ 1 / 2)
      (second_bound : |secondCoordinate| ≤ 1 / 2) :
      |(1 - parameter) * firstCoordinate + parameter * secondCoordinate| ≤ 1 / 2 := by
    calc
      _ ≤ |(1 - parameter) * firstCoordinate| + |parameter * secondCoordinate| := abs_add_le _ _
      _ = (1 - parameter) * |firstCoordinate| + parameter * |secondCoordinate| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - parameter),
          abs_of_nonneg parameter_nonnegative]
      _ ≤ (1 - parameter) * (1 / 2) + parameter * (1 / 2) :=
        add_le_add (mul_le_mul_of_nonneg_left first_bound (by linarith))
          (mul_le_mul_of_nonneg_left second_bound parameter_nonnegative)
      _ = 1 / 2 := by ring
  rw [square.contains_iff_localCoordinates] at first_inside second_inside ⊢
  have localX_identity :
      square.localX ⟨(1 - parameter) * first.x + parameter * second.x,
          (1 - parameter) * first.y + parameter * second.y⟩ =
        (1 - parameter) * square.localX first + parameter * square.localX second := by
    dsimp [PlacedSquare.localX]
    ring
  have localY_identity :
      square.localY ⟨(1 - parameter) * first.x + parameter * second.x,
          (1 - parameter) * first.y + parameter * second.y⟩ =
        (1 - parameter) * square.localY first + parameter * square.localY second := by
    dsimp [PlacedSquare.localY]
    ring
  rw [localX_identity, localY_identity]
  exact ⟨coordinate_bound _ _ first_inside.1 second_inside.1,
    coordinate_bound _ _ first_inside.2 second_inside.2⟩

namespace Stromquist.TenPoints

structure NamedFamily where
  squares : Fin 10 → PlacedSquare
  fits : ∀ index, (squares index).Fits side
  disjoint : ∀ first second, first ≠ second → ∀ point,
    ¬ ((squares first).Contains point ∧ (squares second).Contains point)
  contains_named_point : ∀ index, (squares index).Contains (points index)

theorem exists_namedFamily_of_packing_below
    {candidateSide : ℝ} (packing : Packing 10 candidateSide) (smaller : candidateSide < side) :
    Nonempty NamedFamily := by
  classical
  obtain ⟨squares, fits, disjoint⟩ := packing.exists_closed_disjoint_family_in_larger_container
    (by norm_num) smaller
  obtain ⟨assigned, bijective, contained⟩ := disjoint_incidence_assignment
    (fun owner index => (squares owner).Contains (points index))
    (fun first second different index => disjoint first second different (points index))
    (fun owner => unavoidable (squares owner) (fits owner))
  let assignment := Equiv.ofBijective assigned bijective
  refine ⟨{
    squares := fun index => squares (assignment.symm index)
    fits := fun index => fits (assignment.symm index)
    disjoint := fun first second different => disjoint _ _
      (fun equality => different (assignment.symm.injective equality))
    contains_named_point := ?_ }⟩
  intro index
  have source := contained (assignment.symm index)
  change (squares (assignment.symm index)).Contains (points (assignment (assignment.symm index))) at source
  simpa using source

lemma NamedFamily.excludes_other
    (family : NamedFamily) {owner other : Fin 10} {point : Point}
    (different : owner ≠ other) (other_inside : (family.squares other).Contains point) :
    ¬ (family.squares owner).Contains point := by
  intro owner_inside
  exact family.disjoint owner other different point ⟨owner_inside, other_inside⟩

lemma NamedFamily.excludes_other_named_point
    (family : NamedFamily) {owner other : Fin 10} (different : owner ≠ other) :
    ¬ (family.squares owner).Contains (points other) :=
  family.excludes_other different (family.contains_named_point other)

lemma NamedFamily.owns_replacement
    (family : NamedFamily) (owner : Fin 10) (replacement : Point)
    (replacement_unavoidable : ∀ square : PlacedSquare, square.Fits side →
      square.Contains replacement ∨ ∃ index, index ≠ owner ∧ square.Contains (points index)) :
    (family.squares owner).Contains replacement := by
  rcases replacement_unavoidable (family.squares owner) (family.fits owner) with
    replacement_inside | ⟨index, different, original_inside⟩
  · exact replacement_inside
  · exact False.elim (family.excludes_other_named_point different.symm original_inside)

lemma NamedFamily.owns_replacement_pair
    (family : NamedFamily) (owner : Fin 10) (first second : Point)
    (replacement_unavoidable : ∀ square : PlacedSquare, square.Fits side →
      square.Contains first ∨ square.Contains second ∨
        ∃ index, index ≠ owner ∧ square.Contains (points index)) :
    (family.squares owner).Contains first ∨ (family.squares owner).Contains second := by
  rcases replacement_unavoidable (family.squares owner) (family.fits owner) with
    first_inside | second_inside | ⟨index, different, original_inside⟩
  · exact Or.inl first_inside
  · exact Or.inr second_inside
  · exact False.elim (family.excludes_other_named_point different.symm original_inside)

end Stromquist.TenPoints

end SquarePackingArchive
