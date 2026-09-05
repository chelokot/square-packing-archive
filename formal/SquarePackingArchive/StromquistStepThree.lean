import SquarePackingArchive.StromquistTenBoundary

namespace SquarePackingArchive.Stromquist.TenPoints

lemma NamedFamily.bottom_contains_right_point_of_stepThree_unavoidable
    (family : NamedFamily)
    (coverage : Unavoidable stepThreePoints side)
    (corner_right : (family.squares 0).Contains ⟨6 / 5, 1⟩) :
    (family.squares 7).Contains ⟨2, 1⟩ := by
  have replacement := family.contains_left_replacement (height := side - 49 / 25)
    (by rfl) (by dsimp [side]; linarith [gap_bounds.2])
  have swapped_excluded := family.outer_excludes_swapped_inner_points (owner := 7) (by norm_num)
  obtain ⟨index, inside⟩ := coverage (family.squares 7) (family.fits 7)
  fin_cases index
  · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 0) inside)
  · exact False.elim (family.excludes_other (by decide : (7 : Fin 10) ≠ 0) corner_right inside)
  · exact False.elim (family.excludes_other (by decide : (7 : Fin 10) ≠ 1) replacement inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 2) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 3) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 4) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 5) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 6) inside)
  · exact inside
  · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 8) inside)
  · exact False.elim (family.excludes_other_named_point (by decide : (7 : Fin 10) ≠ 9) inside)
  · exact False.elim (swapped_excluded.1 inside)
  · exact False.elim (swapped_excluded.2 inside)

end SquarePackingArchive.Stromquist.TenPoints
