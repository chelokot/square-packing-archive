import SquarePackingArchive.RationalCertificate
import SquarePackingArchive.Unavoidable

namespace SquarePackingArchive.BentzThirteen

noncomputable def printedR3Points (index : Fin 22) : Point :=
  match index.val with
  | 0 => ⟨1, 457 / 500⟩
  | 1 => ⟨113 / 100, 1⟩
  | 2 => ⟨7 / 5, 1⟩
  | 3 => ⟨87 / 50, 1⟩
  | 4 => ⟨187 / 100, 19 / 25⟩
  | 5 => ⟨457 / 500, 1⟩
  | 6 => ⟨1, 113 / 100⟩
  | 7 => ⟨1, 91 / 50⟩
  | 8 => ⟨19 / 25, 49 / 25⟩
  | 9 => ⟨5 / 2, 91 / 50⟩
  | 10 => ⟨5 / 2, 59 / 25⟩
  | 11 => ⟨3, 21 / 10⟩
  | 12 => ⟨23 / 10, 1⟩
  | 13 => ⟨61 / 20, 1⟩
  | 14 => ⟨9 / 5, 9 / 5⟩
  | 15 => ⟨3, 93 / 50⟩
  | 16 => ⟨1, 107 / 50⟩
  | 17 => ⟨2, 107 / 50⟩
  | 18 => ⟨1, 3⟩
  | 19 => ⟨3 / 2, 3⟩
  | 20 => ⟨23 / 10, 3⟩
  | _ => ⟨31 / 10, 3⟩

def r3GapCertificate : RationalSquare :=
  ⟨7 / 10, 2553 / 1000, 4 / 5, 3 / 5⟩

def r3GapSquare : PlacedSquare :=
  r3GapCertificate.toPlacedSquare (by norm_num [RationalSquare.IsUnit, r3GapCertificate])

theorem r3GapSquare_fits : r3GapSquare.Fits 4 := by
  exact RationalSquare.fits_sound (side := 4) (square := r3GapCertificate)
    (by norm_num [RationalSquare.IsUnit, r3GapCertificate])
    (by norm_num [RationalSquare.Fits, RationalSquare.extent, r3GapCertificate])

theorem r3GapSquare_misses_printed_points (index : Fin 22) :
    ¬ r3GapSquare.Contains (printedR3Points index) := by
  rw [PlacedSquare.contains_iff_localCoordinates]
  fin_cases index <;>
    norm_num [printedR3Points, r3GapSquare, r3GapCertificate, RationalSquare.toPlacedSquare,
      PlacedSquare.localX, PlacedSquare.localY]

theorem printedR3Points_not_unavoidable : ¬ Unavoidable printedR3Points 4 := by
  intro unavoidable
  obtain ⟨index, inside⟩ := unavoidable r3GapSquare r3GapSquare_fits
  exact r3GapSquare_misses_printed_points index inside

theorem r3GapSquare_contains_repaired_point : r3GapSquare.Contains ⟨19 / 20, 3⟩ := by
  rw [PlacedSquare.contains_iff_localCoordinates]
  norm_num [r3GapSquare, r3GapCertificate, RationalSquare.toPlacedSquare,
    PlacedSquare.localX, PlacedSquare.localY]

end SquarePackingArchive.BentzThirteen
