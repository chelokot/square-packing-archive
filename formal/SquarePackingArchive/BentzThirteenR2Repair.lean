import SquarePackingArchive.BentzThirteenR3Repair

namespace SquarePackingArchive.BentzThirteen

noncomputable def printedR2LeftPoints (index : Fin 20) : Point :=
  if index.val < 9 then printedR3Points (index.castLE (by decide)) else
    match index.val with
    | 9 => ⟨5 / 2, 59 / 25⟩
    | 10 => ⟨5 / 2, 309 / 100⟩
    | 11 => ⟨2, 68 / 25⟩
    | 12 => ⟨5 / 2, 1⟩
    | 13 => ⟨31 / 10, 1⟩
    | 14 => ⟨5 / 2, 8 / 5⟩
    | 15 => ⟨8 / 5, 39 / 20⟩
    | 16 => ⟨31 / 10, 2⟩
    | 17 => ⟨1, 68 / 25⟩
    | 18 => ⟨1, 3⟩
    | _ => ⟨9 / 5, 3⟩

def r2LeftGapCertificate : RationalSquare :=
  ⟨569 / 200, 109 / 40, 20 / 29, 21 / 29⟩

def r2LeftGapSquare : PlacedSquare :=
  r2LeftGapCertificate.toPlacedSquare
    (by norm_num [RationalSquare.IsUnit, r2LeftGapCertificate])

theorem r2LeftGapSquare_fits : r2LeftGapSquare.Fits 4 := by
  exact RationalSquare.fits_sound (side := 4) (square := r2LeftGapCertificate)
    (by norm_num [RationalSquare.IsUnit, r2LeftGapCertificate])
    (by norm_num [RationalSquare.Fits, RationalSquare.extent, r2LeftGapCertificate])

theorem r2LeftGapSquare_misses_printed_points (index : Fin 20) :
    ¬ r2LeftGapSquare.Contains (printedR2LeftPoints index) := by
  rw [PlacedSquare.contains_iff_localCoordinates]
  fin_cases index <;>
    norm_num [printedR2LeftPoints, printedR3Points, r2LeftGapSquare, r2LeftGapCertificate,
      RationalSquare.toPlacedSquare, PlacedSquare.localX, PlacedSquare.localY]

theorem printedR2LeftPoints_not_unavoidable : ¬ Unavoidable printedR2LeftPoints 4 := by
  intro unavoidable
  obtain ⟨index, inside⟩ := unavoidable r2LeftGapSquare r2LeftGapSquare_fits
  exact r2LeftGapSquare_misses_printed_points index inside

theorem r2LeftGapSquare_contains_extra_point : r2LeftGapSquare.Contains ⟨31 / 10, 3⟩ := by
  rw [PlacedSquare.contains_iff_localCoordinates]
  norm_num [r2LeftGapSquare, r2LeftGapCertificate, RationalSquare.toPlacedSquare,
    PlacedSquare.localX, PlacedSquare.localY]

end SquarePackingArchive.BentzThirteen
