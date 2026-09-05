import SquarePackingArchive.QuadraticCertificate
import Mathlib.Tactic.FinCases

namespace SquarePackingArchive.Records.Square19Cottingham1979

def certificate : QuadraticCertificate 2 19 where
  side := { rational := ((7 : ℚ) / 2), radical := (1 : ℚ) }
  squares := #v[
    { centerX := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (3 : ℚ), radical := (1 : ℚ) }, centerY := { rational := (3 : ℚ), radical := (1 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := (3 : ℚ), radical := (1 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := (2 : ℚ), radical := (1 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := (3 : ℚ), radical := (1 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (3 : ℚ), radical := (1 : ℚ) }, centerY := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (3 : ℚ), radical := (1 : ℚ) }, centerY := { rational := ((3 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (3 : ℚ), radical := (1 : ℚ) }, centerY := { rational := ((5 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (2 : ℚ), radical := (1 : ℚ) }, centerY := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (2 : ℚ), radical := (1 : ℚ) }, centerY := { rational := ((3 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (1 : ℚ), radical := (1 : ℚ) }, centerY := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := (2 : ℚ), radical := ((-1 : ℚ) / 2) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := ((-1 : ℚ) / 2) }, centerY := { rational := (2 : ℚ), radical := (0 : ℚ) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := ((1 : ℚ) / 2) }, centerY := { rational := (2 : ℚ), radical := (0 : ℚ) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := (2 : ℚ), radical := ((1 : ℚ) / 2) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := (1 : ℚ) }, centerY := { rational := (2 : ℚ), radical := ((1 : ℚ) / 2) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := ((1 : ℚ) / 2) }, centerY := { rational := (2 : ℚ), radical := (1 : ℚ) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := ((3 : ℚ) / 2) }, centerY := { rational := (2 : ℚ), radical := (1 : ℚ) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := (1 : ℚ) }, centerY := { rational := (2 : ℚ), radical := ((3 : ℚ) / 2) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } }
  ]
  separatingAxes := #v[
    #v[.leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightHorizontal, .leftVertical, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftHorizontal, .rightVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftVertical, .leftVertical, .leftVertical, .leftHorizontal, .rightVertical, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightVertical, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftVertical, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftVertical, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightVertical, .leftHorizontal, .leftVertical, .leftVertical, .leftVertical, .leftVertical, .leftHorizontal, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal]
  ]

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem boundaries_valid : certificate.BoundariesValid := by decide +kernel

private theorem separated_row_0 : certificate.SeparatedRow 0 := by decide +kernel

private theorem separated_row_1 : certificate.SeparatedRow 1 := by decide +kernel

private theorem separated_row_2 : certificate.SeparatedRow 2 := by decide +kernel

private theorem separated_row_3 : certificate.SeparatedRow 3 := by decide +kernel

private theorem separated_row_4 : certificate.SeparatedRow 4 := by decide +kernel

private theorem separated_row_5 : certificate.SeparatedRow 5 := by decide +kernel

private theorem separated_row_6 : certificate.SeparatedRow 6 := by decide +kernel

private theorem separated_row_7 : certificate.SeparatedRow 7 := by decide +kernel

private theorem separated_row_8 : certificate.SeparatedRow 8 := by decide +kernel

private theorem separated_row_9 : certificate.SeparatedRow 9 := by decide +kernel

private theorem separated_row_10 : certificate.SeparatedRow 10 := by decide +kernel

private theorem separated_row_11 : certificate.SeparatedRow 11 := by decide +kernel

private theorem separated_row_12 : certificate.SeparatedRow 12 := by decide +kernel

private theorem separated_row_13 : certificate.SeparatedRow 13 := by decide +kernel

private theorem separated_row_14 : certificate.SeparatedRow 14 := by decide +kernel

private theorem separated_row_15 : certificate.SeparatedRow 15 := by decide +kernel

private theorem separated_row_16 : certificate.SeparatedRow 16 := by decide +kernel

private theorem separated_row_17 : certificate.SeparatedRow 17 := by decide +kernel

private theorem separated_row_18 : certificate.SeparatedRow 18 := by decide +kernel

theorem certificate_valid : certificate.Valid := by
  apply QuadraticCertificate.valid_of_rows boundaries_valid
  intro left
  fin_cases left
  · exact separated_row_0
  · exact separated_row_1
  · exact separated_row_2
  · exact separated_row_3
  · exact separated_row_4
  · exact separated_row_5
  · exact separated_row_6
  · exact separated_row_7
  · exact separated_row_8
  · exact separated_row_9
  · exact separated_row_10
  · exact separated_row_11
  · exact separated_row_12
  · exact separated_row_13
  · exact separated_row_14
  · exact separated_row_15
  · exact separated_row_16
  · exact separated_row_17
  · exact separated_row_18

theorem upper_bound : HasPacking 19 ((((7 : ℚ) / 2) : ℝ) + ((1 : ℚ) : ℝ) * Real.sqrt 2) := by
  simpa [certificate, QuadraticNumber.toReal] using QuadraticCertificate.valid_sound certificate_valid

end SquarePackingArchive.Records.Square19Cottingham1979
