import SquarePackingArchive.QuadraticCertificate
import Mathlib.Tactic.FinCases

namespace SquarePackingArchive.Records.Square11Hamalainen1980

def certificate : QuadraticCertificate 2 11 where
  side := { rational := (2 : ℚ), radical := ((4 : ℚ) / 3) }
  squares := #v[
    { centerX := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := ((3 : ℚ) / 2), radical := ((4 : ℚ) / 3) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := ((4 : ℚ) / 3) }, centerY := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((1 : ℚ) / 2), radical := ((4 : ℚ) / 3) }, centerY := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := ((4 : ℚ) / 3) }, centerY := { rational := ((3 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := ((4 : ℚ) / 3) }, centerY := { rational := ((5 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (0 : ℚ), radical := ((5 : ℚ) / 3) }, centerY := { rational := (2 : ℚ), radical := ((5 : ℚ) / 6) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } },
    { centerX := { rational := (1 : ℚ), radical := ((5 : ℚ) / 6) }, centerY := { rational := (1 : ℚ), radical := ((2 : ℚ) / 3) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } },
    { centerX := { rational := (1 : ℚ), radical := ((1 : ℚ) / 3) }, centerY := { rational := (1 : ℚ), radical := ((7 : ℚ) / 6) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } },
    { centerX := { rational := (0 : ℚ), radical := (1 : ℚ) }, centerY := { rational := (2 : ℚ), radical := ((-1 : ℚ) / 2) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } },
    { centerX := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, centerY := { rational := (2 : ℚ), radical := (0 : ℚ) }, cosine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) }, sine := { rational := (0 : ℚ), radical := ((1 : ℚ) / 2) } }
  ]
  separatingAxes := #v[
    #v[.leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .rightHorizontal, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightVertical, .leftVertical, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftVertical, .rightVertical, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal]
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

theorem upper_bound : HasPacking 11 (((2 : ℚ) : ℝ) + (((4 : ℚ) / 3) : ℝ) * Real.sqrt 2) := by
  simpa [certificate, QuadraticNumber.toReal] using QuadraticCertificate.valid_sound certificate_valid

end SquarePackingArchive.Records.Square11Hamalainen1980
