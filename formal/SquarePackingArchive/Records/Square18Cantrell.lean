import SquarePackingArchive.QuadraticCertificate
import Mathlib.Tactic.FinCases

namespace SquarePackingArchive.Records.Square18Cantrell

def certificate : QuadraticCertificate 7 18 where
  side := { rational := ((7 : ℚ) / 2), radical := ((1 : ℚ) / 2) }
  squares := #v[
    { centerX := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := (3 : ℚ), radical := ((1 : ℚ) / 2) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := (3 : ℚ), radical := ((1 : ℚ) / 2) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((5 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := (3 : ℚ), radical := ((1 : ℚ) / 2) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := (2 : ℚ), radical := ((1 : ℚ) / 2) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((3 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := (2 : ℚ), radical := ((1 : ℚ) / 2) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := (1 : ℚ), radical := ((1 : ℚ) / 2) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, centerY := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (3 : ℚ), radical := ((1 : ℚ) / 2) }, centerY := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (2 : ℚ), radical := ((1 : ℚ) / 2) }, centerY := { rational := ((1 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (3 : ℚ), radical := ((1 : ℚ) / 2) }, centerY := { rational := ((3 : ℚ) / 2), radical := (0 : ℚ) }, cosine := { rational := (1 : ℚ), radical := (0 : ℚ) }, sine := { rational := (0 : ℚ), radical := (0 : ℚ) } },
    { centerX := { rational := (3 : ℚ), radical := ((1 : ℚ) / 4) }, centerY := { rational := ((7 : ℚ) / 2), radical := ((1 : ℚ) / 4) }, cosine := { rational := ((1 : ℚ) / 4), radical := ((1 : ℚ) / 4) }, sine := { rational := ((-1 : ℚ) / 4), radical := ((1 : ℚ) / 4) } },
    { centerX := { rational := ((7 : ℚ) / 2), radical := ((1 : ℚ) / 4) }, centerY := { rational := ((29 : ℚ) / 6), radical := ((-7 : ℚ) / 12) }, cosine := { rational := ((1 : ℚ) / 4), radical := ((1 : ℚ) / 4) }, sine := { rational := ((-1 : ℚ) / 4), radical := ((1 : ℚ) / 4) } },
    { centerX := { rational := ((11 : ℚ) / 4), radical := (0 : ℚ) }, centerY := { rational := ((5 : ℚ) / 2), radical := ((1 : ℚ) / 4) }, cosine := { rational := ((1 : ℚ) / 4), radical := ((1 : ℚ) / 4) }, sine := { rational := ((-1 : ℚ) / 4), radical := ((1 : ℚ) / 4) } },
    { centerX := { rational := ((19 : ℚ) / 8), radical := ((-1 : ℚ) / 8) }, centerY := { rational := ((21 : ℚ) / 8), radical := ((-1 : ℚ) / 8) }, cosine := { rational := ((1 : ℚ) / 4), radical := ((1 : ℚ) / 4) }, sine := { rational := ((-1 : ℚ) / 4), radical := ((1 : ℚ) / 4) } },
    { centerX := { rational := ((119 : ℚ) / 32), radical := ((-3 : ℚ) / 32) }, centerY := { rational := ((449 : ℚ) / 96), radical := ((-83 : ℚ) / 96) }, cosine := { rational := ((1 : ℚ) / 4), radical := ((1 : ℚ) / 4) }, sine := { rational := ((-1 : ℚ) / 4), radical := ((1 : ℚ) / 4) } },
    { centerX := { rational := ((107 : ℚ) / 32), radical := ((-7 : ℚ) / 32) }, centerY := { rational := ((461 : ℚ) / 96), radical := ((-119 : ℚ) / 96) }, cosine := { rational := ((1 : ℚ) / 4), radical := ((1 : ℚ) / 4) }, sine := { rational := ((-1 : ℚ) / 4), radical := ((1 : ℚ) / 4) } },
    { centerX := { rational := ((53527 : ℚ) / 43808), radical := ((1839 : ℚ) / 43808) }, centerY := { rational := ((1885 : ℚ) / 43808), radical := ((23043 : ℚ) / 43808) }, cosine := { rational := ((69 : ℚ) / 74), radical := ((-3 : ℚ) / 148) }, sine := { rational := ((23 : ℚ) / 148), radical := ((9 : ℚ) / 74) } },
    { centerX := { rational := ((1267 : ℚ) / 666), radical := ((2 : ℚ) / 37) }, centerY := { rational := ((161 : ℚ) / 296), radical := ((15 : ℚ) / 296) }, cosine := { rational := ((69 : ℚ) / 74), radical := ((-3 : ℚ) / 148) }, sine := { rational := ((23 : ℚ) / 148), radical := ((9 : ℚ) / 74) } }
  ]
  separatingAxes := #v[
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftVertical, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftVertical, .leftVertical, .leftVertical, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightVertical, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightVertical, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftVertical, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftVertical, .leftHorizontal, .leftVertical, .rightVertical, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftHorizontal, .leftHorizontal, .rightVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .rightHorizontal, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal]
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

theorem upper_bound : HasPacking 18 ((((7 : ℚ) / 2) : ℝ) + (((1 : ℚ) / 2) : ℝ) * Real.sqrt 7) := by
  simpa [certificate, QuadraticNumber.toReal] using QuadraticCertificate.valid_sound certificate_valid

end SquarePackingArchive.Records.Square18Cantrell
