import SquarePackingArchive.QuadraticCertificate
import SquarePackingArchive.EvidenceAudit

namespace SquarePackingArchive.QuadraticCertificateChecks

example : (⟨-1, 1⟩ : QuadraticNumber 2).Nonnegative := by decide +kernel
example : ¬(⟨-2, 1⟩ : QuadraticNumber 2).Nonnegative := by decide +kernel
example : (⟨2, -1⟩ : QuadraticNumber 2).Nonnegative := by decide +kernel
example : ¬(⟨1, -1⟩ : QuadraticNumber 2).Nonnegative := by decide +kernel
example : (⟨-2, 1⟩ : QuadraticNumber 4).Nonnegative := by decide +kernel
example : (⟨0, -3⟩ : QuadraticNumber 0).Nonnegative := by decide +kernel

def rotatedPair : QuadraticCertificate 2 2 where
  side := ⟨0, 2⟩
  squares := #v[
    { centerX := ⟨0, 1 / 2⟩
      centerY := ⟨0, 1 / 2⟩
      cosine := ⟨0, 1 / 2⟩
      sine := ⟨0, 1 / 2⟩ },
    { centerX := ⟨0, 3 / 2⟩
      centerY := ⟨0, 1 / 2⟩
      cosine := ⟨0, 1 / 2⟩
      sine := ⟨0, 1 / 2⟩ }]
  separatingAxes := #v[
    #v[.leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal]]

theorem rotatedPair_valid : rotatedPair.Valid := by decide +kernel

theorem rotatedPair_valid_from_rows : rotatedPair.Valid := by
  apply QuadraticCertificate.valid_of_rows
  · decide +kernel
  · decide +kernel

theorem rotatedPair_sound : HasPacking 2 (2 * Real.sqrt 2) := by
  simpa [rotatedPair, QuadraticNumber.toReal] using
    QuadraticCertificate.valid_sound rotatedPair_valid

def radicalSevenSquare : QuadraticCertificate 7 1 where
  side := ⟨3 / 4, 1 / 4⟩
  squares := #v[
    { centerX := ⟨3 / 8, 1 / 8⟩
      centerY := ⟨3 / 8, 1 / 8⟩
      cosine := ⟨3 / 4, 0⟩
      sine := ⟨0, -1 / 4⟩ }]
  separatingAxes := #v[#v[.leftVertical]]

theorem radicalSevenSquare_valid : radicalSevenSquare.Valid := by decide +kernel

theorem radicalSevenSquare_sound : HasPacking 1 (3 / 4 + Real.sqrt 7 / 4) := by
  convert QuadraticCertificate.valid_sound radicalSevenSquare_valid using 1
  simp [radicalSevenSquare, QuadraticNumber.toReal]
  ring

assert_standard_axioms QuadraticNumber.nonnegative_iff
assert_standard_axioms QuadraticCertificate.valid_sound
assert_standard_axioms rotatedPair_valid_from_rows
assert_standard_axioms rotatedPair_sound
assert_standard_axioms radicalSevenSquare_sound

end SquarePackingArchive.QuadraticCertificateChecks
