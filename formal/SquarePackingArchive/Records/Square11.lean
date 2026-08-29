import SquarePackingArchive.RationalCertificate

namespace SquarePackingArchive.Records.Square11TrumpRationalized

def certificate : RationalCertificate 11 where
  side := ((97 : ℚ) / 25)
  squares := #v[
    { centerX := ((1250940271827222167 : ℚ) / 2500000000000000000), centerY := ((1250940271827222167 : ℚ) / 2500000000000000000), cosine := (1 : ℚ), sine := (0 : ℚ) },
    { centerX := ((8449059728172777833 : ℚ) / 2500000000000000000), centerY := ((1250940271827222167 : ℚ) / 2500000000000000000), cosine := (1 : ℚ), sine := (0 : ℚ) },
    { centerX := ((3168079186170797541 : ℚ) / 1250000000000000000), centerY := ((8449059728172777833 : ℚ) / 2500000000000000000), cosine := (1 : ℚ), sine := (0 : ℚ) },
    { centerX := ((1501128326192666193 : ℚ) / 1000000000000000000), centerY := ((8449059728172777833 : ℚ) / 2500000000000000000), cosine := (1 : ℚ), sine := (0 : ℚ) },
    { centerX := ((1250940271827222167 : ℚ) / 2500000000000000000), centerY := ((2378871673807333807 : ℚ) / 1000000000000000000), cosine := (1 : ℚ), sine := (0 : ℚ) },
    { centerX := ((1250940271827222167 : ℚ) / 2500000000000000000), centerY := ((8449059728172777833 : ℚ) / 2500000000000000000), cosine := (1 : ℚ), sine := (0 : ℚ) },
    { centerX := ((3183027269101046369 : ℚ) / 2500000000000000000), centerY := ((454265879245737829 : ℚ) / 312500000000000000), cosine := ((77515847360419276466481633746633 : ℚ) / 101460603096307362421148154551785), sine := ((65464092361099722404348976642744 : ℚ) / 101460603096307362421148154551785) },
    { centerX := ((968965772013474574407 : ℚ) / 500000000000000000000), centerY := ((705138188430840623 : ℚ) / 1000000000000000000), cosine := ((77515847360419276466481633746633 : ℚ) / 101460603096307362421148154551785), sine := ((65464092361099722404348976642744 : ℚ) / 101460603096307362421148154551785) },
    { centerX := ((98054344143962241221 : ℚ) / 50000000000000000000), centerY := ((1095085568166603233 : ℚ) / 500000000000000000), cosine := ((77515847360419276466481633746633 : ℚ) / 101460603096307362421148154551785), sine := ((65464092361099722404348976642744 : ℚ) / 101460603096307362421148154551785) },
    { centerX := ((6564518798164438001 : ℚ) / 2500000000000000000), centerY := ((7208292555888428047 : ℚ) / 5000000000000000000), cosine := ((77515847360419276466481633746633 : ℚ) / 101460603096307362421148154551785), sine := ((65464092361099722404348976642744 : ℚ) / 101460603096307362421148154551785) },
    { centerX := ((15874309057845799019 : ℚ) / 5000000000000000000), centerY := ((11712785988223248861 : ℚ) / 5000000000000000000), cosine := ((77515847360419276466481633746633 : ℚ) / 101460603096307362421148154551785), sine := ((65464092361099722404348976642744 : ℚ) / 101460603096307362421148154551785) }
  ]
  separatingAxes := #v[
    #v[.leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftVertical, .leftVertical, .rightHorizontal, .leftHorizontal, .rightHorizontal, .rightHorizontal, .rightHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightVertical, .rightVertical, .leftVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightHorizontal, .leftVertical, .rightHorizontal, .leftVertical, .rightVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftVertical, .rightVertical, .rightVertical, .rightVertical],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .rightVertical, .rightVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .rightVertical, .rightVertical, .rightVertical, .rightVertical, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftVertical, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal],
    #v[.leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal, .leftHorizontal]
  ]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem certificate_valid : certificate.Valid := by decide +kernel

theorem s11_le_3_88 : HasPacking 11 (((97 : ℚ) / 25) : ℝ) :=
  by simpa [certificate] using RationalCertificate.valid_sound certificate_valid

end SquarePackingArchive.Records.Square11TrumpRationalized
