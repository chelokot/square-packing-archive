import SquarePackingArchive.BentzFiveRowsEndpoint
import SquarePackingArchive.BentzExceptionalSquare
import SquarePackingArchive.BentzOrderedChords

namespace SquarePackingArchive.BentzFiveRows

def consecutiveRows (count offset : ℕ) (fits : count + offset ≤ 5) : Fin count ↪ Fin 5 where
  toFun index := ⟨index.val + offset, by omega⟩
  inj' := by
    intro first second same
    apply Fin.ext
    have value_eq := congrArg Fin.val same
    dsimp at value_eq
    omega

@[simp] theorem consecutiveRows_apply (count offset : ℕ) (fits : count + offset ≤ 5) (index : Fin count) :
    consecutiveRows count offset fits index = ⟨index.val + offset, by omega⟩ := rfl

theorem contradiction_of_row_witnesses {side : ℝ} (packing : Packing 22 side)
    (side_lower : 4999 / 1000 ≤ side) (side_lt_five : side < 5)
    (owners : Fin 5 ↪ Fin 22) (exception : Fin 3)
    (half_inside : ∀ row, (packing.squares (owners row)).InteriorContains
      ((Point.mk (1 / 2) (height row)).scale (side / 5)))
    (one_inside : ∀ row, (packing.squares (owners row)).InteriorContains
      ((Point.mk 1 (height row)).scale (side / 5)))
    (left_inside : ∀ row, row ≠ evenBlueRowIndex exception →
      (packing.squares (owners row)).InteriorContains
        ((Point.mk (2 / 5) (height row)).scale (side / 5)))
    (right_missing : ¬ (packing.squares (owners (evenBlueRowIndex exception))).InteriorContains
      ((Point.mk (3 / 2) (height (evenBlueRowIndex exception))).scale (side / 5))) : False := by
  have ratio_lower : 4999 / 5000 ≤ side / 5 := by linarith
  have ratio_upper : side / 5 ≤ 1 := by linarith
  have anchors (row : Fin 5) : (packing.squares (owners row)).InteriorContains
      ⟨451 / 500, (side / 5) * height row⟩ := by
    apply (packing.squares (owners row)).interiorContains_horizontal_between
      (half_inside row) (one_inside row)
    · dsimp [Point.scale]
      linarith
    · dsimp [Point.scale]
      linarith
  have ordinary_chords (row : Fin 5) (ordinary : row ≠ evenBlueRowIndex exception) :
      ∃ lower upper : ℝ, 1 ≤ upper - lower ∧
        ∀ vertical ∈ Set.Ioo lower upper,
          (packing.squares (owners row)).InteriorContains ⟨451 / 500, vertical⟩ := by
    apply Bentz.vertical_unit_chord_of_left_point _ (packing.fits (owners row))
      (left_inside row ordinary).contains
    dsimp [Point.scale]
    linarith
  have exceptional_right : 11 / 10 ≤ (packing.squares (owners (evenBlueRowIndex exception))).center.x := by
    by_contra! left
    have total := Bentz.count_le_side_of_vertical_unit_chords packing owners
      (line := 451 / 500) (fun row => by
        by_cases same : row = evenBlueRowIndex exception
        · subst row
          exact Bentz.vertical_unit_chord_of_center_le_eleven_tenths _
            (packing.fits _) left.le
        · exact ordinary_chords row same)
    norm_num at total
    linarith
  have missing_below {selectedCount : ℕ} (rows : Fin selectedCount ↪ Fin 5)
      (ordinary : ∀ selected, rows selected ≠ evenBlueRowIndex exception) {cutoff : ℝ}
      (below : ∀ selected, (side / 5) * height (rows selected) < cutoff)
      (cutoff_bound : cutoff ≤ selectedCount) :
      ¬ (packing.squares (owners (evenBlueRowIndex exception))).InteriorContains ⟨451 / 500, cutoff⟩ := by
    intro inside
    have count_bound := Bentz.count_lt_cutoff_of_unit_chords_below packing (rows.trans owners)
      (owners (evenBlueRowIndex exception))
      (fun selected same => ordinary selected (owners.injective same))
      (fun selected => (side / 5) * height (rows selected))
      (fun selected => anchors (rows selected)) below
      (fun selected => ordinary_chords (rows selected) (ordinary selected)) inside
    exact (not_lt_of_ge cutoff_bound) count_bound
  have missing_above {selectedCount : ℕ} (rows : Fin selectedCount ↪ Fin 5)
      (ordinary : ∀ selected, rows selected ≠ evenBlueRowIndex exception) {cutoff : ℝ}
      (above : ∀ selected, cutoff < (side / 5) * height (rows selected))
      (cutoff_bound : side - cutoff ≤ selectedCount) :
      ¬ (packing.squares (owners (evenBlueRowIndex exception))).InteriorContains ⟨451 / 500, cutoff⟩ := by
    intro inside
    have count_bound := Bentz.count_lt_remaining_of_unit_chords_above packing (rows.trans owners)
      (owners (evenBlueRowIndex exception))
      (fun selected same => ordinary selected (owners.injective same))
      (fun selected => (side / 5) * height (rows selected))
      (fun selected => anchors (rows selected)) above
      (fun selected => ordinary_chords (rows selected) (ordinary selected)) inside
    exact (not_lt_of_ge cutoff_bound) count_bound
  fin_cases exception
  · have green_missing := missing_above (consecutiveRows 4 1 (by norm_num))
      (by intro selected; fin_cases selected <;> norm_num [Fin.ext_iff, evenBlueRowIndex])
      (cutoff := 1)
      (by intro selected; fin_cases selected <;> norm_num [height] <;> linarith)
      (by norm_num; linarith)
    apply Bentz.bottom_exception_impossible _ ratio_upper (packing.fits _) _ green_missing exceptional_right
    convert (half_inside (evenBlueRowIndex 0)).contains using 1 <;>
      norm_num [Point.scale, height, evenBlueRowIndex]; ring_nf; simp
  · have low_missing := missing_below (consecutiveRows 2 0 (by norm_num))
      (by intro selected; fin_cases selected <;> norm_num [Fin.ext_iff, evenBlueRowIndex])
      (cutoff := 2)
      (by intro selected; fin_cases selected <;> norm_num [height] <;> linarith)
      (by norm_num)
    have high_missing := missing_above (consecutiveRows 2 3 (by norm_num))
      (by intro selected; fin_cases selected <;> norm_num [Fin.ext_iff, evenBlueRowIndex])
      (cutoff := 3)
      (by intro selected; fin_cases selected <;> norm_num [height] <;> linarith)
      (by norm_num; linarith)
    apply Bentz.middle_exception_impossible _ ratio_lower ratio_upper _ _ low_missing high_missing exceptional_right
    · convert (half_inside (evenBlueRowIndex 1)).contains using 1 <;>
        norm_num [Point.scale, height, evenBlueRowIndex]; ring_nf; simp
    · convert right_missing using 1
      norm_num [Point.scale, height, evenBlueRowIndex]; ring_nf
  · have green_missing := missing_below (consecutiveRows 4 0 (by norm_num))
      (by intro selected; fin_cases selected <;> norm_num [Fin.ext_iff, evenBlueRowIndex])
      (cutoff := side - 1)
      (by intro selected; fin_cases selected <;> norm_num [height] <;> linarith)
      (by norm_num; linarith)
    let square := packing.squares (owners (evenBlueRowIndex 2))
    apply Bentz.bottom_exception_impossible (square.reflectY side) ratio_upper
      ((square.reflectY_fits_iff side).2 (packing.fits _)) _ _ exceptional_right
    · have reflected := (square.reflectY_contains_iff side
        ((Point.mk (1 / 2) (height (evenBlueRowIndex 2))).scale (side / 5))).2
        (by simpa [square] using (half_inside (evenBlueRowIndex 2)).contains)
      convert reflected using 1
      norm_num [Point.scale, Point.reflectY, height, evenBlueRowIndex]; ring_nf; simp
    · intro inside
      apply green_missing
      have original := (square.interiorContains_reflectY_iff side ⟨451 / 500, side - 1⟩).1
        (by simpa [Point.reflectY] using inside)
      exact original

end SquarePackingArchive.BentzFiveRows
