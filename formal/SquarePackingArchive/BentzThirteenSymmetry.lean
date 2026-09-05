import SquarePackingArchive.BentzThirteenFamily
import SquarePackingArchive.BentzThirteenReplacement

namespace SquarePackingArchive.BentzThirteen

open Records.Square13

namespace Family

def reflectX (family : Family) : Family where
  squares owner := (family.squares owner).reflectX 4
  fits owner := ((family.squares owner).reflectX_fits_iff 4).mpr (family.fits owner)
  disjoint first second different point shared := by
    apply family.disjoint first second different (point.reflectX 4)
    constructor
    · exact ((family.squares first).reflectX_contains_iff 4 (point.reflectX 4)).mp (by simpa using shared.1)
    · exact ((family.squares second).reflectX_contains_iff 4 (point.reflectX 4)).mp (by simpa using shared.2)

def reflectY (family : Family) : Family where
  squares owner := (family.squares owner).reflectY 4
  fits owner := ((family.squares owner).reflectY_fits_iff 4).mpr (family.fits owner)
  disjoint first second different point shared := by
    apply family.disjoint first second different (point.reflectY 4)
    constructor
    · exact ((family.squares first).reflectY_contains_iff 4 (point.reflectY 4)).mp (by simpa using shared.1)
    · exact ((family.squares second).reflectY_contains_iff 4 (point.reflectY 4)).mp (by simpa using shared.2)

def swap (family : Family) : Family where
  squares owner := (family.squares owner).swap
  fits owner := ((family.squares owner).swap_fits_iff 4).mpr (family.fits owner)
  disjoint first second different point shared := by
    apply family.disjoint first second different point.swap
    constructor
    · exact ((family.squares first).swap_contains_iff point.swap).mp (by simpa using shared.1)
    · exact ((family.squares second).swap_contains_iff point.swap).mp (by simpa using shared.2)

theorem Restricted.reflectX {family : Family} {owner : Fin 13} {anchor : Fin 16}
    (restricted : family.Restricted owner anchor) :
    family.reflectX.Restricted owner (reflectXIndex anchor) := by
  have involutive : Function.Involutive reflectXIndex := by
    intro index; fin_cases index <;> rfl
  intro index
  have reflected : (family.reflectX.squares owner).Contains (initialPoints index) ↔
      (family.squares owner).Contains (initialPoints (reflectXIndex index)) := by
    rw [initialPoints_reflectX]
    simpa [Family.reflectX] using (family.squares owner).reflectX_contains_iff 4 ((initialPoints index).reflectX 4)
  rw [reflected, restricted]
  exact ⟨fun equal => by rw [← equal, involutive], fun equal => by rw [equal, involutive]⟩

theorem Restricted.reflectY {family : Family} {owner : Fin 13} {anchor : Fin 16}
    (restricted : family.Restricted owner anchor) :
    family.reflectY.Restricted owner (reflectYIndex anchor) := by
  have involutive : Function.Involutive reflectYIndex := by
    intro index; fin_cases index <;> rfl
  intro index
  have reflected : (family.reflectY.squares owner).Contains (initialPoints index) ↔
      (family.squares owner).Contains (initialPoints (reflectYIndex index)) := by
    rw [initialPoints_reflectY]
    simpa [Family.reflectY] using (family.squares owner).reflectY_contains_iff 4 ((initialPoints index).reflectY 4)
  rw [reflected, restricted]
  exact ⟨fun equal => by rw [← equal, involutive], fun equal => by rw [equal, involutive]⟩

theorem Restricted.swap {family : Family} {owner : Fin 13} {anchor : Fin 16}
    (restricted : family.Restricted owner anchor) :
    family.swap.Restricted owner (swapIndex anchor) := by
  have involutive : Function.Involutive swapIndex := by
    intro index; fin_cases index <;> rfl
  intro index
  have swapped : (family.swap.squares owner).Contains (initialPoints index) ↔
      (family.squares owner).Contains (initialPoints (swapIndex index)) := by
    rw [initialPoints_swap]
    simpa [Family.swap] using (family.squares owner).swap_contains_iff (initialPoints index).swap
  rw [swapped, restricted]
  exact ⟨fun equal => by rw [← equal, involutive], fun equal => by rw [equal, involutive]⟩

@[simp] theorem reflectX_contains (family : Family) (owner : Fin 13) (point : Point) :
    (family.reflectX.squares owner).Contains point ↔
      (family.squares owner).Contains (point.reflectX 4) := by
  simpa [Family.reflectX] using (family.squares owner).reflectX_contains_iff 4 (point.reflectX 4)

@[simp] theorem reflectY_contains (family : Family) (owner : Fin 13) (point : Point) :
    (family.reflectY.squares owner).Contains point ↔
      (family.squares owner).Contains (point.reflectY 4) := by
  simpa [Family.reflectY] using (family.squares owner).reflectY_contains_iff 4 (point.reflectY 4)

@[simp] theorem swap_contains (family : Family) (owner : Fin 13) (point : Point) :
    (family.swap.squares owner).Contains point ↔ (family.squares owner).Contains point.swap := by
  simpa [Family.swap] using (family.squares owner).swap_contains_iff point.swap

def orient (family : Family) (corner : Fin 8) : Family :=
  match corner.val with
  | 0 => family
  | 1 => family.swap
  | 2 => family.reflectX
  | 3 => family.reflectX.swap
  | 4 => family.reflectY
  | 5 => family.reflectY.swap
  | 6 => family.reflectY.reflectX
  | _ => family.reflectY.reflectX.swap

def orientIndex (corner : Fin 8) (index : Fin 16) : Fin 16 :=
  match corner.val with
  | 0 => index
  | 1 => swapIndex index
  | 2 => reflectXIndex index
  | 3 => swapIndex (reflectXIndex index)
  | 4 => reflectYIndex index
  | 5 => swapIndex (reflectYIndex index)
  | 6 => reflectXIndex (reflectYIndex index)
  | _ => swapIndex (reflectXIndex (reflectYIndex index))

theorem Restricted.orient {family : Family} {owner : Fin 13} {anchor : Fin 16}
    (restricted : family.Restricted owner anchor) (corner : Fin 8) :
    (family.orient corner).Restricted owner (orientIndex corner anchor) := by
  fin_cases corner
  · exact restricted
  · exact restricted.swap
  · exact restricted.reflectX
  · exact restricted.reflectX.swap
  · exact restricted.reflectY
  · exact restricted.reflectY.swap
  · exact restricted.reflectY.reflectX
  · exact restricted.reflectY.reflectX.swap

theorem orientIndex_corner (corner : Fin 8) : orientIndex corner ⟨corner.val, by omega⟩ = 0 := by
  revert corner
  decide +kernel

theorem orientIndex_preserves_corner (corner : Fin 8) (index : Fin 16) (bound : index.val < 8) :
    (orientIndex corner index).val < 8 := by
  revert corner index
  decide +kernel

theorem orientIndex_injective (corner : Fin 8) : Function.Injective (orientIndex corner) := by
  revert corner
  decide +kernel

def unorientPoint (corner : Fin 8) (point : Point) : Point :=
  match corner.val with
  | 0 => point
  | 1 => point.swap
  | 2 => point.reflectX 4
  | 3 => point.swap.reflectX 4
  | 4 => point.reflectY 4
  | 5 => point.swap.reflectY 4
  | 6 => (point.reflectX 4).reflectY 4
  | _ => (point.swap.reflectX 4).reflectY 4

theorem orient_contains (family : Family) (corner : Fin 8) (owner : Fin 13) (point : Point) :
    ((family.orient corner).squares owner).Contains point ↔
      (family.squares owner).Contains (unorientPoint corner point) := by
  fin_cases corner <;> simp [orient, unorientPoint]

theorem Restricted.corner_segment {family : Family} {owner : Fin 13} {anchor : Fin 16}
    (restricted : family.Restricted owner anchor) (corner_bound : anchor.val < 8)
    {horizontal : ℝ} (horizontal_bounds : 28 / 25 ≤ horizontal ∧ horizontal ≤ 87 / 50) :
    (family.squares owner).Contains (unorientPoint ⟨anchor.val, corner_bound⟩ ⟨horizontal, 1⟩) := by
  let corner : Fin 8 := ⟨anchor.val, corner_bound⟩
  have normalized : orientIndex corner anchor = 0 := orientIndex_corner corner
  have only_anchor : (family.orient corner).Restricted owner 0 := by
    simpa only [normalized] using restricted.orient corner
  exact (family.orient_contains corner owner ⟨horizontal, 1⟩).mp
    (corner_restricted_horizontal_segment ((family.orient corner).fits owner) only_anchor horizontal_bounds)

theorem normalized_restricted_corners (family : Family) :
    ∃ oriented : Family, ∃ first second : Fin 13, ∃ other : Fin 16,
      other.val < 8 ∧ other ≠ 0 ∧
        oriented.Restricted first 0 ∧ oriented.Restricted second other := by
  obtain ⟨first, second, left, right, left_corner, right_corner, different,
    first_restricted, second_restricted⟩ := family.two_restricted_corners
  let corner : Fin 8 := ⟨left.val, left_corner⟩
  have normalized : orientIndex corner left = 0 := orientIndex_corner corner
  refine ⟨family.orient corner, first, second, orientIndex corner right,
    orientIndex_preserves_corner corner right right_corner, ?_, ?_, second_restricted.orient corner⟩
  · intro zero
    exact different ((orientIndex_injective corner) (normalized.trans zero.symm))
  · simpa only [normalized] using first_restricted.orient corner

end Family
end SquarePackingArchive.BentzThirteen
