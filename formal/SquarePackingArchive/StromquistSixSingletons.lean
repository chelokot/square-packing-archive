import SquarePackingArchive.StromquistSixAdjacency

namespace SquarePackingArchive.StromquistSix

def KeySingleton (square : PlacedSquare) (selected : Fin 9) : Prop :=
  ∀ index : Fin 9, square.Contains (keyPoints index) ↔ index = selected

theorem keyReflectX_involutive : Function.Involutive keyReflectX := by
  intro index
  fin_cases index <;> rfl

theorem keyReflectY_involutive : Function.Involutive keyReflectY := by
  intro index
  fin_cases index <;> rfl

theorem keySwap_involutive : Function.Involutive keySwap := by
  intro index
  fin_cases index <;> rfl

theorem KeySingleton.reflectX {square : PlacedSquare} {selected : Fin 9}
    (singleton : KeySingleton square selected) : KeySingleton (square.reflectX 3) (keyReflectX selected) := by
  intro index
  have membership : (square.reflectX 3).Contains (keyPoints index) ↔
      square.Contains (keyPoints (keyReflectX index)) := by
    rw [keyPoints_reflectX]
    simpa using square.reflectX_contains_iff 3 ((keyPoints index).reflectX 3)
  rw [membership, singleton]
  exact keyReflectX_involutive.eq_iff

theorem KeySingleton.reflectY {square : PlacedSquare} {selected : Fin 9}
    (singleton : KeySingleton square selected) : KeySingleton (square.reflectY 3) (keyReflectY selected) := by
  intro index
  have membership : (square.reflectY 3).Contains (keyPoints index) ↔
      square.Contains (keyPoints (keyReflectY index)) := by
    rw [keyPoints_reflectY]
    simpa using square.reflectY_contains_iff 3 ((keyPoints index).reflectY 3)
  rw [membership, singleton]
  exact keyReflectY_involutive.eq_iff

theorem KeySingleton.swap {square : PlacedSquare} {selected : Fin 9}
    (singleton : KeySingleton square selected) : KeySingleton square.swap (keySwap selected) := by
  intro index
  have membership : square.swap.Contains (keyPoints index) ↔ square.Contains (keyPoints (keySwap index)) := by
    rw [keyPoints_swap]
    simpa using square.swap_contains_iff (keyPoints index).swap
  rw [membership, singleton]
  exact keySwap_involutive.eq_iff

def SingletonPairIntersects (first second : Fin 9) : Prop :=
  ∀ corner midpoint : PlacedSquare, corner.Fits 3 → midpoint.Fits 3 →
    KeySingleton corner first → KeySingleton midpoint second →
    ∃ point : Point, corner.Contains point ∧ midpoint.Contains point

theorem SingletonPairIntersects.symm {first second : Fin 9}
    (intersection : SingletonPairIntersects first second) : SingletonPairIntersects second first := by
  intro corner midpoint corner_fits midpoint_fits corner_single midpoint_single
  obtain ⟨point, midpoint_mem, corner_mem⟩ := intersection midpoint corner midpoint_fits corner_fits midpoint_single corner_single
  exact ⟨point, corner_mem, midpoint_mem⟩

theorem SingletonPairIntersects.reflectX {first second : Fin 9}
    (intersection : SingletonPairIntersects first second) : SingletonPairIntersects (keyReflectX first) (keyReflectX second) := by
  intro corner midpoint corner_fits midpoint_fits corner_single midpoint_single
  obtain ⟨point, corner_mem, midpoint_mem⟩ := intersection (corner.reflectX 3) (midpoint.reflectX 3)
    ((corner.reflectX_fits_iff 3).2 corner_fits) ((midpoint.reflectX_fits_iff 3).2 midpoint_fits)
    (by simpa only [keyReflectX_involutive first] using corner_single.reflectX)
    (by simpa only [keyReflectX_involutive second] using midpoint_single.reflectX)
  exact ⟨point.reflectX 3, (corner.reflectX_contains_iff 3 _).1 (by simpa using corner_mem),
    (midpoint.reflectX_contains_iff 3 _).1 (by simpa using midpoint_mem)⟩

theorem SingletonPairIntersects.reflectY {first second : Fin 9}
    (intersection : SingletonPairIntersects first second) : SingletonPairIntersects (keyReflectY first) (keyReflectY second) := by
  intro corner midpoint corner_fits midpoint_fits corner_single midpoint_single
  obtain ⟨point, corner_mem, midpoint_mem⟩ := intersection (corner.reflectY 3) (midpoint.reflectY 3)
    ((corner.reflectY_fits_iff 3).2 corner_fits) ((midpoint.reflectY_fits_iff 3).2 midpoint_fits)
    (by simpa only [keyReflectY_involutive first] using corner_single.reflectY)
    (by simpa only [keyReflectY_involutive second] using midpoint_single.reflectY)
  exact ⟨point.reflectY 3, (corner.reflectY_contains_iff 3 _).1 (by simpa using corner_mem),
    (midpoint.reflectY_contains_iff 3 _).1 (by simpa using midpoint_mem)⟩

theorem SingletonPairIntersects.swap {first second : Fin 9}
    (intersection : SingletonPairIntersects first second) : SingletonPairIntersects (keySwap first) (keySwap second) := by
  intro corner midpoint corner_fits midpoint_fits corner_single midpoint_single
  obtain ⟨point, corner_mem, midpoint_mem⟩ := intersection corner.swap midpoint.swap
    ((corner.swap_fits_iff 3).2 corner_fits) ((midpoint.swap_fits_iff 3).2 midpoint_fits)
    (by simpa only [keySwap_involutive first] using corner_single.swap)
    (by simpa only [keySwap_involutive second] using midpoint_single.swap)
  exact ⟨point.swap, (corner.swap_contains_iff _).1 (by simpa using corner_mem),
    (midpoint.swap_contains_iff _).1 (by simpa using midpoint_mem)⟩

theorem bottom_left_singleton_pair_intersects : SingletonPairIntersects 0 1 := by
  intro corner midpoint corner_fits midpoint_fits corner_single midpoint_single
  apply adjacent_singletons_intersect corner_fits midpoint_fits
  · exact (corner_single 0).2 rfl
  · intro inside
    have impossible := (corner_single 3).1 inside
    norm_num [Fin.ext_iff] at impossible
  · exact (midpoint_single 1).2 rfl
  · intro inside
    have impossible := (midpoint_single 0).1 inside
    norm_num [Fin.ext_iff] at impossible
  · intro inside
    have impossible := (midpoint_single 2).1 inside
    norm_num [Fin.ext_iff] at impossible
  · intro inside
    have impossible := (midpoint_single 4).1 inside
    norm_num [Fin.ext_iff] at impossible

theorem perimeter_adjacent_cases : ∀ first second : Fin 9, first ≠ 4 → second ≠ 4 → GridAdjacent first second →
    (first = 0 ∧ second = 1) ∨ (first = 1 ∧ second = 0) ∨
    (first = 0 ∧ second = 3) ∨ (first = 3 ∧ second = 0) ∨
    (first = 2 ∧ second = 1) ∨ (first = 1 ∧ second = 2) ∨
    (first = 2 ∧ second = 5) ∨ (first = 5 ∧ second = 2) ∨
    (first = 6 ∧ second = 3) ∨ (first = 3 ∧ second = 6) ∨
    (first = 8 ∧ second = 5) ∨ (first = 5 ∧ second = 8) ∨
    (first = 6 ∧ second = 7) ∨ (first = 7 ∧ second = 6) ∨
    (first = 8 ∧ second = 7) ∨ (first = 7 ∧ second = 8) := by decide

theorem adjacent_singleton_keyPoints_intersect
    (first second : PlacedSquare) (first_fits : first.Fits 3) (second_fits : second.Fits 3)
    (left right : Fin 9) (left_not_center : left ≠ 4) (right_not_center : right ≠ 4)
    (first_singleton : ∀ index, first.Contains (keyPoints index) ↔ index = left)
    (second_singleton : ∀ index, second.Contains (keyPoints index) ↔ index = right)
    (adjacent : GridAdjacent left right) : ∃ point, first.Contains point ∧ second.Contains point := by
  have base := bottom_left_singleton_pair_intersects
  have applicable : SingletonPairIntersects left right := by
    rcases perimeter_adjacent_cases left right left_not_center right_not_center adjacent with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact base
    · exact base.symm
    · exact base.swap
    · exact base.swap.symm
    · exact base.reflectX
    · exact base.reflectX.symm
    · exact base.swap.reflectX
    · exact base.swap.reflectX.symm
    · exact base.swap.reflectY
    · exact base.swap.reflectY.symm
    · exact base.swap.reflectX.reflectY
    · exact base.swap.reflectX.reflectY.symm
    · exact base.reflectY
    · exact base.reflectY.symm
    · exact base.reflectX.reflectY
    · exact base.reflectX.reflectY.symm
  exact applicable first second first_fits second_fits first_singleton second_singleton

end SquarePackingArchive.StromquistSix
