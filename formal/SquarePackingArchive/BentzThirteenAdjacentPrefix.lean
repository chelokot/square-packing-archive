import SquarePackingArchive.BentzThirteenAdjacentPair
import SquarePackingArchive.BentzAdjacentInitialData

namespace SquarePackingArchive.BentzThirteen.AdjacentPair

theorem initial_first {family : Family} (pair : AdjacentPair family) (index : Fin 6) :
    (family.squares pair.first).Contains (adjacentInitialPoints ⟨index.val, by omega⟩) := by
  fin_cases index
  · exact pair.first_anchor
  · exact pair.first_segment (by norm_num)
  · exact pair.first_segment (by norm_num)
  · exact pair.first_segment (by norm_num)
  · exact pair.first_segment (by norm_num)
  · exact pair.first_lower

theorem initial_second {family : Family} (pair : AdjacentPair family) (index : Fin 4) :
    (family.squares pair.second).Contains (adjacentInitialPoints ⟨index.val + 6, by omega⟩) := by
  fin_cases index
  · exact pair.second_anchor
  · exact pair.second_segment (by norm_num)
  · exact pair.second_extended.1
  · exact pair.second_extended.2

theorem prefix_cards {family : Family} (pair : AdjacentPair family)
    {count : ℕ} (points : Fin count → Point) (ten : 10 ≤ count)
    (prefix_agreement : ∀ index : Fin 10, points ⟨index.val, by omega⟩ =
      adjacentInitialPoints ⟨index.val, by omega⟩) :
    6 ≤ (family.covered points pair.first).card ∧
      4 ≤ (family.covered points pair.second).card := by
  constructor
  · apply family.covered_card_of_embedding points pair.first
      (⟨fun index : Fin 6 => ⟨index.val, by omega⟩,
        fun first second same => Fin.ext (congrArg (fun value : Fin count => value.val) same)⟩ : Fin 6 ↪ Fin count)
    intro index
    change (family.squares pair.first).Contains (points ⟨index.val, by omega⟩)
    rw [prefix_agreement ⟨index.val, by omega⟩]
    exact pair.initial_first index
  · apply family.covered_card_of_embedding points pair.second
      (⟨fun index : Fin 4 => ⟨index.val + 6, by omega⟩,
        fun first second same => Fin.ext (by
          have := congrArg (fun value : Fin count => value.val) same
          dsimp at this
          omega)⟩ :
          Fin 4 ↪ Fin count)
    intro index
    change (family.squares pair.second).Contains (points ⟨index.val + 6, by omega⟩)
    rw [prefix_agreement ⟨index.val + 6, by omega⟩]
    exact pair.initial_second index

theorem initial_cards {family : Family} (pair : AdjacentPair family) :
    6 ≤ (family.covered adjacentInitialPoints pair.first).card ∧
      4 ≤ (family.covered adjacentInitialPoints pair.second).card :=
  pair.prefix_cards adjacentInitialPoints (by norm_num) (fun _ => rfl)

theorem initial_uncovered {family : Family} (pair : AdjacentPair family) :
    ∃ owner, owner ≠ pair.first ∧ owner ≠ pair.second ∧
      ∀ index, ¬ (family.squares owner).Contains (adjacentInitialPoints index) :=
  pair.exists_uncovered adjacentInitialPoints (by norm_num) pair.initial_cards.1 pair.initial_cards.2

end SquarePackingArchive.BentzThirteen.AdjacentPair
