import SquarePackingArchive.BentzBoundaryPairs
import SquarePackingArchive.StromquistRingBoundary

namespace SquarePackingArchive.BentzThirteen.Nonadjacent

def choicePattern (choice : Fin 16) (corner : Fin 4) : Bool :=
  decide (choice.val / 2 ^ corner.val % 2 = 1)

lemma choicePattern_exhaustive (choices : Fin 4 → Bool) :
    ∃ choice, choices = choicePattern choice := by
  exact (by decide : ∀ choices : Fin 4 → Bool, ∃ choice, choices = choicePattern choice) choices

noncomputable def cornerAlternative (choices : Fin 4 → Bool) (corner : Fin 4) : Point :=
  let base : Point := if choices corner then ⟨457 / 500, 1⟩ else ⟨1, 457 / 500⟩
  match corner.val with
  | 0 => base
  | 1 => base.reflectX 4
  | 2 => base.reflectY 4
  | _ => (base.reflectX 4).reflectY 4

noncomputable def initialPoints (choices : Fin 4 → Bool) (index : Fin 14) : Point :=
  match index.val with
  | 0 => ⟨(1 : ℝ), (87 / 50 : ℝ)⟩
  | 1 => ⟨(3 : ℝ), (87 / 50 : ℝ)⟩
  | 2 => ⟨(1 : ℝ), (113 / 50 : ℝ)⟩
  | 3 => ⟨(3 : ℝ), (113 / 50 : ℝ)⟩
  | 4 => ⟨(2 : ℝ), (87 / 50 : ℝ)⟩
  | 5 => ⟨(2 : ℝ), (113 / 50 : ℝ)⟩
  | 6 => ⟨(8 / 5 : ℝ), (1 : ℝ)⟩
  | 7 => ⟨(12 / 5 : ℝ), (1 : ℝ)⟩
  | 8 => ⟨(8 / 5 : ℝ), (3 : ℝ)⟩
  | 9 => ⟨(12 / 5 : ℝ), (3 : ℝ)⟩
  | 10 => cornerAlternative choices 0
  | 11 => cornerAlternative choices 1
  | 12 => cornerAlternative choices 2
  | _ => cornerAlternative choices 3

noncomputable def finalPoints (choices : Fin 4 → Bool) (index : Fin 15) : Point :=
  match index.val with
  | 0 => ⟨(8 / 5 : ℝ), (1 : ℝ)⟩
  | 1 => ⟨(113 / 50 : ℝ), (1 : ℝ)⟩
  | 2 => ⟨(3 : ℝ), (8 / 5 : ℝ)⟩
  | 3 => ⟨(1 : ℝ), (87 / 50 : ℝ)⟩
  | 4 => ⟨(89 / 50 : ℝ), (87 / 50 : ℝ)⟩
  | 5 => ⟨(113 / 50 : ℝ), (2 : ℝ)⟩
  | 6 => ⟨(8 / 5 : ℝ), (3 : ℝ)⟩
  | 7 => ⟨(113 / 50 : ℝ), (3 : ℝ)⟩
  | 8 => ⟨(3 : ℝ), (12 / 5 : ℝ)⟩
  | 9 => ⟨(1 : ℝ), (113 / 50 : ℝ)⟩
  | 10 => ⟨(89 / 50 : ℝ), (113 / 50 : ℝ)⟩
  | 11 => cornerAlternative choices 0
  | 12 => cornerAlternative choices 1
  | 13 => cornerAlternative choices 2
  | _ => cornerAlternative choices 3

def Hole (point : Point) : Prop :=
  1 ≤ point.x ∧ point.x ≤ 3 ∧ 87 / 50 ≤ point.y ∧ point.y ≤ 113 / 50

end SquarePackingArchive.BentzThirteen.Nonadjacent
