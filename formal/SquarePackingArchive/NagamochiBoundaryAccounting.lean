import SquarePackingArchive.NagamochiBoundaryOrientation
import SquarePackingArchive.NagamochiEdgeOwnership

namespace SquarePackingArchive.NagamochiResource

lemma cornerPointKinds_edge_card (edge : EdgePoint) :
    (cornerPointKinds.filter fun corner => corner.edge = edge).card = 2 := by
  cases edge <;> decide

theorem card_le_two_of_injective_corner_edge
    {Index : Type*} (origins : Finset Index) (corner : origins → CornerPoint)
    (injective : Function.Injective corner) (edge : EdgePoint)
    (same_edge : ∀ origin, (corner origin).edge = edge) :
    origins.card ≤ 2 := by
  classical
  let assigned : origins → (cornerPointKinds.filter fun selected => selected.edge = edge) :=
    fun origin => ⟨corner origin, Finset.mem_filter.mpr ⟨mem_cornerPointKinds _, same_edge origin⟩⟩
  have assigned_injective : Function.Injective assigned := by
    intro first second same
    exact injective (congrArg Subtype.val same)
  exact (Finset.card_le_card_of_injective assigned_injective).trans_eq (cornerPointKinds_edge_card edge)

theorem card_le_two_of_same_square_edge_assignments
    {Index : Type*} (origins : Finset Index) (corner : origins → CornerPoint)
    (injective : Function.Injective corner)
    (square : PlacedSquare) {size : ℕ} {factor : ℝ}
    (size_lower : 4 ≤ size) (factor_positive : 0 < factor) (factor_at_most : factor ≤ 101 / 100)
    (owns_assigned_points : ∀ origin, ∃ coordinate ∈ Finset.Icc 2 (size - 2),
      edgePoint size coordinate (corner origin).edge ∈ square.dilatedInteriorRegion factor) :
    origins.card ≤ 2 := by
  classical
  by_cases empty : origins = ∅
  · simp [empty]
  obtain ⟨first, first_mem⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  let firstOrigin : origins := ⟨first, first_mem⟩
  obtain ⟨firstCoordinate, first_coordinate_mem, first_point_mem⟩ := owns_assigned_points firstOrigin
  apply card_le_two_of_injective_corner_edge origins corner injective (corner firstOrigin).edge
  intro origin
  obtain ⟨coordinate, coordinate_mem, point_mem⟩ := owns_assigned_points origin
  exact Nagamochi.edge_point_sides_equal_of_same_square square (corner origin).edge
    (corner firstOrigin).edge size_lower factor_positive factor_at_most
    coordinate_mem first_coordinate_mem point_mem first_point_mem

theorem card_le_one_of_unique_terminal_corner
    {Index : Type*} (origins : Finset Index) (corner : origins → CornerPoint)
    (injective : Function.Injective corner) (terminalCorner : CornerPoint → CornerPoint)
    (terminal_injective : Function.Injective terminalCorner)
    {size : ℕ} {region : Set Plane}
    (unique_corner : ∃! kind, cornerPoint size kind ∈ region)
    (owns_assigned_points : ∀ origin, cornerPoint size (terminalCorner (corner origin)) ∈ region) :
    origins.card ≤ 1 := by
  classical
  obtain ⟨kind, _contained, unique⟩ := unique_corner
  apply Finset.card_le_one.mpr
  intro first first_mem second second_mem
  let firstOrigin : origins := ⟨first, first_mem⟩
  let secondOrigin : origins := ⟨second, second_mem⟩
  have same_terminal := (unique _ (owns_assigned_points firstOrigin)).trans
    (unique _ (owns_assigned_points secondOrigin)).symm
  have same_origin := injective (terminal_injective same_terminal)
  exact congrArg Subtype.val same_origin

end SquarePackingArchive.NagamochiResource
