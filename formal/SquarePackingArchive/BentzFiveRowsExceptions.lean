import SquarePackingArchive.BentzFiveRowsPoints
import SquarePackingArchive.BentzExceptionCluster

namespace SquarePackingArchive.BentzFiveRows

def BlueRowUnique {side : ℝ} (packing : Packing 22 side) (row : Fin 3) : Prop :=
  ∀ column : Fin 5,
    packing.PointUnique (fun index => (blueBasePoints index).scale (side / 5))
      (bluePointIndex (.inr (row, column)))

theorem blue_odd_row_eq_of_point_index_eq
    {firstRow secondRow : Fin 3} {firstColumn secondColumn : Fin 5}
    (equality : bluePointIndex (.inr (firstRow, firstColumn)) =
      bluePointIndex (.inr (secondRow, secondColumn))) : firstRow = secondRow := by
  have height_eq := congrArg (fun index => (blueBasePoints index).y) equality
  simp only [blueBasePoints, bluePoints_at_index, ShiftedStaggeredLattice.point, blueLattice] at height_eq
  have val_eq : (firstRow : ℝ) = (secondRow : ℝ) := by linarith
  exact Fin.ext (by exact_mod_cast val_eq)

theorem blue_odd_row_eq_of_same_square
    {side : ℝ} (side_lower : 4999 / 1000 ≤ side)
    (square : PlacedSquare) (firstRow secondRow : Fin 3) (firstColumn secondColumn : Fin 5)
    (first_inside : square.InteriorContains
      ((blueBasePoints (bluePointIndex (.inr (firstRow, firstColumn)))).scale (side / 5)))
    (second_inside : square.InteriorContains
      ((blueBasePoints (bluePointIndex (.inr (secondRow, secondColumn)))).scale (side / 5))) :
    firstRow = secondRow := by
  have distance := (square.contained_points_coordinate_distance_lt_ten_sevenths
    first_inside.contains second_inside.contains).2
  simp only [blueBasePoints, bluePoints_at_index, ShiftedStaggeredLattice.point,
    blueLattice, Point.scale] at distance
  rw [abs_lt] at distance
  fin_cases firstRow <;> fin_cases secondRow <;> norm_num at * <;> linarith

theorem at_most_one_exceptional_blue_row
    {side : ℝ} (packing : Packing 22 side)
    (side_lower : 4999 / 1000 ≤ side) (side_lt_five : side < 5) :
    ∃ exception : Fin 3, ∀ row, row ≠ exception → BlueRowUnique packing row := by
  classical
  let points : Fin 23 → Point := fun index => (blueBasePoints index).scale (side / 5)
  have unavoidable : InteriorUnavoidable points side :=
    blue_interior_unavoidable (fun _ => 1 / 2) (by intro row; constructor <;> norm_num)
      (by linarith) side_lt_five
  have bad_rows_equal (first second : Fin 3)
      (first_bad : ¬ BlueRowUnique packing first) (second_bad : ¬ BlueRowUnique packing second) :
      first = second := by
    change ¬ ∀ column, packing.PointUnique points (bluePointIndex (.inr (first, column))) at first_bad
    change ¬ ∀ column, packing.PointUnique points (bluePointIndex (.inr (second, column))) at second_bad
    push Not at first_bad second_bad
    obtain ⟨firstColumn, first_not_unique⟩ := first_bad
    obtain ⟨secondColumn, second_not_unique⟩ := second_bad
    rcases packing.interiorUnavoidable_exception_cluster points unavoidable with
      ⟨extra, failures_extra⟩ | ⟨owner, failures_inside⟩
    · apply blue_odd_row_eq_of_point_index_eq
      exact (failures_extra _ first_not_unique).trans (failures_extra _ second_not_unique).symm
    · exact blue_odd_row_eq_of_same_square side_lower (packing.squares owner)
        first second firstColumn secondColumn
        (failures_inside _ first_not_unique) (failures_inside _ second_not_unique)
  by_cases exists_exception : ∃ row, ¬ BlueRowUnique packing row
  · obtain ⟨exception, exception_bad⟩ := exists_exception
    refine ⟨exception, ?_⟩
    intro row different
    by_contra bad
    exact different (bad_rows_equal row exception bad exception_bad)
  · exact ⟨0, fun row _ => by_contra fun bad => exists_exception ⟨row, bad⟩⟩

end SquarePackingArchive.BentzFiveRows
