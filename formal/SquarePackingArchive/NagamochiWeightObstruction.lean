import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace SquarePackingArchive.Nagamochi

theorem originalLayout_scalar_mass_lower_bound (lineWeight cornerWeight edgeWeight : ℝ)
    (edgeConstraint :
      1 ≤ 10001 / 100000000 + 10001 / 10000 * lineWeight + edgeWeight)
    (cornerConstraint :
      1 ≤ 1 / 100000000 + 1001 / 5000 * lineWeight + 2 * cornerWeight)
    (counterexampleConstraint :
      1 ≤ 611022059041 / 25584000000000 +
        (1251468079 / 1279200000 + 29 / 1000) * lineWeight + cornerWeight) :
    818060198173335527 / 58025847950000000 ≤
      4 + 44 / 5 * lineWeight + 8 * cornerWeight + 4 * edgeWeight := by
  linarith only [edgeConstraint, cornerConstraint, counterexampleConstraint]

theorem originalLayout_scalar_constraints_impossible (lineWeight cornerWeight edgeWeight : ℝ)
    (edgeConstraint :
      1 ≤ 10001 / 100000000 + 10001 / 10000 * lineWeight + edgeWeight)
    (cornerConstraint :
      1 ≤ 1 / 100000000 + 1001 / 5000 * lineWeight + 2 * cornerWeight)
    (counterexampleConstraint :
      1 ≤ 611022059041 / 25584000000000 +
        (1251468079 / 1279200000 + 29 / 1000) * lineWeight + cornerWeight)
    (massBudget : 4 + 44 / 5 * lineWeight + 8 * cornerWeight + 4 * edgeWeight ≤ 14) :
    False := by
  have lower := originalLayout_scalar_mass_lower_bound lineWeight cornerWeight edgeWeight
    edgeConstraint cornerConstraint counterexampleConstraint
  linarith only [lower, massBudget]

theorem uniformDiagonal_scalar_constraints_impossible (cornerWeight : ℝ)
    (leftConstraint : 1 ≤ 72462001 / 50000000 - 499 / 500 * cornerWeight)
    (rightConstraint : 1 ≤ 50209999 / 100000000 + 249 / 250 * cornerWeight) :
    False := by
  linarith only [leftConstraint, rightConstraint]

theorem originalLayout_variableArea_scalar_constraints_impossible
    (areaWeight lineWeight cornerWeight edgeWeight : ℝ)
    (insideConstraint : 1 ≤ 100020001 / 100000000 * areaWeight)
    (edgeConstraint :
      1 ≤ 10001 / 100000000 * areaWeight + 10001 / 10000 * lineWeight + edgeWeight)
    (cornerConstraint :
      1 ≤ 1 / 100000000 * areaWeight + 1001 / 5000 * lineWeight + 2 * cornerWeight)
    (counterexampleConstraint :
      1 ≤ 611022059041 / 25584000000000 * areaWeight +
        (1251468079 / 1279200000 + 29 / 1000) * lineWeight + cornerWeight)
    (massBudget :
      4 * areaWeight + 44 / 5 * lineWeight + 8 * cornerWeight + 4 * edgeWeight ≤ 14) :
    False := by
  linarith only [insideConstraint, edgeConstraint, cornerConstraint,
    counterexampleConstraint, massBudget]

end SquarePackingArchive.Nagamochi
