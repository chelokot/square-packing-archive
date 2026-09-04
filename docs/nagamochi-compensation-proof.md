# A compensation proof for packing n²−2 squares

For every integer `n ≥ 2`, the smallest square container for `n²−2` unit squares has side `n`. Squares may rotate, and their boundaries may touch.

The closed Lean theorem is [`Records.NearSquare.squareMinusTwo_isMinimumSide`](../formal/SquarePackingArchive/NagamochiPackingTheorem.lean). Its only hypothesis is `2 ≤ n`. Lean's axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no unfinished proofs or added axioms.

The compensation argument below covers `n ≥ 4`. For `n = 2`, the theorem uses the [two-square proof](../formal/SquarePackingArchive/Records/NearSquare.lean). For `n = 3`, the [seven-square proof](../formal/SquarePackingArchive/Records/Square7.lean) uses two unavoidable point configurations, following the approach in [Kearney and Shiu (2002), §2](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v9i1r14/pdf/). Neither small case uses the resource measure.

This is a replacement argument for the square-container case of [Hiroshi Nagamochi’s _Packing Unit Squares in a Rectangle_ (2005)](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v12i1r37/pdf). It retains the paper’s resource measure but replaces its false claim that every individual square scores more than one. The [counterexample to Lemma 1](nagamochi-score-counterexample.md) remains valid. This proof does not verify that lemma or establish the paper’s full rectangular-container theorem.

## 1. Scale a hypothetical smaller packing

Write `N = n²−2`. Suppose `N` unit squares fit in a container of side `L < n`. Choose

```text
1 < λ ≤ 1.01,    λL ≤ n.
```

Dilate the entire packing by `λ`. Its squares now have side `λ > 1`, still have disjoint interiors, and fit in `[0,n]²`. Every count below uses square interiors: a marked point on a square’s boundary contributes nothing.

The dilation and contradiction step are checked in [`Packing.squareMinusTwo_side_ge`](../formal/SquarePackingArchive/NagamochiPackingTheorem.lean#L54). The opposite inequality is immediate: remove two cells from the `n×n` grid packing.

## 2. A fixed resource budget

Define a measure `μ` inside `[0,n]²`:

| Resource                                                                                      | Contribution inside a square |
| --------------------------------------------------------------------------------------------- | ---------------------------- |
| The inner region `[1,n−1]²`                                                                   | Covered area                 |
| Its four sides, each extended by `0.1` at both ends                                           | Half the covered length      |
| The eight segment endpoints, called `Q`                                                       | `0.45` per contained point   |
| Points `(i,0.9)`, `(i,n−0.9)`, `(0.9,i)`, `(n−0.9,i)`, for integers `2 ≤ i ≤ n−2`, called `P` | `0.5` per contained point    |

The total mass is

```text
(n−2)² + (2n−3.6) + 3.6 + 2(n−3) = n²−2 = N.
```

Let `a(S) = μ(interior S)`. Disjointness gives `Σ a(S) ≤ N`. Some individual scores can be at most one; call those squares **bad**. The goal is to compensate their deficits using other squares in the same packing.

Lean: [`NagamochiResource.measure_univ`](../formal/SquarePackingArchive/NagamochiResource.lean#L650), [`Packing.squareMinusTwo_originalScore_sum_le_card`](../formal/SquarePackingArchive/NagamochiCompensation.lean).

## 3. Every marked point has an owner

Temporarily raise each `Q` weight from `0.45` to `0.5`. The augmented measure has total mass `N+0.4`, and every dilated square has augmented score strictly greater than one. This statement is proved separately; it does not assume the false original-score lemma.

An unused `P` or `Q` would remove `0.5` from the available budget, leaving at most `N−0.1` for `N` squares whose augmented scores sum to more than `N`. Therefore every mark lies inside a square. Disjoint interiors make its owner unique.

Also, each owner’s augmented score is below `1.4`, since the other `N−1` squares each score more than one. The geometric lower bound for a square containing consecutive marks on a boundary row is greater than `1.5`. Thus consecutive marks have different owners, including the endpoint `Q/P` pairs.

Lean: [`score_gt_one_of_fits`](../formal/SquarePackingArchive/NagamochiAugmented.lean#L102), [ownership and individual upper bounds](../formal/SquarePackingArchive/NagamochiPackingConstraints.lean), [`squareMinusTwo_not_adjacent_bottom_marks`](../formal/SquarePackingArchive/NagamochiWeightedChain.lean#L10).

## 4. A bad square starts a finite boundary chain

Every bad square contains exactly one `Q` and no `P`. Different bad squares contain different `Q` points. Rotate or reflect coordinates so that a chosen bad square `B` contains `Q=(1,0.9)` on the bottom row.

The initial geometric estimate produces a height `h₀ ∈ [0.9,1]` such that

```text
(2,h₀) lies inside B,    a(B) > (1+h₀)/2.
```

Follow the owner of `(2,0.9)`. More generally, suppose the preceding square contains `(i−1,0.9)` and `(i,h)`, while the next square owns `(i,0.9)`. The next square cannot contain `(i,h)`. Its geometry gives either:

- a crossing `(i+1,h′)` with `0.9 ≤ h′ ≤ h`; or
- a terminal configuration, with the relevant leftmost or rightmost vertex below `y=0.9`.

A backward crossing would make segments inside the two convex square interiors intersect, contradicting disjointness. Axis-aligned squares cannot exclude the incoming point at height at most one. These cases are included in the proof, not imposed as extra hypotheses.

The integer coordinate increases at every continuation. A crossing at `x=n` cannot lie in a square’s interior inside the container, so the chain terminates. Its final height `h` satisfies `h ≤ h₀`. Set

```text
credit = (1−h)/2 ≥ 0.
```

Then `a(B)+credit > 1`.

Lean: [bad-square classification](../formal/SquarePackingArchive/NagamochiGlobalBadSquare.lean#L184), [weighted start](../formal/SquarePackingArchive/NagamochiInitialDebt.lean#L232), [no reversal](../formal/SquarePackingArchive/NagamochiBoundaryChain.lean#L7), [actual continuation and finite termination](../formal/SquarePackingArchive/NagamochiFiniteChain.lean#L90).

## 5. Terminals pay the credit

The terminal area, line-length and point estimates give two bounds for its owner `T`:

```text
P terminal:    a(T) > 1 + 2·credit.
Q terminal:    a(T) > 1 + credit.
```

These estimates use the actual square geometry, including the missing neighboring marks. The angular inequalities are checked with exact real arithmetic; the proof uses no numerical search tolerance. A `Q` terminal is at the opposite endpoint of the source boundary row, contains exactly that one `Q`, and contains no `P` anywhere.

A `P` terminal can receive chains from at most two bad squares: its `P` points belong to one boundary row, and that row has only two source `Q` points. A `Q` terminal can receive at most one: its unique `Q` determines the opposite source endpoint. The absence of `P` points also prevents it from receiving a chain as a `P` terminal.

Lean: [terminal score estimates](../formal/SquarePackingArchive/NagamochiBoundaryTransfer.lean#L9), [scalar inequalities](../formal/SquarePackingArchive/NagamochiChainPotential.lean#L50), [physical assignment capacities](../formal/SquarePackingArchive/NagamochiAssignmentCapacity.lean#L52). The combined, all-orientation statement is [`bad_corner_owner_has_capacity_transfer`](../formal/SquarePackingArchive/NagamochiVerifiedTransfer.lean#L9).

## 6. Sum the compensated scores

For each terminal, choose the largest credit assigned to it. There are at most `capacity` incoming credits, so their sum is at most `capacity × largest credit`. The terminal’s score exceeds one plus that amount.

Add each credit to its bad source and subtract it from its terminal. Every adjusted score is strictly greater than one. Terminals are not bad, and other nonbad squares already score more than one. Transfers do not change the total, so

```text
N < sum of adjusted scores = sum of original scores ≤ N,
```

a contradiction. This proves the lower bound; the grid packing gives equality.

Lean: [`finite_scores_sum_gt_card_of_capacity_compensation`](../formal/SquarePackingArchive/Compensation.lean#L67), assembled in [`Packing.squareMinusTwo_impossible_of_scaled_fits`](../formal/SquarePackingArchive/NagamochiPackingTheorem.lean#L7).
