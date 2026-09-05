import SquarePackingArchive.BentzAdjacentR2LeftGeometry

namespace SquarePackingArchive.BentzThirteen

set_option maxHeartbeats 4000000 in
theorem adjacentR2Left_unavoidable : ∀ square : PlacedSquare, square.Fits 4 → adjacentR2LeftOutcome square := by
  intro square fits
  have center_inside : square.Contains square.center := by
    refine ⟨0, 0, by norm_num, by norm_num, ?_⟩
    simp [PlacedSquare.point, Frame.place]
  have container_bounds := fits center_inside
  have container_0 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (0 : ℝ)) := by
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  have container_1 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) := by
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  have container_2 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) := by
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  have container_3 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (4 : ℝ)) := by
    linarith [container_bounds.1, container_bounds.2.1, container_bounds.2.2.1, container_bounds.2.2.2]
  by_cases branch_0 : 0 ≤ ((13 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (481 / 500 : ℝ))
  ·
    by_cases branch_1 : 0 ≤ ((-19 / 20 : ℝ) * square.center.x + (-7 / 50 : ℝ) * square.center.y + (1793 / 1000 : ℝ))
    ·
      by_cases branch_2 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ))
      ·
        by_cases branch_3 : 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ))
        ·
          by_cases branch_4 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ))
          ·
            by_cases branch_5 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ))
            ·
              apply adjacentR2Left_hit_boundary square fits 26
              change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                exact branch_5
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_3
                have weighted_1 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) + (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_5_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) := by linarith only [branch_5]
              apply adjacentR2Left_hit_boundary square fits 34
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_5_negative.le
              ·
                exact branch_4
              ·
                exact branch_3
          ·
            have branch_4_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_4]
            by_cases branch_6 : 0 ≤ ((19 / 20 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-113 / 100 : ℝ))
            ·
              by_cases branch_7 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (37 / 25 : ℝ))
              ·
                by_cases branch_8 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 20 : ℝ))
                ·
                  apply adjacentR2Left_hit_boundary square fits 24
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (37 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ))
                  refine ⟨?_ , ?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_4_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) = (-7 / 20 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (7 / 20 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_7
                  ·
                    exact branch_8
                  ·
                    exact branch_2
                ·
                  have branch_8_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) := by linarith only [branch_8]
                  apply adjacentR2Left_hit_boundary square fits 32
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_4_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (-13 / 100 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_7
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (37 / 25 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) = (-39 / 100 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (39 / 100 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (77 / 500 : ℝ)) branch_1
                    have weighted_1 := mul_pos (by norm_num : 0 < (40247 / 50000 : ℝ)) branch_8_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (19 / 20 : ℝ)) negative
                    have identity : (77 / 500 : ℝ) * ((-19 / 20 : ℝ) * square.center.x + (-7 / 50 : ℝ) * square.center.y + (1793 / 1000 : ℝ)) + (40247 / 50000 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) + (19 / 20 : ℝ) * ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) = (-25597 / 250000 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (25597 / 250000 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                have branch_7_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-37 / 25 : ℝ)) := by linarith only [branch_7]
                by_cases branch_9 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ))
                ·
                  apply adjacentR2Left_hit_boundary square fits 33
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_9
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (7 / 50 : ℝ)) container_2
                    have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_1
                    have weighted_2 := mul_pos (by norm_num : 0 < (19 / 20 : ℝ)) negative
                    have identity : (7 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + (1 : ℝ) * ((-19 / 20 : ℝ) * square.center.x + (-7 / 50 : ℝ) * square.center.y + (1793 / 1000 : ℝ)) + (19 / 20 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) = (-291 / 500 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (291 / 500 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_3
                    have weighted_1 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) negative
                    have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) + (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                ·
                  have branch_9_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [branch_9]
                  by_cases branch_10 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 20 : ℝ))
                  ·
                    apply adjacentR2Left_hit_boundary square fits 25
                    change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-139 / 100 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (209 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ))
                    refine ⟨?_ , ?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (139 / 100 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_7_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                      have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-37 / 25 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (139 / 100 : ℝ)) = (-9 / 100 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (9 / 100 : ℝ))
                      nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                    ·
                      by_contra! failed
                      have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-209 / 100 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_9_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                      have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-209 / 100 : ℝ)) = (-7 / 20 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (7 / 20 : ℝ))
                      nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                    ·
                      exact branch_10
                    ·
                      exact branch_2
                  ·
                    have branch_10_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) := by linarith only [branch_10]
                    apply adjacentR2Left_hit_boundary square fits 32
                    change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_4_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                      have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (-13 / 100 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                      nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                    ·
                      by_contra! failed
                      have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_9_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                      have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) = (-13 / 100 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                      nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                    ·
                      by_contra! failed
                      have negative : 0 < ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (77 / 500 : ℝ)) branch_1
                      have weighted_1 := mul_pos (by norm_num : 0 < (40247 / 50000 : ℝ)) branch_10_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (19 / 20 : ℝ)) negative
                      have identity : (77 / 500 : ℝ) * ((-19 / 20 : ℝ) * square.center.x + (-7 / 50 : ℝ) * square.center.y + (1793 / 1000 : ℝ)) + (40247 / 50000 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) + (19 / 20 : ℝ) * ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) = (-25597 / 250000 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (25597 / 250000 : ℝ))
                      nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
            ·
              have branch_6_negative : 0 < ((-19 / 20 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (113 / 100 : ℝ)) := by linarith only [branch_6]
              by_cases branch_11 : 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-632 / 625 : ℝ))
              ·
                apply adjacentR2Left_hit_boundary square fits 1
                change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_11
                ·
                  by_contra! failed
                  have negative : 0 < ((6 / 25 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1369 / 2500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (162 / 3125 : ℝ)) branch_1
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (899 / 10000 : ℝ)) branch_3
                  have weighted_2 := mul_pos (by norm_num : 0 < (513 / 2500 : ℝ)) negative
                  have identity : (162 / 3125 : ℝ) * ((-19 / 20 : ℝ) * square.center.x + (-7 / 50 : ℝ) * square.center.y + (1793 / 1000 : ℝ)) + (899 / 10000 : ℝ) * ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) + (513 / 2500 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1369 / 2500 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (61 / 100 : ℝ)) branch_3
                  have weighted_1 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) negative
                  have identity : (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ)) + (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_11_negative : 0 < ((-6 / 25 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (632 / 625 : ℝ)) := by linarith only [branch_11]
                by_cases branch_12 : 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ))
                ·
                  apply adjacentR2Left_hit_boundary square fits 32
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_4_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (-13 / 100 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 5 : ℝ)) branch_0
                    have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_6_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (68 / 125 : ℝ)) negative
                    have identity : (1 / 5 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (481 / 500 : ℝ)) + (3 / 5 : ℝ) * ((-19 / 20 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (68 / 125 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) = (-459 / 3125 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (459 / 3125 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    exact branch_12
                ·
                  have branch_12_negative : 0 < ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) := by linarith only [branch_12]
                  apply adjacentR2Left_hit_boundary square fits 24
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (37 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ))
                  refine ⟨?_ , ?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_4_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) = (-7 / 20 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (7 / 20 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-37 / 25 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 5 : ℝ)) branch_2
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_6_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (19 / 20 : ℝ)) negative
                    have identity : (1 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ)) + (1 : ℝ) * ((-19 / 20 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (19 / 20 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-37 / 25 : ℝ)) = (-3 / 500 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (3 / 500 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (77 / 500 : ℝ)) branch_1
                    have weighted_1 := mul_pos (by norm_num : 0 < (19 / 20 : ℝ)) branch_12_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (40247 / 50000 : ℝ)) negative
                    have identity : (77 / 500 : ℝ) * ((-19 / 20 : ℝ) * square.center.x + (-7 / 50 : ℝ) * square.center.y + (1793 / 1000 : ℝ)) + (19 / 20 : ℝ) * ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) + (40247 / 50000 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) = (-25597 / 250000 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (25597 / 250000 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    exact branch_2
        ·
          have branch_3_negative : 0 < ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [branch_3]
          by_cases branch_13 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ))
          ·
            by_cases branch_14 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ))
            ·
              by_cases branch_15 : 0 ≤ ((43 / 500 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-41151 / 250000 : ℝ))
              ·
                apply adjacentR2Left_hit_boundary square fits 24
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (37 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ))
                refine ⟨?_ , ?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (43 / 500 : ℝ)) branch_14
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_15
                  have weighted_2 := mul_pos (by norm_num : 0 < (43 / 500 : ℝ)) negative
                  have identity : (43 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (1 : ℝ) * ((43 / 500 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-41151 / 250000 : ℝ)) + (43 / 500 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) = (-43 / 125000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (43 / 125000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-37 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_13
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-37 / 25 : ℝ)) = (-7 / 20 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (7 / 20 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_3_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) + (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) = (-189 / 2500 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (189 / 2500 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_2
              ·
                have branch_15_negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (41151 / 250000 : ℝ)) := by linarith only [branch_15]
                apply adjacentR2Left_hit_boundary square fits 36
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 125 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_3_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) + (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) = (-1161 / 62500 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (1161 / 62500 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_14
                ·
                  by_contra! failed
                  have negative : 0 < ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1161 / 62500 : ℝ)) branch_3_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (729 / 15625 : ℝ)) branch_15_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (1161 / 62500 : ℝ)) negative
                  have identity : (1161 / 62500 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) + (729 / 15625 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (41151 / 250000 : ℝ)) + (1161 / 62500 : ℝ) * ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (-1347921 / 3906250000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (1347921 / 3906250000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
            ·
              have branch_14_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_14]
              by_cases branch_16 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ))
              ·
                apply adjacentR2Left_hit_boundary square fits 24
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (37 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ))
                refine ⟨?_ , ?_ , ?_ , ?_ ⟩
                ·
                  exact branch_16
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-37 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_13
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-37 / 25 : ℝ)) = (-7 / 20 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (7 / 20 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_3_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) + (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) = (-189 / 2500 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (189 / 2500 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_2
              ·
                have branch_16_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) := by linarith only [branch_16]
                apply adjacentR2Left_hit_boundary square fits 37
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_14_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_2
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ)) + (1 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) = (-47 / 100 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (47 / 100 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (69 / 100 : ℝ)) branch_16_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (69 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) + (1 : ℝ) * ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) = (-759 / 5000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (759 / 5000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
          ·
            have branch_13_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_13]
            by_cases branch_17 : 0 ≤ ((19 / 20 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-113 / 100 : ℝ))
            ·
              apply adjacentR2Left_hit_boundary square fits 2
              change 0 ≤ ((0 : ℝ) * square.center.x + (17 / 50 : ℝ) * square.center.y + (-17 / 50 : ℝ)) ∧ 0 ≤ ((-19 / 20 : ℝ) * square.center.x + (-7 / 50 : ℝ) * square.center.y + (1793 / 1000 : ℝ)) ∧ 0 ≤ ((19 / 20 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-113 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-17 / 50 : ℝ) * square.center.y + (17 / 50 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (17 / 50 : ℝ)) branch_3_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) negative
                have identity : (17 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) + (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-17 / 50 : ℝ) * square.center.y + (17 / 50 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_1
              ·
                exact branch_17
            ·
              have branch_17_negative : 0 < ((-19 / 20 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (113 / 100 : ℝ)) := by linarith only [branch_17]
              apply adjacentR2Left_hit_boundary square fits 24
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (37 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ))
              refine ⟨?_ , ?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_13_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) = (-7 / 20 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (7 / 20 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-37 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 5 : ℝ)) branch_2
                have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_17_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (19 / 20 : ℝ)) negative
                have identity : (1 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (27 / 20 : ℝ)) + (1 : ℝ) * ((-19 / 20 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (19 / 20 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-37 / 25 : ℝ)) = (-3 / 500 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (3 / 500 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_3_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) + (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 20 : ℝ)) = (-189 / 2500 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (189 / 2500 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                exact branch_2
      ·
        have branch_2_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-27 / 20 : ℝ)) := by linarith only [branch_2]
        by_cases branch_18 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (387 / 250 : ℝ))
        ·
          by_cases branch_19 : 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ))
          ·
            apply adjacentR2Left_hit_boundary square fits 37
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_2_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-27 / 20 : ℝ)) + (1 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) = (-11 / 50 : ℝ) := by
                ring
              have constant_negative := (by norm_num : 0 < (11 / 50 : ℝ))
              nlinarith only [weighted_0, weighted_1, constant_negative, identity]
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (41 / 50 : ℝ)) branch_0
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_18
              have weighted_2 := mul_pos (by norm_num : 0 < (68 / 125 : ℝ)) negative
              have identity : (41 / 50 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (481 / 500 : ℝ)) + (13 / 100 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (387 / 250 : ℝ)) + (68 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              by_contra! failed
              have negative : 0 < ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (69 / 100 : ℝ)) branch_19
              have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
              have identity : (69 / 100 : ℝ) * ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ)) + (9 / 10 : ℝ) * ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_19_negative : 0 < ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) := by linarith only [branch_19]
            apply adjacentR2Left_hit_boundary square fits 3
            change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (387 / 250 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (243 / 500 : ℝ) * square.center.y + (-243 / 500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_18
            ·
              by_contra! failed
              have negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (16587 / 25000 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (387 / 5000 : ℝ)) branch_0
              have weighted_1 := mul_pos (by norm_num : 0 < (24041 / 50000 : ℝ)) branch_19_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (27 / 50 : ℝ)) negative
              have identity : (387 / 5000 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (481 / 500 : ℝ)) + (24041 / 50000 : ℝ) * ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) + (27 / 50 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (16587 / 25000 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-243 / 500 : ℝ) * square.center.y + (243 / 500 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (243 / 500 : ℝ)) branch_2_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
              have identity : (243 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-27 / 20 : ℝ)) + (1 : ℝ) * ((0 : ℝ) * square.center.x + (-243 / 500 : ℝ) * square.center.y + (243 / 500 : ℝ)) = (-1701 / 10000 : ℝ) := by
                ring
              have constant_negative := (by norm_num : 0 < (1701 / 10000 : ℝ))
              nlinarith only [weighted_0, weighted_1, constant_negative, identity]
        ·
          have branch_18_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-387 / 250 : ℝ)) := by linarith only [branch_18]
          by_cases branch_20 : 0 ≤ ((-41 / 100 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-1099 / 1000 : ℝ))
          ·
            apply adjacentR2Left_hit_boundary square fits 4
            change 0 ≤ ((-19 / 20 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (481 / 500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-387 / 250 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((19 / 20 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (773 / 1000 : ℝ)) branch_0
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (68 / 125 : ℝ)) branch_20
              have weighted_2 := mul_pos (by norm_num : 0 < (129 / 1000 : ℝ)) negative
              have identity : (773 / 1000 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (481 / 500 : ℝ)) + (68 / 125 : ℝ) * ((-41 / 100 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-1099 / 1000 : ℝ)) + (129 / 1000 : ℝ) * ((19 / 20 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-113 / 100 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_0
            ·
              exact branch_18_negative.le
          ·
            have branch_20_negative : 0 < ((41 / 100 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (1099 / 1000 : ℝ)) := by linarith only [branch_20]
            by_cases branch_21 : 0 ≤ ((19 / 20 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-113 / 100 : ℝ))
            ·
              apply adjacentR2Left_hit_boundary square fits 2
              change 0 ≤ ((0 : ℝ) * square.center.x + (17 / 50 : ℝ) * square.center.y + (-17 / 50 : ℝ)) ∧ 0 ≤ ((-19 / 20 : ℝ) * square.center.x + (-7 / 50 : ℝ) * square.center.y + (1793 / 1000 : ℝ)) ∧ 0 ≤ ((19 / 20 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-113 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-17 / 50 : ℝ) * square.center.y + (17 / 50 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (17 / 50 : ℝ)) branch_2_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (17 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-27 / 20 : ℝ)) + (1 : ℝ) * ((0 : ℝ) * square.center.x + (-17 / 50 : ℝ) * square.center.y + (17 / 50 : ℝ)) = (-119 / 1000 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (119 / 1000 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                exact branch_1
              ·
                exact branch_21
            ·
              have branch_21_negative : 0 < ((-19 / 20 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (113 / 100 : ℝ)) := by linarith only [branch_21]
              apply adjacentR2Left_hit_boundary square fits 4
              change 0 ≤ ((-19 / 20 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (481 / 500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-387 / 250 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_21_negative.le
              ·
                exact branch_0
              ·
                exact branch_18_negative.le
    ·
      have branch_1_negative : 0 < ((19 / 20 : ℝ) * square.center.x + (7 / 50 : ℝ) * square.center.y + (-1793 / 1000 : ℝ)) := by linarith only [branch_1]
      by_cases branch_22 : 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ))
      ·
        by_cases branch_23 : 0 ≤ ((3 / 5 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (-71 / 250 : ℝ))
        ·
          by_cases branch_24 : 0 ≤ ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ))
          ·
            apply adjacentR2Left_hit_boundary square fits 33
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (19 / 25 : ℝ)) branch_1_negative
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (7 / 50 : ℝ)) branch_23
              have weighted_2 := mul_pos (by norm_num : 0 < (403 / 500 : ℝ)) negative
              have identity : (19 / 25 : ℝ) * ((19 / 20 : ℝ) * square.center.x + (7 / 50 : ℝ) * square.center.y + (-1793 / 1000 : ℝ)) + (7 / 50 : ℝ) * ((3 / 5 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (-71 / 250 : ℝ)) + (403 / 500 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              by_contra! failed
              have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_22
              have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) negative
              have identity : (1 : ℝ) * ((-3 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) + (3 / 5 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_24
              have weighted_1 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
              have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) + (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_24_negative : 0 < ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) := by linarith only [branch_24]
            apply adjacentR2Left_hit_boundary square fits 5
            change 0 ≤ ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (-71 / 250 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (19 / 25 : ℝ)) branch_24_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
              have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) + (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_22
            ·
              exact branch_23
        ·
          have branch_23_negative : 0 < ((-3 / 5 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (71 / 250 : ℝ)) := by linarith only [branch_23]
          by_cases branch_25 : 0 ≤ ((-7 / 20 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (463 / 200 : ℝ))
          ·
            apply adjacentR2Left_hit_boundary square fits 6
            change 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (71 / 250 : ℝ)) ∧ 0 ≤ ((-7 / 20 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (463 / 200 : ℝ)) ∧ 0 ≤ ((19 / 20 : ℝ) * square.center.x + (7 / 50 : ℝ) * square.center.y + (-1793 / 1000 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_23_negative.le
            ·
              exact branch_25
            ·
              exact branch_1_negative.le
          ·
            have branch_25_negative : 0 < ((7 / 20 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-463 / 200 : ℝ)) := by linarith only [branch_25]
            apply adjacentR2Left_hit_boundary square fits 16
            change 0 ≤ ((41 / 100 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (1099 / 1000 : ℝ)) ∧ 0 ≤ ((7 / 20 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-463 / 200 : ℝ)) ∧ 0 ≤ ((-19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 10 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-41 / 100 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-1099 / 1000 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2281 / 2500 : ℝ)) branch_0
              have weighted_1 := mul_pos (by norm_num : 0 < (129 / 1000 : ℝ)) branch_1_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (2941 / 5000 : ℝ)) negative
              have identity : (2281 / 2500 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (481 / 500 : ℝ)) + (129 / 1000 : ℝ) * ((19 / 20 : ℝ) * square.center.x + (7 / 50 : ℝ) * square.center.y + (-1793 / 1000 : ℝ)) + (2941 / 5000 : ℝ) * ((-41 / 100 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-1099 / 1000 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_25_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 10 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_22
              have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) negative
              have identity : (19 / 25 : ℝ) * ((-3 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) + (3 / 5 : ℝ) * ((19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 10 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_22_negative : 0 < ((3 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) := by linarith only [branch_22]
        by_cases branch_26 : 0 ≤ ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ))
        ·
          by_cases branch_27 : 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (123 / 50 : ℝ))
          ·
            apply adjacentR2Left_hit_boundary square fits 21
            change 0 ≤ ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-3 / 5 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (123 / 50 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (3 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 5 : ℝ)) branch_26
              have weighted_1 := mul_pos (by norm_num : 0 < (19 / 25 : ℝ)) negative
              have identity : (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) + (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (3 / 5 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_27
            ·
              exact branch_22_negative.le
          ·
            have branch_27_negative : 0 < ((3 / 5 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-123 / 50 : ℝ)) := by linarith only [branch_27]
            by_cases branch_28 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ))
            ·
              by_cases branch_29 : 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (1 / 25 : ℝ))
              ·
                by_cases branch_30 : 0 ≤ ((-9 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (579 / 250 : ℝ))
                ·
                  apply adjacentR2Left_hit_boundary square fits 17
                  change 0 ≤ ((19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 10 : ℝ)) ∧ 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (1 / 25 : ℝ)) ∧ 0 ≤ ((-9 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (579 / 250 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 10 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (19 / 25 : ℝ)) branch_22_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) negative
                    have identity : (19 / 25 : ℝ) * ((3 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) + (3 / 5 : ℝ) * ((-19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 10 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    exact branch_29
                  ·
                    exact branch_30
                ·
                  have branch_30_negative : 0 < ((9 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-579 / 250 : ℝ)) := by linarith only [branch_30]
                  apply adjacentR2Left_hit_boundary square fits 18
                  change 0 ≤ ((9 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-579 / 250 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-23 / 125 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_30_negative.le
                  ·
                    exact branch_28
                  ·
                    by_contra! failed
                    have negative : 0 < ((-16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (23 / 125 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (9 / 25 : ℝ)) branch_0
                    have weighted_1 := mul_pos (by norm_num : 0 < (153 / 500 : ℝ)) branch_22_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (9 / 25 : ℝ)) negative
                    have identity : (9 / 25 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (481 / 500 : ℝ)) + (153 / 500 : ℝ) * ((3 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) + (9 / 25 : ℝ) * ((-16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (23 / 125 : ℝ)) = (-1161 / 25000 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (1161 / 25000 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                have branch_29_negative : 0 < ((2 / 5 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-1 / 25 : ℝ)) := by linarith only [branch_29]
                apply adjacentR2Left_hit_boundary square fits 22
                change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-1 / 25 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-123 / 50 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_28
                ·
                  exact branch_29_negative.le
                ·
                  exact branch_27_negative.le
            ·
              have branch_28_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [branch_28]
              by_cases branch_31 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ))
              ·
                apply adjacentR2Left_hit_boundary square fits 44
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_26
                  have weighted_1 := mul_pos (by norm_num : 0 < (19 / 25 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) + (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  exact branch_31
                ·
                  exact branch_28_negative.le
              ·
                have branch_31_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) := by linarith only [branch_31]
                apply adjacentR2Left_hit_boundary square fits 45
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_31_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) container_1
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_0
                  have weighted_2 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) negative
                  have identity : (13 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (481 / 500 : ℝ)) + (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (-159 / 500 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (159 / 500 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_28_negative.le
        ·
          have branch_26_negative : 0 < ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ)) := by linarith only [branch_26]
          by_cases branch_32 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ))
          ·
            apply adjacentR2Left_hit_boundary square fits 35
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (3 / 5 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_22_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) negative
              have identity : (1 : ℝ) * ((3 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) + (3 / 5 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_32
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-3 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_26_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (19 / 25 : ℝ)) negative
              have identity : (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ)) + (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-3 / 5 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_32_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [branch_32]
            apply adjacentR2Left_hit_boundary square fits 27
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
            refine ⟨?_ , ?_ ⟩
            ·
              exact branch_32_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_26_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (19 / 25 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ)) + (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
  ·
    have branch_0_negative : 0 < ((-13 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-481 / 500 : ℝ)) := by linarith only [branch_0]
    by_cases branch_33 : 0 ≤ ((7 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-138 / 125 : ℝ))
    ·
      by_cases branch_34 : 0 ≤ ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 40 : ℝ))
      ·
        by_cases branch_35 : 0 ≤ ((16 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-813 / 250 : ℝ))
        ·
          by_cases branch_36 : 0 ≤ ((9 / 100 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (969 / 500 : ℝ))
          ·
            apply adjacentR2Left_hit_boundary square fits 12
            change 0 ≤ ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 40 : ℝ)) ∧ 0 ≤ ((9 / 100 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (969 / 500 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-813 / 250 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_34
            ·
              exact branch_36
            ·
              exact branch_35
          ·
            have branch_36_negative : 0 < ((-9 / 100 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-969 / 500 : ℝ)) := by linarith only [branch_36]
            by_cases branch_37 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 5 : ℝ))
            ·
              apply adjacentR2Left_hit_boundary square fits 42
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 5 : ℝ)) container_3
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_33
                have weighted_2 := mul_pos (by norm_num : 0 < (7 / 25 : ℝ)) negative
                have identity : (1 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (4 : ℝ)) + (1 : ℝ) * ((7 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-138 / 125 : ℝ)) + (7 / 25 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (-3 / 125 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (3 / 125 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                exact branch_37
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (9 / 125 : ℝ)) branch_33
                have weighted_1 := mul_pos (by norm_num : 0 < (28 / 125 : ℝ)) branch_36_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (107 / 500 : ℝ)) negative
                have identity : (9 / 125 : ℝ) * ((7 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-138 / 125 : ℝ)) + (28 / 125 : ℝ) * ((-9 / 100 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-969 / 500 : ℝ)) + (107 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_37_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 5 : ℝ)) := by linarith only [branch_37]
              apply adjacentR2Left_hit_boundary square fits 43
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-969 / 500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_37_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_34
                have weighted_1 := mul_pos (by norm_num : 0 < (73 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 40 : ℝ)) + (73 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_36_negative.le
        ·
          have branch_35_negative : 0 < ((-16 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (813 / 250 : ℝ)) := by linarith only [branch_35]
          by_cases branch_38 : 0 ≤ ((9 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-52 / 25 : ℝ))
          ·
            apply adjacentR2Left_hit_boundary square fits 15
            change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (813 / 250 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-138 / 125 : ℝ)) ∧ 0 ≤ ((9 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-52 / 25 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_35_negative.le
            ·
              exact branch_33
            ·
              exact branch_38
          ·
            have branch_38_negative : 0 < ((-9 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (52 / 25 : ℝ)) := by linarith only [branch_38]
            by_cases branch_39 : 0 ≤ ((-41 / 100 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-1099 / 1000 : ℝ))
            ·
              apply adjacentR2Left_hit_boundary square fits 14
              change 0 ≤ ((-9 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (52 / 25 : ℝ)) ∧ 0 ≤ ((77 / 100 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-113 / 250 : ℝ)) ∧ 0 ≤ ((-41 / 100 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-1099 / 1000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_38_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((-77 / 100 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (113 / 250 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (529 / 1000 : ℝ)) branch_33
                have weighted_1 := mul_pos (by norm_num : 0 < (133 / 500 : ℝ)) branch_38_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (17 / 250 : ℝ)) negative
                have identity : (529 / 1000 : ℝ) * ((7 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-138 / 125 : ℝ)) + (133 / 500 : ℝ) * ((-9 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (52 / 25 : ℝ)) + (17 / 250 : ℝ) * ((-77 / 100 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (113 / 250 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_39
            ·
              have branch_39_negative : 0 < ((41 / 100 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (1099 / 1000 : ℝ)) := by linarith only [branch_39]
              apply adjacentR2Left_hit_boundary square fits 16
              change 0 ≤ ((41 / 100 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (1099 / 1000 : ℝ)) ∧ 0 ≤ ((7 / 20 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-463 / 200 : ℝ)) ∧ 0 ≤ ((-19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 10 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_39_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((-7 / 20 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (463 / 200 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (91 / 500 : ℝ)) branch_0_negative
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (327 / 1000 : ℝ)) branch_33
                have weighted_2 := mul_pos (by norm_num : 0 < (97 / 500 : ℝ)) negative
                have identity : (91 / 500 : ℝ) * ((-13 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-481 / 500 : ℝ)) + (327 / 1000 : ℝ) * ((7 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-138 / 125 : ℝ)) + (97 / 500 : ℝ) * ((-7 / 20 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (463 / 200 : ℝ)) = (-43491 / 500000 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (43491 / 500000 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 10 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_34
                have weighted_1 := mul_pos (by norm_num : 0 < (73 / 100 : ℝ)) negative
                have identity : (19 / 25 : ℝ) * ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 40 : ℝ)) + (73 / 100 : ℝ) * ((19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 10 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_34_negative : 0 < ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-73 / 40 : ℝ)) := by linarith only [branch_34]
        by_cases branch_40 : 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (23 / 125 : ℝ))
        ·
          by_cases branch_41 : 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (2079 / 1000 : ℝ))
          ·
            apply adjacentR2Left_hit_boundary square fits 13
            change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (23 / 125 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (2079 / 1000 : ℝ)) ∧ 0 ≤ ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-73 / 40 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_40
            ·
              exact branch_41
            ·
              exact branch_34_negative.le
          ·
            have branch_41_negative : 0 < ((9 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-2079 / 1000 : ℝ)) := by linarith only [branch_41]
            by_cases branch_42 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ))
            ·
              apply adjacentR2Left_hit_boundary square fits 41
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((9 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-2079 / 1000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_34_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (73 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-73 / 40 : ℝ)) + (73 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_42
              ·
                exact branch_41_negative.le
            ·
              have branch_42_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [branch_42]
              apply adjacentR2Left_hit_boundary square fits 31
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                exact branch_42_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (9 / 100 : ℝ)) branch_40
                have weighted_1 := mul_pos (by norm_num : 0 < (16 / 25 : ℝ)) branch_41_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (219 / 500 : ℝ)) negative
                have identity : (9 / 100 : ℝ) * ((-16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (23 / 125 : ℝ)) + (16 / 25 : ℝ) * ((9 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-2079 / 1000 : ℝ)) + (219 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
        ·
          have branch_40_negative : 0 < ((16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-23 / 125 : ℝ)) := by linarith only [branch_40]
          by_cases branch_43 : 0 ≤ ((-9 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (579 / 250 : ℝ))
          ·
            apply adjacentR2Left_hit_boundary square fits 17
            change 0 ≤ ((19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 10 : ℝ)) ∧ 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (1 / 25 : ℝ)) ∧ 0 ≤ ((-9 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (579 / 250 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 10 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (19 / 25 : ℝ)) branch_34_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (73 / 100 : ℝ)) negative
              have identity : (19 / 25 : ℝ) * ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-73 / 40 : ℝ)) + (73 / 100 : ℝ) * ((-19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 10 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              by_contra! failed
              have negative : 0 < ((2 / 5 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-1 / 25 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (57 / 125 : ℝ)) branch_0_negative
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (81 / 500 : ℝ)) branch_43
              have weighted_2 := mul_pos (by norm_num : 0 < (147 / 500 : ℝ)) negative
              have identity : (57 / 125 : ℝ) * ((-13 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-481 / 500 : ℝ)) + (81 / 500 : ℝ) * ((-9 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (579 / 250 : ℝ)) + (147 / 500 : ℝ) * ((2 / 5 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-1 / 25 : ℝ)) = (-1881 / 25000 : ℝ) := by
                ring
              have constant_negative := (by norm_num : 0 < (1881 / 25000 : ℝ))
              nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
            ·
              exact branch_43
          ·
            have branch_43_negative : 0 < ((9 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-579 / 250 : ℝ)) := by linarith only [branch_43]
            by_cases branch_44 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ))
            ·
              apply adjacentR2Left_hit_boundary square fits 18
              change 0 ≤ ((9 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-579 / 250 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-23 / 125 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_43_negative.le
              ·
                exact branch_44
              ·
                exact branch_40_negative.le
            ·
              have branch_44_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [branch_44]
              by_cases branch_45 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
              ·
                apply adjacentR2Left_hit_boundary square fits 31
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
                refine ⟨?_ , ?_ ⟩
                ·
                  exact branch_44_negative.le
                ·
                  exact branch_45
              ·
                have branch_45_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [branch_45]
                apply adjacentR2Left_hit_boundary square fits 45
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (7 / 25 : ℝ)) branch_0_negative
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_33
                  have weighted_2 := mul_pos (by norm_num : 0 < (97 / 500 : ℝ)) negative
                  have identity : (7 / 25 : ℝ) * ((-13 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-481 / 500 : ℝ)) + (13 / 100 : ℝ) * ((7 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-138 / 125 : ℝ)) + (97 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ)) = (-311 / 12500 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (311 / 12500 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_45_negative.le
                ·
                  exact branch_44_negative.le
    ·
      have branch_33_negative : 0 < ((-7 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (138 / 125 : ℝ)) := by linarith only [branch_33]
      by_cases branch_46 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (68 / 25 : ℝ))
      ·
        by_cases branch_47 : 0 ≤ ((-77 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (1201 / 500 : ℝ))
        ·
          by_cases branch_48 : 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ))
          ·
            by_cases branch_49 : 0 ≤ ((7 / 50 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-721 / 1250 : ℝ))
            ·
              by_cases branch_50 : 0 ≤ ((19 / 25 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (-67 / 625 : ℝ))
              ·
                apply adjacentR2Left_hit_boundary square fits 8
                change 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ)) ∧ 0 ≤ ((19 / 25 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (-67 / 625 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-721 / 1250 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_48
                ·
                  exact branch_50
                ·
                  exact branch_49
              ·
                have branch_50_negative : 0 < ((-19 / 25 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (67 / 625 : ℝ)) := by linarith only [branch_50]
                apply adjacentR2Left_hit_boundary square fits 39
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-49 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (68 / 25 : ℝ)) ∧ 0 ≤ ((-19 / 25 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (67 / 625 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (49 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_49
                  have weighted_1 := mul_pos (by norm_num : 0 < (7 / 50 : ℝ)) branch_50_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) negative
                  have identity : (19 / 25 : ℝ) * ((7 / 50 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-721 / 1250 : ℝ)) + (7 / 50 : ℝ) * ((-19 / 25 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (67 / 625 : ℝ)) + (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (49 / 25 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  exact branch_46
                ·
                  exact branch_50_negative.le
            ·
              have branch_49_negative : 0 < ((-7 / 50 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (721 / 1250 : ℝ)) := by linarith only [branch_49]
              by_cases branch_51 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ))
              ·
                apply adjacentR2Left_hit_boundary square fits 37
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) container_0
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) negative
                  have identity : (13 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (0 : ℝ)) + (1 : ℝ) * ((-13 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-481 / 500 : ℝ)) + (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) = (-71 / 250 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (71 / 250 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_51
                ·
                  by_contra! failed
                  have negative : 0 < ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (69 / 100 : ℝ)) branch_48
                  have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                  have identity : (69 / 100 : ℝ) * ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ)) + (9 / 10 : ℝ) * ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_51_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) := by linarith only [branch_51]
                by_cases branch_52 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (49 / 25 : ℝ))
                ·
                  apply adjacentR2Left_hit_boundary square fits 38
                  change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (49 / 25 : ℝ)) ∧ 0 ≤ ((-7 / 50 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (721 / 1250 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_51_negative.le
                  ·
                    exact branch_52
                  ·
                    exact branch_49_negative.le
                ·
                  have branch_52_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-49 / 25 : ℝ)) := by linarith only [branch_52]
                  apply adjacentR2Left_hit_boundary square fits 39
                  change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-49 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (68 / 25 : ℝ)) ∧ 0 ≤ ((-19 / 25 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (67 / 625 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_52_negative.le
                  ·
                    exact branch_46
                  ·
                    by_contra! failed
                    have negative : 0 < ((19 / 25 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (-67 / 625 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (19 / 25 : ℝ)) branch_49_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) branch_52_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (7 / 50 : ℝ)) negative
                    have identity : (19 / 25 : ℝ) * ((-7 / 50 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (721 / 1250 : ℝ)) + (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-49 / 25 : ℝ)) + (7 / 50 : ℝ) * ((19 / 25 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (-67 / 625 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_48_negative : 0 < ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) := by linarith only [branch_48]
            apply adjacentR2Left_hit_boundary square fits 9
            change 0 ≤ ((-13 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-481 / 500 : ℝ)) ∧ 0 ≤ ((-77 / 100 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (1201 / 500 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_0_negative.le
            ·
              exact branch_47
            ·
              exact branch_48_negative.le
        ·
          have branch_47_negative : 0 < ((77 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-1201 / 500 : ℝ)) := by linarith only [branch_47]
          by_cases branch_53 : 0 ≤ ((77 / 100 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-113 / 250 : ℝ))
          ·
            by_cases branch_54 : 0 ≤ ((-41 / 100 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-1099 / 1000 : ℝ))
            ·
              apply adjacentR2Left_hit_boundary square fits 14
              change 0 ≤ ((-9 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (52 / 25 : ℝ)) ∧ 0 ≤ ((77 / 100 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-113 / 250 : ℝ)) ∧ 0 ≤ ((-41 / 100 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-1099 / 1000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((9 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-52 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (9 / 25 : ℝ)) branch_33_negative
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (17 / 250 : ℝ)) branch_46
                have weighted_2 := mul_pos (by norm_num : 0 < (7 / 25 : ℝ)) negative
                have identity : (9 / 25 : ℝ) * ((-7 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (138 / 125 : ℝ)) + (17 / 250 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (68 / 25 : ℝ)) + (7 / 25 : ℝ) * ((9 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-52 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_53
              ·
                exact branch_54
            ·
              have branch_54_negative : 0 < ((41 / 100 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (1099 / 1000 : ℝ)) := by linarith only [branch_54]
              apply adjacentR2Left_hit_boundary square fits 16
              change 0 ≤ ((41 / 100 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (1099 / 1000 : ℝ)) ∧ 0 ≤ ((7 / 20 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-463 / 200 : ℝ)) ∧ 0 ≤ ((-19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 10 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_54_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((-7 / 20 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (463 / 200 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (483 / 1000 : ℝ)) branch_0_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (327 / 1000 : ℝ)) branch_47_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (27 / 50 : ℝ)) negative
                have identity : (483 / 1000 : ℝ) * ((-13 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-481 / 500 : ℝ)) + (327 / 1000 : ℝ) * ((77 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-1201 / 500 : ℝ)) + (27 / 50 : ℝ) * ((-7 / 20 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (463 / 200 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                by_contra! failed
                have negative : 0 < ((19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 10 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (19 / 125 : ℝ)) branch_0_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (57 / 125 : ℝ)) branch_33_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (97 / 500 : ℝ)) negative
                have identity : (19 / 125 : ℝ) * ((-13 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-481 / 500 : ℝ)) + (57 / 125 : ℝ) * ((-7 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (138 / 125 : ℝ)) + (97 / 500 : ℝ) * ((19 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 10 : ℝ)) = (-57 / 5000 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (57 / 5000 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
          ·
            have branch_53_negative : 0 < ((-77 / 100 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (113 / 250 : ℝ)) := by linarith only [branch_53]
            apply adjacentR2Left_hit_boundary square fits 19
            change 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (68 / 25 : ℝ)) ∧ 0 ≤ ((77 / 100 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-1201 / 500 : ℝ)) ∧ 0 ≤ ((-77 / 100 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (113 / 250 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_46
            ·
              exact branch_47_negative.le
            ·
              exact branch_53_negative.le
      ·
        have branch_46_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-68 / 25 : ℝ)) := by linarith only [branch_46]
        by_cases branch_55 : 0 ≤ ((7 / 25 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (237 / 125 : ℝ))
        ·
          apply adjacentR2Left_hit_boundary square fits 20
          change 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (138 / 125 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (237 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-68 / 25 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_33_negative.le
          ·
            exact branch_55
          ·
            exact branch_46_negative.le
        ·
          have branch_55_negative : 0 < ((-7 / 25 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-237 / 125 : ℝ)) := by linarith only [branch_55]
          by_cases branch_56 : 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ))
          ·
            by_cases branch_57 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
            ·
              apply adjacentR2Left_hit_boundary square fits 40
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-68 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_46_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_57
                have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (7 / 25 : ℝ)) branch_56
                have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                have identity : (7 / 25 : ℝ) * ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ)) + (9 / 10 : ℝ) * ((7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_57_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_57]
              apply adjacentR2Left_hit_boundary square fits 30
              change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_56
                have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                have identity : (1 : ℝ) * ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ)) + (9 / 10 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_57_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_56_negative : 0 < ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) := by linarith only [branch_56]
            by_cases branch_58 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
            ·
              apply adjacentR2Left_hit_boundary square fits 23
              change 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-237 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_55_negative.le
              ·
                exact branch_58
              ·
                by_contra! failed
                have negative : 0 < ((-7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (7 / 25 : ℝ)) branch_56_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                have identity : (7 / 25 : ℝ) * ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) + (9 / 10 : ℝ) * ((-7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_58_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_58]
              apply adjacentR2Left_hit_boundary square fits 42
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_56_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                have identity : (1 : ℝ) * ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) + (9 / 10 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) branch_33_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (1 / 5 : ℝ)) branch_55_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (7 / 25 : ℝ)) negative
                have identity : (4 / 5 : ℝ) * ((-7 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (138 / 125 : ℝ)) + (1 / 5 : ℝ) * ((-7 / 25 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-237 / 125 : ℝ)) + (7 / 25 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_58_negative.le

end SquarePackingArchive.BentzThirteen
