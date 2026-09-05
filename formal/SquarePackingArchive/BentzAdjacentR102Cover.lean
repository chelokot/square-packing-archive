import SquarePackingArchive.BentzAdjacentR102Geometry

namespace SquarePackingArchive.BentzThirteen

set_option maxHeartbeats 4000000 in
theorem adjacentR102_unavoidable : ∀ square : PlacedSquare, square.Fits 4 → adjacentR102Outcome square := by
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
  by_cases branch_0 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ))
  ·
    by_cases branch_1 : 0 ≤ ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ))
    ·
      by_cases branch_2 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ))
      ·
        by_cases branch_3 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ))
        ·
          by_cases branch_4 : 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ))
          ·
            by_cases branch_5 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ))
            ·
              by_cases branch_6 : 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1641 / 50000 : ℝ))
              ·
                apply adjacentR102_hit_boundary square fits 0
                change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1641 / 50000 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_4
                ·
                  exact branch_1
                ·
                  exact branch_6
              ·
                have branch_6_negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) := by linarith only [branch_6]
                by_cases branch_7 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ))
                ·
                  apply adjacentR102_hit_boundary square fits 24
                  change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
                  refine ⟨?_ , ?_ ⟩
                  ·
                    exact branch_7
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_1
                    have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                ·
                  have branch_7_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) := by linarith only [branch_7]
                  apply adjacentR102_hit_boundary square fits 30
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_7_negative.le
                  ·
                    exact branch_5
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 125 : ℝ)) branch_1
                    have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                    have identity : (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_5_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_5]
              apply adjacentR102_hit_boundary square fits 0
              change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1641 / 50000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_4
              ·
                exact branch_1
              ·
                by_contra! failed
                have negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_1
                have weighted_1 := mul_pos (by norm_num : 0 < (1591 / 50000 : ℝ)) branch_5_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (13 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (1591 / 50000 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (37 / 100 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_4_negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) := by linarith only [branch_4]
            by_cases branch_8 : 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ))
            ·
              apply adjacentR102_hit_boundary square fits 2
              change 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_8
              ·
                by_contra! failed
                have negative : 0 < ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (917 / 5000 : ℝ)) branch_1
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (111 / 1250 : ℝ)) branch_3
                have weighted_2 := mul_pos (by norm_num : 0 < (1517 / 5000 : ℝ)) negative
                have identity : (917 / 5000 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (111 / 1250 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) + (1517 / 5000 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_4_negative.le
            ·
              have branch_8_negative : 0 < ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ)) := by linarith only [branch_8]
              by_cases branch_9 : 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
              ·
                by_cases branch_10 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ))
                ·
                  apply adjacentR102_hit_boundary square fits 29
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_10
                  ·
                    exact branch_2
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_1
                    have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                    have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                ·
                  have branch_10_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [branch_10]
                  apply adjacentR102_hit_boundary square fits 28
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_9
                    have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                    have identity : (1 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_10_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) = (-13 / 100 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_8_negative.le
              ·
                have branch_9_negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [branch_9]
                by_cases branch_11 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ))
                ·
                  apply adjacentR102_hit_boundary square fits 24
                  change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
                  refine ⟨?_ , ?_ ⟩
                  ·
                    exact branch_11
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_1
                    have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                ·
                  have branch_11_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) := by linarith only [branch_11]
                  apply adjacentR102_hit_boundary square fits 30
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_11_negative.le
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_9_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                    have identity : (1 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) = (-5889 / 50000 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (5889 / 50000 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 125 : ℝ)) branch_1
                    have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                    have identity : (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_3_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) := by linarith only [branch_3]
          by_cases branch_12 : 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ))
          ·
            by_cases branch_13 : 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ))
            ·
              apply adjacentR102_hit_boundary square fits 2
              change 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_13
              ·
                exact branch_12
              ·
                by_contra! failed
                have negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (453 / 1000 : ℝ)) branch_1
                have weighted_1 := mul_pos (by norm_num : 0 < (1591 / 50000 : ℝ)) branch_3_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1517 / 5000 : ℝ)) negative
                have identity : (453 / 1000 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (1591 / 50000 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) + (1517 / 5000 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_13_negative : 0 < ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ)) := by linarith only [branch_13]
              by_cases branch_14 : 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ))
              ·
                by_cases branch_15 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ))
                ·
                  apply adjacentR102_hit_boundary square fits 28
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_0
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_3_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                    have identity : (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) + (1 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) + (41 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                  ·
                    exact branch_15
                  ·
                    exact branch_13_negative.le
                ·
                  have branch_15_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) := by linarith only [branch_15]
                  apply adjacentR102_hit_boundary square fits 29
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_15_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (-13 / 100 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_2
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_1
                    have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                    have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_14_negative : 0 < ((6 / 25 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1369 / 2500 : ℝ)) := by linarith only [branch_14]
                apply adjacentR102_hit_boundary square fits 29
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_1
                  have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) branch_14_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (111 / 1250 : ℝ)) negative
                  have identity : (13 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1369 / 2500 : ℝ)) + (111 / 1250 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  exact branch_2
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_1
                  have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                  have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_12_negative : 0 < ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) := by linarith only [branch_12]
            by_cases branch_16 : 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (63 / 100 : ℝ) * square.center.y + (-3 / 100 : ℝ))
            ·
              apply adjacentR102_hit_boundary square fits 6
              change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (63 / 100 : ℝ) * square.center.y + (-3 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_12_negative.le
              ·
                exact branch_16
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_1
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_16_negative : 0 < ((6 / 25 : ℝ) * square.center.x + (-63 / 100 : ℝ) * square.center.y + (3 / 100 : ℝ)) := by linarith only [branch_16]
              apply adjacentR102_hit_boundary square fits 29
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (63 / 100 : ℝ)) branch_12_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) branch_16_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (6 / 25 : ℝ)) negative
                have identity : (63 / 100 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) + (37 / 100 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (-63 / 100 : ℝ) * square.center.y + (3 / 100 : ℝ)) + (6 / 25 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (-39 / 1250 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (39 / 1250 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                exact branch_2
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_1
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_2_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [branch_2]
        by_cases branch_17 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ))
        ·
          apply adjacentR102_hit_boundary square fits 31
          change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (1 / 2 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_2_negative.le
          ·
            by_contra! failed
            have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_17
            have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
            have identity : (1 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-1 / 2 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_1
            have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
            have identity : (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-1 / 2 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_17_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) := by linarith only [branch_17]
          apply adjacentR102_hit_boundary square fits 25
          change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
          refine ⟨?_ , ?_ ⟩
          ·
            by_contra! failed
            have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_17_negative
            have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
            have identity : (1 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_1
            have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
            have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
    ·
      have branch_1_negative : 0 < ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) := by linarith only [branch_1]
      by_cases branch_18 : 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-73 / 100 : ℝ))
      ·
        by_cases branch_19 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (51 / 20 : ℝ))
        ·
          apply adjacentR102_hit_boundary square fits 9
          change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (51 / 20 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-73 / 100 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_1_negative
            have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
            have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          ·
            exact branch_19
          ·
            exact branch_18
        ·
          have branch_19_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-51 / 20 : ℝ)) := by linarith only [branch_19]
          by_cases branch_20 : 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-31 / 20 : ℝ))
          ·
            by_cases branch_21 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ))
            ·
              apply adjacentR102_hit_boundary square fits 18
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-1 / 2 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-31 / 20 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (1 / 2 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) branch_1_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (1 / 2 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_21
              ·
                exact branch_20
            ·
              have branch_21_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) := by linarith only [branch_21]
              apply adjacentR102_hit_boundary square fits 39
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_1_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_0
              ·
                exact branch_21_negative.le
          ·
            have branch_20_negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (31 / 20 : ℝ)) := by linarith only [branch_20]
            apply adjacentR102_hit_boundary square fits 19
            change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (31 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-51 / 20 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_20_negative.le
            ·
              exact branch_0
            ·
              exact branch_19_negative.le
      ·
        have branch_18_negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) := by linarith only [branch_18]
        by_cases branch_22 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ))
        ·
          by_cases branch_23 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ))
          ·
            by_cases branch_24 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ))
            ·
              by_cases branch_25 : 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
              ·
                apply adjacentR102_hit_boundary square fits 3
                change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (367 / 1000 : ℝ)) branch_1_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (1591 / 50000 : ℝ)) branch_18_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (1517 / 5000 : ℝ)) negative
                  have identity : (367 / 1000 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (1591 / 50000 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) + (1517 / 5000 : ℝ) * ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  exact branch_22
                ·
                  exact branch_25
              ·
                have branch_25_negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [branch_25]
                apply adjacentR102_hit_boundary square fits 32
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 125 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_1_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) = (-1591 / 50000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (1591 / 50000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_24
                ·
                  by_contra! failed
                  have negative : 0 < ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) branch_25_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                  have identity : (27 / 125 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_24_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_24]
              by_cases branch_26 : 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
              ·
                apply adjacentR102_hit_boundary square fits 3
                change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (367 / 1000 : ℝ)) branch_1_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (1591 / 50000 : ℝ)) branch_18_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (1517 / 5000 : ℝ)) negative
                  have identity : (367 / 1000 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (1591 / 50000 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) + (1517 / 5000 : ℝ) * ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  exact branch_22
                ·
                  exact branch_26
              ·
                have branch_26_negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [branch_26]
                apply adjacentR102_hit_boundary square fits 33
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_24_negative.le
                ·
                  exact branch_0
                ·
                  by_contra! failed
                  have negative : 0 < ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (69 / 100 : ℝ)) branch_26_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                  have identity : (69 / 100 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_23_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_23]
            apply adjacentR102_hit_boundary square fits 3
            change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (367 / 1000 : ℝ)) branch_1_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (1591 / 50000 : ℝ)) branch_18_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (1517 / 5000 : ℝ)) negative
              have identity : (367 / 1000 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (1591 / 50000 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) + (1517 / 5000 : ℝ) * ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_22
            ·
              by_contra! failed
              have negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) branch_23_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
              have identity : (453 / 500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (1 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) = (-5889 / 50000 : ℝ) := by
                ring
              have constant_negative := (by norm_num : 0 < (5889 / 50000 : ℝ))
              nlinarith only [weighted_0, weighted_1, constant_negative, identity]
        ·
          have branch_22_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) := by linarith only [branch_22]
          apply adjacentR102_hit_boundary square fits 8
          change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_18_negative.le
          ·
            exact branch_0
          ·
            exact branch_22_negative.le
  ·
    have branch_0_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) := by linarith only [branch_0]
    by_cases branch_27 : 0 ≤ ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (219 / 200 : ℝ))
    ·
      by_cases branch_28 : 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (77 / 50 : ℝ))
      ·
        by_cases branch_29 : 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
        ·
          by_cases branch_30 : 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ))
          ·
            apply adjacentR102_hit_boundary square fits 11
            change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (77 / 50 : ℝ)) ∧ 0 ≤ ((39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_30
            ·
              exact branch_28
            ·
              by_contra! failed
              have negative : 0 < ((-39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (39 / 50 : ℝ)) branch_29
              have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
              have identity : (39 / 50 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((-39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_30_negative : 0 < ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (37 / 100 : ℝ)) := by linarith only [branch_30]
            apply adjacentR102_hit_boundary square fits 12
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (199 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (37 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_0_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-199 / 100 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 20 : ℝ)) branch_27
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (73 / 200 : ℝ)) branch_28
              have weighted_2 := mul_pos (by norm_num : 0 < (73 / 200 : ℝ)) negative
              have identity : (3 / 20 : ℝ) * ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (219 / 200 : ℝ)) + (73 / 200 : ℝ) * ((-6 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (77 / 50 : ℝ)) + (73 / 200 : ℝ) * ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-199 / 100 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_30_negative.le
        ·
          have branch_29_negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [branch_29]
          by_cases branch_31 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 5 : ℝ))
          ·
            apply adjacentR102_hit_boundary square fits 34
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 5 : ℝ)) ∧ 0 ≤ ((-39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_0_negative.le
            ·
              exact branch_31
            ·
              by_contra! failed
              have negative : 0 < ((39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (39 / 50 : ℝ)) branch_29_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
              have identity : (39 / 50 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_31_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 5 : ℝ)) := by linarith only [branch_31]
            by_cases branch_32 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
            ·
              apply adjacentR102_hit_boundary square fits 26
              change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_29_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                have identity : (1 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_32
            ·
              have branch_32_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [branch_32]
              apply adjacentR102_hit_boundary square fits 35
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 / 5 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_31_negative.le
              ·
                exact branch_32_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((2 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (2 / 5 : ℝ)) branch_29_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                have identity : (2 / 5 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((2 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_28_negative : 0 < ((6 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-77 / 50 : ℝ)) := by linarith only [branch_28]
        by_cases branch_33 : 0 ≤ ((49 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (81 / 100 : ℝ))
        ·
          apply adjacentR102_hit_boundary square fits 13
          change 0 ≤ ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (219 / 200 : ℝ)) ∧ 0 ≤ ((49 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (81 / 100 : ℝ)) ∧ 0 ≤ ((6 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-77 / 50 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_27
          ·
            exact branch_33
          ·
            exact branch_28_negative.le
        ·
          have branch_33_negative : 0 < ((-49 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-81 / 100 : ℝ)) := by linarith only [branch_33]
          by_cases branch_34 : 0 ≤ ((39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ))
          ·
            by_cases branch_35 : 0 ≤ ((9 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (141 / 100 : ℝ))
            ·
              apply adjacentR102_hit_boundary square fits 16
              change 0 ≤ ((9 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (141 / 100 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 / 5 : ℝ)) ∧ 0 ≤ ((-49 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-81 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_35
              ·
                by_contra! failed
                have negative : 0 < ((-2 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) branch_34
                have weighted_1 := mul_pos (by norm_num : 0 < (39 / 50 : ℝ)) negative
                have identity : (2 / 5 : ℝ) * ((39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ)) + (39 / 50 : ℝ) * ((-2 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_33_negative.le
            ·
              have branch_35_negative : 0 < ((-9 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-141 / 100 : ℝ)) := by linarith only [branch_35]
              apply adjacentR102_hit_boundary square fits 37
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-141 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_34
                have weighted_1 := mul_pos (by norm_num : 0 < (39 / 50 : ℝ)) negative
                have identity : (1 : ℝ) * ((39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-39 / 50 : ℝ)) + (39 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_27
                have weighted_1 := mul_pos (by norm_num : 0 < (73 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (219 / 200 : ℝ)) + (73 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_35_negative.le
          ·
            have branch_34_negative : 0 < ((-39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) := by linarith only [branch_34]
            by_cases branch_36 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
            ·
              apply adjacentR102_hit_boundary square fits 26
              change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_34_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (39 / 50 : ℝ)) negative
                have identity : (1 : ℝ) * ((-39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) + (39 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_36
            ·
              have branch_36_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [branch_36]
              apply adjacentR102_hit_boundary square fits 35
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-13 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 / 5 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (49 / 100 : ℝ)) branch_28_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (6 / 25 : ℝ)) branch_33_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (73 / 200 : ℝ)) negative
                have identity : (49 / 100 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-77 / 50 : ℝ)) + (6 / 25 : ℝ) * ((-49 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-81 / 100 : ℝ)) + (73 / 200 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (13 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_36_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((2 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (2 / 5 : ℝ)) branch_34_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (39 / 50 : ℝ)) negative
                have identity : (2 / 5 : ℝ) * ((-39 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (39 / 50 : ℝ)) + (39 / 50 : ℝ) * ((2 / 5 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
    ·
      have branch_27_negative : 0 < ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-219 / 200 : ℝ)) := by linarith only [branch_27]
      by_cases branch_37 : 0 ≤ ((-17 / 25 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (407 / 500 : ℝ))
      ·
        by_cases branch_38 : 0 ≤ ((-7 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-839 / 500 : ℝ))
        ·
          by_cases branch_39 : 0 ≤ ((-59 / 100 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (3357 / 1000 : ℝ))
          ·
            apply adjacentR102_hit_boundary square fits 14
            change 0 ≤ ((-7 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-839 / 500 : ℝ)) ∧ 0 ≤ ((-59 / 100 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (3357 / 1000 : ℝ)) ∧ 0 ≤ ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-219 / 200 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_38
            ·
              exact branch_39
            ·
              exact branch_27_negative.le
          ·
            have branch_39_negative : 0 < ((59 / 100 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-3357 / 1000 : ℝ)) := by linarith only [branch_39]
            by_cases branch_40 : 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 20 : ℝ))
            ·
              by_cases branch_41 : 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (2607 / 1000 : ℝ))
              ·
                apply adjacentR102_hit_boundary square fits 17
                change 0 ≤ ((59 / 100 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-3357 / 1000 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 20 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (2607 / 1000 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_39_negative.le
                ·
                  exact branch_40
                ·
                  exact branch_41
              ·
                have branch_41_negative : 0 < ((9 / 100 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-2607 / 1000 : ℝ)) := by linarith only [branch_41]
                apply adjacentR102_hit_boundary square fits 36
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) ∧ 0 ≤ ((9 / 100 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-2607 / 1000 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_27_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (73 / 100 : ℝ)) negative
                  have identity : (1 : ℝ) * ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-219 / 200 : ℝ)) + (73 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_40
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                  have identity : (1 : ℝ) * ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 20 : ℝ)) + (1 / 2 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  exact branch_41_negative.le
            ·
              have branch_40_negative : 0 < ((1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 20 : ℝ)) := by linarith only [branch_40]
              by_cases branch_42 : 0 ≤ ((0 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (21 / 10 : ℝ))
              ·
                apply adjacentR102_hit_boundary square fits 23
                change 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-3 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (21 / 10 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 20 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (3 / 5 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (151 / 500 : ℝ)) branch_37
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (163 / 500 : ℝ)) branch_38
                  have weighted_2 := mul_pos (by norm_num : 0 < (251 / 500 : ℝ)) negative
                  have identity : (151 / 500 : ℝ) * ((-17 / 25 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (407 / 500 : ℝ)) + (163 / 500 : ℝ) * ((-7 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-839 / 500 : ℝ)) + (251 / 500 : ℝ) * ((1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (3 / 5 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  exact branch_42
                ·
                  exact branch_40_negative.le
              ·
                have branch_42_negative : 0 < ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-21 / 10 : ℝ)) := by linarith only [branch_42]
                apply adjacentR102_hit_boundary square fits 38
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-21 / 10 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_40_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                  have identity : (1 : ℝ) * ((1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 20 : ℝ)) + (1 / 2 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 10 : ℝ)) container_3
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_37
                  have weighted_2 := mul_pos (by norm_num : 0 < (17 / 25 : ℝ)) negative
                  have identity : (3 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (4 : ℝ)) + (1 : ℝ) * ((-17 / 25 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (407 / 500 : ℝ)) + (17 / 25 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) = (-13 / 500 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (13 / 500 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_42_negative.le
        ·
          have branch_38_negative : 0 < ((7 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (839 / 500 : ℝ)) := by linarith only [branch_38]
          by_cases branch_43 : 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (199 / 100 : ℝ))
          ·
            apply adjacentR102_hit_boundary square fits 12
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (199 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (37 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_0_negative.le
            ·
              exact branch_43
            ·
              by_contra! failed
              have negative : 0 < ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (181 / 500 : ℝ)) branch_27_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (73 / 200 : ℝ)) branch_38_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (73 / 125 : ℝ)) negative
              have identity : (181 / 500 : ℝ) * ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-219 / 200 : ℝ)) + (73 / 200 : ℝ) * ((7 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (839 / 500 : ℝ)) + (73 / 125 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_43_negative : 0 < ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-199 / 100 : ℝ)) := by linarith only [branch_43]
            apply adjacentR102_hit_boundary square fits 15
            change 0 ≤ ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-199 / 100 : ℝ)) ∧ 0 ≤ ((-17 / 25 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (407 / 500 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (839 / 500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_43_negative.le
            ·
              exact branch_37
            ·
              exact branch_38_negative.le
      ·
        have branch_37_negative : 0 < ((17 / 25 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-407 / 500 : ℝ)) := by linarith only [branch_37]
        by_cases branch_44 : 0 ≤ ((-17 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (1657 / 500 : ℝ))
        ·
          apply adjacentR102_hit_boundary square fits 20
          change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((-17 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (1657 / 500 : ℝ)) ∧ 0 ≤ ((17 / 25 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-407 / 500 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_0_negative.le
          ·
            exact branch_44
          ·
            exact branch_37_negative.le
        ·
          have branch_44_negative : 0 < ((17 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-1657 / 500 : ℝ)) := by linarith only [branch_44]
          by_cases branch_45 : 0 ≤ ((0 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (7 / 4 : ℝ))
          ·
            by_cases branch_46 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ))
            ·
              apply adjacentR102_hit_boundary square fits 21
              change 0 ≤ ((-17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (51 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (7 / 4 : ℝ)) ∧ 0 ≤ ((17 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-1657 / 500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-51 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (17 / 25 : ℝ)) branch_46
                have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                have identity : (17 / 25 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-51 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_45
              ·
                exact branch_44_negative.le
            ·
              have branch_46_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) := by linarith only [branch_46]
              apply adjacentR102_hit_boundary square fits 40
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-51 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_0_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_45
                have weighted_1 := mul_pos (by norm_num : 0 < (7 / 10 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (7 / 4 : ℝ)) + (7 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-5 / 2 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((-17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (51 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (17 / 25 : ℝ)) branch_46_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                have identity : (17 / 25 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((-17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (51 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_45_negative : 0 < ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-7 / 4 : ℝ)) := by linarith only [branch_45]
            by_cases branch_47 : 0 ≤ ((1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (3 / 5 : ℝ))
            ·
              by_cases branch_48 : 0 ≤ ((-17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (51 / 25 : ℝ))
              ·
                apply adjacentR102_hit_boundary square fits 22
                change 0 ≤ ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-7 / 4 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (3 / 5 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_45_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_48
                  have weighted_1 := mul_pos (by norm_num : 0 < (17 / 25 : ℝ)) negative
                  have identity : (1 / 2 : ℝ) * ((-17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (51 / 25 : ℝ)) + (17 / 25 : ℝ) * ((1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  exact branch_47
              ·
                have branch_48_negative : 0 < ((17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-51 / 25 : ℝ)) := by linarith only [branch_48]
                by_cases branch_49 : 0 ≤ ((0 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (21 / 10 : ℝ))
                ·
                  apply adjacentR102_hit_boundary square fits 41
                  change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (5 / 2 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_45_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (7 / 10 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-7 / 4 : ℝ)) + (7 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (5 / 2 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_49
                    have weighted_1 := mul_pos (by norm_num : 0 < (7 / 10 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (21 / 10 : ℝ)) + (7 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) branch_48_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (17 / 25 : ℝ)) negative
                    have identity : (1 / 2 : ℝ) * ((17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-51 / 25 : ℝ)) + (17 / 25 : ℝ) * ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                ·
                  have branch_49_negative : 0 < ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-21 / 10 : ℝ)) := by linarith only [branch_49]
                  apply adjacentR102_hit_boundary square fits 27
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
                  refine ⟨?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_48_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (17 / 25 : ℝ)) negative
                    have identity : (1 : ℝ) * ((17 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-51 / 25 : ℝ)) + (17 / 25 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_49_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (7 / 10 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-21 / 10 : ℝ)) + (7 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_47_negative : 0 < ((-1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-3 / 5 : ℝ)) := by linarith only [branch_47]
              by_cases branch_50 : 0 ≤ ((0 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (21 / 10 : ℝ))
              ·
                apply adjacentR102_hit_boundary square fits 23
                change 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-3 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (21 / 10 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 20 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_47_negative.le
                ·
                  exact branch_50
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 20 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (7 / 20 : ℝ)) branch_37_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (3 / 20 : ℝ)) branch_44_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (17 / 25 : ℝ)) negative
                  have identity : (7 / 20 : ℝ) * ((17 / 25 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-407 / 500 : ℝ)) + (3 / 20 : ℝ) * ((17 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-1657 / 500 : ℝ)) + (17 / 25 : ℝ) * ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 20 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                have branch_50_negative : 0 < ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-21 / 10 : ℝ)) := by linarith only [branch_50]
                by_cases branch_51 : 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ))
                ·
                  apply adjacentR102_hit_boundary square fits 38
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-21 / 10 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (7 / 10 : ℝ)) branch_37_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (3 / 10 : ℝ)) branch_44_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (17 / 25 : ℝ)) negative
                    have identity : (7 / 10 : ℝ) * ((17 / 25 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-407 / 500 : ℝ)) + (3 / 10 : ℝ) * ((17 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-1657 / 500 : ℝ)) + (17 / 25 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_51
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                    have identity : (1 : ℝ) * ((-1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) + (1 / 2 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    exact branch_50_negative.le
                ·
                  have branch_51_negative : 0 < ((1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) := by linarith only [branch_51]
                  apply adjacentR102_hit_boundary square fits 27
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
                  refine ⟨?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_51_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                    have identity : (1 : ℝ) * ((1 / 2 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) + (1 / 2 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_50_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (7 / 10 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-21 / 10 : ℝ)) + (7 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]

end SquarePackingArchive.BentzThirteen
