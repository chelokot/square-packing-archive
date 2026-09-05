import SquarePackingArchive.BentzAdjacentInitialGeometry

namespace SquarePackingArchive.BentzThirteen

set_option maxHeartbeats 4000000 in
theorem adjacentInitial_unavoidable : ∀ square : PlacedSquare, square.Fits 4 → adjacentInitialOutcome square := by
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
      by_cases branch_2 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ))
      ·
        by_cases branch_3 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ))
        ·
          apply adjacentInitial_hit_boundary square fits 15
          change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
          refine ⟨?_ , ?_ ⟩
          ·
            exact branch_3
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_1
            have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
            have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_3_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) := by linarith only [branch_3]
          by_cases branch_4 : 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ))
          ·
            by_cases branch_5 : 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1641 / 50000 : ℝ))
            ·
              apply adjacentInitial_hit_boundary square fits 1
              change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1641 / 50000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_4
              ·
                exact branch_1
              ·
                exact branch_5
            ·
              have branch_5_negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) := by linarith only [branch_5]
              apply adjacentInitial_hit_boundary square fits 21
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_3_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_1
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) branch_5_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1591 / 50000 : ℝ)) negative
                have identity : (13 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) + (1591 / 50000 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 125 : ℝ)) branch_1
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_4_negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) := by linarith only [branch_4]
            by_cases branch_6 : 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ))
            ·
              apply adjacentInitial_hit_boundary square fits 3
              change 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_6
              ·
                by_contra! failed
                have negative : 0 < ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (917 / 5000 : ℝ)) branch_1
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (111 / 1250 : ℝ)) branch_2
                have weighted_2 := mul_pos (by norm_num : 0 < (1517 / 5000 : ℝ)) negative
                have identity : (917 / 5000 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (111 / 1250 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) + (1517 / 5000 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_4_negative.le
            ·
              have branch_6_negative : 0 < ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ)) := by linarith only [branch_6]
              by_cases branch_7 : 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
              ·
                by_cases branch_8 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ))
                ·
                  apply adjacentInitial_hit_boundary square fits 20
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_8
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) container_2
                    have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_2
                    have weighted_2 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                    have identity : (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + (1 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) + (41 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) = (-8 / 25 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (8 / 25 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_1
                    have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                    have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                ·
                  have branch_8_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [branch_8]
                  apply adjacentInitial_hit_boundary square fits 19
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_7
                    have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                    have identity : (1 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_8_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) = (-13 / 100 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_6_negative.le
              ·
                have branch_7_negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [branch_7]
                apply adjacentInitial_hit_boundary square fits 21
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_3_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_7_negative
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
        have branch_2_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) := by linarith only [branch_2]
        by_cases branch_9 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ))
        ·
          by_cases branch_10 : 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ))
          ·
            by_cases branch_11 : 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ))
            ·
              apply adjacentInitial_hit_boundary square fits 3
              change 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_11
              ·
                exact branch_10
              ·
                by_contra! failed
                have negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (453 / 1000 : ℝ)) branch_1
                have weighted_1 := mul_pos (by norm_num : 0 < (1591 / 50000 : ℝ)) branch_2_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1517 / 5000 : ℝ)) negative
                have identity : (453 / 1000 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (1591 / 50000 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) + (1517 / 5000 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_11_negative : 0 < ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ)) := by linarith only [branch_11]
              by_cases branch_12 : 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ))
              ·
                by_cases branch_13 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ))
                ·
                  apply adjacentInitial_hit_boundary square fits 19
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_0
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_2_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                    have identity : (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) + (1 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) + (41 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                  ·
                    exact branch_13
                  ·
                    exact branch_11_negative.le
                ·
                  have branch_13_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) := by linarith only [branch_13]
                  apply adjacentInitial_hit_boundary square fits 20
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_13_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (-13 / 100 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_9
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_1
                    have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                    have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_12_negative : 0 < ((6 / 25 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1369 / 2500 : ℝ)) := by linarith only [branch_12]
                apply adjacentInitial_hit_boundary square fits 20
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_1
                  have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) branch_12_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (111 / 1250 : ℝ)) negative
                  have identity : (13 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1369 / 2500 : ℝ)) + (111 / 1250 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  exact branch_9
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_1
                  have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                  have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_10_negative : 0 < ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) := by linarith only [branch_10]
            by_cases branch_14 : 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (63 / 100 : ℝ) * square.center.y + (-3 / 100 : ℝ))
            ·
              apply adjacentInitial_hit_boundary square fits 8
              change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (63 / 100 : ℝ) * square.center.y + (-3 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_10_negative.le
              ·
                exact branch_14
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_1
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_14_negative : 0 < ((6 / 25 : ℝ) * square.center.x + (-63 / 100 : ℝ) * square.center.y + (3 / 100 : ℝ)) := by linarith only [branch_14]
              apply adjacentInitial_hit_boundary square fits 20
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (63 / 100 : ℝ)) branch_10_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) branch_14_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (6 / 25 : ℝ)) negative
                have identity : (63 / 100 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) + (37 / 100 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (-63 / 100 : ℝ) * square.center.y + (3 / 100 : ℝ)) + (6 / 25 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (-39 / 1250 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (39 / 1250 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                exact branch_9
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_1
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_9_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [branch_9]
          by_cases branch_15 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ))
          ·
            apply adjacentInitial_hit_boundary square fits 22
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (1 / 2 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_9_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_15
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
            have branch_15_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) := by linarith only [branch_15]
            apply adjacentInitial_hit_boundary square fits 16
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
            refine ⟨?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_15_negative
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
      by_cases branch_16 : 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-73 / 100 : ℝ))
      ·
        by_cases branch_17 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (51 / 20 : ℝ))
        ·
          apply adjacentInitial_hit_boundary square fits 11
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
            exact branch_17
          ·
            exact branch_16
        ·
          have branch_17_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-51 / 20 : ℝ)) := by linarith only [branch_17]
          by_cases branch_18 : 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-31 / 20 : ℝ))
          ·
            by_cases branch_19 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ))
            ·
              apply adjacentInitial_hit_boundary square fits 13
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
                exact branch_19
              ·
                exact branch_18
            ·
              have branch_19_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) := by linarith only [branch_19]
              apply adjacentInitial_hit_boundary square fits 27
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
                exact branch_19_negative.le
          ·
            have branch_18_negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (31 / 20 : ℝ)) := by linarith only [branch_18]
            apply adjacentInitial_hit_boundary square fits 14
            change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (31 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-51 / 20 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_18_negative.le
            ·
              exact branch_0
            ·
              exact branch_17_negative.le
      ·
        have branch_16_negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) := by linarith only [branch_16]
        by_cases branch_20 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ))
        ·
          by_cases branch_21 : 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-16587 / 25000 : ℝ))
          ·
            apply adjacentInitial_hit_boundary square fits 9
            change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_20
            ·
              exact branch_21
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) branch_1_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
              have identity : (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_21_negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (16587 / 25000 : ℝ)) := by linarith only [branch_21]
            apply adjacentInitial_hit_boundary square fits 30
            change 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (16587 / 25000 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_0
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_1_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_21_negative.le
        ·
          have branch_20_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) := by linarith only [branch_20]
          apply adjacentInitial_hit_boundary square fits 10
          change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_16_negative.le
          ·
            exact branch_0
          ·
            exact branch_20_negative.le
  ·
    have branch_0_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) := by linarith only [branch_0]
    by_cases branch_22 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ))
    ·
      by_cases branch_23 : 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
      ·
        by_cases branch_24 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ))
        ·
          apply adjacentInitial_hit_boundary square fits 34
          change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ))
          refine ⟨?_ , ?_ , ?_ , ?_ ⟩
          ·
            by_contra! failed
            have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_23
            have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
            have identity : (1 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          ·
            exact branch_22
          ·
            exact branch_0_negative.le
          ·
            exact branch_24
        ·
          have branch_24_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) := by linarith only [branch_24]
          by_cases branch_25 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ))
          ·
            apply adjacentInitial_hit_boundary square fits 25
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_23
              have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
              have identity : (1 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_22
            ·
              exact branch_25
          ·
            have branch_25_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ)) := by linarith only [branch_25]
            apply adjacentInitial_hit_boundary square fits 31
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_23
              have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
              have identity : (1 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_22
            ·
              exact branch_24_negative.le
            ·
              exact branch_25_negative.le
      ·
        have branch_23_negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [branch_23]
        by_cases branch_26 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ))
        ·
          apply adjacentInitial_hit_boundary square fits 23
          change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 50 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_0_negative.le
          ·
            exact branch_26
          ·
            by_contra! failed
            have negative : 0 < ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 50 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_pos (by norm_num : 0 < (27 / 50 : ℝ)) branch_23_negative
            have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
            have identity : (27 / 50 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 50 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_26_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) := by linarith only [branch_26]
          by_cases branch_27 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ))
          ·
            apply adjacentInitial_hit_boundary square fits 17
            change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ))
            refine ⟨?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_23_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
              have identity : (1 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_27
          ·
            have branch_27_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ)) := by linarith only [branch_27]
            apply adjacentInitial_hit_boundary square fits 24
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ)) ∧ 0 ≤ ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_26_negative.le
            ·
              exact branch_27_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-73 / 100 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (73 / 100 : ℝ)) branch_23_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
              have identity : (73 / 100 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-73 / 100 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
    ·
      have branch_22_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) := by linarith only [branch_22]
      by_cases branch_28 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ))
      ·
        by_cases branch_29 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ))
        ·
          apply adjacentInitial_hit_boundary square fits 33
          change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ))
          refine ⟨?_ , ?_ , ?_ , ?_ ⟩
          ·
            exact branch_22_negative.le
          ·
            by_contra! failed
            have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_29
            have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
            have identity : (1 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          ·
            exact branch_0_negative.le
          ·
            exact branch_28
        ·
          have branch_29_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) := by linarith only [branch_29]
          apply adjacentInitial_hit_boundary square fits 28
          change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-81 / 50 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_0_negative.le
          ·
            exact branch_28
          ·
            by_contra! failed
            have negative : 0 < ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (81 / 50 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_pos (by norm_num : 0 < (27 / 50 : ℝ)) branch_29_negative
            have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
            have identity : (27 / 50 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (81 / 50 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_28_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) := by linarith only [branch_28]
        by_cases branch_30 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ))
        ·
          by_cases branch_31 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ))
          ·
            apply adjacentInitial_hit_boundary square fits 18
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ))
            refine ⟨?_ , ?_ ⟩
            ·
              exact branch_30
            ·
              exact branch_31
          ·
            have branch_31_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ)) := by linarith only [branch_31]
            apply adjacentInitial_hit_boundary square fits 29
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ)) ∧ 0 ≤ ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-219 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_28_negative.le
            ·
              exact branch_31_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (219 / 100 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (73 / 100 : ℝ)) branch_30
              have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
              have identity : (73 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) + (1 : ℝ) * ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (219 / 100 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_30_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [branch_30]
          by_cases branch_32 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ))
          ·
            apply adjacentInitial_hit_boundary square fits 26
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-309 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_22_negative.le
            ·
              exact branch_30_negative.le
            ·
              exact branch_32
          ·
            have branch_32_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ)) := by linarith only [branch_32]
            apply adjacentInitial_hit_boundary square fits 32
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (309 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ , ?_ ⟩
            ·
              exact branch_22_negative.le
            ·
              exact branch_30_negative.le
            ·
              exact branch_28_negative.le
            ·
              exact branch_32_negative.le

end SquarePackingArchive.BentzThirteen
