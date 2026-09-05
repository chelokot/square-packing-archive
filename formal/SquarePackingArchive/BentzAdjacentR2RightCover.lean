import SquarePackingArchive.BentzAdjacentR2RightGeometry

namespace SquarePackingArchive.BentzThirteen

set_option maxHeartbeats 4000000 in
theorem adjacentR2Right_unavoidable : ∀ square : PlacedSquare, square.Fits 4 → adjacentR2RightOutcome square := by
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
    by_cases branch_1 : 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-73 / 100 : ℝ))
    ·
      by_cases branch_2 : 0 ≤ ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ))
      ·
        by_cases branch_3 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ))
        ·
          by_cases branch_4 : 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ))
          ·
            by_cases branch_5 : 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ))
            ·
              apply adjacentR2Right_hit_boundary square fits 4
              change 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_5
              ·
                exact branch_4
              ·
                by_contra! failed
                have negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1591 / 50000 : ℝ)) branch_1
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (367 / 1000 : ℝ)) branch_2
                have weighted_2 := mul_pos (by norm_num : 0 < (1517 / 5000 : ℝ)) negative
                have identity : (1591 / 50000 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-73 / 100 : ℝ)) + (367 / 1000 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (1517 / 5000 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_5_negative : 0 < ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ)) := by linarith only [branch_5]
              by_cases branch_6 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ))
              ·
                by_cases branch_7 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ))
                ·
                  by_cases branch_8 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ))
                  ·
                    apply adjacentR2Right_hit_boundary square fits 26
                    change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
                    refine ⟨?_ , ?_ ⟩
                    ·
                      exact branch_8
                    ·
                      by_contra! failed
                      have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_2
                      have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                      have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    have branch_8_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) := by linarith only [branch_8]
                    apply adjacentR2Right_hit_boundary square fits 32
                    change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      exact branch_8_negative.le
                    ·
                      exact branch_7
                    ·
                      by_contra! failed
                      have negative : 0 < ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 125 : ℝ)) branch_2
                      have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                      have identity : (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, identity]
                ·
                  have branch_7_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_7]
                  apply adjacentR2Right_hit_boundary square fits 30
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_7_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (-13 / 100 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_6
                  ·
                    exact branch_5_negative.le
              ·
                have branch_6_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) := by linarith only [branch_6]
                apply adjacentR2Right_hit_boundary square fits 31
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_6_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (-13 / 100 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_3
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_2
                  have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                  have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_4_negative : 0 < ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) := by linarith only [branch_4]
            by_cases branch_9 : 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (63 / 100 : ℝ) * square.center.y + (-3 / 100 : ℝ))
            ·
              apply adjacentR2Right_hit_boundary square fits 8
              change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (63 / 100 : ℝ) * square.center.y + (-3 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_4_negative.le
              ·
                exact branch_9
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_2
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_9_negative : 0 < ((6 / 25 : ℝ) * square.center.x + (-63 / 100 : ℝ) * square.center.y + (3 / 100 : ℝ)) := by linarith only [branch_9]
              apply adjacentR2Right_hit_boundary square fits 31
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (63 / 100 : ℝ)) branch_4_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) branch_9_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (6 / 25 : ℝ)) negative
                have identity : (63 / 100 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) + (37 / 100 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (-63 / 100 : ℝ) * square.center.y + (3 / 100 : ℝ)) + (6 / 25 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (-39 / 1250 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (39 / 1250 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                exact branch_3
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_2
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_3_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [branch_3]
          by_cases branch_10 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ))
          ·
            apply adjacentR2Right_hit_boundary square fits 33
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (1 / 2 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_3_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_10
              have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
              have identity : (1 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-1 / 2 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_2
              have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
              have identity : (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-1 / 2 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_10_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) := by linarith only [branch_10]
            apply adjacentR2Right_hit_boundary square fits 27
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
            refine ⟨?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_10_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
              have identity : (1 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_2
              have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_2_negative : 0 < ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) := by linarith only [branch_2]
        by_cases branch_11 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (51 / 20 : ℝ))
        ·
          apply adjacentR2Right_hit_boundary square fits 11
          change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (51 / 20 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-73 / 100 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_2_negative
            have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
            have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          ·
            exact branch_11
          ·
            exact branch_1
        ·
          have branch_11_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-51 / 20 : ℝ)) := by linarith only [branch_11]
          by_cases branch_12 : 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-31 / 20 : ℝ))
          ·
            by_cases branch_13 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ))
            ·
              apply adjacentR2Right_hit_boundary square fits 22
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-1 / 2 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-31 / 20 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (1 / 2 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) branch_2_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (1 / 2 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_13
              ·
                exact branch_12
            ·
              have branch_13_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) := by linarith only [branch_13]
              apply adjacentR2Right_hit_boundary square fits 42
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_2_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_0
              ·
                exact branch_13_negative.le
          ·
            have branch_12_negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (31 / 20 : ℝ)) := by linarith only [branch_12]
            apply adjacentR2Right_hit_boundary square fits 23
            change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (31 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-51 / 20 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_12_negative.le
            ·
              exact branch_0
            ·
              exact branch_11_negative.le
    ·
      have branch_1_negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) := by linarith only [branch_1]
      by_cases branch_14 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ))
      ·
        by_cases branch_15 : 0 ≤ ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ))
        ·
          by_cases branch_16 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ))
          ·
            apply adjacentR2Right_hit_boundary square fits 26
            change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
            refine ⟨?_ , ?_ ⟩
            ·
              exact branch_16
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_15
              have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_16_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) := by linarith only [branch_16]
            by_cases branch_17 : 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ))
            ·
              by_cases branch_18 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ))
              ·
                apply adjacentR2Right_hit_boundary square fits 32
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_16_negative.le
                ·
                  exact branch_18
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 125 : ℝ)) branch_15
                  have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                  have identity : (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_18_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_18]
                apply adjacentR2Right_hit_boundary square fits 2
                change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1641 / 50000 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_17
                ·
                  exact branch_15
                ·
                  by_contra! failed
                  have negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_15
                  have weighted_1 := mul_pos (by norm_num : 0 < (1591 / 50000 : ℝ)) branch_18_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                  have identity : (13 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (1591 / 50000 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (37 / 100 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_17_negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) := by linarith only [branch_17]
              by_cases branch_19 : 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ))
              ·
                apply adjacentR2Right_hit_boundary square fits 4
                change 0 ≤ ((77 / 500 : ℝ) * square.center.x + (87 / 100 : ℝ) * square.center.y + (-47459 / 50000 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_19
                ·
                  by_contra! failed
                  have negative : 0 < ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (111 / 1250 : ℝ)) branch_1_negative
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (2117 / 5000 : ℝ)) branch_15
                  have weighted_2 := mul_pos (by norm_num : 0 < (1517 / 5000 : ℝ)) negative
                  have identity : (111 / 1250 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) + (2117 / 5000 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (1517 / 5000 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-73 / 100 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  exact branch_17_negative.le
              ·
                have branch_19_negative : 0 < ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ)) := by linarith only [branch_19]
                by_cases branch_20 : 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
                ·
                  apply adjacentR2Right_hit_boundary square fits 30
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-77 / 500 : ℝ) * square.center.x + (-87 / 100 : ℝ) * square.center.y + (47459 / 50000 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_20
                    have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                    have identity : (1 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) branch_1_negative
                    have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_14
                    have weighted_2 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                    have identity : (1 / 2 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) + (1 / 2 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) + (41 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) = (-1517 / 5000 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (1517 / 5000 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    exact branch_19_negative.le
                ·
                  have branch_20_negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [branch_20]
                  apply adjacentR2Right_hit_boundary square fits 32
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_16_negative.le
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_20_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                    have identity : (1 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) = (-5889 / 50000 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (5889 / 50000 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 125 : ℝ)) branch_15
                    have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                    have identity : (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_15_negative : 0 < ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) := by linarith only [branch_15]
          by_cases branch_21 : 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
          ·
            apply adjacentR2Right_hit_boundary square fits 5
            change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1591 / 50000 : ℝ)) branch_1_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (367 / 1000 : ℝ)) branch_15_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (1517 / 5000 : ℝ)) negative
              have identity : (1591 / 50000 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) + (367 / 1000 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (1517 / 5000 : ℝ) * ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_14
            ·
              exact branch_21
          ·
            have branch_21_negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [branch_21]
            by_cases branch_22 : 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-16587 / 25000 : ℝ))
            ·
              apply adjacentR2Right_hit_boundary square fits 9
              change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-16587 / 25000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_14
              ·
                exact branch_22
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) branch_15_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                have identity : (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_22_negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (16587 / 25000 : ℝ)) := by linarith only [branch_22]
              by_cases branch_23 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ))
              ·
                apply adjacentR2Right_hit_boundary square fits 34
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 125 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_15_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (37 / 100 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (37 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) = (-1591 / 50000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (1591 / 50000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_23
                ·
                  by_contra! failed
                  have negative : 0 < ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) branch_21_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                  have identity : (27 / 125 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_23_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_23]
                apply adjacentR2Right_hit_boundary square fits 35
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_23_negative.le
                ·
                  exact branch_0
                ·
                  by_contra! failed
                  have negative : 0 < ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (69 / 100 : ℝ)) branch_21_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                  have identity : (69 / 100 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_14_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) := by linarith only [branch_14]
        apply adjacentR2Right_hit_boundary square fits 10
        change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (73 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ))
        refine ⟨?_ , ?_ , ?_ ⟩
        ·
          exact branch_1_negative.le
        ·
          exact branch_0
        ·
          exact branch_14_negative.le
  ·
    have branch_0_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) := by linarith only [branch_0]
    by_cases branch_24 : 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-63 / 250 : ℝ))
    ·
      by_cases branch_25 : 0 ≤ ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-73 / 40 : ℝ))
      ·
        by_cases branch_26 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ))
        ·
          by_cases branch_27 : 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-12 / 25 : ℝ))
          ·
            by_cases branch_28 : 0 ≤ ((-9 / 20 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (267 / 100 : ℝ))
            ·
              apply adjacentR2Right_hit_boundary square fits 15
              change 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-12 / 25 : ℝ)) ∧ 0 ≤ ((-9 / 20 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (267 / 100 : ℝ)) ∧ 0 ≤ ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-73 / 40 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_27
              ·
                exact branch_28
              ·
                exact branch_25
            ·
              have branch_28_negative : 0 < ((9 / 20 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-267 / 100 : ℝ)) := by linarith only [branch_28]
              by_cases branch_29 : 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (177 / 100 : ℝ))
              ·
                apply adjacentR2Right_hit_boundary square fits 21
                change 0 ≤ ((9 / 20 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-267 / 100 : ℝ)) ∧ 0 ≤ ((-9 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 25 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (177 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_28_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((9 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (9 / 25 : ℝ)) branch_26
                  have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                  have identity : (9 / 25 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((9 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 25 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  exact branch_29
              ·
                have branch_29_negative : 0 < ((9 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-177 / 100 : ℝ)) := by linarith only [branch_29]
                apply adjacentR2Right_hit_boundary square fits 38
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((9 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-177 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_25
                  have weighted_1 := mul_pos (by norm_num : 0 < (73 / 100 : ℝ)) negative
                  have identity : (1 : ℝ) * ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-73 / 40 : ℝ)) + (73 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_26
                  have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                  have identity : (1 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  exact branch_29_negative.le
          ·
            have branch_27_negative : 0 < ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (12 / 25 : ℝ)) := by linarith only [branch_27]
            by_cases branch_30 : 0 ≤ ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-253 / 100 : ℝ))
            ·
              apply adjacentR2Right_hit_boundary square fits 17
              change 0 ≤ ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-253 / 100 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 50 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (12 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_30
              ·
                exact branch_26
              ·
                exact branch_27_negative.le
            ·
              have branch_30_negative : 0 < ((-27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (253 / 100 : ℝ)) := by linarith only [branch_30]
              apply adjacentR2Right_hit_boundary square fits 18
              change 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-17 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (253 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (17 / 100 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_25
                have weighted_1 := mul_pos (by norm_num : 0 < (73 / 200 : ℝ)) branch_27_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (73 / 200 : ℝ)) negative
                have identity : (13 / 100 : ℝ) * ((73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-73 / 40 : ℝ)) + (73 / 200 : ℝ) * ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (12 / 25 : ℝ)) + (73 / 200 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (17 / 100 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_0_negative.le
              ·
                exact branch_30_negative.le
        ·
          have branch_26_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) := by linarith only [branch_26]
          by_cases branch_31 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-66 / 25 : ℝ))
          ·
            by_cases branch_32 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
            ·
              apply adjacentR2Right_hit_boundary square fits 29
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_26_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                have identity : (1 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_32
            ·
              have branch_32_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [branch_32]
              apply adjacentR2Right_hit_boundary square fits 41
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-66 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((9 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_31
              ·
                exact branch_32_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((-9 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (9 / 25 : ℝ)) branch_26_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                have identity : (9 / 25 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ)) + (41 / 50 : ℝ) * ((-9 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_31_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (66 / 25 : ℝ)) := by linarith only [branch_31]
            apply adjacentR2Right_hit_boundary square fits 43
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (66 / 25 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 50 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_0_negative.le
            ·
              exact branch_31_negative.le
            ·
              exact branch_26_negative.le
      ·
        have branch_25_negative : 0 < ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 40 : ℝ)) := by linarith only [branch_25]
        by_cases branch_33 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (59 / 50 : ℝ))
        ·
          by_cases branch_34 : 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (199 / 100 : ℝ))
          ·
            apply adjacentR2Right_hit_boundary square fits 13
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (199 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (37 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_0_negative.le
            ·
              exact branch_34
            ·
              by_contra! failed
              have negative : 0 < ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 100 : ℝ)) branch_24
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (79 / 500 : ℝ)) branch_33
              have weighted_2 := mul_pos (by norm_num : 0 < (8 / 25 : ℝ)) negative
              have identity : (27 / 100 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-63 / 250 : ℝ)) + (79 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (59 / 50 : ℝ)) + (8 / 25 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_34_negative : 0 < ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-199 / 100 : ℝ)) := by linarith only [branch_34]
            by_cases branch_35 : 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-17 / 100 : ℝ))
            ·
              apply adjacentR2Right_hit_boundary square fits 18
              change 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-17 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (253 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_35
              ·
                exact branch_0_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-253 / 100 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (27 / 100 : ℝ)) branch_25_negative
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (73 / 200 : ℝ)) branch_33
                have weighted_2 := mul_pos (by norm_num : 0 < (73 / 200 : ℝ)) negative
                have identity : (27 / 100 : ℝ) * ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 40 : ℝ)) + (73 / 200 : ℝ) * ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (59 / 50 : ℝ)) + (73 / 200 : ℝ) * ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-253 / 100 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_35_negative : 0 < ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (17 / 100 : ℝ)) := by linarith only [branch_35]
              apply adjacentR2Right_hit_boundary square fits 19
              change 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-199 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (17 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_33
                have weighted_1 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (59 / 50 : ℝ)) + (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_34_negative.le
              ·
                exact branch_35_negative.le
        ·
          have branch_33_negative : 0 < ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-59 / 50 : ℝ)) := by linarith only [branch_33]
          by_cases branch_36 : 0 ≤ ((16 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-813 / 250 : ℝ))
          ·
            by_cases branch_37 : 0 ≤ ((9 / 100 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (969 / 500 : ℝ))
            ·
              apply adjacentR2Right_hit_boundary square fits 16
              change 0 ≤ ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 40 : ℝ)) ∧ 0 ≤ ((9 / 100 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (969 / 500 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-813 / 250 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_25_negative.le
              ·
                exact branch_37
              ·
                exact branch_36
            ·
              have branch_37_negative : 0 < ((-9 / 100 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-969 / 500 : ℝ)) := by linarith only [branch_37]
              apply adjacentR2Right_hit_boundary square fits 40
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-969 / 500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (7 / 10 : ℝ)) branch_24
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (3 / 10 : ℝ)) branch_36
                have weighted_2 := mul_pos (by norm_num : 0 < (16 / 25 : ℝ)) negative
                have identity : (7 / 10 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-63 / 250 : ℝ)) + (3 / 10 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-813 / 250 : ℝ)) + (16 / 25 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                by_contra! failed
                have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_25_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (73 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((-73 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (73 / 40 : ℝ)) + (73 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_37_negative.le
          ·
            have branch_36_negative : 0 < ((-16 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (813 / 250 : ℝ)) := by linarith only [branch_36]
            apply adjacentR2Right_hit_boundary square fits 20
            change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (813 / 250 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-63 / 250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_36_negative.le
            ·
              exact branch_24
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_33_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-59 / 50 : ℝ)) + (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
    ·
      have branch_24_negative : 0 < ((-16 / 25 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (63 / 250 : ℝ)) := by linarith only [branch_24]
      by_cases branch_38 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (59 / 50 : ℝ))
      ·
        by_cases branch_39 : 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
        ·
          by_cases branch_40 : 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (37 / 100 : ℝ))
          ·
            apply adjacentR2Right_hit_boundary square fits 13
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (199 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (37 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_0_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-199 / 100 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (27 / 100 : ℝ)) branch_24_negative
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (241 / 500 : ℝ)) branch_38
              have weighted_2 := mul_pos (by norm_num : 0 < (8 / 25 : ℝ)) negative
              have identity : (27 / 100 : ℝ) * ((-16 / 25 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (63 / 250 : ℝ)) + (241 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (59 / 50 : ℝ)) + (8 / 25 : ℝ) * ((27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-199 / 100 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_40
          ·
            have branch_40_negative : 0 < ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) := by linarith only [branch_40]
            apply adjacentR2Right_hit_boundary square fits 14
            change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (59 / 50 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 50 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_40_negative.le
            ·
              exact branch_38
            ·
              by_contra! failed
              have negative : 0 < ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 50 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 50 : ℝ)) branch_39
              have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
              have identity : (27 / 50 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 50 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_39_negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [branch_39]
          apply adjacentR2Right_hit_boundary square fits 36
          change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 50 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_0_negative.le
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_38
            have weighted_1 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
            have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (59 / 50 : ℝ)) + (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          ·
            by_contra! failed
            have negative : 0 < ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 50 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_pos (by norm_num : 0 < (27 / 50 : ℝ)) branch_39_negative
            have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
            have identity : (27 / 50 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 50 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_38_negative : 0 < ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-59 / 50 : ℝ)) := by linarith only [branch_38]
        by_cases branch_41 : 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 50 : ℝ))
        ·
          by_cases branch_42 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
          ·
            apply adjacentR2Right_hit_boundary square fits 37
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-59 / 25 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (16 / 25 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_38_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-59 / 50 : ℝ)) + (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (59 / 25 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_42
              have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              by_contra! failed
              have negative : 0 < ((16 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-16 / 25 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (16 / 25 : ℝ)) branch_41
              have weighted_1 := mul_pos (by norm_num : 0 < (27 / 50 : ℝ)) negative
              have identity : (16 / 25 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 50 : ℝ)) + (27 / 50 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-16 / 25 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_42_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_42]
            apply adjacentR2Right_hit_boundary square fits 28
            change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
            refine ⟨?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_41
              have weighted_1 := mul_pos (by norm_num : 0 < (27 / 50 : ℝ)) negative
              have identity : (1 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 50 : ℝ)) + (27 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_42_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_41_negative : 0 < ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 50 : ℝ)) := by linarith only [branch_41]
          by_cases branch_43 : 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (107 / 50 : ℝ))
          ·
            apply adjacentR2Right_hit_boundary square fits 24
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-59 / 50 : ℝ)) ∧ 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (107 / 50 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-16 / 25 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_38_negative.le
            ·
              exact branch_43
            ·
              by_contra! failed
              have negative : 0 < ((-16 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (16 / 25 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (16 / 25 : ℝ)) branch_41_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (27 / 50 : ℝ)) negative
              have identity : (16 / 25 : ℝ) * ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 50 : ℝ)) + (27 / 50 : ℝ) * ((-16 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (16 / 25 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_43_negative : 0 < ((16 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-107 / 50 : ℝ)) := by linarith only [branch_43]
            by_cases branch_44 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
            ·
              apply adjacentR2Right_hit_boundary square fits 25
              change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (63 / 250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-107 / 50 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_24_negative.le
              ·
                exact branch_44
              ·
                exact branch_43_negative.le
            ·
              have branch_44_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_44]
              by_cases branch_45 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 5 : ℝ))
              ·
                apply adjacentR2Right_hit_boundary square fits 39
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_41_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (27 / 50 : ℝ)) negative
                  have identity : (1 : ℝ) * ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 50 : ℝ)) + (27 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  exact branch_45
                ·
                  exact branch_44_negative.le
              ·
                have branch_45_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 5 : ℝ)) := by linarith only [branch_45]
                apply adjacentR2Right_hit_boundary square fits 40
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((-9 / 100 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-969 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_45_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 10 : ℝ)) container_3
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_24_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (16 / 25 : ℝ)) negative
                  have identity : (3 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (4 : ℝ)) + (1 : ℝ) * ((-16 / 25 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (63 / 250 : ℝ)) + (16 / 25 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) = (-37 / 250 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (37 / 250 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((9 / 100 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (969 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (9 / 125 : ℝ)) branch_24_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (421 / 1000 : ℝ)) branch_44_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (64 / 125 : ℝ)) negative
                  have identity : (9 / 125 : ℝ) * ((-16 / 25 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (63 / 250 : ℝ)) + (421 / 1000 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (64 / 125 : ℝ) * ((9 / 100 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (969 / 500 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]

end SquarePackingArchive.BentzThirteen
