import SquarePackingArchive.BentzAdjacentR4Geometry

namespace SquarePackingArchive.BentzThirteen

set_option maxHeartbeats 4000000 in
theorem adjacentR4_unavoidable : ∀ square : PlacedSquare, square.Fits 4 → adjacentR4Outcome square := by
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
  by_cases branch_0 : 0 ≤ ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ))
  ·
    by_cases branch_1 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ))
    ·
      by_cases branch_2 : 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ))
      ·
        by_cases branch_3 : 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-632 / 625 : ℝ))
        ·
          apply adjacentR4_hit_boundary square fits 3
          change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_3
          ·
            exact branch_2
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (61 / 100 : ℝ)) branch_0
            have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
            have identity : (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_3_negative : 0 < ((-6 / 25 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (632 / 625 : ℝ)) := by linarith only [branch_3]
          by_cases branch_4 : 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ))
          ·
            by_cases branch_5 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ))
            ·
              apply adjacentR4_hit_boundary square fits 29
              change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                exact branch_5
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_0
                have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_5_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) := by linarith only [branch_5]
              by_cases branch_6 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ))
              ·
                by_cases branch_7 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ))
                ·
                  by_cases branch_8 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 5 : ℝ))
                  ·
                    apply adjacentR4_hit_boundary square fits 41
                    change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-47 / 100 : ℝ) * square.center.y + (403 / 500 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      exact branch_8
                    ·
                      exact branch_7
                    ·
                      by_contra! failed
                      have negative : 0 < ((6 / 25 : ℝ) * square.center.x + (47 / 100 : ℝ) * square.center.y + (-403 / 500 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (81 / 1250 : ℝ)) branch_2
                      have weighted_1 := mul_pos (by norm_num : 0 < (51 / 625 : ℝ)) branch_3_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (183 / 1250 : ℝ)) negative
                      have identity : (81 / 1250 : ℝ) * ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ)) + (51 / 625 : ℝ) * ((-6 / 25 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (632 / 625 : ℝ)) + (183 / 1250 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (47 / 100 : ℝ) * square.center.y + (-403 / 500 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                  ·
                    have branch_8_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 5 : ℝ)) := by linarith only [branch_8]
                    apply adjacentR4_hit_boundary square fits 39
                    change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      exact branch_6
                    ·
                      by_contra! failed
                      have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_8_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                      have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 5 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) = (-1 / 10 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (1 / 10 : ℝ))
                      nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                    ·
                      exact branch_4
                ·
                  have branch_7_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) := by linarith only [branch_7]
                  apply adjacentR4_hit_boundary square fits 42
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_7_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (-13 / 100 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_1
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_0
                    have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                    have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_6_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [branch_6]
                apply adjacentR4_hit_boundary square fits 43
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_5_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_6_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (1 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) = (-13 / 100 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (13 / 100 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 125 : ℝ)) branch_0
                  have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                  have identity : (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_4_negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) := by linarith only [branch_4]
            by_cases branch_9 : 0 ≤ ((43 / 500 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1641 / 50000 : ℝ))
            ·
              apply adjacentR4_hit_boundary square fits 2
              change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-41151 / 250000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_4_negative.le
              ·
                exact branch_0
              ·
                by_contra! failed
                have negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (41151 / 250000 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1161 / 62500 : ℝ)) branch_4_negative
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (12599 / 250000 : ℝ)) branch_9
                have weighted_2 := mul_pos (by norm_num : 0 < (1591 / 50000 : ℝ)) negative
                have identity : (1161 / 62500 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) + (12599 / 250000 : ℝ) * ((43 / 500 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1641 / 50000 : ℝ)) + (1591 / 50000 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (41151 / 250000 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_9_negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) := by linarith only [branch_9]
              by_cases branch_10 : 0 ≤ ((43 / 500 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-41151 / 250000 : ℝ))
              ·
                apply adjacentR4_hit_boundary square fits 2
                change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) ∧ 0 ≤ ((43 / 500 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (-41151 / 250000 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_4_negative.le
                ·
                  exact branch_0
                ·
                  exact branch_10
              ·
                have branch_10_negative : 0 < ((-43 / 500 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (41151 / 250000 : ℝ)) := by linarith only [branch_10]
                by_cases branch_11 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ))
                ·
                  apply adjacentR4_hit_boundary square fits 29
                  change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
                  refine ⟨?_ , ?_ ⟩
                  ·
                    exact branch_11
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_0
                    have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                ·
                  have branch_11_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) := by linarith only [branch_11]
                  apply adjacentR4_hit_boundary square fits 43
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-27 / 125 : ℝ) * square.center.y + (27 / 125 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_11_negative.le
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_0
                    have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) branch_9_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (12599 / 250000 : ℝ)) negative
                    have identity : (13 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((-43 / 500 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) + (12599 / 250000 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 125 : ℝ)) branch_0
                    have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                    have identity : (27 / 125 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (27 / 125 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_2_negative : 0 < ((6 / 25 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1369 / 2500 : ℝ)) := by linarith only [branch_2]
        apply adjacentR4_hit_boundary square fits 42
        change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-87 / 50 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ))
        refine ⟨?_ , ?_ , ?_ ⟩
        ·
          by_contra! failed
          have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) := by linarith only [failed]
          have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_0
          have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) branch_2_negative
          have weighted_2 := mul_pos (by norm_num : 0 < (879 / 6250 : ℝ)) negative
          have identity : (13 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1369 / 2500 : ℝ)) + (879 / 6250 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (87 / 50 : ℝ)) = (0 : ℝ) := by
            ring
          nlinarith only [weighted_0, weighted_1, weighted_2, identity]
        ·
          exact branch_1
        ·
          by_contra! failed
          have negative : 0 < ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) := by linarith only [failed]
          have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (19 / 25 : ℝ)) branch_0
          have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
          have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) = (0 : ℝ) := by
            ring
          nlinarith only [weighted_0, weighted_1, identity]
    ·
      have branch_1_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [branch_1]
      by_cases branch_12 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ))
      ·
        apply adjacentR4_hit_boundary square fits 44
        change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (3 / 5 : ℝ))
        refine ⟨?_ , ?_ , ?_ ⟩
        ·
          exact branch_1_negative.le
        ·
          exact branch_12
        ·
          by_contra! failed
          have negative : 0 < ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-3 / 5 : ℝ)) := by linarith only [failed]
          have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 5 : ℝ)) branch_0
          have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
          have identity : (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-3 / 5 : ℝ)) = (0 : ℝ) := by
            ring
          nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_12_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [branch_12]
        apply adjacentR4_hit_boundary square fits 33
        change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
        refine ⟨?_ , ?_ ⟩
        ·
          exact branch_12_negative.le
        ·
          by_contra! failed
          have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
          have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_0
          have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
          have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-293 / 500 : ℝ) * square.center.y + (293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
            ring
          nlinarith only [weighted_0, weighted_1, identity]
  ·
    have branch_0_negative : 0 < ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) := by linarith only [branch_0]
    by_cases branch_13 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 100 : ℝ))
    ·
      by_cases branch_14 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (91 / 100 : ℝ))
      ·
        by_cases branch_15 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ))
        ·
          by_cases branch_16 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ))
          ·
            by_cases branch_17 : 0 ≤ ((13 / 100 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-1641 / 50000 : ℝ))
            ·
              by_cases branch_18 : 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-632 / 625 : ℝ))
              ·
                by_cases branch_19 : 0 ≤ ((83 / 100 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-2753 / 2500 : ℝ))
                ·
                  by_cases branch_20 : 0 ≤ ((13 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-139 / 200 : ℝ))
                  ·
                    apply adjacentR4_hit_boundary square fits 6
                    change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 100 : ℝ)) ∧ 0 ≤ ((69 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-1 / 8 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-139 / 200 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      exact branch_13
                    ·
                      by_contra! failed
                      have negative : 0 < ((-69 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (1 / 8 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (283 / 50000 : ℝ)) branch_15
                      have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (69 / 100 : ℝ)) branch_17
                      have weighted_2 := mul_pos (by norm_num : 0 < (13 / 100 : ℝ)) negative
                      have identity : (283 / 50000 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (69 / 100 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) + (13 / 100 : ℝ) * ((-69 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (1 / 8 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                    ·
                      exact branch_20
                  ·
                    have branch_20_negative : 0 < ((-13 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (139 / 200 : ℝ)) := by linarith only [branch_20]
                    apply adjacentR4_hit_boundary square fits 7
                    change 0 ≤ ((-13 / 100 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (4831 / 5000 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (413 / 500 : ℝ) * square.center.y + (-413 / 500 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((13 / 100 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-4831 / 5000 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (39 / 1250 : ℝ)) branch_15
                      have weighted_1 := mul_pos (by norm_num : 0 < (13 / 100 : ℝ)) branch_20_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (13 / 100 : ℝ)) negative
                      have identity : (39 / 1250 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (13 / 100 : ℝ) * ((-13 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (139 / 200 : ℝ)) + (13 / 100 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-4831 / 5000 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                    ·
                      exact branch_17
                    ·
                      by_contra! failed
                      have negative : 0 < ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (413 / 500 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) branch_0_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                      have identity : (413 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (413 / 500 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, identity]
                ·
                  have branch_19_negative : 0 < ((-83 / 100 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (2753 / 2500 : ℝ)) := by linarith only [branch_19]
                  apply adjacentR4_hit_boundary square fits 7
                  change 0 ≤ ((-13 / 100 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (4831 / 5000 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (413 / 500 : ℝ) * square.center.y + (-413 / 500 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((13 / 100 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-4831 / 5000 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (583 / 1000 : ℝ)) branch_15
                    have weighted_1 := mul_pos (by norm_num : 0 < (13 / 100 : ℝ)) branch_19_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (83 / 100 : ℝ)) negative
                    have identity : (583 / 1000 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (13 / 100 : ℝ) * ((-83 / 100 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (2753 / 2500 : ℝ)) + (83 / 100 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-4831 / 5000 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                  ·
                    exact branch_17
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (413 / 500 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) branch_0_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                    have identity : (413 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (413 / 500 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_18_negative : 0 < ((-6 / 25 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (632 / 625 : ℝ)) := by linarith only [branch_18]
                apply adjacentR4_hit_boundary square fits 7
                change 0 ≤ ((-13 / 100 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (4831 / 5000 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (413 / 500 : ℝ) * square.center.y + (-413 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((13 / 100 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-4831 / 5000 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (407 / 5000 : ℝ)) branch_15
                  have weighted_1 := mul_pos (by norm_num : 0 < (13 / 100 : ℝ)) branch_18_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (6 / 25 : ℝ)) negative
                  have identity : (407 / 5000 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (13 / 100 : ℝ) * ((-6 / 25 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (632 / 625 : ℝ)) + (6 / 25 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-4831 / 5000 : ℝ)) = (-169 / 20000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (169 / 20000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_17
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (413 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) branch_0_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                  have identity : (413 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (413 / 500 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_17_negative : 0 < ((-13 / 100 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (1641 / 50000 : ℝ)) := by linarith only [branch_17]
              apply adjacentR4_hit_boundary square fits 45
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 125 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) = (-12599 / 250000 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (12599 / 250000 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                exact branch_15
              ·
                by_contra! failed
                have negative : 0 < ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1161 / 62500 : ℝ)) branch_15
                have weighted_1 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) branch_17_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (13 / 100 : ℝ)) negative
                have identity : (1161 / 62500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (27 / 125 : ℝ) * ((-13 / 100 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (1641 / 50000 : ℝ)) + (13 / 100 : ℝ) * ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_16_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_16]
            by_cases branch_21 : 0 ≤ ((13 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-139 / 200 : ℝ))
            ·
              apply adjacentR4_hit_boundary square fits 6
              change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 100 : ℝ)) ∧ 0 ≤ ((69 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-1 / 8 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-139 / 200 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_13
              ·
                by_contra! failed
                have negative : 0 < ((-69 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (1 / 8 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_15
                have weighted_1 := mul_pos (by norm_num : 0 < (69 / 100 : ℝ)) branch_16_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (69 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (1 : ℝ) * ((-69 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (1 / 8 : ℝ)) = (-897 / 10000 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (897 / 10000 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                exact branch_21
            ·
              have branch_21_negative : 0 < ((-13 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (139 / 200 : ℝ)) := by linarith only [branch_21]
              apply adjacentR4_hit_boundary square fits 7
              change 0 ≤ ((-13 / 100 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (4831 / 5000 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (-43 / 500 : ℝ) * square.center.y + (-1641 / 50000 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (413 / 500 : ℝ) * square.center.y + (-413 / 500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((13 / 100 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-4831 / 5000 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (39 / 1250 : ℝ)) branch_15
                have weighted_1 := mul_pos (by norm_num : 0 < (13 / 100 : ℝ)) branch_21_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (13 / 100 : ℝ)) negative
                have identity : (39 / 1250 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (13 / 100 : ℝ) * ((-13 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (139 / 200 : ℝ)) + (13 / 100 : ℝ) * ((13 / 100 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-4831 / 5000 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                by_contra! failed
                have negative : 0 < ((-13 / 100 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (1641 / 50000 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (43 / 500 : ℝ)) branch_15
                have weighted_1 := mul_pos (by norm_num : 0 < (13 / 100 : ℝ)) branch_16_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (43 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (13 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (1 : ℝ) * ((-13 / 100 : ℝ) * square.center.x + (43 / 500 : ℝ) * square.center.y + (1641 / 50000 : ℝ)) = (-169 / 10000 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (169 / 10000 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (413 / 500 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (413 / 500 : ℝ)) branch_0_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                have identity : (413 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-413 / 500 : ℝ) * square.center.y + (413 / 500 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_15_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_15]
          by_cases branch_22 : 0 ≤ ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ))
          ·
            by_cases branch_23 : 0 ≤ ((69 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-1 / 8 : ℝ))
            ·
              apply adjacentR4_hit_boundary square fits 6
              change 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 100 : ℝ)) ∧ 0 ≤ ((69 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (-1 / 8 : ℝ)) ∧ 0 ≤ ((13 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-139 / 200 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_13
              ·
                exact branch_23
              ·
                by_contra! failed
                have negative : 0 < ((-13 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (139 / 200 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (69 / 200 : ℝ)) branch_15_negative
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_22
                have weighted_2 := mul_pos (by norm_num : 0 < (69 / 100 : ℝ)) negative
                have identity : (69 / 200 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (13 / 100 : ℝ) * ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) + (69 / 100 : ℝ) * ((-13 / 100 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (139 / 200 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_23_negative : 0 < ((-69 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (1 / 8 : ℝ)) := by linarith only [branch_23]
              apply adjacentR4_hit_boundary square fits 10
              change 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (1 / 8 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (91 / 100 : ℝ)) ∧ 0 ≤ ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_23_negative.le
              ·
                exact branch_14
              ·
                exact branch_22
          ·
            have branch_22_negative : 0 < ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ)) := by linarith only [branch_22]
            apply adjacentR4_hit_boundary square fits 46
            change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_15_negative.le
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_14
              have weighted_1 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
              have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (91 / 100 : ℝ)) + (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_22_negative.le
      ·
        have branch_14_negative : 0 < ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-91 / 100 : ℝ)) := by linarith only [branch_14]
        by_cases branch_24 : 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (37 / 100 : ℝ))
        ·
          apply adjacentR4_hit_boundary square fits 13
          change 0 ≤ ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-91 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (81 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (37 / 100 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_14_negative.le
          ·
            by_contra! failed
            have negative : 0 < ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-81 / 100 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 50 : ℝ)) branch_13
            have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
            have identity : (27 / 50 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 100 : ℝ)) + (41 / 50 : ℝ) * ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-81 / 100 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
          ·
            exact branch_24
        ·
          have branch_24_negative : 0 < ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) := by linarith only [branch_24]
          by_cases branch_25 : 0 ≤ ((13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (79 / 100 : ℝ))
          ·
            by_cases branch_26 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (111 / 100 : ℝ))
            ·
              apply adjacentR4_hit_boundary square fits 30
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-41 / 100 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (111 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-161 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (231 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (41 / 100 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) branch_14_negative
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_25
                have weighted_2 := mul_pos (by norm_num : 0 < (13 / 100 : ℝ)) negative
                have identity : (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-91 / 100 : ℝ)) + (1 / 2 : ℝ) * ((13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (79 / 100 : ℝ)) + (13 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (41 / 100 : ℝ)) = (-67 / 10000 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (67 / 10000 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                exact branch_26
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (161 / 100 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_14_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-91 / 100 : ℝ)) + (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (161 / 100 : ℝ)) = (-21 / 200 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (21 / 200 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-231 / 100 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_25
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (13 / 50 : ℝ)) branch_26
                have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                have identity : (1 : ℝ) * ((13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (79 / 100 : ℝ)) + (13 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (111 / 100 : ℝ)) + (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-231 / 100 : ℝ)) = (-191 / 2500 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (191 / 2500 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
            ·
              have branch_26_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-111 / 100 : ℝ)) := by linarith only [branch_26]
              apply adjacentR4_hit_boundary square fits 14
              change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) ∧ 0 ≤ ((13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (79 / 100 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_24_negative.le
              ·
                exact branch_25
              ·
                by_contra! failed
                have negative : 0 < ((-7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (7 / 25 : ℝ)) branch_26_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (7 / 25 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-111 / 100 : ℝ)) + (1 : ℝ) * ((-7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 25 : ℝ)) = (-77 / 2500 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (77 / 2500 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
          ·
            have branch_25_negative : 0 < ((-13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-79 / 100 : ℝ)) := by linarith only [branch_25]
            by_cases branch_27 : 0 ≤ ((7 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (957 / 500 : ℝ))
            ·
              by_cases branch_28 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (111 / 100 : ℝ))
              ·
                by_cases branch_29 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ))
                ·
                  apply adjacentR4_hit_boundary square fits 47
                  change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ)) ∧ 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 25 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_14_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-91 / 100 : ℝ)) + (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    exact branch_29
                  ·
                    by_contra! failed
                    have negative : 0 < ((7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 25 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (7 / 25 : ℝ)) branch_25_negative
                    have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (7 / 50 : ℝ)) branch_29
                    have weighted_2 := mul_pos (by norm_num : 0 < (13 / 50 : ℝ)) negative
                    have identity : (7 / 25 : ℝ) * ((-13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-79 / 100 : ℝ)) + (7 / 50 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ)) + (13 / 50 : ℝ) * ((7 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 25 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  have branch_29_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-21 / 10 : ℝ)) := by linarith only [branch_29]
                  by_cases branch_30 : 0 ≤ ((9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (-111 / 100 : ℝ))
                  ·
                    apply adjacentR4_hit_boundary square fits 17
                    change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (297 / 125 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (-111 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-79 / 100 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-297 / 125 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (33 / 50 : ℝ)) branch_13
                      have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (123 / 250 : ℝ)) branch_27
                      have weighted_2 := mul_pos (by norm_num : 0 < (369 / 500 : ℝ)) negative
                      have identity : (33 / 50 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 100 : ℝ)) + (123 / 250 : ℝ) * ((7 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (957 / 500 : ℝ)) + (369 / 500 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-297 / 125 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                    ·
                      exact branch_30
                    ·
                      exact branch_25_negative.le
                  ·
                    have branch_30_negative : 0 < ((-9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (111 / 100 : ℝ)) := by linarith only [branch_30]
                    apply adjacentR4_hit_boundary square fits 48
                    change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-21 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (111 / 100 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      exact branch_29_negative.le
                    ·
                      by_contra! failed
                      have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (7 / 50 : ℝ)) container_1
                      have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_27
                      have weighted_2 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                      have identity : (7 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 : ℝ) * ((7 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (957 / 500 : ℝ)) + (9 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (-113 / 500 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (113 / 500 : ℝ))
                      nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                    ·
                      exact branch_30_negative.le
              ·
                have branch_28_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-111 / 100 : ℝ)) := by linarith only [branch_28]
                apply adjacentR4_hit_boundary square fits 17
                change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (297 / 125 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (-111 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-79 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-297 / 125 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (33 / 50 : ℝ)) branch_13
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (123 / 250 : ℝ)) branch_27
                  have weighted_2 := mul_pos (by norm_num : 0 < (369 / 500 : ℝ)) negative
                  have identity : (33 / 50 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 100 : ℝ)) + (123 / 250 : ℝ) * ((7 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (957 / 500 : ℝ)) + (369 / 500 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-297 / 125 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((-9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (111 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 / 10 : ℝ)) branch_14_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (9 / 20 : ℝ)) branch_28_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                  have identity : (1 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-91 / 100 : ℝ)) + (9 / 20 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-111 / 100 : ℝ)) + (1 / 2 : ℝ) * ((-9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (111 / 100 : ℝ)) = (-71 / 2000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (71 / 2000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_25_negative.le
            ·
              have branch_27_negative : 0 < ((-7 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-957 / 500 : ℝ)) := by linarith only [branch_27]
              by_cases branch_31 : 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (297 / 125 : ℝ))
              ·
                by_cases branch_32 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 4 : ℝ))
                ·
                  by_cases branch_33 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
                  ·
                    by_cases branch_34 : 0 ≤ ((9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (-111 / 100 : ℝ))
                    ·
                      apply adjacentR4_hit_boundary square fits 17
                      change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (297 / 125 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (-111 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-79 / 100 : ℝ))
                      refine ⟨?_ , ?_ , ?_ ⟩
                      ·
                        exact branch_31
                      ·
                        exact branch_34
                      ·
                        exact branch_25_negative.le
                    ·
                      have branch_34_negative : 0 < ((-9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (111 / 100 : ℝ)) := by linarith only [branch_34]
                      apply adjacentR4_hit_boundary square fits 48
                      change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-21 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (111 / 100 : ℝ))
                      refine ⟨?_ , ?_ , ?_ ⟩
                      ·
                        by_contra! failed
                        have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ)) := by linarith only [failed]
                        have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (7 / 50 : ℝ)) container_0
                        have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_27_negative
                        have weighted_2 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                        have identity : (7 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (0 : ℝ)) + (1 : ℝ) * ((-7 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-957 / 500 : ℝ)) + (9 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ)) = (-3 / 125 : ℝ) := by
                          ring
                        have constant_negative := (by norm_num : 0 < (3 / 125 : ℝ))
                        nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                      ·
                        by_contra! failed
                        have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                        have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_33
                        have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                        have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                          ring
                        nlinarith only [weighted_0, weighted_1, identity]
                      ·
                        exact branch_34_negative.le
                  ·
                    have branch_33_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_33]
                    apply adjacentR4_hit_boundary square fits 36
                    change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
                    refine ⟨?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (4 / 5 : ℝ)) branch_31
                      have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_33_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (64 / 125 : ℝ)) negative
                      have identity : (4 / 5 : ℝ) * ((-16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (297 / 125 : ℝ)) + (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (64 / 125 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                    ·
                      by_contra! failed
                      have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_33_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                      have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, identity]
                ·
                  have branch_32_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 4 : ℝ)) := by linarith only [branch_32]
                  apply adjacentR4_hit_boundary square fits 17
                  change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (297 / 125 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (-111 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-79 / 100 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_31
                  ·
                    by_contra! failed
                    have negative : 0 < ((-9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (111 / 100 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 10 : ℝ)) container_2
                    have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) branch_32_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + (9 / 10 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 4 : ℝ)) + (1 : ℝ) * ((-9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (111 / 100 : ℝ)) = (-3 / 200 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (3 / 200 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    exact branch_25_negative.le
              ·
                have branch_31_negative : 0 < ((16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-297 / 125 : ℝ)) := by linarith only [branch_31]
                by_cases branch_35 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-53 / 20 : ℝ))
                ·
                  by_cases branch_36 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
                  ·
                    apply adjacentR4_hit_boundary square fits 21
                    change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (61 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-297 / 125 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-61 / 125 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (53 / 250 : ℝ)) branch_13
                      have weighted_1 := mul_pos (by norm_num : 0 < (41 / 250 : ℝ)) branch_24_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (41 / 100 : ℝ)) negative
                      have identity : (53 / 250 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 100 : ℝ)) + (41 / 250 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (41 / 100 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-61 / 125 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                    ·
                      exact branch_36
                    ·
                      exact branch_31_negative.le
                  ·
                    have branch_36_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_36]
                    by_cases branch_37 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ))
                    ·
                      apply adjacentR4_hit_boundary square fits 36
                      change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
                      refine ⟨?_ , ?_ ⟩
                      ·
                        exact branch_37
                      ·
                        by_contra! failed
                        have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                        have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_36_negative
                        have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                        have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                          ring
                        nlinarith only [weighted_0, weighted_1, identity]
                    ·
                      have branch_37_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) := by linarith only [branch_37]
                      apply adjacentR4_hit_boundary square fits 49
                      change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (17 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
                      refine ⟨?_ , ?_ , ?_ ⟩
                      ·
                        exact branch_37_negative.le
                      ·
                        by_contra! failed
                        have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-17 / 10 : ℝ)) := by linarith only [failed]
                        have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_13
                        have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                        have identity : (1 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 100 : ℝ)) + (41 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-17 / 10 : ℝ)) = (-41 / 250 : ℝ) := by
                          ring
                        have constant_negative := (by norm_num : 0 < (41 / 250 : ℝ))
                        nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                      ·
                        exact branch_36_negative.le
                ·
                  have branch_35_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (53 / 20 : ℝ)) := by linarith only [branch_35]
                  apply adjacentR4_hit_boundary square fits 21
                  change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (61 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-297 / 125 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-61 / 125 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (53 / 250 : ℝ)) branch_13
                    have weighted_1 := mul_pos (by norm_num : 0 < (41 / 250 : ℝ)) branch_24_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (41 / 100 : ℝ)) negative
                    have identity : (53 / 250 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (123 / 100 : ℝ)) + (41 / 250 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-37 / 100 : ℝ)) + (41 / 100 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-61 / 125 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) branch_35_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (53 / 20 : ℝ)) + (1 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) = (-7 / 25 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (7 / 25 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_31_negative.le
    ·
      have branch_13_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 100 : ℝ)) := by linarith only [branch_13]
      by_cases branch_38 : 0 ≤ ((-11 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (246 / 125 : ℝ))
      ·
        by_cases branch_39 : 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (48 / 125 : ℝ))
        ·
          by_cases branch_40 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (4167 / 2500 : ℝ))
          ·
            apply adjacentR4_hit_boundary square fits 4
            change 0 ≤ ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-6 / 25 : ℝ) * square.center.y + (4167 / 2500 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-37 / 100 : ℝ) * square.center.y + (-2783 / 5000 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) branch_0_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
              have identity : (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_40
            ·
              by_contra! failed
              have negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (2783 / 5000 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (4097 / 5000 : ℝ)) branch_13_negative
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1517 / 5000 : ℝ)) branch_38
              have weighted_2 := mul_pos (by norm_num : 0 < (369 / 500 : ℝ)) negative
              have identity : (4097 / 5000 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 100 : ℝ)) + (1517 / 5000 : ℝ) * ((-11 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (246 / 125 : ℝ)) + (369 / 500 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (37 / 100 : ℝ) * square.center.y + (2783 / 5000 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_40_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-4167 / 2500 : ℝ)) := by linarith only [branch_40]
            apply adjacentR4_hit_boundary square fits 8
            change 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (33 / 50 : ℝ) * square.center.y + (48 / 125 : ℝ)) ∧ 0 ≤ ((-11 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (246 / 125 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (6 / 25 : ℝ) * square.center.y + (-4167 / 2500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_39
            ·
              exact branch_38
            ·
              exact branch_40_negative.le
        ·
          have branch_39_negative : 0 < ((3 / 5 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (-48 / 125 : ℝ)) := by linarith only [branch_39]
          by_cases branch_41 : 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (8 / 5 : ℝ))
          ·
            apply adjacentR4_hit_boundary square fits 9
            change 0 ≤ ((0 : ℝ) * square.center.x + (19 / 25 : ℝ) * square.center.y + (-19 / 25 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (8 / 5 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (-48 / 125 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (19 / 25 : ℝ)) branch_0_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
              have identity : (19 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-19 / 25 : ℝ) * square.center.y + (19 / 25 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_41
            ·
              exact branch_39_negative.le
          ·
            have branch_41_negative : 0 < ((3 / 5 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (-8 / 5 : ℝ)) := by linarith only [branch_41]
            by_cases branch_42 : 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (64 / 25 : ℝ))
            ·
              apply adjacentR4_hit_boundary square fits 23
              change 0 ≤ ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-3 / 5 : ℝ)) ∧ 0 ≤ ((-3 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (64 / 25 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (-8 / 5 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (3 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_0_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                have identity : (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (3 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_42
              ·
                exact branch_41_negative.le
            ·
              have branch_42_negative : 0 < ((3 / 5 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-64 / 25 : ℝ)) := by linarith only [branch_42]
              by_cases branch_43 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ))
              ·
                apply adjacentR4_hit_boundary square fits 24
                change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (4 / 25 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-64 / 25 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_43
                ·
                  by_contra! failed
                  have negative : 0 < ((-2 / 5 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-4 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (39 / 250 : ℝ)) branch_38
                  have weighted_1 := mul_pos (by norm_num : 0 < (257 / 500 : ℝ)) branch_39_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (1713 / 2500 : ℝ)) negative
                  have identity : (39 / 250 : ℝ) * ((-11 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (246 / 125 : ℝ)) + (257 / 500 : ℝ) * ((3 / 5 : ℝ) * square.center.x + (-33 / 50 : ℝ) * square.center.y + (-48 / 125 : ℝ)) + (1713 / 2500 : ℝ) * ((-2 / 5 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-4 / 25 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  exact branch_42_negative.le
              ·
                have branch_43_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [branch_43]
                apply adjacentR4_hit_boundary square fits 52
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (11 / 50 : ℝ)) branch_13_negative
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (41 / 50 : ℝ)) branch_38
                  have weighted_2 := mul_pos (by norm_num : 0 < (369 / 500 : ℝ)) negative
                  have identity : (11 / 50 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 100 : ℝ)) + (41 / 50 : ℝ) * ((-11 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (246 / 125 : ℝ)) + (369 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) = (-3321 / 25000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (3321 / 25000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_43_negative.le
      ·
        have branch_38_negative : 0 < ((11 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-246 / 125 : ℝ)) := by linarith only [branch_38]
        by_cases branch_44 : 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (54 / 25 : ℝ))
        ·
          by_cases branch_45 : 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (157 / 100 : ℝ))
          ·
            by_cases branch_46 : 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-49 / 100 : ℝ))
            ·
              apply adjacentR4_hit_boundary square fits 15
              change 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-49 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (157 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-81 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_46
              ·
                exact branch_45
              ·
                by_contra! failed
                have negative : 0 < ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (81 / 100 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (27 / 50 : ℝ)) branch_13_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                have identity : (27 / 50 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 100 : ℝ)) + (41 / 50 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (81 / 100 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_46_negative : 0 < ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (49 / 100 : ℝ)) := by linarith only [branch_46]
              by_cases branch_47 : 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (46 / 25 : ℝ))
              ·
                apply adjacentR4_hit_boundary square fits 16
                change 0 ≤ ((11 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-246 / 125 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (46 / 25 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (49 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_38_negative.le
                ·
                  exact branch_47
                ·
                  exact branch_46_negative.le
              ·
                have branch_47_negative : 0 < ((1 / 2 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-46 / 25 : ℝ)) := by linarith only [branch_47]
                apply adjacentR4_hit_boundary square fits 22
                change 0 ≤ ((1 / 2 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-46 / 25 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (54 / 25 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (1 / 25 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_47_negative.le
                ·
                  exact branch_44
                ·
                  by_contra! failed
                  have negative : 0 < ((-2 / 5 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-1 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (9 / 25 : ℝ)) branch_45
                  have weighted_1 := mul_pos (by norm_num : 0 < (38 / 125 : ℝ)) branch_47_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (73 / 500 : ℝ)) negative
                  have identity : (9 / 25 : ℝ) * ((-13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (157 / 100 : ℝ)) + (38 / 125 : ℝ) * ((1 / 2 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-46 / 25 : ℝ)) + (73 / 500 : ℝ) * ((-2 / 5 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-1 / 25 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_45_negative : 0 < ((13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-157 / 100 : ℝ)) := by linarith only [branch_45]
            by_cases branch_48 : 0 ≤ ((7 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (957 / 500 : ℝ))
            ·
              by_cases branch_49 : 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-1 / 25 : ℝ))
              ·
                apply adjacentR4_hit_boundary square fits 18
                change 0 ≤ ((13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-157 / 100 : ℝ)) ∧ 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-1 / 25 : ℝ)) ∧ 0 ≤ ((7 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (957 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_45_negative.le
                ·
                  exact branch_49
                ·
                  exact branch_48
              ·
                have branch_49_negative : 0 < ((2 / 5 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (1 / 25 : ℝ)) := by linarith only [branch_49]
                apply adjacentR4_hit_boundary square fits 22
                change 0 ≤ ((1 / 2 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-46 / 25 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (54 / 25 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (1 / 25 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 / 2 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (46 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (9 / 25 : ℝ)) branch_45_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (73 / 500 : ℝ)) branch_49_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (38 / 125 : ℝ)) negative
                  have identity : (9 / 25 : ℝ) * ((13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-157 / 100 : ℝ)) + (73 / 500 : ℝ) * ((2 / 5 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (1 / 25 : ℝ)) + (38 / 125 : ℝ) * ((-1 / 2 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (46 / 25 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  exact branch_44
                ·
                  exact branch_49_negative.le
            ·
              have branch_48_negative : 0 < ((-7 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-957 / 500 : ℝ)) := by linarith only [branch_48]
              by_cases branch_50 : 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-61 / 125 : ℝ))
              ·
                by_cases branch_51 : 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (59 / 20 : ℝ))
                ·
                  apply adjacentR4_hit_boundary square fits 20
                  change 0 ≤ ((-7 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-957 / 500 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (59 / 20 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-61 / 125 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_48_negative.le
                  ·
                    exact branch_51
                  ·
                    exact branch_50
                ·
                  have branch_51_negative : 0 < ((1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-59 / 20 : ℝ)) := by linarith only [branch_51]
                  by_cases branch_52 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
                  ·
                    apply adjacentR4_hit_boundary square fits 27
                    change 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (19 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-59 / 20 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((1 / 2 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (-19 / 20 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (109 / 250 : ℝ)) branch_44
                      have weighted_1 := mul_pos (by norm_num : 0 < (9 / 100 : ℝ)) branch_48_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (81 / 100 : ℝ)) negative
                      have identity : (109 / 250 : ℝ) * ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (54 / 25 : ℝ)) + (9 / 100 : ℝ) * ((-7 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-957 / 500 : ℝ)) + (81 / 100 : ℝ) * ((1 / 2 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (-19 / 20 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                    ·
                      exact branch_52
                    ·
                      exact branch_51_negative.le
                  ·
                    have branch_52_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_52]
                    apply adjacentR4_hit_boundary square fits 50
                    change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-17 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (17 / 10 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (7 / 10 : ℝ)) branch_50
                      have weighted_1 := mul_pos (by norm_num : 0 < (1 / 5 : ℝ)) branch_51_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (137 / 250 : ℝ)) negative
                      have identity : (7 / 10 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-61 / 125 : ℝ)) + (1 / 5 : ℝ) * ((1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-59 / 20 : ℝ)) + (137 / 250 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (17 / 10 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                    ·
                      by_contra! failed
                      have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_44
                      have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                      have identity : (1 : ℝ) * ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (54 / 25 : ℝ)) + (9 / 10 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) = (-9 / 100 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (9 / 100 : ℝ))
                      nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                    ·
                      exact branch_52_negative.le
              ·
                have branch_50_negative : 0 < ((-16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (61 / 125 : ℝ)) := by linarith only [branch_50]
                by_cases branch_53 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
                ·
                  apply adjacentR4_hit_boundary square fits 21
                  change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (61 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-297 / 125 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_50_negative.le
                  ·
                    exact branch_53
                  ·
                    by_contra! failed
                    have negative : 0 < ((-16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (297 / 125 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (41 / 250 : ℝ)) branch_13_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (123 / 250 : ℝ)) branch_45_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (41 / 100 : ℝ)) negative
                    have identity : (41 / 250 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 100 : ℝ)) + (123 / 250 : ℝ) * ((13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-157 / 100 : ℝ)) + (41 / 100 : ℝ) * ((-16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (297 / 125 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  have branch_53_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_53]
                  by_cases branch_54 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (17 / 10 : ℝ))
                  ·
                    apply adjacentR4_hit_boundary square fits 49
                    change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-9 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (17 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_13_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
                      have identity : (1 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-123 / 100 : ℝ)) + (41 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (9 / 10 : ℝ)) = (-123 / 250 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (123 / 250 : ℝ))
                      nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                    ·
                      exact branch_54
                    ·
                      exact branch_53_negative.le
                  ·
                    have branch_54_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-17 / 10 : ℝ)) := by linarith only [branch_54]
                    apply adjacentR4_hit_boundary square fits 50
                    change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-17 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      exact branch_54_negative.le
                    ·
                      by_contra! failed
                      have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_44
                      have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                      have identity : (1 : ℝ) * ((-9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (54 / 25 : ℝ)) + (9 / 10 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) = (-9 / 100 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (9 / 100 : ℝ))
                      nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                    ·
                      exact branch_53_negative.le
        ·
          have branch_44_negative : 0 < ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-54 / 25 : ℝ)) := by linarith only [branch_44]
          by_cases branch_55 : 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (59 / 20 : ℝ))
          ·
            by_cases branch_56 : 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (4 / 25 : ℝ))
            ·
              by_cases branch_57 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-11 / 4 : ℝ))
              ·
                by_cases branch_58 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ))
                ·
                  apply adjacentR4_hit_boundary square fits 24
                  change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (4 / 25 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-64 / 25 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_58
                  ·
                    exact branch_56
                  ·
                    by_contra! failed
                    have negative : 0 < ((-3 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (64 / 25 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (63 / 100 : ℝ)) branch_38_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (193 / 500 : ℝ)) branch_44_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (81 / 100 : ℝ)) negative
                    have identity : (63 / 100 : ℝ) * ((11 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-246 / 125 : ℝ)) + (193 / 500 : ℝ) * ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-54 / 25 : ℝ)) + (81 / 100 : ℝ) * ((-3 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (64 / 25 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  have branch_58_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [branch_58]
                  apply adjacentR4_hit_boundary square fits 52
                  change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 5 : ℝ)) branch_55
                    have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_56
                    have weighted_2 := mul_pos (by norm_num : 0 < (63 / 100 : ℝ)) negative
                    have identity : (2 / 5 : ℝ) * ((-1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (59 / 20 : ℝ)) + (1 / 2 : ℝ) * ((2 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (4 / 25 : ℝ)) + (63 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                  ·
                    exact branch_58_negative.le
              ·
                have branch_57_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (11 / 4 : ℝ)) := by linarith only [branch_57]
                apply adjacentR4_hit_boundary square fits 24
                change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((2 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (4 / 25 : ℝ)) ∧ 0 ≤ ((3 / 5 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-64 / 25 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_57_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (11 / 4 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) = (-7 / 20 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (7 / 20 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_56
                ·
                  by_contra! failed
                  have negative : 0 < ((-3 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (64 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (63 / 100 : ℝ)) branch_38_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (193 / 500 : ℝ)) branch_44_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (81 / 100 : ℝ)) negative
                  have identity : (63 / 100 : ℝ) * ((11 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-246 / 125 : ℝ)) + (193 / 500 : ℝ) * ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-54 / 25 : ℝ)) + (81 / 100 : ℝ) * ((-3 / 5 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (64 / 25 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              have branch_56_negative : 0 < ((-2 / 5 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-4 / 25 : ℝ)) := by linarith only [branch_56]
              apply adjacentR4_hit_boundary square fits 25
              change 0 ≤ ((-2 / 5 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-4 / 25 : ℝ)) ∧ 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (59 / 20 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-54 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_56_negative.le
              ·
                exact branch_55
              ·
                exact branch_44_negative.le
          ·
            have branch_55_negative : 0 < ((1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-59 / 20 : ℝ)) := by linarith only [branch_55]
            by_cases branch_59 : 0 ≤ ((1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (11 / 20 : ℝ))
            ·
              by_cases branch_60 : 0 ≤ ((7 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (957 / 500 : ℝ))
              ·
                by_cases branch_61 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-11 / 4 : ℝ))
                ·
                  by_cases branch_62 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ))
                  ·
                    apply adjacentR4_hit_boundary square fits 26
                    change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (11 / 20 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-59 / 20 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      exact branch_62
                    ·
                      exact branch_59
                    ·
                      exact branch_55_negative.le
                  ·
                    have branch_62_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [branch_62]
                    by_cases branch_63 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ))
                    ·
                      apply adjacentR4_hit_boundary square fits 52
                      change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ))
                      refine ⟨?_ , ?_ , ?_ ⟩
                      ·
                        by_contra! failed
                        have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                        have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
                        have weighted_1 := mul_pos (by norm_num : 0 < (293 / 500 : ℝ)) negative
                        have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (293 / 500 : ℝ) * square.center.y + (-293 / 500 : ℝ)) + (293 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                          ring
                        nlinarith only [weighted_0, weighted_1, identity]
                      ·
                        exact branch_63
                      ·
                        exact branch_62_negative.le
                    ·
                      have branch_63_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) := by linarith only [branch_63]
                      apply adjacentR4_hit_boundary square fits 53
                      change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ))
                      refine ⟨?_ , ?_ , ?_ ⟩
                      ·
                        exact branch_63_negative.le
                      ·
                        by_contra! failed
                        have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                        have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (7 / 50 : ℝ)) container_1
                        have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_60
                        have weighted_2 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                        have identity : (7 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 : ℝ) * ((7 / 50 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (957 / 500 : ℝ)) + (9 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (-113 / 500 : ℝ) := by
                          ring
                        have constant_negative := (by norm_num : 0 < (113 / 500 : ℝ))
                        nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                      ·
                        exact branch_62_negative.le
                ·
                  have branch_61_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (11 / 4 : ℝ)) := by linarith only [branch_61]
                  apply adjacentR4_hit_boundary square fits 26
                  change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (11 / 20 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-59 / 20 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_61_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (11 / 4 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) = (-7 / 20 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (7 / 20 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_59
                  ·
                    exact branch_55_negative.le
              ·
                have branch_60_negative : 0 < ((-7 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-957 / 500 : ℝ)) := by linarith only [branch_60]
                by_cases branch_64 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ))
                ·
                  apply adjacentR4_hit_boundary square fits 26
                  change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (11 / 20 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-59 / 20 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_64
                  ·
                    exact branch_59
                  ·
                    exact branch_55_negative.le
                ·
                  have branch_64_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [branch_64]
                  by_cases branch_65 : 0 ≤ ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (9 / 5 : ℝ))
                  ·
                    apply adjacentR4_hit_boundary square fits 53
                    change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (7 / 50 : ℝ)) container_0
                      have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_60_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                      have identity : (7 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (0 : ℝ)) + (1 : ℝ) * ((-7 / 50 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-957 / 500 : ℝ)) + (9 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (2 : ℝ)) = (-57 / 500 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (57 / 500 : ℝ))
                      nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                    ·
                      by_contra! failed
                      have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_65
                      have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) negative
                      have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (9 / 5 : ℝ)) + (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, identity]
                    ·
                      exact branch_64_negative.le
                  ·
                    have branch_65_negative : 0 < ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-9 / 5 : ℝ)) := by linarith only [branch_65]
                    apply adjacentR4_hit_boundary square fits 37
                    change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
                    refine ⟨?_ , ?_ ⟩
                    ·
                      exact branch_64_negative.le
                    ·
                      by_contra! failed
                      have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_65_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) negative
                      have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-9 / 5 : ℝ)) + (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_59_negative : 0 < ((-1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-11 / 20 : ℝ)) := by linarith only [branch_59]
              by_cases branch_66 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
              ·
                by_cases branch_67 : 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (19 / 20 : ℝ))
                ·
                  apply adjacentR4_hit_boundary square fits 27
                  change 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (19 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-59 / 20 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_67
                  ·
                    exact branch_66
                  ·
                    exact branch_55_negative.le
                ·
                  have branch_67_negative : 0 < ((1 / 2 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (-19 / 20 : ℝ)) := by linarith only [branch_67]
                  apply adjacentR4_hit_boundary square fits 28
                  change 0 ≤ ((-1 / 2 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-11 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (9 / 5 : ℝ)) ∧ 0 ≤ ((1 / 2 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (-19 / 20 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_59_negative.le
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-9 / 5 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 5 : ℝ)) branch_66
                    have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                    have identity : (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-9 / 5 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    exact branch_67_negative.le
              ·
                have branch_66_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_66]
                by_cases branch_68 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ))
                ·
                  by_cases branch_69 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ))
                  ·
                    apply adjacentR4_hit_boundary square fits 50
                    change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-17 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (5 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (17 / 10 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_44_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                      have identity : (1 : ℝ) * ((9 / 10 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-54 / 25 : ℝ)) + (9 / 10 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (17 / 10 : ℝ)) = (-63 / 100 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (63 / 100 : ℝ))
                      nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                    ·
                      exact branch_69
                    ·
                      exact branch_66_negative.le
                  ·
                    have branch_69_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) := by linarith only [branch_69]
                    apply adjacentR4_hit_boundary square fits 51
                    change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-5 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (-9 / 5 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      exact branch_69_negative.le
                    ·
                      exact branch_68
                    ·
                      by_contra! failed
                      have negative : 0 < ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (9 / 5 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_66_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                      have identity : (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (9 / 5 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, identity]
                ·
                  have branch_68_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) := by linarith only [branch_68]
                  apply adjacentR4_hit_boundary square fits 37
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
                  refine ⟨?_ , ?_ ⟩
                  ·
                    exact branch_68_negative.le
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_66_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]

end SquarePackingArchive.BentzThirteen
