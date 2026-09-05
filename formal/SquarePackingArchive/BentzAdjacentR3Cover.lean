import SquarePackingArchive.BentzAdjacentR3Geometry

namespace SquarePackingArchive.BentzThirteen

set_option maxHeartbeats 4000000 in
theorem adjacentR3_unavoidable : ∀ square : PlacedSquare, square.Fits 4 → adjacentR3Outcome square := by
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
  by_cases branch_0 : 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ))
  ·
    by_cases branch_1 : 0 ≤ ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ))
    ·
      by_cases branch_2 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 5 : ℝ))
      ·
        by_cases branch_3 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ))
        ·
          by_cases branch_4 : 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-843 / 500 : ℝ))
          ·
            apply adjacentR3_hit_boundary square fits 33
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 5 : ℝ)) container_2
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_4
              have weighted_2 := mul_pos (by norm_num : 0 < (41 / 50 : ℝ)) negative
              have identity : (1 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + (1 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-843 / 500 : ℝ)) + (41 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) = (-57 / 125 : ℝ) := by
                ring
              have constant_negative := (by norm_num : 0 < (57 / 125 : ℝ))
              nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
            ·
              exact branch_3
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (4 / 5 : ℝ)) branch_1
              have weighted_1 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
              have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) + (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_4_negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (843 / 500 : ℝ)) := by linarith only [branch_4]
            by_cases branch_5 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ))
            ·
              apply adjacentR3_hit_boundary square fits 33
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (4 / 5 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_5
              ·
                exact branch_3
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (4 / 5 : ℝ)) branch_1
                have weighted_1 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
                have identity : (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) + (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-4 / 5 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_5_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) := by linarith only [branch_5]
              by_cases branch_6 : 0 ≤ ((6 / 25 : ℝ) * square.center.x + (47 / 100 : ℝ) * square.center.y + (-403 / 500 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 2
                change 0 ≤ ((6 / 25 : ℝ) * square.center.x + (37 / 50 : ℝ) * square.center.y + (-632 / 625 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-13 / 100 : ℝ) * square.center.y + (1369 / 2500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-6 / 25 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (632 / 625 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (81 / 1250 : ℝ)) branch_5_negative
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (37 / 50 : ℝ)) branch_6
                  have weighted_2 := mul_pos (by norm_num : 0 < (47 / 100 : ℝ)) negative
                  have identity : (81 / 1250 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) + (37 / 50 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (47 / 100 : ℝ) * square.center.y + (-403 / 500 : ℝ)) + (47 / 100 : ℝ) * ((-6 / 25 : ℝ) * square.center.x + (-37 / 50 : ℝ) * square.center.y + (632 / 625 : ℝ)) = (-2997 / 125000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (2997 / 125000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((6 / 25 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1369 / 2500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 100 : ℝ)) branch_1
                  have weighted_1 := mul_pos (by norm_num : 0 < (183 / 1250 : ℝ)) branch_5_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
                  have identity : (13 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) + (183 / 1250 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) + (61 / 100 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (13 / 100 : ℝ) * square.center.y + (-1369 / 2500 : ℝ)) = (-549 / 15625 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (549 / 15625 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_1
              ·
                have branch_6_negative : 0 < ((-6 / 25 : ℝ) * square.center.x + (-47 / 100 : ℝ) * square.center.y + (403 / 500 : ℝ)) := by linarith only [branch_6]
                apply adjacentR3_hit_boundary square fits 32
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-7 / 5 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (187 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (-47 / 100 : ℝ) * square.center.y + (403 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_2
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_5_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-187 / 100 : ℝ)) = (-37 / 100 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (37 / 100 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_6_negative.le
        ·
          have branch_3_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) := by linarith only [branch_3]
          apply adjacentR3_hit_boundary square fits 36
          change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (61 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-3 / 4 : ℝ) * square.center.y + (3 / 4 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_3_negative.le
          ·
            by_contra! failed
            have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-61 / 20 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) container_2
            have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_0
            have weighted_2 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
            have identity : (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (0 : ℝ)) + (1 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (4 / 5 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-61 / 20 : ℝ)) = (-1 / 10 : ℝ) := by
              ring
            have constant_negative := (by norm_num : 0 < (1 / 10 : ℝ))
            nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (3 / 4 : ℝ) * square.center.y + (-3 / 4 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 4 : ℝ)) branch_1
            have weighted_1 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
            have identity : (3 / 4 : ℝ) * ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) + (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (3 / 4 : ℝ) * square.center.y + (-3 / 4 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
      ·
        have branch_2_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 5 : ℝ)) := by linarith only [branch_2]
        by_cases branch_7 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ))
        ·
          apply adjacentR3_hit_boundary square fits 24
          change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
          refine ⟨?_ , ?_ ⟩
          ·
            exact branch_7
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_1
            have weighted_1 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
            have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) + (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
        ·
          have branch_7_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) := by linarith only [branch_7]
          apply adjacentR3_hit_boundary square fits 35
          change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (7 / 5 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-243 / 500 : ℝ) * square.center.y + (243 / 500 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_7_negative.le
          ·
            exact branch_2_negative.le
          ·
            by_contra! failed
            have negative : 0 < ((0 : ℝ) * square.center.x + (243 / 500 : ℝ) * square.center.y + (-243 / 500 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (243 / 500 : ℝ)) branch_1
            have weighted_1 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
            have identity : (243 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (-61 / 100 : ℝ) * square.center.y + (61 / 100 : ℝ)) + (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (243 / 500 : ℝ) * square.center.y + (-243 / 500 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, identity]
    ·
      have branch_1_negative : 0 < ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) := by linarith only [branch_1]
      by_cases branch_8 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ))
      ·
        by_cases branch_9 : 0 ≤ ((6 / 25 : ℝ) * square.center.x + (47 / 100 : ℝ) * square.center.y + (-403 / 500 : ℝ))
        ·
          by_cases branch_10 : 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ))
          ·
            by_cases branch_11 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ))
            ·
              apply adjacentR3_hit_boundary square fits 1
              change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1871 / 5000 : ℝ)) branch_1_negative
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (2623 / 50000 : ℝ)) branch_10
                have weighted_2 := mul_pos (by norm_num : 0 < (61 / 125 : ℝ)) negative
                have identity : (1871 / 5000 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) + (2623 / 50000 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ)) + (61 / 125 : ℝ) * ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_11
              ·
                by_contra! failed
                have negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (21291 / 50000 : ℝ)) branch_8
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (453 / 500 : ℝ)) branch_9
                have weighted_2 := mul_pos (by norm_num : 0 < (6 / 25 : ℝ)) negative
                have identity : (21291 / 50000 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (453 / 500 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (47 / 100 : ℝ) * square.center.y + (-403 / 500 : ℝ)) + (6 / 25 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) = (-158097 / 5000000 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (158097 / 5000000 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
            ·
              have branch_11_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) := by linarith only [branch_11]
              apply adjacentR3_hit_boundary square fits 7
              change 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ)) ∧ 0 ≤ ((-1 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (369 / 250 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_10
              ·
                by_contra! failed
                have negative : 0 < ((1 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-369 / 250 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 50 : ℝ)) container_1
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (4 / 5 : ℝ)) branch_8
                have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (1 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) + (1 : ℝ) * ((1 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-369 / 250 : ℝ)) = (-123 / 250 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (123 / 250 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                exact branch_11_negative.le
          ·
            have branch_10_negative : 0 < ((4 / 5 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-9 / 10 : ℝ)) := by linarith only [branch_10]
            apply adjacentR3_hit_boundary square fits 5
            change 0 ≤ ((0 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-9 / 10 : ℝ)) ∧ 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) ∧ 0 ≤ ((4 / 5 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-18 / 25 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) branch_1_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
              have identity : (9 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) + (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, identity]
            ·
              exact branch_0
            ·
              by_contra! failed
              have negative : 0 < ((-4 / 5 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (18 / 25 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (2 / 25 : ℝ)) branch_0
              have weighted_1 := mul_pos (by norm_num : 0 < (18 / 25 : ℝ)) branch_10_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (16 / 25 : ℝ)) negative
              have identity : (2 / 25 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (18 / 25 : ℝ) * ((4 / 5 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-9 / 10 : ℝ)) + (16 / 25 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (18 / 25 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
        ·
          have branch_9_negative : 0 < ((-6 / 25 : ℝ) * square.center.x + (-47 / 100 : ℝ) * square.center.y + (403 / 500 : ℝ)) := by linarith only [branch_9]
          by_cases branch_12 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (113 / 100 : ℝ))
          ·
            by_cases branch_13 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ))
            ·
              apply adjacentR3_hit_boundary square fits 37
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 125 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_1_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) + (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) = (-2623 / 50000 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (2623 / 50000 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                exact branch_8
              ·
                by_contra! failed
                have negative : 0 < ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 125 : ℝ)) branch_13
                have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (27 / 125 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (457 / 500 : ℝ)) + (1 : ℝ) * ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (-1161 / 62500 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (1161 / 62500 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
            ·
              have branch_13_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-457 / 500 : ℝ)) := by linarith only [branch_13]
              by_cases branch_14 : 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 1
                change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (8021 / 50000 : ℝ)) branch_1_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (2623 / 50000 : ℝ)) branch_9_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (183 / 1250 : ℝ)) negative
                  have identity : (8021 / 50000 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) + (2623 / 50000 : ℝ) * ((-6 / 25 : ℝ) * square.center.x + (-47 / 100 : ℝ) * square.center.y + (403 / 500 : ℝ)) + (183 / 1250 : ℝ) * ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) = (-7869 / 6250000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (7869 / 6250000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1327 / 5000 : ℝ)) branch_1_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (2501 / 5000 : ℝ)) branch_9_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (183 / 1250 : ℝ)) negative
                  have identity : (1327 / 5000 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) + (2501 / 5000 : ℝ) * ((-6 / 25 : ℝ) * square.center.x + (-47 / 100 : ℝ) * square.center.y + (403 / 500 : ℝ)) + (183 / 1250 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) = (-7503 / 625000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (7503 / 625000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_14
              ·
                have branch_14_negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [branch_14]
                apply adjacentR3_hit_boundary square fits 37
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-457 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (113 / 100 : ℝ)) ∧ 0 ≤ ((-27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 125 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_1_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) + (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (457 / 500 : ℝ)) = (-2623 / 50000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (2623 / 50000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_8
                ·
                  by_contra! failed
                  have negative : 0 < ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (27 / 125 : ℝ)) branch_14_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                  have identity : (27 / 125 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((27 / 125 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 125 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_12_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_12]
            apply adjacentR3_hit_boundary square fits 1
            change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (8021 / 50000 : ℝ)) branch_1_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (2623 / 50000 : ℝ)) branch_9_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (183 / 1250 : ℝ)) negative
              have identity : (8021 / 50000 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) + (2623 / 50000 : ℝ) * ((-6 / 25 : ℝ) * square.center.x + (-47 / 100 : ℝ) * square.center.y + (403 / 500 : ℝ)) + (183 / 1250 : ℝ) * ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) = (-7869 / 6250000 : ℝ) := by
                ring
              have constant_negative := (by norm_num : 0 < (7869 / 6250000 : ℝ))
              nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
            ·
              by_contra! failed
              have negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (1327 / 5000 : ℝ)) branch_1_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (2501 / 5000 : ℝ)) branch_9_negative
              have weighted_2 := mul_pos (by norm_num : 0 < (183 / 1250 : ℝ)) negative
              have identity : (1327 / 5000 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) + (2501 / 5000 : ℝ) * ((-6 / 25 : ℝ) * square.center.x + (-47 / 100 : ℝ) * square.center.y + (403 / 500 : ℝ)) + (183 / 1250 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) = (-7503 / 625000 : ℝ) := by
                ring
              have constant_negative := (by norm_num : 0 < (7503 / 625000 : ℝ))
              nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
            ·
              by_contra! failed
              have negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) branch_12_negative
              have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
              have identity : (453 / 500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (1 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) = (-5889 / 50000 : ℝ) := by
                ring
              have constant_negative := (by norm_num : 0 < (5889 / 50000 : ℝ))
              nlinarith only [weighted_0, weighted_1, constant_negative, identity]
      ·
        have branch_8_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) := by linarith only [branch_8]
        by_cases branch_15 : 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
        ·
          by_cases branch_16 : 0 ≤ ((-1 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (369 / 250 : ℝ))
          ·
            by_cases branch_17 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-29 / 20 : ℝ))
            ·
              by_cases branch_18 : 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (18 / 25 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 4
                change 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (18 / 25 : ℝ)) ∧ 0 ≤ ((-1 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (369 / 250 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-387 / 250 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_18
                ·
                  exact branch_16
                ·
                  by_contra! failed
                  have negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (387 / 250 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (2 / 5 : ℝ)) branch_1_negative
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (2501 / 5000 : ℝ)) branch_17
                  have weighted_2 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
                  have identity : (2 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) + (2501 / 5000 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-29 / 20 : ℝ)) + (61 / 100 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (387 / 250 : ℝ)) = (-2501 / 100000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (2501 / 100000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
              ·
                have branch_18_negative : 0 < ((4 / 5 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-18 / 25 : ℝ)) := by linarith only [branch_18]
                apply adjacentR3_hit_boundary square fits 5
                change 0 ≤ ((0 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-9 / 10 : ℝ)) ∧ 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) ∧ 0 ≤ ((4 / 5 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-18 / 25 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) branch_1_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (61 / 100 : ℝ)) negative
                  have identity : (9 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (61 / 100 : ℝ) * square.center.y + (-61 / 100 : ℝ)) + (61 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  exact branch_0
                ·
                  exact branch_18_negative.le
            ·
              have branch_17_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (29 / 20 : ℝ)) := by linarith only [branch_17]
              by_cases branch_19 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 1
                change 0 ≤ ((-43 / 500 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-371 / 1000 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (173 / 100 : ℝ)) ∧ 0 ≤ ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (43 / 500 : ℝ)) branch_0
                  have weighted_1 := mul_pos (by norm_num : 0 < (443 / 1000 : ℝ)) branch_8_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                  have identity : (43 / 500 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (443 / 1000 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (4 / 5 : ℝ) * ((43 / 500 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (371 / 1000 : ℝ)) = (-51 / 20000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (51 / 20000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_19
                ·
                  exact branch_15
              ·
                have branch_19_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) := by linarith only [branch_19]
                apply adjacentR3_hit_boundary square fits 4
                change 0 ≤ ((-4 / 5 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (18 / 25 : ℝ)) ∧ 0 ≤ ((-1 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (369 / 250 : ℝ)) ∧ 0 ≤ ((41 / 50 : ℝ) * square.center.x + (2 / 5 : ℝ) * square.center.y + (-387 / 250 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((4 / 5 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-18 / 25 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (2 / 5 : ℝ)) branch_8_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) branch_17_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (2 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) + (4 / 5 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (29 / 20 : ℝ)) + (1 : ℝ) * ((4 / 5 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (-18 / 25 : ℝ)) = (-3 / 250 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (3 / 250 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_16
                ·
                  by_contra! failed
                  have negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (387 / 250 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (41 / 500 : ℝ)) branch_15
                  have weighted_1 := mul_pos (by norm_num : 0 < (453 / 1250 : ℝ)) branch_19_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (453 / 1000 : ℝ)) negative
                  have identity : (41 / 500 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 1250 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-173 / 100 : ℝ)) + (453 / 1000 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (-2 / 5 : ℝ) * square.center.y + (387 / 250 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_16_negative : 0 < ((1 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-369 / 250 : ℝ)) := by linarith only [branch_16]
            by_cases branch_20 : 0 ≤ ((-17 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (513 / 250 : ℝ))
            ·
              apply adjacentR3_hit_boundary square fits 9
              change 0 ≤ ((1 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-369 / 250 : ℝ)) ∧ 0 ≤ ((-17 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (513 / 250 : ℝ)) ∧ 0 ≤ ((8 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_16_negative.le
              ·
                exact branch_20
              ·
                by_contra! failed
                have negative : 0 < ((-8 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (8 / 25 : ℝ)) branch_15
                have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                have identity : (8 / 25 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((-8 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_20_negative : 0 < ((17 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-513 / 250 : ℝ)) := by linarith only [branch_20]
              by_cases branch_21 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ))
              ·
                by_cases branch_22 : 0 ≤ ((0 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (33 / 20 : ℝ))
                ·
                  by_cases branch_23 : 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ))
                  ·
                    by_cases branch_24 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ))
                    ·
                      apply adjacentR3_hit_boundary square fits 20
                      change 0 ≤ ((-17 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (63 / 250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) ∧ 0 ≤ ((17 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-513 / 250 : ℝ))
                      refine ⟨?_ , ?_ , ?_ ⟩
                      ·
                        by_contra! failed
                        have negative : 0 < ((17 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-63 / 250 : ℝ)) := by linarith only [failed]
                        have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (69 / 250 : ℝ)) branch_0
                        have weighted_1 := mul_pos (by norm_num : 0 < (33 / 100 : ℝ)) branch_16_negative
                        have weighted_2 := mul_pos (by norm_num : 0 < (63 / 100 : ℝ)) negative
                        have identity : (69 / 250 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (33 / 100 : ℝ) * ((1 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-369 / 250 : ℝ)) + (63 / 100 : ℝ) * ((17 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-63 / 250 : ℝ)) = (0 : ℝ) := by
                          ring
                        nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                      ·
                        exact branch_24
                      ·
                        exact branch_20_negative.le
                    ·
                      have branch_24_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) := by linarith only [branch_24]
                      apply adjacentR3_hit_boundary square fits 21
                      change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (279 / 100 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ))
                      refine ⟨?_ , ?_ , ?_ ⟩
                      ·
                        exact branch_24_negative.le
                      ·
                        by_contra! failed
                        have negative : 0 < ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) := by linarith only [failed]
                        have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_1
                        have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_0
                        have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                        have identity : (3 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 / 2 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (1 / 2 : ℝ) * ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) = (-21 / 200 : ℝ) := by
                          ring
                        have constant_negative := (by norm_num : 0 < (21 / 200 : ℝ))
                        nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                      ·
                        exact branch_23
                  ·
                    have branch_23_negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) := by linarith only [branch_23]
                    apply adjacentR3_hit_boundary square fits 22
                    change 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (33 / 20 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (1 / 20 : ℝ) * square.center.y + (-967 / 1000 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      exact branch_23_negative.le
                    ·
                      exact branch_22
                    ·
                      by_contra! failed
                      have negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (-1 / 20 : ℝ) * square.center.y + (967 / 1000 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (671 / 1000 : ℝ)) branch_15
                      have weighted_1 := mul_pos (by norm_num : 0 < (453 / 10000 : ℝ)) branch_20_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (453 / 625 : ℝ)) negative
                      have identity : (671 / 1000 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 10000 : ℝ) * ((17 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-513 / 250 : ℝ)) + (453 / 625 : ℝ) * ((-43 / 50 : ℝ) * square.center.x + (-1 / 20 : ℝ) * square.center.y + (967 / 1000 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  have branch_22_negative : 0 < ((0 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-33 / 20 : ℝ)) := by linarith only [branch_22]
                  apply adjacentR3_hit_boundary square fits 42
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-33 / 20 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 20 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_15
                    have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                    have identity : (1 : ℝ) * ((453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 20 : ℝ)) = (-453 / 10000 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (453 / 10000 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_21
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) + (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) = (-3 / 20 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (3 / 20 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_22_negative.le
              ·
                have branch_21_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ)) := by linarith only [branch_21]
                by_cases branch_25 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-29 / 20 : ℝ))
                ·
                  by_cases branch_26 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ))
                  ·
                    apply adjacentR3_hit_boundary square fits 20
                    change 0 ≤ ((-17 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (63 / 250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) ∧ 0 ≤ ((17 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-513 / 250 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((17 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-63 / 250 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (69 / 250 : ℝ)) branch_0
                      have weighted_1 := mul_pos (by norm_num : 0 < (33 / 100 : ℝ)) branch_16_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (63 / 100 : ℝ)) negative
                      have identity : (69 / 250 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (33 / 100 : ℝ) * ((1 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-369 / 250 : ℝ)) + (63 / 100 : ℝ) * ((17 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-63 / 250 : ℝ)) = (0 : ℝ) := by
                        ring
                      nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                    ·
                      exact branch_26
                    ·
                      exact branch_20_negative.le
                  ·
                    have branch_26_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) := by linarith only [branch_26]
                    apply adjacentR3_hit_boundary square fits 21
                    change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (279 / 100 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      exact branch_26_negative.le
                    ·
                      by_contra! failed
                      have negative : 0 < ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_1
                      have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_0
                      have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                      have identity : (3 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 / 2 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (1 / 2 : ℝ) * ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) = (-21 / 200 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (21 / 200 : ℝ))
                      nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                    ·
                      by_contra! failed
                      have negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_0
                      have weighted_1 := mul_pos (by norm_num : 0 < (83 / 100 : ℝ)) branch_21_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                      have identity : (1 / 2 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (83 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ)) + (1 / 2 : ℝ) * ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) = (-111 / 2000 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (111 / 2000 : ℝ))
                      nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  have branch_25_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (29 / 20 : ℝ)) := by linarith only [branch_25]
                  by_cases branch_27 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (249 / 100 : ℝ))
                  ·
                    by_cases branch_28 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (217 / 100 : ℝ))
                    ·
                      by_cases branch_29 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ))
                      ·
                        apply adjacentR3_hit_boundary square fits 20
                        change 0 ≤ ((-17 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (63 / 250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) ∧ 0 ≤ ((17 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-513 / 250 : ℝ))
                        refine ⟨?_ , ?_ , ?_ ⟩
                        ·
                          by_contra! failed
                          have negative : 0 < ((17 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-63 / 250 : ℝ)) := by linarith only [failed]
                          have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (69 / 250 : ℝ)) branch_0
                          have weighted_1 := mul_pos (by norm_num : 0 < (33 / 100 : ℝ)) branch_16_negative
                          have weighted_2 := mul_pos (by norm_num : 0 < (63 / 100 : ℝ)) negative
                          have identity : (69 / 250 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (33 / 100 : ℝ) * ((1 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-369 / 250 : ℝ)) + (63 / 100 : ℝ) * ((17 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-63 / 250 : ℝ)) = (0 : ℝ) := by
                            ring
                          nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                        ·
                          exact branch_29
                        ·
                          exact branch_20_negative.le
                      ·
                        have branch_29_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) := by linarith only [branch_29]
                        apply adjacentR3_hit_boundary square fits 21
                        change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (279 / 100 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ))
                        refine ⟨?_ , ?_ , ?_ ⟩
                        ·
                          exact branch_29_negative.le
                        ·
                          by_contra! failed
                          have negative : 0 < ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) := by linarith only [failed]
                          have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_1
                          have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_0
                          have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                          have identity : (3 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 / 2 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (1 / 2 : ℝ) * ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) = (-21 / 200 : ℝ) := by
                            ring
                          have constant_negative := (by norm_num : 0 < (21 / 200 : ℝ))
                          nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                        ·
                          by_contra! failed
                          have negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) := by linarith only [failed]
                          have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_0
                          have weighted_1 := mul_pos (by norm_num : 0 < (83 / 100 : ℝ)) branch_21_negative
                          have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                          have identity : (1 / 2 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (83 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ)) + (1 / 2 : ℝ) * ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) = (-111 / 2000 : ℝ) := by
                            ring
                          have constant_negative := (by norm_num : 0 < (111 / 2000 : ℝ))
                          nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                    ·
                      have branch_28_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-217 / 100 : ℝ)) := by linarith only [branch_28]
                      apply adjacentR3_hit_boundary square fits 21
                      change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (279 / 100 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ))
                      refine ⟨?_ , ?_ , ?_ ⟩
                      ·
                        by_contra! failed
                        have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) := by linarith only [failed]
                        have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_28_negative
                        have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                        have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-217 / 100 : ℝ)) + (1 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) = (-3 / 100 : ℝ) := by
                          ring
                        have constant_negative := (by norm_num : 0 < (3 / 100 : ℝ))
                        nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                      ·
                        by_contra! failed
                        have negative : 0 < ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) := by linarith only [failed]
                        have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_1
                        have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_0
                        have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                        have identity : (3 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 / 2 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (1 / 2 : ℝ) * ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) = (-21 / 200 : ℝ) := by
                          ring
                        have constant_negative := (by norm_num : 0 < (21 / 200 : ℝ))
                        nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                      ·
                        by_contra! failed
                        have negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) := by linarith only [failed]
                        have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_0
                        have weighted_1 := mul_pos (by norm_num : 0 < (83 / 100 : ℝ)) branch_21_negative
                        have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                        have identity : (1 / 2 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (83 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ)) + (1 / 2 : ℝ) * ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) = (-111 / 2000 : ℝ) := by
                          ring
                        have constant_negative := (by norm_num : 0 < (111 / 2000 : ℝ))
                        nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    have branch_27_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-249 / 100 : ℝ)) := by linarith only [branch_27]
                    apply adjacentR3_hit_boundary square fits 21
                    change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (279 / 100 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ))
                    refine ⟨?_ , ?_ , ?_ ⟩
                    ·
                      by_contra! failed
                      have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_27_negative
                      have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                      have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-249 / 100 : ℝ)) + (1 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) = (-7 / 20 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (7 / 20 : ℝ))
                      nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                    ·
                      by_contra! failed
                      have negative : 0 < ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 100 : ℝ)) container_1
                      have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_0
                      have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                      have identity : (3 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 / 2 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (1 / 2 : ℝ) * ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) = (-21 / 200 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (21 / 200 : ℝ))
                      nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                    ·
                      by_contra! failed
                      have negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) := by linarith only [failed]
                      have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_0
                      have weighted_1 := mul_pos (by norm_num : 0 < (83 / 100 : ℝ)) branch_21_negative
                      have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                      have identity : (1 / 2 : ℝ) * ((-4 / 5 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (117 / 50 : ℝ)) + (83 / 100 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ)) + (1 / 2 : ℝ) * ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) = (-111 / 2000 : ℝ) := by
                        ring
                      have constant_negative := (by norm_num : 0 < (111 / 2000 : ℝ))
                      nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
        ·
          have branch_15_negative : 0 < ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) := by linarith only [branch_15]
          by_cases branch_30 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ))
          ·
            by_cases branch_31 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ))
            ·
              apply adjacentR3_hit_boundary square fits 38
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-113 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (91 / 50 : ℝ)) ∧ 0 ≤ ((-69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (69 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_8_negative.le
              ·
                exact branch_31
              ·
                by_contra! failed
                have negative : 0 < ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (69 / 100 : ℝ)) branch_15_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                have identity : (69 / 100 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((69 / 100 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-69 / 100 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_31_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) := by linarith only [branch_31]
              apply adjacentR3_hit_boundary square fits 40
              change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-91 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) ∧ 0 ≤ ((-8 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (8 / 25 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_31_negative.le
              ·
                exact branch_30
              ·
                by_contra! failed
                have negative : 0 < ((8 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 25 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (8 / 25 : ℝ)) branch_15_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                have identity : (8 / 25 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((8 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-8 / 25 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_30_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) := by linarith only [branch_30]
            by_cases branch_32 : 0 ≤ ((0 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (33 / 20 : ℝ))
            ·
              by_cases branch_33 : 0 ≤ ((43 / 50 : ℝ) * square.center.x + (1 / 20 : ℝ) * square.center.y + (-967 / 1000 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 22
                change 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (33 / 20 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (1 / 20 : ℝ) * square.center.y + (-967 / 1000 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (43 / 50 : ℝ)) branch_15_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (453 / 1000 : ℝ)) branch_30_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                  have identity : (43 / 50 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 1000 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) + (453 / 500 : ℝ) * ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  exact branch_32
                ·
                  exact branch_33
              ·
                have branch_33_negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (-1 / 20 : ℝ) * square.center.y + (967 / 1000 : ℝ)) := by linarith only [branch_33]
                apply adjacentR3_hit_boundary square fits 41
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 20 : ℝ) * square.center.y + (967 / 1000 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_30_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_32
                  have weighted_1 := mul_pos (by norm_num : 0 < (11 / 20 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (33 / 20 : ℝ)) + (11 / 20 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  exact branch_33_negative.le
            ·
              have branch_32_negative : 0 < ((0 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-33 / 20 : ℝ)) := by linarith only [branch_32]
              by_cases branch_34 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 20 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 30
                change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
                refine ⟨?_ , ?_ ⟩
                ·
                  exact branch_34
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_32_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (11 / 20 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-33 / 20 : ℝ)) + (11 / 20 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_34_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 20 : ℝ)) := by linarith only [branch_34]
                apply adjacentR3_hit_boundary square fits 42
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-33 / 20 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_34_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_15_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (453 / 500 : ℝ)) negative
                  have identity : (1 : ℝ) * ((-453 / 500 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (453 / 500 : ℝ)) + (453 / 500 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) = (-453 / 1000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (453 / 1000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_32_negative.le
  ·
    have branch_0_negative : 0 < ((4 / 5 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-117 / 50 : ℝ)) := by linarith only [branch_0]
    by_cases branch_35 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ))
    ·
      by_cases branch_36 : 0 ≤ ((11 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (63 / 100 : ℝ))
      ·
        by_cases branch_37 : 0 ≤ ((-1 / 50 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-153 / 125 : ℝ))
        ·
          by_cases branch_38 : 0 ≤ ((-17 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (63 / 250 : ℝ))
          ·
            apply adjacentR3_hit_boundary square fits 20
            change 0 ≤ ((-17 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (63 / 250 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) ∧ 0 ≤ ((17 / 50 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-513 / 250 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_38
            ·
              by_contra! failed
              have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (17 / 50 : ℝ)) branch_36
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (11 / 50 : ℝ)) branch_38
              have weighted_2 := mul_pos (by norm_num : 0 < (63 / 500 : ℝ)) negative
              have identity : (17 / 50 : ℝ) * ((11 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (63 / 100 : ℝ)) + (11 / 50 : ℝ) * ((-17 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (63 / 250 : ℝ)) + (63 / 500 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              by_contra! failed
              have negative : 0 < ((-17 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (513 / 250 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (127 / 500 : ℝ)) branch_0_negative
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (47 / 100 : ℝ)) branch_37
              have weighted_2 := mul_pos (by norm_num : 0 < (57 / 100 : ℝ)) negative
              have identity : (127 / 500 : ℝ) * ((4 / 5 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-117 / 50 : ℝ)) + (47 / 100 : ℝ) * ((-1 / 50 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-153 / 125 : ℝ)) + (57 / 100 : ℝ) * ((-17 / 50 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (513 / 250 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
          ·
            have branch_38_negative : 0 < ((17 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-63 / 250 : ℝ)) := by linarith only [branch_38]
            by_cases branch_39 : 0 ≤ ((14 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (63 / 250 : ℝ))
            ·
              apply adjacentR3_hit_boundary square fits 11
              change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((14 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (63 / 250 : ℝ)) ∧ 0 ≤ ((-1 / 50 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-153 / 125 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 50 : ℝ)) branch_35
                have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                have identity : (27 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) + (1 : ℝ) * ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ)) = (-27 / 250 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (27 / 250 : ℝ))
                nlinarith only [weighted_0, weighted_1, constant_negative, identity]
              ·
                exact branch_39
              ·
                exact branch_37
            ·
              have branch_39_negative : 0 < ((-14 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-63 / 250 : ℝ)) := by linarith only [branch_39]
              by_cases branch_40 : 0 ≤ ((8 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-171 / 100 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 12
                change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((11 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (63 / 100 : ℝ)) ∧ 0 ≤ ((8 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-171 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 50 : ℝ)) branch_35
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                  have identity : (27 / 50 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) + (1 : ℝ) * ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ)) = (-27 / 250 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (27 / 250 : ℝ))
                  nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                ·
                  exact branch_36
                ·
                  exact branch_40
              ·
                have branch_40_negative : 0 < ((-8 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (171 / 100 : ℝ)) := by linarith only [branch_40]
                apply adjacentR3_hit_boundary square fits 28
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-29 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (43 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-29 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (43 / 20 : ℝ))
                refine ⟨?_ , ?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (29 / 20 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) branch_0_negative
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_36
                  have weighted_2 := mul_pos (by norm_num : 0 < (51 / 100 : ℝ)) negative
                  have identity : (1 / 2 : ℝ) * ((4 / 5 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-117 / 50 : ℝ)) + (1 / 2 : ℝ) * ((11 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (63 / 100 : ℝ)) + (51 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (29 / 20 : ℝ)) = (-231 / 2000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (231 / 2000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-43 / 20 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) branch_39_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (7 / 10 : ℝ)) branch_40_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (63 / 125 : ℝ)) negative
                  have identity : (1 / 2 : ℝ) * ((-14 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-63 / 250 : ℝ)) + (7 / 10 : ℝ) * ((-8 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (171 / 100 : ℝ)) + (63 / 125 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-43 / 20 : ℝ)) = (-63 / 5000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (63 / 5000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (29 / 20 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 50 : ℝ)) container_0
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_37
                  have weighted_2 := mul_pos (by norm_num : 0 < (7 / 10 : ℝ)) negative
                  have identity : (1 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (0 : ℝ)) + (1 : ℝ) * ((-1 / 50 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-153 / 125 : ℝ)) + (7 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (29 / 20 : ℝ)) = (-209 / 1000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (209 / 1000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-43 / 20 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (8 / 25 : ℝ)) branch_36
                  have weighted_1 := mul_pos (by norm_num : 0 < (11 / 50 : ℝ)) branch_40_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (27 / 100 : ℝ)) negative
                  have identity : (8 / 25 : ℝ) * ((11 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (63 / 100 : ℝ)) + (11 / 50 : ℝ) * ((-8 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (171 / 100 : ℝ)) + (27 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-43 / 20 : ℝ)) = (-27 / 10000 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (27 / 10000 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
        ·
          have branch_37_negative : 0 < ((1 / 50 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (153 / 125 : ℝ)) := by linarith only [branch_37]
          apply adjacentR3_hit_boundary square fits 15
          change 0 ≤ ((1 / 50 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (153 / 125 : ℝ)) ∧ 0 ≤ ((4 / 5 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-117 / 50 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (843 / 500 : ℝ))
          refine ⟨?_ , ?_ , ?_ ⟩
          ·
            exact branch_37_negative.le
          ·
            exact branch_0_negative.le
          ·
            by_contra! failed
            have negative : 0 < ((41 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-843 / 500 : ℝ)) := by linarith only [failed]
            have weighted_0 := mul_pos (by norm_num : 0 < (1 / 5 : ℝ)) branch_0_negative
            have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (57 / 100 : ℝ)) branch_35
            have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
            have identity : (1 / 5 : ℝ) * ((4 / 5 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-117 / 50 : ℝ)) + (57 / 100 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) + (1 / 2 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-843 / 500 : ℝ)) = (0 : ℝ) := by
              ring
            nlinarith only [weighted_0, weighted_1, weighted_2, identity]
      ·
        have branch_36_negative : 0 < ((-11 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-63 / 100 : ℝ)) := by linarith only [branch_36]
        by_cases branch_41 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
        ·
          by_cases branch_42 : 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (279 / 100 : ℝ))
          ·
            by_cases branch_43 : 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ))
            ·
              by_cases branch_44 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 21
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (279 / 100 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_0_negative
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (4 / 5 : ℝ)) branch_44
                  have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                  have identity : (1 : ℝ) * ((4 / 5 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-117 / 50 : ℝ)) + (4 / 5 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) + (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) = (-7 / 100 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (7 / 100 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_42
                ·
                  exact branch_43
              ·
                have branch_44_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) := by linarith only [branch_44]
                by_cases branch_45 : 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (43 / 20 : ℝ))
                ·
                  apply adjacentR3_hit_boundary square fits 28
                  change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-29 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (43 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-29 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (43 / 20 : ℝ))
                  refine ⟨?_ , ?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (29 / 20 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_44_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) + (1 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (29 / 20 : ℝ)) = (-1 / 20 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (1 / 20 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-43 / 20 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) branch_36_negative
                    have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) branch_42
                    have weighted_2 := mul_pos (by norm_num : 0 < (27 / 50 : ℝ)) negative
                    have identity : (1 / 2 : ℝ) * ((-11 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-63 / 100 : ℝ)) + (1 / 2 : ℝ) * ((-43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (279 / 100 : ℝ)) + (27 / 50 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-43 / 20 : ℝ)) = (-81 / 1000 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (81 / 1000 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (29 / 20 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (11 / 50 : ℝ)) branch_0_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) branch_36_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (51 / 100 : ℝ)) negative
                    have identity : (11 / 50 : ℝ) * ((4 / 5 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-117 / 50 : ℝ)) + (4 / 5 : ℝ) * ((-11 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-63 / 100 : ℝ)) + (51 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (29 / 20 : ℝ)) = (-2793 / 10000 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (2793 / 10000 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    exact branch_45
                ·
                  have branch_45_negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-43 / 20 : ℝ)) := by linarith only [branch_45]
                  apply adjacentR3_hit_boundary square fits 21
                  change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-107 / 50 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (279 / 100 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_45_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-43 / 20 : ℝ)) + (1 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (107 / 50 : ℝ)) = (-1 / 100 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (1 / 100 : ℝ))
                    nlinarith only [weighted_0, weighted_1, constant_negative, identity]
                  ·
                    exact branch_42
                  ·
                    exact branch_43
            ·
              have branch_43_negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) := by linarith only [branch_43]
              apply adjacentR3_hit_boundary square fits 22
              change 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (33 / 20 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (1 / 20 : ℝ) * square.center.y + (-967 / 1000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_43_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-33 / 20 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (11 / 20 : ℝ)) branch_41
                have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                have identity : (11 / 20 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-33 / 20 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                by_contra! failed
                have negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (-1 / 20 : ℝ) * square.center.y + (967 / 1000 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (86 / 125 : ℝ)) branch_0_negative
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (39 / 100 : ℝ)) branch_41
                have weighted_2 := mul_pos (by norm_num : 0 < (16 / 25 : ℝ)) negative
                have identity : (86 / 125 : ℝ) * ((4 / 5 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-117 / 50 : ℝ)) + (39 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) + (16 / 25 : ℝ) * ((-43 / 50 : ℝ) * square.center.x + (-1 / 20 : ℝ) * square.center.y + (967 / 1000 : ℝ)) = (-172 / 3125 : ℝ) := by
                  ring
                have constant_negative := (by norm_num : 0 < (172 / 3125 : ℝ))
                nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
          ·
            have branch_42_negative : 0 < ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ)) := by linarith only [branch_42]
            by_cases branch_46 : 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-539 / 500 : ℝ))
            ·
              apply adjacentR3_hit_boundary square fits 18
              change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (259 / 125 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-539 / 500 : ℝ)) ∧ 0 ≤ ((-11 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-63 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                by_contra! failed
                have negative : 0 < ((16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-259 / 125 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (64 / 125 : ℝ)) branch_35
                have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (1 / 5 : ℝ)) branch_41
                have weighted_2 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                have identity : (64 / 125 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) + (1 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-259 / 125 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                exact branch_46
              ·
                exact branch_36_negative.le
            ·
              have branch_46_negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (539 / 500 : ℝ)) := by linarith only [branch_46]
              apply adjacentR3_hit_boundary square fits 23
              change 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (539 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-279 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_46_negative.le
              ·
                exact branch_41
              ·
                exact branch_42_negative.le
        ·
          have branch_41_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_41]
          by_cases branch_47 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ))
          ·
            by_cases branch_48 : 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 20 : ℝ))
            ·
              apply adjacentR3_hit_boundary square fits 30
              change 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (19 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
              refine ⟨?_ , ?_ ⟩
              ·
                exact branch_48
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_41_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_48_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 20 : ℝ)) := by linarith only [branch_48]
              apply adjacentR3_hit_boundary square fits 42
              change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-19 / 20 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (3 / 2 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-33 / 20 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_48_negative.le
              ·
                exact branch_47
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (33 / 20 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (11 / 20 : ℝ)) branch_41_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                have identity : (11 / 20 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (33 / 20 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_47_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) := by linarith only [branch_47]
            apply adjacentR3_hit_boundary square fits 43
            change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-3 / 2 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (23 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_47_negative.le
            ·
              exact branch_35
            ·
              exact branch_41_negative.le
    ·
      have branch_35_negative : 0 < ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) := by linarith only [branch_35]
      by_cases branch_49 : 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ))
      ·
        by_cases branch_50 : 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (183 / 100 : ℝ))
        ·
          by_cases branch_51 : 0 ≤ ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ))
          ·
            apply adjacentR3_hit_boundary square fits 10
            change 0 ≤ ((-7 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) ∧ 0 ≤ ((-13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (183 / 100 : ℝ)) ∧ 0 ≤ ((27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-27 / 20 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              exact branch_49
            ·
              exact branch_50
            ·
              exact branch_51
          ·
            have branch_51_negative : 0 < ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) := by linarith only [branch_51]
            by_cases branch_52 : 0 ≤ ((-1 / 50 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-153 / 125 : ℝ))
            ·
              by_cases branch_53 : 0 ≤ ((11 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (63 / 100 : ℝ))
              ·
                by_cases branch_54 : 0 ≤ ((8 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-171 / 100 : ℝ))
                ·
                  apply adjacentR3_hit_boundary square fits 12
                  change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((11 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (63 / 100 : ℝ)) ∧ 0 ≤ ((8 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-171 / 100 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_51_negative.le
                  ·
                    exact branch_53
                  ·
                    exact branch_54
                ·
                  have branch_54_negative : 0 < ((-8 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (171 / 100 : ℝ)) := by linarith only [branch_54]
                  apply adjacentR3_hit_boundary square fits 11
                  change 0 ≤ ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) ∧ 0 ≤ ((14 / 25 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (63 / 250 : ℝ)) ∧ 0 ≤ ((-1 / 50 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-153 / 125 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_51_negative.le
                  ·
                    by_contra! failed
                    have negative : 0 < ((-14 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-63 / 250 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (63 / 125 : ℝ)) branch_35_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (7 / 10 : ℝ)) branch_54_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                    have identity : (63 / 125 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) + (7 / 10 : ℝ) * ((-8 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (171 / 100 : ℝ)) + (1 / 2 : ℝ) * ((-14 / 25 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-63 / 250 : ℝ)) = (-441 / 5000 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (441 / 5000 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    exact branch_52
              ·
                have branch_53_negative : 0 < ((-11 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-63 / 100 : ℝ)) := by linarith only [branch_53]
                apply adjacentR3_hit_boundary square fits 18
                change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (259 / 125 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-539 / 500 : ℝ)) ∧ 0 ≤ ((-11 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-63 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-259 / 125 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 250 : ℝ)) branch_50
                  have weighted_1 := mul_pos (by norm_num : 0 < (67 / 250 : ℝ)) branch_51_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (27 / 100 : ℝ)) negative
                  have identity : (27 / 250 : ℝ) * ((-13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (183 / 100 : ℝ)) + (67 / 250 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) + (27 / 100 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-259 / 125 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (539 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (127 / 250 : ℝ)) branch_35_negative
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (3 / 10 : ℝ)) branch_50
                  have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                  have identity : (127 / 250 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) + (3 / 10 : ℝ) * ((-13 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (183 / 100 : ℝ)) + (1 / 2 : ℝ) * ((-43 / 50 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (539 / 500 : ℝ)) = (-201 / 2500 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (201 / 2500 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  exact branch_53_negative.le
            ·
              have branch_52_negative : 0 < ((1 / 50 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (153 / 125 : ℝ)) := by linarith only [branch_52]
              apply adjacentR3_hit_boundary square fits 15
              change 0 ≤ ((1 / 50 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (153 / 125 : ℝ)) ∧ 0 ≤ ((4 / 5 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-117 / 50 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (843 / 500 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_52_negative.le
              ·
                exact branch_0_negative.le
              ·
                by_contra! failed
                have negative : 0 < ((41 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-843 / 500 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (27 / 250 : ℝ)) branch_49
                have weighted_1 := mul_pos (by norm_num : 0 < (177 / 500 : ℝ)) branch_51_negative
                have weighted_2 := mul_pos (by norm_num : 0 < (27 / 100 : ℝ)) negative
                have identity : (27 / 250 : ℝ) * ((-7 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) + (177 / 500 : ℝ) * ((-27 / 50 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (27 / 20 : ℝ)) + (27 / 100 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-843 / 500 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, weighted_2, identity]
        ·
          have branch_50_negative : 0 < ((13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-183 / 100 : ℝ)) := by linarith only [branch_50]
          by_cases branch_55 : 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-23 / 125 : ℝ))
          ·
            by_cases branch_56 : 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (249 / 100 : ℝ))
            ·
              apply adjacentR3_hit_boundary square fits 17
              change 0 ≤ ((13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-183 / 100 : ℝ)) ∧ 0 ≤ ((-9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (249 / 100 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-23 / 125 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_50_negative.le
              ·
                exact branch_56
              ·
                exact branch_55
            ·
              have branch_56_negative : 0 < ((9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (-249 / 100 : ℝ)) := by linarith only [branch_56]
              by_cases branch_57 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 45
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-21 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (-249 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (13 / 50 : ℝ)) branch_49
                  have weighted_1 := mul_pos (by norm_num : 0 < (7 / 25 : ℝ)) branch_50_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (27 / 100 : ℝ)) negative
                  have identity : (13 / 50 : ℝ) * ((-7 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-21 / 100 : ℝ)) + (7 / 25 : ℝ) * ((13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-183 / 100 : ℝ)) + (27 / 100 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_57
                  have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
                ·
                  exact branch_56_negative.le
              ·
                have branch_57_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_57]
                apply adjacentR3_hit_boundary square fits 31
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
                refine ⟨?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (4 / 5 : ℝ)) branch_55
                  have weighted_1 := mul_pos (by norm_num : 0 < (3 / 5 : ℝ)) branch_57_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (64 / 125 : ℝ)) negative
                  have identity : (4 / 5 : ℝ) * ((16 / 25 : ℝ) * square.center.x + (-3 / 5 : ℝ) * square.center.y + (-23 / 125 : ℝ)) + (3 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (64 / 125 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_57_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
          ·
            have branch_55_negative : 0 < ((-16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (23 / 125 : ℝ)) := by linarith only [branch_55]
            by_cases branch_58 : 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ))
            ·
              by_cases branch_59 : 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (259 / 125 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 18
                change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (259 / 125 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (-3 / 10 : ℝ) * square.center.y + (-539 / 500 : ℝ)) ∧ 0 ≤ ((-11 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-63 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_59
                ·
                  by_contra! failed
                  have negative : 0 < ((-43 / 50 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (539 / 500 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (86 / 125 : ℝ)) branch_35_negative
                  have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (3 / 10 : ℝ)) branch_58
                  have weighted_2 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                  have identity : (86 / 125 : ℝ) * ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) + (3 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((-43 / 50 : ℝ) * square.center.x + (3 / 10 : ℝ) * square.center.y + (539 / 500 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((11 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (63 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (47 / 250 : ℝ)) branch_50_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (6 / 25 : ℝ)) branch_55_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (119 / 250 : ℝ)) negative
                  have identity : (47 / 250 : ℝ) * ((13 / 50 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-183 / 100 : ℝ)) + (6 / 25 : ℝ) * ((-16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (23 / 125 : ℝ)) + (119 / 250 : ℝ) * ((11 / 50 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (63 / 100 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                have branch_59_negative : 0 < ((16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-259 / 125 : ℝ)) := by linarith only [branch_59]
                apply adjacentR3_hit_boundary square fits 19
                change 0 ≤ ((-16 / 25 : ℝ) * square.center.x + (3 / 5 : ℝ) * square.center.y + (23 / 125 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-4 / 5 : ℝ) * square.center.y + (12 / 5 : ℝ)) ∧ 0 ≤ ((16 / 25 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (-259 / 125 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_55_negative.le
                ·
                  exact branch_58
                ·
                  exact branch_59_negative.le
            ·
              have branch_58_negative : 0 < ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) := by linarith only [branch_58]
              by_cases branch_60 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 31
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ))
                refine ⟨?_ , ?_ ⟩
                ·
                  exact branch_60
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_58_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (4 / 5 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ)) + (4 / 5 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_60_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) := by linarith only [branch_60]
                apply adjacentR3_hit_boundary square fits 44
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (31 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (4 / 5 : ℝ) * square.center.y + (-12 / 5 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_35_negative.le
                ·
                  exact branch_60_negative.le
                ·
                  exact branch_58_negative.le
      ·
        have branch_49_negative : 0 < ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ)) := by linarith only [branch_49]
        by_cases branch_61 : 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (3051 / 1000 : ℝ))
        ·
          by_cases branch_62 : 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-843 / 500 : ℝ))
          ·
            by_cases branch_63 : 0 ≤ ((0 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ))
            ·
              by_cases branch_64 : 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-61 / 20 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 27
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-61 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
                refine ⟨?_ , ?_ ⟩
                ·
                  exact branch_64
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_63
                  have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ)) + (9 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
              ·
                have branch_64_negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (61 / 20 : ℝ)) := by linarith only [branch_64]
                apply adjacentR3_hit_boundary square fits 36
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-23 / 10 : ℝ)) ∧ 0 ≤ ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (61 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-3 / 4 : ℝ) * square.center.y + (3 / 4 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_35_negative.le
                ·
                  exact branch_64_negative.le
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (3 / 4 : ℝ) * square.center.y + (-3 / 4 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (3 / 4 : ℝ)) branch_63
                  have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                  have identity : (3 / 4 : ℝ) * ((0 : ℝ) * square.center.x + (-9 / 10 : ℝ) * square.center.y + (9 / 10 : ℝ)) + (9 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (3 / 4 : ℝ) * square.center.y + (-3 / 4 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]
            ·
              have branch_63_negative : 0 < ((0 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-9 / 10 : ℝ)) := by linarith only [branch_63]
              apply adjacentR3_hit_boundary square fits 14
              change 0 ≤ ((41 / 50 : ℝ) * square.center.x + (-1 / 5 : ℝ) * square.center.y + (-843 / 500 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (3 / 4 : ℝ) * square.center.y + (-3 / 4 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (3051 / 1000 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_62
              ·
                by_contra! failed
                have negative : 0 < ((0 : ℝ) * square.center.x + (-3 / 4 : ℝ) * square.center.y + (3 / 4 : ℝ)) := by linarith only [failed]
                have weighted_0 := mul_pos (by norm_num : 0 < (3 / 4 : ℝ)) branch_63_negative
                have weighted_1 := mul_pos (by norm_num : 0 < (9 / 10 : ℝ)) negative
                have identity : (3 / 4 : ℝ) * ((0 : ℝ) * square.center.x + (9 / 10 : ℝ) * square.center.y + (-9 / 10 : ℝ)) + (9 / 10 : ℝ) * ((0 : ℝ) * square.center.x + (-3 / 4 : ℝ) * square.center.y + (3 / 4 : ℝ)) = (0 : ℝ) := by
                  ring
                nlinarith only [weighted_0, weighted_1, identity]
              ·
                exact branch_61
          ·
            have branch_62_negative : 0 < ((-41 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (843 / 500 : ℝ)) := by linarith only [branch_62]
            apply adjacentR3_hit_boundary square fits 15
            change 0 ≤ ((1 / 50 : ℝ) * square.center.x + (-7 / 10 : ℝ) * square.center.y + (153 / 125 : ℝ)) ∧ 0 ≤ ((4 / 5 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-117 / 50 : ℝ)) ∧ 0 ≤ ((-41 / 50 : ℝ) * square.center.x + (1 / 5 : ℝ) * square.center.y + (843 / 500 : ℝ))
            refine ⟨?_ , ?_ , ?_ ⟩
            ·
              by_contra! failed
              have negative : 0 < ((-1 / 50 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-153 / 125 : ℝ)) := by linarith only [failed]
              have weighted_0 := mul_pos (by norm_num : 0 < (117 / 200 : ℝ)) branch_49_negative
              have weighted_1 := mul_nonneg (by norm_num : 0 ≤ (93 / 500 : ℝ)) branch_61
              have weighted_2 := mul_pos (by norm_num : 0 < (141 / 250 : ℝ)) negative
              have identity : (117 / 200 : ℝ) * ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ)) + (93 / 500 : ℝ) * ((-41 / 50 : ℝ) * square.center.x + (-11 / 20 : ℝ) * square.center.y + (3051 / 1000 : ℝ)) + (141 / 250 : ℝ) * ((-1 / 50 : ℝ) * square.center.x + (7 / 10 : ℝ) * square.center.y + (-153 / 125 : ℝ)) = (0 : ℝ) := by
                ring
              nlinarith only [weighted_0, weighted_1, weighted_2, identity]
            ·
              exact branch_0_negative.le
            ·
              exact branch_62_negative.le
        ·
          have branch_61_negative : 0 < ((41 / 50 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-3051 / 1000 : ℝ)) := by linarith only [branch_61]
          by_cases branch_65 : 0 ≤ ((-1 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-81 / 100 : ℝ))
          ·
            by_cases branch_66 : 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (18 / 25 : ℝ))
            ·
              apply adjacentR3_hit_boundary square fits 13
              change 0 ≤ ((-1 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-81 / 100 : ℝ)) ∧ 0 ≤ ((-6 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (18 / 25 : ℝ)) ∧ 0 ≤ ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_65
              ·
                exact branch_66
              ·
                exact branch_49_negative.le
            ·
              have branch_66_negative : 0 < ((6 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-18 / 25 : ℝ)) := by linarith only [branch_66]
              by_cases branch_67 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-21 / 10 : ℝ))
              ·
                apply adjacentR3_hit_boundary square fits 45
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-21 / 10 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (3 : ℝ)) ∧ 0 ≤ ((9 / 10 : ℝ) * square.center.x + (-1 / 10 : ℝ) * square.center.y + (-249 / 100 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  exact branch_67
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (7 / 25 : ℝ)) container_1
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_49_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                  have identity : (7 / 25 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 : ℝ) * ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ)) + (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-3 : ℝ)) = (-17 / 100 : ℝ) := by
                    ring
                  have constant_negative := (by norm_num : 0 < (17 / 100 : ℝ))
                  nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((-9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (249 / 100 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (3 / 125 : ℝ)) branch_49_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (211 / 500 : ℝ)) branch_66_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (3 / 25 : ℝ)) negative
                  have identity : (3 / 125 : ℝ) * ((7 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (21 / 100 : ℝ)) + (211 / 500 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-18 / 25 : ℝ)) + (3 / 25 : ℝ) * ((-9 / 10 : ℝ) * square.center.x + (1 / 10 : ℝ) * square.center.y + (249 / 100 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
              ·
                have branch_67_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ)) := by linarith only [branch_67]
                apply adjacentR3_hit_boundary square fits 46
                change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-93 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ)) ∧ 0 ≤ ((6 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-18 / 25 : ℝ))
                refine ⟨?_ , ?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (93 / 50 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (6 / 25 : ℝ)) branch_65
                  have weighted_1 := mul_pos (by norm_num : 0 < (1 / 25 : ℝ)) branch_66_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (3 / 25 : ℝ)) negative
                  have identity : (6 / 25 : ℝ) * ((-1 / 25 : ℝ) * square.center.x + (1 / 2 : ℝ) * square.center.y + (-81 / 100 : ℝ)) + (1 / 25 : ℝ) * ((6 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-18 / 25 : ℝ)) + (3 / 25 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (93 / 50 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  exact branch_67_negative.le
                ·
                  exact branch_66_negative.le
          ·
            have branch_65_negative : 0 < ((1 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (81 / 100 : ℝ)) := by linarith only [branch_65]
            by_cases branch_68 : 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 20 : ℝ) * square.center.y + (2673 / 1000 : ℝ))
            ·
              apply adjacentR3_hit_boundary square fits 16
              change 0 ≤ ((41 / 50 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-3051 / 1000 : ℝ)) ∧ 0 ≤ ((-43 / 50 : ℝ) * square.center.x + (-1 / 20 : ℝ) * square.center.y + (2673 / 1000 : ℝ)) ∧ 0 ≤ ((1 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (81 / 100 : ℝ))
              refine ⟨?_ , ?_ , ?_ ⟩
              ·
                exact branch_61_negative.le
              ·
                exact branch_68
              ·
                exact branch_65_negative.le
            ·
              have branch_68_negative : 0 < ((43 / 50 : ℝ) * square.center.x + (1 / 20 : ℝ) * square.center.y + (-2673 / 1000 : ℝ)) := by linarith only [branch_68]
              by_cases branch_69 : 0 ≤ ((0 : ℝ) * square.center.x + (3 / 4 : ℝ) * square.center.y + (-3 / 4 : ℝ))
              ·
                by_cases branch_70 : 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-93 / 50 : ℝ))
                ·
                  apply adjacentR3_hit_boundary square fits 46
                  change 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-93 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (21 / 10 : ℝ)) ∧ 0 ≤ ((6 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-18 / 25 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_70
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-21 / 10 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 / 25 : ℝ)) container_1
                    have weighted_1 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_65_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) negative
                    have identity : (1 / 25 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (4 : ℝ)) + (1 : ℝ) * ((1 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (81 / 100 : ℝ)) + (1 / 2 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-21 / 10 : ℝ)) = (-2 / 25 : ℝ) := by
                      ring
                    have constant_negative := (by norm_num : 0 < (2 / 25 : ℝ))
                    nlinarith only [weighted_0, weighted_1, weighted_2, constant_negative, identity]
                  ·
                    by_contra! failed
                    have negative : 0 < ((-6 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (18 / 25 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_pos (by norm_num : 0 < (3 / 250 : ℝ)) branch_65_negative
                    have weighted_1 := mul_pos (by norm_num : 0 < (3 / 25 : ℝ)) branch_68_negative
                    have weighted_2 := mul_pos (by norm_num : 0 < (54 / 125 : ℝ)) negative
                    have identity : (3 / 250 : ℝ) * ((1 / 25 : ℝ) * square.center.x + (-1 / 2 : ℝ) * square.center.y + (81 / 100 : ℝ)) + (3 / 25 : ℝ) * ((43 / 50 : ℝ) * square.center.x + (1 / 20 : ℝ) * square.center.y + (-2673 / 1000 : ℝ)) + (54 / 125 : ℝ) * ((-6 / 25 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (18 / 25 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  have branch_70_negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (93 / 50 : ℝ)) := by linarith only [branch_70]
                  apply adjacentR3_hit_boundary square fits 47
                  change 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (93 / 50 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) ∧ 0 ≤ ((43 / 50 : ℝ) * square.center.x + (1 / 20 : ℝ) * square.center.y + (-2673 / 1000 : ℝ))
                  refine ⟨?_ , ?_ , ?_ ⟩
                  ·
                    exact branch_70_negative.le
                  ·
                    by_contra! failed
                    have negative : 0 < ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) := by linarith only [failed]
                    have weighted_0 := mul_nonneg (by norm_num : 0 ≤ (1 : ℝ)) branch_69
                    have weighted_1 := mul_pos (by norm_num : 0 < (3 / 4 : ℝ)) negative
                    have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (3 / 4 : ℝ) * square.center.y + (-3 / 4 : ℝ)) + (3 / 4 : ℝ) * ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ)) = (0 : ℝ) := by
                      ring
                    nlinarith only [weighted_0, weighted_1, identity]
                  ·
                    exact branch_68_negative.le
              ·
                have branch_69_negative : 0 < ((0 : ℝ) * square.center.x + (-3 / 4 : ℝ) * square.center.y + (3 / 4 : ℝ)) := by linarith only [branch_69]
                apply adjacentR3_hit_boundary square fits 27
                change 0 ≤ ((1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (-61 / 20 : ℝ)) ∧ 0 ≤ ((0 : ℝ) * square.center.x + (-1 : ℝ) * square.center.y + (1 : ℝ))
                refine ⟨?_ , ?_ ⟩
                ·
                  by_contra! failed
                  have negative : 0 < ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (61 / 20 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (3 / 4 : ℝ)) branch_61_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (11 / 20 : ℝ)) branch_69_negative
                  have weighted_2 := mul_pos (by norm_num : 0 < (123 / 200 : ℝ)) negative
                  have identity : (3 / 4 : ℝ) * ((41 / 50 : ℝ) * square.center.x + (11 / 20 : ℝ) * square.center.y + (-3051 / 1000 : ℝ)) + (11 / 20 : ℝ) * ((0 : ℝ) * square.center.x + (-3 / 4 : ℝ) * square.center.y + (3 / 4 : ℝ)) + (123 / 200 : ℝ) * ((-1 : ℝ) * square.center.x + (0 : ℝ) * square.center.y + (61 / 20 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, weighted_2, identity]
                ·
                  by_contra! failed
                  have negative : 0 < ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) := by linarith only [failed]
                  have weighted_0 := mul_pos (by norm_num : 0 < (1 : ℝ)) branch_69_negative
                  have weighted_1 := mul_pos (by norm_num : 0 < (3 / 4 : ℝ)) negative
                  have identity : (1 : ℝ) * ((0 : ℝ) * square.center.x + (-3 / 4 : ℝ) * square.center.y + (3 / 4 : ℝ)) + (3 / 4 : ℝ) * ((0 : ℝ) * square.center.x + (1 : ℝ) * square.center.y + (-1 : ℝ)) = (0 : ℝ) := by
                    ring
                  nlinarith only [weighted_0, weighted_1, identity]

end SquarePackingArchive.BentzThirteen
