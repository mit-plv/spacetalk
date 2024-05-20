
theorem Nat.zero_lt_ten : 0 < 10 := by simp
theorem Nat.one_lt_ten : 1 < 10 := by simp
theorem Nat.two_lt_ten : 2 < 10 := by simp
theorem Nat.three_lt_ten : 3 < 10 := by simp
theorem Nat.four_lt_ten : 4 < 10 := by simp
theorem Nat.five_lt_ten : 5 < 10 := by simp
theorem Nat.six_lt_ten : 6 < 10 := by simp
theorem Nat.seven_lt_ten : 7 < 10 := by simp
theorem Nat.eight_lt_ten : 8 < 10 := by simp
theorem Nat.nine_lt_ten : 9 < 10 := by simp

theorem Nat.two_gt_one : 2 > 1 := by simp
theorem Nat.nine_gt_one : 9 > 1 := by simp
theorem Nat.three_gt_one : 3 > 1 := by simp
theorem Nat.three_gt_zero : 3 > 0 := by simp
theorem Nat.two_gt_zero : 2 > 0 := by simp
theorem Nat.six_gt_five : 6 > 5 := by simp
theorem Nat.seven_gt_five : 7 > 5 := by simp
theorem Nat.five_gt_four : 5 > 4 := by simp
theorem Nat.nine_gt_four : 9 > 4 := by simp
theorem Nat.six_gt_four : 6 > 4 := by simp
theorem Nat.four_gt_three : 4 > 3 := by simp
theorem Nat.eight_gt_three : 8 > 3 := by simp

theorem Fin.gt_of_val_gt {a b : Fin n} : a.val > b.val → a > b := by intro h; exact h
