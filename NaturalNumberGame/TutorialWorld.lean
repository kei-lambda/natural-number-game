import NaturalNumberGame.Basic

open Natural

variable (a b c : Natural)

/- # rfl: reflexivity -/
-- 1
example : seven * five * a + b = seven * five * a + b := by
  rfl

/- # rw: rewrite -/
-- 2
example (h : b = a + seven) : two * b = two * (a + seven) := by
  rw [h]

-- 3
example : two = succ (succ zero) := by
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]

-- 4
example : two = succ (succ zero) := by
  rw [← one_eq_succ_zero]
  rw [← two_eq_succ_one]

-- 5
example : a + (b + zero) + (c + zero) = a + b + c := by
  rw [add_zero, add_zero]

-- 6
example : a + (b + zero) + (c + zero) = a + b + c := by
  rw [add_zero c]
  rw [add_zero b]

-- 7
example : succ a = a + one := by
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]

-- 8
example : two + two = four := by
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  rw [add_succ, add_succ]
  rw [add_zero]
  rw [four_eq_succ_three, three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]
