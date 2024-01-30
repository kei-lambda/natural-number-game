import NaturalNumberGame.Basic

open Natural

variable (a b c : Natural)

-- 1
example : a + c = b + c → a = b := by
  apply add_right_cancel

-- 2
example : c + a = c + b → a = b := by
  apply add_left_cancel

-- 3
example : a + b = b → a = zero := by
  apply add_left_eq_self

-- 4
example : a + b = a → b = zero := by
  apply add_right_eq_self

/- # cases -/
-- 5
example : a + b = zero → a = zero := by
  apply add_right_eq_zero

-- 6
example : a + b = zero → b = zero := by
  apply add_left_eq_zero
