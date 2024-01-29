import NaturalNumberGame.N

open N

-- #1: a + n = b + n ⇒ a = b
example (a b n : N) : a + n = b + n → a = b := by
  apply add_right_cancel

-- #2: n + a = n + b ⇒ a = b
example (a b n : N) : n + a = n + b → a = b := by
  apply add_left_cancel

-- #3: a + b = b ⇒ a = 0
example (a b : N) : a + b = b → a = z := by
  apply add_left_eq_self

-- #4: a + b = a ⇒ b = 0
example (a b : N) : a + b = a → b = z := by
  apply add_right_eq_self

/- # cases -/
-- #5: a + b = 0 ⇒ a = 0
example (a b : N) : a + b = z → a = z := by
  apply add_right_eq_z

-- #6: a + b = 0 ⇒ b = 0
example (a b : N) : a + b = z → b = z := by
  apply add_left_eq_z
