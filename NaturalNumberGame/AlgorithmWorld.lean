import NaturalNumberGame.Basic

open Natural

variable (a b c d e f g h : Natural)

-- 1
example : a + (b + c) = b + (a + c) := by
  rw [add_left_comm]

-- 2
example : (a + b) + (c + d) = ((a + c) + d) + b := by
  repeat rw [add_assoc]
  rw [add_comm d b]
  rw [add_left_comm c b]

/- # simp -/
-- 3
example : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_assoc, add_left_comm, add_comm]

-- 4
example : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp_add

-- 5
example (h : succ a = succ b) : a = b := by
  apply succ_inj
  exact h

/- # trivial -/
-- 6
example : succ a ≠ zero := by apply succ_ne_zero

/- # contrapose -/
-- 7
example (h : a ≠ b) : succ a ≠ succ b := by
  apply succ_ne_succ
  exact h

/- # decide -/
-- 8
example : (two * ten) + (two * ten) = (four * ten) := by decide

-- 9
example : two + two ≠ five := by decide
