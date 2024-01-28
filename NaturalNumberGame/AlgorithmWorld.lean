import NaturalNumberGame.N

open N

-- #1: a + (b + c) = b + (a + c)
example (a b c : N) : a + (b + c) = b + (a + c) := by
  rw [add_left_comm]

-- #2: (a + b) + (c + d) = ((a + c) + d) + b
example (a b c d : N) : (a + b) + (c + d) = ((a + c) + d) + b := by
  repeat rw [add_assoc]
  rw [add_comm d b]
  rw [add_left_comm c b]

/- # simp -/
-- #3: (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h
example
  (a b c d e f g h : N)
  : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_assoc, add_left_comm, add_comm]

-- #4: (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h
example
  (a b c d e f g h : N)
  : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp_add

-- #5: s a = s b ⇒ a = b
example (a b : N) (h : s a = s b) : a = b := by
  apply s_inj
  exact h

/- # trivial -/
-- #6: s a ≠ 0
example (a : N) : s a ≠ z := by apply s_ne_z

/- # contrapose -/
-- #7: a ≠ b ⇒ s a ≠ s b
example (a b : N) (h : a ≠ b) : s a ≠ s b := by
  apply s_ne_s
  exact h

/- # decide -/
-- #8: 20 + 20 = 40
example : (two * ten) + (two * ten) = (four * ten) := by decide

-- #9: 2 + 2 ≠ 5
example : two + two ≠ five := by decide
