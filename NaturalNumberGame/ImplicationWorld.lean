import NaturalNumberGame.N

open N

/- # exact -/
-- #1: x + y = 37
example
  (x y z : N)
  (h₁ : x + y = (three * ten + seven))
  (h₂ : three * x + z = (four * ten + two))
  : x + y = (three * ten + seven) := by
  exact h₁

-- #2: x = y + 2
example (x y : N) (h : z + x = z + y + two) : x = y + two := by
  repeat rw [z_add] at h
  exact h

/- # apply -/
-- #3: x = 37 ⇒ y = 42
example
  (x y : N)
  (h₁ : x = (three * ten + seven))
  (h₂ : x = (three * ten + seven) → y = (four * ten + two))
  : y = (four * ten + two) := by
  apply h₂
  exact h₁

/- # injection -/
-- #4: x + 1 = 4 ⇒ x = 3
example (x : N) (h : x + one = four) : x = three := by
  rw [four_eq_s_three] at h
  rw [← s_eq_add_one] at h
  apply s_inj
  exact h

-- #5: x + 1 = 4 ⇒ x = 3 (backwards)
example (x : N) (h : x + one = four) : x = three := by
  apply s_inj
  rw [s_eq_add_one]
  rw [← four_eq_s_three]
  exact h

/- # intro -/
-- #6: x = 37 ⇒ x = 37
example (x : N) : x = (three * ten + seven) → x = (three * ten + seven) := by
  intro h
  exact h

-- #7: x + 1 = y + 1 ⇒ x = y
example (x y : N) : x + one = y + one → x = y := by
  intro h
  apply s_inj
  repeat rw [s_eq_add_one]
  exact h

-- #8: x = y ⇒ x ≠ y → False
example (x y : N) (h₁ : x = y) (h₂ : x ≠ y) : False := by
  apply h₂
  exact h₁

-- #9: 0 ≠ 1
example : z ≠ one := by
  apply z_ne_s

-- #10: 1 ≠ 0
example : one ≠ z := by
  apply s_ne_z

-- #11: 2 + 2 ≠ 5
example : s (s z) + s (s z) ≠ s (s (s (s (s z)))) := by
  intro h
  rw [s_add, s_add, z_add] at h
  injection h with h₁
  injection h₁ with h₂
  injection h₂ with h₃
  injection h₃ with h₄
  injection h₄
