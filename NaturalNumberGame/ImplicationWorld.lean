import NaturalNumberGame.Basic

open Natural

variable (a b c : Natural)

/- # exact -/
-- 1
example (h : a + b = (three * ten + seven)) : a + b = (three * ten + seven) := by exact h

-- #2: a = b + 2
example (h : zero + a = zero + b + two) : a = b + two := by
  repeat rw [zero_add] at h
  exact h

/- # apply -/
-- 3
example
  (h₁ : a = (three * ten + seven))
  (h₂ : a = (three * ten + seven) → b = (four * ten + two))
  : b = (four * ten + two) := by
  apply h₂
  exact h₁

/- # injection -/
-- 4
example (h : a + one = four) : a = three := by
  rw [four_eq_succ_three] at h
  rw [← succ_eq_add_one] at h
  apply succ_inj
  exact h

-- 5
example (h : a + one = four) : a = three := by
  apply succ_inj
  rw [succ_eq_add_one]
  rw [← four_eq_succ_three]
  exact h

/- # intro -/
-- 6
example : a = (three * ten + seven) → a = (three * ten + seven) := by
  intro h
  exact h

-- 7
example : a + one = b + one → a = b := by
  intro h
  apply succ_inj
  repeat rw [succ_eq_add_one]
  exact h

-- 8
example (h₁ : a = b) (h₂ : a ≠ b) : False := by
  apply h₂
  exact h₁

-- 9
example : zero ≠ one := by
  apply zero_ne_succ

-- 10
example : one ≠ zero := by
  apply succ_ne_zero

-- 11
example : succ (succ zero) + succ (succ zero) ≠ succ (succ (succ (succ (succ zero)))) := by
  intro h
  rw [succ_add, succ_add, zero_add] at h
  cases h
