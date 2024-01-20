import NaturalNumberGame.N

open N

/- # rfl: reflexivity -/
-- #1: 37x + q = 37x + q
example (x q : N) : seven * five * x + q = seven * five * x + q := by
  rfl

/- # rw: rewrite -/
-- #2: 2y = 2(x + 7), where h : y = x + 7
example (x y : N) (h : y = x + seven) : two * y = two * (x + seven) := by
  rw [h]

-- #3: 2 = s (s z), by: s 1 = s (s z); s (s 0) = s (s z);
example : two = s (s z) := by
  rw [two_eq_s_one]
  rw [one_eq_s_z]

-- #4: 2 = s (s z), by: 2 = s 1; 2 = s (s 0);
example : two = s (s z) := by
  rw [← one_eq_s_z]
  rw [← two_eq_s_one]

-- #5: a + (b + 0) + (c + 0) = a + b + c
example (a b c : N) : a + (b + z) + (c + z) = a + b + c := by
  rw [add_z, add_z]

-- #6: a + (b + 0) + (c + 0) = a + b + c
example (a b c : N) : a + (b + z) + (c + z) = a + b + c := by
  rw [add_z c]
  rw [add_z b]

-- #7: s n = n + 1
example (n : N) : s n = n + one := by
  rw [one_eq_s_z]
  rw [add_s]
  rw [add_z]

-- #8: 2 + 2 = 4
example : two + two = four := by
  rw [two_eq_s_one]
  rw [one_eq_s_z]
  rw [add_s, add_s]
  rw [add_z]
  rw [four_eq_s_three, three_eq_s_two, two_eq_s_one, one_eq_s_z]
