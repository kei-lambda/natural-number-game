import NaturalNumberGame.N

open N

/- # induction -/
-- #1: 0 + n = n
example (n : N) : z + n = n := by
  induction n with
  | z => rfl
  | s n ih => rw [add_s, ih]

-- #2: s m + n = s (m + n)
example (m n : N) : s m + n = s (m + n) := by
  induction n with
  | z => rfl
  | s n ih => rw [add_s, ih, add_s]

-- #3: a + b = b + c
example (a b : N) : a + b = b + a := by
  induction a with
  | z => rw [add_z, z_add]
  | s a ih => rw [add_s, s_add, ih]

-- #4: a + b + c = a + (b + c)
example (a b c : N) : a + b + c = a + (b + c) := by
  induction c with
  | z => rfl
  | s n ih => rw [add_s, add_s, ih, add_s]

-- #5: (a + b) + c = (a + c) + b
example (a b c : N) : (a + b) + c = (a + c) + b := by
  rw [add_assoc, add_assoc, add_comm b c]
