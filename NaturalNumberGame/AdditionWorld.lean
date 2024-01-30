import NaturalNumberGame.Basic

open Natural

variable (a b c : Natural)

/- # induction -/
-- 1
example : zero + a = a := by
  induction a with
  | zero => rfl
  | succ _ ih => rw [add_succ, ih]

-- 2
example : succ a + b = succ (a + b) := by
  induction b with
  | zero => rfl
  | succ _ ih => rw [add_succ, ih, add_succ]

-- 3
example : a + b = b + a := by
  induction a with
  | zero => rw [add_zero, zero_add]
  | succ _ ih => rw [add_succ, succ_add, ih]

-- 4
example : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ _ ih => rw [add_succ, add_succ, ih, add_succ]

-- 5
example : (a + b) + c = (a + c) + b := by
  rw [add_assoc, add_assoc, add_comm b c]
