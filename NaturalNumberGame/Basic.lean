import Mathlib.Tactic.Contrapose

inductive Natural : Type
| zero : Natural
| succ : Natural → Natural
deriving Repr, DecidableEq

namespace Natural

def add : Natural → Natural → Natural
| a, zero => a
| a, succ b => succ (add a b)

instance : Add Natural where
  add := Natural.add

def mul : Natural → Natural → Natural
| _, zero => zero
| a, succ b => add a (mul a b)

instance : Mul Natural where
  mul := Natural.mul

def pred : Natural → Natural
| zero => zero
| succ a => a

def zero? : Natural → Prop
| zero => True
| succ _ => False

def one   : Natural := succ zero
def two   : Natural := succ one
def three : Natural := succ two
def four  : Natural := succ three
def five  : Natural := succ four
def six   : Natural := succ five
def seven : Natural := succ six
def eight : Natural := succ seven
def nine  : Natural := succ eight
def ten   : Natural := succ nine

theorem one_eq_succ_zero    : one   = succ zero  := rfl
theorem two_eq_succ_one     : two   = succ one   := rfl
theorem three_eq_succ_two   : three = succ two   := rfl
theorem four_eq_succ_three  : four  = succ three := rfl
theorem five_eq_succ_four   : five  = succ four  := rfl
theorem six_eq_succ_five    : six   = succ five  := rfl
theorem seven_eq_succ_six   : seven = succ six   := rfl
theorem eight_eq_succ_seven : eight = succ seven := rfl
theorem nine_eq_succ_eight  : nine  = succ eight := rfl
theorem ten_eq_succ_nine    : ten   = succ nine  := rfl

variable (a b c : Natural)

theorem succ_eq_add_one : succ a = a + one := rfl

theorem pred_succ : pred (succ a) = a := rfl

theorem succ_inj (h : succ a = succ b) : a = b := by
  rw [← pred_succ a, ← pred_succ b, h]

theorem succ_ne_succ (h : a ≠ b) : succ a ≠ succ b := by
  contrapose! h
  apply succ_inj
  exact h

theorem zero_zero? : zero? zero = True := rfl
theorem zero_succ? : zero? (succ a) = False := rfl

-- see also:
-- https://proofassistants.stackexchange.com/a/1664
-- https://proofassistants.stackexchange.com/a/2626
-- https://proofassistants.stackexchange.com/a/2625
theorem zero_ne_succ : zero ≠ succ a := by
  intro h
  rw [← zero_succ? a, ← h, zero_zero?]
  trivial

theorem succ_ne_zero : succ a ≠ zero := by
  intro h
  rw [← zero_succ? a, h, zero_zero?]
  trivial

theorem add_zero : a + zero = a := rfl
theorem add_succ : a + succ b = succ (a + b) := rfl

theorem zero_add : zero + a = a := by
  induction a with
  | zero => rfl
  | succ _ ih => rw [add_succ, ih]

theorem succ_add : succ a + b = succ (a + b) := by
  induction b with
  | zero => rfl
  | succ _ ih => rw [add_succ, ih, add_succ]

theorem add_comm : a + b = b + a := by
  induction a with
  | zero => rw [add_zero, zero_add]
  | succ _ ih => rw [add_succ, succ_add, ih]

theorem add_assoc : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ _ ih => rw [add_succ, add_succ, ih, add_succ]

theorem add_right_comm : (a + b) + c = (a + c) + b := by
  rw [add_assoc, add_assoc, add_comm b c]

theorem add_left_comm : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

theorem add_right_cancel : a + c = b + c → a = b := by
  induction c with
  | zero => simp [add_zero]
  | succ => simp [add_succ]; assumption

theorem add_left_cancel : c + a = c + b → a = b := by
  induction c with
  | zero => simp [zero_add]
  | succ => simp [succ_add]; assumption

theorem add_right_eq_self : a + b = a → b = zero := by
  induction a with
  | zero => simp [zero_add]
  | succ => simp [succ_add]; assumption

theorem add_left_eq_self : a + b = b → a = zero := by
  induction b with
  | zero => simp [add_zero]
  | succ => simp [add_succ]; assumption

-- NOTE: can be solved with: `cases b <;> simp [add_zero, add_succ]`
theorem add_right_eq_zero : a + b = zero → a = zero := by
  cases b
  simp [add_zero]
  intro h
  rw [add_succ] at h
  symm at h
  contrapose h
  apply zero_ne_succ

theorem add_left_eq_zero : a + b = zero → b = zero := by
  cases a
  simp [zero_add]
  intro h
  rw [succ_add] at h
  contrapose h
  apply succ_ne_zero

syntax (name := simp_add) "simp_add" : tactic
macro_rules | `(tactic| simp_add) => `(tactic| (simp only [add_assoc, add_left_comm, add_comm]))

end Natural
