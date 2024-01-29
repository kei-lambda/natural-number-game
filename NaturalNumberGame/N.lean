import Mathlib.Tactic.Contrapose

inductive N : Type
| z : N
| s : N → N
deriving Repr

namespace N

open N

def add : N → N → N
| m, z => m
| m, s n => s (add m n)

def mul : N → N → N
| _, z => z
| m, s n => add m (mul m n)

def pred : N → N
| z => z
| s n => n

def z? : N → Prop
| z => True
| s _ => False

instance : Add N where
  add := add

instance : Mul N where
  mul := mul

def one   : N := s z
def two   : N := s one
def three : N := s two
def four  : N := s three
def five  : N := s four
def six   : N := s five
def seven : N := s six
def eight : N := s seven
def nine  : N := s eight
def ten   : N := s nine

theorem one_eq_s_z       : one   = s z     := rfl
theorem two_eq_s_one     : two   = s one   := rfl
theorem three_eq_s_two   : three = s two   := rfl
theorem four_eq_s_three  : four  = s three := rfl
theorem five_eq_s_four   : five  = s four  := rfl
theorem six_eq_s_five    : six   = s five  := rfl
theorem seven_eq_s_six   : seven = s six   := rfl
theorem eight_eq_s_seven : eight = s seven := rfl
theorem nine_eq_s_eight  : nine  = s eight := rfl
theorem ten_eq_s_nine    : ten   = s nine  := rfl

theorem add_z (n : N)   : n + z   = n         := rfl
theorem add_s (m n : N) : m + s n = s (m + n) := rfl

theorem z_add (n : N) : z + n = n := by
  induction n with
  | z => rfl
  | s n ih => rw [add_s, ih]

theorem s_add (m n : N) : s m + n = s (m + n) := by
  induction n with
  | z => rfl
  | s n ih => rw [add_s, ih, add_s]

theorem add_comm (a b : N) : a + b = b + a := by
  induction a with
  | z => rw [add_z, z_add]
  | s n ih => rw [add_s, s_add, ih]

theorem add_assoc (a b c : N) : a + b + c = a + (b + c) := by
  induction c with
  | z => rfl
  | s n ih => rw [add_s, add_s, ih, add_s]

theorem add_right_comm (a b c : N) : (a + b) + c = (a + c) + b := by
  rw [add_assoc, add_assoc, add_comm b c]

theorem add_left_comm (a b c : N) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, add_comm a b, add_assoc]

theorem pred_s (n : N) : pred (s n) = n     := rfl
theorem z_z?           : z? z       = True  := rfl
theorem z_s?   (n : N) : z? (s n)   = False := rfl

theorem s_inj (a b : N) (h : s a = s b) : a = b := by
  rw [← pred_s a, ← pred_s b, h]

theorem s_eq_add_one (n : N) : s n = n + one := rfl

-- see also:
-- https://proofassistants.stackexchange.com/a/1664
-- https://proofassistants.stackexchange.com/a/2626
-- https://proofassistants.stackexchange.com/a/2625
theorem z_ne_s (n : N) : z ≠ s n := by
  intro h
  rw [← z_s? n, ← h, z_z?]
  trivial

theorem s_ne_z (n : N) : s n ≠ z := by
  intro h
  rw [← z_s? n, h, z_z?]
  trivial

theorem s_ne_s (m n : N) (h : m ≠ n) : s m ≠ s n := by
  contrapose! h
  apply s_inj
  exact h

syntax (name := simp_add) "simp_add" : tactic
macro_rules | `(tactic| simp_add) => `(tactic| (simp only [add_assoc, add_left_comm, add_comm]))

-- NOTE: can be automatically derived using:
-- `deriving instance DecidableEq for N`
instance instDecidableEq : DecidableEq N
| z, z => isTrue <| by
  show z = z
  rfl
| s m, z => isFalse <| by
  show s m ≠ z
  exact s_ne_z m
| z, s n => isFalse <| by
  show z ≠ s n
  exact z_ne_s n
| s m, s n => match instDecidableEq m n with
  | isTrue (h : m = n) => isTrue <| by
    show s m = s n
    rw [h]
  | isFalse (h : m ≠ n) => isFalse <| by
    show s m ≠ s n
    exact s_ne_s m n h

theorem add_right_cancel (a b n : N) : a + n = b + n → a = b := by
  induction n with
  | z => simp [add_z]
  | s => simp [add_s]; assumption

theorem add_left_cancel (a b n : N) : n + a = n + b → a = b := by
  induction n with
  | z => simp [z_add]
  | s => simp [s_add]; assumption

theorem add_left_eq_self (a b : N) : a + b = b → a = z := by
  induction b with
  | z => simp [add_z]
  | s => simp [add_s]; assumption

theorem add_right_eq_self (a b : N) : a + b = a → b = z := by
  induction a with
  | z => simp [z_add]
  | s => simp [s_add]; assumption

-- NOTE: can be solved with: `cases b <;> simp [add_z, add_s]`
theorem add_right_eq_z (a b : N) : a + b = z → a = z := by
  cases b
  simp [add_z]
  intro h
  rw [add_s] at h
  symm at h
  contrapose h
  apply z_ne_s

theorem add_left_eq_z (a b : N) : a + b = z → b = z := by
  cases a
  simp [z_add]
  intro h
  rw [s_add] at h
  contrapose h
  apply s_ne_z

end N
