inductive N : Type
| z : N
| s : N → N
deriving Repr

open N

def N.add : N → N → N
| m, z => m
| m, s n => s (add m n)

def N.mul : N → N → N
| _, z => z
| m, s n => add m (mul m n)

instance : Add N where
  add := N.add

instance : Mul N where
  mul := N.mul

def zero  : N := z
def one   : N := s zero
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

theorem N.add_z (n : N) : n + z = n := rfl
theorem N.add_s (m n : N) : m + s n = s (m + n) := rfl

theorem N.z_add (n : N) : z + n = n := by
  induction n with
  | z => rfl
  | s n ih => rw [add_s, ih]

theorem N.s_add (m n : N) : s m + n = s (m + n) := by
  induction n with
  | z => rfl
  | s n ih => rw [add_s, ih, add_s]

theorem N.add_comm (a b : N) : a + b = b + a := by
  induction a with
  | z => rw [add_z, z_add]
  | s n ih => rw [add_s, s_add, ih]
