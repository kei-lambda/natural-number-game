inductive N : Type
| z : N
| s : N → N
deriving Repr

open N

def N.add : N → N → N
| z,   n => n
| s m, n => s (m.add n)

def N.mul : N → N → N
| z,   _ => z
| s m, n => n.add (m.mul n)

infixl:65 " + " => N.add
infixl:70 " * " => N.mul

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

theorem N.add_z : ∀ (x : N), x + z = x
| z   => rfl
| s n => by rw [add, add_z n]

theorem N.add_s : ∀ (x y : N), x + (s y) = s (x + y)
| z,   y => rfl
| s x, y => by
  rw [add, add]
  rw [add_s x y]
