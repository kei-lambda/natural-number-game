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
