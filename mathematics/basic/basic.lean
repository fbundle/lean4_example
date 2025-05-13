import Mathlib.Algebra.Ring.Basic

section Ring
  -- let `R` be an associative unital ring
  variable (R : Type*) [Ring R]

  #check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
  #check (add_comm : ∀ a b : R, a + b = b + a)
  #check (zero_add : ∀ a : R, 0 + a = a)
  #check (neg_add_cancel : ∀ a : R, -a + a = 0)
  #check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
  #check (mul_one : ∀ a : R, a * 1 = a)
  #check (one_mul : ∀ a : R, 1 * a = a)
  #check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
  #check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

  theorem neg_add_cancel_left1 (a b : R) : -a + (a + b) = b := by
    calc
      - a + (a + b) = -a + a + b := by rw[← add_assoc]
      _ = 0 + b := by rw [neg_add_cancel]
      _ = b := by rw [zero_add]

  theorem add_neg_cancel_right1 (a b : R) : a + b + -b = a := by
    calc
      a + b + -b = a + (b + -b) := by rw[add_assoc]
      _ = a + (-b + b) := by rw [add_comm]
      _ = a + 0 := by rw [neg_add_cancel]
      _ = 0 + a := by rw [add_comm]
      _ = a := by rw [zero_add]


end Ring

section CommRing
  -- let `R` be an commutative unital ring
  variable (R : Type*) [CommRing R]

  #check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
  #check (add_comm : ∀ a b : R, a + b = b + a)
  #check (zero_add : ∀ a : R, 0 + a = a)
  #check (neg_add_cancel : ∀ a : R, -a + a = 0)
  #check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
  #check (mul_one : ∀ a : R, a * 1 = a)
  #check (one_mul : ∀ a : R, 1 * a = a)
  #check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
  #check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
  #check (mul_comm: ∀ a b : R, a * b = b * a)

end CommRing
