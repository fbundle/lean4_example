-- calculation proof also works for inequalities or any transitive relation

section CalculationProofTransitive
  variable (a b c d : Nat)
  variable (h1 : a = b)
  variable (h2 : b ≤ c)
  variable (h3 : c + 1 < d)

  -- example using `calc` to show inequality
  example  : a < d :=
    calc
      a = b     := h1
      _ < b + 1 := Nat.lt_succ_self b -- `Nat.lt_succ_self a` gives a proof for `a < a + 1`
      _ ≤ c + 1 := Nat.succ_le_succ h2 -- `Nat.succ_le_succ` gives a proof for `n.succ ≤ m.succ` from `n ≤ m`
      _ < d     := h3


  -- `x` divides `y` as natural numbers
  def divides (x y : Nat) : Prop := ∃ k: Nat, k*x = y

  -- transitivity of `divides` - I don't understand this at the moment
  def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
    have ⟨k₁, d₁⟩ := h₁ -- `k₁: Nat` and `d₁: k₁ * x = y` is a proof for `k₁ * x = y`
    have ⟨k₂, d₂⟩ := h₂ -- `k₂: Nat` and `d₂: k₂ * y = z` is a proof for `k₂ * y = z`
    ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

  -- `x` divides `k * x`
  def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
    ⟨k, rfl⟩

  -- declaring `divides` as a transitive relation
  instance : Trans divides divides divides where
    trans := divides_trans

  -- example using `calc`
  example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
    calc
      divides x y     := h₁
      _ = z           := h₂
      divides _ (2*z) := divides_mul ..
end CalculationProofTransitive
