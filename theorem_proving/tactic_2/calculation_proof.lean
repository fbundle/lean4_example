section
  variable (a b c d e: Nat)
  variable (h1: a = b)
  variable (h2: b = c + 1)
  variable (h3: c = d)
  variable (h4: e = 1 + d)

  -- example using `calc` to show equality
  example : a = e := by
  calc
    a = b := h1
    _ = c + 1 := h2
    _ = d + 1 := congrArg (λ x => x + 1) h3   -- `congrArg` is used to apply a function to both sides of an equation
    _ = 1 + d := Nat.add_comm d 1             -- `Nat.add_comm a b` gives a proof for `a + b = b + a`
    _ = e := Eq.symm h4

  -- example using `calc` to show equality with `rewrite` tactic
  example : a = e := by
  calc
    a = b := by rw [h1]
    _ = c + 1 := by rw [h2]
    _ = d + 1 := by rw [h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e := by rw [h4]

  -- example using `simp` tactic to simplify `calc` proof with `rewrite`
  example : a = e := by
    simp [h1, h2, h3, Nat.add_comm, h4]
end
