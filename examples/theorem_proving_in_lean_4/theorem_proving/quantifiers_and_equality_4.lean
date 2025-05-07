
section

  -- always true
  def p : Nat → Prop := λ _ ↦ true

  -- proof for p x for every x
  def hpx {x: Nat} : Nat → p x :=
    λ x ↦ (show p x from rfl)

  -- for every x in Nat, p x
  def q : Prop := ∀ x : Nat, p x

  -- proof for ∀ x : Nat, p x is a function from x to proof of p x
  theorem hq : q :=
    λ x ↦ hpx x
end

section

-- proof for 1 = 1
example: 1 = 1 := Eq.refl 1

end

#check Exists.intro
