

section

variable (p q : Prop)
-- commutativity of ∧
example: (p ∧ q) → (q ∧ p) :=
  λ (hpq: p ∧ q) =>
    let hp := And.left hpq
    let hq := And.right hpq
    And.intro hq hp

-- commutativity of ∨
example : (p ∨ q) → (q ∨ p) :=
  λ (hpq: p ∨ q) =>
    Or.elim hpq -- proof for p ∨ q
      (λ hp => Or.intro_right q hp) -- proof for p → (q ∨ p)
      (λ hq => Or.intro_left p hq) -- proof for q → (p ∨ q)
end

-- negation of p and p is a contradiction
example : ¬(¬p ∧ p) :=
  λ (h: ¬p ∧ p) =>
    let hnp := And.left h
    let hp := And.right h
    hnp hp -- or write `absurd hp hnp` or `False.elim (hnp hp)`

-- implies anything from a contradiction
example : (¬ p ∧ p) → q :=
  λ (h: ¬p ∧ p) =>
    let hnp := And.left h
    let hp := And.right h
    absurd hp hnp -- or write `absurd hp hnp` or `False.elim (hnp hp)`

-- logcal equivalence
-- p ∧ q ↔ q ∧ p
example : p ∧ q ↔ q ∧ p :=
  ⟨λ hpq => And.intro (And.right hpq) (And.left hpq), λ hqp => And.intro (And.right hqp) (And.left hqp)⟩

/-



-- TODO : finish all sorry proofs in this file

section
  variable (p q r : Prop)

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := sorry
  example : p ∨ q ↔ q ∨ p := sorry

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  example : ¬(p ∧ ¬p) := sorry
  example : p ∧ ¬q → ¬(p → q) := sorry
  example : ¬p → (p → q) := sorry
  example : (¬p ∨ q) → (p → q) := sorry
  example : p ∨ False ↔ p := sorry
  example : p ∧ False ↔ False := sorry
  example : (p → q) → (¬q → ¬p) := sorry

end

section

  open Classical

  variable (p q r : Prop)

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
  example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
  example : ¬(p → q) → p ∧ ¬q := sorry
  example : (p → q) → (¬p ∨ q) := sorry
  example : (¬q → ¬p) → (p → q) := sorry
  example : p ∨ ¬p := sorry
  example : (((p → q) → p) → p) := sorry


end

-/
