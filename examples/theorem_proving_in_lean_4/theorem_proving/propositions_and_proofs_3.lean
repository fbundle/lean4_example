

section

-- commutativity of ∧
def and_comm1: (p ∧ q) → (q ∧ p) :=
  λ (hpq: p ∧ q) =>
    let hp := And.left hpq
    let hq := And.right hpq
    And.intro hq hp

-- commutativity of ∨
def or_comm1: (p ∨ q) → (q ∨ p) :=
  λ (hpq: p ∨ q) =>
    Or.elim hpq -- proof for p ∨ q
      (λ hp => Or.intro_right q hp) -- proof for p → (q ∨ p)
      (λ hq => Or.intro_left p hq) -- proof for q → (p ∨ q)

-- negation of p and p is a contradiction
def contr_implies_false: ¬(¬p ∧ p) :=
  λ (h: ¬p ∧ p) =>
    let hnp := And.left h
    let hp := And.right h
    hnp hp -- or write `absurd hp hnp` or `False.elim (hnp hp)`

-- implies anything from a contradiction
def contr_implies_anything : (¬ p ∧ p) → q :=
  λ (h: ¬p ∧ p) =>
    let hnp := And.left h
    let hp := And.right h
    absurd hp hnp -- or write `absurd hp hnp` or `False.elim (hnp hp)`


-- logical equivalence
example : (p ∧ q) ↔ (q ∧ p) :=
  Iff.intro and_comm1 and_comm1
end

-- subgoal
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left -- same as `let hp := And.left h`
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

-- subgoal
example (h : p ∧ q) : q ∧ p :=
  -- we already show p here by certificate hp
  have hp : p := h.left
  -- it suffices to show q because we can show q ∧ p from two certificates hq and hp
  suffices hq : q from And.intro hq hp
  show q from And.right h

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

-- always true
def p : Nat → Prop := λ _ => true

-- for every x in Nat, p x
def q := ∀ x : Nat, p x

theorem hq : q :=
  λ x => (show p x from rfl) -- λ n => (a proof for p n)

#check hq



#check p