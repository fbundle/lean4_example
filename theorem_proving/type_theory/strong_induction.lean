import Mathlib.Logic.Basic

section StrongInduction

def is_prime (n: Nat): Prop := by
  exact (2 ≤ n) ∧ (∀ (m: Nat), m ∣ n → ¬ (2 ≤ m ∧ m < n))

-- from classical logic
def l1 {α : Sort u} {p: α → Prop}: ¬ (∀ (a: α), p a) → (∃ (a: α), ¬ p a) := by sorry

def l2: ¬ (p ∧ q) → p → ¬ q := by
  intro h hp hq
  exact h (And.intro hp hq)

def l3: ∀ (n: Nat), n ∣ n := by sorry

def l4: ∀ (m n l: Nat), m ∣ n → n ∣ l → m ∣ l := by sorry

def l5 {p q: Prop}: ¬ (p → ¬ q) → p ∧ q := by
  intro h
  have h₁ : ¬(p → ¬q) ↔ p ∧ ¬¬q := _root_.not_imp
  have h₂ : p ∧ ¬¬q := h₁.mp h
  have hp : p := h₂.left
  have h₃ : ¬¬q → q := _root_.of_not_not
  have hq : q := h₃ h₂.right
  exact And.intro hp hq


theorem prime_decomposition: ∀ (n: Nat), (2 ≤ n) → ∃ (m: Nat), (is_prime m) ∧ (m ∣ n) := by
  intro n -- `n: Nat`
  -- `h₀` strong induction hypothesis
  have h₀ : ∀ (m: Nat), (m < n) → (m ≥ 2) → ∃ (l: Nat), (is_prime l) ∧ (l ∣ m) := by sorry
  intro h₁ -- `h₁: 2 ≤ n`
  by_cases h₂ : is_prime n
  case pos => -- `h₂: is_prime n`
    exact Exists.intro n (And.intro h₂ (l3 n))
  case neg => -- h₂: `¬is_prime n`
    have h₃ : ¬ (∀ (m: Nat), m ∣ n → ¬ (2 ≤ m ∧ m < n)) := l2 h₂ h₁
    have h₄ : ∃ (m: Nat), ¬(m ∣ n → ¬ (2 ≤ m ∧ m < n)) := by exact l1 h₃
    cases h₄ with
      | intro w hw => -- `hw : ¬(w ∣ n → ¬ (1 < w ∧ w < n)`
        have hw₀ : w ∣ n ∧ 1 < w ∧ w < n := l5 hw
        have hw₁ : w ∣ n := hw₀.left
        have hw₂ : 1 < w ∧ w < n := hw₀.right
        by_cases hw₃ : is_prime w
        case pos => -- `hw₄ : is_prime w`
          exact Exists.intro w (And.intro hw₃ hw₁)
        case neg => -- `hw₄ : ¬ is_prime w`
          have hv₀ : (w < n) → (w ≥ 2) → ∃ (l: Nat), (is_prime l) ∧ (l ∣ w) := h₀ w
          have hv₁ : ∃ l, is_prime l ∧ l ∣ w := (hv₀ hw₂.right) hw₂.left
          cases hv₁ with
          | intro v hv => -- `hv : is_prime v ∧ v ∣ w`
            have hv₁: is_prime v := hv.left
            have hv₂: v ∣ w := hv.right
            have v_divides_n := l4 v w n hv₂ hw₁
            exact Exists.intro v (And.intro hv₁ v_divides_n)

end StrongInduction
