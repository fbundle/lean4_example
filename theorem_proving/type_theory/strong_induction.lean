import Mathlib.Tactic.Tauto
section StrongInduction

def is_prime (n: Nat): Prop :=
  2 ≤ n ∧ ∀ (m: Nat), m ∣ n → ¬ (2 ≤ m ∧ m < n)

-- some truth in classical logic
def cl_1 {α : Sort u} {p: α → Prop}: ¬ (∀ (a: α), p a) → (∃ (a: α), ¬ p a) := by
  let h₁ : ¬ (∀ (a: α), ¬ ¬ p a) ↔ (∃ (a: α), ¬ p a) := not_forall_not
  intro (h₂: ¬ (∀ (a : α), p a))
  let h₃ : (∀ (a : α), p a) ↔ (∀ (a: α), ¬ ¬ p a) :=
    Iff.intro
      λ h a => by exact not_not_intro (h a)
      λ h a => by exact Classical.byContradiction (h a)
  let h₄ : ¬ (∀ (a : α), p a) ↔ ¬ (∀ (a: α), ¬ ¬ p a) := Iff.not h₃
  exact h₁.mp (h₄.mp h₂)
def cl_2 {p q: Prop}: ¬ (p → ¬ q) → p ∧ q := by tauto -- auto prove simple propositions
def cl_3 {p q: Prop}: ¬ (p ∧ q) → p → ¬ q := by tauto -- auto prove simple propositions

-- divide is reflexive `def Nat.dvd (m n : Nat) : Prop := ∃ k, n = m * k`
def divide_rfl: ∀ (n: Nat), n ∣ n := by
  intro n
  let h : n = n * 1 := Eq.symm (Nat.mul_one n)
  exact Exists.intro 1 h

-- divide is transitive
def divide_trans: ∀ (m n l: Nat), m ∣ n → n ∣ l → m ∣ l := by
  intro (m: Nat) (n: Nat) (l: Nat) (hmn: m ∣ n) (hnl: n ∣ l)
  cases hmn with | intro k₁ hk₁ => -- `k₁: Nat`, `hk₁: n = m * k₁`
      cases hnl with | intro k₂ hk₂ => -- `k₂: Nat`, `hk₂: l = n * k₂`
          let k := k₁ * k₂
          let h : l = m * k := by
            calc
              l = n * k₂ := by rw [hk₂]
              _ = m * k₁ * k₂ := by rw[hk₁]
              _ = m * (k₁ * k₂) := by rw[Nat.mul_assoc]
              _ = m * k := by rfl

          exact Exists.intro k h

theorem prime_factor: ∀ (n: Nat), 2 ≤ n → ∃ (m: Nat), is_prime m ∧ m ∣ n := by
  intro (n: Nat) -- wts `2 ≤ n → ∃ m, is_prime m ∧ m ∣ n`
  -- strong induction
  induction n using Nat.strongRecOn with | ind n ih =>
    -- `ih : ∀ (m : ℕ), m < n → 2 ≤ m → ∃ l, is_prime l ∧ l ∣ m`
    -- wts `2 ≤ n → ∃ m, is_prime m ∧ m ∣ n` given `ih`
    intro (h₁: 2 ≤ n)
    by_cases h₂ : is_prime n
    case pos => -- `h₂: is_prime n`
      exact Exists.intro n (And.intro h₂ (divide_rfl n))
    case neg => -- h₂: `¬is_prime n`
      let h₃ : ¬ (∀ (m: Nat), m ∣ n → ¬ (2 ≤ m ∧ m < n)) := (cl_3 h₂) h₁
      let h₄ : ∃ (m: Nat), ¬(m ∣ n → ¬ (2 ≤ m ∧ m < n)) := cl_1 h₃
      cases h₄ with | intro w hw => -- `hw : ¬(w ∣ n → ¬(2 ≤ w ∧ w < n))`
          let hw₀ : w ∣ n ∧ 1 < w ∧ w < n := cl_2 hw
          let hw₁ : w ∣ n := hw₀.left
          let hw₂ : 2 ≤ w ∧ w < n := hw₀.right
          by_cases hw₃ : is_prime w
          case pos => -- `hw₃ : is_prime w`
            exact Exists.intro w (And.intro hw₃ hw₁)
          case neg => -- `hw₃ : ¬ is_prime w`
            let hw₄ : (w < n) → (w ≥ 2) → ∃ (l: Nat), (is_prime l) ∧ (l ∣ w) := ih w
            let hw₅ : ∃ l, is_prime l ∧ l ∣ w := (hw₄ hw₂.right) hw₂.left
            cases hw₅ with | intro v hv => -- `hv : is_prime v ∧ v ∣ w`
              let hv₁: is_prime v := hv.left
              let hv₂: v ∣ w := hv.right
              let v_divides_n := divide_trans v w n hv₂ hw₁
              exact Exists.intro v (And.intro hv₁ v_divides_n)

end StrongInduction
