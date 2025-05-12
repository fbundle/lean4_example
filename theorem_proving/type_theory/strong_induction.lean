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
  let h₃ : ¬ (∀ (a : α), p a) ↔ ¬ (∀ (a: α), ¬ ¬ p a) := Iff.not h₃
  exact h₁.mp (h₃.mp h₂)
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
    if h₂ : is_prime n then
      exact Exists.intro n (And.intro h₂ (divide_rfl n))
    else -- `h₂: ¬ is_prime n`
      let h₃ : ∃ (m: Nat), ¬(m ∣ n → ¬ (2 ≤ m ∧ m < n)) := cl_1 (cl_3 h₂ h₁)
      obtain ⟨(m: Nat), (hm : ¬(m ∣ n → ¬(2 ≤ m ∧ m < n)))⟩ := h₃
      let h₄ : m ∣ n ∧ 2 ≤ m ∧ m < n := cl_2 hm
      let m_divides_n : m ∣ n := h₄.left
      let m_ge_2 : 2 ≤ m := h₄.right.left
      let m_lt_n : m < n := h₄.right.right
      if h₅ : is_prime m then
        exact Exists.intro m (And.intro h₅ m_divides_n)
      else -- `h₅ : ¬ is_prime w`
        let h₆ : ∃ l, is_prime l ∧ l ∣ m := ih m m_lt_n m_ge_2
        obtain ⟨(l: Nat), (hl: is_prime l ∧ l ∣ m)⟩ := h₆
        let l_is_prime: is_prime l := hl.left
        let l_divides_m: l ∣ m := hl.right
        let l_divides_n := divide_trans l m n l_divides_m m_divides_n
        exact Exists.intro l (And.intro l_is_prime l_divides_n)

end StrongInduction
