namespace Contradiction

def l1 : ∀ (a: Int), a ∣ 2 → a * a ∣ 4 := by
  intro a
  intro h
  obtain ⟨ x, h₁ ⟩ := h
  let h₂: 4 = (a * a) * (x * x) := by
    calc
      4 = 2 * 2 := by rfl
      _ = a * x * (a * x) := by rw[h₁]
      _ = a * x * a * x := by rw[← Int.mul_assoc (a * x) a x]
      _ = a * (x * a) * x := by rw[Int.mul_assoc a x a]
      _ = a * (a * x) * x := by rw[Int.mul_comm x a]
      _ = a * a * x * x := by rw[Int.mul_assoc a a x]
      _ = (a * a) * (x * x) := by rw[Int.mul_assoc (a * a) x x]

  exact Exists.intro (x * x) h₂

def coprime (a b : Int): Prop := ¬ (∃ (k: Int), 2 ≤ k ∧ a ∣ k ∧ b ∣ k)

def root2_not_rational : ¬ (∃ (a b : Int), coprime a b ∧ a * a = 2 * b * b) := by
  intro h₀
  obtain ⟨ a , h₁ ⟩ := h₀
  obtain ⟨ b , h₂ ⟩ := h₁
  let h_gcd := h₂.left
  let h_ratio := h₂.right
  if h : a ∣ 2 then
    let h_a2_divides_4 : a*a ∣ 4 := l1 a h
    if hh : b ∣ 2 then
      let two_le_two : (2: Int) ≤ 2 := by simp
      let two_divdes_a_and_b : a ∣ 2 ∧ b ∣ 2 := And.intro h hh
      let x : ∃ (k: Int), 2 ≤ k ∧ a ∣ k ∧ b ∣ k := Exists.intro 2 (And.intro two_le_two two_divdes_a_and_b)
      exact h_gcd x
    else

      sorry
  else
    sorry



end Contradiction
