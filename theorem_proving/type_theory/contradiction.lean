namespace Contradiction

def root2_not_rational: ¬ (∃ (a b : Int), Int.gcd a b = 1 ∧ a * a = 2 * b * b) := by
  intro h₀
  obtain ⟨ a , h₁ ⟩ := h₀
  obtain ⟨ b , h₂ ⟩ := h₁
  let h_gcd := h₂.left
  let h_ratio := h₂.right
  if h : a ∣ 2 then
    sorry
  else
    sorry



end Contradiction
