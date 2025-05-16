import Mathlib.Data.Set.Basic

section Set

variable {α : Type*}
variable (s t u : Set α)
open Set

example : s ∩ t = t ∩ s := by
  ext x -- make goal `x ∈ s ∩ t ↔ x ∈ t ∩ s`
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

end Set

section Function

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl -- `rfl` is like `by definition`

def g: s → u := sorry




end Function
