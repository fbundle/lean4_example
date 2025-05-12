-- the import order is also the reading order
import type_theory.dependent_type_theory
import type_theory.inductive_type
import type_theory.predicate_logic

import tactic.calculation_proof
import tactic.calculation_proof_for_transitivity
import tactic.auxiliary_subgoals
import tactic.tactic

import Mathlib.Logic.Basic

def l5 {p q: Prop}: ¬ (p → ¬ q) → p ∧ q := by
  intro h
  have h₁ : ¬(p → ¬q) ↔ p ∧ ¬¬q := Mathlib.Logic.Basic.not_imp
  exact sorry

def main : IO Unit :=
  IO.println s!"Hello, World!"
