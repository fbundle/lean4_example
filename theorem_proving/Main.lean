-- the import order is also the reading order
import type_theory.dependent_type_theory
import type_theory.inductive_type
import type_theory.predicate_logic

import tactic.calculation_proof
import tactic.calculation_proof_for_transitivity
import tactic.auxiliary_subgoals
import tactic.tactic

import Mathlib.Tactic.Tauto
def l5 {p q: Prop}: ¬ (p → ¬ q) → p ∧ q := by
  exact Mathlib.Tactic.Tauto.tauto


def main : IO Unit :=
  IO.println s!"Hello, World!"
