-- Enumerated Types

-- Constructors with Arguments

-- Inductively Defined Propositions

-- Subtype

-- Defining the Natural Numbers



namespace Hidden

-- `cases` and `match` are the same thing
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n with -- decompose `n: Nat` into two cases
    | zero =>
      exact hz
    | succ m =>
      exact hs m

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  match n with -- decompose `n: Nat` into two cases
    | Nat.zero =>
      exact hz
    | Nat.succ m =>
      exact hs m

-- example for induction proof
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]
end Hidden
