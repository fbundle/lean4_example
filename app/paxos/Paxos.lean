structure Acceptor (α: Type) where
  promise: Nat
  value: Option α

def Acceptor.prepare {α: Type} (a: Acceptor α) (proposal: Nat): (Acceptor α) × Nat × (Option α) × Bool :=
  if proposal ≤ a.promise then
    (a, a.promise, a.value, false)
  else
    let new_a: Acceptor α := {
      promise := proposal,
      value := a.value,
    }
    (new_a, a.promise, a.value, true)

def Acceptor.accept {α: Type} (a: Acceptor α) (proposal: Nat) (value: α): (Acceptor α) × Bool :=
  if proposal < a.promise then
    (a, false)
  else
    let new_a: Acceptor α := {
      promise := proposal,
      value := value,
    }
    (new_a, true)

def propose {α: Type} (as: List (Acceptor α)) (proposal: Nat) (value: α): Bool :=
  -- prepare phase
  let rs := as.map ((λ (a: Acceptor α) =>
    a.prepare proposal
  ): Acceptor α → (Acceptor α) × Nat × (Option α) × Bool)

  let as: List (Acceptor α) := rs.map ((λ (r: (Acceptor α) × Nat × (Option α) × Bool) =>
    let (a, _, _, _) := r
    a
  ): (Acceptor α) × Nat × (Option α) × Bool) → Acceptor α))
