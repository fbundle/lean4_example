/-
`Prop` is an object at `universe level 1` which is at the same level with `Nat` or `String`. A term of `universe Prop` is called a `proposition`, e.g. `1 + 1 = 3`, `True`, `Fermat's last theorem`

Curry-Howard (CH) asserts that there is an correspondence between mathematical proofs and computer programs. In that correspondence, a mathematical statement is a `proposition` and proving for a mathematical statement is constructing a term for the corresponding `proposition`.

If `hp: p` is a term of proposition `p: Prop`, then we say the truth of `p` is witnessed by `hp` or `hp` is a proof/certificate for the truth of `p`

A proposition `p: Prop` is `inhabited` if and only if it is true.
-/

-- some basic propositions




namespace PredicateLogic

-- `False` is an uninhabited type i.e. there is no proof for `False`
-- `False` implies everything
inductive False
def False.elim {q: Sort u} : (h : False) → q :=
  λ h ↦ nomatch h
example: False → 2 + 2 = 5 := by
  intro h
  exact False.elim h

-- `True` is an inhabited type with a single constructor
-- `trivial` is short for `True.intro`
inductive True where
  | intro : True


-- `Implies p q` is actually `p → q` by `CH`
-- `Implies.elim` proves `q` from `hpq: Implies p q` and `hp: p`
inductive Implies (p: Sort u) (q: Sort v) where
  | intro : (p → q) → Implies p q

def Implies.elim {p: Sort u} {q: Sort v}: Implies p q → p → q := by
  intro hpq hp
  match hpq with
    | intro hpq => exact hpq hp

-- `And p q` also written as `p ∧ q`
-- `And` takes in a pair of proofs for `p` and `q`
-- `And.left` `And.right` extract the proof for `p` and `q`
inductive And (p: Sort u) (q: Sort v) where
  | intro : p → q → And p q

def And.left: And p q → p := by
  intro h
  cases h with
  | intro hp _ => exact hp

def And.right:  And p q → q := by
  intro h
  cases h with
  | intro _ hq => exact hq

-- `Or p q` also written as `p ∨ q`
-- `Or` takes in either proof for `p` or `q`
-- `Or.elim` proves `r` from `p ∨ q`, `p → r` and `q → r`
inductive Or (p: Sort u) (q: Sort v) where
  | inl : p → Or p q
  | inr : q → Or p q

def Or.elim: Or p q → (p → r) → (q → r) → r := by
  intro h hpr hqr
  cases h with
  | inl hp => exact hpr hp
  | inr hq => exact hqr hq

-- `Not p` is actually `p → False`
-- `Not.elim` proves `False` from `hp: p`
inductive Not (p: Sort u) where
  | intro: (p → False) → Not p

def Not.elim: Not p → p → False := by
  intro h hp
  cases h with
  | intro hnp => exact hnp hp

-- `Iff p q` also written as `p ↔ q`
-- `Iff` takes in `p → q` and `q → p`
-- `Iff.mp` and `Iff.mpr` extract the proof for `p → q` and `q → p`
inductive Iff (p: Sort u) (q: Sort v) where
  | intro: (p → q) → (q → p) → Iff p q

def Iff.mp: Iff p q → Implies p q := by
  intro h
  cases h with
    | intro hpq _ => exact Implies.intro hpq

def Iff.mpr: Iff p q → Implies q p := by
  intro h
  cases h with
    | intro _ hqp => exact Implies.intro hqp

-- `Forall` also written as `∀ (a: α), p a`
-- `Forall.elim h a` proves `p a` from `h: Forall α p` and `a: α`
inductive Forall (α: Sort u) (p: α → Sort v) where
  | intro : ((a: α) → p a) → Forall α p

def Forall.elim: Forall α p → (a: α) → p a := by
  intro h a
  match h with
  | intro hap => exact hap a

-- `Exists` also written as `∃ (a: α), p a`
-- `Exists` is constructed from `a: α` and `p a: Prop`
inductive Exists (α: Sort u) (p: α → Sort v)  where
  | intro : (a: α) → (ha: p a) → Exists α p

def Exists.elim: Exists α p → Forall α (λ a => p a → q) → q := by
  intro h hpq
  match h with
  | Exists.intro a ha => exact (Forall.elim hpq a) ha


axiom EM : Forall (Sort u) (λ (p: Sort u) ↦ (Or p (Not p)))

end PredicateLogic
