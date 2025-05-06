main reference: [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)

# SOME WORDS ON DEPENDENT TYPE THEORY

- [Curry–Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) : there is a one-to-one correspondence between computer programs and mathematical proofs


- consider the set of all formal strings and the semantic equivalence relation on them, for example, `λ (x: Nat) => x + 4` and `fun (y: Nat) => y + 4` are two different strings but have the same semantic.

- we will use the word *object* for both the syntactic string and its meaning without confusion

- each object in lean belongs to a universe level in type hierarchy, e.g.

    - universe level -1 (informal): ...

    - universe level 0: objects like `1`, `1.5`, `"Hello World"`, `1 + 1 = 2` - analogous to *value* in programming

    - universe level 1: objectis like `Nat`, `Int`, `String`, `Prop` - analogous to `type` in programming

    - universe level 2: `Sort 1` (aka `Type` or `Type 0`)

    - universe level 3: `Sort 2` (aka `Type 1`)

    - universe level 4: ...

- there is a function `t` that maps object at level `k` to level `k+1` which, to the best of my knowledge, is not exposed to user in `lean`. but an equivalent version in `python` is `type`, in `javascript` is `typeof`. We say that *`x` is of type `α`* if `t(x) = α`

- if `α` and `β` are objects at level `k`, then `α → β` is also an object at level `k`, this is analogous to the hom-set $\mathrm{Hom}(\alpha, \beta)$ in mathematics that is the collection of all morphisms from $\alpha$ to $\beta$

- `α → β → γ ≅ α × β → γ` - tensor-hom adjunction

- the object `Prop` is called proposition which resides at level 1 just like `Nat`, `Int`, `String`, etc.

- the object `1 + 1 = 2` is a proposition asserting if `1 + 1` equals to `2`, it is of type `Prop` 

- if `x` is of type `α`, we write `x` as `x: α` to denote its *type*

- in constructive mathematics, a proposition is true if and only if we can construct a proof for it

- in `lean`, a proposition `p: Prop` is true if and only if we can construct an object `hp` (at level -1) of type `p`. that is, the truth of `p` is witnessed by constructing the certificate `hp`

- theorem proving in `lean` is essentially programming, that is to construct objects at level -1 using programming convention

# PROPOSITIONAL LOGIC

```lean
Not: Prop → Prop
And: Prop × Prop → Prop
Or: Prop × Prop → Prop
Implies: Prop × Prop → Prop
Iff: Prop × Prop → Prop
```

Below, `p, q, r: Prop` are of type `Prop`

## CONJUNCTION (AND)

`And` accepts two propositions and return a proposition, write `And p q` or `p ∧ q`

- *and-introduction* rule: `And.intro: p × q → p ∧ q` accepts two proofs for `p` and `q` then returns a proof for `p ∧ q`

- note that, `let x := And.intro hp hq` can be also written as `let x: And := ⟨hp, hq⟩`

- *and-elimination* rule: `And.left: p ∧ q → p` accept a proof for `p ∧ q` then return a proof for `p`

- *and-elimination* rule: `And.right: p ∧ q → q` accept a proof for `p ∧ q` then return a proof for `q`

```lean
-- commutativity of ∧
def and_comm1: (p ∧ q) → (q ∧ p) :=
  λ (hpq: p ∧ q) =>
    let hp := And.left hpq
    let hq := And.right hpq
    And.intro hq hp
```

## DISJUNCTION (OR)

`Or` accepts two propositions and return a proposition, write `Or p q` or `p ∨ q`

- *or-introduction* rule: `Or.intro_left: Prop × p → p ∨ q` accept `q: Prop` and a proof for `p` then return a proof for `p ∨ q`

- *or-introduction* rule: `Or.intro_left: Prop × q → p ∨ q` accept `p: Prop` and a proof for `q` then return a proof for `p ∨ q`

- if it is inferrable, one can short hand `Or.intro_left` and `Or.intro_right` by `Or.inl: p → p ∨ q` and `Or.inr: q → p ∨ q`

- *or-elimination* rule: `Or.elim: (p ∨ q) × (p → r) × (q → r) → r` accepts a proof for `p ∨ q`, a proof for `p → r`, and a proof for `q → r`, then returns a proof for `r`

```lean
-- commutativity of ∨
def or_comm1: (p ∨ q) → (q ∨ p) :=
  λ (hpq: p ∨ q) =>
    Or.elim hpq -- proof for p ∨ q
      (λ hp => Or.intro_right q hp) -- proof for p → (q ∨ p)
      (λ hq => Or.intro_left p hq) -- proof for q → (p ∨ q)
```

## NEGATION AND FALSIFY (NOT)

`Not` accepts a proposition and returns a proposition, write `Not p` or `¬p`, note that `Not p` is precisely `p → False`

- One can use `absurd` or `False.elim` to derive anything from `False` - see example

```lean
-- negation of p and p is a contradiction
def contr_implies_false: ¬(¬p ∧ p) :=
  λ (h: ¬p ∧ p) =>
    let hnp := And.left h
    let hp := And.right h
    hnp hp -- or write `absurd hp hnp` or `False.elim (hnp hp)`

-- implies anything from a contradiction
def contr_implies_anything : (¬ p ∧ p) → q :=
  λ (h: ¬p ∧ p) =>
    let hnp := And.left h
    let hp := And.right h
    absurd hp hnp -- or write `absurd hp hnp` or `False.elim (hnp hp)`
```

## LOGICAL EQUIVALENCE (IF AND ONLY IF)

`Iff` accepts two propositions and returns a proposition, write `Iff p q` or `p ↔ q`

- *iff-introduction* rule: `Iff.intro: (p → q) × (q → p) → (p ↔ q)` accepts two proofs for `p → q` and `q → p` then return a proof for `p ↔ q`

- *iff-elimination* rule: `Iff.mp: (p ↔ q) → (p → q)` accepts a proof for `p ↔ q` then returns a proof for `p → q`

- *iff-elimination* rule: `Iff.mpr: (p ↔ q) → (q → p)` accepts a proof for `p ↔ q` then returns a proof for `q → p`

```lean
-- logical equivalence
example : (p ∧ q) ↔ (q ∧ p) :=
  Iff.intro and_comm1 and_comm1
end
```

## AUXILIARY SUBGOALS

```lean
-- subgoal
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left -- same as `let hp := And.left h`
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

-- subgoal
example (h : p ∧ q) : q ∧ p :=
  -- we already show p here by certificate hp
  have hp : p := h.left
  -- it suffices to show q because we can show q ∧ p from two certificates hq and hp
  suffices hq : q from And.intro hq hp
  show q from And.right h
```

## CLASSICAL LOGIC

classical logic assumes [Law of excluded middle](https://en.wikipedia.org/wiki/Law_of_excluded_middle) (`em`), that is, `p ∨ ¬p` is always `True`. Moreover, law of excluded middle is true if and only if principle of double-negation elimination (`dne`) is true, that is `¬¬p → p`.

Use `open Classical` to use classical logic

- `em: Prop → Prop`, `em p` is precisely `p ∨ ¬p`


# PREDICATE LOGIC

## UNIVERSAL QUANTIFIER (FOR ALL)

in `lean`, the object `(∀ x : α, p x): Prop` is a proposition where `p: α → Prop` is a map from type `α` to `Prop`, a proof for `(∀ x : α, p x)` is `h: α → Prop` which sends each element `x` of type `α` into a proof for `p x: Prop`

- *introduction rule*: Given a proof of `p x`, in a context where `x : α` is arbitrary, we obtain a proof `∀ x : α, p x`.

- *eliminiation rule*: Given a proof `∀ x : α, p x` and any term `t : α`, we obtain a proof of `p t`.


```lean
-- always true
def p : Nat → Prop := λ _ => true

-- proof for p x for every x
def hpx : Nat → p x :=
  λ x => (show p x from rfl)

-- for every x in Nat, p x
def q : Prop := ∀ x : Nat, p x

-- proof for ∀ x : Nat, p x is a function from x to proof of p x
theorem hq : q :=
  λ x => hpx x
```

## EQUALITY









































# INSTALLATION

## INSTALL ELAN

- download `elan` at [https://github.com/leanprover/elan/releases/tag/v4.1.1](https://github.com/leanprover/elan/releases/tag/v4.1.1)

- `bash elan-init.sh` choose `default toolchain: stable` and `modify PATH variable: no`

- `elan` binaries will be stored at `$HOME/.elan`

## HELLO WORLD

make a hello world project as follows:

```bash
mkdir test
cd test
lake init test
```

execute `lake build` to build. execute `lake exe test` to build and run

# FOR PROGRAMMERS

main reference: [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/). `examples/functional_programming_in_lean` should be sufficient except proving termination of a function (`TODO`)