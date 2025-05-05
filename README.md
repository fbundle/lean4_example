some lean4 examples

# INSTALLATION

## INSTALL ELAN

- download `elan` at [https://github.com/leanprover/elan/releases/tag/v4.1.1](https://github.com/leanprover/elan/releases/tag/v4.1.1)

- `bash elan-init.sh` choose `default toolchain: stable` and `modify PATH variable: no`

- `elan` binaries will be stored at `$HOME/.elan`

## CREATE HELLO WORLD PROJECT

```bash
mkdir test
cd test
lake init test
```

- `lake build` - build

- `lake exe test` - build and run

# FOR PROGRAMMERS

main reference: [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/). `examples/functional_programming_in_lean/1_getting_to_know_lean` should be sufficient except proving termination of a function (`TODO`)

# FOR MATHEMATICIANS

main reference: [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)

## SOME WORDS ON DEPENDENT TYPE THEORY

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

- in `lean`, a proposition `p: Prop` is true if and only if we can construct an object `hp` (at level -1) of type `p`. that is, the truth of `p` is witnessed by constructing `hp`

- theorem proving in `lean` is essentially programming, that is to construct objects at level -1 using programming convention

## PROPOSITIONAL LOGIC

```lean
Not: Prop → Prop
And: Prop × Prop → Prop
Or: Prop × Prop → Prop
Implies: Prop × Prop → Prop
Iff: Prop × Prop → Prop
```

Below, `p, q, r: Prop` are of type `Prop`

### NOT

- `Not` accepts a proposition and returns a proposition

    - write `Not p` or `¬p`
    
    - note that `Not p` is just `p → False`

### CONJUNCTION (AND)

- `And` accepts two propositions and return a proposition

    - write `And p q` or `p ∧ q`

- *and-introduction* rule: `And.intro: p × q → p ∧ q` accepts two proofs for `p` and `q` then returns a proof for `p ∧ q`

- note that, `let x := And.intro hp hq` can be also written as `let x: And := ⟨hp, hq⟩`

- *and-elimination* rule: `And.left: p ∧ q → p` or `And.right: p ∧ q → q` accept a proof for proposition `p ∧ q` then return a proof for proposition `p` or `q`

### DISJUNCTION (OR)

- *or-introduction* rule: `Or.intro_left: p → p ∨ q` or `Or.intro_right: q → p ∨ q` accept a proof for proposition `p` or `q` then return a proof for proposition `p ∨ q`

- *or-elimination* rule: `Or.elim: (p ∨ q) × (p → r) × (q → r) → r` accepts a proof for `p ∨ q`, a proof for `p → r`, and a proof for `q → r`, then returns a proof for  