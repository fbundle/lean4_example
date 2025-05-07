
## AUXILIARY SUBGOALS

```lean
section
-- subgoal
example {p q: Prop} (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left -- same as `let hp := And.left h`
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

-- subgoal
example {p q: Prop} (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  -- it suffices to show hq: q because we can show q ∧ p from two certificates hq and hp
  suffices hq : q from And.intro hq hp
  show q from And.right h
end
```

## CLASSICAL LOGIC

classical logic assumes [Law of excluded middle](https://en.wikipedia.org/wiki/Law_of_excluded_middle) (`em`), that is, `p ∨ ¬p` is always `True`. Moreover, law of excluded middle is true if and only if principle of double-negation elimination (`dne`) is true, that is `¬¬p → p`.

Use `open Classical` to use classical logic

- `em: Prop → Prop`, `em p` is precisely `p ∨ ¬p`


# PREDICATE LOGIC

## UNIVERSAL QUANTIFIER (FOR ALL)

in `lean`, the object `(∀ x : α, p x): Prop` is a proposition where `p: α → Prop` is a map from type `α` to `Prop`, a proof for `(∀ x : α, p x)` is `h: α → p x` which sends each element `x` of type `α` into a proof for `p x: Prop`

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

`Eq` accepts two objects and return a proposition, write `Eq a b` or `a = b`

- *reflexsive*: `Eq.refl: α → (a = a)` accepts an object `a` and returns a proof for `a = a`

- *symmetric*: `Eq.symm: (a = b) → (b = a)` accepts a proof for `a = b` and returns a proof for `b = a`

- *transitive*: `Eq.trans: (a = b) × (b = c) → (a = c`) accepts two proofs for `a = b` and `b = c` and returns a proof for `a = c`







































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
