# LEAN4_EXAMPLE
some lean4 examples

## INSTALLATION

### INSTALL ELAN

- download `elan` at [https://github.com/leanprover/elan/releases/tag/v4.1.1](https://github.com/leanprover/elan/releases/tag/v4.1.1)

- `bash elan-init.sh` choose `default toolchain: stable` and `modify PATH variable: no`

- `elan` binaries will be stored at `$HOME/.elan`

### CREATE HELLO WORLD PROJECT

```bash
mkdir test
cd test
lake init test
```

- `lake build` - build

- `lake exe test` - build and run

### FOR PROGRAMMERS

- main reference: [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)

- `examples/functional_programming_in_lean/1_getting_to_know_lean` should be sufficient except proving termination of a function (`TODO`)

### FOR MATHEMATICIANS

- main reference: [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)

#### SOME WORDS ON DEPENDENT TYPE THEORY

- [Curry–Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) : there is a one-to-one correspondence between computer programs and mathematical proofs


- consider the set of all formal strings and the semantic equivalence relation on them, for example, `λ (x: Nat) => x + 4` and `fun (y: Nat) => y + 4` are two different strings but have the same semantic.

- we will use the word *object* for both string and its semantic without confusion

- each object in lean belongs to a universe level in type hierarchy, e.g.

    - universe level -1: ...

    - universe level 0: `1`, `1.5`, `"Hello World"`, `1 + 1 = 2` - similar object in programming

    - universe level 1: `Nat`, `Int`, `String`, `Prop` - similar to type in programming

    - universe level 2: `Sort 1` (or `Type 0`)

    - universe level 3: `Sort 2` (or `Type 1`)

    - universe level 4: ...

- there is a function `t` that maps object at level `k` to level `k+1` which, to the best of my knowledge, is not exposed to user in `lean`. but an equivalent version in `python` is `type`, in `javascript` is `typeof`. We say that `x` is of type `y` if `t(x) = y`

- if `α` and `β` are objects at level `k`, then `α → β` is also an object at level `k`. in mathematics, `α → β` is like $\mathrm{Hom}(\alpha, \beta)$ which is the collection of all morphisms from $\alpha$ to $\beta$

- `α → β → γ ≅ α × β → γ` - this is just the tensor-hom adjunction

- `Prop` is called proposition which is at level 1 which is the same level with `Int`, `Float`, `String`

- `1 + 1 = 2` is a proposition asserting if `1 + 1` equals to `2`. `1 + 1 = 2` is of type `Prop` 

- if `x` is of type `α`, we write `x` as `x: α` to denote its *type*

- in constructive mathematics, a proposition is true if and only if we can construct a proof for it

- in `lean`, a proposition `p: Prop` is true if and only if we can construct an object `hp` at level -1 of type `p`

- theorem proving in `lean` is basically constructing objects at level -1 using programming rules

