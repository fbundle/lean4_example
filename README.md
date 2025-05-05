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

- [Curry–Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) : there is a one-to-one correspondence between between computer programs and mathematical proofs


- consider the set of all formal strings and the semantic equivalence relation on them, for example, `λ (x: Nat) => x + 4` and `fun (y: Nat) => y + 4` are two different strings but have the same semantic.

- we will use the word expression for both string and its semantic without confusion

- each expression in lean belongs to a level in type hierarchy, e.g.

    - level -1: ...

    - level 0: `1`, `1.5`, `"Hello World"`, `1 + 1 = 2` - like literals in programming

    - level 1: `Int`, `Float`, `String`, `Prop`

    - level 2: `Sort 1` (or `Type 0`)

    - level 3: `Sort 2` (or `Type 1`)

    - level 4: ...

- there is a function that maps expression at level `k` to level `k+1` which is, to the best of my knowledge, not specified in `lean`. but an equivalent version in `python` is `type`, in `javascript` is `typeof`

- if `α` and `β` are expressions at level `k`, then `α → β` is also an expression at level `k`. In math, `α → β` is like $\mathrm{Hom}(\alpha, \beta)$ which is the collection of all morphisms from $\alpha$ to $\beta$

- `α → β → γ = α × β → γ` - this is just the tensor-hom adjunction

- `Prop` is at level 1 which is the same level with `Int`, `Float`, `String`, 

