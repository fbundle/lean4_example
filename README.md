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

- consider the set of all formal strings and the semantic equivalence relation on them, for example, `λ (n: Nat) => n + 4`
