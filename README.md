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

Basic of `lean4` should by sufficient from the first chapter of [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/). except proving termination of a function (`TODO`)

Examples in `./functional_programming_in_lean` 

# FOR MATHEMATICIANS

After reading the official book [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/title_page.html), I realized that it's mostly junk. One can learn proving in `lean` by reading three main topics:

| Topic                     | Remarks                                                   |
|---------------------------|-----------------------------------------------------------|
| Dependent Type Theory     | universe level, arrow type, proof as construction of term |
| Inductive Type            | a framework to construct type                             |
| Tactic Mode               | an alternative way to write proof                         |
