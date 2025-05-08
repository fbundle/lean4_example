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

See [docs](https://khanh101.github.io/lean4_example/docs/main.html)

