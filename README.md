
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
