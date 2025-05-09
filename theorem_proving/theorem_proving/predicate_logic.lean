namespace PredicateLogic

/-
`Prop` is an object at `universe level 1` which is the same level with `Nat`. An element (in `universe level 0`) of `universe Prop` is called a proposition. For example, `True`, `1 + 1 = 3`, `Fermat's last theorem`.

Curry–Howard (CH) asserts that proving a proposition `p: Prop` is equivalent to constructing a term `x: p` at `universe level -1`. Hence, a proposition `p: Prop` is said to be true if and only if there exists an element  `x: p`, we say that the truth of `p: Prop` is `witnessed` by the proof `x: p` or `x: p` is a `certificate` for the truth of `p: Prop`.

We say `p: Prop` is `inhabited` if there is a proof for `p: Prop`, `p: Prop` is `uninhabited` if there is no proof for `p: Prop`

The type system in lean is powerful enough to model predicate logic, we will describe below the builtin logical connectives and related `introduction rules` and `elimination rules`. An `introduction rule` is a way to prove `p: Prop` from something else, an `elimination rule` is a way deduce something else from `p: Prop`

-/

-- `False` : type with no
inductive False

inductive True where
  | intro: True







end PredicateLogic
