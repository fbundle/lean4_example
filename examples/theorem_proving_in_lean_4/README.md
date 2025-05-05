# test

- use `lake build` to build

## SOME WORDS ON DEPENDENT TYPE THEORY

- the type of every usual type (`Int`, `Float`, etc) is `Type = Type 0`, hence usual type is `Type -1 = Sort 0`

- type of `Type 0` is `Type 1`, type of `Type u` is `Type (u + 1)`

- `α → β` is `Hom(α, β)`

- `α → β → γ ≅ α × β → γ` : tensor-hom adjunction

- `Sort 1 = Type 0`, `Sort u = Type (u-1)`

- `Prop` is proposition

- [Curry–Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) : there is a one-to-one correspondence between between computer programs and mathematical proofs

- `Prop` is a usual type just like `Int`, type of `Prop` is `Sort 1 = Type 0 = Type`

- `let p : Prop := 1 + 1 = 2`, `p` is the proposition `1 + 1 = 2`, type of `p` is `Prop`

- consider `p` as a type, `let hp : p := rfl`, `hp` is a proof for `p`, that is, type of `hp` is `p`

- a proposition is true if and only if there exists a proof for that proposition. in lean language, `p : Prop` is true of and only if we can construct an element `hp: p` of type `p`.

## PROPOSITIONAL LOGIC


## PREDICATE LOGIC

