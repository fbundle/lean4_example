namespace PredicateLogic
/-
`Prop` is an object at `universe level 1` which is at the same level with `Nat` or `String`. A term of `universe Prop` is called a `proposition`, e.g. `1 + 1 = 3`, `True`, `Fermat's last theorem`

Curry-Howard (CH) asserts that there is an correspondence between mathematical proofs and computer programs. In that correspondence, a mathematical statement is a `proposition` and proving for a mathematical statement is constructing a term for the corresponding `proposition`.

If `hp: p` is a term of proposition `p: Prop`, then we say the truth of `p` is witnessed by `hp` or `hp` is a proof/certificate for the truth of `p`


A proposition `p: Prop` is `inhabited` if and only if it is true.
-/






end PredicateLogic
