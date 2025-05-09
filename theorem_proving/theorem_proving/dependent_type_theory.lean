namespace DependentTypeTheory

/-
BASIC DEPENDENT TYPE THEORY

Consider the set of all formal strings `S` and the sematic equivalence relation `∼` on `S`. For example, `λ (x: Nat) → x + 4` and `fun (y: Nat) => y + 4` are two different strings but have the same semantic. We will use the same word `object` for both syntactic string and its meaning without confusion

In lean, every object longs to a `universe level`, below are some examples

- `universe level -1`: proofs
- `universe level 0`: `1`, `-2`, `1.4`, `"hello word"`, `λ (x: Nat) → x + 4`
- `universe level 1`: `Nat`, `Int`, `Float`, `String`, `Nat → Nat`
- `universe level 2`: `Type` (aka `Type 0` or `Sort 1`)
- `universe level 3`: `Type 1` (aka `Sort 2`)
- ...

Moreover, every object has a type, that is a function `t` that maps object from `universe level n` to `universe level n+1`. In programming, this is called getting type of (`type` in Python, `typeof` in Javascript). For example, `t(1) = Nat`, `t(true) = Bool`, `t(λ (x: Nat) => x + 4) = Nat → Nat`. Let `α` be any object at `universe level n+1`, the collection of all objects in `universe level n` of type `α` is called the `universe α`. For example, `universe Nat` consists of of all natural numbers. We write `x : Nat` to denote `x` is of type `Nat` and `x` is called a `term` (or `element` of `Nat`)

In lean, `t` is not exposed to user. However, during compilation process, lean allows user to print value and type of an object using `#eval` and `#check`
-/

#eval 20
#check 20

/-
ARROW TYPE

If `α` and `β` are two objects at `universe level n` and `universe level m` respectively, then `α → β` is an object at `universe level max(n, m)`. We will call it `arrow type`. when `f` is of arrow type `α → β`, we write `f : α → β` (or `f (a: α) : β` like function in programming)

Moreover, lean allows user to define dependent type, for example `g (α: Type) (b: β): γ α b` where `γ α b` is another object. A more concrete example is `make_vector (α: Type) (n: Nat): Vector α n` which is a function creating a vector of dimension `n` of type `α`
-/

inductive Vector (α : Type u) : Nat → Type u
| nil  : Vector α 0
| cons {n: Nat} : α → Vector α n → Vector α (n + 1)


def make_vector (α: Type) (n: Nat) [Inhabited α]: Vector α n :=
  match n with
  | 0 => Vector.nil
  | m+1 => Vector.cons default (make_vector α m)

end DependentTypeTheory
