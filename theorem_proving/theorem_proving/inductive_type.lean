namespace InductiveType

/-
Inductive type is a very powerful notion that can be generalize greatly. Any inductive type is constructed as follows:

inductive Foo where
  | constructor₁ : ... → Foo
  | constructor₂ : ... → Foo
  ...
  | constructorₙ : ... → Foo

Below are some examples of inductive types
-/


-- finite list of terms
inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday


-- `Bool` is defined by
inductive Bool where
  | false : Bool
  | true  : Bool

-- use match to process each constructor separately
def and (a b: Bool): Bool :=
  match a with
    | Bool.true => b
    | Bool.false => Bool.false

-- type can have arguments
-- `Prod α β ≡ α × β`, `Prod.mk a b ≡ (a, b)`
inductive Prod (α : Type u) (β : Type v) where
  | mk : α → β → Prod α β

-- `Sum α β ≡ α ⊕ β`
inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β

-- `structure` is actually product type
-- `Color1 ≡ Color2`
inductive Color1 where
  | mk (red: Nat) (green: Nat) (blue: Nat): Color1

structure Color2 where
  red: Nat
  green: Nat
  blue: Nat

-- more complex examples with type dependent
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α

def option_nat_none : Option Nat := Option.none
def inhatbited_nat_2 : Inhabited Nat := Inhabited.mk 2

-- natural numbers
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

-- `add` inductively
def add (x : Nat) (y: Nat) : Nat :=
  match y with
  | Nat.zero   => x
  | Nat.succ z => Nat.succ (add x z)

-- proving `0 + y = y`
theorem add_zero (y: Nat): add Nat.zero y = y :=
  by
  induction y with -- use induction to get `ih: add Nat.zero z = z`
    | zero => rfl
    | succ z ih =>
      calc
        add Nat.zero (Nat.succ z) = Nat.succ (add Nat.zero z) := by rfl
        _ = Nat.succ z := by rw [ih]





end InductiveType
