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


-- `And` and `Or` are actually `Prod` and `Sum`
-- `And a b ≡ a ∧ b`, `Or a b ≡ a ∨ b`

-- proof by `cases`
example: (a ∨ b) → (b ∨ a) := by
  intro h
  cases h with
    | inl ha => exact Or.inr ha
    | inr hb => exact Or.inl hb


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

-- proof by (weak) `induction` for `0 + y = y`
theorem add_zero: (y: Nat) → add Nat.zero y = y := by
  intro y
  -- similar to `cases ` but `induction` gives `ih: add Nat.zero z = z`
  induction y with
    | zero => rfl
    | succ z ih =>
      calc
        add Nat.zero (Nat.succ z) = Nat.succ (add Nat.zero z) := by rfl
        _ = Nat.succ z := by rw [ih]

end InductiveType

section StrongInduction


-- `f n = 1^2 + 2^2 + ... + n^2`
-- `g n = n (n+1) (2n+1) / 6`
def f (n: Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ m => n^2 + f m

def g (n: Nat): Nat :=
  n * (n + 1) * (2 * n + 1) / 6

theorem g_step (m : Nat) : (m + 1)^2 + g m = g (m + 1) := by
  sorry


-- prove that `f n = g n`
example: ∀ (n: Nat), f n = g n := by
  intro n
  induction n with
    | zero => rfl
    | succ m hm =>
      calc
        f (m+1) = (m+1)^2 + f m := by rfl
        _ = (m+1)^2 + g m := by rw [hm]
        _ = g (m+1) := by rw [g_step]






end StrongInduction
