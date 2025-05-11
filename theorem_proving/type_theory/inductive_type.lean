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

def is_prime (n: Nat): Prop := by
  exact (2 ≤ n) ∧ (∀ (m: Nat), m ∣ n → ¬ (2 ≤ m ∧ m < n))

-- from classical logic
def l1 {α : Sort u} {p: α → Prop}: ¬ (∀ (a: α), p a) → (∃ (a: α), ¬ p a) := by sorry

def l2: ¬ (p ∧ q) → p → ¬ q := by
  intro h hp hq
  exact h (And.intro hp hq)

def l3: ∀ (n: Nat), n ∣ n := by sorry

def l4: ∀ (m n l: Nat), m ∣ n → n ∣ l → m ∣ l := by sorry

theorem prime_decomposition: ∀ (n: Nat), (2 ≤ n) → ∃ (m: Nat), (is_prime m) ∧ (m ∣ n) := by
  intro n -- `n: Nat`
  -- `h₀` strong induction hypothesis
  have h₀ : ∀ (m: Nat), (m < n) → (m ≥ 2) → ∃ (l: Nat), (is_prime l) ∧ (l ∣ m) := by sorry
  intro h₁ -- `h₁: 2 ≤ n`
  by_cases h₂ : is_prime n
  case pos => -- `h₂: is_prime n`
    exact Exists.intro n (And.intro h₂ (l3 n))
  case neg => -- h₂: `¬is_prime n`
    have h₃ : ¬ (∀ (m: Nat), m ∣ n → ¬ (2 ≤ m ∧ m < n)) := l2 h₂ h₁
    have h₄ : ∃ (m: Nat), ¬(m ∣ n → ¬ (2 ≤ m ∧ m < n)) := by exact l1 h₃
    cases h₄ with
      | intro w hw => -- `hw : ¬(w ∣ n → ¬ ((1 < w) ∧ (w < n)))`
        have hw₀ : w ∣ n ∧ 1 < w ∧ w < n := by sorry -- rewrite hw
        have hw₁ : w ∣ n := hw₀.left
        have hw₂ : 1 < w ∧ w < n := hw₀.right
        by_cases hw₃ : is_prime w
        case pos => -- `hw₄ : is_prime w`
          exact Exists.intro w (And.intro hw₃ hw₁)
        case neg => -- `hw₄ : ¬ is_prime w`
          have hv₀ : (w < n) → (w ≥ 2) → ∃ (l: Nat), (is_prime l) ∧ (l ∣ w) := h₀ w
          have hv₁ : ∃ l, is_prime l ∧ l ∣ w := (hv₀ hw₂.right) hw₂.left
          cases hv₁ with
          | intro v hv => -- `hv : is_prime v ∧ v ∣ w`
            have hv₁: is_prime v := hv.left
            have hv₂: v ∣ w := hv.right
            have v_divides_n := l4 v w n hv₂ hw₁
            exact Exists.intro v (And.intro hv₁ v_divides_n)

end StrongInduction
