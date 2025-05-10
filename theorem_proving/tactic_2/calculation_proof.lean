

/-
Let `a` and `b` be any objects, then `a = b` is a proposition (also written as `Eq a b`). `Eq` admits several properties

- `Eq.refl`: Let `a` be any object, then `Eq.refl a: a = a` is a proof

- `Eq.symm`: Let `hab: a = b` be a proof, then `Eq.symm hab: b = a` is also a proof

- `Eq.trans`: Let `hab: a = b`, `hbc: b = c` be proofs, then `Eq.trans hab hbc: a = c` is also a proof


In proving equality, lean provides several substitution rules

- `Eq.subst`: Let `x: $\alpha$` and `y: $\alpha$`. Let `h: a = b` be a proof and `p: $\alpha \to$ Prop`, then if `hx: p x` is a proof, then `Eq:subst: p y` is also a proof

- `congrArg`: Let `x: $\alpha$` and `y: $\alpha$`. Let `h: a = b` be a proof and `f: $\alpha \to \beta$`, then `congrArg f h: f x = f y` is a proof

- `congrFun`: Let `f: $\alpha \to \beta$` and `g: $\alpha \to \beta$`. Let `h: f = g` and `x: $\alpha$`, then `congrFun h x: f x = g x` is a proof

- `congr`: Let `x: $\alpha$` and `y: $\alpha$`. Let `f: $\alpha \to \beta$` and `g: $\alpha \to \beta$`. Let `h\_1: x = y` and `h\_2: f = g`, then `congr h\_2 h\_1: f x = g y` is a proof
-/

section CalculationProof
  -- TODO: implement `Eq` as an inductive type


  variable (a b c d e: Nat)
  variable (h1: a = b)
  variable (h2: b = c + 1)
  variable (h3: c = d)
  variable (h4: e = 1 + d)

  -- example using `calc` to show equality
  example : a = e := by
  calc
    a = b := h1
    _ = c + 1 := h2
    _ = d + 1 := congrArg (λ x => x + 1) h3   -- `congrArg` is used to apply a function to both sides of an equation
    _ = 1 + d := Nat.add_comm d 1             -- `Nat.add_comm a b` gives a proof for `a + b = b + a`
    _ = e := Eq.symm h4

  -- example using `calc` to show equality with `rewrite` tactic
  example : a = e := by
  calc
    a = b := by rw [h1]
    _ = c + 1 := by rw [h2]
    _ = d + 1 := by rw [h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e := by rw [h4]

  -- example using `simp` tactic to simplify `calc` proof with `rewrite`
  example : a = e := by
    simp [h1, h2, h3, Nat.add_comm, h4]


end CalculationProof
