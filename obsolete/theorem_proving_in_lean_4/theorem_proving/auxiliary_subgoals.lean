section
  -- subgoal example 1
  example {p q: Prop} (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left           -- same as let `hp := And.left h`
  have hq : q := h.right          -- same as let `hq := And.right h`
  show q ∧ p from And.intro hq hp -- same as `And.intro hq hp`

  -- subgoal example 2
  example {p q: Prop} (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left           -- same as let `hp := And.left h`
  -- instead of showing `hq: q`, we assume `hq: q` and show `And.intro hq hp: q ∧ p` first
  suffices hq : q from And.intro hq hp
  show q from And.right h         -- now we show `hq: q`
end
