section
  -- subgoal
  example {p q: Prop} (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left -- same as let hp := And.left h
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

  -- subgoal
  example {p q: Prop} (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  -- it suffices to show hq: q because we can show q ∧ p from two certificates hq and hp
  suffices hq : q from And.intro hq hp
  show q from And.right h
end
