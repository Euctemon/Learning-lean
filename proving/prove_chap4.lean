variable {x : Type}
variable {p q : x → Prop}

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
intro h1 h2 r
exact ((h1 r) (h2 r))