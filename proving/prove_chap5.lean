-- different versions of one proof in tactic mode

-- proofs with the or connective
example (p q : Prop) : p ∨ q → q ∨ p := by
intro h
apply Or.elim h
intro hp
exact Or.intro_right q hp
intro hq
exact Or.intro_left p hq

example (p q : Prop) : p ∨ q → q ∨ p := by
intro h
cases h
apply Or.intro_right
assumption
apply Or.intro_left
assumption

example (p q : Prop) : p ∨ q → q ∨ p := by
intro h
cases h with
  | inl hp => apply Or.intro_right
              exact hp
  | inr hq => apply Or.intro_left
              exact hq

example (p q : Prop) : p ∨ q → q ∨ p := by
intro h
cases h with
  | inl => apply Or.intro_right
           assumption
  | inr => apply Or.intro_left
           assumption

-- proofs with the and connective

example (p q : Prop) : p ∧ q → q ∧ p := by
intro h
apply And.intro
exact h.right
exact h.left

example (p q : Prop) : p ∧ q → q ∧ p := by
intro h  
cases h
apply And.intro
repeat assumption

example (p q : Prop) : p ∧ q → q ∧ p := by
intro h  
cases h with
| intro hp hq => exact (And.intro hq hp)

example (p q : Prop) : p ∧ q → q ∧ p := by
intro h  
cases h with
| intro => apply And.intro
           repeat assumption

example (p q : Prop) : p ∧ q → q ∧ p :=
fun h => And.intro h.right h.left