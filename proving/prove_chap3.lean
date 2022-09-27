variable (p q r : Prop)

example : p ∧ q ↔ q ∧ p :=
Iff.intro
(fun hl : p ∧ q => show q ∧ p from And.intro (And.right hl) (And.left hl))
(fun hr : q ∧ p => show p ∧ q from And.intro (And.right hr) (And.left hr))

example : p ∨ q ↔ q ∨ p :=
Iff.intro
(fun x : p ∨ q => Or.elim x (fun hp : p => show q ∨ p from Or.intro_right q hp)
                            (fun hq : q => show q ∨ p from Or.intro_left p hq))
(fun x : q ∨ p => Or.elim x (fun hq : q => show p ∨ q from Or.intro_right p hq)
                            (fun hq : p => show p ∨ q from Or.intro_left q hq))

example : p ∨ q ↔ q ∨ p :=
Iff.intro
(fun x : p ∨ q => Or.elim x (fun hp : p => show q ∨ p from Or.intro_right q hp)
                            (fun hq : q => show q ∨ p from Or.intro_left p hq))
(fun x : q ∨ p => Or.elim x (fun hq : q => show p ∨ q from Or.intro_right p hq)
                            (fun hq : p => show p ∨ q from Or.intro_left q hq))
