variable (p q r : Prop)

example : p ∧ q ↔ q ∧ p := Iff.intro
(fun hpq : p ∧ q => show q ∧ p from And.intro (And.right hpq) (And.left hpq))
(fun hqp : q ∧ p => show p ∧ q from And.intro (And.right hqp) (And.left hqp))

example : p ∨ q ↔ q ∨ p := Iff.intro
(fun hpq : p ∨ q => Or.elim hpq
   (fun hp : p => show q ∨ p from Or.intro_right q hp)
   (fun hq : q => show q ∨ p from Or.intro_left p hq))
(fun hqp : q ∨ p => Or.elim hqp
   (fun hq : q => show p ∨ q from Or.intro_right p hq)
   (fun hq : p => show p ∨ q from Or.intro_left q hq))

-- first version of a proof
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
Iff.intro
(fun hpq : (p ∧ q) ∧ r => show p ∧ (q ∧ r) from And.intro (hpq.left.left) (And.intro hpq.left.right hpq.right))
(fun hqp : p ∧ (q ∧ r) => show (p ∧ q) ∧ r from And.intro (And.intro hqp.left hqp.right.left) hqp.right.right)

-- same proof using subgoals
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := Iff.intro
(fun impl_left : (p ∧ q) ∧ r =>
   have hpq : (p ∧ q) := impl_left.left
   have hqr : (q ∧ r) := And.intro hpq.right impl_left.right
   show p ∧ (q ∧ r) from And.intro (hpq.left) hqr)
(fun impl_right : p ∧ (q ∧ r) =>
   have hqr : (q ∧ r) := impl_right.right
   have hpq : (p ∧ q) := And.intro impl_right.left hqr.left
   show (p ∧ q) ∧ r from And.intro hpq hqr.right)


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := Iff.intro
(fun impl_left : (p ∨ q) ∨ r => Or.elim impl_left
   (fun hpq : (p ∨ q) => Or.elim hpq
      (fun hp : p => show p ∨ (q ∨ r) from Or.intro_left (q ∨ r) hp)
      (fun hq : q =>
         have hqr : q ∨ r := Or.intro_left r hq
         show p ∨ (q ∨ r) from Or.intro_right p hqr))
   (fun hqp : r =>
      have hqr : q ∨ r := Or.intro_right q hqp
      show p ∨ (q ∨ r) from Or.intro_right p hqr))
(fun impl_right : p ∨ (q ∨ r) => Or.elim impl_right
   (fun hp : p =>
      have hpq : p ∨ q := Or.intro_left q hp
      show (p ∨ q) ∨ r from Or.intro_left r hpq)
   (fun hqr : q ∨ r => Or.elim hqr 
      (fun hq : q =>
         have hpq : p ∨ q := Or.intro_right p hq
         show (p ∨ q) ∨ r from Or.intro_left r hpq)
      (fun hqp : r => show (p ∨ q) ∨ r from Or.intro_right (p ∨ q) hqp)))

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := Iff.intro
(fun impl_left : p ∧ (q ∨ r) =>
   have hp : p := impl_left.left
   Or.elim impl_left.right
      (fun hq : q =>
         have hpq : p ∧ q := And.intro hp hq
         show (p ∧ q) ∨ (p ∧ r) from Or.intro_left (p ∧ r) hpq)
      (fun hqp : r =>
         have hpr : p ∧ r := And.intro hp hqp
         show (p ∧ q) ∨ (p ∧ r) from Or.intro_right (p ∧ q) hpr))
(fun impl_right : (p ∧ q) ∨ (p ∧ r) => Or.elim impl_right
   (fun hpq : p ∧ q =>
      have hqr : q ∨ r := Or.intro_left r hpq.right
      show p ∧ (q ∨ r) from And.intro hpq.left hqr)
   (fun hpr : p ∧ r =>
      have hqr : q ∨ r := Or.intro_right q hpr.right
      show p ∧ (q ∨ r) from And.intro hpr.left hqr))
