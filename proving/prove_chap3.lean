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

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := Iff.intro
(fun impl_left : p ∨ (q ∧ r) => Or.elim impl_left
   (fun hp : p =>
      have hpq : p ∨ q := Or.intro_left q hp
      have hpr : p ∨ r := Or.intro_left r hp
      show (p ∨ q) ∧ (p ∨ r) from And.intro hpq hpr)
   (fun hqr : q ∧ r =>
      have hpq : p ∨ q := Or.intro_right p hqr.left
      have hpr : p ∨ r := Or.intro_right p hqr.right
      show (p ∨ q) ∧ (p ∨ r) from And.intro hpq hpr))
(fun impl_right : (p ∨ q) ∧ (p ∨ r) =>
   have hpq : (p ∨ q) := impl_right.left
   have hpr : (p ∨ r) := impl_right.right
   Or.elim hpq
      (fun hp : p => show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hp)
      (fun hq : q => Or.elim hpr
         (fun hp : p => show p ∨ (q ∧ r) from Or.intro_left (q ∧ r) hp)
         (fun hr : r =>
            have hqr : q ∧ r := And.intro hq hr
            show p ∨ (q ∧ r) from Or.intro_right p hqr)))

example : (p → (q → r)) ↔ (p ∧ q → r) := Iff.intro
(fun hpqr : p → (q → r) =>
   fun hpq : p ∧ q =>
   have hqr : q → r := hpqr hpq.left
   show r from hqr hpq.right)
(fun hpqr : p ∧ q → r =>
   fun hp : p =>
   fun hq : q =>
   have hpq : p ∧ q := And.intro hp hq
   show r from hpqr hpq)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := Iff.intro
(fun hpq : (p ∨ q) → r =>
   have hpr : p → r := fun hp : p => hpq (Or.intro_left q hp)
   have hqr : q → r := fun hq : q => hpq (Or.intro_right p hq)
   show (p → r) ∧ (q → r) from And.intro hpr hqr)
(fun h1 : (p → r) ∧ (q → r) =>
   have hpr : p → r := h1.left
   have hqr : q → r := h1.right
   fun hpq : p ∨ q => Or.elim hpq
      (fun hp : p => show r from hpr hp)
      (fun hq : q => show r from hqr hq))

example : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q := Iff.intro -- same as the previous, just replace r with False
(fun hpq : p ∨ q → False =>
   have hpf : p → False := fun hp : p => hpq (Or.intro_left q hp)
   have hqf : q → False := fun hq : q => hpq (Or.intro_right p hq)
   show ¬ p ∧ ¬ q from And.intro hpf hqf)
(fun h1 : ¬ p ∧ ¬ q =>
   have hpf : ¬ p := h1.left
   have hqf : ¬ q := h1.right
   fun hpq : p ∨ q => Or.elim hpq
      (fun hp : p => show False from hpf hp)
      (fun hq : q => show False from hqf hq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
fun h1 : ¬p ∨ ¬q =>
   fun hpq : p ∧ q =>
      show False from Or.elim h1
         (fun hp : p → False => hp hpq.left)
         (fun hq : q → False => hq hpq.right)

example : ¬(p ∧ ¬p) :=
fun hpp : p ∧ ¬p => show False from hpp.right hpp.left

example : p ∧ ¬q → ¬(p → q) :=
fun h1 : p ∧ ¬q =>
   fun hpq : p → q =>
      have hq : q := hpq h1.left
      show False from h1.right hq

example : ¬p → (p → q) :=
fun h1 : p → False =>
   fun hp : p => False.elim (h1 hp)

example : (¬p ∨ q) → (p → q) :=
fun hpq : ¬p ∨ q =>
   fun hp : p =>
      show q from Or.elim hpq
         (fun hnp : p → False => False.elim (hnp hp))
         (fun hq : q => hq)

example : p ∨ False ↔ p := Iff.intro
(fun hpf : p ∨ False => Or.elim hpf
   (fun hp : p => hp)
   (fun hf : False => False.elim hf))
(fun hp : p => show p ∨ False from Or.intro_left False hp)

example : p ∧ False ↔ False := Iff.intro
(fun hpf : p ∧ False => show False from hpf.right)
(fun hf : False =>
   have hp : p := False.elim hf
   show p ∧ False from And.intro hp hf)

example : (p → q) → (¬q → ¬p) :=
fun hpq : p → q =>
   fun hqf : q → False =>
      fun hp : p => show False from (hqf (hpq hp))

open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
fun hpqr : (p → q ∨ r) => Or.elim (em q)
   (fun hq : q =>
      suffices hpq : p → q from Or.intro_left (p → r) hpq
      fun _ : p => show q from hq)
   (fun hqf : q → False =>
         suffices hpr : p → r from Or.intro_right (p → q) hpr
         fun hp : p => Or.elim (hpqr hp)
            (fun hq : q => show r from False.elim (hqf hq))
            (fun hr : r => hr))

example : (¬q → ¬p) → (p → q) :=
fun hqp : ¬q → ¬p => Or.elim (em q)
   (fun hq : q =>
      fun _ : p => show q from hq)
   (fun hqf : q → False =>
      have hpf : p → False := hqp hqf
      fun hp : p => show q from False.elim (hpf hp))

example : p ∨ ¬p := em p
