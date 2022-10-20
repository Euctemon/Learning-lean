open Nat

theorem zero_add (n : Nat) : 0 + n = n :=
Nat.recOn (motive := fun x : Nat => 0 + x = x) n
(show 0 + 0 = 0 from rfl)
(fun (n : Nat) (ih : 0 + n = n) => show 0 + succ n = succ n from
calc 0 + succ n = succ (0 + n) := rfl
              _ = succ n := by rw [ih])

open List

def append (as bs : List α) : List α :=
match as with
| nil       => bs
| cons head tail => cons head (append tail bs)

theorem append_nil (as : List α) : append as nil = as :=
List.recOn (motive := fun t : List α => append t nil = t) as
(show append nil nil = nil from rfl)
(fun (head : α) (tail : List α) (ih : append tail nil = tail) => show append (cons head tail) nil = cons head tail from
calc append (cons head tail) nil = cons head (append tail nil) := rfl
    _ = cons head tail := by rw [ih])

theorem append_assoc (as bs cs : List α) : append (append as bs) cs = append as (append bs cs) :=
List.recOn (motive := fun as : List α => append (append as bs) cs = append as (append bs cs)) as
(show append (append nil bs) cs = append nil (append bs cs) from rfl)
(fun (head : α) (tail : List α) (ih : append (append tail bs) cs = append tail (append bs cs)) =>
show append (append (cons head tail) bs) cs = append (cons head tail) (append bs cs) from
calc append (append (cons head tail) bs) cs = append (cons head (append tail bs)) cs := rfl
    _ = cons head (append (append tail bs) cs) := rfl
    _ = cons head (append tail (append bs cs)) := by rw [ih])

def len (as : List α) : Nat :=
match as with
| nil => 0
| cons _ tail => succ (length tail)

theorem len_distrib (as bs : List α) : length (append as bs) = length as + length bs :=
List.recOn (motive := fun as : List α => length (append as bs) = length as + length bs) as
(show length (append nil bs) = length nil + length bs from
calc length (append nil bs) = length bs := rfl
     _ = 0 + length bs := by rw [Nat.zero_add])
(fun (head : α) (tail : List α) (ih : length (append tail bs) = length tail + length bs) =>
show length (append (cons head tail) bs) = length (cons head tail) + length bs from
calc length (append (cons head tail) bs) = length (cons head (append tail bs)) := rfl
     _ = succ (length (append tail bs)) := rfl
     _ = succ (length tail + length bs) := by rw [ih]
     _ = succ (length tail) + length bs := by rw [Nat.succ_add])

namespace Hidden

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c := by rw [h₁,h₂]

theorem congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) := by rw [h]

def subtract (n m : Nat) : Nat :=
match m with
| zero => n
| succ k => pred (subtract n k)

theorem pred_sub_eq_sub_pred : pred (subtract n k) = subtract (pred n) k :=
Nat.recOn (motive := fun x : Nat => pred (subtract n x) = subtract (pred n) x) k
(show pred (subtract n zero) = subtract (pred n) zero from rfl)
(fun (r : Nat) (ih : pred (subtract n r) = subtract (pred n) r) =>
show pred (subtract n (succ r)) = subtract (pred n) (succ r) from
by rw [subtract,ih,subtract])

theorem left_sub_cancel : subtract (n+k) n = k :=
Nat.recOn (motive := fun x : Nat => subtract (x+k) x = k) n
(show subtract (zero + k) zero = k from by rw [Nat.zero_add k,subtract])
(fun (r : Nat) (ih : subtract (r+k) r = k) =>
show subtract ((succ r)+k) (succ r) = k from
by rw [Nat.succ_add,subtract,pred_sub_eq_sub_pred, Nat.pred_succ,ih])