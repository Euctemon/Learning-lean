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