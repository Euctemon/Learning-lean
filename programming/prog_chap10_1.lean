def Tail.len (xs : List α) : Nat := Tail.lenHelper 0 xs
where Tail.lenHelper (acc : Nat) : List α → Nat
  | [] => acc
  | _ :: xs => Tail.lenHelper (acc + 1) xs


def Tail.fact (a : Nat) : Nat := Tail.factHelper 1 a
where Tail.factHelper (acc : Nat) : Nat → Nat
  | 0 => acc
  | Nat.succ k => Tail.factHelper (acc * (Nat.succ k)) k


def Tail.filter (p : α → Bool) (xs : List α) : List α := Tail.filterHepler (p : α → Bool) [] xs
where Tail.filterHepler (p : α → Bool) (acc : List α) : List α → List α
  | [] => acc
  | x :: xs => Tail.filterHepler p (if p x then acc ++ [x] else acc) xs


#eval (Tail.len [2,8,11])
#eval (Tail.fact 6)
#eval (Tail.filter (λ x => x % 2 == 0) [2,3,7,6])