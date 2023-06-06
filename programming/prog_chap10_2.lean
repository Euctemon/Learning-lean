def NonTail.sum : List Nat → Nat
 | [] => 0
 | x :: xs => x + sum xs


def Tail.sumHelper (soFar : Nat) : List Nat → Nat
 | [] => soFar
 | x :: xs => Tail.sumHelper (soFar + x) xs

def Tail.sum (xs : List Nat) : Nat := Tail.sumHelper 0 xs

theorem Helper_sum_eq (xs : List Nat) : ∀ (n : Nat) , (n + NonTail.sum xs = Tail.sumHelper n xs) := by
induction xs with
| nil => intro s
         rfl
| cons y ys h => intro s
                 simp [NonTail.sum, Tail.sumHelper]
                 rw [← Nat.add_assoc, h (s + y)]

theorem Non_tail_eq_tail_sum : NonTail.sum = Tail.sum := by
funext xs
simp [Tail.sum]
rw [← Nat.zero_add (NonTail.sum xs)]
exact Helper_sum_eq xs 0

--

def NonTail.reverse : List α → List α
 | [] => []
 | x :: xs => NonTail.reverse xs ++ [x]

def Tail.reverseHelper (soFar : List α) : List α → List α
 | [] => soFar
 | x :: xs => Tail.reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α := Tail.reverseHelper [] xs

theorem Helper_reverse_eq (as : List α) : ∀ (bs : List α), NonTail.reverse as ++ bs = Tail.reverseHelper bs as := by
induction as with
| nil => intro m
         simp [NonTail.reverse, Tail.reverseHelper]
| cons y ys h => intro m
                 simp [NonTail.reverse, Tail.reverseHelper]
                 rw [← List.append_cons, ← h (y::m)]

theorem Non_tail_eq_tail_reverse : @NonTail.reverse = @Tail.reverse := by
funext α xs
simp [Tail.reverse]
rw [← List.append_nil (NonTail.reverse xs)]
exact Helper_reverse_eq xs []

--

def NonTail.fact : Nat → Nat
 | 0 => 1
 | Nat.succ k => (Nat.succ k) * NonTail.fact k


def Tail.factHelper (acc : Nat) : Nat → Nat
 | 0 => acc
 | Nat.succ k => Tail.factHelper (acc * (Nat.succ k)) k

def Tail.fact (a : Nat) : Nat := Tail.factHelper 1 a

theorem Helper_fact_eq (a : Nat) : ∀ (b : Nat), b * NonTail.fact a = Tail.factHelper b a := by
induction a with
 | zero => intro h
           simp [NonTail.fact, Tail.factHelper]
 | succ k h => intro f
               simp [NonTail.fact, Tail.factHelper]
               rw [← Nat.mul_assoc, h (f * Nat.succ k)]

theorem Non_tail_eq_tail_fact : NonTail.fact = Tail.fact := by
funext a
simp [Tail.fact]
rw [← Nat.one_mul (NonTail.fact a)]
exact Helper_fact_eq a 1