def List.last? {α : Type} (xs : List α) : Option α :=
match xs with
| [] => none
| y :: [] => some y
| _ :: ys => List.last? ys

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
match xs with
| [] => none
| y :: ys => if predicate y then some y else List.findFirst? ys predicate

def emptyList : List Nat := []
def fullList : List Nat := [2,3,4]

#eval List.last? fullList
#eval List.last? emptyList

#eval List.findFirst? fullList (fun x => x>2)
#eval List.findFirst? emptyList (λ x => x>2) -- predicate function using λ notation

------------------------------

def Prod.swap {α β : Type} (pair : Prod α β) := Prod.mk pair.snd pair.fst

def twoNats := (2,3)

#eval Prod.swap twoNats

------------------------------

def zip {α β : Type} (xs : List α) (ys : List β) :=
match xs with
| [] => []
| a :: as => match ys with
  | [] => []
  | b :: bs => (a,b) :: zip as bs

def Nats := [2,3,1,5,2]
def Bools := [true,false,false]

#eval zip Nats Bools

------------------------------

def take {α : Type} (n : Nat) (xs : List α) :=
match xs with
| [] => []
| y :: ys => if n>0 then y :: take (Nat.pred n) ys else []

#eval take 3 Nats

------------------------------

def distribProd {α β γ : Type u} (val : Prod α (Sum β γ)) :=
match val.snd with
| Sum.inl aa => Sum.inl (Prod.mk val.fst aa)
| Sum.inr bb => Sum.inr (val.fst, bb)

def sum1 : Sum Nat String := Sum.inl 2
def sum2 : Sum Nat String := Sum.inr "two"
def prod1 := (2,sum1)
def prod2 := (2,sum2)

#eval distribProd prod1
#eval distribProd prod2

------------------------------

def boolToPlus {α : Type u} (val : Prod Bool α) :=
match val.fst with
| true => Sum.inl val.snd
| false => Sum.inr val.snd

def prodTrue := (true,2)
def prodFalse := (false,2)

#eval boolToPlus prodTrue
#eval boolToPlus prodFalse
