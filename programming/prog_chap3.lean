example : 2 + 3 = 5 := rfl

example : 15 - 8 = 7 := rfl

example : "Hello".append " lean" = "Hello lean" := rfl

example : 5 < 8 := by simp

def getFiftElem (x : List α) (h : x.length > 5) := x[5]'h

def getSixthElem (x : List α) (h1 : x.length > 10) := x[6]'h2
  where h2 : x.length > 6 := by
have h : 6 < 10 := by simp
apply Nat.lt_trans h
exact h1