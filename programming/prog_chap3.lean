example : 2 + 3 = 5 := rfl

example : 15 - 8 = 7 := rfl

example : "Hello".append " lean" = "Hello lean" := rfl

example : 5 < 8 := by simp

def getFiftElem (x : List α) (h : x.length > 5) := x[5]'h