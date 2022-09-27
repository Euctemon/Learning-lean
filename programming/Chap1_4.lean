structure RectangularPrism where
height : Float
width : Float
depth : Float

def volume (box : RectangularPrism) : Float := box.depth*box.height*box.width

def Box : RectangularPrism := {height := 2, width := 3, depth := 2}

#eval volume Box

------------------------------

structure Point where
xcoord : Float
ycoord : Float

structure Segment where
point1 : Point
point2 : Point

def length (s : Segment) := Float.sqrt ((s.point1.xcoord-s.point2.xcoord)^2.0 + (s.point1.ycoord-s.point2.ycoord)^2.0)

def A : Point := {xcoord := 2, ycoord := 1}
def B : Point := Point.mk 5 5 -- different construction of structure
def Line : Segment := Segment.mk A B

#eval length Line


