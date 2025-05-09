namespace Structure_4

-- some float example

#check (1.2: Float)

#check -454.2123215

#check 0.0

#check 0 -- Nat not Float


-- cartesian coordinates
structure Point3 where
  x: Float
  y: Float
  z: Int := 0 -- default value
  deriving Repr -- deriving Repr to print the structure

#eval ({x := 1.0, y := 2.0}: Point3) -- create a Point3

def p : Point3 := { x := 2.0, y := -1.0 }

#eval p

#eval p.x -- get field x

-- add two Point3s
def addPoint3s (p1: Point3) (p2: Point3) : Point3 :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

-- distance between two Point3s
def distance (p1 : Point3) (p2 : Point3) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance p {x := 5.0, y := -1.0}

#eval {x := 1.0, y := 2.0: Point3} -- syntactic sugar to create a Point3


-- set field x to zero
def setXzero (p: Point3) : Point3 :=
  { x := 0.0, y := p.y, z := p.z }

-- a better way to set field x to one
def setXoneZtwo (p: Point3) : Point3 :=
  { p with x := 1.0, z := 2 }

#eval setXzero p -- set field x to zero
#eval setXoneZtwo p -- set field x to one and z to two


-- default constructor
#check Point3.mk 1.0 2.0 3 -- create a Point3

-- overwrite default constructor name
structure Point2 where make_point::
  x: Float
  y: Float
  deriving Repr

#check Point2.make_point 1.0 2.0 -- create a Point2

#check Point2.x -- Point2.x is a function

-- method for p1
def Point2.sub (p1: Point2) (p2: Point2) : Point2 :=
  { x := p1.x - p2.x, y := p1.y - p2.y }

#eval Point2.sub {x := 3.0, y := 4.0} {x := 1.0, y := 2.0}

#eval ({x := 3.0, y := 4.0}: Point2).sub {x := 1.0, y := 2.0} -- syntactic sugar to call a method

end Structure_4
