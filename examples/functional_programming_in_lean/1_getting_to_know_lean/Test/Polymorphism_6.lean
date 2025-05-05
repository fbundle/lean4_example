namespace Polymorphism_6


-- type as parameter
structure Point (α: Type) where
  x: α
  y: α
  deriving Repr


def p1 : Point Int := { x := 1, y := 2 }
def p2 : Point Float := { x := 1.0, y := 2.0 }

#eval p1 -- Point Int
#eval p2 -- Point Float

def updateX {α: Type} (p: Point α) (xx: α): Point α :=
  { p with x := xx }

#check updateX

#eval updateX p1 3 -- update x to 3
#eval updateX p2 3.0 -- update x to 3.0

-- implicit {α : Type}
def updateXX (p: Point α) (xx: α): Point α :=
  { p with x := xx }

-- implicit (α: Type)
def updateY: Point α → α → Point α
  | p,yy => { p with y := yy } -- update y to y




inductive Sign where
  | pos
  | neg

-- return (3 : Nat) if is positive, (-3 : Int) if negative
-- return type is determined by the value of s
def posOrNegThree (s : Sign) : (match s with
  | Sign.pos => Nat
  | Sign.neg => Int
) := (match s with
    | Sign.pos => (3 : Nat)
    | Sign.neg => (-3 : Int)
)

#check posOrNegThree

-- builtin List
inductive MyList (α: Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

-- three ways to define bultin List
def ll1 := [1, 2, 3]
def ll2 := List.cons 1 (List.cons 2 (List.cons 3 List.nil))
def ll3 := [1::[2, 3]] -- :: is like cons

#eval [ll1, ll2]




def MyList.append (l: MyList α) (e: α) :=
  MyList.cons e l

def l1 := MyList.nil.append  1
def l2 := l1.append  2
def l3 := l2.append  3

#eval l3

def MyList.len (l : MyList α): Nat :=
  match l with
  | MyList.nil => 0
  | MyList.cons _ l => 1 + l.len

#eval l3.len


-- builtin Option
inductive MyOption (α : Type) : Type where
  | none : MyOption α
  | some: (val : α) → MyOption α
  deriving Repr


def x := MyOption.some 1
def y : MyOption Nat := MyOption.none

#eval [x, y]


def MyList.head (l: MyList α) : MyOption α :=
  match l with
  | MyList.nil => MyOption.none
  | MyList.cons e _ => MyOption.some e

#eval l3.head

#eval (MyList.nil : MyList Int).head

-- builtin Prod - Product
structure MyProd (α : Type) (β : Type) : Type where
  fst : α
  snd : β
  deriving Repr

-- three ways to define builtin Product
def fives1 : Prod String Int := {fst:= "five", snd := 5}

def fives2 : String × Int := { fst := "five", snd := 5 }

def fives3 : String × Int := ("five", 5)

-- builtin Sum - Coproduct
inductive MySum (α : Type) (β : Type) : Type where
  | inl : α → MySum α β
  | inr : β → MySum α β
  deriving Repr

-- two ways to define builtin Sum
def z1: Sum Nat Float := Sum.inl 1
def z2: Nat ⊕ Float := Sum.inr 2.0

-- builtin Unit, Empty


end Polymorphism_6
