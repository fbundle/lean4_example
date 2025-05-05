
namespace Recursion_5

/-
Datatypes that allow choices are called sum types
and datatypes that can include instances of themselves are called recursive datatypes.
Recursive sum types are called inductive datatypes,
because mathematical induction may be used to prove statements about them.
When programming, inductive datatypes are consumed through pattern matching and recursive functions.
-/

-- builtin Nat
-- Natural is a recursive datatype
-- zero is a constructor
-- succ is a constructor that takes a Natural and returns a Natural
-- succ is a recursive constructor
inductive Natural where
  | zero: Natural
  | succ: Natural → Natural
  deriving Repr

def zero := Natural.zero
def one := Natural.succ zero
def two := Natural.succ one
def three := Natural.succ two
def four := Natural.succ three
def five := Natural.succ four

#eval two

-- pattern matching
def isZero (n: Natural): Bool :=
  match n with
  | Natural.zero => true
  | Natural.succ _ => false -- _ wildcard pattern

#eval isZero zero -- true
#eval isZero one -- false

-- another example - pred : predecessor
def pred (n: Natural): Natural :=
  match n with
  | Natural.zero => Natural.zero
  | Natural.succ m => m

#eval pred two

structure Point2 where make_point::
  x: Int
  y: Int
  deriving Repr

-- pattern matching on structure
def getX (p: Point2): Int :=
  match p with
  | {x := xx, y := _} => xx

def onAxes (p: Point2): Bool :=
  match p with
  | {x := 0, y := _} => True
  | {x := _, y := 0} => True
  | _ => False

#eval getX {x := 1, y := 2} -- 1
#eval onAxes {x := 0, y := 2} -- true
#eval onAxes {x := 1, y := 0} -- true
#eval onAxes {x := 1, y := 2} -- false
#eval onAxes {x := 0, y := 0} -- true

-- recursive function
def isEven (n: Natural): Bool :=
  match n with
  | Natural.zero => true
  | Natural.succ m => not (isEven m)

#eval isEven zero -- true
#eval isEven one -- false
#eval isEven two -- true
#eval isEven three -- false

-- another example
def add (a: Natural) (b: Natural): Natural :=
  match a with
  | Natural.zero => b
  | Natural.succ m => add m (Natural.succ b)

def equal (a: Natural) (b: Natural): Bool :=
  match a, b with
  | Natural.zero, Natural.zero => true
  | Natural.succ m, Natural.succ n => equal m n
  | _, _ => false

#eval equal five (add two three)


-- this example does not work since `div` requires a manual proof of termination
/-
g parameter k of Recursion_5.div:
  it is unchanged in the recursive calls
Cannot use parameter k:
  failed to eliminate recursive application
    div (n - k) k


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
k n : Nat
h✝ : ¬n < k
⊢ n - k < n
error: Lean exited with code 1
Some required builds logged failures:
- Test.Recursion_5
error: build failed

def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)

-/

end Recursion_5
