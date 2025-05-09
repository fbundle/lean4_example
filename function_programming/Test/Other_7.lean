namespace Other_7

-- (x+1) × 2 + (x+1) × 3
def f(x: Nat) : Nat :=
  let y := x + 1; -- use semicolon to separate
  y * 2 + y * 3

#eval f 1 -- 10

-- list of pairs to pair of lists
def myUnzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) : List α × List β := myUnzip xys ; -- recursive call
    (x :: xs, y :: ys)

-- let rec : for recursive function
def myReverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

-- if let - another way to pattern matching
inductive Animal
  | cat : String → Animal
  | dog : String → Animal
  | fish : String → Animal
  deriving Repr

def catName : Animal → Option String := λ a =>
  if let Animal.cat name := a then
    Option.some name
  else
    Option.none

#eval catName (Animal.cat "Mittens") -- some "Mittens"
#eval catName (Animal.dog "Fido") -- none




end Other_7
