
namespace Function_3

-- function (or variable - anything is a function) without arguments
def hello: String := "world"

#eval hello

def lean: String := "Lean" -- with type

#eval lean

-- two ways to define a function
-- 1. using def
-- 2. using fun - lambda expression

def add2 (n: Nat): Nat := n + 2

def add3: Nat → Nat := fun n => n + 3

def add4: Nat → Nat := λ n => n + 4
def add5: Nat → Nat := ( · + 5 )

#eval [(add2 3), (add3 3), (add4 3), (add5 3)] -- will be list [5, 6, 7, 8]

-- two ways to define a function with two arguments
-- 1. using def
-- 2. using fun - lambda expression (curried function)

def mysum1 (a: Nat) (b: Nat): Nat := a + b
def mysum2: Nat → Nat → Nat := fun a b => a + b
def mysum3: Nat → Nat → Nat := fun a => fun b => a + b
def mysum4: Nat → Nat → Nat
  | a, b => a + b -- using pattern matching

#eval [(mysum1 3 4), (mysum2 3 4), (mysum3 3 4), (mysum4 3 4)] -- will be list [7, 7, 7, 7]

#check [mysum1, mysum2, mysum3, mysum4] -- check type

#check [mysum1 3, mysum2 3, mysum3 3, mysum4 3] -- check type




def Str1: Type := String -- type as first class citizen
def Str2: Type := String → String

def aStr: Str1 := "hello"
def aStr2: Str2 := fun (s : String) => (s ++ " world": String)
def aStr3: Str2 := λ (s : String) => (s ++ " world": String)

#eval aStr3 aStr -- will be "hello world"

abbrev N: Type := Nat -- type alias - recommended way

end Function_3
