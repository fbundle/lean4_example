import json.Json
import json.JsonUtil
import echo_line.EchoLine

open Json

-- use map filter reduce to simplify code
--
def reduce (actions: List β) (update: α → β → α) (state: α): α :=
  match actions with
    | [] => state
    | action :: actions => reduce actions update (update state action)

def printList (l: List Int): String :=
  let s := reduce l (λ (acc: String)(item: Int) => acc ++ item.repr ++ ", ") ""
  "[" ++ s ++ "]"

#eval printList [1, 2, 3]

def sum(a: Option (Array Int)): Int :=
  match a with
    | some a => reduce a.toList (λ (x: Int)(y: Int) => x + y) 0
    | _ => 0

def echo(s: Option String): String :=
  match s with
    | some s => s
    | _ => ""


def fib (n: Option Int): Int :=
  match n with
    | some n =>
      let rec loop (remain: Nat) (a: Nat) (b: Nat): Nat × Nat :=
        if remain == 0
          then (a, b)
          else loop (remain-1) b (a + b)
      decreasing_by all_goals sorry

      let (a, b) := loop n.natAbs 0 1
      a
    | _ => 0


-- State : the structure that holds the state of the application
structure State where
  count : Nat

-- default : starting state
def default_state : State := { count := 0 }
-- apply : transform state by receiving input
def apply (state: State) (input: String): State × String :=
  let new_state := { state with count := state.count + 1 }
  let (_, o) := parseJson input -- read the first json only

  match o with
    | some (Json.object o) =>
      let l := o.map λ (kv: String × Json) =>
        let (key, val) := kv
        match key with
          | "sum" => (sum (JsonUtil.getArrayOfNumbersFromJson val)).repr
          | "echo" => echo (JsonUtil.getStringFromJson val)
          | "fib" => (fib (JsonUtil.getNumberFromJson val)).repr
          | _ => ""
      let s := reduce l.toList (λ (x: String) (y: String) => x ++ "|" ++ y) s!"state {state.count}"
      (new_state, s)
    | _ => (new_state, s!"state {state.count}")

def main : IO Unit := do
  IO.println "Hello"
  EchoLine.loop default_state apply
  IO.println "Goodbye!"
