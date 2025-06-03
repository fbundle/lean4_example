import json.Json
import json.JsonUtil
import echo_line.EchoLine

open Json

-- use map filter reduce to simplify code
def reduce (items: List α) (combine: α → α → α) (acc: α): α :=
  match items with
    | [] => acc
    | item :: items => reduce items combine (combine acc item)


-- State : the structure that holds the state of the application
structure State where
  count : Nat

-- default : starting state
def default_state : State := { count := 0 }

def sum(json: Json): Int :=
  let o_a := JsonUtil.getArrayOfNumbers json
  match o_a with
    | some a => reduce a.toList (λ (a: Int)(b: Int) => a + b) 0
    | _ => 0

def echo(json: Json): String :=
  match json with
    | Json.string s => s
    | _ => ""

def fib(json: Json): String :=
  let calc_fib (n: Nat): Nat :=
    let rec loop (remain: Nat) (a: Nat) (b: Nat): Nat × Nat :=
      if remain == 0
        then (a, b)
        else loop (remain-1) b (a + b)
    decreasing_by all_goals sorry

    let (a, b) := loop n 0 1
    a
  match json with
    | Json.number i => (calc_fib i.natAbs).repr
    | _ => ""

-- apply : transform state by receiving input
def apply (state: State) (input: String): State × String :=
  let new_state := { state with count := state.count + 1 }
  let (_, o_o) := parseJson input -- read the first json only
  let rec loop (o : List (String × Json)) (acc: String): String :=
    match o with
      | [] => acc
      | x :: xs =>
        let (key, val) := x
        match key with
          | "sum" => loop xs (acc ++ " " ++ s!"sum {sum val}")
          | "echo" => loop xs (acc ++ " " ++ (echo val))
          | "fib" => loop xs (acc ++ " " ++ (fib val))
          | _ => loop xs acc

  match o_o with
  | some (Json.object o) => (new_state, s!"state {state.count}: {loop o.toList ""}")
  | _ => (new_state, s!"state {state.count}")


def main : IO Unit := do
  IO.println "Hello"
  EchoLine.loop default_state apply
  IO.println "Goodbye!"
