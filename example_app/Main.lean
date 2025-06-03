import json.Json
import json.JsonUtil
import echo_line.EchoLine


def calc_fib (n: Nat): Nat :=
  let rec loop (n: Nat) (nm1: Nat) (nm2: Nat): Nat × Nat × Nat :=
    if n = 0
      then (n, nm1, nm2)
      else loop (n-1) (nm2) (nm1 + nm2)
  
  let (n, nm1, nm2) := loop n 0 1
  nm1


-- State : the structure that holds the state of the application
structure State where
  count : Nat

-- default : starting state
def default_state : State := { count := 0 }

def sum(json: Json.Json): Int :=
  let o_a := JsonUtil.getArrayOfNumbers json
  match o_a with
    | some a =>
      let rec loop (l: List Int) (acc: Int): Int :=
        match l with 
          | [] => acc
          | x :: xs => loop xs (acc + x)
      
      loop a.toList 0
    | _ => 0

def echo(json: Json.Json): String :=
  match json with
    | Json.Json.string s => s
    | _ => ""

def fib(json: Json.Json): String :=
  match json with
    | Json.Json.number i => (calc_fib i.natAbs).repr
    | _ => ""

-- apply : transform state by receiving input
def apply (state: State) (input: String): State × String :=
  let new_state := { state with count := state.count + 1 }
  let (_, o_o) := Json.parseJson input -- read the first json only
  let rec loop (o : List (String × Json.Json)) (acc: String): String :=
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
  | some (Json.Json.object o) => (new_state, s!"state {state.count}: {loop o.toList ""}")
  | _ => (new_state, s!"state {state.count}")


def main : IO Unit := do
  IO.println "Hello"
  EchoLine.loop default_state apply
  IO.println "Goodbye!"
