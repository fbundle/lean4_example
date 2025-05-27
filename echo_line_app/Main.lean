import json.Json
import echo_line.EchoLine


-- State : the structure that holds the state of the application
structure State where
  count : Nat

-- default : starting state
def default_state : State := { count := 0 }

def sum(json: Json): Int :=
  match json with
  | Json.array l =>
    let rec loop (l: List Json) (acc: Int): Int :=
      match l with
        | [] => acc
        | x :: xs =>
          match x with
            | Json.number y => loop xs (acc + y)
            | _ => loop xs acc

    loop l 0
  | _ => 0

def echo(json: Json): String :=
  match json with
    | Json.string s => s
    | _ => ""

-- apply : transform state by receiving input
def apply (state: State) (input: String): State × String :=
  let new_state := { state with count := state.count + 1 }
  let (input, o_o) := parseJson input
  let rec loop (o : List (String × Json)) (acc: String): String :=
    match o with
      | [] => acc
      | x :: xs =>
        let (key, val) := x
        match key with
          | "sum" => loop xs (acc ++ " " ++ s!"sum {sum val}")
          | "echo" => loop xs (acc ++ " " ++ (echo val))
          | _ => loop xs acc

  match o_o with
  | some (Json.object o) => (new_state, loop o "")
  | _ => (new_state, "")


def main : IO Unit := do
  IO.println "Hello"
  EchoLine.loop default_state apply
  IO.println "Goodbye!"
