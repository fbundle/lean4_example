import json.Json
import echo_line.EchoLine


-- State : the structure that holds the state of the application
structure State where
  count : Nat

-- default : starting state
def default_state : State := { count := 0 }

def sum(json: Json.Value): Int :=
  match json with
  | Json.Value.array l =>
    let rec loop (l: List Json.Value) (acc: Int): Int :=
      match l with
        | [] => acc
        | x :: xs =>
          match x with
            | Json.Value.number y => loop xs (acc + y)
            | _ => loop xs acc

    loop l.toList 0
  | _ => 0

def echo(json: Json.Value): String :=
  match json with
    | Json.Value.string s => s
    | _ => ""

-- apply : transform state by receiving input
def apply (state: State) (input: String): State × String :=
  let new_state := { state with count := state.count + 1 }
  let (_, o_o) := Json.parseJson input -- read the first json only
  let rec loop (o : List (String × Json.Value)) (acc: String): String :=
    match o with
      | [] => acc
      | x :: xs =>
        let (key, val) := x
        match key with
          | "sum" => loop xs (acc ++ " " ++ s!"sum {sum val}")
          | "echo" => loop xs (acc ++ " " ++ (echo val))
          | _ => loop xs acc

  match o_o with
  | some (Json.Value.object o) => (new_state, s!"state {state.count}: {loop o.toList ""}")
  | _ => (new_state, s!"state {state.count}")


def main : IO Unit := do
  IO.println "Hello"
  EchoLine.loop default_state apply
  IO.println "Goodbye!"
