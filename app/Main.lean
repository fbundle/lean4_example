import json.Json
import echo_line.EchoLine

open Json


-- State : the structure that holds the state of the application
structure State where
  count : Nat

-- init_state : starting state
def init_state : State := { count := 0 }

-- apply : transform state by receiving input

def apply_echo_json (state: State) (input: String): State × String :=
  let new_state := { state with count := state.count + 1 }
  let (_, o) := parseJson input -- read the first json only

  match o with
    | some o => (new_state, s!"{o}")
    | _ => (new_state, s!"state {state.count}")



def main : IO Unit := do
  IO.println "Hello"
  EchoLine.main_loop apply_echo_json init_state
  IO.println "Goodbye!"
