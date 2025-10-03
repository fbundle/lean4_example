import json.Json
import echo_line.EchoLine


structure State where
  count : Nat

def init_state : State := { count := 0 }

def apply_echo_json (state: State) (input: String): State × String :=
  let new_state := { state with count := state.count + 1 }
  let (_, o) := Json.parseJson input -- read the first json only

  match o with
    | some o => (new_state, s!"{o}")
    | _ => (new_state, s!"state {state.count}")

def apply_echo_json_builtin (state: State) (input: String): State × String :=
  let new_state := { state with count := state.count + 1 }
  sorry


def main : IO Unit := do
  IO.println "Hello"
  EchoLine.main_loop apply_echo_json init_state
  IO.println "Goodbye!"
