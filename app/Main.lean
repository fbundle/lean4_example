import Lean.Data.Json
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

  -- Parse JSON using Lean.Data.Json
  match Lean.Json.parse input with
  | Except.ok json => (new_state, s!"Parsed JSON: {json}")
  | Except.error err => (new_state, s!"JSON parse error: {err}")


def main : IO Unit := do
  IO.println "Hello"
  EchoLine.main_loop apply_echo_json_builtin init_state
  IO.println "Goodbye!"
