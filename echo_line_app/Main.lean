import json.Json

def main : IO Unit := do
  IO.println "Enter your name:"
/-
import echo_line.EchoLine


-- State : the structure that holds the state of the application
structure State where
  count : Nat

-- default : starting state
def default_state : State := { count := 0 }

-- apply : transform state by receiving input
def apply : State × String → State × String := λ (state, input) =>
  let new_state := { state with count := state.count + 1 }
  let output := s!"Hello, \"{input}\" {new_state.count}th times!"
  (new_state, output)

def main : IO Unit := do
  IO.println "Enter your name:"
  EchoLine.loop default_state apply
  IO.println "Goodbye!"
-/