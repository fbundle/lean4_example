
namespace EchoLine

universe u

def apply_func (α : Type u) : Type u := α → String → α × String

partial def main_loop (apply: apply_func α) (state: α) : IO Unit :=
  do
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    let line ← stdin.getLine
    if line.isEmpty then
      pure ()
    else
      let (new_state, output) := apply state line.trim
      stdout.putStrLn output
      main_loop apply new_state

end EchoLine
