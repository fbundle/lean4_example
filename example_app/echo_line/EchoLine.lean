
namespace EchoLine

-- I don't care what it does - I just know that
-- read stdin line by line
-- pass the line to apply
-- print the result to stdout
-- repeat until EOF

partial def loop : α  →  (α → String → α × String) → IO Unit := λ state => λ apply => do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let buf ← stdin.getLine
  if buf.isEmpty then
    pure ()
  else
    let input := buf.trim
    let (new_state, output) := apply state input
    stdout.putStrLn output
    loop new_state apply

end EchoLine
