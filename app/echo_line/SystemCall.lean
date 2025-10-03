import Lean.Data.Json

namespace EchoLine

open Lean.Json

def ReadFileTextRequest (filename: String): Lean.Json :=
  mkObj [
    ⟨"request", "read_file_text"⟩,
    ⟨"filename", filename⟩
  ]

def ReadFileTextResponse2 (json: Lean.Json): Except String String := do
  let error ← json.getObjVal? "error"
  if error != null then
    Except.error error.compress
  else
    let content ← json.getObjVal? "content"
    let contentStr ← content.getStr?
    return contentStr


#eval ReadFileTextResponse2 (mkObj [
  ⟨ "error", null ⟩,
  ⟨ "content", "file content" ⟩,
])

end EchoLine
