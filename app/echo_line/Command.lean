import Lean.Data.Json

namespace EchoLine

def Json := Lean.Json
def mkObj := Lean.Json.mkObj
def null := Lean.Json.null


def ReadFileTextRequest (filename: String): Json :=
  mkObj [
    ⟨"command", "read_file_text"⟩,
    ⟨"filename", filename⟩
  ]

def ReadFileTextResponse (json: Json): Except String String := do
  let error ← json.getObjVal? "error"
  if error != null then
    Except.error error.compress
  else
    let content ← json.getObjVal? "content"
    let contentStr ← content.getStr?
    return contentStr

#eval ReadFileTextRequest "filename.txt"

#eval ReadFileTextResponse (mkObj [
  ⟨ "error", null ⟩,
  ⟨ "content", "file content" ⟩,
])

end EchoLine
