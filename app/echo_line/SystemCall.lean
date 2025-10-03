import Lean.Data.Json

namespace EchoLine

open Lean.Json

def ReadFileTextRequest (filename: String): Lean.Json :=
  Lean.Json.mkObj [
    ⟨"request", "read_file_text"⟩,
    ⟨"filename", filename⟩
  ]

def ReadFileTextResponse (json: Lean.Json): Except String String :=
  match json.getObjVal? "error" with
    | Except.error err => Except.error err -- error field does not exist
    | Except.ok err =>
      match err with
        | Lean.Json.null => -- error field null
          match json.getObjVal? "content" with
            | Except.error err => Except.error err -- content field does not exist
            | Except.ok content =>
              match content.getStr? with
                | Except.error err => Except.error err -- content is not a string
                | Except.ok str => Except.ok str
        | _ => Except.error err.compress -- error field non-null





end EchoLine
