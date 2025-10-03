import Lean.Data.Json

namespace EchoLine


def SysCallReadFileText (filename: String): Lean.Json :=
  Lean.Json.mkObj [
    ⟨"syscall", "read_file_text"⟩,
    ⟨"syscall", filename⟩
  ]


end EchoLine
