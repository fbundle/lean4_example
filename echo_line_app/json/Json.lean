inductive KV where
  | mk : String → Json → KV

inductive Json where
  | null : Json
  | number : Int → Json
  | string : String → Json
  | list : List Json → Json
  | object : List KV → Json

def Parser : Type := String → (Json × String)


def head: String → Option Char := λ (s: String) =>
  match s.length with
    | 0 => none
    | _ => s.front

def parseString: Parser := λ (s: String) =>
  let rec parseStringInner(json: String) (s: String): (Json × String) :=
    match head s with
      | some '"' => (Json.string json, (s.drop 1))
      | some head => parseStringInner (json ++ String.mk [head]) (s.drop 1)
      | _ => (Json.null, "")  -- unexpected EOF

      termination_by
      


  match head s with
    | some '"' => parseStringInner "" (s.drop 1)
    | _ => (Json.null, "") -- unexpected EOF
