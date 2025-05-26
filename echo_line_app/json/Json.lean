inductive Json where
  | null : Json
  | number : Nat → Json
  | string : String → Json
  | list : List Json → Json
  | object : List (String × Json) → Json
  deriving Repr

def Parser : Type := String → (Json × String)


def head: String → Option Char := λ (s: String) =>
  match s.length with
    | 0 => none
    | _ => some s.front

def parseString: Parser := λ (s: String) =>
  let rec parseStringInner: String → String → (Json × String) := λ (canvas: String) (s: String) =>
    match head s with
        | none => (Json.null, "")  -- unexpected EOF
        | some '"' => (Json.string canvas, s.drop 1)
        | some c => parseStringInner (canvas ++ String.mk [c]) (s.drop 1)
        decreasing_by sorry

  match head s with
    | some '"' => parseStringInner "" (s.drop 1)
    | _ => (Json.null, "") -- unexpected EOF

#eval! parseString "\"hello world\""
#eval! parseString "\"hello world\" 123"

-- def parseNumber: Parser := λ (s: String) =>
