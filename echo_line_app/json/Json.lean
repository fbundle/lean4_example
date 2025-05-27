inductive Json where
  | null: Json
  | bool (b : Bool): Json
  | number (n : Int): Json
  | string (s : String): Json
  | array (a : List Json): Json
  | object (o : List (String × Json)): Json
  deriving Repr

def head (s: String): Option Char :=
  match s.length with
    | 0 => none
    | _ => some s.front

def head2 (s: String): Option Char × Option Char :=
  match s.length with
    | 0 => (none, none)
    | 1 => (some s.front, none)
    | _ => (some s.front, some (s.drop 1).front)

def consumeExactString (s₁: String) (s: String): String × Bool :=
  if s.startsWith s₁
  then (s.drop s₁.length, true)
  else (s, false) -- string does not match

-- parse literal

def parseStringLiteral(s: String): String × Option String :=
  let rec parseContent (s: String) (acc: String) : String × Option String :=
    match head2 s with
      | (none, none) => (s, none) -- parse error
      | (some '"', none) => (s.drop 1, some acc) -- end of string
      | (some '\\', some '"') => parseContent (s.drop 2) (acc ++ "\"")
      | (some '\\', some '\\') => parseContent (s.drop 2) (acc ++ "\\")
      | (some c, _) => parseContent (s.drop 1) (acc ++ c.toString)
      | _ => (s, none) -- dummy case to satisfy pattern matching
    decreasing_by all_goals sorry

  let consumeDoubleQuote (s: String): String × Bool := consumeExactString "\"" s

  -- we can only parse a string if it starts with a double quote
  match consumeDoubleQuote s with
    | (s, true) => -- string must start with double quote
      let (s, o_acc) := parseContent s ""
      match o_acc with
        | none => (s, none)
        | some acc => (s, some acc)
    | _ => (s, none) -- parse error

def parseIntegerLiteral (s: String): String × Option Int :=
  let consumeDigit (s: String): String × Option Char :=
    match head s with
      | some c =>
        if c.isDigit
        then (s.drop 1, some c)
        else (s, none) -- character is not a digit
      | _ => (s, none) -- parse error
  let rec parseNatural (s: String) (acc: String): String × Option Int :=
    match consumeDigit s with
      | (s, some c) => parseNatural s (acc ++ c.toString)
      | (s, none) =>
        match acc.toInt? with
          | some abs => (s, some abs)
          | none => (s, none)
  decreasing_by all_goals sorry

  let consumeSign (s: String) : String × Int :=
    match consumeExactString "-" s with
      | (s, true) => (s, -1)
      | _ => (s, 1)

  let (s, sign) := consumeSign s
  let (s, o_abs) := parseNatural s ""
  match o_abs with
    | some abs => (s, some (sign * abs))
    | none => (s, none)




-- parse json
mutual

  def parseStringJson(s: String): String × Option Json :=
    let (s, o_acc) := parseStringLiteral s
    match o_acc with
      | some acc => (s, (Json.string acc))
      | none => (s, none)

  def parseIntegerJson(s: String): String × Option Json :=
    let (s, o_acc) := parseIntegerLiteral s
    match o_acc with
      | some acc => (s, (Json.number acc))
      | none => (s, none)

  def parseConstantJson (s: String): String × Option Json :=
    if s.startsWith "null"
    then (s.drop 4, some Json.null)
    else if s.startsWith "true"
    then (s.drop 4, some (Json.bool true))
    else if s.startsWith "false"
    then (s.drop 5, some (Json.bool false))
    else (s, none) -- parse error, return none



  def parseArrayJson(s: String): String × Option Json :=
    let rec parseContent (s: String) (acc: List Json): String × Option (List Json) :=
      match parseJson s with
        | (s, some json) =>
          let acc := acc ++ [json]
          match head s with
            | some ',' => parseContent (s.drop 1) acc
            | some ']' => ((s.drop 1), acc)
            | _ => (s, none)
        | _ => (s, none) -- parse error
      decreasing_by all_goals sorry

    let consumeOpenBracket (s: String): String × Bool := consumeExactString "[" s

    match consumeOpenBracket s with
      | (s, true) =>
        let (s, o_acc) := parseContent s []
        match o_acc with
          | some acc => (s, Json.array acc)
          | none => (s, none)
      | _ => (s, none)

  def parseObjectJson (s: String): String × Option Json :=
    let consumeOpenBrace (s: String): String × Bool := consumeExactString "{" s

    (s, none)


  def parseJson(s: String): String × Option Json :=
    (s, none)

end
