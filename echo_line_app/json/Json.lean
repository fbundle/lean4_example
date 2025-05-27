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



def parseExactString (s₁: String) (s: String): String × Bool :=
  if s.startsWith s₁
  then (s.drop s₁.length, true)
  else (s, false) -- string does not match

def parseExactChar (c: Char) (s: String): String × Bool := parseExactString c.toString s

def parseDigit (s: String): String × Option Char :=
  match head s with
    | some c =>
      if c.isDigit
      then (s.drop 1, some c)
      else (s, none) -- character is not a digit
    | _ => (s, none) -- parse error

-- parse json

def parseString(s: String): String × Option Json :=
  let rec loop (s: String) (acc: String) : String × String :=
    match head2 s with
      | (none, none) => (s, acc) -- parse error
      | (some '"', none) => (s.drop 1, acc) -- end of string
      | (some '\\', some '"') => loop (s.drop 2) (acc ++ "\"")
      | (some '\\', some '\\') => loop (s.drop 2) (acc ++ "\\")
      | (some c, _) => loop (s.drop 1) (acc ++ c.toString)
      | _ => (s, acc) -- dummy case to satisfy pattern matching
    decreasing_by all_goals sorry

  -- we can only parse a string if it starts with a double quote
  match parseExactChar '"' s with
    | (s, true) => -- string must start with double quote
      let (s, s₁) := loop s ""
      (s, some (Json.string s₁))
    | _ => (s, none) -- parse error


#eval! parseString "\"Hello, World!\""
#eval! parseString "\"Hello, \\\"World!\\\"\" 123"

def parseInteger (s: String): String × Option Json :=
  let parseIntegerString (s: String): String × String :=
  -- parse a number, which may start with a minus sign
    let rec parseAllDigits (s: String) (acc: String): String × String :=
      match parseDigit s with
        | (s, some c) => parseAllDigits s (acc ++ c.toString)
        | (s, none) => (s, acc)
    decreasing_by all_goals sorry

    match parseExactChar '-' s with
      | (s, true) => parseAllDigits s "-"
      | _ => parseAllDigits s ""

  let (s, c) := parseIntegerString s
  match c.toInt? with
    | some n => (s, some (Json.number n))
    | none => (s, none) -- parse error

#eval! parseInteger "-12345"
#eval! parseInteger "67890"

def parseConst (s: String): String × Option Json :=
  if s.startsWith "null"
  then (s.drop 4, some Json.null)
  else if s.startsWith "true"
  then (s.drop 4, some (Json.bool true))
  else if s.startsWith "false"
  then (s.drop 5, some (Json.bool false))
  else (s, none) -- parse error, return none

#eval! parseConst "null"
#eval! parseConst "true"
#eval! parseConst "false"
