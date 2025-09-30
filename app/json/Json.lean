/-!
Module: Json

Lightweight JSON AST and a minimal, whitespace-tolerant parser implemented in pure Lean.

Scope and limitations:
- Numbers: only integers are supported (no decimals or exponents).
- Strings: supports basic escapes for `\"` and `\\`.
- Objects: parsed into an array of key–value pairs, keys are strings.
- Arrays and objects permit arbitrary whitespace between tokens.
- Parser returns the remaining unconsumed input together with an optional result.

This is intended for educational/demo purposes, not as a fully compliant JSON parser.
-/

namespace Json

  /--
  Core JSON algebraic data type used by this module.

  Note: numbers are represented as `Int`. If you need full JSON number
  support (decimals, exponents), extend the parser and this type accordingly.
  -/
  inductive Json where
    | null: Json
    | bool (b : Bool): Json
    | number (n : Int): Json
    | string (s : String): Json
    | array (a : Array Json): Json
    | object (o : Array (String × Json)): Json
    deriving Repr

  /-- Return the first character of `s` if present. -/
  private def head (s: String): Option Char :=
    match s.length with
      | 0 => none
      | _ => some s.front

  /-- Return the first and second characters of `s` (if present). -/
  private def head2 (s: String): Option Char × Option Char :=
    match s.length with
      | 0 => (none, none)
      | 1 => (some s.front, none)
      | _ => (some s.front, some (s.drop 1).front)

  /--
  If the `input` starts with any of the `patterns`, consume it and return `(rest, some pattern)`.
  Otherwise, return `(input, none)` without consuming anything.
  -/
  private def parseExact (patterns: List String) (input: String) : String × Option String :=
    match patterns with
    | [] => (input, none)
    | pattern :: patterns =>
      if input.startsWith pattern
      then ((input.drop pattern.length), some pattern)
      else parseExact patterns input

  /-- Parse a JSON string, supporting `\"` and `\\` escapes. -/
  private partial def parseString (input: String): String × Option String :=
    let (input, c) := parseExact ["\""] input
    match c with
    | some "\"" => -- start of string

      let rec loop (input: String) (acc: String): String × Option String :=
        let (o_c1, o_c2) := head2 input
        match (o_c1, o_c2) with
          | (some '\"', _)          => ((input.drop 1), acc) -- end of string
          | (some '\\', some '\"')  => loop (input.drop 2) (acc.push '\"')
          | (some '\\', some '\\')  => loop (input.drop 2) (acc.push '\\')
          | (some c1, _)            => loop (input.drop 1) (acc.push c1)
          | _                       => (input, none) -- parse error

      loop input ""

    | _ => (input, none) -- parse error

  /-- Parse a signed sequence of digits into an `Int`. -/
  private partial def parseInteger (input: String): String × Option Int :=
    let parseSign (input: String): String × Int :=
      let (input, s) := parseExact ["-"] input
      match s with
        | some "-" => (input, -1)
        | _ => (input, 1)

    let (input, sign) := parseSign input

    let parseAbs (input: String): String × Option Int :=
      let rec loop (input: String) (acc: String): String × String :=
        let (input, o_d) := parseExact ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"] input
        match o_d with
          | some d => loop input (acc ++ d)
          | _ => (input, acc)

      let (input, abs_s) := loop input ""

      match abs_s.toInt? with
        | some abs => (input, some abs)
        | _ => (input, none) -- parse error

    let (input, o_abs) := parseAbs input

    match o_abs with
      | some abs => (input, abs * sign)
      | _ => (input, none)

  /-- Consume leading whitespace characters from `input`. -/
  private partial def consumeSpace (input: String): String :=
    match head input with
      | some c =>
        if c.isWhitespace
          then consumeSpace (input.drop 1)
          else input
      | none => input

  /-- Parse a JSON string value and wrap it in `Json.string`. -/
  private def parseStringJson (input: String): String × Option Json :=
    let (input, o_s) := parseString input
    match o_s with
      | some s => (input, Json.string s)
      | none => (input, none)

  /-- Parse a JSON integer number and wrap it in `Json.number`. -/
  private def parseIntegerJson (input: String): String × Option Json :=
    let (input, o_i) := parseInteger input
    match o_i with
      | some i => (input, Json.number i)
      | none => (input, none)

  /-- Parse `null`, `true`, or `false` as JSON constants. -/
  private def parseConstantJson (input: String): String × Option Json :=
    if input.startsWith "null"
    then (input.drop 4, some Json.null)
    else if input.startsWith "true"
    then (input.drop 4, some (Json.bool true))
    else if input.startsWith "false"
    then (input.drop 5, some (Json.bool false))
    else (input, none) -- parse error, return none

  mutual
    /-- Parse a JSON array: `[ v1, v2, ... ]`. -/
    private partial def parseArrayJson (input: String): String × Option Json :=

      let (input, c) := parseExact ["["] input
      match c with
        | some "[" =>

          let rec loop (input: String) (acc: Array Json): String × Option (Array Json) :=
            let input := consumeSpace input
            let (input, o_json) := parseJson input
            let acc :=
              match o_json with
                | some json => acc.push json
                | _ => acc

            let input := consumeSpace input
            let (input, c) := parseExact [",", "]"] input
            match c with
              | some "," => loop input acc
              | some "]" => (input, some acc)
              | _ => (input, none) -- parse error

          let (input, o_a) := loop input #[]

          match o_a with
            | some a => (input, Json.array a)
            | _ => (input, none)

        | _ => (input, none)

    /-- Parse a JSON object: `{ "key": value, ... }`. -/
    private partial def parseObjectJson (input: String): String × Option Json :=
      let parseKV (input: String): String × Option (String × Json) :=
        let input := consumeSpace input
        let (input, o_key) := parseString input
        match o_key with
          | some key =>
            let input := consumeSpace input
            let (input, c) := parseExact [":"] input
            match c with
              | some ":" =>
                let input := consumeSpace input
                let (input, o_val) := parseJson input
                match o_val with
                  | some val => (input, some (key, val))
                  | _ => (input, none)
              | _ => (input, none)
          | _ => (input, none)


      let (input, c) := parseExact ["{"] input
      match c with
        | some "{" =>

          let rec loop (input: String) (acc: Array (String × Json)) : String × Option (Array (String × Json)) :=
            let input := consumeSpace input
            let (input, o_kv) := parseKV input
            let acc := match o_kv with
              | some kv => acc.push kv
              | _ => acc

            let input := consumeSpace input
            let (input, c) := parseExact [",", "}"] input
            match c with
              | some "," => loop input acc
              | some "}" => (input, acc)
              | _ => (input, none)

          let (input, o_o) := loop input #[]

          match o_o with
            | some o => (input, Json.object o)
            | _ => (input, none)

        | _ => (input, none)

    /--
    Parse any JSON value from `input`, consuming leading whitespace. On success,
    returns the remaining input and `some Json`. On failure, returns `(input, none)`.
    -/
    partial def parseJson (input: String): String × Option Json :=
      let input := consumeSpace input
      let (input, o_c) := parseConstantJson input
      match o_c with
        | some c => (input, some c)
        | _ =>
          match head input with
            | some '\"' => parseStringJson input
            | some '-' | some '0'| some '1'| some '2'| some '3'| some '4'| some '5'| some '6'| some '7'| some '8'| some '9' => parseIntegerJson input
            | some '[' => parseArrayJson input
            | some '{' => parseObjectJson input
            | _ => (input, none)

  end

end Json
