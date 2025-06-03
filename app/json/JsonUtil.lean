import json.Json

namespace JsonUtil
  open Json
  -- TODO use map filter reduce
  def getArrayOfNumbersFromJson (json: Json): Option (Array Int) :=
    match json with
      | Json.array a =>
        let rec loop (l: List Json) (acc: Array Int): Array Int  :=
          match l with
            | [] => acc
            | x :: xs =>
              match x with
                | Json.number i => loop xs (acc.push i)
                | _ => loop xs acc

        loop a.toList #[]
      | _ => none

  def getStringFromJson (json: Json): Option String :=
    match json with
      | Json.string s => s
      | _ => none

  def getNumberFromJson (json: Json): Option Int :=
    match json with
      | Json.number i => i
      | _ => none

end JsonUtil
