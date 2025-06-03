import json.Json

namespace JsonUtil
  open Json
  def getArrayOfNumbersFromJson (json: Json): Option (Array Int) :=
    match json with
      | Json.array a =>
        let a := a.map ((λ (json: Json) =>
          match json with
            | Json.number i => some i
            | _ => none
        ): Json → Option Int)

        let a := a.filter (λ (i: Option Int) =>
          match i with
            | some _ => true
            | none => false
        )

        let a := a.map ((λ (i: Option Int) =>
          match i with
           | some i => i
           | none => 0
        ): Option Int → Int)

        some a
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
