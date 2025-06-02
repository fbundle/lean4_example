import json.Json

namespace JsonUtil
  open Json

  def parseArray (s: String): String × Option (Array Json) :=
    let (s, o) := parseJson s
    match o with
      | Json.array a => (s, some a)
      | _ => (s, none)

  def parseArrayOfNumbers (s: String): String × Option (Array Int) :=
    let (s, o_a) := parseArray s
    match o_a with
      | some a =>
        -- use (a: List Json.Json) instead of (a: Array Json.Json) for loop
        let rec loop (a: List Json.Json) (acc: Array Int): (List Json.Json × Array Int) :=
          match a with 
            | [] => (a, acc)
            | x :: xs => 
              match x with
                | Json.number i => loop xs (acc.push i)
                | _ => loop xs acc
        -- decreasing_by all_goals sorry
        let (a, acc) := loop a.toList #[]
        (s, some acc)
      | _ => (s, none)

  #eval! parseArrayOfNumbers "[1, 2, 4, 5]" 
end JsonUtil 
