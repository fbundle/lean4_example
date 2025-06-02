import json.Json

def parseArrayOfNumbers (s: String): Option (Array Int) :=
  let (s, o) := Json.parseJson s
  match o with
    | Json.Json.array a =>
      -- use (a: List Json.Json) instead of (a: Array Json.Json) for loop
      let rec loop (a: List Json.Json) (acc: Array Int): (List Json.Json × Array Int) :=
        match a with 
          | [] => (a, acc)
          | x :: xs => 
            match x with
              | Json.Json.number i => loop xs (acc.push i)
              | _ => loop xs acc
      -- decreasing_by all_goals sorry
      let (a, acc) := loop a.toList #[]
      some acc
    | _ => none

#eval! parseArrayOfNumbers "[1, 2, 4, 5]"

