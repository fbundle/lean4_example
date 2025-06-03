import json.Json

namespace JsonUtil
  open Json

  def getArrayOfNumbers (json: Json): Option (Array Int) :=
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
end JsonUtil 
