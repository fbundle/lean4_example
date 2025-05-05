-- basic examples

namespace Basic_1 -- namespace

def add1 (n : Nat) : Nat := n + 1

#eval add1 7 -- #eval will appear as info and calculated at compile time

#eval 1 + 2

#eval (String.append "great " (String.append "oak " "tree"))

#eval (String.append "it is " (if 1 > 2 then "yes" else "no"))

end Basic_1 -- end namespace
