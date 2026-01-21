import YatimaStdLib.List

namespace String

/--
Split a string at an index.
```
"abc".splitAt 2 = ("ab","c")
```
-/
def splitAt (n : Nat) (str : String) : String × String :=
  match List.splitAt n str.toList with
    | (s₁,s₂) => (String.ofList s₁, String.ofList s₂)

def blankIndent (n : Nat) : String :=
  let rec blankAux (cs : List Char) : Nat → List Char
    | 0     => cs
    | n + 1 => ' ' :: ' ' :: (blankAux cs n)
  String.ofList (blankAux [] n)

end String
