Palindrome.lidr
===============

```idris
module Palindrome

isPalindrome : Nat -> String -> Bool
isPalindrome min str =
  length str > min &&
  let normalized = toLower str
      reversed   = reverse normalized
  in  normalized == reversed
```
