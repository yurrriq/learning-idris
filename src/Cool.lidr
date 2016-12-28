> module Cool
>

First, add the following type signature:

> word_lengths : List String -> List Nat

Then move the point to the function name and press `C-c C-s`
to call `idris-add-clause`, which will start an inferior Idris process
(as needed) and generate the following:

```idris
word_lengths xs = ?word_lengths_rhs
```

If you move the point to `?word_lengths_rhs` and press `C-c C-t`, i.e.
`idris-type-at-point`, it will tell you:

```idris
  xs : List String
--------------------------------------
word_lengths_rhs : List Nat
```

Very cool.

Then move the point to `xs` and press `C-c C-c` for `idris-case-dwim`.

```idris
word_lengths [] = ?word_lengths_rhs_1
word_lengths (x :: xs) = ?word_lengths_rhs_2

-- where

--------------------------------------
word_lengths_rhs_1 : List Nat

-- and

  x  : String
  xs : List String
--------------------------------------
word_lengths_rhs_2 : List Nat
```

The case when the input is empty is trivial:

> word_lengths [] = []

Then we can rename `x` and `xs` to the more descriptive `word` and `words`
and use another hole for the sake of example:

```idris
word_lengths (word :: words) = length word :: ?rest

-- where

  word  : String
  words : List String
--------------------------------------
  rest  : List Nat
```

N.B. This incomplete defintion is callable in a REPL:

```idris
*cool> word_lengths ["testing", "one", "two", "three"]
7 :: ?rest : List Nat
```

Filling in the hole is trivial

> word_lengths (word :: words) = length word :: word_lengths words

```idris
*cool> word_lengths ["testing", "one", "two", "three"]
[7, 3, 3, 5] : List Nat
```
