Average.lidr
============

```idris
module Average
```

Documentation comments are introduced with three vertical bars, `|||`.

```idris
||| Calculate the average length of words in a string.
average : String -> Double
```

As the docstring suggests, `average` takes a `String` and computes the average length, as a `Double`, of words in the given string.

```idris
average str = let num_words    = word_count str
                  total_length = sum (word_lengths (words str))
              in  cast total_length / cast num_words
```

The compiler seems to be ok with my obsessive aligment of `=` and the perhaps more ML-style `let`/`in` layout.

N.B. The example in the book puts the `in` right after `words str`, instead of on its own line.

Idris's `where` is very familiar.

```idris
 where
```

`word_count` is pretty self-explanatory: It splits a string into a list of [words](http://www.idris-lang.org/docs/current/prelude_doc/docs/Prelude.Strings.html#Prelude.Strings.words) and returns the `length` of that list.

```idris
   word_count : String -> Nat
   word_count = length . words
```

`word_lengths` just takes a list of strings (as returned by `words`) and returns a list of the `length`s of those strings.

```idris
   word_lengths : List String -> List Nat
   word_lengths = map length
```

Point-free is the way to be, obviously.
