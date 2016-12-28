Elaborator Reflection: Extending Idris in Idris
===============================================

[🎥 YouTube](https://www.youtube.com/watch?v=pqFgYCdiYz4)

```idris
module Magic
```

`Pruviloj.Core` provides `try`.

```idris
import Pruviloj.Core
```

`Pruviloj.Induction` provides `induction`.

```idris
import Pruviloj.Induction
```

```idris
%language ElabReflection
%access export
%default total
```

Tactics
-------

[🕑 13:50](https://youtu.be/pqFgYCdiYz4?t=13m50s)

```idris
auto : Elab ()
auto = do compute
          attack
          try intros
          hs <- map fst <$> getEnv
          for_ hs $
            \ih => try (rewriteWith (Var ih))
          hypothesis <|> search' 100 []
          solve
```

[🕒 14:44](https://youtu.be/pqFgYCdiYz4?t=14m44s)

```idris
partial
mush : Elab ()
mush =
    do attack
       n <- gensym "j"
       intro n
       try intros
       induction (Var n) `andThen` auto
       solve
```

🔮 Magic
-------

### Prelude.Nat.plusAssociative

[🕒 14:59](https://youtu.be/pqFgYCdiYz4?t=14m59s)

``` idris
plusAssociative : (left, centre, right : Nat) ->
                  left + (centre + right) = (left + centre) + right
plusAssociative Z        centre right = Refl
plusAssociative (S left) centre right =
    let inductiveHypothesis = plusAssociative left centre right in
        rewrite inductiveHypothesis in Refl
```

```idris
plusAssoc : (j, k, l : Nat) ->
            (j + k) + l = j + (k + l)
plusAssoc = %runElab mush
```

### Prelude.Nat.plusZeroRightNeutral

``` idris
plusZeroRightNeutral : (left : Nat) -> left + 0 = left
plusZeroRightNeutral Z     = Refl
plusZeroRightNeutral (S n) =
    let inductiveHypothesis = plusZeroRightNeutral n in
        rewrite inductiveHypothesis in Refl
```

```idris
plusZeroR : (k : Nat) -> k + 0 = k
plusZeroR = %runElab mush
```

### Prelude.Nat.plusSuccRightSucc

[🕒 15:14](https://youtu.be/pqFgYCdiYz4?t=15m14s)

``` idris
plusSuccRightSucc : (left, right : Nat) ->
                    S (left + right) = left + (S right)
plusSuccRightSucc Z right        = Refl
plusSuccRightSucc (S left) right =
    let inductiveHypothesis = plusSuccRightSucc left right in
        rewrite inductiveHypothesis in Refl
```

```idris
plusSRightS : (left, right : Nat) ->
              S (left + right) = left + (S right)
plusSRightS = %runElab mush
```

### Prelude.Nat.multOneRightNeutral

``` idris
multOneLeftNeutral : (right : Nat) -> 1 * right = right
multOneLeftNeutral Z         = Refl
multOneLeftNeutral (S right) =
    let inductiveHypothesis = multOneLeftNeutral right in
        rewrite inductiveHypothesis in Refl
```

```idris
multOneLNeutral : (right : Nat) ->
                  1 * right = right
multOneLNeutral = %runElab mush
```

### Prelude.Nat.plusMinusLeftCancel

[🕞 15:20](https://youtu.be/pqFgYCdiYz4?t=15m20s)

``` idris
plusMinusLeftCancel : (left, right, right' : Nat) ->
                      minus (left + right) (left + right') = minus right right'
plusMinusLeftCancel Z right right'        = Refl
plusMinusLeftCancel (S left) right right' =
    let inductiveHypothesis = plusMinusLeftCancel left right right' in
        rewrite inductiveHypothesis in Refl
```

```idris
plusMinusLeftCancel : (left, right, right' : Nat) ->
                      minus (left + right) (left + right') =
                      minus right right'
plusMinusLeftCancel = %runElab mush
```

### Prelude.Nat.powerOneNeutral

[🕞 15:25](https://youtu.be/pqFgYCdiYz4?t=15m25s)

``` idris
powerOneNeutral : (base : Nat) -> power base 1 = base
powerOneNeutral Z        = Refl
powerOneNeutral (S base) =
    let inductiveHypothesis = powerOneNeutral base in
        rewrite inductiveHypothesis in Refl
```

```idris
powerOneNeutral : (base : Nat) ->
                  power base 1 = base
powerOneNeutral = %runElab mush
```

### Prelude.List.mapPreservesLength

[🕞 15:30](https://youtu.be/pqFgYCdiYz4?t=15m30s)

``` idris
mapPreservesLength : (f : a -> b) -> (l : List a) ->
                     length (map f l) = length l
mapPreservesLength f []      = Refl
mapPreservesLength f (x::xs) =
    let inductiveHypothesis = mapPreservesLength f xs in
        rewrite inductiveHypothesis in Refl
```

FIXME: this fails in Idris 0.99

``` idris
mapPreservesLen : (f : a -> b) -> (l : List a) ->
                  length (map f l) = length l
mapPreservesLen = %runElab mush
```

    When checking right hand side of mapPreservesLen with expected type
            (f : a -> b) -> (l : List a) -> length (map f l) = length l

    a -> b is not an inductive family

Thanks to @Melvar on IRC, I learned that error message basically says, "I can't
generate an induction principle for `f`, because it's a function, not data."

An *inductive family* is the formal name for what you define with a data
declaration.

The solution then is to put `f` on the left-hand side, so we do induction on
`l`, which, unlike `f`, **is** an *inductive family*. 😄

[Looking back at the video](https://youtu.be/pqFgYCdiYz4?t=15m30s) after a few
hours of sleep, @david-christiansen indeed put `f` on the left-hand side and I
previously made a typo.

```idris
mapPreservesLen : (f : a -> b) -> (l : List a) ->
                  length (map f l) = length l
mapPreservesLen f = %runElab mush
```

### Prelude.List.lengthAppend

``` idris
lengthAppend : (left : List a) -> (right : List a) ->
               length (left ++ right) = length left + length right
lengthAppend []      right = Refl
lengthAppend (x::xs) right =
   let inductiveHypothesis = lengthAppend xs right in
       rewrite inductiveHypothesis in Refl
```

```idris
lenAppend : (left, right : List a) ->
            length (left ++ right) =
            length left + length right
lenAppend = %runElab mush
```

### Prelude.List.appendNilRightNeutral

[🕓 15:40](https://youtu.be/pqFgYCdiYz4?t=15m40s)

``` idris
appendNilRightNeutral : (l : List a) -> l ++ [] = l
appendNilRightNeutral []      = Refl
appendNilRightNeutral (x::xs) =
    let inductiveHypothesis = appendNilRightNeutral xs in
        rewrite inductiveHypothesis in Refl
```

```idris
appendNilRightId : (l : List a) ->
                   l ++ [] = l
appendNilRightId = %runElab mush
```

-- Local Variables:
-- idris-interpreter-flags: ("-p" "pruviloj")
-- End:
