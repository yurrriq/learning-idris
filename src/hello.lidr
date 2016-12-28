= hello.lidr

> module Main
>
> main : IO ()

Add a hole to stand in place of a conversion.

```idris
main = putStrLn (?convert 'x')
```

An appropriate `Char -> String` function to fill the `convert` hole is
[`cast`](http://www.idris-lang.org/docs/current/prelude_doc/docs/Prelude.Cast.html#Prelude.Cast.cast).

> main = putStrLn (cast 'x')

= Compile and Run

Compile:

```fish
$ make compile
idris src/hello.lidr -o bin/hello
```

Run:

```fish
$ bin/hello
x
```
