module Text.Show.Extras where

showsTernaryWith
    :: (Int -> a -> ShowS)
    -> (Int -> b -> ShowS)
    -> (Int -> c -> ShowS)
    -> String -> Int -> a -> b -> c
    -> ShowS
showsTernaryWith sp1 sp2 sp3 n d x y z = showParen (d > 10)
    $ showString n
    . showChar ' '
    . sp1 11 x
    . showChar ' '
    . sp2 11 y
    . showChar ' '
    . sp3 11 z

showsQuadWith
    :: (Int -> a -> ShowS)
    -> (Int -> b -> ShowS)
    -> (Int -> c -> ShowS)
    -> (Int -> d -> ShowS)
    -> String -> Int -> a -> b -> c -> d
    -> ShowS
showsQuadWith sp1 sp2 sp3 sp4 n d x y z w = showParen (d > 10)
    $ showString n
    . showChar ' '
    . sp1 11 x
    . showChar ' '
    . sp2 11 y
    . showChar ' '
    . sp3 11 z
    . showChar ' '
    . sp4 11 w

showsQuintWith
    :: (Int -> a -> ShowS)
    -> (Int -> b -> ShowS)
    -> (Int -> c -> ShowS)
    -> (Int -> d -> ShowS)
    -> (Int -> e -> ShowS)
    -> String -> Int -> a -> b -> c -> d -> e
    -> ShowS
showsQuintWith sp1 sp2 sp3 sp4 sp5 n d x y z u v = showParen (d > 10)
    $ showString n
    . showChar ' '
    . sp1 11 x
    . showChar ' '
    . sp2 11 y
    . showChar ' '
    . sp3 11 z
    . showChar ' '
    . sp4 11 u
    . showChar ' '
    . sp5 11 v
