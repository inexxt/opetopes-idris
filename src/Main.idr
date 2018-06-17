module Main

import Opetope as O
import OpetopesUtils
import Face
import Contraction
import Product as P

a: Opetope Z
a = O.Point "a"
b: Opetope Z
b = O.Point "b"
ab1: Opetope (S Z)
ab1 = O.Arrow "ab1" a b
ab2: Opetope (S Z)
ab2 = O.Arrow "ab1" a b
alpha: Opetope (S (S Z))
alpha = O.Face "alpha" [ab1] ab2

op : String
op = show $ snd $ (P.product alpha alpha)

main : IO ()
main = putStrLn op
