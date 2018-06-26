module Main

import Opetope as O
import OpetopesUtils
import Face
import Product as P
import FacesUtils

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

c: Opetope Z
c = O.Point "c"
d: Opetope Z
d = O.Point "d"
cd1: Opetope (S Z)
cd1 = O.Arrow "cd1" c d

op : String
op = show $ (P.product ab1 cd1)

main : IO ()
main = putStrLn op
