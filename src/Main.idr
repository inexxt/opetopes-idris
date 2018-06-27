module Main

import Opetope as O
import OpetopesUtils
import Face as F
import Product as P
import FacesUtils
import Utils as U

a: Opetope Z
a = O.Point "a"
b: Opetope Z
b = O.Point "b"
ab1: Opetope (S Z)
ab1 = O.Arrow "ab1" a b
ab2: Opetope (S Z)
ab2 = O.Arrow "ab2" a b
alpha: Opetope (S (S Z))
alpha = O.Face "alpha" [ab1] ab2

c: Opetope Z
c = O.Point "c"
d: Opetope Z
d = O.Point "d"
cd1: Opetope (S Z)
cd1 = O.Arrow "cd1" c d

pAC: F.ProdFace Z
pAC = F.Point a c
pAD: F.ProdFace Z
pAD = F.Point a d
pBC: F.ProdFace Z
pBC = F.Point b c
pBD: F.ProdFace Z
pBD = F.Point b d

ar1: F.ProdFace (S Z)
ar1 = (F.Arrow a cd1 pAC pAD)
ar2: F.ProdFace (S Z)
ar2 = (F.Arrow ab1 d pAD pBD)
ar3: F.ProdFace (S Z)
ar3 = (F.Arrow ab1 cd1 pAC pBD)

p : F.ProdFace (S (S Z))
p = F.Face ab1 cd1 [ar1, ar2] ar3

op : String
op = show $ (P.product alpha cd1)

main : IO ()
main = putStrLn $ op
