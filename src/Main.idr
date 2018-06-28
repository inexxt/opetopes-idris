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

aACAD: F.ProdFace (S Z)
aACAD = (F.Arrow a cd1 pAC pAD)
aADBD1: F.ProdFace (S Z)
aADBD1 = (F.Arrow ab1 d pAD pBD)
aACBD1: F.ProdFace (S Z)
aACBD1 = (F.Arrow ab1 cd1 pAC pBD)
aACBD2: F.ProdFace (S Z)
aACBD2 = (F.Arrow ab2 cd1 pAC pBD)

s1 : F.ProdFace 2
s1 = F.Face ab1 cd1 [aACAD, aADBD1] aACBD1
s2 : ProdFace 2
s2 = F.Face alpha cd1 [aACAD, aADBD1] aACBD2
s3 : ProdFace 2
s3 = F.Face alpha cd1 [aACBD1] aACBD2

sd : ProdFace 3
sd = F.Face alpha cd1 [s3, s1] s2

-- p : F.ProdFace (S (S Z))
-- p = F.Face ab1 cd1 [aACAD, aADBD] aACBD

op : String
op = show $ (P.product alpha cd1)

-- main = putStrLn $ (show $ is_valid sd)
main : IO ()
main = putStrLn $ (show $ op)
