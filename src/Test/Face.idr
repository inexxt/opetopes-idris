module Test.Face

import Face as F
import Test.Utils
import Opetope as O

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

matchEyeFace : IO ()
matchEyeFace = assert $ O.match $ F.embed p
