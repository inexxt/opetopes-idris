module OpetopesUtils

import Data.SortedBag as MS
import Data.HVect as HV

import Opetope

%access public export


OMap : Type
OMap = (n: Nat) -> OSet n

empty: OMap
empty n = MS.empty

singleton : {n: Nat} -> (Opetope n) -> OMap
singleton {n} x = \k => case decEq n k of
    Yes prf => MS.singleton (replace prf x)
    No _ => MS.empty

get : (n:Nat) -> OMap -> OSet n
get n om = om n

union : OMap -> OMap -> OMap
union om1 om2 = \n => MS.union (get n om1) (get n om2)

unions : (List OMap) -> OMap
unions [] = empty
unions (x::xs) = x `union` (unions xs)


subopetopes : Opetope n -> OMap
subopetopes op = case op of
    (Point x) => singleton op
    (Arrow s d c) => unions $ [singleton op, subopetopes d, subopetopes c]
    (Face s d c) => unions $ [singleton op, (unions (map subopetopes d)), subopetopes c]

subouts : Opetope n -> OMap
subouts op = case op of
    (Point x) => empty
    (Arrow s d c) => singleton c
    (Face s d c) => unions [singleton c, (unions (map subouts d)), subouts c]


dmap: Functor f => (func : a -> b) -> f a -> f (Lazy b)
dmap func it = map (Delay . func) it


is_non_degenerated : Opetope n -> Bool
is_non_degenerated op = case op of
    (Point _) => True
    (Arrow _ d c) => c /= d
    (Face _ d c) => (and (dmap (is_non_degenerated) d)) && (is_non_degenerated c)


Show OMap where
    show t = show' t 0
        where
            show' : OMap -> Nat -> String
            show' t n = if (p == MS.empty) then ""
                        else ((show p) ++ ", " ++ (show' t (n + 1)))
                where
                    p : OSet n
                    p = t n
