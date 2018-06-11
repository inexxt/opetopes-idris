 module OpetopeUtils

import Data.SortedBag as MS
import Data.HVect as HV

import Opetope

-- import Data.SortedMap as M
-- this is this key moment - I want to have a function n:Nat -> OSet (Opetope n)
-- but implemented efficiently - either by SortedMap (might be impossible) or just a Vector
-- data OMap : Nat -> Type where
--     OMNil : OMap Z
--     OMCons : OMap n -> OSet (S n) -> OMap (S n)

OMap : Type
OMap = (n: Nat) -> OSet n

empty: OMap
empty n = emptyOSet {n}

singleton : {n: Nat} -> (Opetope n) -> OMap
singleton {n} x = \k => case decEq n k of
    Yes prf => singletonOSet (replace prf x)
    No _ => emptyOSet

get : (n:Nat) -> OMap -> OSet n
get n om = om n

union : OMap -> OMap -> OMap
union om1 om2 = \n => unionOSet (get n om1) (get n om2)

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

export
is_non_degenerated : Opetope n -> Bool
is_non_degenerated op = case op of
    (Point _) => True
    (Arrow _ d c) => c /= d
    (Face _ d c) => (and (dmap (is_non_degenerated) d)) && (is_non_degenerated c)
