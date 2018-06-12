module FacesUtils

import Face

-- import Data.SortedMap as M
-- this is this key moment - I want to have a function n:Nat -> FSet (Face n)
-- but implemented efficiently - either by SortedMap (might be impossible) or just a Vector
-- data FMap : Nat -> Type where
--     OMNil : FMap Z
--     OMCons : FMap n -> FSet (S n) -> FMap (S n)

FMap : Type
FMap = (n: Nat) -> FSet n

empty: FMap
empty n = emptyFSet {n}

singleton : {n: Nat} -> (ProdFace n) -> FMap
singleton {n} x = \k => case decEq n k of
   Yes prf => singletonFSet (replace prf x)
   No _ => emptyFSet

get : (n:Nat) -> FMap -> FSet n
get n om = om n

union : FMap -> FMap -> FMap
union om1 om2 = \n => unionFSet (get n om1) (get n om2)

unions : (List FMap) -> FMap
unions [] = empty
unions (x::xs) = x `union` (unions xs)

dmap: Functor f => (func : a -> b) -> f a -> f (Lazy b)
dmap func it = map (Delay . func) it
