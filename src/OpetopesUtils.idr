 module OpetopeUtils

import Data.SortedBag as MS

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

-- f : (n: Nat) -> (k: Nat) -> Opetope n
-- f n k with (decEq k n)
--     f _ k | (Yes prf) = replace prf (build_op k)
--     f n k | (No _) = build_op n

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

-- export
-- is_valid_contraction : Contraction n -> Bool
-- is_valid_contraction c = ?hole


dmap: Functor f => (func : a -> b) -> f a -> f (Lazy b)
dmap func it = map (Delay . func) it

eq : {n1: Nat} -> {n2: Nat} -> Opetope n1 -> Opetope n2 -> Bool
eq {n1} {n2} op1 op2 = case decEq n1 n2 of
    Yes prf => (replace prf op1) == op2
    No _ => False


dec : Nat -> Nat
dec Z = Z
dec (S n) = n

all_eq : (Eq a) => List a -> Bool
all_eq p xs = and $ dmap (\t => t == p) xs

is_valid_contraction : Contraction n -> Bool 
is_valid_contraction contr = case contr of
        (CPoint _ _) => eq (p1 contr) (p2 contr)
        (CArrow _ _ _ _) => eq (p1 contr) (p2 contr) -- niebezpieczne, sprawdzić
        (CFace _ _ _ _) => contract' contr
    where
        contract' : {k: Nat} -> Contraction (S (S k)) -> Bool
        contract' {k} contr = case compare (dim (p1 contr)) (S (S k)) of
            EQ => eq (p1 contr) (p2 contr)
            LT => False
            GT => if all_eq (p1 contr) ((nameC (codC contr))::(map name (domC contr)))
                then is_valid_contraction (domC contr)
                else False

export
is_non_degenerated : Opetope n -> Bool
is_non_degenerated op = case op of
    (Point _) => True
    (Arrow _ d c) => c /= d
    (Face _ d c) => (and (dmap (is_non_degenerated) d)) && (is_non_degenerated c)