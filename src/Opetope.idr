module Opetope

import Data.SortedBag as MS

public export
data Opetope : Nat -> Type where
    Point : String -> Opetope Z
    Arrow : String -> Opetope Z -> Opetope Z -> Opetope (S Z)
    Face : String -> List (Opetope (S n)) -> Opetope (S n) -> Opetope (S (S n))

public export
data Contraction : n -> Type where
    CPoint : Opetope Z -> String -> Contraction Z
    CArrow : Opetope k -> String -> Contraction Z -> Contraction Z -> Contraction (S Z)
    CFace : Opetope k -> String -> List (Contraction (S n)) -> Contraction (S n) -> Contraction (S (S n))

export
p1 : Contraction n -> Opetope k
p1 (CPoint p _) = p
p1 (CArrow p _ _ _) = p
p1 (CFace p _ _ _) = p

export
p2 : Contraction n -> Opetope n
p2 (CPoint _ s) = Point s
p2 (CArrow _ s d c) = Arrow s (p2 d) (p2 c)
p2 (CFace _ s d c) = Face s (map p2 d) (p2 c)


-- public export
-- data MOpetope: a -> Nat -> Type where
--     Point : a -> Opetope a Z
--     Arrow : a -> Opetope a Z -> Opetope a Z -> Opetope a (S Z)
--     Face : a -> List (Opetope a (S n)) -> Opetope a (S n) -> Opetope a (S (S n))


export
dim : {n: Nat} -> Opetope n -> Nat
dim {n} _ = n

add : (n: Nat) -> Nat
add n = S n

export
mkOpetope : {k: Nat} -> String -> List (Opetope k) -> Opetope k -> Opetope (S k)
mkOpetope {k} s ds c = case ds of
    (d::Nil) => case decEq k Z of
        -- tu się dzieje magia
        Yes prf => replace (sym (cong {f=S} prf)) (Arrow s (replace prf d) (replace prf c)) 
        No _ => ?hole1 -- (Face s ds c)
    _ => ?hole2 -- (Face s ds c)
    

-- eq : Eq a => List a -> List a -> Bool
-- eq Nil (x::xs) = False
-- eq (x::xs) Nil = False
-- eq Nil Nil = True
-- eq (x::xs) (y::ys) = (x == y) && (eq xs ys) 


export
Show (Opetope n) where
    show (Point s)     = s
    show (Arrow s d c) = unwords $ [(show ((dim c) + 1)), "[", s, ":", (show d), " -> ", (show c), "]"]
    show (Face s d c)  = unwords $ [(show ((dim c) + 1)), "[", s, ":", (show d), " -> ", (show c), "]"]



-- TODO change the equality
export
Eq (Opetope n) where
    (Point s1) == (Point s2) = s1 == s2
    (Arrow s1 d1 c1) == (Arrow s2 d2 c2) = s1 == s2-- compare (s1, d1, c1) (s2, d2, c2)
    (Face s1 d1 c1) == (Face s2 d2 c2) = s1 == s2 -- compare (s1, d1, c1) (s2, d2, c2)


export
Eq (Opetope n) => Ord (Opetope n) where
    compare (Point s1) (Point s2) = compare s1 s2
    compare (Arrow s1 d1 c1) (Arrow s2 d2 c2) = compare s1 s2-- compare (s1, d1, c1) (s2, d2, c2)
    compare (Face s1 d1 c1) (Face s2 d2 c2) = compare s1 s2 -- compare (s1, d1, c1) (s2, d2, c2)


-- somewhere else
-- compare (Point _) (Arrow _ _ _) = LT
-- compare (Point _) (Face _ _ _) = LT
-- compare (Arrow _ _ _) (Face _ _ _) = LT


-- export
-- Show (Opetope n) where
--     show op = case op of
--             (Point s) => s
--             (Arrow s d c) => show' s [d] c
--             (Face s d c) => show' s d c
--         where
--             show' : String -> (List (Opetope k)) -> Opetope k -> String
--             show' s d c = unwords $ [(show ((dim c) + 1)), "[", s, ":", (show d), " -> ", (show c), "]"]

export
build_op : (n: Nat) -> Opetope n
build_op Z = Point "a"
build_op (S Z) = Arrow "b" (build_op Z) (build_op Z)
-- build_op (S n) = Face "c" [(build_op n)] (build_op n) -- for some reason, doesn't work
build_op (S (S n)) = Face "c" [(build_op (S n))] (build_op (S n))

export
dom : (Opetope (S n)) -> List (Opetope n)
dom (Arrow _ d _) = [d]
dom (Face _ d _) = d

export
cod : (Opetope (S n)) -> Opetope n
cod (Arrow _ _ c) = c
cod (Face _ _ c) = c

export
domC : (Contraction (S n)) -> List (Contraction n)
domC (CArrow _ _ d _) = [d]
domC (CFace _ _ d _) = d

export
domC : (Contraction (S n)) -> (Contraction n)
codC (CArrow _ _ _ c) = c
codC (CFace _ _ _ c) = c


export
OSet : Nat -> Type
OSet n = MS.SortedBag (Opetope n)

export
emptyOSet : {n: Nat} -> OSet n
emptyOSet {n} = MS.empty

export
singletonOSet : {n: Nat} -> Opetope n -> OSet n
singletonOSet {n} op = MS.singleton op

export
unionOSet : {n: Nat} -> OSet n -> OSet n -> OSet n
unionOSet os1 os2 = MS.union os1 os2

export
are_equal : (OSet n) -> (OSet n) -> Bool
are_equal ms1 ms2 = (MS.toList ms1) == (MS.toList ms2)

export
match : {n: Nat} -> List (Opetope (S n)) -> Opetope (S n) -> Bool
match {n} ins out = are_equal (all_dom `MS.union` out_cod) (all_cod `MS.union` out_cod)
    where
        all_dom : OSet n
        all_dom = MS.fromList (concat $ map dom ins)
        out_dom : OSet n
        out_dom = MS.fromList (dom out)
        all_cod : OSet n
        all_cod = MS.fromList (map cod ins)
        out_cod : OSet n
        out_cod = MS.singleton (cod out)

export
is_unary : Opetope (S dim) -> Bool
is_unary op = (length (dom op)) == 1