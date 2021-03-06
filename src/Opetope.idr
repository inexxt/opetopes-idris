module Opetope

import Data.SortedBag as MS

import Dd
import Debug.Trace as D

import Utils as U


public export
data Opetope : Nat -> Type where
    Point : String -> Opetope Z
    Arrow : String -> Opetope Z -> Opetope Z -> Opetope (S Z)
    Face : String -> List (Opetope (S n)) -> Opetope (S n) -> Opetope (S (S n))


export
name : Opetope n -> String
name (Point s) = s
name (Arrow s _ _) = s
name (Face s _ _) = s

public export
dim : {n: Nat} -> Opetope n -> Nat
dim {n} _ = n

lemma_zero : (dim (Point "a")) = Z
lemma_zero = Refl


-- export
-- mkOpetope : {k: Nat} -> String -> List (Opetope k) -> Opetope k -> Opetope (S k)
-- mkOpetope {k} s ds c = case ds of
--     (d::Nil) => case decEq k Z of
--         Yes prf => replace (sym (cong {f=S} prf)) (Arrow s (replace prf d) (replace prf c))
--         No _ => ?hole1 -- (Face s ds c) -- i teraz mam udowodnić, że jest k = S l...
--     _ => ?hole2 -- (Face s ds c) -- i tu też muszę to dowodzić


export
Show (Opetope n) where
    show (Point s)     = s
    show (Arrow s d c) = "(" ++ s ++ ": " ++ show [d] ++ " -> " ++ show c ++ ")"
    show (Face s d c)  = "(" ++ s ++ ": " ++ show d ++ " -> " ++ show c ++ ")"


mutual
    public export
    Eq (Opetope n) where
        (Point s1) == (Point s2) = s1 == s2
        (Arrow s1 d1 c1) == (Arrow s2 d2 c2) = (s1, d1, c1) == (s2, d2, c2)
        (Face s1 d1 c1) == (Face s2 d2 c2) = (s1, sort d1, c1) == (s2, sort d2, c2)

    public export
    Eq (Opetope n) => Ord (Opetope n) where
        compare (Point s1) (Point s2) = compare s1 s2
        compare (Arrow s1 d1 c1) (Arrow s2 d2 c2) = compare (s1, d1, c1) (s2, d2, c2)
        compare (Face s1 d1 c1) (Face s2 d2 c2) = compare (s1, sort d1, c1) (s2, sort d2, c2)

export
build_op : (n: Nat) -> Opetope n
build_op Z = Point "a"
build_op (S Z) = Arrow "b" (build_op Z) (build_op Z)
build_op (S (S n)) = Face "c" [(build_op (S n))] (build_op (S n))

export
dom : (Opetope (S n)) -> List (Opetope n)
dom (Arrow _ d _) = [d]
dom (Face _ d _) = d

export
cod : (Opetope (S n)) -> Opetope n
cod (Arrow _ _ c) = c
cod (Face _ _ c) = c

public export
OSet : Nat -> Type
OSet n = MS.SortedBag (Opetope n)

-- should work, since toList is keeping lists sorted
public export
Eq (OSet n) where
    a == b = (MS.toList a) == (MS.toList b)

public export
Show (OSet n) where
    show a = show (MS.toList a)

export
match : {n: Nat} -> Opetope n -> Bool
match {n=Z} _ = True
match {n=(S Z)} _ = True
match {n=(S (S k))} (Face _ ins out) = (all_dom `MS.union` out_cod) == (all_cod `MS.union` out_dom) && U.and_ (map match ins) && match out
    where
        all_dom : OSet k
        all_dom = MS.fromList (concat $ map dom ins)
        out_dom : OSet k
        out_dom = MS.fromList (dom out)
        all_cod : OSet k
        all_cod = MS.fromList (map cod ins)
        out_cod : OSet k
        out_cod = MS.singleton (cod out)

export
is_unary : Opetope (S dim) -> Bool
is_unary op = (length (dom op)) == 1


export
eq : {n1: Nat} -> {n2: Nat} -> Opetope n1 -> Opetope n2 -> Bool
eq {n1} {n2} op1 op2 = case decEq n1 n2 of
    Yes prf => (replace prf op1) == op2
    No _ => False

export
comp : {n1: Nat} -> {n2: Nat} -> Opetope n1 -> Opetope n2 -> Ordering
comp {n1} {n2} op1 op2 = case decEq n1 n2 of
    Yes prf => compare (replace prf op1) op2
    No _ => compare n1 n2
