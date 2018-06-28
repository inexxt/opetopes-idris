module Face

import Opetope as O
import OpetopesUtils
import Data.AVL.Set as S
import Data.SortedBag as MS
-- import Subtype

import Dd
import Debug.Trace as D

import Utils as U

%access export

public export
data ProdFace : Nat -> Type where
    Point : O.Opetope Z -> O.Opetope Z -> ProdFace Z
    -- TODO there should be refinment types - it has to have p1, p2 of dim > 1
    Arrow : O.Opetope k1 -> O.Opetope k2 -> ProdFace Z -> ProdFace Z -> ProdFace (S Z)
    Face : O.Opetope k1 -> O.Opetope k2 -> List (ProdFace (S m)) -> ProdFace (S m) -> ProdFace (S (S m))

public export
flip : ProdFace n -> ProdFace n
flip (Point p q) = Point q p
flip (Arrow p q d c) = Arrow q p (flip d) (flip c)
flip (Face p q d c) = Face q p (map flip d) (flip c)


export
dom : (ProdFace (S n)) -> List (ProdFace n)
dom (Arrow _ _ d _) = [d]
dom (Face _ _ d _) = d

export
cod : (ProdFace (S n)) -> (ProdFace n)
cod (Arrow _ _ _ c) = c
cod (Face _ _ _ c) = c

public export
dim : {n: Nat} -> (ProdFace n) -> Nat
dim {n} _ = n


helper_dim: {n: Nat} -> (ProdFace n) -> Nat
helper_dim (Point _ _) = Z
helper_dim (Arrow _ _ _ _) = (S Z)
helper_dim (Face _ _ _ c) = S (dim c)

lemma_dim_eq_helper_dim: {n: Nat} -> (g: ProdFace n) -> dim g = helper_dim g
lemma_dim_eq_helper_dim {n = Z} (Point x y) = Refl
lemma_dim_eq_helper_dim {n = (S Z)} (Arrow x y z w) = Refl
lemma_dim_eq_helper_dim {n = (S (S m))} (Face x y xs z) = Refl

export
total
dim_p1 : ProdFace n -> Nat
dim_p1 (Point p _) = dim p
dim_p1 (Arrow p _ _ _) = dim p
dim_p1 (Face p _ _ _) = dim p


export
total
dim_p2 : ProdFace n -> Nat
dim_p2 (Point _ q) = dim q
dim_p2 (Arrow _ q _ _) = dim q
dim_p2 (Face _ q _ _) = dim q

total
lemma_of_dim_op : {n: Nat} -> (op: Opetope n) -> (n = (dim op))
lemma_of_dim_op {n = Z} (Point x) = Refl
lemma_of_dim_op {n = (S Z)} (Arrow x y z) = Refl
lemma_of_dim_op {n = (S (S k))} (Face x xs y) = Refl

total
lemma_of_dim_face : {n: Nat} -> (g: ProdFace n) -> (n = (dim g))
lemma_of_dim_face {n = Z} (Point x y) = Refl
lemma_of_dim_face {n = (S Z)} (Arrow x y z w) = Refl
lemma_of_dim_face {n = (S (S m))} (Face x y xs z) = Refl


export
p1 : (g: ProdFace n) -> Opetope (dim_p1 g)
p1 g = case g of
    (Point p _) => replace (lemma_of_dim_op p) p
    (Arrow p _ _ _) => replace (lemma_of_dim_op p) p
    (Face p _ _ _) => replace (lemma_of_dim_op p) p

export
p2 : (g: ProdFace n) -> Opetope (dim_p2 g)
p2 g = case g of
    (Point _ q) => replace (lemma_of_dim_op q) q
    (Arrow _ q _ _) => replace (lemma_of_dim_op q) q
    (Face _ q _ _) => replace (lemma_of_dim_op q) q

mutual
    public export
    Eq (ProdFace n) where
        (Point p q) == (Point p' q')           = (p, q) == (p', q')
        (Arrow p q d c) == (Arrow p' q' d' c') = O.eq p p' &&
                                                 O.eq q q' &&
                                                 (c, d) == (c', d')
        (Face p q d c) == (Face p' q' d' c')   = O.eq p p' &&
                                                 O.eq q q' &&
                                                 (c, sort d) == (c', sort d')

    public export
    Eq (ProdFace n) => Ord (ProdFace n) where
        compare (Point p q) (Point p' q')           = compare (p, q) (p', q')
        compare (Arrow p q d c) (Arrow p' q' d' c') = lexi_order (p, q, d, c) (p', q', d', c')
        compare (Face p q d c) (Face p' q' d' c')   = lexi_order (p, q, sort d, c) (p', q', sort d', c')

    lexi_order : (Ord a) => (Opetope n1, Opetope n2, a) -> (Opetope k1, Opetope k2, a) -> Ordering
    lexi_order (a1, a2, x) (b1, b2, y) = case (O.comp a1 b1, O.comp a2 b2, compare x y) of
        (LT, _, _) => LT
        (EQ, LT, _) => LT
        (EQ, EQ, LT) => LT
        (EQ, EQ, EQ) => EQ
        _ => GT


public export
Show (ProdFace n) where
    show (Point p q) = show p ++ show q
    show (Arrow p q d c) = (show $ 1) ++ "!(" ++ show [d] ++ " -> " ++ show c ++ ")"
    show (Face p q d c) = (show $ dim c + 1) ++ "!(" ++ show d ++ "->" ++ show c ++ ")"
    -- show (Arrow p q d c) = (show $ 1) ++ "!(" ++ show ((p, q)) ++ ": " ++ show [d] ++ " -> " ++ show c ++ ")"
    -- show (Face p q d c) = (show $ dim c + 1) ++ "!(" ++ show ((p, q)) ++ ": " ++ show d ++ "->" ++ show c ++ ")"

-- instance Subtype (ProdFace dim) where
--     type SuperType (ProdFace dim) = O.Opetope dim

name_of_op : O.Opetope k -> O.Opetope l -> String
name_of_op p q = show (p, q)


embed : {n:Nat} -> (g: ProdFace n) -> O.Opetope (dim g)
embed {n} op = case op of
        (Point p q) => O.Point (name_of_op p q)
        (Arrow p q d c) => O.Arrow (name_of_op p q) (embed d) (embed c)
        (Face p q d c) =>  O.Face (name_of_op p q) (map embed d) (embed c)

public export
match : ProdFace n -> Bool
match op = case op of
    (Point _ _) => True
    (Arrow _ _ _ _) => True
    (Face _ _ _ _) => O.match (embed op)


-- Projection : Type
-- Projection = {n: Nat}
--            -> (dim_px: ProdFace n -> Nat)
--            -> ((t: ProdFace n) -> Opetope (dim_px t))


all_eq : List (Opetope k) -> Opetope l -> Bool
all_eq ls op = U.and_ (map (\x => O.eq x op) ls)

transform_n_k : {n: Nat} -> (k: Nat) -> Opetope n -> Maybe (Opetope k)
transform_n_k k op = case decEq (dim op) k of
        Yes prf => Just (replace prf op)
        No _ => Nothing

-- contracted_eq : {k1: Nat} -> Opetope k1 -> Opetope k2 -> Bool
-- contracted_eq {k1=Z} op1 op2 = O.eq op1 op2
-- contracted_eq {k1=(S l)} op1 op2 = O.eq op1 op2 || ((all_eq ((O.cod op1)::(O.dom op1)) op2) &&
--                                          contracted_eq (cod op1) op2)

-- deep_p1_m : {n: Nat} -> (g: ProdFace n) -> Bool
-- deep_p1_m (Point p _) = True
-- deep_p1_m (Arrow p _ d c) = case p of
--     (O.Point _) => O.eq (p1 d) (p1 c) && O.eq p (p1 c)
--     (O.Arrow _ st fn) => O.eq (p1 d) st && O.eq (p1 c) fn
--     _ => False
-- deep_p1_m {n = (S (S m))} (Face p _ d c) =
--     (U.and_ (map deep_p1_m d)) && (deep_p1_m c) && case out of
--             Nothing => False
--             (Just x) => contracted_eq (O.Face (name p) ins x) p
--     where
--         ins : List (Opetope (S m))
--         ins = catMaybes $ map (\x => transform_n_k (S m) (p1 x)) d
--         out : Maybe (Opetope (S m))
--         out = transform_n_k (S m) (p1 c)


all_eq_lsts : List (Opetope k1) -> List (Opetope k2) -> Bool
all_eq_lsts (x::xs) (y::ys) = case decEq (dim x) (dim y) of
    Yes prf => (MS.fromList (replace prf xs)) == (MS.fromList ys)
    No _ => False

contracted_eq' : {k1: Nat} -> {k2: Nat} -> List (Opetope k1) -> Opetope k1 -> Opetope k2 -> Bool
contracted_eq' {k1=Z} {k2=Z} ins out op = all_eq (out::ins) op
contracted_eq' {k1=(S l1)} {k2=(S l2)} ins out op = (O.eq (cod op) out && all_eq_lsts ins (dom op)) ||
                            (all_eq ins out && contracted_eq' (dom out) (cod out) op)
contracted_eq' {k1=Z} {k2=(S l2)} ins out op = (O.eq (cod op) out && all_eq_lsts ins (dom op))
contracted_eq' {k1=(S l1)} {k2=Z} ins out op = (all_eq ins out && contracted_eq' (dom out) (cod out) op)

deep_p1_m : {n: Nat} -> (g: ProdFace n) -> Bool
deep_p1_m (Point p _) = True
deep_p1_m (Arrow p _ d c) = case p of
    (O.Point _) => O.eq (p1 d) (p1 c) && O.eq p (p1 c)
    (O.Arrow _ st fn) => O.eq (p1 d) st && O.eq (p1 c) fn
    _ => False
deep_p1_m {n = (S (S m))} (Face p _ d c) =
        (U.and_ (map deep_p1_m d)) && (deep_p1_m c) && (contracted_eq' ins out p)
    where
        out : Opetope (dim_p1 c)
        out = p1 c
        ins : List (Opetope (dim_p1 c))
        ins = catMaybes $ map (\x => transform_n_k (dim $ p1 c) (p1 x)) d


deep_p2_m : {n: Nat} -> (g: ProdFace n) -> Bool
deep_p2_m (Point _ q) = True
deep_p2_m (Arrow _ q d c) = case q of
    (O.Point _) => O.eq (p2 d) (p2 c) && O.eq q (p2 c)
    (O.Arrow _ st fn) => O.eq (p2 d) st && O.eq (p2 c) fn
    _ => False
deep_p2_m {n = (S (S m))} (Face _ q d c) =
        (U.and_ (map deep_p2_m d)) && (deep_p2_m c) && (contracted_eq' ins out q)
    where
        out : Opetope (dim_p2 c)
        out = p2 c
        ins : List (Opetope (dim_p2 c))
        ins = catMaybes $ map (\x => transform_n_k (dim $ p2 c) (p2 x)) d


export
is_valid : {n: Nat} -> ProdFace n -> Bool
is_valid {n} g = match g && deep_p1_m g && deep_p2_m g


export
from_point_and_point : O.Opetope Z -> O.Opetope Z -> ProdFace Z
from_point_and_point p1 p2 = Point p1 p2

export
from_arrow_and_point : O.Opetope (S Z) -> O.Opetope Z -> ProdFace (S Z)
from_arrow_and_point arr pt = let (O.Arrow _ d c) = arr in
    Arrow arr pt (Point d pt) (Point c pt)


export
from_point_and_arrow :  O.Opetope Z -> O.Opetope (S Z) -> ProdFace (S Z)
from_point_and_arrow pt arr = flip (from_arrow_and_point arr pt)

export
from_arrow_and_arrow : O.Opetope (S Z) -> O.Opetope (S Z) -> ProdFace (S Z)
from_arrow_and_arrow arr1 arr2 =
    let (O.Arrow _ d1 c1) = arr1
        (O.Arrow _ d2 c2) = arr2 in
            Arrow arr1 arr2 (Point d1 d2) (Point c1 c2)

public export
FSet : Nat -> Type
FSet n = S.Set (ProdFace n)

-- public export
-- Show (FSet n) where
--     show t = show (S.toList t)

export
singleton : {n: Nat} -> ProdFace n -> FSet n
singleton {n} op = S.insert op S.empty

export
unions : (Foldable t) => t (FSet n) -> FSet n
unions os = foldr S.union S.empty os
