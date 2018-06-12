module Face

import Opetope as O
import OpetopesUtils
import Data.AVL.Set as S
-- import Subtype

public export
data ProdFace : Nat -> Type where
    Point : O.Opetope Z -> O.Opetope Z -> ProdFace Z
    -- TODO there should be refinment types - it has to have p1, p2 of dim > 1
    Arrow : O.Opetope k1 -> O.Opetope k2 -> ProdFace Z -> ProdFace Z -> ProdFace (S Z)
    Face : O.Opetope k1 -> O.Opetope k2 -> List (ProdFace (S m)) -> ProdFace (S m) -> ProdFace (S (S m))

export
dom : (ProdFace (S n)) -> List (ProdFace n)
dom (Arrow _ _ d _) = [d]
dom (Face _ _ d _) = d

export
cod : (ProdFace (S n)) -> (ProdFace n)
cod (Arrow _ _ _ c) = c
cod (Face _ _ _ c) = c

export
dim : {n: Nat} -> (ProdFace n) -> Nat
dim {n} _ = n

helper_dim: {n: Nat} -> (ProdFace n) -> Nat
helper_dim (Point _ _) = Z
helper_dim (Arrow _ _ _ _) = (S Z)
helper_dim (Face _ _ _ c) = S (dim c)

lemma_dim_eq_helper_dim: {n: Nat} -> (g: ProdFace n) -> dim g = helper_dim g
lemma_dim_eq_helper_dim = ?hole

export
total
dim_p1 : ProdFace n -> Nat
dim_p1 (Point p _) = dim p
dim_p1 (Arrow p _ _ _) = dim p
dim_p1 (Face p _ _ _) = dim p


export
total
dim_p2 : ProdFace n -> Nat
dim_p2 (Point _ p) = dim p
dim_p2 (Arrow _ p _ _) = dim p
dim_p2 (Face _ p _ _) = dim p

lemma_zero : (dim (Point "a")) = Z
lemma_zero = ?hh11

lemma_of_dim_op : {n:Nat} -> (op: Opetope n) -> (n = (dim op))
lemma_of_dim_op {n = Z} (Point x) = ?hole_1
lemma_of_dim_op {n = (S Z)} (Arrow x y z) = ?hole_2
lemma_of_dim_op {n = (S (S k))} (Face x xs y) = ?hole_3

lemma_of_dim_face : (g: ProdFace n) -> (n = (dim g))
lemma_of_dim_face = ?hole6


export
p1 : (g: ProdFace n) -> Opetope (dim_p1 g)
p1 g = case g of
    (Point p _) => replace (lemma_of_dim_op p) p
    (Arrow p _ _ _) => replace (lemma_of_dim_op p) p
    (Face p _ _ _) => replace (lemma_of_dim_op p) p

export
p2 : (g: ProdFace n) -> Opetope (dim_p2 g)
p2 g = case g of
    (Point _ p) => replace (lemma_of_dim_op p) p
    (Arrow _ p _ _) => replace (lemma_of_dim_op p) p
    (Face _ p _ _) => replace (lemma_of_dim_op p) p

public export
Eq (ProdFace n) where
    (Point p q) == (Point p' q') = p == p' && q == q'
    (Arrow p q d c) == (Arrow p' q' d' c') = O.eq p p' && O.eq q q' && d == d' && c == c'
    (Face p q d c) == (Face p' q' d' c') = O.eq p p' && O.eq q q' && d == d' && c == c'

lexi : (Opetope n1, Opetope n2) -> (Opetope k1, Opetope k2) -> Ordering
lexi (a1, a2) (b1, b2) = case comp a1 b1 of
    LT => LT
    GT => GT
    EQ => comp a2 b2

public export
Eq (ProdFace n) => Ord (ProdFace n) where
    compare (Point p q) (Point p' q') = compare (p, q) (p', q')
    compare (Arrow p q _ _) (Arrow p' q' _ _) = lexi (p, q) (p', q')
    compare (Face p q _ _) (Face p' q' _ _) = lexi (p, q) (p', q')

-- instance Subtype (ProdFace dim) where
--     type SuperType (ProdFace dim) = O.Opetope dim

name_of_op : O.Opetope k -> O.Opetope l -> String
name_of_op p q = show (p, q)


embed : {n:Nat} -> (g: ProdFace n) -> O.Opetope (dim g)
embed {n} op = case op of
        (Point p q) => O.Point (name_of_op p q)
        (Arrow p q d c) => O.Arrow (name_of_op p q) (embed d) (embed c)
        (Face p q d c) =>  O.Face (name_of_op p q) (map embed d) (embed c)


match : ProdFace n -> Bool
match op = case op of
    (Point _ _) => True
    (Arrow _ _ _ _) => True
    (Face _ _ _ _) => O.match (embed op)


Projection : Type
Projection = {n: Nat} -> (dim_px: ProdFace n -> Nat) -> ((t: ProdFace n) -> Opetope (dim_px t))


all_eq : Opetope k -> List (ProdFace n) -> (dim_px: ProdFace n -> Nat) -> ((t: ProdFace n) -> Opetope (dim_px t)) -> Bool
all_eq p [] _ _ = True
all_eq p (x::Nil) _ pi = eq p (pi x)
all_eq p (x::xs) dim_px pi = (eq p (pi x)) && (all_eq p xs dim_px pi)



-- finally breaking from dependent types to Maybe monad
-- but there is no other way, since I have no control over internals
-- of opetopes projections inside ProdFace, so I can't construct Opetope n
deep_p1 : {n: Nat} -> (g: ProdFace n) -> Maybe (Opetope n)
deep_p1 {n} g =
    case decEq (dim_p1 g) n of
        Yes prf => case g of
            (Point p _) => Just (O.Point (name p))
            (Arrow p _ d c) => do
                d' <- deep_p1 d
                c' <- deep_p1 c
                pure (O.Arrow (name p) d' c')
            (Face p _ d c) =>  do
                d' <- sequence (map deep_p1 d)
                c' <- deep_p1 c
                pure (O.Face (name p) d' c')
        No _ => Nothing

mutual
    is_valid_contraction : ProdFace n -> Bool
    is_valid_contraction contr = case contr of
            (Point _ _) => True
            (Arrow _ _ _ _) => contract contr
            (Face _ _ _ _) => contract contr

    contract : {k: Nat} -> ProdFace (S k) -> Bool
    contract {k} contr = case compare (O.dim (p1 contr)) (S k) of
        EQ => case deep_p1 contr of
            (Just x) => eq (p1 contr) x
            Nothing => False
        LT => False
        GT => if (eq (p1 contr) (p1 (cod contr))) && (all_eq (p1 contr) ((cod contr)::(dom contr)) dim_p1 p1)
            then is_valid_contraction (cod contr)
            else False

export
is_valid : ProdFace n -> Bool
is_valid g = match g && is_valid_contraction g

-- --TODO shouldn't match work recursivly?
-- --TODO shouldn't verify work recursivly?

export
from_point_and_point : O.Opetope Z -> O.Opetope Z -> ProdFace Z
from_point_and_point p1 p2 = Point p1 p2

export
from_arrow_and_point : O.Opetope (S Z) -> O.Opetope Z -> ProdFace (S Z)
from_arrow_and_point arr pt = let (O.Arrow _ d c) = arr in
    Arrow arr pt (Point d pt) (Point c pt)


-- we can't just use from_arrow_and_point, because the order p1, p2 is important
export
from_point_and_arrow :  O.Opetope Z -> O.Opetope (S Z) -> ProdFace (S Z)
from_point_and_arrow pt arr = let (O.Arrow _ d c) = arr in
    Arrow pt arr (Point pt d) (Point pt c)

export
from_arrow_and_arrow : O.Opetope (S Z) -> O.Opetope (S Z) -> ProdFace (S Z)
from_arrow_and_arrow arr1 arr2 =
    let (O.Arrow _ d1 c1) = arr1
        (O.Arrow _ d2 c2) = arr2 in
            Arrow arr1 arr2 (Point d1 d2) (Point c1 c2)

export
FSet : Nat -> Type
FSet n = S.Set (ProdFace n)

-- Semigroup (FSet n) where
--     a <+> b = a `S.union` b
--
-- Monoid (FSet n) where
--     neutral = S.empty

export
emptyFSet : {n: Nat} -> FSet n
emptyFSet {n} = S.empty

export
singletonFSet : {n: Nat} -> ProdFace n -> FSet n
singletonFSet {n} op = S.insert op S.empty

export
unionFSet : {n: Nat} -> FSet n -> FSet n -> FSet n
unionFSet os1 os2 = S.union os1 os2

export
toListFSet : FSet n -> List (ProdFace n)
toListFSet os = S.toList os

export
fromListFSet : List (ProdFace n) -> FSet n
fromListFSet os = S.fromList os

export
containsFSet : ProdFace n -> FSet n -> Bool
containsFSet b op = S.contains b op

export
insertFSet : ProdFace n -> FSet n -> FSet n
insertFSet b op = S.insert b op
