module Face

import Opetope as O
import OpetopesUtils
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

convert : n=k -> Opetope n -> Opetope k
convert prf op = replace prf op

lemma_of_dim : (op: Opetope n) -> (n = (dim op))
lemma_of_dim = ?hole

export
p1 : (g: ProdFace n) -> Opetope (dim_p1 g)
p1 g = case g of
    (Point p _) => replace (lemma_of_dim p) p
    (Arrow p _ _ _) => replace (lemma_of_dim p) p
    (Face p _ _ _) => replace (lemma_of_dim p) p

export
p2 : (g: ProdFace n) -> Opetope (dim_p2 g)
p2 g = case g of
    (Point _ p) => replace (lemma_of_dim p) p
    (Arrow _ p _ _) => replace (lemma_of_dim p) p
    (Face _ p _ _) => replace (lemma_of_dim p) p


Eq (ProdFace n) where
    (Point p q) == (Point p' q') = p == p' && q == q'
    (Arrow p q d c) == (Arrow p' q' d' c') = O.eq p p' && O.eq q q' && d == d' && c == c'
    (Face p q d c) == (Face p' q' d' c') = O.eq p p' && O.eq q q' && d == d' && c == c'

lexi : (Opetope n1, Opetope n2) -> (Opetope k1, Opetope k2) -> Ordering
lexi (a1, a2) (b1, b2) = case comp a1 b1 of
    LT => LT
    GT => GT
    EQ => comp a2 b2

Eq (ProdFace n) => Ord (ProdFace n) where
    compare (Point p q) (Point p' q') = compare (p, q) (p', q')
    compare (Arrow p q _ _) (Arrow p' q' _ _) = lexi (p, q) (p', q')
    compare (Face p q _ _) (Face p' q' _ _) = lexi (p, q) (p', q')

-- instance Subtype (ProdFace dim) where
--     type SuperType (ProdFace dim) = O.Opetope dim 

embed : ProdFace n -> O.Opetope n
embed op = case op of
        (Point p q) => O.Point (name p q)
        (Arrow p q d c) => O.Arrow (name p q) (embed d) (embed c)
        (Face p q d c) => O.Face (name p q) (map embed d) (embed c)
    where
        name : Opetope k -> Opetope n -> String
        name p q = show (p, q)


dim : {n: Nat} -> ProdFace n -> Nat
dim {n} _ = n

match : ProdFace (S (S n)) -> Bool
match op = O.match (embed op)


-- data FaceE = forall n. FaceE (ProdFace n)

-- instance Eq FaceE where
--     (FaceE (Point x1 y1)) == (FaceE (Point x2 y2)) = x1 == x2 && y1 == y2
--     (FaceE (Arrow a1 x1 y1 _ _)) == (FaceE (Arrow a2 x2 y2 _ _)) = a1 == a2 && x1 == x2 && y1 == y2 -- Dlaczego to nie działa? Przecież powinno zejść rekurencyjnie ... && c == c' && d == d'
--     (FaceE (Face a1 x1 y1 _ _)) == (FaceE (Face a2 x2 y2 _ _)) = a1 == a2 && x1 == x2 && y1 == y2 -- j.w. && c == c' && d == d'

--     _ == _ = False

-- -- instance Ord FaceE where
-- --     (FaceE (Point a)) <= (FaceE (Point b)) = a <= b
-- --     (FaceE (Arrow a c d)) <= (FaceE (Arrow b c' d')) = a <= b -- j.w. (a, c, d) <= (b, c', d')
-- --     (FaceE (Face a c d)) <= (FaceE (Face b c' d')) = a <= b -- j.w. (a, c, d) <= (b, c', d')

-- --     (FaceE (Point _)) <= (FaceE (Arrow _ _ _)) = True
-- --     (FaceE (Point _)) <= (FaceE (Face _ _ _)) = True
-- --     (FaceE (Arrow _ _ _)) <= (FaceE (Face _ _ _)) = True


-- --     @staticmethod
-- --     def verify_construction(p1: Opetope, p2: Opetope, ins: 'Iterable[Face]' = (), out=None, name="") -> bool:
-- --         if not Opetope.match(ins, out, out.level + 1):
-- --             return False

-- --         face = Face(p1, p2, ins, out, name)

-- --         def get_pxs(f: 'Face', px) -> Opetope:
-- --             if not f.level:
-- --                 return Opetope(name=px(f).name)

-- --             out = get_pxs(f.out, px)
-- --             ins = [get_pxs(i, px) for i in f.ins if i.level == out.level]
-- --             return Opetope(ins=ins, out=out, name=px(f).name)  # (*)

-- --         op1 = get_pxs(face, lambda x: x.p1)
-- --         op2 = get_pxs(face, lambda x: x.p2)

-- --         # FIXME remove these
-- --         op1.name = "abecadło"  # I can trust in names of all things below me, but I can't in my name, as in (*)
-- --         op2.name = "abecadło"  # I can trust in names of all things below me, but I can't in my name, as in (*)

-- --         # We have to check here if this is a valid projection
-- --         # eg if all (recursivly) faces of self, projected on p1, together get us p1
-- --         # and similarly p2
-- --         if not (Opetope.is_valid_morphism(op1, p1) and Opetope.is_valid_morphism(op2, p2)):
-- --             return False

-- --         return True


-- from_arrow_and_point :: O.Opetope (S Z) -> O.Opetope Z -> ProdFace (S Z)
-- from_arrow_and_point arr pt = let (O.Arrow _ d c) = arr in
--     Arrow "" (em arr) (em pt) (Point d pt) (Point c pt)

-- -- we can't just use from_arrow_and_point, because the order p1, p2 is important
-- from_point_and_arrow ::  O.Opetope Z -> O.Opetope (S Z) -> ProdFace (S Z)
-- from_point_and_arrow pt arr = let (O.Arrow _ d c) = arr in
--     Arrow "" (em pt) (em arr) (Point pt d) (Point pt c)

-- from_arrow_and_arrow :: O.Opetope (S Z) -> O.Opetope (S Z) -> ProdFace (S Z)
-- from_arrow_and_arrow arr1 arr2 =
--     let (O.Arrow _ d1 c1) = arr1
--         (O.Arrow _ d2 c2) = arr2 in
--             Arrow "" (em arr1) (em arr2) (Point d1 d2) (Point c1 c2)
