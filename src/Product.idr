module Product

import Opetope as O
import OpetopesUtils as OU
import Face as F
import FacesUtils as FU

import Data.AVL.Set as S
import Data.SortedBag as MS

import Dd
import Debug.Trace as D

import Utils as U

%access public export

dfs : FSet n -> FSet (S n) -> FSet (S n) -> ProdFace (S n) -> Opetope k1 -> Opetope k2 -> FSet (S (S n))
dfs ins used building_blocks target_out p q =
    let f = F.Face p q (S.toList used) target_out in
    if F.is_valid f
        then F.singleton f
        else F.unions [(dfs new_ins
                            new_used
                            building_blocks
                            target_out
                            p q) | b <- S.toList building_blocks,
                                   i <- S.toList ins,
                                   not (S.contains b used),
                                   S.contains (cod b) (holes_to_fill used target_out),
                                   let new_ins = (ins `S.union` (S.fromList (F.dom b))),
                                   let new_used = (b `S.insert` used)]
    where
        holes_to_fill : FSet (S n) -> ProdFace (S n) -> FSet n
        holes_to_fill s t = (S.insert (F.cod t) (S.fromList (concat $ map F.dom (S.toList s)))
                           `S.difference`
                           (S.fromList $ map F.cod (S.toList s)))
possible_faces : F.ProdFace (S n) -> List (F.ProdFace (S n)) -> Opetope k1 -> Opetope k2 -> FSet (S (S n))
possible_faces op building_blocks p q =
    dfs (F.singleton (F.cod op)) S.empty (S.fromList building_blocks) op p q


mul_0k : O.Opetope Z -> O.Opetope k -> F.ProdFace k
mul_0k p q = case q of
    (O.Point _) => F.Point p q
    (O.Arrow _ d c) => F.Arrow p q (F.Point p d) (F.Point p c)
    (O.Face _ d c) => F.Face p q (map (\s => mul_0k p s) d) (mul_0k p c)

mul_k0 : O.Opetope k -> O.Opetope Z -> F.ProdFace k
mul_k0 p q = case p of
    (O.Point _) => F.Point p q
    (O.Arrow _ d c) => F.Arrow p q (F.Point d q) (F.Point c q)
    (O.Face _ d c) => F.Face p q (map (\s => mul_k0 s q) d) (mul_k0 c q)


base_case_0k : {k: Nat} -> O.Opetope Z -> O.Opetope k -> FU.FMap
base_case_0k {k} p q = FU.unions [FU.fromList (map (\s => mul_0k p s) (MS.toList $ (OU.subopetopes q n))) | n <- natRange (S k)]

base_case_k0 : {k: Nat} -> O.Opetope k -> O.Opetope Z -> FU.FMap
base_case_k0 {k} p q = FU.unions [FU.fromList (map (\s => mul_k0 s q) (MS.toList $ (OU.subopetopes p n))) | n <- natRange (S k)]


getIf : List a -> Bool -> List a
getIf l b = if b then l else []


big_product : Nat -> FU.FMap -> O.Opetope (S k1) -> O.Opetope (S k2) -> (FU.FMap, Nat)
big_product (S (S k)) curr_faces p q =
        if new_faces == S.empty && k > 1 then
            (curr_faces, (S (S k)))
        else
            big_product (S (S (S k))) (FU.union (FU.fromFSet new_faces) curr_faces) p q
    where
        maxd : Nat
        maxd = (maximum (dim p) (dim q))
        build_new_opetopes : F.ProdFace (S k) -> FSet (S (S k))
        build_new_opetopes op = possible_faces op building_blocks p q where
            building_blocks : List (F.ProdFace (S k))
            building_blocks = [s | s <- S.toList $ curr_faces (S k),
                                   op /= s]
        possible_codomains : List (F.ProdFace (S k))
        possible_codomains = [s | s <- faces,
                                       O.eq (p1 s) p,
                                       O.eq (p2 s) q] ++
                             (getIf [s | s <- faces,
                                              O.eq (p1 s) (cod p),
                                              O.eq (p2 s) (cod q)]
                                    ((S (S k)) == maxd)) ++
                             (getIf [s | s <- faces,
                                              O.eq (p1 s) p,
                                              O.eq (p2 s) (cod q)]
                                    ((S (S k)) == maxd && (dim p) < (dim q))) ++
                             (getIf [s | s <- faces,
                                              O.eq (p1 s) (cod p),
                                              O.eq (p2 s) q]
                                    ((S (S k)) == maxd && (dim p) > (dim q))) where
            faces : List (ProdFace (S k))
            faces = S.toList $ curr_faces (S k)

        new_faces : F.FSet (S (S k))
        new_faces = F.unions $ map build_new_opetopes possible_codomains


mutual
    small_faces : {k1: Nat} -> {k2: Nat} -> O.Opetope (S k1) -> O.Opetope (S k2) -> FU.FMap
    small_faces {k1} {k2} p q =
        let pt_pt = make from_point_and_point (subs p Z) (subs q Z)
            pt_ar = make from_point_and_arrow (subs p Z) (subs q (S Z))
            ar_pt = make from_arrow_and_point (subs p (S Z)) (subs q Z)
            ar_ar = make from_arrow_and_arrow (subs p (S Z)) (subs q (S Z)) in
        FU.unions ([pt_pt, pt_ar, ar_pt, ar_ar] ++ small_products) where
            make : (a -> b -> ProdFace nk) -> List a -> List b -> FU.FMap
            make f l1 l2 = FU.fromList $ U.cart_prod_with f l1 l2
            subs : O.Opetope k -> (n: Nat) -> List (O.Opetope n)
            subs op n = MS.toList $ OU.subopetopes op n
            small_products : List (FU.FMap)
            small_products =  [fst (product r s) | n1 <- U.natFromTo Z (S k1),
                                             n2 <- U.natFromTo Z (S k2),
                                             r <- subs p n1,
                                             s <- subs q n2,
                                             n1 < (S k1) || n2 < (S k2),
                                             n1 > Z || n2 > Z]

    product : {k1: Nat} -> {k2: Nat} -> O.Opetope k1 -> O.Opetope k2 -> (FU.FMap, Nat)
    product {k1} {k2} p q = case (p, q) of
            ((Point _), _) => (base_case_0k p q, dim q)
            (_, (Point _)) => (base_case_k0 p q, dim p)
            (Arrow _ _ _, Arrow _ _ _) => (big_product (S (S Z)) (small_faces p q) p q)
            (Face _ _ _, Arrow _ _ _) => (big_product (maximum (dim p) (dim q)) (small_faces p q) p q)
            (Arrow _ _ _, Face _ _ _) => (big_product (maximum (dim p) (dim q)) (small_faces p q) p q)
            (Face _ _ _, Face _ _ _) => (big_product (maximum (dim p) (dim q)) (small_faces p q) p q)
