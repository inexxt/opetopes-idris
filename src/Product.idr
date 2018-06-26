module Product

import Opetope as O
import OpetopesUtils as OU
import Face as F
import FacesUtils as FU

import Data.AVL.Set as S
import Data.SortedBag as MS

import Debug.Trace as D

%access public export

dtrace : (Show a) => a -> a
dtrace x = D.trace (show x) x

dtrace' : a -> a
dtrace' x = D.trace "aaaa" x

dfs : FSet n -> FSet (S n) -> FSet (S n) -> ProdFace (S n) -> Opetope k1 -> Opetope k2 -> FSet (S (S n))
dfs ins used building_blocks target_out p q =
    let f = F.Face p q (S.toList used) target_out
        dd = dtrace "test" in
    if F.is_valid f
        then F.singleton f
        else F.unions [(dfs new_ins
                               new_used
                               building_blocks
                               target_out
                               p q) | b <- S.toList building_blocks,
                                      i <- S.toList ins,
                                      not (S.contains b used),
                                      let new_ins = (ins `S.union` (S.fromList (F.dom b))),
                                      let new_used = (b `S.insert` used)]

possible_faces : F.ProdFace (S n) -> List (F.ProdFace (S n)) -> Opetope k1 -> Opetope k2 -> FSet (S (S n))
possible_faces op building_blocks p q =
    dfs (F.singleton (F.cod op)) S.empty (S.fromList building_blocks) op p q


mul_0k : O.Opetope Z -> O.Opetope k -> F.ProdFace k
mul_0k p q = case q of
    (O.Point _) => F.Point p q
    (O.Arrow _ d c) => F.Arrow p q (F.Point d p) (F.Point c p)
    (O.Face _ d c) => F.Face p q (map (\s => mul_0k p s) d) (mul_0k p c)

base_case_0k : {k: Nat} -> O.Opetope Z -> O.Opetope k -> FU.FMap
base_case_0k {k} p q = FU.unions [FU.fromList (map (\s => mul_0k p s) (MS.toList $ OU.get n (OU.subopetopes p))) | n <- natRange k]

base_case_k0 : {k: Nat} -> O.Opetope k -> O.Opetope Z -> FU.FMap
base_case_k0 {k} p q = FU.unions [FU.fromList (map (\s => F.flip (mul_0k q s)) (MS.toList $ OU.get n (OU.subopetopes p))) | n <- natRange k]


getIf : List a -> Bool -> List a
getIf l b = if b then l else []

small_faces : O.Opetope (S k1) -> O.Opetope (S k2) -> FU.FMap
small_faces p q =
    let pt_pt = make from_point_and_point (subs p Z) (subs q Z)
        pt_ar = make from_point_and_arrow (subs p Z) (subs q (S Z))
        ar_pt = make from_arrow_and_point (subs p (S Z)) (subs q Z)
        ar_ar = make from_arrow_and_arrow (subs p (S Z)) (subs q (S Z))
        dd = dtrace "test" in
    FU.unions [pt_pt, pt_ar, ar_pt, ar_ar] where
        make : (O.Opetope n1 -> O.Opetope n2 -> ProdFace n3) -> List (O.Opetope n1) -> List (O.Opetope n2) -> FU.FMap
        make f l1 l2 = FU.fromList [f s1 s2 | s1 <- l1,
                                              s2 <- l2]
        subs : O.Opetope k -> (n: Nat) -> List (O.Opetope n)
        subs op n = MS.toList $ OU.get n (OU.subopetopes op)

big_product : Nat -> FU.FMap -> O.Opetope (S k1) -> O.Opetope (S k2) -> (FU.FMap, Nat)
big_product k curr_faces p q =
        if new_faces == S.empty then
            (curr_faces, k)
        else
            big_product (S k) (FU.fromFSet new_faces) p q
    where
        maxd : Nat
        maxd = (maximum (dim p) (dim q))
        build_new_opetopes : F.ProdFace (S k) -> FSet (S (S k))
        build_new_opetopes op = possible_faces op building_blocks p q where
            building_blocks : List (F.ProdFace (S k))
            building_blocks = [s | s <- S.toList $ FU.get (S k) curr_faces,
                                   op /= s]
        possible_codomains : List (F.ProdFace (S k))
        possible_codomains = [s | s <- faces] ++
                             (getIf [s | s <- faces,
                                              O.eq (p1 s) (cod p),
                                              O.eq (p2 s) (cod q)]
                                    ((S k) == maxd)) ++
                             (getIf [s | s <- faces,
                                              O.eq (p1 s) p,
                                              O.eq (p2 s) (cod q)]
                                    ((S k) == maxd && (dim p) < (dim q))) ++
                             (getIf [s | s <- faces,
                                              O.eq (p1 s) (cod p),
                                              O.eq (p2 s) q]
                                    ((S k) == maxd && (dim p) > (dim q))) where
            faces : List (ProdFace (S k))
            faces = S.toList $ curr_faces (S k)

        new_faces : F.FSet (S (S k))
        new_faces = F.unions $ map build_new_opetopes possible_codomains

product : {k1: Nat} -> {k2: Nat} -> O.Opetope k1 -> O.Opetope k2 -> (FU.FMap, Nat)
product {k1} {k2} p q = case (p, q) of
        ((Point _), _) =>  D.trace "x" (base_case_0k p q, dim q)
        (_, (Point _)) =>  D.trace "y" (base_case_k0 p q, dim p)
        (Arrow _ _ _, Arrow _ _ _) => D.trace "z" (big_product (maximum (dim p) (dim q)) (small_faces p q) p q)
        (Face _ _ _, Arrow _ _ _) => D.trace "w" (big_product (maximum (dim p) (dim q)) (small_faces p q) p q)
        (Arrow _ _ _, Face _ _ _) =>  D.trace "zz" (big_product (maximum (dim p) (dim q)) (small_faces p q) p q)
        (Face _ _ _, Face _ _ _) =>  D.trace "zzz" (big_product (maximum (dim p) (dim q)) (small_faces p q) p q)
    where
        dd : String
        dd = dtrace "test"


-- for some reason I can't do that
-- product : {k1: Nat} -> {k2: Nat} -> O.Opetope k1 -> O.Opetope k2 -> FU.FMap
-- product {k1} {k2} p q = case (decEq k1 Z, decEq k2 Z) of
--     (Yes prf, _) => base_case_0k (replace prf p) q
--     (_, Yes prf) => base_case_k0 p (replace prf q)
--     (_, _) => big_product (maximum (dim p) (dim q)) (small_faces p q) p q
