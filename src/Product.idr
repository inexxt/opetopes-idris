module Product

import Opetope as O
import OpetopesUtils as OU
import Face as F
import FacesUtils as FU

import Data.AVL.Set as S

-- data OpetopeOrder n where
--     OpetopeOrder : {op: O.Opetope n, ord: S.Set (OU.OpetopeE -> OU.OpetopeE) } -> OpetopeOrder n-- TODO undefined


-- doesn't work
-- Semigroup (FSet n) where
--   a <+> b = a `S.union` b

fset_concat : Foldable t => t (FSet n) -> FSet n
fset_concat xs = foldr (\x, y => x `F.unionFSet` y) F.emptyFSet xs

dfs : FSet n -> FSet (S n) -> FSet (S n) -> ProdFace (S n) -> Opetope k1 -> Opetope k2 -> FSet (S (S n))
dfs ins used building_blocks target_out p q =
    let f = F.Face p q (F.toListFSet used) target_out in
    if F.is_valid f
        then F.singletonFSet f
        else fset_concat [(dfs new_ins
                               new_used
                               building_blocks
                               target_out
                               p q) | b <- F.toListFSet building_blocks,
                                      i <- F.toListFSet ins,
                                      not (F.containsFSet b used),
                                      let new_ins = (ins `F.unionFSet` (F.fromListFSet (F.dom b))),
                                      let new_used = (b `F.insertFSet` used),
                                      --matching_cond i b,
                                      order_cond b]
            where
                --matching_cond : Opetope k -> Opetope l -> Bool
                --matching_cond i b = ?hole -- (i == (F.cod b)) && (p1 i) `S.member` (U.subopetopes p) && (p2 i) `S.member` (U.subopetopes q)
                order_cod : Opetope k -> Bool
                order_cond b = True -- (and [or [ordP (F.em bi) (F.em ti) | bi <- (O.dom (p1 b))] | ti <- (O.dom (p1 t))]) && (and [or [ordQ (F.em bi) (F.em ti) | bi <- (O.dom (p2 b))] | ti <- (O.dom (p2 t))])
                    -- ((b.p1.level < target_out.p1.level)
                    -- (b.p2.level < target_out.p2.level)

possible_faces : F.ProdFace (S n) -> List (F.ProdFace (S n)) -> Opetope k1 -> Opetope k2 -> FSet (S (S n))
possible_faces op building_blocks p q =
    dfs (F.singletonFSet (F.cod op)) F.emptyFSet (F.fromListFSet building_blocks) op p q


product : O.Opetope k1 -> O.Opetope k2 -> (FU.FMap, FU.FMap)
product p q =
        let subsp = OU.subopetopes p
            subsq = OU.subopetopes q
            small_faces_points = [F.from_point_and_point p1 p2 | p1 <- subsp Z, p2 <- subsq Z]
            small_faces_arrows = [F.from_point_and_arrow p1 p2 | p1 <- subsp Z, p2 <- subsq (S Z)] ++
                                 [F.from_arrow_and_point p1 p2 | p1 <- subsp (S Z), p2 <- subsq Z] ++
                                 [F.from_arrow_and_arrow p1 p2 | p1 <- subsp (S Z), p2 <- subsq (S Z)] in
    ?hole
