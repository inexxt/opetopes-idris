module Product

import Opetope as O
import OpetopesUtils as U
import Face as F
import Data.SortedBag as S

-- data OpetopeOrder n where
--     OpetopeOrder : {op: O.Opetope n, ord: S.Set (U.OpetopeE -> U.OpetopeE) } -> OpetopeOrder n-- TODO undefined



dfs : FSet n -> FSet (S n) -> FSet (S n) -> ProdFace (S n) -> Opetope k1 -> Opetope k2 -> FSet (S (S n))
dfs ins used building_blocks target_out p q =
    let f = F.Face p q (S.toList used) target_out in
    if F.is_valid f
        then S.singleton f
        else S.unions [(dfs new_ins new_used building_blocks target_out orderP orderQ) | b <- S.toList (building_blocks S.\\ used),
                                                                                         i <- S.toList ins,
                                                                                         let new_ins = ins `S.union` (S.fromList (F.dom b)),
                                                                                         let new_used = b `S.insert` used,
                                                                                         matching_cond i b,
                                                                                         order_cond b]
            where
                matching_cond : Opetope k -> Opetope l -> Bool
                matching_cond i b = ?hole -- (i == (F.cod b)) && (p1 i) `S.member` (U.subopetopes p) && (p2 i) `S.member` (U.subopetopes q)
                order_cod : Opetope k -> Bool
                order_cond b = True -- (and [or [ordP (F.em bi) (F.em ti) | bi <- (O.dom (p1 b))] | ti <- (O.dom (p1 t))]) && (and [or [ordQ (F.em bi) (F.em ti) | bi <- (O.dom (p2 b))] | ti <- (O.dom (p2 t))])
                    -- ((b.p1.level < target_out.p1.level)
                    -- (b.p2.level < target_out.p2.level)

possible_faces : F.ProdFace (S n) -> List (F.ProdFace (S n)) -> Opetope k1 -> Opetope k2 -> FSet (S (S n))
possible_faces op building_blocks p q =
    dfs (F.singletonFSet (F.cod op)) F.emptyFSet (S.fromList building_blocks) op p q

--
-- product :: OpetopeOrder pn -> OpetopeOrder qn -> (S.Set FaceE, S.Set FaceE)
-- product orderP orderQ =
--     let p = op orderP
--         q = op orderQ
--         subsp = U.subopetopes p
--         subsq = U.subopetopes q
--         points s = undefined in undefined
