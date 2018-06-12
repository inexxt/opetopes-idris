module Product

import Opetope as O
import OpetopesUtils as OU
import Face as F
import FacesUtils as FU

import Data.AVL.Set as S


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
                                      let new_used = (b `F.insertFSet` used)]

possible_faces : F.ProdFace (S n) -> List (F.ProdFace (S n)) -> Opetope k1 -> Opetope k2 -> FSet (S (S n))
possible_faces op building_blocks p q =
    dfs (F.singletonFSet (F.cod op)) F.emptyFSet (F.fromListFSet building_blocks) op p q


product : O.Opetope k1 -> O.Opetope k2 -> (FU.FMap, FU.FMap)
product p q =
        let subsp = OU.subopetopes p
            subsq = OU.subopetopes q in
    ?hole
