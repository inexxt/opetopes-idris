module Contraction

-- import Opetope
-- import OpetopesUtils

-- public export
-- data Contraction : n -> Type where
--     CPoint : Opetope Z -> String -> Contraction Z
--     CArrow : Opetope k -> String -> Contraction Z -> Contraction Z -> Contraction (S Z)
--     CFace : Opetope k -> String -> List (Contraction (S n)) -> Contraction (S n) -> Contraction (S (S n))

-- export
-- total
-- dim_p1 : Contraction n -> Nat
-- dim_p1 (CPoint p _) = dim p
-- dim_p1 (CArrow p _ _ _) = dim p
-- dim_p1 (CFace p _ _ _) = dim p 


-- export
-- p1 : (c: Contraction n) -> Opetope (dim_p1 c)
-- p1 c = case c of
--         (CPoint p p') => case decEq (dim p) (dim_p1 (CPoint p p')) of 
--                             Yes prf => replace prf p
--                             No _ => ?hole
--         (CArrow p s d c) => case decEq (dim p) (dim_p1 (CArrow p s d c)) of 
--                             Yes prf => replace prf p
--                             No _ => ?hole
--         (CFace p s d c) => case decEq (dim p) (dim_p1 (CFace p s d c)) of 
--                             Yes prf => replace prf p
--                             No _ => ?hole

-- export
-- p2 : Contraction n -> Opetope n
-- p2 (CPoint _ s) = Point s
-- p2 (CArrow _ s d c) = Arrow s (p2 d) (p2 c)
-- p2 (CFace _ s d c) = Face s (map p2 d) (p2 c)

-- export
-- domC : (Contraction (S n)) -> List (Contraction n)
-- domC (CArrow _ _ d _) = [d]
-- domC (CFace _ _ d _) = d

-- export
-- codC : (Contraction (S n)) -> (Contraction n)
-- codC (CArrow _ _ _ c) = c
-- codC (CFace _ _ _ c) = c

-- all_eq : Opetope n -> List (Contraction m) -> Bool
-- all_eq p [] = True
-- all_eq p (x::Nil) = eq p (p1 x)
-- all_eq p (x::xs) = eq p (p1 x) && (all_eq p xs)

-- mutual
--     is_valid_contraction : Contraction w -> Bool 
--     is_valid_contraction contr = case contr of
--             (CPoint _ _) => eq (p1 contr) (p2 contr)
--             (CArrow _ _ _ _) => eq (p1 contr) (p2 contr) -- niebezpieczne, sprawdzić
--             (CFace _ _ _ _) => contract contr

--     contract : {k: Nat} -> Contraction (S (S k)) -> Bool
--     contract {k} contr = case compare (dim (p1 contr)) (S (S k)) of
--         EQ => eq (p1 contr) (p2 contr)
--         LT => False
--         GT => if (eq (p1 contr) (p1 (codC contr))) && (all_eq (p1 contr) ((codC contr)::(domC contr)))
--             then is_valid_contraction (codC contr)
--             else False

