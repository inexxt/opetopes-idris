module Utils

%access public export
Show Ordering where
    show LT = "LT"
    show GT = "GT"
    show EQ = "EQ"

Ord Ordering where
    compare LT EQ = LT
    compare LT GT = LT
    compare EQ GT = LT

    compare EQ EQ = EQ
    compare LT LT = EQ
    compare GT GT = EQ

    compare EQ LT = GT
    compare GT LT = GT
    compare GT EQ = GT


dmap: Functor f => (func : a -> b) -> f a -> f (Lazy b)
dmap func it = map (Delay . func) it

and_ : List Bool -> Bool
and_ [] = True
and_ (x::xs) = x && (and_ xs)

cart_prod_with : (a -> b -> c) -> List a -> List b -> List c
cart_prod_with f as bs = [f a b | a <- as, b <- bs]

natFromTo : Nat -> Nat -> List Nat
natFromTo b e = if b <= e then natEnumFromTo b e else []
