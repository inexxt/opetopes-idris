module Dd

import Debug.Trace as D

%access public export

dtrace : (Show a) => a -> a
-- dtrace x = D.trace (show x) x
dtrace x = x

dtrace' : a -> a
dtrace' x = D.trace "aaaa" x

dt : (Show a) => String -> a -> a
-- dt s x = D.trace (s ++ " " ++ (show x)) x
dt _ x = x
