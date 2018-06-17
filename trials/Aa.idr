module Aa

public export
f : Nat -> Nat
f x = x + 5

lemma : (f 1) = 6
lemma = Refl
