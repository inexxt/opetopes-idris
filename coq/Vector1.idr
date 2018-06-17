module Vector1

public export
data Vec: Nat -> Type where
    Nil : String -> Vec Z
    Cons : String -> {k: Nat} -> Nat -> Vec k -> Vec (S k)

public export
vec_len1 : {k: Nat} -> (v: Vec k) -> Nat
vec_len1 {k} _ = k

lemma_zero : (vec_len1 (Nil "a")) = Z
lemma_zero = Refl
