Set Implicit arguments.

Inductive nat := 
 | Z : nat
 | S : nat -> nat.

Inductive vec: nat -> Set :=
 | nil : vec Z
 | cons : forall {k: nat}, nat -> vec k -> vec (S k).

Print vec.
Definition vec_len1 {k: nat} (v: vec k): nat := k.
Fixpoint vec_len2 {k: nat} (v: vec k): nat := 
  match v with
  | nil => Z
  | cons _ _ v' => S (vec_len2 v')
 end.

Lemma len1_eq_k: forall {k: nat} (v: vec k), vec_len1 v = k.
Proof.
intros.
auto.
Defined.

Lemma len2_eq_k: forall {k: nat} (v: vec k), vec_len2 v = k.
Proof.
intros.
induction v.
trivial.
simpl.
rewrite IHv.
trivial.
Defined.

Lemma len1_eq_len2: forall {k: nat} (v: vec k), vec_len1 v = vec_len2 v.
Proof.
intros.
rewrite len1_eq_k.
rewrite len2_eq_k.
trivial.
Defined.

Print len1_eq_len2.
