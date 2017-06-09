(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Omega.

Inductive id : Type :=
  Id : nat -> id.

Reserved Notation "m <<= n" (at level 70, no associativity).
Reserved Notation "m >>  n" (at level 70, no associativity).
Reserved Notation "m <<  n" (at level 70, no associativity).

Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) <<= (Id m)
where "n <<= m" := (le_id n m).   

Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) << (Id m)
where "n << m" := (lt_id n m).   

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) >> (Id m)
where "n >> m" := (gt_id n m).   

Notation "n <<= m" := (le_id n m).
Notation "n >>  m" := (gt_id n m).
Notation "n <<  m" := (lt_id n m).

Lemma lt_eq_lt_id_dec: forall (id1 id2 : id), {id1 << id2} + {id1 = id2} + {id2 << id1}.
Proof. intros [id1]. induction id1.
+ intros [id2]. destruct id2.
  - left. right. auto.
  - left. left. apply lt_conv. omega.
+ intros [id2']. destruct id2' as [|id2''].
- right.  apply lt_conv. omega.
- destruct IHid1 with (id2 := Id (id2'')) as [[L | E ] | R].
* left. left. apply lt_conv. inversion L. omega.
* left. right. inversion E.  auto.
* right. apply lt_conv. inversion R. omega.
Qed. 
  
Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 >> id2} + {id1 = id2} + {id2 >> id1}.
Proof. 
intros. pose proof lt_eq_lt_id_dec as X. destruct X with (id1 := id1) (id2 := id2) as [[L | E ] | R].
+ right. destruct id1. destruct id2. inversion L. apply gt_conv. omega.
+ left. right.  auto.
+ left. left. destruct id1. destruct id2. inversion R. apply gt_conv. omega.
Qed. 

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 <<= id2} + {id1 >> id2}.
Proof. 
intros. pose proof lt_eq_lt_id_dec as X. destruct X with (id1 := id1) (id2 := id2) as [[L | E ] | R].
+ left. destruct id1. destruct id2. apply le_conv. inversion L. omega.
+ left. destruct id1. destruct id2. apply le_conv. inversion E. omega.
+ right. destruct id1. destruct id2. inversion R. apply gt_conv. omega.
Qed.

Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof. 
intros. pose proof lt_eq_lt_id_dec as X. destruct X with (id1 := (Id n)) (id2 := (Id m)) as [[L | E ] | R].
+ right. inversion L. omega.
+ left. inversion E. omega.
+ right. inversion R. omega.
Qed.

Lemma eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof. 
intros. pose proof eq_dec as X. destruct id1. destruct id2. 
destruct X with (n := n) (m := n0) as [L | R].
+ left. auto. 
+ right. intros eq. inversion eq. auto.
Qed. 

Lemma eq_id : forall (T:Type) x (p q:T), (if eq_id_dec x x then p else q) = p. 
Proof. intros. destruct (eq_id_dec x x).
+ auto.
+ destruct x. destruct n. auto.
Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if eq_id_dec x y then p else q) = q. 
Proof. admit. Admitted.

Lemma lt_gt_id_false : forall id1 id2 : id, id1 >> id2 -> id2 >> id1 -> False.
Proof. admit. Admitted.

Lemma le_gt_id_false : forall id1 id2 : id, id2 <<= id1 -> id2 >> id1 -> False.
Proof. admit. Admitted.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, id1 <<= id2 -> {id1 = id2} + {id2 >> id1}.
Proof. admit. Admitted.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id, id1 <> id2 -> {id1 >> id2} + {id2 >> id1}.
Proof. admit. Admitted.
    
Lemma eq_gt_id_false : forall id1 id2 : id, id1 = id2 -> id1 >> id2 -> False.
Proof. admit. Admitted.

