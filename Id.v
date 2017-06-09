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
+ intros [id2']. destruct IHid1 with (id2 := (Id id2')) as [[ L | E] | R]. 
     - left. destruct id2'. 
 * left. inversion L. apply lt_conv. inversion H1.
 * destruct IHid1 with (id2 := (Id (id2'))). left. apply lt_conv. inversion L. 
     - left. left. apply lt_conv. inversion E. omega.
     -  destruct n0 as [|n0']. 
    * left. left. apply lt_conv. omega.
    * destruct n0 as [|n0']. left. right. inversion R. inversion H1. auto. inversion H3. apply lt_conv R.


induction n0.
    * left. left. inversion l. omega.
    * induction n0. left. right. inversion l. destruct n. auto. omega. right.
apply lt_conv. inversion l. 

  - left. left. apply lt_conv. omega.
+ intros . destruct id2. destruct id1'. 
  - destruct n. right. apply lt_conv. omega. destruct IH with (id2 := Id (S (S n))).
inversion s. left. left. apply lt_conv. inversion H. omega.
   - right. apply lt_conv. omega.
  - destruct IH with (id2 := (S n)) .
-  destruct IH'. left. left. apply lt_conv. c s. inversion H. omega. inversion H. omega. 
symmetry. 
  
Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 >> id2} + {id1 = id2} + {id2 >> id1}.
Proof. admit. Admitted.

Lemma le_gt_id_dec : forall id1 id2 : id, {id1 <<= id2} + {id1 >> id2}.
Proof. admit. Admitted.

Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof. admit. Admitted.

Lemma eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof. admit. Admitted. 

Lemma eq_id : forall (T:Type) x (p q:T), (if eq_id_dec x x then p else q) = p. 
Proof. admit. Admitted.

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

