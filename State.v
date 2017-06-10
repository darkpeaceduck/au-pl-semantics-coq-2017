(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Omega.
Require Export Arith Arith.EqNat.
Require Export Id.

Section S.

  Variable A : Set.

  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).

  Lemma state_deterministic: forall (st : state) (x : id) (n m : A),
    st / x => n -> st / x => m -> n = m.
  Proof. 
  intros. induction st.
  + inversion H.
  + inversion H. 
    - inversion H0. congruence. congruence. 
    - inversion H0. congruence. auto.
  Qed.

 
  Lemma update_eq : forall (st : state) (x : id) (n : A),
    st [x <- n] / x => n.
  Proof. 
  intros. induction st.
  + apply st_binds_hd.
  + apply st_binds_hd.
  Qed.

  Lemma update_neq : forall (st : state) (x2 x1 : id) (n m : A),
    x2 <> x1 -> st / x1 => m -> st [x2 <- n] / x1 => m.
  Proof. 
  intros. induction st.
  + apply st_binds_tl. auto. auto.
  + apply st_binds_tl. auto. auto.
  Qed.

  Lemma update_shadow : forall (st : state) (x1 x2 : id) (n1 n2 m : A),
    st[x2 <- n1][x2 <- n2] / x1 => m -> st[x2 <- n2] / x1 => m.
  Proof. 
  intros. inversion H. 
  + apply update_eq. 
  + apply update_neq. 
    - auto. 
    - inversion H6. symmetry in H7. contradiction. auto.
  Qed.


  Lemma update_same : forall (st : state) (x1 x2 : id) (n1 m : A),
    st / x1 => n1 -> st / x2 => m -> st [x1 <- n1] / x2 => m.
  Proof. 
  intros. destruct (eq_id_dec x1 x2). 
  + rewrite e in H. pose proof state_deterministic as X. 
destruct X with (st := st) (x := x2) (n := n1) (m:=m). auto. auto. rewrite e. apply update_eq.
  + apply update_neq. auto. auto.
  Qed.

  Lemma update_permute : forall (st : state) (x1 x2 x3 : id) (n1 n2 m : A),
    x2 <> x1 -> 
    st [x2 <- n1][x1 <- n2] / x3 => m ->
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. 
  intros. destruct (eq_id_dec x1 x3).
  + symmetry in e. rewrite e in H0. rewrite e. apply st_binds_tl. auto. 
remember (update_eq ((st) [x2 <- n1]) x1 n2).
remember (state_deterministic ((st) [x2 <- n1] [x1 <- n2])
x1 n2 m).
destruct e0. auto. auto. apply update_eq.
+  destruct (eq_id_dec x2 x3).
-  symmetry in e.
rewrite e in H0.
rewrite e.
pose proof st_binds_tl as X.
unfold update in H0. auto.
remember (X 
(((x2, n1) :: st))
(x2)
(n1)
(x1) 
(n2)) . apply s in H.
remember ( state_deterministic
((x1, n2) :: (x2, n1) :: st)
x2 n1 m).
destruct e0.
auto. auto. apply update_eq. apply update_eq.
fold update in H.

apply update_eq. auto.
pose proof update_same as X.
End S.