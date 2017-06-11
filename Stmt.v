Require Import List.
Import ListNotations.
Require Import Omega.

Require Export BigZ.
Require Export Id.
Require Export State.
Require Export Expr.

(* The type of statements *)
Inductive stmt : Type :=
  | SKIP  : stmt
  | Assn  : id -> expr -> stmt
  | READ  : id -> stmt
  | WRITE : expr -> stmt
  | Seq   : stmt -> stmt -> stmt
  | If    : expr -> stmt -> stmt -> stmt
  | While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf :=  (state Z * list Z * list Z)%type.

Reserved Notation "c1 '==' s '==>' c2" (at level 0).

(* Big-step evaluation relation *)
Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
  | bs_Skip        : forall (c : conf), c == SKIP ==> c 
  | bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z), 
                       [| e |] s => z -> (s, i, o) == x ::= e ==> (s [x <- z], i, o)
  | bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
                       (s, z::i, o) == READ x ==> (s [x <- z], i, o)
  | bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z), 
                       [| e |] s => z -> (s, i, o) == WRITE e ==> (s, i, z::o)
  | bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt),
                       c == s1 ==> c' -> c' == s2 ==> c'' -> c ==  s1 ;; s2 ==> c''
  | bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
                       [| e |] s => Z.one -> (s, i, o) == s1 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
  | bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
                       [| e |] s => Z.zero -> (s, i, o) == s2 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
  | bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt),
                       [| e |] st => Z.one -> (st, i, o) == s ==> c' -> c' == WHILE e DO s END ==> c'' ->
                          (st, i, o) == WHILE e DO s END ==> c''
  | bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt),
                       [| e |] st => Z.zero -> (st, i, o) == WHILE e DO s END ==> (st, i, o) 
where "c1 == s ==> c2" := (bs_int s c1 c2).

(* Big-step semantics is deterministic *)
Lemma bs_int_deterministic : forall (c c1 c2 : conf) (s : stmt), c == s ==> c1 -> c == s ==> c2 -> c1 = c2.
Proof. 
intros c c1 c2 s . revert c. revert c1. revert c2.
induction s.
+ intros. inversion H. inversion H0. congruence.
+ intros. inversion H. inversion H0. symmetry in H2. rewrite H2 in H7. inversion H7. 
rewrite H12 in H10. destruct (bs_eval_deterministic e s z z0). auto. auto. auto.
+ intros. inversion H. inversion H0. symmetry in H1. rewrite H1 in H4. inversion H4. auto.
+ intros.  inversion H. inversion H0.  symmetry in H3. rewrite H3 in H7.  inversion H7. 
rewrite H10 in H6. destruct (bs_eval_deterministic e s z z0). auto. auto. auto.
+ intros. inversion H. inversion H0. destruct IHs1 with (c1 := c') (c2 := c'0) (c := c).
auto. auto. destruct IHs2 with (c1 := c1) (c2 := c2) (c := c'). auto. auto. auto.
+ intros. inversion H. inversion H0. symmetry in H3. rewrite H3 in H10. inversion H10. rewrite H16 in H13.
rewrite H10 in H14. destruct IHs1 with (c := (s, i, o)) (c1 := c1) (c2 := c2). auto. auto. auto.
symmetry in H3. rewrite H3 in H10. inversion H10. rewrite H16 in H13.
rewrite H10 in H14. exfalso. assert (Z.zero = Z.one -> False). 
intros. inversion H15. 
remember (bs_eval_deterministic e s (Z.zero) (Z.one)). apply H15. apply e2. auto. auto. 
inversion H0. symmetry in H3. rewrite H3 in H10. inversion H10. rewrite H16 in H13.
rewrite H10 in H14. exfalso. assert (Z.zero = Z.one -> False). 
intros. inversion H15. 
apply H15.
remember (bs_eval_deterministic e s (Z.zero) (Z.one)). apply e2. auto. auto. 
symmetry in H3. rewrite H3 in H10. inversion H10. rewrite H10 in H14.
rewrite H16 in H13.
destruct IHs2 with (c := (s, i, o)) (c1 := c1) (c2 := c2). auto. auto. auto.
+ intros. revert H0. revert c2. induction H.

{ intros. inversion H0. auto. } 
{ intros. inversion H0. destruct (bs_eval_deterministic e0 s0 z z0). auto. auto. auto. }
{ intros. inversion H0. auto. }
{ intros. inversion H0. destruct (bs_eval_deterministic e0 s0 z z0). auto. auto. auto. }
{ intros. inversion H1. apply IHbs_int1 in H4. symmetry in  H4. rewrite H4 in H7.
apply IHbs_int2 in H7. auto. }
{ intros. inversion H1. apply IHbs_int in H10. auto.
exfalso. assert (Z.zero = Z.one -> False). 
intros. inversion H11. apply H11. remember (bs_eval_deterministic e0 s0 (Z.zero) (Z.one)).
apply e2. auto. auto.
}
{ intros. inversion H1. exfalso. assert (Z.zero = Z.one -> False). 
intros. inversion H11. apply H11. remember (bs_eval_deterministic e0 s0 (Z.zero) (Z.one)).
apply e2. auto. auto.
apply IHbs_int in H10. auto.
}

intros. apply IHbs_int2.

inversion H2.
- apply IHbs_int1 in H10. symmetry in H10. rewrite H10 in H11. auto.
- exfalso. assert (Z.zero = Z.one -> False). 
intros. inversion H10.  apply H10. remember (bs_eval_deterministic e0 st (Z.zero) (Z.one)).
apply e2. auto. auto.

- intros. inversion H0. 
* exfalso. assert (Z.zero = Z.one -> False). 
intros. inversion H10. apply H10.  remember (bs_eval_deterministic e0 st (Z.zero) (Z.one)).
apply e2. auto. auto.
* auto.
Qed.


Reserved Notation "s1 '~~~' s2" (at level 0).

Inductive bs_equivalent: stmt -> stmt -> Prop :=
  bs_eq_intro: forall (s1 s2 : stmt), 
                 (forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c') -> s1 ~~~ s2
where "s1 '~~~' s2" := (bs_equivalent s1 s2).

Module SmokeTest.

  Lemma seq_assoc : forall (s1 s2 s3 : stmt) (c c' : conf),
                      ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof. admit. Admitted.

  Lemma while_unfolds : forall (e : expr) (s : stmt) (c c' : conf),
                          (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. admit. Admitted.    

  Lemma while_false : forall (e : expr) (s : stmt) (st : state Z) (i o : list Z) (c : conf),
                        c == WHILE e DO s END ==> (st, i, o) -> [| e |] st => Z.zero.
  Proof. admit. Admitted.

  Definition True := Nat 1.

  Lemma loop_eq_undefined : (WHILE True DO SKIP END) ~~~ (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. admit. Admitted.
  
End SmokeTest.

(* Contextual equivalence *)
Inductive Context : Type :=
| Hole 
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt := 
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s) 
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: stmt -> stmt -> Prop :=
  ceq_intro : forall (s1 s2 : stmt),
                (forall (C : Context), (C <~ s1) ~~~ (C <~ s2)) -> s1 ~c~ s2
where "s1 '~c~' s2" := (contextual_equivalent s1 s2).

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq: forall (s1 s2 : stmt), s1 ~~~ s2 <-> s1 ~c~ s2.
Proof. admit. Admitted.

(* CPS-style semantics *)
Inductive cont : Type := 
| KEmpty : cont
| KStmt  : stmt -> cont.
 
Definition Kapp (l r : cont) : cont :=
  match (l, r) with
  | (KStmt ls, KStmt rs) => KStmt (ls ;; rs)
  | (KEmpty  , _       ) => r
  | (_       , _       ) => l
  end.

Notation "'!' s" := (KStmt s) (at level 0).
Notation "s1 @ s2" := (Kapp s1 s2) (at level 0).

Reserved Notation "k '|-' c1 '--' s '-->' c2" (at level 0).

Inductive cps_int : cont -> cont -> conf -> conf -> Prop :=
| cps_Empty       : forall (c : conf), KEmpty |- c -- KEmpty --> c
| cps_Skip        : forall (c c' : conf) (k : cont), 
                      KEmpty |- c -- k --> c' -> 
                      k |- c -- !SKIP --> c'
| cps_Assn        : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (x : id) (e : expr) (n : Z),
                      [| e |] s => n ->
                      KEmpty |- (s [x <- n], i, o) -- k --> c' ->
                      k |- (s, i, o) -- !(x ::= e) --> c'
| cps_Read        : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (x : id) (z : Z),
                      KEmpty |- (s [x <- z], i, o) -- k --> c' ->
                      k |- (s, z::i, o) -- !(READ x) --> c'
| cps_Write       : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (z : Z),
                      [| e |] s => z ->
                      KEmpty |- (s, i, z::o) -- k --> c' ->
                      k |- (s, i, o) -- !(WRITE e) --> c'
| cps_Seq         : forall (c c' : conf) (k : cont) (s1 s2 : stmt), 
                      !s2 @ k |- c -- !s1 --> c' ->
                      k |- c -- !(s1 ;; s2) --> c'
| cps_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s1 s2 : stmt),
                      [| e |] s => Z.one ->
                      k |- (s, i, o) -- !s1 --> c' ->
                      k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s1 s2 : stmt),
                      [| e |] s => Z.zero ->
                      k |- (s, i, o) -- !s2 --> c' ->
                      k |- (s, i, o) -- !(COND e THEN s1 ELSE s2 END) --> c'
| cps_While_True  : forall (st : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s : stmt),
                      [| e |] st => Z.one ->
                      !(WHILE e DO s END) @ k |- (st, i, o) -- !s --> c' ->
                      k |- (st, i, o) -- !(WHILE e DO s END) --> c'
| cps_While_False : forall (st : state Z) (i o : list Z) (c' : conf) (k : cont) (e : expr) (s : stmt),
                      [| e |] st => Z.zero ->
                      KEmpty |- (st, i, o) -- k --> c' ->
                      k |- (st, i, o) -- !(WHILE e DO s END) --> c'
where "k |- c1 -- s --> c2" := (cps_int k s c1 c2).

Lemma bs_int_to_cps_int: forall (st : state Z) (i o : list Z) (c' : conf) (s : stmt),
  (st, i, o) == s ==> c' -> KEmpty |- (st, i, o) -- !s --> c'.
Proof. admit. Admitted.

Lemma cps_int_to_bs_int: forall (st : state Z) (i o : list Z) (c' : conf) (s : stmt),
  KEmpty |- (st, i, o) -- !s --> c' -> (st, i, o) == s ==> c'.
Proof. admit. Admitted.
