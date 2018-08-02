Require Export BigZ.
Require Export Id.
Require Export State.

(* Type of binary operators *)
Inductive bop : Type :=
| Add : bop
| Sub : bop
| Mul : bop
| Div : bop
| Mod : bop
| Le  : bop
| Lt  : bop
| Ge  : bop
| Gt  : bop
| Eq  : bop
| Ne  : bop
| And : bop
| Or  : bop.

(* Type of arithmetic expressions *)
Inductive expr : Type :=
| Nat : nat -> expr
| Var : id  -> expr              
| Bop : bop -> expr -> expr -> expr.

(* Supplementary notation *)
Notation "x '[+]'  y" := (Bop Add x y) (at level 40, left associativity).
Notation "x '[-]'  y" := (Bop Sub x y) (at level 40, left associativity).
Notation "x '[*]'  y" := (Bop Mul x y) (at level 41, left associativity).
Notation "x '[/]'  y" := (Bop Div x y) (at level 41, left associativity).
Notation "x '[%]'  y" := (Bop Mod x y) (at level 41, left associativity).
Notation "x '[<=]' y" := (Bop Le  x y) (at level 39, no associativity).
Notation "x '[<]'  y" := (Bop Lt  x y) (at level 39, no associativity).
Notation "x '[>=]' y" := (Bop Ge  x y) (at level 39, no associativity).
Notation "x '[>]'  y" := (Bop Gt  x y) (at level 39, no associativity).
Notation "x '[==]' y" := (Bop Eq  x y) (at level 39, no associativity).
Notation "x '[/=]' y" := (Bop Ne  x y) (at level 39, no associativity).
Notation "x '[&]'  y" := (Bop And x y) (at level 38, left associativity).
Notation "x '[\/]' y" := (Bop Or  x y) (at level 38, left associativity).

Definition zbool (x : Z) : Prop := x = Z.one \/ x = Z.zero.
  
Definition zor (x y : Z) : Z :=
  if Z_le_gt_dec (Z.of_nat 1) (x + y) then Z.one else Z.zero.
   
Reserved Notation "[| e |] st => z" (at level 0).
Notation "st / x => y" := (st_binds Z st x y) (at level 0).

(* Big-step evaluation relation *)
Inductive bs_eval : expr -> state Z -> Z -> Prop := 
  bs_Nat  : forall (s : state Z) (n : nat), [| Nat n |] s => (Z.of_nat n)
| bs_Var  : forall (s : state Z) (i : id) (z : Z), s / i => z -> [| Var i |] s => z

| bs_Add  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [+] b |] s => (za + zb)
| bs_Sub  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [-] b |] s => (za - zb)
| bs_Mul  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [*] b |] s => (za * zb)
| bs_Div  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [/] b |] s => (Z.div za zb)
| bs_Mod  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [%] b |] s => (Z.modulo za zb)

| bs_Le_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [<=] b |] s => Z.one
| bs_Le_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [<=] b |] s => Z.zero

| bs_Lt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [<] b |] s => Z.one
| bs_Lt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [<] b |] s => Z.zero

| bs_Ge_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [>=] b |] s => Z.one
| bs_Ge_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [>=] b |] s => Z.zero

| bs_Gt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [>] b |] s => Z.one
| bs_Gt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [>] b |] s => Z.zero

| bs_Eq_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [==] b |] s => Z.one
| bs_Eq_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [==] b |] s => Z.zero

| bs_Ne_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [/=] b |] s => Z.one
| bs_Ne_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [/=] b |] s => Z.zero

| bs_And  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [&] b |] s => (za * zb)

| bs_Or   : forall (s : state Z) (a b : expr) (za zb : Z), 
              [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [\/] b |] s => (zor za zb)
where "[| e |] st => z" := (bs_eval e st z). 

Hint Constructors bs_eval.

Module SmokeTest.

  Lemma nat_always : 
    forall (n : nat) (s : state Z), [| Nat n |] s => (Z.of_nat n).
  Proof. 
  intros. apply bs_Nat.
  Qed.

  Lemma double_and_sum : 
    forall (s : state Z) (e : expr) (z : Z), 
      [| e [*] (Nat 2) |] s => z -> [| e [+] e |] s => z.
  Proof. 
  intros. pose proof bs_Mul as X. inversion H. inversion H5. replace (Z.mul za (Z.of_nat 2)) with (Z.add za za).
  apply bs_Add. auto. auto. simpl. omega.
  Qed.

End SmokeTest.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Add : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [+]  b)
| v_Sub : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [-]  b)
| v_Mul : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [*]  b)
| v_Div : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/]  b)
| v_Mod : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [%]  b)
| v_Le  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<=] b)
| v_Lt  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<]  b)
| v_Ge  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>=] b)
| v_Gt  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>]  b)
| v_Eq  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [==] b)
| v_Ne  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/=] b)
| v_And : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [&]  b)
| v_Or  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [\/] b)
where "x ? e" := (V e x).

(* If an expression is defined in some state, then each its' variable is
   defined in that state
*)
Lemma defined_expression: forall (e : expr) (s : state Z) (z : Z) (id : id),
  [| e |] s => z -> id ? e -> exists z', s / id => z'.
Proof. 
intros. 
induction H.
+ inversion H0.
+ inversion H0. symmetry in H1. rewrite H1. exists z. auto.
+ inversion H0. destruct H5. 
  - apply IHbs_eval1 in H5. auto.
  - apply IHbs_eval2 in H5. auto.
+ inversion H0. destruct H5. 
  - apply IHbs_eval1 in H5. auto.
  - apply IHbs_eval2 in H5. auto.
+ inversion H0. destruct H5. 
  - apply IHbs_eval1 in H5. auto.
  - apply IHbs_eval2 in H5. auto.
+ inversion H0. destruct H5. 
  - apply IHbs_eval1 in H5. auto.
  - apply IHbs_eval2 in H5. auto.
+ inversion H0. destruct H5. 
  - apply IHbs_eval1 in H5. auto.
  - apply IHbs_eval2 in H5. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H6. 
  - apply IHbs_eval1 in H6. auto.
  - apply IHbs_eval2 in H6. auto.
+ inversion H0. destruct H7. 
  - apply IHbs_eval1 in H7. auto.
  - apply IHbs_eval2 in H7. auto.
+ inversion H0. destruct H7. 
  - apply IHbs_eval1 in H7. auto.
  - apply IHbs_eval2 in H7. auto.
Qed.
(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable: forall (e : expr) (s : state Z) (id : id),
  id ? e -> (forall (z : Z), ~ (s / id => z)) -> (forall (z : Z), ~ ([| e |] s => z)).
Proof. 
unfold not.
intros.
induction H.
+ inversion H1. apply H0 in H2. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H8. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H8. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H8. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H8. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H8. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H8. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H8. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H8. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H8. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H8. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
  - destruct H.
    *  remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
    * remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
  - destruct H.
    *  remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
    * remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
  - destruct H.
    *  remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
    * remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
  - destruct H.
    *  remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
    * remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
  - destruct H.
    *  remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
    * remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
  - destruct H.
    *  remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H9. auto.
    * remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H9. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H10. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H10. auto.
+ inversion H1. destruct H.
  - remember (defined_expression a s za id). destruct e. auto. auto. apply H0 in H10. auto.
  - remember (defined_expression b s zb id). destruct e. auto. auto. apply H0 in H10. auto.
Qed.


Lemma bs_eval_deterministic: forall (e : expr) (s : state Z) (z1 z2 : Z),
  [| e |] s => z1 -> [| e |] s => z2 -> z1 = z2.
Proof. 
induction e. 
+ intros. inversion H. inversion H0. omega.
+ intros. inversion H. inversion H0. apply state_deterministic with (st := s) (x := i) (n := z1) (m := z2). auto. auto.
+ intros. destruct b. 
- inversion H. inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega.
- inversion H. inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega.
- inversion H. inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega.
- inversion H. inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega.
- inversion H. inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega.
- inversion H. inversion H0. auto. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega.
inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega. auto.
- inversion H. inversion H0. auto. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega.
inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega. auto.
-inversion H. inversion H0. auto. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega.
inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega. auto.
-inversion H. inversion H0. auto. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega.
inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega. auto.
-inversion H. inversion H0. auto. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. contradiction. 
inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. contradiction. auto.  
-inversion H. inversion H0. auto. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. contradiction. 
inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. contradiction. auto. 
-inversion H. inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega.
-inversion H. inversion H0. remember (IHe1 s za za0). destruct e. auto. auto.
remember (IHe2 s zb zb0). destruct e0. auto. auto. omega.
Qed.




(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z :Z, s1 /id => z <-> s2 / id => z.

(* The result of expression evaluation in a state dependes only on the values
   of occurring variables
*)
Lemma variable_relevance: forall (e : expr) (s1 s2 : state Z) (z : Z),
  (forall (id : id), id ? e -> equivalent_states s1 s2 id) -> 
  [| e |] s1 => z -> [| e |] s2 => z.
Proof. 
intros e.
induction e.
+ intros. inversion H0. auto.
+ intros. inversion H0. remember (H i). destruct e with (z := z). apply v_Var.
apply bs_Var. auto.
+ destruct b.
- intros. inversion H0. apply bs_Add. 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Add. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Add. auto. auto.
- intros. inversion H0. apply bs_Sub. 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Sub. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Sub. auto. auto.
- intros. inversion H0. apply bs_Mul. 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Mul. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Mul. auto. auto.
- intros. inversion H0. apply bs_Div. 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Div. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Div. auto. auto.
- intros. inversion H0. apply bs_Mod. 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Mod. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Mod. auto. auto.
- intros. inversion H0. apply bs_Le_T with (za := za) (zb := zb). 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Le. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Le. auto. auto.
 * auto. 
 * apply bs_Le_F with (za := za) (zb := zb).
   apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Le. auto. auto.
   apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Le. auto. auto.
   auto. 
- intros. inversion H0. apply bs_Lt_T with (za := za) (zb := zb). 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Lt. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Lt. auto. auto.
 * auto. 
 * apply bs_Lt_F with (za := za) (zb := zb).
   apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Lt. auto. auto.
   apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Lt. auto. auto.
   auto. 
- intros. inversion H0. apply bs_Ge_T with (za := za) (zb := zb). 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Ge. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Ge. auto. auto.
 * auto. 
 * apply bs_Ge_F with (za := za) (zb := zb).
   apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Ge. auto. auto.
   apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Ge. auto. auto.
   auto. 
- intros. inversion H0. apply bs_Gt_T with (za := za) (zb := zb). 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Gt. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Gt. auto. auto.
 * auto. 
 * apply bs_Gt_F with (za := za) (zb := zb).
   apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Gt. auto. auto.
   apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Gt. auto. auto.
   auto. 
- intros. inversion H0. apply bs_Eq_T with (za := za) (zb := zb). 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Eq. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Eq. auto. auto.
 * auto. 
 * apply bs_Eq_F with (za := za) (zb := zb).
   apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Eq. auto. auto.
   apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Eq. auto. auto.
   auto. 
- intros. inversion H0. apply bs_Ne_T with (za := za) (zb := zb). 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Ne. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Ne. auto. auto.
 * auto. 
 * apply bs_Ne_F with (za := za) (zb := zb).
   apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Ne. auto. auto.
   apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Ne. auto. auto.
   auto. 
- intros. inversion H0. apply bs_And with (za := za) (zb := zb). 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_And. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_And. auto. auto.
 * auto.
 * auto.
- intros. inversion H0. apply bs_Or with (za := za) (zb := zb). 
 * apply IHe1 with (s1 := s1). intros. 
   apply H. apply v_Or. auto. auto.
 * apply IHe2 with (s1 := s1). intros. 
   apply H. apply v_Or. auto. auto.
 * auto.
 * auto.
Qed.


(* Semantic equivalence *)
Reserved Notation "e1 '~~' e2" (at level 42, no associativity).

Inductive equivalent: expr -> expr -> Prop := 
  eq_intro : forall (e1 e2 : expr), 
               (forall (n : Z) (s : state Z), 
                 [| e1 |] s => n <-> [| e2 |] s => n
               ) -> e1 ~~ e2
where "e1 '~~' e2" := (equivalent e1 e2).

(* Semantic equivalence is an equivalence relation *)
Lemma eq_refl: forall (e : expr), e ~~ e.
Proof. 
intros.
apply eq_intro. intros. split.
+ apply variable_relevance. intros. split. auto. auto.
+ apply variable_relevance. intros. split. auto. auto.
Qed.

Lemma eq_symm: forall (e1 e2 : expr), e1 ~~ e2 -> e2 ~~ e1.
Proof. 
intros. apply eq_intro. intros. split.
+ inversion H. apply H0.
+ inversion H. apply H0.
Qed.

Lemma eq_trans: forall (e1 e2 e3 : expr), e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3.
Proof. 
intros. apply eq_intro. intros. split.
+ intros. inversion H. inversion H0.  apply H5. apply H2. auto.
+ intros. inversion H. inversion H0.  apply H2. apply H5. auto.
Qed.

(* Contexts *)
Inductive Context : Type :=
| Hole : Context
| BopL : bop -> Context -> expr -> Context
| BopR : bop -> expr -> Context -> Context.

(* Plugging an expression into a context *)
Fixpoint plug (C : Context) (e : expr) : expr := 
  match C with
  | Hole => e
  | BopL b C e1 => Bop b (plug C e) e1
  | BopR b e1 C => Bop b (plug C e) e1
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: expr -> expr -> Prop :=
  ceq_intro : forall (e1 e2 : expr),
                (forall (C : Context), (C <~ e1) ~~ (C <~ e2)) -> e1 ~c~ e2
where "e1 '~c~' e2" := (contextual_equivalent e1 e2).



Lemma eq_helper: forall (e1  e2: expr) (n : Z) (s : state Z) (C : Context), 
e1 ~~ e2 -> [|C <~ e2|] s => (n) -> [|C <~ e1|] s => (n).
Proof.
intros. revert H0. revert n. induction C. 
* intros. inversion H. apply H1. auto.
* intros. inversion H0.
apply bs_Add. apply IHC. auto. auto.
apply bs_Sub. apply IHC. auto. auto.
apply bs_Mul. apply IHC. auto. auto.
apply bs_Div. apply IHC. auto. auto.
apply bs_Mod. apply IHC. auto. auto.
apply bs_Le_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Le_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Lt_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Lt_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Ge_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Ge_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Gt_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Gt_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Eq_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Eq_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Ne_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Ne_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_And with (za := za) (zb := zb). apply IHC. auto. auto. auto. auto.
apply bs_Or with (za := za) (zb := zb). apply IHC. auto. auto. auto. auto.
* intros. inversion H0. 
apply bs_Add. apply IHC. auto. auto.
apply bs_Sub. apply IHC. auto. auto.
apply bs_Mul. apply IHC. auto. auto.
apply bs_Div. apply IHC. auto. auto.
apply bs_Mod. apply IHC. auto. auto.
apply bs_Le_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Le_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Lt_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Lt_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Ge_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Ge_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Gt_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Gt_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Eq_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Eq_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Ne_T with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_Ne_F with (za := za) (zb := zb). apply IHC. auto. auto. auto.
apply bs_And with (za := za) (zb := zb). apply IHC. auto. auto. auto. auto.
apply bs_Or with (za := za) (zb := zb). apply IHC. auto. auto. auto. auto.
Qed.

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq: forall (e1 e2 : expr), e1 ~~ e2 <-> e1 ~c~ e2.
Proof. 
intros. split.
+ intros. apply ceq_intro. intros.
apply eq_intro. intros. split.
- apply eq_helper. apply eq_symm. auto.
- apply eq_helper. auto.
+ intros. inversion H. apply H0 with (C := Hole).
Qed. 

















 


  