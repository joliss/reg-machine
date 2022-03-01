(** Calculation for the lambda calculus + arithmetic using a call
    stack for saving registers before a call. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module Lambda (Import mem : Memory).


(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Var : nat -> Expr
| Abs : Expr -> Expr
| App : Expr -> Expr -> Expr.

(** * Semantics *)

(** The evaluator for this language is given as follows (as in the
paper):
<<
type Env = [Value]
data Value =  Num Int | Fun (Value -> Value)


eval ::  Expr -> Env -> Value
eval (Val n) e   = Num n
eval (Add x y) e = case eval x e of
                     Num n -> case eval y e of
                                Num m -> Num (n+m)
eval (Var i) e   = e !! i
eval (Abs x) e   = Fun (\v -> eval x (v:e))
eval (App x y) e = case eval x e of
                     Fun f -> f (eval y e)
>>
After defunctionalisation and translation into relational form we
obtain the semantics below. *)

Inductive Value : Set :=
| Num : nat -> Value
| Clo : Expr -> list Value -> Value.

Definition Env := list Value.

Reserved Notation "x ⇓[ e ] y" (at level 80, no associativity).

Inductive eval : Expr -> Env -> Value -> Prop :=
| eval_val e n : Val n ⇓[e] Num n
| eval_add e x y n n' : x ⇓[e] Num n -> y ⇓[e] Num n' -> Add x y ⇓[e] Num (n + n')
| eval_var e i v : nth e i = Some v -> Var i ⇓[e] v
| eval_abs e x : Abs x ⇓[e] Clo x e
| eval_app e e' x x' x'' y y' : x ⇓[e] Clo x' e' -> y ⇓[e] y' -> x' ⇓[y' :: e'] x'' -> App x y ⇓[e] x''
where "x ⇓[ e ] y" := (eval x e y).

(** * Compiler *)

Inductive Code : Set :=
| HALT : Code
| LOAD : nat -> Code -> Code
| LOOKUP : nat -> Code -> Code
| STORE : Reg -> Code -> Code
| ADD : Reg -> Code -> Code

| STC : Reg -> Code -> Code                         
| APP : Reg -> Code -> Code
| ABS : Code -> Code -> Code
| RET : Code

| RUN_BLOCK : Code -> Code -> Code
| RET_BLOCK : Code
.

Fixpoint comp (e : Expr) (c : Code) : Code :=
  match e with
    | Val n   => LOAD n c
    | Var i   => LOOKUP i c
    | Add x y => RUN_BLOCK
                  (comp x RET_BLOCK)
                  (STORE first
                         (RUN_BLOCK
                            (comp y RET_BLOCK)
                            (ADD first c)))
    | App x y => RUN_BLOCK
                  (comp x RET_BLOCK)
                  (STC first
                       (RUN_BLOCK
                          (comp y RET_BLOCK)
                          (APP first c)))
    | Abs x   => ABS (comp x RET) c
  end.

Definition compile (e : Expr) : Code := comp e HALT.

(** * Virtual Machine *)

Inductive Value' : Set :=
| NULL
| NUM : nat -> Value'
| CLO : Code -> list Value' -> Value'
| BLOCK_RETURN : Code -> Value'.

Definition Env' := list Value'.

Definition empty := (@empty Value').


Definition Frame : Type := (Value' * Mem Value') % type.

Definition Stack : Type := list Frame.

Inductive Conf : Type := 
| conf : Code -> Value' -> Env' -> Stack -> Mem Value' -> Conf.

Notation "⟨ c , a , e , s , m ⟩" := (conf c a e s m).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_load n c m a e s :
    ⟨LOAD n c, a, e, s, m⟩         ==> ⟨c, NUM n, e, s, m⟩
| vm_add c a n r m e s : m[r] = NUM n ->
    ⟨ADD r c, NUM a, e, s, m⟩     ==> ⟨c, NUM(n + a), e, s, m⟩
| vm_store c n r m e s :
    ⟨STORE r c, NUM n, e, s, m⟩   ==> ⟨c, NULL, e, s, m[r:=NUM n]⟩
| vm_stc c c' e' r m e s :
    ⟨STC r c, CLO c' e', e, s, m⟩ ==> ⟨c, NULL, e, s, m[r:=CLO c' e']⟩
| vm_lookup e i c v a m s : nth e i = Some v ->
    ⟨LOOKUP i c, a, e, s, m⟩       ==> ⟨c, v, e, s, m⟩
| vm_ret a c e e' m m' s :
    ⟨RET, a, e', (CLO c e, m') :: s, m⟩       ==> ⟨c, a, e, s, m'⟩
| vm_call c c' e e' v r m s : m[r]=CLO c' e' ->
    ⟨APP r c, v, e, s, m⟩          ==> ⟨c', v, v :: e', (CLO c e, m) :: s, empty⟩
| vm_fun a c c' m e s :
    ⟨ABS c' c, a, e, s, m⟩         ==> ⟨c, CLO c' e, e, s, m⟩

| vm_run_block a c c' m e s :
    ⟨RUN_BLOCK c' c, a, e, s, m⟩ ==> ⟨c', NULL, e, (BLOCK_RETURN c, m) :: s, empty⟩
| vm_ret_block a c m m' e s :
    ⟨RET_BLOCK, a, e, (BLOCK_RETURN c, m') :: s, m⟩ ==> ⟨c, a, e, s, m'⟩
where "x ==> y" := (VM x y).

(** Conversion functions from semantics to VM *)

Fixpoint conv (v : Value) : Value' :=
  match v with
    | Num n   => NUM n
    | Clo x e => CLO (comp x RET) (map conv e)
  end.

Definition convE : Env -> Env' := map conv.

Inductive stackle : Stack -> Stack -> Prop :=
| stackle_empty : stackle nil nil
| stackle_cons r m m' s s' : m ⊑ m' -> stackle s s' -> stackle ((r, m) :: s) ((r, m') :: s').

Hint Constructors stackle : memory.

Lemma stackle_refl s : stackle s s.
Proof.
  induction s.

  (* nil *)
  constructor.

  (* a :: s *)
  induction a.
  auto with memory.
Qed.

Lemma stackle_trans s1 s2 s3 : stackle s1 s2 -> stackle s2 s3 -> stackle s1 s3.
Proof.
  intros L1. generalize s3. induction L1; intros s3' L2. assumption. inversion L2. subst. constructor;
  eauto with memory.
Qed.

Hint Resolve stackle_refl stackle_trans : core.

Inductive cle : Conf -> Conf -> Prop :=
 | cle_mem  c a e s s' m m' : stackle s s' -> m ⊑ m' -> cle ⟨ c , a , e , s, m ⟩ ⟨ c , a , e , s', m' ⟩.

Hint Constructors cle : core.

Lemma rel_eq {T} {R : T -> T -> Prop} x y y' : R x y' -> y = y' -> R x y.
Proof. intros. subst. auto.
Qed .
Lemma rel_eq' {T} {R : T -> T -> Prop} x x' y : R x' y -> x = x' -> R x y.
Proof. intros. subst. auto.
Qed .


(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Machine.
Definition Conf := Conf.
Definition Pre := cle.
Definition Rel := VM.
Lemma monotone : monotonicity cle VM.
  prove_monotonicity1.
  all: try (match goal with [H : stackle (_ :: _) _ |- _] => inversion H end).
  all: prove_monotonicity2.
Qed.
Lemma preorder : is_preorder cle.
prove_preorder. Qed.
End VM.


Module VMCalc := Calculation mem VM.
Import VMCalc.



(** Specification of the compiler *)

Theorem spec p v e c a s :
  p ⇓[e] v ->
  exists m, ⟨comp p c, a, convE e, s, empty⟩ =>> ⟨c , conv v, convE e, s, m⟩.

(** Setup the induction proof *)

Proof.
  intros E.
  generalize dependent c.
  generalize dependent a.
  generalize dependent s.
  induction E; intros; eexists.

(** Calculation of the compiler *)

(** - [Val n ⇓[e] Num n]: *)

  begin
  ⟨c, NUM n , convE e, s, empty⟩.
  <== { apply vm_load }
  ⟨LOAD n c, a, convE e, s, empty⟩.
  [].

(** - [Add x y ⇓[e] Num (n + n')]: *)

  edestruct IHE1 as [m1 H1].
  edestruct IHE2 as [m2 H2].

  begin
    ⟨c, NUM (n + n'), convE e, s, empty[first:=NUM n]⟩ .
  <== { apply vm_add }
    ⟨ADD first c, NUM n', convE e, s, empty[first:=NUM n]⟩ .
  <== { apply vm_ret_block }
    ⟨RET_BLOCK, NUM n', convE e, (BLOCK_RETURN (ADD first c), empty[first:=NUM n]) :: s, m2⟩.
  <<= { apply H2 }
      ⟨comp y RET_BLOCK, NULL, convE e, (BLOCK_RETURN (ADD first c), empty[first:=NUM n]) :: s, empty⟩.
  <== { apply vm_run_block }
    ⟨(RUN_BLOCK
        (comp y RET_BLOCK)
        (ADD first c)),
      NULL, convE e, s, empty[first:=NUM n]⟩.
  <== { apply vm_store }
    ⟨STORE first
           (RUN_BLOCK
              (comp y RET_BLOCK)
              (ADD first c)),
      NUM n, convE e, s, empty⟩.
  <== { apply vm_ret_block }
    ⟨RET_BLOCK, NUM n, convE e,
      (BLOCK_RETURN (STORE first
                           (RUN_BLOCK
                              (comp y RET_BLOCK)
                              (ADD first c))),
        empty) :: s, m1⟩.
  <<= { apply H1 }
    ⟨comp x RET_BLOCK, NULL, convE e,
      (BLOCK_RETURN (STORE first
                           (RUN_BLOCK
                              (comp y RET_BLOCK)
                              (ADD first c))),
        empty) :: s, empty⟩.
  <== { apply vm_run_block }
    ⟨RUN_BLOCK
       (comp x RET_BLOCK)
       (STORE first
              (RUN_BLOCK
                 (comp y RET_BLOCK)
                 (ADD first c)))
      , a, convE e, s, empty⟩.
  [].

(** - [Var i ⇓[e] v] *)

  begin
    ⟨c, conv v, convE e , s, empty⟩.
  <== {apply vm_lookup; unfold convE; rewrite nth_map; rewr_assumption}
      ⟨LOOKUP i c, a , convE e, s, empty ⟩.
   [].

(** - [Abs x ⇓[e] Clo x e] *)

  begin
    ⟨c, CLO (comp x RET) (convE e), convE e, s, empty ⟩.
  <== { apply vm_fun }
    ⟨ABS (comp x RET) c, a, convE e, s, empty ⟩.
  [].

(** - [App x y ⇓[e] x''] *)

  edestruct IHE1 as [m1 H1].
  edestruct IHE2 as [m2 H2].
  edestruct IHE3 as [m3 H3].

  begin
    ⟨c, conv x'', convE e, s, empty[first:=CLO (comp x' RET) (convE e')] ⟩.
  <== { apply vm_ret }
    ⟨RET, conv x'', convE (y' :: e'), (CLO c (convE e), empty[first:=CLO (comp x' RET) (convE e')]) :: s, m3⟩.
  <<= {apply H3}
      ⟨comp x' RET, conv y', convE (y' :: e'), (CLO c (convE e), empty[first:=CLO (comp x' RET) (convE e')]) :: s, empty⟩.
  = {auto}
      ⟨comp x' RET, conv y', conv y' :: convE e', (CLO c (convE e), empty[first:=CLO (comp x' RET) (convE e')]) :: s, empty⟩.
  <== {apply vm_call}
    ⟨(APP first c), conv y', convE e, s, empty[first:=CLO (comp x' RET) (convE e')]⟩.
  <== { apply vm_ret_block }
    ⟨RET_BLOCK, conv y', convE e,
      (BLOCK_RETURN (APP first c), empty[first:=CLO (comp x' RET) (convE e')]) :: s, m2⟩.
  <<= { apply H2 }
      ⟨comp y RET_BLOCK, NULL, convE e,
        (BLOCK_RETURN (APP first c), empty[first:=CLO (comp x' RET) (convE e')]) :: s, empty⟩.
  <== { apply vm_run_block }
    ⟨RUN_BLOCK
       (comp y RET_BLOCK)
       (APP first c),
      NULL, convE e, s, empty[first:=CLO (comp x' RET) (convE e')]⟩.
  <== { apply vm_stc }
    ⟨STC first
         (RUN_BLOCK
            (comp y RET_BLOCK)
            (APP first c)),
      CLO (comp x' RET) (convE e'), convE e, s, empty⟩.
  = { auto }
      ⟨STC first
           (RUN_BLOCK
              (comp y RET_BLOCK)
              (APP first c)),
        conv (Clo x' e'), convE e, s, empty⟩.
  <== { apply vm_ret_block }
    ⟨RET_BLOCK, conv (Clo x' e'), convE e,
      (BLOCK_RETURN (STC first
                         (RUN_BLOCK
                            (comp y RET_BLOCK)
                            (APP first c))), empty) :: s, m1⟩.
  <<= { apply H1 }
      ⟨comp x RET_BLOCK, NULL, convE e,
        (BLOCK_RETURN (STC first
                           (RUN_BLOCK
                              (comp y RET_BLOCK)
                              (APP first c))), empty) :: s, empty⟩.
  <== { apply vm_run_block }
    ⟨RUN_BLOCK
       (comp x RET_BLOCK)
       (STC first
            (RUN_BLOCK
               (comp y RET_BLOCK)
               (APP first c))),
      a, convE e, s, empty ⟩.
  [].
Qed.


(** Specification of the whole compiler *)

Theorem spec' x a (e : Env) s v : x ⇓[e] v ->
                                exists m, ⟨compile x, a, convE e, s, empty⟩  =>> ⟨HALT , conv v , convE e, s, m⟩.
Proof.
  intros E.
  edestruct (spec x v e) as [m H]; auto.
  exists m.
  begin
    ⟨HALT , conv v , convE e, s, m⟩.
  <<= { apply H }
      ⟨comp x HALT, a, convE e, s, empty⟩.
  [].
Qed.


(** * Soundness *)

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; congruence.
Qed.
  

Definition terminates (p : Expr) : Prop := exists r, p ⇓[nil] r.

Theorem sound p a C : terminates p -> ⟨compile p, a, nil, nil, empty⟩ =>>! C -> 
                          exists v m, C = ⟨HALT , conv v, nil, nil, m⟩ /\ p ⇓[nil] v.
Proof.
  unfold terminates. intros T M. destruct T as [v T].
  pose (spec' p a nil nil v T) as H'.
  destruct H' as [x H].
  pose (determ_trc determ_vm) as D.
  unfold determ in D.
  exists v. eexists. split. eapply D. apply M. split.
  unfold comp.
  simpl in *. apply H. intro Contra. destruct Contra as [x0 H0].
  inversion H0. assumption.
Qed.

End Lambda.
