(* Abstract specification of memory *)

Create HintDb memory.

Module Type Memory.

(* Types *)
Parameter Reg : Set.
Parameter Mem : Type -> Type.

(* Operations *)
Parameter empty : forall {T}, Mem T.
Parameter set : forall {T}, Reg -> T -> Mem T -> Mem T.
Parameter get : forall {T}, Reg -> Mem T -> option T.
Parameter first : Reg.
Parameter next : Reg -> Reg.

(* Predicates *)
Parameter freeFrom : forall {T}, Reg -> Mem T -> Prop.
Parameter memle : forall {T}, Mem T -> Mem T -> Prop.

(* Notations *)
Declare Scope memory_scope.
Open Scope memory_scope.
Notation "m [ r ] = v" := (get r m = Some v) (at level 70).
Notation "m [ r := v ]" := (set r v m) (at level 70).


(* Property 2 *)

Axiom get_set : forall T (r : Reg) (v : T) (m :  Mem T),
    get r (set r v m) = Some v.


End Memory.


Lemma rel_eq {T} {R : T -> T -> Prop} x y y' : R x y' -> y = y' -> R x y.
Proof. intros. subst. auto.
Qed.


(* Additional axioms not used in the paper. *)
Module Type MAxioms (Import mem: Memory).
  Axiom set_set : forall T (r : Reg) (v v' : T) (m :  Mem T),
    set r v (set r v' m) = set r v m.
  
  Ltac apply_eq t := eapply rel_eq; [apply t | repeat rewrite set_set; auto].
End MAxioms.

Module Type SetMem := Memory <+ MAxioms.
