(** * Simply Typed Lambda Calculus (STLC) *)

(* TODO: edit imports *)
Require Import Basics.

Module STLC.

Definition admit {T: Type} : T.
Admitted.

Definition Var := nat.

(** ** Syntax *)

(** Syntax for types. *)
Inductive TType : Type := 
  | Unit : TType 
  | Fun  : TType -> TType -> TType.

(** Syntax for terms. *)
Inductive Term : Type :=
  | unit : Term
  | ref  : Var -> Term
  | abs  : Var -> TType -> Term -> Term
  | app  : Term -> Term -> Term.

(** ** Operational Semantics *)

(** *** Dynamic Semantics *)

(** Predicate for terms that are values. A value of type [Val t] is a proof that
    term [t] is a value. *)
Inductive Val : Term -> Prop :=
  | Val_Unit : Val unit
  | Val_Abs  : forall (v : Var) (T : TType) (t : Term),
               Val (abs v T t).

(** Predicate for substitution. A value of type [Sub v t t1 t2] is a proof that
    term [t2] is the result of substituting term [t] for references to the free
    variable [v] in term [t1]. *)
Inductive Sub (v : Var) (t : Term) : Term -> Term -> Prop :=
  | Sub_Unit : Sub v t unit unit
  | Sub_Ref1 : Sub v t (ref v) t
  | Sub_Ref2 : forall v1 : Var,
               v <> v1 ->
               Sub v t (ref v1) (ref v1)
  | Sub_Abs1 : forall (v1 : Var) (T : TType) (t1 : Term),
               v = v1 ->
               Sub v t (abs v1 T t1) (abs v1 T t1)
  | Sub_Abs2 : forall (v1 : Var) (T : TType) (t1 t2 : Term),
               v <> v1 ->
               Sub v t t1 t2 ->
               Sub v t (abs v1 T t1) (abs v1 T t2)
  | Sub_App  : forall t1 t2 t1' t2' : Term,
               Sub v t t1 t1' ->
               Sub v t t2 t2' ->
               Sub v t (app t1 t2) (app t1' t2').

(** Decidable equality for variables used by substitution function. *)
Theorem eq_var_dec : forall v1 v2 : Var,
                     {v1 = v2} + {v1 <> v2}.
Proof.
  intro v1.
  induction v1 as [|v1'].
  (* case v1 = 0 *)
    intro v2.
    destruct v2 as [|v2'].
    (* subcase v2 = 0 *)
      left.
      reflexivity.
    (* subcase v2 = S v2' *)
      right.
      intros contra.
      inversion contra.
  (* case v1 = S v1' *)
    intro v2.
    destruct v2 as [|v2'].
    (* subcase v2 = 0 *)
      right.
      intros contra.
      inversion contra.
    (* subcase v2 = S v2' *)
      destruct IHv1' with (v2 := v2') as [eq | neq].
      (* subsubcase S v1' = S v2' *)
        left.
        apply f_equal.
        apply eq.
      (* subsubcase S v1' <> S v2' *)
        right.
        intros Heq.
        inversion Heq as [Heq'].
          apply neq.
          apply Heq'.
Defined.

(** Function for substitution. The term [sub v t1 t2] is the result of
    substituting term [t2] for references to the free variable [v] in term
    [t1]. *)
Fixpoint sub (v : Var) (t1 t2 : Term) : Term :=
  match t1 with
  | unit        => unit
  | ref v1      => if eq_var_dec v v1 then t2 else t1
  | abs v1 T t3 => abs v1 T (if eq_var_dec v v1 then t3 else sub v t3 t2)
  | app t3 t4   => app (sub v t3 t2) (sub v t4 t2)
  end.

(** The substitution predicate and function agree. *)
Theorem sub_agree : forall (v : Var) (t t1 t2 : Term),
                    Sub v t t1 t2 <-> sub v t1 t = t2.
Proof.
  (* TODO: fill in proof *)
Admitted.

(** Operational semantics for evaluation. A value of type [Eval t1 t2] is a
    proof that term [t1] transitions to [t2] in a single step. *)
Inductive Eval : Term -> Term -> Prop :=
  | Eval_AppAbs : forall (v : Var) (T : TType) (t1 t2 : Term),
                  Eval (app (abs v T t1) t2) (sub v t1 t2)
  | Eval_App1   : forall (t1 t1' t2 : Term),
                  Eval t1 t1' ->
                  Eval (app t1 t2) (app t1' t2)
  | Eval_App2   : forall (t1 t2 t2' : Term),
                  Eval t2 t2' ->
                  Eval (app t1 t2) (app t1 t2').

(** *** Static Semantics *)

(** Typing environment (or typing context). *)
Definition Env := Var -> option TType.

(** The empty typing environment. *)
Definition empty : Env :=
  fun _ => None.

(** Add a bind of a variable name to a type in an environment. *)
Definition add (m : Env) (v : Var) (T : TType) : Env :=
  fun v' => if eq_var_dec v v' then Some T else m v'.

(** Typing relation. A value of type [HasType m t T] is a proof that the term [t]
    has type [T] in the environment [m]. *)
Inductive HasType : Env -> Term -> TType -> Prop :=
  | HasType_Unit : forall (m : Env),
                   HasType m unit Unit
  | HasType_Ref  : forall (m : Env) (v : Var) (T : TType),
                   m v = Some T ->
                   HasType m (ref v) T
  | HasType_Abs  : forall (m : Env) (v : Var) (t : Term) (T1 T2 : TType),
                   HasType (add m v T1) t T2 ->
                   HasType m (abs v T1 t) (Fun T1 T2)
  | HasType_App  : forall (m : Env) (t1 t2 : Term) (T1 T2 : TType),
                   HasType m t1 (Fun T1 T2) ->
                   HasType m t2 T1 ->
                   HasType m (app t1 t2) T2.

End STLC.
