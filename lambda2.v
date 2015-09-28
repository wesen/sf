Require Import String.

Set Implicit Arguments.

Inductive star A (R : A -> A -> Prop) : A -> A -> Prop :=
| StarRefl : forall x, star R x x
| StarStep : forall x1 x2 x3,
               R x1 x2
               -> star R x2 x3
               -> star R x1 x3.

Theorem star_trans: forall A (R : A -> A -> Prop) x1 x2 x3,
                      star R x1 x2
                      -> star R x2 x3
                      -> star R x1 x3.
Proof.
  induction 1; intros.
  (* x -> * x3 *)
  assumption.

  econstructor. eassumption. apply IHstar. assumption.
Qed.

Inductive exp : Set :=
| Var : string -> exp
| Abs : string -> exp -> exp
| App : exp -> exp -> exp.

Fixpoint subst (rep : exp) (x : string) (e : exp) : exp :=
  match e with
    | Var y => if string_dec y x then rep else Var y
    | Abs y e' => if string_dec y x then Abs y e' else Abs y (subst rep x e')
    | App e1 e2 => App (subst rep x e1) (subst rep x e2)
  end.

Eval compute in subst (Var "foo") "x" (Abs "foo" (Var "x")).

Inductive bigStep : exp -> exp -> Prop :=
| BigAbs : forall x e, bigStep (Abs x e) (Abs x e)
| BigApp : forall e1 x e1' e2 v2 v,
             bigStep e1 (Abs x e1')
             -> bigStep e2 v2
             -> bigStep (subst v2 x e1') v
             -> bigStep (App e1 e2) v.
