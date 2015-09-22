
Require Import Arith.
Require Import String.

Inductive term : Set :=
| Var : string -> term
| Abs : string -> term -> term
| App : term -> term -> term.

Fixpoint fact (n : nat) : nat :=
  match n with
    | 0 => 1
    | S n => fact n * S n
  end.

Inductive fact_state : Set :=
| AnswerIs : nat -> fact_state
| WithAccumulator : nat -> nat -> fact_state.

(* Relations *)


(* relation fact_init between input and an accumulator state with that input and 1 as accumulator *)
Inductive fact_init (original_input : nat) : fact_state -> Prop :=
| FactInit : fact_init original_input (WithAccumulator original_input 1).

(* relation fact_final for all states AnswerIs *)
Inductive fact_final : fact_state -> Prop :=
| FactFinal : forall ans, fact_final (AnswerIs ans).

Inductive fact_step : fact_state -> fact_state -> Prop :=
| FactStep : forall n acc, fact_step (WithAccumulator (S n) acc) (WithAccumulator n (acc * S n))
| FactDone : forall acc, fact_step (WithAccumulator 0 acc) (AnswerIs acc).

Definition fact_invariant (original_input : nat) (st : fact_state) : Prop :=
  match st with
    | AnswerIs acc => acc = fact original_input
    | WithAccumulator n acc => fact original_input = fact n * acc
  end.

Theorem fact_invariant_init :
  forall original_input st,
    fact_init original_input st
    -> fact_invariant original_input st.
Proof.
  destruct 1. simpl. ring.
Qed.

Theorem fact_invariant_preserve : forall original_input st st',
                                    fact_step st st'
                                    -> fact_invariant original_input st
                                    -> fact_invariant original_input st'.
Proof.
  destruct 1 ; simpl ; intros.
  (* FactStep *)
  rewrite H. ring. 
  (* FactDone *)
  rewrite H. ring.
Qed.

Theorem fact_invariant_final : forall original_input st,
                                 fact_final st ->
                                 fact_invariant original_input st ->
                                 st = AnswerIs (fact original_input).
Proof.
  destruct 1. simpl. intros.
  (* rewrite H. reflexivity. *)
  congruence.
Qed.

(* Transition systems in general *)

Record transition_system' {State : Set} :=
  {
    Init  : State -> Prop;
    Step  : State -> State -> Prop;
    Final : State -> Prop
  }.

Record transition_system :=
  {
    State : Set;
    (*
    Init  : State -> Prop;
    Step  : State -> State -> Prop;
    Final : State -> Prop
*)
    Super :> @transition_system' State 
  }.

(*
Definition fact_ts (original_input : nat) :=
  {|
    State := fact_state;
    Super := {| Init := fact_init original_input;
                Step := fact_step;
                Final := fact_final |}
  |}.
*)

(* relation that captures which final states are reachable from a particular initial state *)
Inductive runFrom (ts : transition_system) : State ts -> State ts -> Prop :=
| RunFinal : forall st,
               Final ts st -> runFrom ts st st
| RunStep : forall st st' st'',
              Step ts st st'
              -> runFrom ts st' st''
              -> runFrom ts st st''.

Inductive run (ts : transition_system) (st : State ts) : Prop :=
| Run : forall st0,
          Init ts st0
          -> runFrom ts st0 st
          -> run ts st.

Lemma runFrom_final : forall ts st st',
                        runFrom ts st st'
                        -> Final ts st'.
Proof.
  induction 1.
  (* RunFinal *)
  assumption.
  (* RunStep *)
  assumption.
Qed.

Lemma run_final : forall ts st,
                    run ts st -> Final ts st.
Proof.
  destruct 1.
  (*
  apply runFrom_final with (st := st0).
  assumption.
   *)
  eapply runFrom_final.
  eassumption.
Qed.

(* 35:16 *)

Inductive isInvariant (ts : transition_system) (inv : State ts -> Prop) : Prop :=
| IsInvariant : (forall st, Init ts st -> inv st)
                -> (forall st st', Step ts st st' -> inv st -> inv st')
                -> isInvariant ts inv.

Theorem invariant_final' :
  forall (ts : transition_system) (inv : State ts -> Prop) st st',
    (forall st st', Step ts st st' -> inv st -> inv st')
    -> runFrom ts st st'
    -> inv st
    -> inv st'.
Proof.
  induction 2; intros.
  (* inv st -> inv st *) assumption.
  (* inv st -> inv st'' *)
  apply IHrunFrom. eapply H. eapply H0. assumption.
Qed.

Theorem invariant_final'' :
  forall (ts : transition_system) (inv : State ts -> Prop) st st',
    isInvariant ts inv
    -> runFrom ts st st'
    -> inv st
    -> inv st'.
Proof.
  induction 2; intros.
  (* inv st -> inv st *) assumption.
  (* inv st -> inv st'' *)
  apply IHrunFrom. eapply H. eapply H0. assumption.
Qed.

Theorem invariant_final :
  forall ts inv st,
    isInvariant ts inv
    -> run ts st
    -> inv st.
Proof.
  destruct 1, 1.
  eapply invariant_final''.
  apply IsInvariant. assumption. assumption. eapply H2. apply H. assumption.
Qed.
  
  
Theorem invariant_final1 :
  forall ts inv st,
    isInvariant ts inv
    -> run ts st
    -> inv st.
Proof.
  destruct 1, 1.
  eapply invariant_final'.
  assumption. eapply H2. 
  
(* parallel state machines for locking *)
Inductive increment_program : Set :=
| Lock : increment_program
| Read : increment_program
| Write : nat -> increment_program
| Unlock : increment_program
| Done : increment_program.

Record inc_state :=
  {
    Locked : bool;
    Global : nat
  }.

Definition increment_state := (inc_state * increment_program)%type.

Inductive increment_init : increment_state -> Prop :=
| IncInit : increment_init ({| Locked := false; Global := 0 |}, Lock).

Inductive increment_step : increment_state -> increment_state -> Prop :=
| IncLock : forall g,
              increment_step ({| Locked := false; Global := g |}, Lock)
                             ({| Locked := true; Global := g |}, Read)
| IncRead : forall l g,
              increment_step ({| Locked := l; Global := g |}, Read)
                             ({| Locked := l; Global := g |}, Write g)
| IncWrite : forall l g v,
              increment_step ({| Locked := l; Global := g |}, Write v)
                             ({| Locked := l; Global := S v |}, Unlock)
| IncUnlock : forall l g,
              increment_step ({| Locked := l; Global := g |}, Unlock)
                             ({| Locked := false; Global := g |}, Done).

Inductive increment_final : increment_state -> Prop :=
| IncFinal : forall l g,
               increment_final ({| Locked := l; Global := g |}, Done).

Definition increment_ts :=
  {|
    State := increment_state;
    Super := {| Init := increment_init;
                Step := increment_step;
                Final := increment_final
             |}
  |}.


(* Running transition systems in parallel *)
Inductive parallel_init {Shared Private1 Private2 : Set}
          (Init1 : Shared * Private1 -> Prop)
          (Init2 : Shared * Private2 -> Prop)
: Shared * Private1 * Private2 -> Prop :=
| Pinit : forall sh pr1 pr2,
            Init1 (sh, pr1)
            -> Init2 (sh, pr2)
            -> parallel_init Init1 Init2 (sh, pr1, pr2).

Inductive parallel_step {Shared Private1 Private2 : Set}
          (Step1 : Shared * Private1 -> Shared * Private1 -> Prop)
          (Step2 : Shared * Private2 -> Shared * Private2 -> Prop)
: Shared * Private1 * Private2 -> Shared * Private1 * Private2 -> Prop :=
| Pstep1 : forall sh pr1 pr2 sh' pr1',
             Step1 (sh, pr1) (sh', pr1')
             -> parallel_step Step1 Step2 (sh, pr1, pr2) (sh', pr1', pr2)
| Pstep2 : forall sh pr1 pr2 sh' pr2',
             Step2 (sh, pr2) (sh', pr2')
             -> parallel_step Step1 Step2 (sh, pr1, pr2) (sh', pr1, pr2').

Inductive parallel_final {Shared Private1 Private2 : Set}
          (Final1 : Shared * Private1 -> Prop)
          (Final2 : Shared * Private2 -> Prop)
: Shared * Private1 * Private2 -> Prop :=
| Pfinal : forall sh pr1 pr2,
             Final1 (sh, pr1) -> Final2 (sh, pr2) -> parallel_final Final1 Final2 (sh, pr1, pr2).

Definition parallel {Shared Private1 Private2 : Set}
           (ts1 : @transition_system' (Shared * Private1))
           (ts2 : @transition_system' (Shared * Private2)) :=
  {|
    State := Shared * Private1 * Private2;
    Super := {| Init := parallel_init (Init ts1) (Init ts2);
                Step := parallel_step (Step ts1) (Step ts2);
                Final := parallel_final (Final ts1) (Final ts2)
             |}
  |}.

Definition increment2_ts := parallel increment_ts increment_ts.

Definition has_lock (pr : increment_program) : bool :=
  match pr with
    | Lock => false
    | Done => false
    | _ => true
  end.

Definition contribution_from (pr : increment_program) : nat :=
  match pr with
    | Lock | Read | Write _ => 0
    | Unlock | Done => 1
  end.

Definition program_ok (self other : increment_program) : Prop :=
  match self with
    | Lock | Done => True
    | Read => has_lock other = false
    | Write n => has_lock other = false /\ n = contribution_from other
    | Unlock => has_lock other = false
  end.

Definition shared_from_private (pr1 pr2 : increment_program) :=
  {| Locked := has_lock pr1 || has_lock pr2;
     Global := contribution_from pr1 + contribution_from pr2
  |}.

Inductive increment2_invariant : State increment2_ts -> Prop :=
| Inc2Inv :
    forall pr1 pr2,
      program_ok  pr1 pr2
      -> program_ok  pr2 pr1
      -> increment2_invariant (shared_from_private pr1 pr2,
                              pr1, pr2).

(* restate invariant in terms of equality *)
Lemma Inc2Inv' : forall sh pr1 pr2,
                  sh = shared_from_private pr1 pr2
                  -> program_ok pr1 pr2
                  -> program_ok pr2 pr1
                  -> increment2_invariant (sh, pr1, pr2).
Proof.
  intros.
  rewrite H.
  apply Inc2Inv; assumption.
Qed.

Lemma final_eq :
  forall st,
    Final increment2_ts st
    -> increment2_invariant st
    -> st = ({| Locked := false; Global := 2 |}, Done, Done).
Proof.
  destruct 1.
  inversion H; subst.
  inversion H0; subst.
  inversion 1; subst.
  simpl. reflexivity.
Qed.

Hint Resolve run_final.

Theorem increment2_ts_correct :
  forall st,
    run increment2_ts st -> st = ({| Locked := false; Global := 2 |}, Done, Done).
Proof.
  intros.
  apply final_eq; eauto.
  apply invariant_final.
  (* construct isInvariant *)
  constructor.
  (* forall st0, Init increment2_ts st0 -> increment2_invariant st0 *)
  destruct 1.
  inversion H0; subst.
  inversion H1; subst.
  change {| Locked := false; Global := 0 |} with (shared_from_private Lock Lock).
  constructor; simpl; intuition.

  (* forall st0 st', Step increment2_ts st0 st' -> increment2_invariant st0 -> increment2_invariant st' *)
  destruct 1. (* case analysis on which step we take *)
  (* case analysis on one program, inversion on the step the other program is taking *)
  destruct pr2; inversion H0; subst; inversion 1; subst; apply Inc2Inv'; simpl in *; intuition; subst; reflexivity || congruence.
  destruct pr1; inversion H0; subst; inversion 1; subst; apply Inc2Inv'; simpl in *; intuition; subst; reflexivity || congruence.
  assumption.
Qed.
