Require Export SfLib.

(* even / odd proofs *)
Fixpoint even_count (n : nat) (l : list nat) : bool :=
  match l with
    | nil => true
    | h :: t => if beq_nat n h then negb (even_count n t) else even_count n t
  end.

Definition odd_count (n : nat) (l : list nat) : bool :=
  negb (even_count n l).

Theorem odd_count_then_even_count :
  forall n l,
    even_count n l = true -> odd_count n (n :: l) = true.
Proof.
  intros n l.
  destruct l.
  Case "l = []". intros H. unfold odd_count. simpl.
  rewrite <- beq_nat_refl. reflexivity.
  Case "l = h :: t". intros H. unfold odd_count. rewrite negb_true_iff.
  simpl. rewrite <- beq_nat_refl. rewrite negb_false_iff.
  destruct (beq_nat n n0) eqn:H1.
  SCase "n = n0". rewrite negb_true_iff. simpl in H. rewrite H1 in H.  rewrite negb_true_iff in H. apply H.
  SCase "n != n0". simpl in H. rewrite H1 in H. apply H.
Qed.

Theorem odd_count_then_even_count' :
  forall n l,
    even_count n l = true -> odd_count n (n :: l) = true.
Proof.
  intros n l H.
  destruct l.
  Case "l = []". unfold odd_count. simpl. rewrite <- beq_nat_refl. reflexivity.
  Case "l = h :: t". unfold odd_count. simpl.  rewrite <- beq_nat_refl. rewrite negb_involutive.
  simpl in H. destruct (beq_nat n n0); apply H.
Qed.






(* *** *)
Inductive state : Type :=
| A : state
| B : state.

Inductive input : Type :=
| one : input
| zero : input.

Definition beq_input (a b : input) : bool :=
  match (a, b) with
    | (one, one) => true
    | (zero, zero) => true
    | _ => false
  end.

Definition beq_state (a b :state) : bool :=
  match (a, b) with
    | (A, A) => true
    | (B, B) => true
    | _ => false
  end.

Fixpoint count_input (v:input) (s: list input) : nat :=
  match s with
    | nil => 0
    | h :: t => (if beq_input v h then 1 else 0) + count_input v t
  end.

Inductive automata : Type :=
| Automata (state : state) (consumed : list input).

Fixpoint run_automata (a : automata) (input : list input) : automata :=
  match a with
    | Automata state consumed =>
      match input with
        | nil => a
        | h :: t => match (h, state) with
                      | (zero, A) => run_automata (Automata A (zero :: consumed)) t
                      | (one, A) => run_automata (Automata B (one :: consumed)) t
                      | (zero, B) => run_automata (Automata B (zero :: consumed)) t
                      | (one, B) => run_automata (Automata A (one :: consumed)) t
                    end
      end
  end.

Definition is_final (a : automata) : bool :=
  match a with
    | Automata state _ => beq_state state B
  end.

Theorem automata_oddb :
  forall (l : list input),
    match run_automata (Automata A nil) l with
      | Automata state consumed => beq_state state B = true <-> Nat.odd (count_input one consumed) = true
    end.
Proof.
  intros l.
  induction l as [| h t].
  Case "l = nil". simpl. split ; intros; inversion H.
  Case "l = h :: t". destruct h. simpl.
  Abort.
