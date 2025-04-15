(** simple enumeration - enums *)

Unset Automatic Proposition Inductives.

Inductive empty: Type := .

Inductive unit: Type := tt. (* constructor *)
(* https://en.wikipedia.org/wiki/Unit_type *)

Check tt.

Set Automatic Proposition Inductives.

Inductive bool: Type := true | false.
Check true: bool.
Check false: bool.
(* true : bool : Type *)

Inductive issue_state: Type :=
| new
| in_progress 
| review 
| testing
| done.
 
Theorem true_is_true: true = true.
Proof. reflexivity. Qed.

Theorem true_not_false: true <> false.
Proof. discriminate. Qed.

Check true = true : Prop.

Theorem all_bools: forall b: bool, b = true \/ b = false.
Proof.
  intro b. destruct b.
  - (* b = true *) left. reflexivity.
  - (* b = false *) right. reflexivity.
Qed.

Theorem bools_is_eq: true = true /\ false = false.
Proof.
  split.
  - (* left *) reflexivity.
  - (* right *) reflexivity.
Qed.

Theorem bools_is_eq': true = true /\ false = false.
Proof. split; reflexivity. Qed.

Theorem empty_exfalso: forall x: empty, 1 = 0.
Proof. intro x. destruct x. Qed.

Definition negb (b: bool): bool
  := match b with
     | true => false
     | false => true
     end.

Compute negb true.

Definition negb' (b: bool): bool := if b then false else true.

Compute negb' true.

Definition andb (a b: bool): bool := if a then b else false.

Definition orb (a b: bool): bool := if a then true else b.

Print Notation "_ && _".
(* Notation "_ && _" at level 40 with arguments constr at level 40, 
   constr at next level,
   left associativity. *)

(* https://rocq-prover.org/doc/V9.0.0/corelib/Corelib.Init.Notations.html *)
Require Init.Notations.
   
Notation "x && y" := (andb x y).

Notation "x || y" := (orb x y).

Compute true && (false || true).

Theorem de_morgan: forall a b: bool, negb (a && b) = negb a || negb b.
Proof.
  intros a b. destruct a, b.
  - simpl. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem de_morgan': forall a b: bool, negb (a && b) = negb a || negb b.
Proof. destruct a, b; reflexivity. Qed.

(* new -> in_progress -> review -> testing -> done <- *)
Definition next_state (st: issue_state) :=
  match st with
  | new => in_progress
  | in_progress => review 
  | review => testing
  | testing => done
  | done => done
  end.

Definition comp {X: Type} (f g: X -> X) (x: X) := f (g x).
Definition repeat2 {X: Type} (f: X -> X): X -> X := comp f f.
Definition repeat4 {X: Type} (f: X -> X): X -> X := repeat2 (repeat2 f).

Compute repeat4 (fun n => n * 2) 1.

Theorem done_in_4_steps: forall st, repeat4 next_state st = done.
Proof.
  intro st. simpl. 
  destruct st.
  - simpl.
    unfold repeat4. simpl.
    unfold repeat2. simpl.
    unfold comp. simpl.
    reflexivity.
  - reflexivity.
Abort.

Theorem done_in_4_steps: forall st, repeat4 next_state st = done.
Proof. intro st. destruct st; reflexivity. Qed.


(** three-valued logic - Kleene/Priest *)
(* https://en.wikipedia.org/wiki/Three-valued_logic#Kleene_and_Priest_logics *)
Inductive B3 := F | U | T.

Definition neg3 (b: B3): B3
  := match b with
     | F => T
     | U => U
     | T => F
     end.

Definition and3 (a b: B3): B3
  := match a, b with
     | F, _ => F
     | _, F => F
     | U, _ => U
     | _, U => U
     | T, T => T
     end.

Definition or3 (a b: B3): B3
  := match a, b with
     | T, _ => T
     | _, T => T
     | U, _ => U
     | _, U => U
     | F, F => F
     end.

Definition bool_to_B3 (b: bool): B3
  := match b with
     | true => T
     | false => F
     end.

Theorem and3_incl: forall a b: bool, bool_to_B3 (andb a b) 
  = and3 (bool_to_B3 a) (bool_to_B3 b).
Proof. destruct a, b; reflexivity. Qed.
  
(* TODO prove some interesting facts *)
