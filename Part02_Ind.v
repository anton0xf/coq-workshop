(** simple enumeration *)
Inductive bool: Type :=
  | true
  | false.

Check true: bool.
Check false: bool.

Theorem true_is_true: true = true.
Proof. reflexivity. Qed.

Theorem true_not_false : true <> false.
Proof. discriminate. Qed.

Theorem all_bools: forall b: bool, b = true \/ b = false.
Proof.
  intro b. destruct b.
  - (* b = true *) left. reflexivity.
  - (* b = false *) right. reflexivity.
Qed.

Theorem bools_is_eq: true = true /\ false = false.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

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

Definition andb3 (b1: bool) (b2: bool) (b3: bool): bool
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Notation "x && y" := (andb x y).

Print Notation "_ && _".
(* Notation "_ && _" at level 40 with arguments constr at level 40, constr at next level,
   left associativity. *)

(* https://rocq-prover.org/doc/V9.0.0/corelib/Corelib.Init.Notations.html *)
Require Init.Notations.

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

(* negation of or *)
Definition nor (b1: bool) (b2: bool): bool
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example test_nor1: (nor true true) = false.
Proof. Fail reflexivity. Admitted.

Example test_nor2: (nor true false) = false.
Proof. Fail reflexivity. Admitted.

Example test_nor3: (nor false true) = false.
Proof. Fail reflexivity. Admitted.

Example test_nor4: (nor false false) = true.
Proof. Fail reflexivity. Admitted.

(* ex: state and proove the other De Morgan's law *)

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

Theorem and3_incl: forall a b: bool, bool_to_B3 (andb a b) = and3 (bool_to_B3 a) (bool_to_B3 b).
Proof. destruct a, b; reflexivity. Qed.
  
(* TODO prove some interesting facts *)

(** simple record *)

Inductive bool_prod: Type := bool_pair (a b: bool).

Check bool_pair true false: bool_prod.

Definition test_bool_pair := bool_pair true false.

Definition bool_fst (p: bool_prod): bool
  := match p with
     | bool_pair x _ => x
     end.

Compute bool_fst test_bool_pair.

Definition bool_snd (p: bool_prod): bool
  := match p with
     | bool_pair _ x => x
     end.

Compute bool_snd test_bool_pair.

(* dependent product *)
Inductive prod (A B: Type): Type := pair (a: A) (b: B).
Check pair. (* : forall A B : Type, A -> B -> prod A B *)
Check pair bool bool true false : prod bool bool.
Check pair bool nat false 42 : prod bool nat.

Arguments pair {A} {B}.

Check pair false 42 : prod bool nat.

Definition fst {A B: Type} (p: prod A B): A
  := match p with
     | pair a _ => a
     end.

Definition snd {A B: Type} (p: prod A B): B
  := match p with
     | pair _ b => b
     end.

Compute fst (pair false 42).
Compute snd (pair false 42).

Theorem fst_correct {A B: Type}: forall (a: A) (b: B), fst (pair a b) = a.
Proof. reflexivity. Qed.

Theorem snd_correct {A B: Type}: forall (a: A) (b: B), snd (pair a b) = b.
Proof. reflexivity. Qed.
