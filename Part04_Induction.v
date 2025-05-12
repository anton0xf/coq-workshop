Module MyNat.

(* https://en.wikipedia.org/wiki/Peano_axioms *)
Inductive nat: Set :=
| O: nat (* big letter 'o' *)
| S: nat -> nat. (* successor *)

Definition one := S O.
Definition two := S one.

Definition pred (n: nat): nat
  := match n with
     | O => O
     | S n' => n'
     end.

Compute pred two.

Example pred_two: pred two = one.
Proof. simpl. reflexivity. Qed.

Theorem pred_Sn (n: nat): pred (S n) = n.
Proof. simpl. reflexivity. Qed.

Fail Definition add (n m: nat): nat
  := match n with
     | O => m
     | S n' => S (add n' m)
     end.

(* https://en.wikipedia.org/wiki/Fixed-point_combinator *)
Fixpoint add (n m: nat): nat
  := match n with
     | O => m
     | S n' => S (add n' m)
     end.

Notation "n + m" := (add n m).

Theorem add_O_l: forall (n: nat), O + n = n.
Proof. intro n. reflexivity. Qed.

(* same as forall *)
Check add_O_l. (* : forall n : nat, O + n = n *)

Check add_O_l two : (O + two) = two.
Check (O + two) = two : Prop.

Example add_O_two: O + two = two.
Proof. exact (add_O_l two). Qed.

Definition add_O_two'': O + two = two := add_O_l two.

Example add_O_two': O + two = two.
Proof. apply add_O_l. Qed.

(** Implication *)

(* premise -> conclusion/consequent *)
Check forall A B: Prop, A -> B. 
Check true = false -> one = two.

(* It holds if we can proof B, given evidence (some proof) of A.
   Special cases:
   1. conclusion holds
   2. premise not holds *)

Example ignore_premise: negb false = true -> S one = two.
Proof. intro H. reflexivity. Qed.

Example ignore_conclusion: true = false -> 1 = 3.
Proof. intro H. discriminate H. Qed.

Theorem exfalso: forall A: Prop, true = false -> A.
Proof. intros A H. discriminate H. Qed.

Theorem eq_S (n m: nat): n = m -> S n = S m.
Proof. 
  (* forall H: (n = m), ((S n) = (S m)) *)
  intro H. rewrite H. (* <- -> *)
  reflexivity. 
Qed.

Locate "_ -> _".
(* Notation "A -> B" := (forall _ : A, B) : type_scope (default interpretation) *)

Theorem eq_S' (n m: nat): forall H: n = m, S n = S m.
Proof. intro H. rewrite H. reflexivity. Qed.

Theorem eq_S'' (n m: nat) (H: n = m): S n = S m.
Proof. rewrite H. reflexivity. Qed.

Theorem f_equal {A B: Type} (f: A -> B) (x y: A): x = y -> f x = f y.
Proof. intro H. rewrite H. reflexivity. Qed.

Theorem eq_S''' (n m: nat): n = m -> S n = S m.
Proof. (* apply f_equal. *)
  intro H. apply f_equal. (* or w/o apply *)
  exact H. 
Qed.

(* Proof by induction *)
Theorem add_O_r (n: nat): n + O = n.
Proof. 
  Fail reflexivity.
  Print add.
  simpl. destruct n as [ | n'].
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. f_equal. 
Abort.

(* 
Base: n = 0 => 0 + 0 = 0
Step: n = S k /\ k + 0 = k => n + 0 = n
*)

Check nat_ind.

Theorem add_O_r (n: nat): n + O = n.
Proof.
  Check nat_ind.
  Check (nat_ind (fun n => n + O = n)).
  apply (nat_ind (fun n => n + O = n)).
  - reflexivity.
  - intro k. intro H. simpl. rewrite H. reflexivity.
Qed.

Theorem add_O_r' (n: nat): n + O = n.
Proof.
  induction n as [ | k IH ].
  - reflexivity.
  - Print add. simpl. rewrite IH. reflexivity.
Qed.

End MyNat.

Require Import Arith.
Import Nat.
Check add.

Module MyList.

Inductive list (A: Type): Type :=
| nil: list A
| cons: A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} x xs.

Notation "x :: xs" := (cons x xs)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Check 1 :: 2 :: nil.
Check [1; 2].

Definition hd {A: Type} (default: A) (xs: list A) :=
  match xs with
  | [] => default
  | x :: _ => x
  end.

Compute hd 42 [1; 2].
Compute hd 42 [].

Definition hd_error {A: Type} (xs: list A): option A :=
  match xs with
  | [] => None
  | x :: _ => Some x
  end.

Compute hd_error [1; 2].
Compute @hd_error nat [].

Definition tail {A: Type} (xs: list A) :=
  match xs with
  | [] => []
  | _ :: xs' => xs'
  end.

Compute tail [1; 2; 3].
Compute @tail nat [].

Fixpoint repeat {A: Type} (x: A) (n: nat): list A :=
  match n with
  | O => []
  | S n' => x :: (repeat x n')
  end.

Compute repeat 7 3.
Compute repeat tt 7.

Fixpoint app {A: Type} (xs ys: list A): list A :=
  match xs with
  | [] => ys
  | x :: xs' => x :: app xs' ys
  end.

Notation "xs ++ ys" := (app xs ys)
  (right associativity, at level 60).

Compute [1; 2; 3] ++ [4; 5].

Theorem app_assoc {A: Type}: forall xs ys zs: list A,
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
  Print list.
  induction xs as [ | x xs' IH].
  - (* xs = [] *) simpl. reflexivity.
  - (* xs = x :: xs' *)
    simpl. intros ys zs. rewrite IH. reflexivity.
Qed.

End MyList.

Fail Check 1 :: nil.

Require Import List.
Import ListNotations.

Check 1 :: nil.
Check [1; 2].
