(* https://softwarefoundations.cis.upenn.edu/lf-current/Extraction.html *)

(*
Proof General https://proofgeneral.github.io/
https://github.com/cpitclaudel/company-coq
*)

From Coq Require Extraction.
Extraction Language OCaml.

Definition nand (a b: bool) := negb (a && b).
Print nand.

Recursive Extraction nand.

Set Extraction Output Directory "ocaml".
Extraction "nand.ml" nand.
(*
https://opam.ocaml.org/
https://github.com/ocaml/dune

opam install utop
*)

Extract Inductive bool => "bool" [ "true" "false" ].
Recursive Extraction nand.

(* https://ocaml.org/manual/5.3/api/Bool.html *)
Extract Inlined Constant negb => "not".
Recursive Extraction nand.

Extraction "nand.ml" nand.

Require Import Arith.
Import Init.Nat.

(* https://en.wikipedia.org/wiki/Fibonacci_sequence
   0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144 ... *)
(*
Fixpoint nth_fib_naive (n: nat): nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n => nth_fib_naive (n-1) + nth_fib_naive (n-2)
  end.
*)

Fixpoint nth_fib_naive (n: nat): nat :=
  match n with
  | 0 => 0
  | S n' (* n' = n - 1 *)
    => match n' with
      | 0 (* n = 1 *) => 1
      | S n'' (* n'' = n - 2 *)
        => nth_fib_naive n' + nth_fib_naive n''
      end
  end.

Compute nth_fib_naive 12. (* = 144 *)
Example nth_fib_naive_ex12: nth_fib_naive 12 = 144.
Proof. reflexivity. Qed.

Require Import List.
Import ListNotations.

Check map.
Search (nat -> list nat).

Compute seq 0 13.
Compute map nth_fib_naive (seq 0 13).
(* = [0; 1; 1; 2; 3; 5; 8; 13; 21; 34; 55; 89; 144] *)

Example nth_fib_naive_ex:
  map nth_fib_naive (seq 0 13) =
    [0; 1; 1; 2; 3; 5; 8; 13; 21; 34; 55; 89; 144].
Proof. reflexivity. Qed.

Fixpoint fib_aux (a b n: nat): nat :=
  match n with
  | 0 => a
  | 1 => b
  | S n' => fib_aux b (a + b) n'
  end.

Definition nth_fib (n: nat): nat := fib_aux 0 1 n.

Compute map nth_fib (seq 0 13).

Example nth_fib_ex:
  map nth_fib (seq 0 13) =
    [0; 1; 1; 2; 3; 5; 8; 13; 21; 34; 55; 89; 144].
Proof. reflexivity. Qed.

Recursive Extraction nth_fib.

Extract Inductive nat => "int" [ "0" "(fun x -> x + 1)" ].

Recursive Extraction nth_fib.

Extract Inductive nat => "int"
  [ "0" "(fun x -> x + 1)" ]
  "(fun zero succ n ->
      if n=0 then zero () else succ (n-1))".

Recursive Extraction nth_fib.

Extract Inlined Constant add => "( + )".

Recursive Extraction nth_fib.

Extraction "fib.ml" nth_fib.
Extraction "fib_naive.ml" nth_fib_naive.

Theorem nth_fib_correct: forall n: nat, nth_fib n = nth_fib_naive n.
Proof.
  unfold nth_fib.
  induction n as [| n' IH]. { reflexivity. }
  simpl. Abort.

Check nat_ind.

(* https://en.wikipedia.org/wiki/Mathematical_induction#Complete_(strong)_induction *)
Lemma complete_induction_aux (P: nat -> Prop):
  (forall n: nat, (forall m: nat, m < n -> P m) -> P n)
  -> forall n k: nat, k <= n -> P k.
Proof.
  intro H. induction n as [| n' IH].
  - intros k Hle.
    Search (_ <= 0). apply le_0_r in Hle. subst k.
    apply H. intros m Hlt.
    Search (_ < 0). apply nlt_0_r in Hlt. contradiction.
  - intros k Hle. apply H. intros m Hlt.
    apply IH. Search (_ < _) (_ <= _).

    (* assert (m < S n') as Hlt2. *)
    (* { apply lt_le_trans with k; assumption. } *)
    (* apply PeanoNat.lt_n_Sm_le. exact Hlt2. *)

    apply PeanoNat.lt_n_Sm_le.
    apply lt_le_trans with k; assumption.
Qed.

Theorem complete_induction (P: nat -> Prop):
  (forall n: nat, (forall m: nat, m < n -> P m) -> P n)
  -> forall n: nat, P n.
Proof.
  intro H. Check (complete_induction_aux P H).
  pose (complete_induction_aux P H) as H'.
  intro n. apply (H' n).
  Locate "_ <= _". Print Peano.le. Search (?x <= ?x).
  apply le_n.
Qed.

Theorem nth_fib_correct: forall n: nat, nth_fib n = nth_fib_naive n.
Proof.
  unfold nth_fib. apply complete_induction.
  intros n H. destruct n as [| n']. { reflexivity. }
  simpl. destruct n' as [| n'']. { reflexivity. }
  simpl. Abort.

Theorem nth_fib_naive_step: forall n: nat,
    nth_fib_naive (2 + n) = nth_fib_naive (1 + n) + nth_fib_naive n.
Proof.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem nth_fib_step: forall n: nat,
    nth_fib (2 + n) = nth_fib (1 + n) + nth_fib n.
Proof.
  unfold nth_fib. apply complete_induction.
  intros n H. simpl. Abort.

Lemma fib_aux_step1: forall n a b: nat,
    fib_aux a b (S n) = fib_aux b (a + b) n.
Proof.
  intros n a b. simpl. destruct n as [| n'].
  - simpl. reflexivity.
  - reflexivity.
Qed.

Lemma fib_aux_step2: forall n a b: nat,
    fib_aux a b (2 + n) = fib_aux a b (1 + n) + fib_aux a b n.
Proof.
  apply (complete_induction (fun n => forall a b: nat, _)).
  intros n H a b. destruct n as [| n'].
  { simpl. apply add_comm. }
  replace (2 + S n') with (S (2 + n')) by reflexivity.
  rewrite !fib_aux_step1.
  rewrite (H n') by apply lt_succ_diag_r.
  apply f_equal2_plus; [|reflexivity].
  rewrite fib_aux_step1. reflexivity.
Qed.

Theorem nth_fib_step: forall n: nat,
    nth_fib (2 + n) = nth_fib (1 + n) + nth_fib n.
Proof.
  intro n. unfold nth_fib. apply fib_aux_step2.
Qed.

Theorem nth_fib_correct: forall n: nat, nth_fib n = nth_fib_naive n.
Proof.
  apply complete_induction.
  intros n H.
  destruct n as [| n']. { reflexivity. }
  destruct n' as [| n'']. { reflexivity. }
  replace (S (S n'')) with (2 + n'') by reflexivity.
  rewrite nth_fib_naive_step. rewrite nth_fib_step.
  rewrite !H.
  - reflexivity.
  - apply lt_lt_succ_r. apply lt_succ_diag_r.
  - simpl. apply lt_succ_diag_r.
Qed.

