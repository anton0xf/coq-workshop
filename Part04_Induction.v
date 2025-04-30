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

Theorem add_O_l (n: nat): O + n = n.
Proof. reflexivity. Qed.

(* same as forall *)
Check add_O_l. (* : forall n : nat, O + n = n *)

Check add_O_l two.

Example add_O_two: O + two = two.
Proof. exact (add_O_l two). Qed.

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
Proof. intro H. rewrite H. reflexivity. Qed. (* <- -> *)

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
  Check (nat_ind (fun n => n + O = n)).
  apply (nat_ind (fun n => n + O = n)).
  - reflexivity.
  - intros k H. simpl. rewrite H. reflexivity.
Qed.

Theorem add_O_r' (n: nat): n + O = n.
Proof.
  induction n as [ | n' IH ].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* Theorem add_comm: forall (n m: nat), n + m = m + n.
Proof.
  induction n.
  - intro m. rewrite add_O_l. rewrite add_O_r. reflexivity.
  - intro m. simpl. *)

End MyNat.

Require Import Arith.
Import Nat.

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
  - simpl. reflexivity.
  - simpl. intros ys zs. rewrite IH. reflexivity.
Qed.

End MyList.

Fail Check 1 :: nil.

Require Import List.
Import ListNotations.

Check 1 :: nil.
Check [1; 2].

(* bin-tree *)
Inductive bin_tree (A: Type) :=
| leaf
| node (val: A) (left right: bin_tree A).

Arguments leaf {A}.
Arguments node {A}.

Notation "{{ }}" := leaf.
Notation "{{ x }}" := (node x leaf leaf).
Notation "l <~ x ~> r" := (node x l r) (at level 100).

Check node 1 leaf leaf.
Check node 1 leaf (node 2 leaf leaf).
Check {{4}} <~ 2 ~> {{5}}.
Definition tree_ex := 
  ({{4}} <~ 2 ~> {{5}}) <~ 1 ~> ({{6}} <~ 3 ~> {{}}).

(* https://en.wikipedia.org/wiki/Tree_rotation *)
Definition rotate_right {A: Type} (t: bin_tree A)
  : option (bin_tree A) 
  := match t with
     |      (a <~ A ~> b) <~ B ~> c => 
       Some (a <~ A ~> (b <~ B ~> c))
     | _ => None
     end.

Compute rotate_right tree_ex.

Fixpoint height {A: Type} (t: bin_tree A): nat :=
  match t with
  | {{}} => 0
  | t1 <~ _ ~> t2 => 1 + max (height t1) (height t2)
  end.

Compute height {{7}}.
Compute height ({{3}} <~ 7 ~> {{}}).

Theorem height_node {A: Type} (x: A) (t1 t2: bin_tree A):
  height (t1 <~ x ~> t2) = 1 + max (height t1) (height t2).
Proof. reflexivity. Qed.

Fixpoint size {A: Type} (t: bin_tree A): nat :=
  match t with
  | {{}} => 0
  | t1 <~ _ ~> t2 => 1 + (size t1) + (size t2)
  end.

Theorem size_lt {A: Type} (t: bin_tree A):
  size t < 2^(height t).
Proof.
  (*
    Base: t = {{}} => size t = 0 /\ height t = 0 => 0 < 2^0 = 1
    Step: t = t1 <~ x ~> t2:
      size t1 < 2 ^ height t1 /\ size t2 < 2 ^ height t2 ->
        size t < 2 ^ height t
      
      size t1 < 2 ^ height t1 <=> 1 + size t1 <= 2 ^ height t1
      size t2 < 2 ^ height t2 <=> 1 + size t2 <= 2 ^ height t2
      
      sum:  2 + size t1 + size t2 <= (2 ^ height t1) + (2 ^ height t2)
      goal: 1 + size t1 + size t2 < 2 ^ (1 + max (height t1) (height t2))
            2 + size t1 + size t2 <= 2 * 2 ^ max (height t1) (height t2)

      new goal: (2 ^ height t1) + (2 ^ height t2) <=
                   2 * 2 ^ max (height t1) (height t2)
   *)
  Locate "<". unfold Peano.lt.
  induction t as [ | x t1 IH1 t2 IH2].
  - simpl. Search (?x <= ?x). apply le_n.
  - simpl.
    Search (_ + 0 = _). rewrite add_0_r.
    Search (_ + _ <= _ + _). Fail apply add_le_mono.
    Search (S (_ + _) = _ + S _). rewrite plus_n_Sm.
    Search (S _ + _ = S (_ + _)). rewrite <- plus_Sn_m.
    apply add_le_mono.
    + Search (?a <= ?b -> ?b <= ?c -> ?a <= ?c).
      apply le_trans with (2 ^ height t1).
      * exact IH1.
      * Search pow Peano.le. apply pow_le_mono_r.
        { discriminate. }
        Search Peano.le max. apply le_max_l.
    + apply le_trans with (2 ^ height t2). { exact IH2. }
      apply pow_le_mono_r. { discriminate. }
      apply le_max_r.
Qed.    

Theorem size_lt' {A: Type} (t: bin_tree A):
  size t < 2^(height t).
Proof.
  unfold Peano.lt.
  induction t as [ | x t1 IH1 t2 IH2]; simpl.
  { apply le_n. } rewrite add_0_r, plus_n_Sm.
  rewrite <- plus_Sn_m. apply add_le_mono.
  - apply le_trans with (2 ^ height t1). { exact IH1. }
    apply pow_le_mono_r. { discriminate. }
    apply le_max_l.
  - apply le_trans with (2 ^ height t2). { exact IH2. }
    apply pow_le_mono_r. { discriminate. }
    apply le_max_r.
Qed.    

(* sum type *)
Inductive sum (A B: Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B.

Notation "x + y" := (sum x y): type_scope.

Arguments inl {A B} _ , {A} B _.
Arguments inr {A B} _ , A {B} _.

Definition f (n: nat): bool + nat :=
  match n with
  | 0 => inl false
  | 1 => inl true
  | n => inr (n - 2)
  end.

Compute f 0.
Compute f 1.
Compute f 5.
