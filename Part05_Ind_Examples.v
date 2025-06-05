Require Import Arith.
Import Nat.

(* bin-tree *)
Inductive bin_tree (A: Type) :=
| leaf
| node (val: A) (left right: bin_tree A).

Check node.

Arguments leaf {A}.
Arguments node {A}.

Check node 1 leaf leaf.
Check node 1 leaf (node 2 leaf leaf).

Notation "{{ }}" := leaf.
Notation "{{ x }}" := (node x leaf leaf).
Notation "l <~ x ~> r" := (node x l r) (at level 100).

Check node 1 leaf leaf.
Check node 1 leaf (node 2 leaf leaf).
Check {{4}} <~ 2 ~> {{5}}.

Definition tree_ex := 
  ({{4}} <~ 2 ~> {{5}}) <~ 1 ~> ({{6}} <~ 3 ~> {{}}).
(*
            1
          /   \
        2       3
       / \     /
      4   5   6
*)

(* https://en.wikipedia.org/wiki/Tree_rotation *)

Definition tree_ex2 := ({{9}} <~ 17 ~> {{23}}) <~ 50 ~> {{76}}.

Definition rotate_right {A: Type} (t: bin_tree A)
  : option (bin_tree A) 
  := match t with
     |      (a <~ A ~> b) <~ B ~> c => 
       Some (a <~ A ~> (b <~ B ~> c))
     | _ => None
     end.

Compute rotate_right tree_ex2.
Compute rotate_right tree_ex.

Fixpoint height {A: Type} (t: bin_tree A): nat :=
  match t with
  | {{}} => 0
  | t1 <~ _ ~> t2 => 1 + max (height t1) (height t2)
  end.

Compute height {{}}.
Compute height {{7}}.
Compute height ({{3}} <~ 7 ~> {{}}).
Compute height tree_ex.

Theorem height_node {A: Type} (x: A) (t1 t2: bin_tree A):
  height (t1 <~ x ~> t2) = 1 + max (height t1) (height t2).
Proof. reflexivity. Qed.

Fixpoint size {A: Type} (t: bin_tree A): nat :=
  match t with
  | {{}} => 0
  | t1 <~ _ ~> t2 => 1 + (size t1) + (size t2)
  end.

Compute size {{}}.
Compute size {{7}}.
Compute size ({{3}} <~ 7 ~> {{}}).
Compute size tree_ex.

Theorem size_lt {A: Type} (t: bin_tree A):
  size t < 2^(height t).
Proof.
  (*
    Base: t = {{}} => size t = 0 /\ height t = 0 => 0 < 2^0 = 1
    Step: t = t1 <~ x ~> t2:
      size t1 < 2 ^ height t1 /\ size t2 < 2 ^ height t2 =>
        (?) size t < 2 ^ height t

      size t1 < 2 ^ height t1 <=> 1 + size t1 <= 2 ^ height t1
      size t2 < 2 ^ height t2 <=> 1 + size t2 <= 2 ^ height t2

      sum:  2 + size t1 + size t2 <= (2 ^ height t1) + (2 ^ height t2)
      goal: 1 + size t1 + size t2 < 2 ^ (1 + max (height t1) (height t2))
            2 + size t1 + size t2 <= 2 * 2 ^ max (height t1) (height t2)

      new goal: (2 ^ height t1) + (2 ^ height t2) <=
             2 * 2 ^ max (height t1) (height t2) ==
             2 ^ max (height t1) (height t2) + 2 ^ max (height t1) (height t2)
   *)
  Locate "_ < _". Print Peano.lt. unfold Peano.lt.
  induction t as [ | x t1 IH1 t2 IH2].
  - simpl. Search (?x <= ?x). Print le_n. Print Peano.le.
    Check le_n. apply le_n.
  - simpl.
    Search (?x + 0 = ?x). rewrite add_0_r.
    Search (_ + _ <= _ + _).
    Search (?a <= ?b -> ?c <= ?d -> ?a + ?c <= ?b + ?d).
    Fail apply add_le_mono.
    Search (S (_ + _) = _ + S _). rewrite plus_n_Sm.
    Search (S (_ + _) = (S _) + _).
    Search ((S _) + _ = S (_ + _)). rewrite <- plus_Sn_m.
    Check add_le_mono.
    apply add_le_mono.
    + Search (?a <= ?b -> ?b <= ?c -> ?a <= ?c).
      apply le_trans with (m := 2 ^ height t1).
      * exact IH1.
      * Locate "^". Search pow Peano.le. 
        Search (?a <= ?b -> ?n ^ ?a <= ?n ^ ?b).
        apply pow_le_mono_r.
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
  induction t as [ | x t1 IH1 t2 IH2]. { apply le_n. }
  simpl. rewrite add_0_r. rewrite plus_n_Sm. 
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
| inl (a: A)
| inr (b: B).

Notation "x + y" := (sum x y): type_scope.

Check inl.
Arguments inl {A B}.
Arguments inr {A B} _.

Check inl.

Definition f (n: nat): bool + nat :=
  match n with
  | 0 => inl false
  | 1 => inl true
  | n => inr (n - 2)
  end.

Compute f 0.
Compute f 1.
Compute f 5.
