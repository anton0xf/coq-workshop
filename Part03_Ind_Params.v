(** simple record *)

(* Set is optional *)
Inductive boxed: Set := box (x: bool).

Inductive bool_prod: Set := bool_pair (a b: bool).

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

Notation "( x , y )" := (pair x y).
Notation "x * y" := (prod x y) : type_scope.

Check (false, 42) : bool * nat.

Definition fst {A B: Type} (p: prod A B): A
  := match p with
     | pair a _ => a
     end.

Definition snd {A B: Type} (p: prod A B): B
  := match p with
     | pair _ b => b
     end.

Compute fst (false, 42).
Compute snd (false, 42).

Theorem fst_correct {A B: Type}: forall (a: A) (b: B), fst (a, b) = a.
Proof. reflexivity. Qed.

Theorem snd_correct {A B: Type}: forall (a: A) (b: B), snd (a, b) = b.
Proof. reflexivity. Qed.

Definition uncurry {A B C:Type} (f: A -> B -> C) (p: A * B): C
  := match p with
     | (x, y) => f x y
     end.

Definition curry {A B C: Type} (f: A * B -> C) (x: A) (y:B): C
  := f (x, y).

Check andb: bool -> bool -> bool.
Check uncurry andb: (bool * bool -> bool).

Compute (uncurry andb) (true, false).

(** two options *)

Inductive option (A: Type): Type :=
| Some (_: A)
| None.

Module ArrowForm.

  Inductive unit := tt: unit.
  Inductive boxed := box: bool -> boxed.
  Inductive bool_prod := bool_pair': bool -> bool -> bool_prod.

  Inductive option (A: Type): Type :=
  | Some: A -> option A
  | None: option A.

End ArrowForm.

Arguments Some {A} a.
Arguments None {A}.

Definition option_map {A B: Type}
  (f: A -> B) (o: option A) : option B
  := match o with
     | Some a => Some (f a) (* explicit B *)
     | None => None
     end.

Definition option_flat_map {A B: Type}
  (f: A -> option B) (o: option A): option B
  := match o with
     | Some a => f a
     | None => None
     end.

Definition option_map' {A B: Type}
  (f: A -> B) (o: option A) : option B
  := option_flat_map (fun x => Some (f x)) o.

Theorem map_by_flat_map {A B: Type} (f: A -> B) (o: option A):
  option_map f o = option_map' f o.
Proof. reflexivity. Qed. 

Notation "o >>= k" := (option_flat_map k o)
  (at level 90, left associativity).

Definition div2 (n: nat): option nat
  := if Nat.eqb (Nat.modulo n 2) 0
     then Some (Nat.div n 2)
     else None.

Compute Some 4 >>= div2.
Compute Some 3 >>= div2.
Compute None >>= div2.
Compute Some 6 >>= div2 >>= div2.

(** recursion *)

Module MyNat.

  (* https://en.wikipedia.org/wiki/Peano_axioms *)
  Inductive nat: Set :=
  | O : nat (* big letter 'o' *)
  | S : nat -> nat.

  Check S (S O).

  Definition pred (n: nat): nat
    := match n with
       | O => O
       | S n' => n'
       end.

  Compute pred (S (S O)).

  Fail Definition add (n m: nat): nat
    := match n with
       | O => m
       | S n' => S (add n' m)
       end.

  Fixpoint add (n m: nat): nat
    := match n with
       | O => m
       | S n' => S (add n' m)
       end.

  Fail Fixpoint broken_add (n m: nat): nat
    := match n with
       | O => m
       | _ => S (broken_add (pred n) m)
       end.

(* 
Fixpoint loop (n: nat): AnyType := loop n.
Fixpoint loop (n: nat): 1 = 0 := loop n.
 *)

End MyNat.

Require Import Arith.

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


(* bin-tree *)


(* TODO generic function with pattern matching by type argument *)
