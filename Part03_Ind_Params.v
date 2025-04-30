(** simple record *)

(* Set/Type is optional *)
Inductive boxed: Type := box (x: bool). (* x unused *)
Check box true.
Compute box true.

Definition unbox (bx: boxed): bool := 
match bx with
| box b => b
end.

Compute unbox (box false).

(* product *)
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
Check pair false 42 : prod bool nat.

Check ((false, 42), box true) : bool * nat * boxed.

Definition fst {A B: Type} (p: prod A B): A
  := match p with
     | pair a _ => a
     end.

Compute fst (false, 42).

Definition snd {A B: Type} (p: A * B): B
  := match p with
     | (_, b) => b
     end.

Compute snd (false, 42).

Theorem fst_correct {A B: Type}: 
  forall (a: A) (b: B), fst (a, b) = a.
Proof. intros a b. simpl. reflexivity. Qed.

Theorem snd_correct {A B: Type}: 
  forall (a: A) (b: B), snd (a, b) = b.
Proof. reflexivity. Qed.

Definition uncurry {A B C:Type} (f: A -> B -> C): A * B -> C
  := fun p => match p with
     | (x, y) => f x y
     end.

Definition curry {A B C: Type} (f: A * B -> C): A -> B -> C
  := fun (x: A) (y:B) => f (x, y).

Check andb: bool -> bool -> bool.
Check uncurry andb: (bool * bool -> bool).

Compute (uncurry andb) (true, false).

(** two options *)

Inductive option (A: Type): Type :=
| Some (_: A)
| None.

Inductive result (E A: Type): Type :=
| ok (_: A)
| error (_: E).

Module ArrowForm.

  Inductive unit := tt: unit.
  Inductive bool := true : bool | false : bool.
  
  Inductive boxed := box: bool -> boxed.
  Inductive bool_prod := bool_pair: bool -> bool -> bool_prod.

  Inductive option (A: Type): Type :=
  | Some: A -> option A
  | None.

End ArrowForm.

Arguments Some {A} x.
Arguments None {A}.

Definition option_map {A B: Type}
  (f: A -> B) (o: option A) : option B
  := match o with
     | Some x => Some (f x) (* explicit B *)
     | None => None
     end.

Definition option_flat_map {A B: Type}
  (f: A -> option B) (o: option A): option B
  := match o with
     | Some x => f x
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

Compute div2 4.
Compute div2 5.
Compute Some 4 >>= div2.
Compute Some 3 >>= div2.
Compute None >>= div2.
Compute Some 6 >>= div2 >>= div2.

(** recursion *)

Module MyNat.

  (* https://en.wikipedia.org/wiki/Peano_axioms *)
  Inductive nat: Set :=
  | O: nat (* big letter 'o' *)
  | S: nat -> nat. (* successor *)

  Check S (S O).
  Compute S (S O).
  Definition two := S (S O).

  Definition pred (n: nat): nat
    := match n with
       | O => O
       | S n' => n'
       end.

  Compute pred two.

  Definition pred_part (n: nat): option nat
    := match n with
       | O => None
       | S n' => Some n'
       end.

  Compute pred_part two.
  Compute pred_part O.

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

  Fail Fixpoint broken_add (n m: nat): nat
    := match n with
       | O => m
       | _ => S (broken_add (pred n) m)
       end.

  Fail Fixpoint loop (n: nat): bool := loop n.
  Fail Fixpoint loop (n: nat): 1 = 0 := loop n.
  
  Notation "n + m" := (add n m).
  
  Theorem add_O_l (n: nat): O + n = n.
  Proof. reflexivity. Qed.

  Check add_O_l two.
  
  Example add_O_two: O + two = two.
  Proof. exact (add_O_l two). Qed.
  
  Example add_O_two': O + two = two.
  Proof. apply add_O_l. Qed.

End MyNat.

