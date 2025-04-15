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

(* TODO generic function with pattern matching by type argument *)
