(* Vernacular and Gallina *) 

(* comments and command separator *)

Require Import Bool.
Require Import Arith.

(** standard types and operations *)

(* type declaration *)
Check bool.
Check nat.

Check true.
Check (true : bool).
Check true : bool.
Fail Check true : nat.

Check (bool : Set).
Check (bool : Type).
Check Set.
Check Type.
(* Set = Type(0) : Type(1) : Type(2) : ... *)

Check (true && false) : bool.
Compute (true && false). (* = false : bool *)

Locate "_ && _".
Locate "&&".
(* Notation "x && y" := (andb x y) : bool_scope 
   (default interpretation) *)

Print Notation "_ && _". (* doesn't work in jscoq *)
(* Notation "_ && _" at level 40 with arguments constr at level 40, 
   constr at next level,
   left associativity. *)

Check true && false && true.

Set Printing Parentheses.
Check true && false && true. (* (true && false) && true : bool *)

Print Notation "_ || _".
(* Notation "_ || _" at level 50 with arguments constr at level 50, 
   constr at next level,
   left associativity. *)

Check true || false && true. (* true || (false && true) : bool *)

Unset Printing Parentheses.

Check 0: nat.
Check 5: nat.
Check (5 + 7): nat.

Compute (5 + 7). (* = 12 : nat *)
Compute 2 * 3.

(** definitions *)

Definition five := 5.

Check five.
Compute five. (* = 5 : nat *)
Compute five * 3.

Definition fifteen: nat := five * 3.
Check fifteen.
Compute fifteen.

(* theorems *)

Theorem equality_example : 5 + 7 = 12.
Proof. simpl. reflexivity. Qed.

Check equality_example.
Print equality_example.

(** functions *)

Definition mul3 (n: nat): nat := n * 3.

(* no parens *)
Compute mul3 4. (* = 12 : nat *)

Locate "*".
(* Notation "x * y" := (Init.Nat.mul x y) : nat_scope 
   (default interpretation) *)

Compute 2 * 3.
Compute Nat.mul 2 3.

Check (Nat.mul 2 3).

Unset Printing Notations.
Check 2 * 3. (* Init.Nat.mul 2 3 : nat *)
Set Printing Notations.

Check Nat.mul 2 3.

Compute 5 + (mul3 7).
Compute Nat.add 5 (mul3 7).

Compute (Nat.mul 2 3).

(* function types *)
Check mul3: nat -> nat.

Check Nat.mul: nat -> nat -> nat.
Check Nat.mul: nat -> (nat -> nat).
Fail Check Nat.mul : (nat -> nat) -> nat.

Set Printing Parentheses.
Check Nat.mul. (* : nat -> (nat -> nat) *)
Unset Printing Parentheses.

(* Curring *)
Check Nat.mul 2 : nat -> nat.
Check (Nat.mul 2) 3. (* 2 * 3 : nat *)

Definition mul3_curry: nat -> nat := Nat.mul 3.

Compute mul3_curry 5.

Theorem mul3_def (n: nat): mul3 n = n * 3.
Proof. simpl. unfold mul3. reflexivity. Qed.

Theorem mul3_def': forall n: nat, mul3 n = n * 3.
Proof. intro n. unfold mul3. reflexivity. Qed.

(** anonymous functions *)
Check (fun (n: nat) => n * 3): nat -> nat.
Compute (fun (n: nat) => n * 3) 2.

Definition mul3_lambda: nat -> nat := fun n: nat => n * 3.
Check mul3_lambda: nat -> nat.
Compute mul3_lambda 2.

Definition sum_sq3 (a b c: nat): nat := a^2 + b^2 + c^2.
Check sum_sq3: nat -> (nat -> (nat -> nat)).
Compute sum_sq3 1 2 3.

Definition sum_sq3_5: nat -> (nat -> nat) := sum_sq3 5.
Compute sum_sq3_5 6 7.
Compute (sum_sq3_5 6) 7.
Compute ((sum_sq3 5) 6) 7.

(* you can ommit some types *)
Definition five' := 5.
Check five.
Compute 5.

Definition mul3' n := n * 3.
Check mul3' : nat -> nat.
Compute mul3' 4.

Check (fun n => n * 2).

(* hole *)
Definition const1 (a: nat): _ := 1.

Check const1 : nat -> nat.

Compute const1 10.

Definition const1'  (_: nat)    := 1.
Definition const1'' (_: nat): _ := 1.
Definition const1_lambda: nat -> nat := fun _ => 1.

Print const1.
(* const1 = fun _ : nat => 1 *)
(*      : nat -> nat *)

(* Arguments const1 _%nat_scope *)

Definition mul3''  (n: _): _ := n * 3.

(** high order functions *)

Definition repeat2 (f: nat -> nat) (n: nat): nat := f (f n).
Compute repeat2 mul3 5.
Check repeat2.

(* curring examples *)
Definition mul3x2 := repeat2 mul3.

Definition comp (f g: nat -> nat) (n: nat) := f (g n).
Definition repeat2' (f: nat -> nat) := comp f f.

(** generic functions *)

Definition repeat2_gen (X: Type) (f: X -> X) (x: X): X := f (f x).
Check repeat2_gen.
Check repeat2_gen nat.
Check repeat2_gen bool.

Compute repeat2_gen nat mul3 5.
Compute repeat2_gen _ mul3 5.
Compute repeat2_gen bool negb true.

Arguments repeat2_gen {X}.

Compute repeat2_gen mul3 5.
Compute repeat2_gen negb true.

Check @repeat2_gen nat.
Compute @repeat2_gen nat mul3 5.

Definition repeat2_gen' {X: Type} (f: X -> X) (x: X): X := f (f x).
Compute repeat2_gen' mul3 5.
