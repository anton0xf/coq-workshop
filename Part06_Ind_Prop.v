Locate "_ -> _".
(* Notation "A -> B" := (forall _ : A, B) : type_scope (default interpretation) *)

Module MyLogic.

  (* False *)
  Inductive empty: Set := .
  Inductive False: Prop := .

  Example false: False.
  Proof. Abort.

  (* True *)
  Inductive unit: Set := tt.
  Inductive True: Prop := I.

  Example true: True.
  Proof. exact I. Qed.

  Print true. (* true = I : True *)

  Example true': True := I.
  Print true'.

  (* Implication (non-standard) *)
  Definition impl (A B: Prop): Prop := forall HA: A, B.
  Print impl.
  (* impl = fun A B : Prop => A -> B *)
  (*      : Prop -> Prop -> Prop *)

  Example exfalso (A: Prop): impl False A. (* -> *)
  Proof. intro H. destruct H. Qed.

  Print exfalso.
  (* fun (A : Prop) (H : False) => match H return A with *)
  (*                               end *)
  (*      : forall A : Prop, False -> A *)
  
  Definition exfalso' (A: Prop) (H: False): A :=
    match H with end.

  Example modus_ponens (A B: Prop): (A -> B) -> A -> B.
  Proof. (* associativity *)
    intro HAB. intro HA. apply HAB. exact HA. 
  Qed.
  
  Print modus_ponens.
  
  Definition modus_ponens' (A B: Prop) (HAB: A -> B) (HA: A): B
    := HAB HA.

  Definition modus_ponens2 (A B: Prop) (HAB: A -> B): A -> B
    := HAB.
    
  Definition id {A: Type} (x: A): A := x.
  Check fun A B: Prop => @id (A -> B).
  
  Definition modus_ponens3 (A B: Prop) (HAB: A -> B): (A -> B)
    := @id (A -> B) HAB.
  
  Definition modus_ponens4 (A B: Prop): (A -> B) -> (A -> B)
    := id.

  (* And *)
  Inductive prod (A B: Type): Type := pair (a: A) (b: B).
  Arguments pair {A} {B}.
  
  Definition fst {A B: Type} (p: prod A B): A
    := match p with
       | pair a _ => a
       end.

  Inductive and (A B: Prop): Prop := conj (HA: A) (HB: B).
  Arguments conj {A} {B}.
  
  Example and_prop (A B: Prop) (HA: A) (HB: B): and A B.
  Proof. 
    Print conj.
    apply conj.
    - exact HA.
    - exact HB.
  Qed.
  
  Example and_prop' (A B: Prop) (HA: A) (HB: B): and A B.
  Proof. split. { exact HA. } { exact HB. } Qed.

  Definition proj1 {A B: Prop} (p: and A B): A :=
    match p with
    | conj HA _ => HA
    end.

  Theorem proj2 {A B: Prop} (p: and A B): B.
  Proof. destruct p as [HA HB]. exact HB. Qed.
  
  Print proj2.
  
  Inductive or (A B: Prop): Prop :=  
  | or_introl (HA: A)
  | or_intror (HB: B).
  
  Arguments or_introl {A} {B}.
  Arguments or_intror {A} {B}.

  Example or_l (A B: Prop) (HA: A): or A B.
  Proof. 
    Check or_introl.
    apply or_introl. exact HA.
  Qed.
  
  (* TODO Negation *)

End MyLogic.

Print False.
(* Inductive False : Prop :=  . *)

Print True.
(* Inductive True : Prop :=  I : True. *)

Locate "_ /\ _".
(* Notation "A /\ B" := (and A B) : type_scope 
    (default interpretation) *)
Print and.
(* Inductive and (A B : Prop) : Prop 
    :=  conj : A -> B -> A /\ B. *)

(*
Inductive and (A B:Prop) : Prop :=
  conj : A -> B -> A /\ B
where "A /\ B" := (and A B) : type_scope.
*)

Locate "_ \/ _".
(* Notation "A \/ B" := (or A B) : type_scope (default interpretation) *)

Print or.
(* Inductive or (A B : Prop) : Prop :=  or_introl : A -> A \/ B | or_intror : B -> A \/ B. *)
