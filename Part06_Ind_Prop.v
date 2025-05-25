Module MyLogic.

  (* False *)
  Inductive empty: Set := .
  Inductive False: Prop := . (* TODO more details *)

  Example false: False.
  Proof. Abort.
  
  (* see exfalso below *)

  (* True *)
  Inductive unit: Set := tt.
  Inductive True: Prop := I.

  Example true: True.
  Proof. exact I. Qed.

  Print true. (* true = I : True *)

  Example true': True := I.
  Print true'.
  
  Definition true'': True := I.
  
  Locate "_ -> _".
  (* Notation "A -> B" := (forall _ : A, B) : type_scope 
     (default interpretation) *)

  (* Implication (non-standard) *)
  Definition impl (A B: Prop): Prop := forall (HA: A), B.
  
  Print impl.
  (* impl = fun A B : Prop => A -> B : Prop -> Prop -> Prop *)

  Example ignore_premise (A: Prop): A -> True.
  Proof. intro H. exact I. Qed.
  
  Print ignore_premise.
  
  Example ignore_premise' (A: Prop): A -> True 
    := fun (H: A) => I.

  Example exfalso (A: Prop): False -> A.
  Proof. intro H. destruct H. Qed.

  Print exfalso.
  (* fun (A : Prop) (H : False) => match H return A with *)
  (*                               end *)
  (*      : forall A : Prop, False -> A *)
  
  Definition exfalso' (A: Prop) (H: False): A :=
    match H with 
    (* | constructor *)
    end.

  Example modus_ponens (A B: Prop): (A -> B) -> A -> B.
  Proof. (* associativity *)
    intro HAB. intro HA. apply HAB. exact HA. 
  Qed.
  
  Example modus_ponens' (A B: Prop): (A -> B) -> A -> B.
  Proof.
    intro HAB. intro H. apply HAB in H. exact H. 
  Qed.
  
  Example modus_ponens'' (A B: Prop): (A -> B) -> A -> B.
  Proof.
    intro HAB. intro H. 
    Check (HAB H). exact (HAB H). 
  Qed.
  
  Print modus_ponens.
  
  Example modus_ponens''' (A B: Prop): (A -> B) -> A -> B
    := fun (HAB: A -> B) (HA: A) => HAB HA.

  Definition modus_ponens1 (A B: Prop) (HAB: A -> B) (HA: A): B
    := HAB HA.

  Definition modus_ponens2 (A B: Prop): (A -> B) -> (A -> B)
    := fun (HAB: A -> B) => HAB.

  Definition modus_ponens2' (A B: Prop) (HAB: A -> B): A -> B
    := HAB.

  Definition id {A: Type} (x: A): A := x.
  
  Check (@id nat).
  Compute (id 42).
  
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
  
  Locate "_ /\ _". (* Notation "A /\ B" := (and A B) : type_scope *)
  
  Example and_prop (A B: Prop): A -> B -> and A B.
  Proof.
    intros HA HB. 
    Check (@conj A B).
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
  
  (* or *)
  Inductive or (A B: Prop): Prop :=  
  | or_introl (HA: A)
  | or_intror (HB: B).
  
  Arguments or_introl {A} {B}.
  Arguments or_intror {A} {B}.
  
  Locate "_ \/ _". (* Notation "A \/ B" := (or A B) : type_scope *)

  Example or_l (A B: Prop): A -> or A B.
  Proof.
    intro HA.
    Check (@or_introl A B).
    apply or_introl. exact HA.
  Qed.
  
  Print or_l.
  
  Example or_l' (A B: Prop) (HA: A): or A B
    := or_introl HA.
  
  (* Negation: ~A = A -> False *)
  Definition not (A: Prop): Prop := A -> False.
  Notation "~ x" := (not x) : type_scope.
  
  Example contra (A B: Prop): (A -> B) -> (~B -> ~A).
  Proof.
    intros H HnB. unfold not. intro HA. 
    unfold not in HnB. apply HnB. 
    apply H. exact HA.
  Qed.
End MyLogic.