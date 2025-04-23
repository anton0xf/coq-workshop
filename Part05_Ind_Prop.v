Inductive empty: Type := .

Theorem empty_exfalso (P: Prop): forall x: empty, P.
Proof. intro x. destruct x. Qed.