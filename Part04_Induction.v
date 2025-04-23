Theorem add_O_r (n: nat): n + O = n.
  Proof. 
    Fail reflexivity.
    simpl. destruct n as [ | n'].
    - (* n = O *) reflexivity.
    - (* n = S n' *) simpl. f_equal. (* ?? *)
  Abort.

  Check nat_ind.

Theorem add_O_r (n: nat): n + O = n.
Proof. 
  apply (nat_ind (fun n => n + O = n)).
  - reflexivity.
  - intros. simpl. f_equal. exact H.
Qed.

Theorem add_O_r' (n: nat): n + O = n.
Proof.
  induction n as [ | n' IH ].
  - reflexivity.
  - simpl. f_equal. exact IH.
Qed.