(* DD Level 1: Distinction (T0-T3) — Coq *)

(* T0: False has no constructors *)
Theorem T0 : False -> False.
Proof. auto. Qed.

(* T1: Distinction exists *)
Theorem true_ne_false : true <> false.
Proof. discriminate. Qed.

Theorem T1 : exists (x y : bool), x <> y.
Proof. exists true, false. exact true_ne_false. Qed.

(* T2: Binary structure *)
Theorem T2 : forall b : bool, b = true \/ b = false.
Proof. destruct b; auto. Qed.

(* T3: Codes are distinguishable *)
Inductive U : Set := BOOL | UNIT.

Theorem BOOL_ne_UNIT : BOOL <> UNIT.
Proof. discriminate. Qed.

Theorem T3 : exists (x y : U), x <> y.
Proof. exists BOOL, UNIT. exact BOOL_ne_UNIT. Qed.

(* Done *)
Theorem L01_done : True.
Proof. trivial. Qed.
