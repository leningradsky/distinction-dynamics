(* DD Level 2: Iteration (T4) — Coq *)

Require Import Arith Lia.

(* Monoid laws *)
Theorem add_identity_l : forall n, 0 + n = n.
Proof. reflexivity. Qed.

Theorem add_identity_r : forall n, n + 0 = n.
Proof. lia. Qed.

Theorem add_assoc : forall m n p, (m + n) + p = m + (n + p).
Proof. lia. Qed.

(* T4: Irreversibility — S n <> n *)
Theorem T4 : forall n, S n <> n.
Proof.
  induction n.
  - discriminate.
  - intro H. injection H. exact IHn.
Qed.

(* No maximum *)
Theorem no_max : forall n, n < S n.
Proof. lia. Qed.

(* Done *)
Theorem L02_done : True.
Proof. trivial. Qed.
