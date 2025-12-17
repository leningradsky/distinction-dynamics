(* DD Level 3: Criticality & Number Tower (T5-T6) — Coq *)

Require Import ZArith QArith Reals.
Require Import Lia Lra.
Open Scope R_scope.

(** * T5: Critical Regime — 0 < Φ < ∞ *)

Definition critical (phi : R) : Prop := 0 < phi.

Theorem T5_critical_positive : forall phi, critical phi -> 0 < phi.
Proof. intros phi H. exact H. Qed.

(** * T6: Number Tower ℕ → ℤ → ℚ → ℝ *)

(* ℤ exists and is ordered *)
Theorem T6_Z_exists : exists z : Z, (z < 0)%Z.
Proof. exists (-1)%Z. lia. Qed.

Theorem T6_Z_ordered : forall a b : Z, (a < b \/ a = b \/ a > b)%Z.
Proof. intros. lia. Qed.

(* ℚ exists *)
Theorem T6_Q_exists : exists q : Q, Qlt 0 q.
Proof. exists (1#1)%Q. reflexivity. Qed.

(* ℝ exists and is dense *)
Theorem T6_R_exists : exists r : R, r > 0.
Proof. exists 1. lra. Qed.

Theorem T6_R_dense : forall x y : R, x < y -> exists z : R, x < z < y.
Proof. intros. exists ((x + y) / 2). lra. Qed.

(* Embeddings *)
Definition Z_to_R (z : Z) : R := IZR z.
Definition Q_to_R (q : Q) : R := Q2R q.

(* Embedding preserves order *)
Theorem T6_Z_embed_order : forall a b : Z, (a < b)%Z -> Z_to_R a < Z_to_R b.
Proof. intros. apply IZR_lt. assumption. Qed.

(* ℕ embeds in ℝ *)
Theorem T6_N_nonneg : forall n : nat, 0 <= INR n.
Proof. intros. apply pos_INR. Qed.

Theorem L03_done : True.
Proof. trivial. Qed.
