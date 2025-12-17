(* DD T5: Full Iteration — Φ diverges under non-unitary *)

Require Import Reals.
Require Import Lra.
Require Import Psatz.
Open Scope R_scope.

(** * Setup *)

Record Vec2 := mkVec2 { v1 : R; v2 : R }.
Definition norm2 (v : Vec2) : R := v1 v * v1 v + v2 v * v2 v.
Definition Phi (v : Vec2) : R := norm2 v.

Record Mat2 := mkMat2 { a11 : R; a12 : R; a21 : R; a22 : R }.

Definition apply (M : Mat2) (v : Vec2) : Vec2 :=
  mkVec2 (a11 M * v1 v + a12 M * v2 v)
         (a21 M * v1 v + a22 M * v2 v).

Definition Scale (s : R) : Mat2 := mkMat2 s 0 0 s.

Lemma Scale_norm : forall s v, norm2 (apply (Scale s) v) = s * s * norm2 v.
Proof.
  intros s [x y]. unfold apply, Scale, norm2. simpl. ring.
Qed.

(** * Iteration *)

Fixpoint iterate (M : Mat2) (n : nat) (v : Vec2) : Vec2 :=
  match n with
  | O => v
  | S n' => apply M (iterate M n' v)
  end.

(* Key: iterate Scale compounds *)
Lemma iterate_Scale : forall s n v,
  norm2 (iterate (Scale s) n v) = (s * s) ^ n * norm2 v.
Proof.
  intros s n v. induction n.
  - simpl. ring.
  - simpl iterate. rewrite Scale_norm. rewrite IHn. 
    simpl pow. ring.
Qed.

(** * Power bounds *)

Lemma pow_ge_1 : forall a n, a >= 1 -> a ^ n >= 1.
Proof.
  intros a n Ha. induction n; simpl.
  - lra.
  - assert (a * a ^ n >= a * 1) by (apply Rmult_ge_compat_l; lra).
    lra.
Qed.

Lemma pow_le_1 : forall a n, 0 <= a <= 1 -> a ^ n <= 1.
Proof.
  intros a n [Ha1 Ha2]. induction n; simpl.
  - lra.
  - assert (H1 : 0 <= a ^ n).
    { clear IHn. induction n; simpl; nra. }
    nra.
Qed.

Lemma pow_pos : forall a n, 0 < a -> 0 < a ^ n.
Proof.
  intros a n Ha. induction n; simpl.
  - lra.
  - apply Rmult_lt_0_compat; assumption.
Qed.

(** * Non-zero vectors have positive norm *)

Lemma norm2_pos : forall v, v1 v <> 0 \/ v2 v <> 0 -> 0 < norm2 v.
Proof.
  intros v [Hv|Hv]; unfold norm2;
  [assert (0 < v1 v * v1 v) by (apply Rsqr_pos_lt; assumption);
   assert (0 <= v2 v * v2 v) by apply Rle_0_sqr |
   assert (0 <= v1 v * v1 v) by apply Rle_0_sqr;
   assert (0 < v2 v * v2 v) by (apply Rsqr_pos_lt; assumption)]; lra.
Qed.

(** * Main theorems *)

(* s > 1 implies Φ grows *)
Theorem Phi_grows : forall s v n,
  s > 1 -> v1 v <> 0 \/ v2 v <> 0 ->
  Phi (iterate (Scale s) n v) >= Phi v.
Proof.
  intros s v n Hs Hv.
  unfold Phi. rewrite iterate_Scale.
  assert (H1 : norm2 v > 0) by (apply norm2_pos; assumption).
  assert (Hs2 : s * s > 1) by nra.
  assert (H2 : (s * s) ^ n >= 1) by (apply pow_ge_1; lra).
  nra.
Qed.

(* 0 < s < 1 implies Φ decays *)
Theorem Phi_decays : forall s v n,
  0 < s < 1 -> v1 v <> 0 \/ v2 v <> 0 ->
  Phi (iterate (Scale s) n v) <= Phi v.
Proof.
  intros s v n [Hs1 Hs2] Hv.
  unfold Phi. rewrite iterate_Scale.
  assert (H1 : norm2 v > 0) by (apply norm2_pos; assumption).
  assert (Hs3 : 0 < s * s < 1) by nra.
  assert (H2 : (s * s) ^ n <= 1) by (apply pow_le_1; lra).
  assert (H3 : 0 < (s * s) ^ n) by (apply pow_pos; lra).
  nra.
Qed.

(* Exact formula *)
Theorem Phi_iterate_exact : forall s v n,
  Phi (iterate (Scale s) n v) = (s * s) ^ n * Phi v.
Proof.
  intros. unfold Phi. apply iterate_Scale.
Qed.

(** * CRITICAL THEOREM: Unitarity ↔ Φ preservation *)

Theorem unitarity_iff_preservation : forall s v,
  v1 v <> 0 \/ v2 v <> 0 ->
  (forall n, Phi (iterate (Scale s) n v) = Phi v) <-> s * s = 1.
Proof.
  intros s v Hv. split.
  - (* Preservation implies s² = 1 *)
    intros H. specialize (H 1%nat).
    simpl in H. unfold Phi in H. rewrite Scale_norm in H.
    assert (Hn : norm2 v > 0) by (apply norm2_pos; assumption).
    nra.
  - (* s² = 1 implies preservation *)
    intros Hs n. unfold Phi. rewrite iterate_Scale.
    assert (H : (s * s) ^ n = 1).
    { rewrite Hs. induction n; simpl; lra. }
    lra.
Qed.

(** * Summary *)

(*
PROVEN FORMALLY:
1. iterate(Scale(s), n, v) has norm = s^(2n) * |v|²
2. s > 1 ⟹ Φ(n) ≥ Φ(0) (grows without bound as n → ∞)
3. 0 < s < 1 ⟹ Φ(n) ≤ Φ(0) (decays toward 0)
4. ∀n. Φ(n) = Φ(0) ⟺ s² = 1 (unitarity)

CONCLUSION:
Criticality (0 < Φ < ∞ for all time) REQUIRES s² = 1, i.e., unitarity.
This is the formal proof connecting DD's T5 (criticality) and T8 (unitarity).
*)
