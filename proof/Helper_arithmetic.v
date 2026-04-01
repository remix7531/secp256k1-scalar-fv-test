(** * Helper_arithmetic: Pure Z lemmas for multi-limb arithmetic

    All results are stated over abstract base [B] and are independent
    of VST, secp256k1, or any specific word size.  Contents:

    - Limb reconstruction and extraction ([eval2], [eval4], [eval8], [limb]).
    - 2x2 schoolbook multiplication correctness ([schoolbook_mul_2x2]).
    - 4x4 schoolbook multiplication correctness ([schoolbook_mul_4x4]).
    - Carry-chain identity for 4-limb ripple addition ([reduce_carry_chain]).
    - Modular folding ([fold_sub_mod]) and conditional subtraction
      ([cond_sub_mod]) for modular reduction.

    We use [Z] rather than [N] because [lia]/[nia] are weaker over [N],
    and key stdlib lemmas ([Z_div_mod_eq_full], [Z.mod_pos_bound],
    etc.) lack mature [N] counterparts.  Staying in [Z] also avoids
    coercion noise at the VST/CompCert call sites. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Definitions *)
(* ================================================================= *)

(** Little-endian 2-limb evaluation. *)
Definition eval2 (B : Z) (a0 a1 : Z) : Z :=
  a0 + a1 * B.

(** Little-endian 4-limb evaluation. *)
Definition eval4 (B : Z) (a0 a1 a2 a3 : Z) : Z :=
  a0 + a1 * B + a2 * B^2 + a3 * B^3.

(** Little-endian 8-limb evaluation. *)
Definition eval8 (B : Z) (r0 r1 r2 r3 r4 r5 r6 r7 : Z) : Z :=
  r0 + r1 * B + r2 * B^2 + r3 * B^3
     + r4 * B^4 + r5 * B^5 + r6 * B^6 + r7 * B^7.

(** Limb extraction: the [i]-th digit of [x] in base [B]. *)
Definition limb (B : Z) (x : Z) (i : nat) : Z :=
  (x / B ^ Z.of_nat i) mod B.

(* ================================================================= *)
(** ** Tactics *)
(* ================================================================= *)

(** Expand [B^k] to left-associated products [B * B * ... * B]. *)
Ltac expand_pow B :=
  try replace (B ^ 7) with (B * B * B * B * B * B * B) by ring;
  try replace (B ^ 6) with (B * B * B * B * B * B) by ring;
  try replace (B ^ 5) with (B * B * B * B * B) by ring;
  try replace (B ^ 4) with (B * B * B * B) by ring;
  try replace (B ^ 3) with (B * B * B) by ring;
  try replace (B ^ 2) with (B * B) by ring.

(* ================================================================= *)
(** ** Reconstruction lemmas *)
(* ================================================================= *)

(** A value in [[0, B^4)] equals its 4-limb little-endian reconstruction.

    Strategy: name successive quotients [qk := q(k-1) / B], align
    compound divisions via [Z.div_div], show the top digit fits in
    one limb, then telescope using [Z_div_mod_eq_full]. *)
Lemma eval4_limbs : forall B x,
  B > 1 -> 0 <= x < B^4 ->
  eval4 B (limb B x 0) (limb B x 1) (limb B x 2) (limb B x 3) = x.
Proof.
  intros B x HB Hx.
  unfold limb, eval4.
  simpl (Z.of_nat _).
  rewrite Z.pow_0_r, Z.pow_1_r, Z.div_1_r.

  expand_pow B.

  (* Name successive quotients q_k = q_{k-1} / B *)
  set (q0 := x / B).
  set (q1 := q0 / B).
  set (q2 := q1 / B).

  (* Align compound divisions via Z.div_div *)
  replace (x / (B * B)) with q1 by
    (unfold q1, q0; rewrite <- Z.div_div by lia; reflexivity).
  replace (x / (B * B * B)) with q2 by
    (unfold q2, q1, q0; do 2 rewrite <- Z.div_div by lia; reflexivity).

  (* Top digit fits in one limb *)
  assert (Hq2 : 0 <= q2 < B).
  { unfold q2, q1, q0.
    split.
    - repeat (apply Z.div_pos; [|lia]); lia.
    - do 3 (apply Z.div_lt_upper_bound; [lia|]).
      replace (B * (B * (B * B))) with (B ^ 4) by ring.
      lia. }
  rewrite (Zmod_small q2 B Hq2).

  (* Telescope: substitute div/mod identities *)
  generalize (Z_div_mod_eq_full x B),
             (Z_div_mod_eq_full q0 B),
             (Z_div_mod_eq_full q1 B).
  fold q0 q1 q2.
  intros H0 H1 H2.
  rewrite H2 in H1.
  rewrite H1 in H0.
  lia.
Qed.

(** The [limb] extraction is a left inverse of [eval4]: given 4 digits
    already in [[0, B)), extracting the digits of their evaluation
    returns the original digits. *)
Lemma limbs_eval4 : forall B a0 a1 a2 a3,
  B > 1 ->
  0 <= a0 < B -> 0 <= a1 < B -> 0 <= a2 < B -> 0 <= a3 < B ->
  limb B (eval4 B a0 a1 a2 a3) 0 = a0 /\
  limb B (eval4 B a0 a1 a2 a3) 1 = a1 /\
  limb B (eval4 B a0 a1 a2 a3) 2 = a2 /\
  limb B (eval4 B a0 a1 a2 a3) 3 = a3.
Proof.
  intros B a0 a1 a2 a3 HB H0 H1 H2 H3.
  unfold eval4, limb.
  simpl (Z.of_nat _).

  repeat split.
  - (* conjunct 0: (sum / B^0) mod B = a0 *)
    rewrite Z.pow_0_r, Z.div_1_r.
    replace (a0 + a1 * B + a2 * B ^ 2 + a3 * B ^ 3)
      with (a0 + (a1 + a2 * B + a3 * B ^ 2) * B) by ring.
    rewrite Z_mod_plus_full.
    apply Zmod_small; lia.

  - (* conjunct 1: (sum / B^1) mod B = a1 *)
    rewrite Z.pow_1_r.
    replace (a0 + a1 * B + a2 * B ^ 2 + a3 * B ^ 3)
      with ((a1 + (a2 + a3 * B) * B) * B + a0) by ring.
    replace (((a1 + (a2 + a3 * B) * B) * B + a0) / B)
      with (a1 + (a2 + a3 * B) * B) by
      (apply Z.div_unique with (r := a0); lia).
    rewrite Z_mod_plus_full.
    apply Zmod_small; lia.

  - (* conjunct 2: (sum / B^2) mod B = a2 *)
    replace (a0 + a1 * B + a2 * B ^ 2 + a3 * B ^ 3)
      with ((a2 + a3 * B) * B ^ 2 + (a0 + a1 * B)) by ring.
    replace (((a2 + a3 * B) * B ^ 2 + (a0 + a1 * B)) / B ^ 2)
      with (a2 + a3 * B) by
      (apply Z.div_unique with (r := a0 + a1 * B); nia).
    rewrite Z_mod_plus_full.
    apply Zmod_small; lia.

  - (* conjunct 3: (sum / B^3) mod B = a3 *)
    replace (a0 + a1 * B + a2 * B ^ 2 + a3 * B ^ 3)
      with (a3 * B ^ 3 + (a0 + a1 * B + a2 * B ^ 2)) by ring.
    replace ((a3 * B ^ 3 + (a0 + a1 * B + a2 * B ^ 2)) / B ^ 3)
      with a3 by
      (apply Z.div_unique with (r := a0 + a1 * B + a2 * B ^ 2); nia).
    apply Zmod_small; lia.
Qed.

(** A value in [[0, B^8)] equals its 8-limb little-endian reconstruction.

    Same strategy as [eval4_limbs] with 7 quotients. *)
Lemma eval8_limbs : forall B x,
  B > 1 -> 0 <= x < B^8 ->
  eval8 B (limb B x 0) (limb B x 1) (limb B x 2) (limb B x 3)
          (limb B x 4) (limb B x 5) (limb B x 6) (limb B x 7) = x.
Proof.
  intros B x HB Hx.
  unfold limb, eval8.
  simpl (Z.of_nat _).
  rewrite Z.pow_0_r, Z.pow_1_r, Z.div_1_r.

  expand_pow B.

  (* Name successive quotients q_k = q_{k-1} / B *)
  set (q0 := x / B).
  set (q1 := q0 / B).
  set (q2 := q1 / B).
  set (q3 := q2 / B).
  set (q4 := q3 / B).
  set (q5 := q4 / B).
  set (q6 := q5 / B).

  (* Align compound divisions x/(B*...*B) with iterated q_k via Z.div_div *)
  replace (x / (B * B)) with q1 by
    (unfold q1, q0; rewrite <- Z.div_div by lia; reflexivity).
  replace (x / (B * B * B)) with q2 by
    (unfold q2, q1, q0; do 2 rewrite <- Z.div_div by lia; reflexivity).
  replace (x / (B * B * B * B)) with q3 by
    (unfold q3, q2, q1, q0; do 3 rewrite <- Z.div_div by lia; reflexivity).
  replace (x / (B * B * B * B * B)) with q4 by
    (unfold q4, q3, q2, q1, q0; do 4 rewrite <- Z.div_div by lia; reflexivity).
  replace (x / (B * B * B * B * B * B)) with q5 by
    (unfold q5, q4, q3, q2, q1, q0; do 5 rewrite <- Z.div_div by lia; reflexivity).
  replace (x / (B * B * B * B * B * B * B)) with q6 by
    (unfold q6, q5, q4, q3, q2, q1, q0; do 6 rewrite <- Z.div_div by lia; reflexivity).

  (* Top digit fits in one limb *)
  assert (Hq6 : 0 <= q6 < B).
  { unfold q6, q5, q4, q3, q2, q1, q0.
    split.
    - repeat (apply Z.div_pos; [|lia]); lia.
    - do 7 (apply Z.div_lt_upper_bound; [lia|]).
      replace (B * (B * (B * (B * (B * (B * (B * B))))))) with (B ^ 8) by ring.
      lia. }
  rewrite (Zmod_small q6 B Hq6).

  (* Telescope: substitute div/mod identities from top down *)
  generalize (Z_div_mod_eq_full x B),
             (Z_div_mod_eq_full q0 B),
             (Z_div_mod_eq_full q1 B),
             (Z_div_mod_eq_full q2 B),
             (Z_div_mod_eq_full q3 B),
             (Z_div_mod_eq_full q4 B),
             (Z_div_mod_eq_full q5 B).
  fold q0 q1 q2 q3 q4 q5 q6.
  intros H0 H1 H2 H3 H4 H5 H6.
  rewrite H6 in H5.
  rewrite H5 in H4.
  rewrite H4 in H3.
  rewrite H3 in H2.
  rewrite H2 in H1.
  rewrite H1 in H0.
  lia.
Qed.

(*
(** The [limb] extraction is a left inverse of [eval8]: given 8 digits
    already in [[0, B)), extracting the digits of their evaluation
    returns the original digits. *)
Lemma limbs_eval8 : forall B r0 r1 r2 r3 r4 r5 r6 r7,
  B > 1 ->
  0 <= r0 < B -> 0 <= r1 < B -> 0 <= r2 < B -> 0 <= r3 < B ->
  0 <= r4 < B -> 0 <= r5 < B -> 0 <= r6 < B -> 0 <= r7 < B ->
  limb B (eval8 B r0 r1 r2 r3 r4 r5 r6 r7) 0 = r0 /\
  limb B (eval8 B r0 r1 r2 r3 r4 r5 r6 r7) 1 = r1 /\
  limb B (eval8 B r0 r1 r2 r3 r4 r5 r6 r7) 2 = r2 /\
  limb B (eval8 B r0 r1 r2 r3 r4 r5 r6 r7) 3 = r3 /\
  limb B (eval8 B r0 r1 r2 r3 r4 r5 r6 r7) 4 = r4 /\
  limb B (eval8 B r0 r1 r2 r3 r4 r5 r6 r7) 5 = r5 /\
  limb B (eval8 B r0 r1 r2 r3 r4 r5 r6 r7) 6 = r6 /\
  limb B (eval8 B r0 r1 r2 r3 r4 r5 r6 r7) 7 = r7.
*)

(* ================================================================= *)
(** ** Congruence lemmas *)
(* ================================================================= *)

Lemma eval4_congr : forall B a0 a1 a2 a3 b0 b1 b2 b3,
  a0 = b0 -> a1 = b1 -> a2 = b2 -> a3 = b3 ->
  eval4 B a0 a1 a2 a3 = eval4 B b0 b1 b2 b3.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma eval8_congr : forall B r0 r1 r2 r3 r4 r5 r6 r7
                              s0 s1 s2 s3 s4 s5 s6 s7,
  r0 = s0 -> r1 = s1 -> r2 = s2 -> r3 = s3 ->
  r4 = s4 -> r5 = s5 -> r6 = s6 -> r7 = s7 ->
  eval8 B r0 r1 r2 r3 r4 r5 r6 r7 = eval8 B s0 s1 s2 s3 s4 s5 s6 s7.
Proof.
  intros. subst. reflexivity.
Qed.

(* ================================================================= *)
(** ** Auxiliary lemmas *)
(* ================================================================= *)

(** A 2-limb little-endian value fits in [[0, B^2)]. *)
Lemma eval2_bound : forall B a0 a1,
  B > 1 ->
  0 <= a0 < B -> 0 <= a1 < B ->
  0 <= eval2 B a0 a1 < B * B.
Proof.
  intros B a0 a1 HB H0 H1.
  unfold eval2.
  assert (0 <= a1 * B) by (apply Z.mul_nonneg_nonneg; lia).
  assert (a1 * B <= (B - 1) * B) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert ((B - 1) + (B - 1) * B = B * B - 1) by ring.
  lia.
Qed.

(** The product of two 2-limb numbers fits in 4 limbs. *)
Lemma eval2_mul_range : forall B a0 a1 b0 b1,
  B > 1 ->
  0 <= a0 < B -> 0 <= a1 < B ->
  0 <= b0 < B -> 0 <= b1 < B ->
  0 <= eval2 B a0 a1 * eval2 B b0 b1 < B ^ 4.
Proof.
  intros.
  pose proof (eval2_bound B a0 a1 ltac:(lia) ltac:(lia) ltac:(lia)) as Ha.
  pose proof (eval2_bound B b0 b1 ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  replace (B ^ 4) with (B * B * (B * B)) by ring.
  split.
  - lia.
  - apply Z.mul_lt_mono_nonneg; lia.
Qed.

(** A 4-limb little-endian value fits in [[0, B^4)]. *)
Lemma eval4_bound : forall B a0 a1 a2 a3,
  B > 1 ->
  0 <= a0 < B -> 0 <= a1 < B -> 0 <= a2 < B -> 0 <= a3 < B ->
  0 <= a0 + a1 * B + a2 * (B * B) + a3 * (B * B * B) < B * B * B * B.
Proof.
  intros B a0 a1 a2 a3 HB H0 H1 H2 H3.

  (* Non-negativity of each limb * power *)
  assert (0 <= a1 * B) by (apply Z.mul_nonneg_nonneg; lia).
  assert (0 <= a2 * (B * B))
    by (apply Z.mul_nonneg_nonneg; [lia|apply Z.mul_nonneg_nonneg; lia]).
  assert (0 <= a3 * (B * B * B))
    by (apply Z.mul_nonneg_nonneg;
        [lia|apply Z.mul_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; lia|lia]]).

  (* Upper bound: each a_i <= B-1, so sum <= (B-1)*(1+B+B^2+B^3) = B^4-1 *)
  assert (a1 * B <= (B - 1) * B) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (a2 * (B * B) <= (B - 1) * (B * B))
    by (apply Z.mul_le_mono_nonneg_r; [apply Z.mul_nonneg_nonneg; lia|lia]).
  assert (a3 * (B * B * B) <= (B - 1) * (B * B * B))
    by (apply Z.mul_le_mono_nonneg_r;
        [apply Z.mul_nonneg_nonneg; [apply Z.mul_nonneg_nonneg; lia|lia]|lia]).
  assert ((B - 1) + (B - 1) * B + (B - 1) * (B * B) + (B - 1) * (B * B * B)
          = B * B * B * B - 1) by ring.

  lia.
Qed.

(** The product of two 4-limb numbers fits in 8 limbs. *)
Lemma eval4_mul_range : forall B a0 a1 a2 a3 b0 b1 b2 b3,
  B > 1 ->
  0 <= a0 < B -> 0 <= a1 < B -> 0 <= a2 < B -> 0 <= a3 < B ->
  0 <= b0 < B -> 0 <= b1 < B -> 0 <= b2 < B -> 0 <= b3 < B ->
  0 <= eval4 B a0 a1 a2 a3 * eval4 B b0 b1 b2 b3 < B^8.
Proof.
  intros.
  pose proof (eval4_bound B a0 a1 a2 a3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Ha.
  pose proof (eval4_bound B b0 b1 b2 b3
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hb.
  unfold eval4.
  replace (B ^ 2) with (B * B) by ring.
  replace (B ^ 3) with (B * B * B) by ring.
  replace (B ^ 8) with (B * B * B * B * (B * B * B * B)) by ring.
  split.
  - lia.
  - apply Z.mul_lt_mono_nonneg; lia.
Qed.

(** Uniqueness of a single base-[B] digit: if [a + b*B = c + d*B]
    with [0 <= a, c < B], then [a = c] and [b = d]. *)
Lemma base_rep_unique_step : forall B a b c d,
  B > 0 ->
  0 <= a < B -> 0 <= c < B ->
  a + b * B = c + d * B ->
  a = c /\ b = d.
Proof.
  intros B a b c d HB Ha Hc Heq.
  (* Extract the low digit via mod *)
  assert (Ha_mod : (a + b * B) mod B = a)
    by (rewrite Z_mod_plus_full; apply Zmod_small; lia).
  assert (Hc_mod : (c + d * B) mod B = c)
    by (rewrite Z_mod_plus_full; apply Zmod_small; lia).
  rewrite Heq in Ha_mod.
  rewrite Hc_mod in Ha_mod.
  split.
  - lia.
  - assert (Hbd : b * B = d * B) by lia.
    apply Z.mul_cancel_r in Hbd; lia.
Qed.

(** If three limbs of a 4-limb number are known to lie in [[0, B)) and
    the value lies in [[0, B^4)), then the fourth (most significant) limb
    also lies in [[0, B)).

    This is the key bound used to promote [carry2] from [0 <= carry2]
    (which follows from non-negativity of the accumulators) to
    [carry2 < B] in [schoolbook_mul_2x2]. *)
Lemma eval4_last_limb_bound : forall B r0 r1 r2 r3,
  B > 1 ->
  0 <= r0 < B -> 0 <= r1 < B -> 0 <= r2 < B ->
  0 <= r3 ->
  eval4 B r0 r1 r2 r3 < B ^ 4 ->
  r3 < B.
Proof.
  intros B r0 r1 r2 r3 HB Hr0 Hr1 Hr2 Hr3_nn Heval.
  unfold eval4 in Heval.
  replace (B ^ 4) with (B ^ 3 * B) in Heval by ring.
  assert (r3 * B ^ 3 < B ^ 3 * B) by nia.
  assert (0 < B ^ 3) by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.

(** If seven limbs of an 8-limb number are known to lie in [[0, B)) and
    the value lies in [[0, B^8)), then the eighth (most significant) limb
    also lies in [[0, B)).

    This is the key bound used to promote [carry6] from [0 <= carry6]
    (which follows from non-negativity of the accumulators) to
    [carry6 < B] in [schoolbook_mul_4x4]. *)
Lemma eval8_last_limb_bound : forall B r0 r1 r2 r3 r4 r5 r6 r7,
  B > 1 ->
  0 <= r0 < B -> 0 <= r1 < B -> 0 <= r2 < B -> 0 <= r3 < B ->
  0 <= r4 < B -> 0 <= r5 < B -> 0 <= r6 < B ->
  0 <= r7 ->
  eval8 B r0 r1 r2 r3 r4 r5 r6 r7 < B ^ 8 ->
  r7 < B.
Proof.
  intros B r0 r1 r2 r3 r4 r5 r6 r7 HB
         Hr0 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7 Hlt.
  unfold eval8 in Hlt.
  assert (0 < B ^ 7) by (apply Z.pow_pos_nonneg; lia).
  assert (r7 * B ^ 7 < B ^ 8) by nia.
  replace (B ^ 8) with (B * B ^ 7) in * by ring.
  apply Z.mul_lt_mono_pos_r with (p := B ^ 7); lia.
Qed.

(* ================================================================= *)
(** ** Injectivity lemmas *)
(* ================================================================= *)

(** [eval4] is injective on digits in [[0, B)): if two 4-limb
    representations evaluate to the same integer, their digits
    are equal pairwise. *)
Lemma eval4_injective : forall B a0 a1 a2 a3 b0 b1 b2 b3,
  B > 1 ->
  0 <= a0 < B -> 0 <= a1 < B -> 0 <= a2 < B -> 0 <= a3 < B ->
  0 <= b0 < B -> 0 <= b1 < B -> 0 <= b2 < B -> 0 <= b3 < B ->
  eval4 B a0 a1 a2 a3 = eval4 B b0 b1 b2 b3 ->
  a0 = b0 /\ a1 = b1 /\ a2 = b2 /\ a3 = b3.
Proof.
  intros B a0 a1 a2 a3 b0 b1 b2 b3 HB
         Ha0 Ha1 Ha2 Ha3 Hb0 Hb1 Hb2 Hb3 H8.
  unfold eval4 in H8.

  (* Digit 0: regroup both sides as [a0 + (rest_a) * B] so that
     [base_rep_unique_step] can peel off the least-significant digit. *)
  replace (a0 + a1 * B + a2 * B ^ 2 + a3 * B ^ 3)
    with (a0 + (a1 + a2 * B + a3 * B ^ 2) * B) in H8 by ring.
  replace (b0 + b1 * B + b2 * B ^ 2 + b3 * B ^ 3)
    with (b0 + (b1 + b2 * B + b3 * B ^ 2) * B) in H8 by ring.
  apply base_rep_unique_step in H8 as [E0 H8]; [| lia| lia | lia].

  (* Digit 1: same regrouping on the remaining equality. *)
  replace (a1 + a2 * B + a3 * B ^ 2)
    with (a1 + (a2 + a3 * B) * B) in H8 by ring.
  replace (b1 + b2 * B + b3 * B ^ 2)
    with (b1 + (b2 + b3 * B) * B) in H8 by ring.
  apply base_rep_unique_step in H8 as [E1 H8]; [| lia| lia | lia].

  (* Digits 2 and 3: already in [a2 + a3*B] form; one more peel gives both. *)
  apply base_rep_unique_step in H8 as [E2 E3]; [| lia| lia | lia].
  exact (conj E0 (conj E1 (conj E2 E3))).
Qed.

(** [eval8] is injective on digits in [[0, B)): if two 8-limb
    representations evaluate to the same integer, their digits
    are equal pairwise. *)
Lemma eval8_injective : forall B r0 r1 r2 r3 r4 r5 r6 r7
                                  s0 s1 s2 s3 s4 s5 s6 s7,
  B > 1 ->
  0 <= r0 < B -> 0 <= r1 < B -> 0 <= r2 < B -> 0 <= r3 < B ->
  0 <= r4 < B -> 0 <= r5 < B -> 0 <= r6 < B -> 0 <= r7 < B ->
  0 <= s0 < B -> 0 <= s1 < B -> 0 <= s2 < B -> 0 <= s3 < B ->
  0 <= s4 < B -> 0 <= s5 < B -> 0 <= s6 < B -> 0 <= s7 < B ->
  eval8 B r0 r1 r2 r3 r4 r5 r6 r7 = eval8 B s0 s1 s2 s3 s4 s5 s6 s7 ->
  r0 = s0 /\ r1 = s1 /\ r2 = s2 /\ r3 = s3 /\
  r4 = s4 /\ r5 = s5 /\ r6 = s6 /\ r7 = s7.
Proof.
  intros B r0 r1 r2 r3 r4 r5 r6 r7
         s0 s1 s2 s3 s4 s5 s6 s7 HB
         Hr0 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7
         Hs0 Hs1 Hs2 Hs3 Hs4 Hs5 Hs6 Hs7 H8.
  unfold eval8 in H8.

  (* Digit 0: regroup both sides as [r0 + (rest_r) * B] and peel. *)
  replace (r0 + r1*B + r2*B^2 + r3*B^3 + r4*B^4 + r5*B^5 + r6*B^6 + r7*B^7)
    with (r0 + (r1 + r2*B + r3*B^2 + r4*B^3 + r5*B^4 + r6*B^5 + r7*B^6) * B) in H8 by ring.
  replace (s0 + s1*B + s2*B^2 + s3*B^3 + s4*B^4 + s5*B^5 + s6*B^6 + s7*B^7)
    with (s0 + (s1 + s2*B + s3*B^2 + s4*B^3 + s5*B^4 + s6*B^5 + s7*B^6) * B) in H8 by ring.
  apply base_rep_unique_step in H8 as [E0 H8]; [| lia | lia | lia].

  (* Digit 1: regroup and peel. *)
  replace (r1 + r2*B + r3*B^2 + r4*B^3 + r5*B^4 + r6*B^5 + r7*B^6)
    with (r1 + (r2 + r3*B + r4*B^2 + r5*B^3 + r6*B^4 + r7*B^5) * B) in H8 by ring.
  replace (s1 + s2*B + s3*B^2 + s4*B^3 + s5*B^4 + s6*B^5 + s7*B^6)
    with (s1 + (s2 + s3*B + s4*B^2 + s5*B^3 + s6*B^4 + s7*B^5) * B) in H8 by ring.
  apply base_rep_unique_step in H8 as [E1 H8]; [| lia | lia | lia].

  (* Digit 2: regroup and peel. *)
  replace (r2 + r3*B + r4*B^2 + r5*B^3 + r6*B^4 + r7*B^5)
    with (r2 + (r3 + r4*B + r5*B^2 + r6*B^3 + r7*B^4) * B) in H8 by ring.
  replace (s2 + s3*B + s4*B^2 + s5*B^3 + s6*B^4 + s7*B^5)
    with (s2 + (s3 + s4*B + s5*B^2 + s6*B^3 + s7*B^4) * B) in H8 by ring.
  apply base_rep_unique_step in H8 as [E2 H8]; [| lia | lia | lia].

  (* Digit 3: regroup and peel. *)
  replace (r3 + r4*B + r5*B^2 + r6*B^3 + r7*B^4)
    with (r3 + (r4 + r5*B + r6*B^2 + r7*B^3) * B) in H8 by ring.
  replace (s3 + s4*B + s5*B^2 + s6*B^3 + s7*B^4)
    with (s3 + (s4 + s5*B + s6*B^2 + s7*B^3) * B) in H8 by ring.
  apply base_rep_unique_step in H8 as [E3 H8]; [| lia | lia | lia].

  (* Digit 4: regroup and peel. *)
  replace (r4 + r5*B + r6*B^2 + r7*B^3)
    with (r4 + (r5 + r6*B + r7*B^2) * B) in H8 by ring.
  replace (s4 + s5*B + s6*B^2 + s7*B^3)
    with (s4 + (s5 + s6*B + s7*B^2) * B) in H8 by ring.
  apply base_rep_unique_step in H8 as [E4 H8]; [| lia | lia | lia].

  (* Digit 5: regroup and peel. *)
  replace (r5 + r6*B + r7*B^2)
    with (r5 + (r6 + r7*B) * B) in H8 by ring.
  replace (s5 + s6*B + s7*B^2)
    with (s5 + (s6 + s7*B) * B) in H8 by ring.
  apply base_rep_unique_step in H8 as [E5 H8]; [| lia | lia | lia].

  (* Digits 6 and 7: already in [r6 + r7*B] form; one more peel gives both. *)
  apply base_rep_unique_step in H8 as [E6 E7]; [| lia | lia | lia].
  exact (conj E0 (conj E1 (conj E2 (conj E3 (conj E4 (conj E5 (conj E6 E7))))))).
Qed.


(* ================================================================= *)
(** ** Auxiliary lemmas *)
(* ================================================================= *)

(** If a 4-limb representation with all digits in [[0, B)] equals [x],
    then each digit is [(x / B^k) mod B].

    Derived from [eval4_injective] and [eval4_limbs]. *)
Lemma eval4_digit_unique : forall B r0 r1 r2 r3,
  B > 1 ->
  0 <= r0 < B -> 0 <= r1 < B -> 0 <= r2 < B -> 0 <= r3 < B ->
  let x := eval4 B r0 r1 r2 r3 in
  r0 = x mod B /\
  r1 = (x / B) mod B /\
  r2 = (x / B^2) mod B /\
  r3 = (x / B^3) mod B.
Proof.
  intros B r0 r1 r2 r3 HB Hr0 Hr1 Hr2 Hr3 x.

  assert (Hx : 0 <= x < B ^ 4) by (unfold x, eval4; nia).

  pose proof (eval4_limbs B x HB Hx) as Hcanon.
  assert (Hlimb : forall i, 0 <= limb B x i < B)
    by (intro; unfold limb; apply Z.mod_pos_bound; lia).

  symmetry in Hcanon.
  apply (eval4_injective B _ _ _ _
    (limb B x 0) (limb B x 1) (limb B x 2) (limb B x 3)
    HB Hr0 Hr1 Hr2 Hr3) in Hcanon;
    try apply Hlimb.

  unfold limb in Hcanon.
  simpl Z.of_nat in Hcanon.
  rewrite ?Z.pow_0_r, ?Z.div_1_r, ?Z.pow_1_r in Hcanon.
  exact Hcanon.
Qed.

(** If an 8-limb representation with all digits in [[0, B)] equals [x],
    then each digit is [(x / B^k) mod B].

    Derived from [eval8_injective] and [eval8_limbs]. *)
Lemma eval8_digit_unique : forall B r0 r1 r2 r3 r4 r5 r6 r7,
  B > 1 ->
  0 <= r0 < B -> 0 <= r1 < B -> 0 <= r2 < B -> 0 <= r3 < B ->
  0 <= r4 < B -> 0 <= r5 < B -> 0 <= r6 < B -> 0 <= r7 < B ->
  let x := eval8 B r0 r1 r2 r3 r4 r5 r6 r7 in
  r0 = x mod B /\
  r1 = (x / B) mod B /\
  r2 = (x / B^2) mod B /\
  r3 = (x / B^3) mod B /\
  r4 = (x / B^4) mod B /\
  r5 = (x / B^5) mod B /\
  r6 = (x / B^6) mod B /\
  r7 = (x / B^7) mod B.
Proof.
  intros B r0 r1 r2 r3 r4 r5 r6 r7 HB
         Hr0 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7 x.

  assert (Hx : 0 <= x < B ^ 8) by (unfold x, eval8; nia).

  (* Reconstruct x from its canonical limbs *)
  pose proof (eval8_limbs B x HB Hx) as Hcanon.
  assert (Hlimb : forall i, 0 <= limb B x i < B)
    by (intro; unfold limb; apply Z.mod_pos_bound; lia).

  (* eval8 B (limb ..) = x = eval8 B r0..r7, so digits match *)
  symmetry in Hcanon.
  apply (eval8_injective B _ _ _ _ _ _ _ _
    (limb B x 0) (limb B x 1) (limb B x 2) (limb B x 3)
    (limb B x 4) (limb B x 5) (limb B x 6) (limb B x 7)
    HB Hr0 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7) in Hcanon;
    try apply Hlimb.

  (* Unfold limb to div/mod form *)
  unfold limb in Hcanon.
  simpl Z.of_nat in Hcanon.
  rewrite ?Z.pow_0_r, ?Z.div_1_r, ?Z.pow_1_r in Hcanon.
  exact Hcanon.
Qed.

(* ================================================================= *)
(** ** Modular / division bridging lemmas *)
(* ================================================================= *)

(** Adding [y mod B] and [z mod B] instead of [y] and [z] does not
    change the result modulo [B]. *)
Lemma Zmod_add_mod_idemp : forall B x y z,
  B > 0 ->
  (x + y mod B + z mod B) mod B = (x + y + z) mod B.
Proof.
  intros B x y z HB.
  rewrite (Z_div_mod_eq_full y B) at 2.
  rewrite (Z_div_mod_eq_full z B) at 2.
  replace (x + (B * (y / B) + y mod B) + (B * (z / B) + z mod B))
    with (x + y mod B + z mod B + (y / B + z / B) * B) by ring.
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.

(** Splitting a sum of three cross-products: dividing [x + y + z] by [B]
    equals the sum of high parts [y / B + z / B] plus the carry from the
    mid-level accumulation [(x + y mod B + z mod B) / B]. *)
Lemma Zdiv_cross_product_split : forall B x y z,
  B > 0 ->
  (x + y + z) / B = y / B + z / B + (x + y mod B + z mod B) / B.
Proof.
  intros B x y z HB.
  rewrite (Z_div_mod_eq_full y B) at 1.
  rewrite (Z_div_mod_eq_full z B) at 1.
  replace (x + (B * (y / B) + y mod B) + (B * (z / B) + z mod B))
    with ((y / B + z / B) * B + (x + y mod B + z mod B)) by ring.
  rewrite Z.div_add_l by lia.
  lia.
Qed.

(** Two-digit reconstruction: the low two base-[B] digits of [x]
    reassemble to [x mod (B * B)]. *)
Lemma eval2_mod_mul : forall B x,
  B > 0 ->
  x mod B + (x / B) mod B * B = x mod (B * B).
Proof.
  intros B x HB.
  pose proof (Z_div_mod_eq_full x B).
  pose proof (Z_div_mod_eq_full (x / B) B).
  pose proof (Z.mod_pos_bound x B ltac:(lia)).
  pose proof (Z.mod_pos_bound (x / B) B ltac:(lia)).
  symmetry.
  replace x
    with ((x mod B + (x / B) mod B * B) + (x / B / B) * (B * B)) at 1 by nia.
  rewrite Z_mod_plus_full.
  apply Zmod_small. nia.
Qed.

(* ================================================================= *)
(** ** Schoolbook 2x2 multiplication correctness *)
(* ================================================================= *)

(** Given base [B > 1] and input limbs [a0, a1], [b0, b1] in [[0, B)],
    the accumulate-and-carry algorithm produces output limbs [r0..r3]
    that are the base-[B] digits of
    [eval2 B a0 a1 * eval2 B b0 b1].

    At each round [k] (for [k = 0 .. 2]):
    - accumulate all cross-products [ai * bj] with [i + j = k]
      into the carry from the previous round;
    - extract the low limb [rk := acc mod B];
    - propagate the carry [carry := acc / B].

    The proof proceeds in three steps:
    1. Telescope the carry chain to show
       [eval4 B r0..r2 carry2 = product].
    2. Bound [carry2 < B] using [product < B^4].
    3. Apply [eval4_digit_unique] to extract all 4 digit equalities. *)
Theorem schoolbook_mul_2x2 :
  forall (B : Z),
  B > 1 ->
  forall (a0 a1 b0 b1 : Z),
  0 <= a0 < B -> 0 <= a1 < B ->
  0 <= b0 < B -> 0 <= b1 < B ->
  forall (acc0 : Z), acc0 = a0 * b0 ->
  forall (carry0 : Z), carry0 = acc0 / B ->
  forall (acc1 : Z), acc1 = carry0 + a0 * b1 + a1 * b0 ->
  forall (carry1 : Z), carry1 = acc1 / B ->
  forall (acc2 : Z), acc2 = carry1 + a1 * b1 ->
  forall (carry2 : Z), carry2 = acc2 / B ->
  let r0 := acc0 mod B in
  let r1 := acc1 mod B in
  let r2 := acc2 mod B in
  let r3 := carry2 mod B in
  let product := eval2 B a0 a1 * eval2 B b0 b1 in
  r0 = product mod B /\
  r1 = (product / B) mod B /\
  r2 = (product / B^2) mod B /\
  r3 = (product / B^3) mod B.
Proof.
  intros B HB a0 a1 b0 b1
         Ha0 Ha1 Hb0 Hb1
         acc0 Hacc0 carry0 Hcarry0
         acc1 Hacc1 carry1 Hcarry1
         acc2 Hacc2 carry2 Hcarry2
         r0 r1 r2 r3 product.

  (* Step 1: Telescope the carry chain.
     Expand [product] via [eval2], introduce div-mod decompositions,
     substitute all carries and output limbs, then [nia] verifies
     the telescoping cancellation. *)
  assert (Hprod_expand : product =
    a0*b0 + (a0*b1 + a1*b0)*B + a1*b1*B^2)
    by (unfold product, eval2; ring).

  pose proof (Z_div_mod_eq_full acc0 B) as DM0.
  pose proof (Z_div_mod_eq_full acc1 B) as DM1.
  pose proof (Z_div_mod_eq_full acc2 B) as DM2.
  subst carry0 carry1 carry2.
  subst r0 r1 r2 r3.
  assert (Heval : eval4 B (acc0 mod B) (acc1 mod B) (acc2 mod B) (acc2 / B) = product).
  { unfold eval4.
    subst acc0 acc1 acc2.
    nia. }

  clear Hprod_expand DM0 DM1 DM2.

  (* Step 2: Bound [carry2 = acc2 / B].
     Non-negativity follows from the accumulators being non-negative.
     Upper bound: delegate to [eval4_last_limb_bound] using [Heval]
     and [eval2_mul_range]. *)
  assert (Hprod_range : 0 <= product < B ^ 4)
    by (subst product; apply eval2_mul_range; assumption).
  assert (Hcarry2_nn : 0 <= acc2 / B).
  { assert (0 <= acc0) by (subst acc0; nia).
    assert (0 <= acc0 / B) by (apply Z.div_pos; lia).
    assert (0 <= acc1) by (subst acc1; lia).
    assert (0 <= acc1 / B) by (apply Z.div_pos; lia).
    assert (0 <= acc2) by (subst acc2; lia).
    apply Z.div_pos; lia. }
  assert (Hcarry2_bound : 0 <= acc2 / B < B).
  { split.
    - exact Hcarry2_nn.
    - apply eval4_last_limb_bound with
        (r0 := acc0 mod B) (r1 := acc1 mod B) (r2 := acc2 mod B);
        try (apply Z.mod_pos_bound; lia);
        try assumption.
      rewrite Heval.
      exact (proj2 Hprod_range). }
  clear Hprod_range Hacc0 Hacc1 Hacc2
        Ha0 Ha1 Hb0 Hb1 Hcarry2_nn.

  (* Step 3: Apply [eval4_digit_unique] and conclude.
     All output limbs lie in [[0, B)] since they are [mod B] results.
     We obtain digit equalities, rewrite [eval4 ...] to [product],
     simplify [(acc2 / B) mod B] to [acc2 / B], and finish. *)
  assert (Hr0 : 0 <= acc0 mod B < B) by (apply Z.mod_pos_bound; lia).
  assert (Hr1 : 0 <= acc1 mod B < B) by (apply Z.mod_pos_bound; lia).
  assert (Hr2 : 0 <= acc2 mod B < B) by (apply Z.mod_pos_bound; lia).
  pose proof (eval4_digit_unique B
    (acc0 mod B) (acc1 mod B) (acc2 mod B) (acc2 / B)
    HB Hr0 Hr1 Hr2 Hcarry2_bound) as Hdigits.
  rewrite Heval in Hdigits.
  cbv zeta in Hdigits.
  rewrite (Zmod_small (acc2 / B) B Hcarry2_bound).
  exact Hdigits.
Qed.

(* ================================================================= *)
(** ** Schoolbook 4x4 multiplication correctness *)
(* ================================================================= *)

(** Given base [B > 1] and input limbs [a0..a3], [b0..b3] in [[0, B)],
    the accumulate-and-carry algorithm produces output limbs [r0..r7]
    that are the base-[B] digits of
    [eval4 B a0 a1 a2 a3 * eval4 B b0 b1 b2 b3].

    At each round [k] (for [k = 0 .. 6]):
    - accumulate all cross-products [ai * bj] with [i + j = k]
      into the carry from the previous round;
    - extract the low limb [rk := acc mod B];
    - propagate the carry [carry := acc / B].

    The proof proceeds in three steps:
    1. Telescope the carry chain to show
       [eval8 B r0..r6 carry6 = product].
    2. Bound [carry6 < B] using [product < B^8].
    3. Apply [eval8_digit_unique] to extract all 8 digit equalities. *)
Theorem schoolbook_mul_4x4 :
  forall (B : Z),
  B > 1 ->
  forall (a0 a1 a2 a3 b0 b1 b2 b3 : Z),
  0 <= a0 < B -> 0 <= a1 < B -> 0 <= a2 < B -> 0 <= a3 < B ->
  0 <= b0 < B -> 0 <= b1 < B -> 0 <= b2 < B -> 0 <= b3 < B ->
  forall (acc0 : Z), acc0 = a0 * b0 ->
  forall (carry0 : Z), carry0 = acc0 / B ->
  forall (acc1 : Z), acc1 = carry0 + a0 * b1 + a1 * b0 ->
  forall (carry1 : Z), carry1 = acc1 / B ->
  forall (acc2 : Z), acc2 = carry1 + a0 * b2 + a1 * b1 + a2 * b0 ->
  forall (carry2 : Z), carry2 = acc2 / B ->
  forall (acc3 : Z), acc3 = carry2 + a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 ->
  forall (carry3 : Z), carry3 = acc3 / B ->
  forall (acc4 : Z), acc4 = carry3 + a1 * b3 + a2 * b2 + a3 * b1 ->
  forall (carry4 : Z), carry4 = acc4 / B ->
  forall (acc5 : Z), acc5 = carry4 + a2 * b3 + a3 * b2 ->
  forall (carry5 : Z), carry5 = acc5 / B ->
  forall (acc6 : Z), acc6 = carry5 + a3 * b3 ->
  forall (carry6 : Z), carry6 = acc6 / B ->
  let r0 := acc0 mod B in
  let r1 := acc1 mod B in
  let r2 := acc2 mod B in
  let r3 := acc3 mod B in
  let r4 := acc4 mod B in
  let r5 := acc5 mod B in
  let r6 := acc6 mod B in
  let r7 := carry6 mod B in
  let product := eval4 B a0 a1 a2 a3 * eval4 B b0 b1 b2 b3 in
  r0 = product mod B /\
  r1 = (product / B) mod B /\
  r2 = (product / B^2) mod B /\
  r3 = (product / B^3) mod B /\
  r4 = (product / B^4) mod B /\
  r5 = (product / B^5) mod B /\
  r6 = (product / B^6) mod B /\
  r7 = (product / B^7) mod B.
Proof.
  intros B HB a0 a1 a2 a3 b0 b1 b2 b3
         Ha0 Ha1 Ha2 Ha3 Hb0 Hb1 Hb2 Hb3
         acc0 Hacc0 carry0 Hcarry0
         acc1 Hacc1 carry1 Hcarry1
         acc2 Hacc2 carry2 Hcarry2
         acc3 Hacc3 carry3 Hcarry3
         acc4 Hacc4 carry4 Hcarry4
         acc5 Hacc5 carry5 Hcarry5
         acc6 Hacc6 carry6 Hcarry6
         r0 r1 r2 r3 r4 r5 r6 r7 product.

  (* Step 1: Telescope the carry chain.
     Expand [product] via [eval4], introduce div-mod decompositions,
     substitute all carries and output limbs, then [nia] verifies
     the telescoping cancellation. *)
  assert (Hprod_expand : product =
    a0*b0 + (a0*b1 + a1*b0)*B + (a0*b2 + a1*b1 + a2*b0)*B^2 +
    (a0*b3 + a1*b2 + a2*b1 + a3*b0)*B^3 +
    (a1*b3 + a2*b2 + a3*b1)*B^4 + (a2*b3 + a3*b2)*B^5 + a3*b3*B^6)
    by (unfold product, eval4; ring).

  pose proof (Z_div_mod_eq_full acc0 B) as DM0.
  pose proof (Z_div_mod_eq_full acc1 B) as DM1.
  pose proof (Z_div_mod_eq_full acc2 B) as DM2.
  pose proof (Z_div_mod_eq_full acc3 B) as DM3.
  pose proof (Z_div_mod_eq_full acc4 B) as DM4.
  pose proof (Z_div_mod_eq_full acc5 B) as DM5.
  pose proof (Z_div_mod_eq_full acc6 B) as DM6.
  subst carry0 carry1 carry2 carry3 carry4 carry5 carry6.
  subst r0 r1 r2 r3 r4 r5 r6 r7.
  assert (Heval : eval8 B (acc0 mod B) (acc1 mod B) (acc2 mod B) (acc3 mod B)
                          (acc4 mod B) (acc5 mod B) (acc6 mod B) (acc6 / B) = product).
  { unfold eval8.
    subst acc0 acc1 acc2 acc3 acc4 acc5 acc6.
    nia. }

  clear Hprod_expand DM0 DM1 DM2 DM3 DM4 DM5 DM6.

  (* Step 2: Bound [carry6 = acc6 / B].
     Non-negativity follows from the accumulators being non-negative.
     Upper bound: delegate to [eval8_last_limb_bound] using [Heval]
     and [eval4_mul_range]. *)
  assert (Hprod_range : 0 <= product < B ^ 8)
    by (subst product; apply eval4_mul_range; assumption).
  assert (Hcarry6_nn : 0 <= acc6 / B).
  { assert (0 <= acc0) by (subst acc0; nia).
    assert (0 <= acc0 / B) by (apply Z.div_pos; lia).
    assert (0 <= acc1) by (subst acc1; lia).
    assert (0 <= acc1 / B) by (apply Z.div_pos; lia).
    assert (0 <= acc2) by (subst acc2; lia).
    assert (0 <= acc2 / B) by (apply Z.div_pos; lia).
    assert (0 <= acc3) by (subst acc3; lia).
    assert (0 <= acc3 / B) by (apply Z.div_pos; lia).
    assert (0 <= acc4) by (subst acc4; lia).
    assert (0 <= acc4 / B) by (apply Z.div_pos; lia).
    assert (0 <= acc5) by (subst acc5; lia).
    assert (0 <= acc5 / B) by (apply Z.div_pos; lia).
    assert (0 <= acc6) by (subst acc6; lia).
    apply Z.div_pos; lia. }
  assert (Hcarry6_bound : 0 <= acc6 / B < B).
  { split.
    - exact Hcarry6_nn.
    - apply eval8_last_limb_bound with
        (r0 := acc0 mod B) (r1 := acc1 mod B)
        (r2 := acc2 mod B) (r3 := acc3 mod B)
        (r4 := acc4 mod B) (r5 := acc5 mod B)
        (r6 := acc6 mod B);
        try (apply Z.mod_pos_bound; lia);
        try assumption.
      rewrite Heval.
      exact (proj2 Hprod_range). }
  clear Hprod_range Hacc0 Hacc1 Hacc2 Hacc3 Hacc4 Hacc5 Hacc6
        Ha0 Ha1 Ha2 Ha3 Hb0 Hb1 Hb2 Hb3
        Hcarry6_nn.

  (* Step 3: Apply [eval8_digit_unique] and conclude.
     All output limbs lie in [[0, B)] since they are [mod B] results.
     We obtain digit equalities, rewrite [eval8 ...] to [product],
     simplify [(acc6 / B) mod B] to [acc6 / B], and finish. *)
  assert (Hr0 : 0 <= acc0 mod B < B) by (apply Z.mod_pos_bound; lia).
  assert (Hr1 : 0 <= acc1 mod B < B) by (apply Z.mod_pos_bound; lia).
  assert (Hr2 : 0 <= acc2 mod B < B) by (apply Z.mod_pos_bound; lia).
  assert (Hr3 : 0 <= acc3 mod B < B) by (apply Z.mod_pos_bound; lia).
  assert (Hr4 : 0 <= acc4 mod B < B) by (apply Z.mod_pos_bound; lia).
  assert (Hr5 : 0 <= acc5 mod B < B) by (apply Z.mod_pos_bound; lia).
  assert (Hr6 : 0 <= acc6 mod B < B) by (apply Z.mod_pos_bound; lia).
  pose proof (eval8_digit_unique B
    (acc0 mod B) (acc1 mod B) (acc2 mod B) (acc3 mod B)
    (acc4 mod B) (acc5 mod B) (acc6 mod B) (acc6 / B)
    HB Hr0 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hcarry6_bound) as Hdigits.
  rewrite Heval in Hdigits.
  cbv zeta in Hdigits.
  rewrite (Zmod_small (acc6 / B) B Hcarry6_bound).
  exact Hdigits.
Qed.

(* ================================================================= *)
(** ** Carry-chain identity for 4-limb ripple addition *)
(* ================================================================= *)

(** The carry chain ripple-adds [ov * C] (where [C = c0 + c1*B + c2*B^2])
    into a 4-limb value [val = d0 + d1*B + d2*B^2 + d3*B^3].  At each
    stage the low limb is extracted ([mod B]) and the carry is
    propagated ([/ B]).

    The four extracted limbs plus the final carry [hi] reconstruct
    exactly to [val + ov * C].  When the result fits in [B^4] the
    carry is zero; when it fits in [2 * B^4] the carry is at most 1. *)

Lemma reduce_carry_chain :
  forall B d0 d1 d2 d3 c0 c1 c2 (ov : Z),
    1 < B ->
    0 <= d0 < B -> 0 <= d1 < B -> 0 <= d2 < B -> 0 <= d3 < B ->
    0 <= c0 -> 0 <= c1 -> 0 <= c2 -> 0 <= ov ->
    let B2 := B * B in let B3 := B * B * B in let B4 := B * B * B * B in
    let val := d0 + d1 * B + d2 * B2 + d3 * B3 in
    let C := c0 + c1 * B + c2 * B2 in
    0 <= val + ov * C < 2 * B4 ->
    let t0 := d0 + ov * c0 in
    let t1 := t0 / B + d1 + ov * c1 in
    let t2 := t1 / B + d2 + ov * c2 in
    let t3 := t2 / B + d3 in
    let r_z := (t0 mod B) + (t1 mod B) * B + (t2 mod B) * B2 + (t3 mod B) * B3 in
    let hi := t3 / B in
    r_z + hi * B4 = val + ov * C
    /\ 0 <= r_z < B4
    /\ 0 <= hi <= 1.
Proof.
  intros B d0 d1 d2 d3 c0 c1 c2 ov HB Hd0 Hd1 Hd2 Hd3 Hc0 Hc1 Hc2 Hov
    B2 B3 B4 val C Hresult t0 t1 t2 t3 r_z hi.

  (* Non-negativity of intermediate accumulators *)
  assert (Ht0_nn : 0 <= t0).
  { subst t0. apply Z.add_nonneg_nonneg.
    - lia.
    - apply Z.mul_nonneg_nonneg; lia. }
  assert (Ht1_nn : 0 <= t1).
  { subst t1. apply Z.add_nonneg_nonneg.
    - apply Z.add_nonneg_nonneg.
      + apply Z.div_pos; lia.
      + lia.
    - apply Z.mul_nonneg_nonneg; lia. }
  assert (Ht2_nn : 0 <= t2).
  { subst t2. apply Z.add_nonneg_nonneg.
    - apply Z.add_nonneg_nonneg.
      + apply Z.div_pos; lia.
      + lia.
    - apply Z.mul_nonneg_nonneg; lia. }

  (* Euclidean division: t_i = B * q_i + m_i *)
  set (q0 := t0 / B).
  set (m0 := t0 mod B).
  set (q1 := t1 / B).
  set (m1 := t1 mod B).
  set (q2 := t2 / B).
  set (m2 := t2 mod B).
  set (m3 := t3 mod B).
  assert (Ht0_eq : t0 = B * q0 + m0) by (subst q0 m0; apply Z_div_mod_eq_full).
  assert (Ht1_eq : t1 = B * q1 + m1) by (subst q1 m1; apply Z_div_mod_eq_full).
  assert (Ht2_eq : t2 = B * q2 + m2) by (subst q2 m2; apply Z_div_mod_eq_full).
  assert (Ht3_eq : t3 = B * hi + m3) by (subst hi m3; apply Z_div_mod_eq_full).

  (* t_{i+1} = q_i + d_{i+1} + ov*c_{i+1} *)
  assert (Ht1_def : t1 = q0 + d1 + ov * c1) by (subst t1 q0; ring).
  assert (Ht2_def : t2 = q1 + d2 + ov * c2) by (subst t2 q1; ring).
  assert (Ht3_def : t3 = q2 + d3) by (subst t3 q2; ring).

  (* Remainder bounds *)
  assert (Hm0 : 0 <= m0 < B) by (subst m0; apply Z.mod_pos_bound; lia).
  assert (Hm1 : 0 <= m1 < B) by (subst m1; apply Z.mod_pos_bound; lia).
  assert (Hm2 : 0 <= m2 < B) by (subst m2; apply Z.mod_pos_bound; lia).
  assert (Hm3 : 0 <= m3 < B) by (subst m3; apply Z.mod_pos_bound; lia).

  (* Telescoping: substitute div/mod at each round *)
  assert (Hstep0 : val + ov * C = t0 + (d1 + ov * c1) * B + (d2 + ov * c2) * B2 + d3 * B3)
    by (subst val C t0 B2 B3; ring).
  assert (Hstep1 : val + ov * C = m0 + t1 * B + (d2 + ov * c2) * B2 + d3 * B3)
    by (rewrite Hstep0, Ht0_eq, Ht1_def; subst B2 B3; ring).
  assert (Hstep2 : val + ov * C = m0 + m1 * B + t2 * B2 + d3 * B3)
    by (rewrite Hstep1, Ht1_eq, Ht2_def; subst B2 B3; ring).
  assert (Hstep3 : val + ov * C = m0 + m1 * B + m2 * B2 + t3 * B3)
    by (rewrite Hstep2, Ht2_eq, Ht3_def; subst B2 B3; ring).

  (* Expand t3 = B * hi + m3 in the telescoped identity *)
  assert (Hstep4 : val + ov * C = m0 + m1 * B + m2 * B2 + m3 * B3 + hi * B4)
    by (rewrite Hstep3, Ht3_eq; subst B2 B3 B4; ring).

  (* r_z = m0 + m1*B + m2*B2 + m3*B3 *)
  assert (Hr_z_eq : r_z = m0 + m1 * B + m2 * B2 + m3 * B3)
    by (subst r_z m0 m1 m2 m3; reflexivity).

  (* r_z non-negativity *)
  assert (Hr_z_nn : 0 <= r_z).
  { rewrite Hr_z_eq.
    assert (0 <= m1 * B) by (apply Z.mul_nonneg_nonneg; lia).
    assert (0 <= m2 * B2).
    { subst B2. apply Z.mul_nonneg_nonneg.
      - lia.
      - apply Z.mul_nonneg_nonneg; lia. }
    assert (0 <= m3 * B3).
    { subst B3. apply Z.mul_nonneg_nonneg.
      - lia.
      - apply Z.mul_nonneg_nonneg.
        + apply Z.mul_nonneg_nonneg; lia.
        + lia. }
    lia. }

  (* r_z < B4 via geometric identity: sum of (B-1)*B^i = B^4 - 1 *)
  assert (Hr_z_ub : r_z < B4).
  { rewrite Hr_z_eq.
    assert (0 <= B2) by (subst B2; apply Z.mul_nonneg_nonneg; lia).
    assert (0 <= B3).
    { subst B3. apply Z.mul_nonneg_nonneg.
      - apply Z.mul_nonneg_nonneg; lia.
      - lia. }
    assert (m1 * B <= (B - 1) * B) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (m2 * B2 <= (B - 1) * B2) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (m3 * B3 <= (B - 1) * B3) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert ((B - 1) + (B - 1) * B + (B - 1) * B2 + (B - 1) * B3 = B4 - 1)
      by (subst B2 B3 B4; ring).
    lia. }

  (* hi bounds *)
  assert (Ht3_nonneg : 0 <= t3).
  { rewrite Ht3_def.
    assert (0 <= q2) by (subst q2; apply Z.div_pos; lia). lia. }
  assert (Hhi_nn : 0 <= hi) by (subst hi; apply Z.div_pos; lia).
  assert (0 < B4).
  { subst B4. apply Z.mul_pos_pos.
    - apply Z.mul_pos_pos.
      + apply Z.mul_pos_pos; lia.
      + lia.
    - lia. }
  assert (Hhi_le1 : hi <= 1).
  { destruct (Z_lt_dec hi 2) as [Hlt2|Hge2].
    - lia.
    - exfalso.
      assert (2 * B4 <= hi * B4) by (apply Z.mul_le_mono_nonneg_r; lia).
      lia. }

  repeat split; lia.
Qed.

(* ================================================================= *)
(** ** Modular folding lemmas *)
(* ================================================================= *)

(** General modular folding: subtracting multiples of [n] inside a
    product does not change the residue. *)
Lemma fold_sub_mod : forall a b x n : Z,
  (a + b * (x - n)) mod n = (a + b * x) mod n.
Proof.
  intros a b x n.
  replace (a + b * (x - n)) with (a + b * x + (-b) * n) by ring.
  rewrite Z_mod_plus_full.
  reflexivity.
Qed.

(** Conditional subtraction (version B): subtract multiples of N.
    Equivalent formulation: [val - k * N = val mod N] where
    [k = hi + overflow].  No [mod B] needed. *)
Lemma cond_sub_mod : forall B r hi val N,
  N < B ->
  B - N < N ->
  0 <= r < B ->
  0 <= hi <= 1 ->
  val = r + hi * B ->
  (hi = 1 -> r + (B - N) < N) ->
  val mod N = val - (hi + (if Z_lt_dec r N then 0 else 1)) * N.
Proof.
  intros B r hi val N HNB HBN Hr Hhi Hval Hhi1.
  subst val.
  assert (Hhi_cases : hi = 0 \/ hi = 1) by lia.
  destruct (Z_lt_dec r N) as [Hlt | Hge];
    destruct Hhi_cases as [Hhi0 | Hhi1'];
    subst hi.
  - (* r < N, hi = 0 *)
    simpl.
    rewrite Z.sub_0_r.
    apply Z.mod_small.
    lia.
  - (* r < N, hi = 1 *)
    specialize (Hhi1 eq_refl).
    replace (r + 1 * B) with ((r + (B - N)) + 1 * N) by lia.
    rewrite Z_mod_plus_full.
    rewrite Z.mod_small by lia.
    lia.
  - (* r >= N, hi = 0 *)
    assert (Hge' : N <= r) by lia.
    replace ((r + 0 * B) mod N) with ((r - N + 1 * N) mod N)
      by (f_equal; lia).
    rewrite Z_mod_plus_full.
    rewrite Z.mod_small by lia.
    destruct N; lia.
  - (* r >= N, hi = 1 *)
    specialize (Hhi1 eq_refl).
    lia.
Qed.
