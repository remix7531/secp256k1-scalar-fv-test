(** * Helper_arithmetic: General 4×4 limb schoolbook multiplication correctness

    This is a pure [Z] lemma, completely independent of VST, secp256k1,
    or any specific word size.  It states that the standard
    accumulate-extract-carry schoolbook algorithm correctly computes
    the product of two 4-limb numbers into 8 limbs.

    We use [Z] rather than [N] because [lia]/[nia] are weaker over [N],
    and key stdlib lemmas ([Z_div_mod_eq_full], [Z.mod_pos_bound],
    [Z.div_le_mono], etc.) lack mature [N] counterparts.  Staying
    in [Z] also avoids coercion noise at the VST/CompCert call sites
    which represent all machine integers as [Z]. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Hammer Require Import Hammer.
Open Scope Z_scope.

Set Hammer ATPLimit 30.

(* ================================================================== *)
(** ** Definitions *)
(* ================================================================== *)

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

(* ================================================================== *)
(** ** Reconstruction lemmas *)
(* ================================================================== *)

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
  simpl (Z.of_nat _); simpl (_ ^ 0);
    rewrite Z.pow_1_r, Z.div_1_r.
  replace (B ^ 2) with (B * B) by ring;
  replace (B ^ 3) with (B * B * B) by ring.
  set (q0 := x / B); set (q1 := q0 / B); set (q2 := q1 / B).
  replace (x / (B * B)) with q1 by
    (unfold q1, q0; rewrite <- Z.div_div by lia; reflexivity).
  replace (x / (B * B * B)) with q2 by
    (unfold q2, q1, q0; do 2 rewrite <- Z.div_div by lia; reflexivity).
  assert (Hq2 : 0 <= q2 < B).
  { unfold q2, q1, q0; split.
    - repeat (apply Z.div_pos; [|lia]); lia.
    - do 3 (apply Z.div_lt_upper_bound; [lia|]).
      replace (B * (B * (B * B))) with (B ^ 4) by ring; lia. }
  rewrite (Zmod_small q2 B Hq2).
  generalize (Z_div_mod_eq_full x B),
             (Z_div_mod_eq_full q0 B),
             (Z_div_mod_eq_full q1 B).
  fold q0 q1 q2. intros H0 H1 H2.
  rewrite H2 in H1; rewrite H1 in H0. lia.
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
  simpl (Z.of_nat _); simpl (_ ^ 0);
    rewrite Z.pow_1_r, Z.div_1_r.
  replace (B ^ 2) with (B * B) by ring;
  replace (B ^ 3) with (B * B * B) by ring;
  replace (B ^ 4) with (B * B * B * B) by ring;
  replace (B ^ 5) with (B * B * B * B * B) by ring;
  replace (B ^ 6) with (B * B * B * B * B * B) by ring;
  replace (B ^ 7) with (B * B * B * B * B * B * B) by ring.
  set (q0 := x / B); set (q1 := q0 / B); set (q2 := q1 / B);
  set (q3 := q2 / B); set (q4 := q3 / B); set (q5 := q4 / B);
  set (q6 := q5 / B).
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
  assert (Hq6 : 0 <= q6 < B).
  { unfold q6, q5, q4, q3, q2, q1, q0; split.
    - repeat (apply Z.div_pos; [|lia]); lia.
    - do 7 (apply Z.div_lt_upper_bound; [lia|]).
      replace (B * (B * (B * (B * (B * (B * (B * B))))))) with (B ^ 8) by ring;
      lia. }
  rewrite (Zmod_small q6 B Hq6).
  generalize (Z_div_mod_eq_full x B),
             (Z_div_mod_eq_full q0 B),
             (Z_div_mod_eq_full q1 B),
             (Z_div_mod_eq_full q2 B),
             (Z_div_mod_eq_full q3 B),
             (Z_div_mod_eq_full q4 B),
             (Z_div_mod_eq_full q5 B).
  fold q0 q1 q2 q3 q4 q5 q6.
  intros H0 H1 H2 H3 H4 H5 H6.
  rewrite H6 in H5; rewrite H5 in H4; rewrite H4 in H3;
  rewrite H3 in H2; rewrite H2 in H1; rewrite H1 in H0.
  lia.
Qed.

(* ================================================================== *)
(** ** Auxiliary lemmas *)
(* ================================================================== *)

(** The product of two 4-limb numbers fits in 8 limbs. *)
Lemma eval4_mul_range : forall B a0 a1 a2 a3 b0 b1 b2 b3,
  B > 1 ->
  0 <= a0 < B -> 0 <= a1 < B -> 0 <= a2 < B -> 0 <= a3 < B ->
  0 <= b0 < B -> 0 <= b1 < B -> 0 <= b2 < B -> 0 <= b3 < B ->
  0 <= eval4 B a0 a1 a2 a3 * eval4 B b0 b1 b2 b3 < B^8.
Proof.
  intros. unfold eval4.
  assert (Ha : 0 <= a0 + a1 * B + a2 * B ^ 2 + a3 * B ^ 3 < B ^ 4) by nia.
  assert (Hb : 0 <= b0 + b1 * B + b2 * B ^ 2 + b3 * B ^ 3 < B ^ 4) by nia.
  replace (B ^ 8) with (B ^ 4 * B ^ 4) by ring.
  split; [lia|].
  apply Z.mul_lt_mono_nonneg; lia.
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
  assert (Ha_mod : (a + b * B) mod B = a)
    by (rewrite Z_mod_plus_full; apply Zmod_small; lia).
  assert (Hc_mod : (c + d * B) mod B = c)
    by (rewrite Z_mod_plus_full; apply Zmod_small; lia).
  rewrite Heq in Ha_mod; rewrite Hc_mod in Ha_mod.
  split; [lia|].
  assert (Hbd : b * B = d * B) by lia.
  apply Z.mul_cancel_r in Hbd; lia.
Qed.

(** If an 8-limb representation with all digits in [[0, B)] equals [x],
    then each digit is [(x / B^k) mod B].

    Strategy: compare the given 8-limb representation against the
    canonical one from [eval8_limbs], then peel digits one at a time
    using [base_rep_unique_step]. *)
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
  pose proof (eval8_limbs B x HB Hx) as Hcanon.
  (* Both representations equal x; equate them *)
  assert (Heq : eval8 B r0 r1 r2 r3 r4 r5 r6 r7 =
                eval8 B (limb B x 0) (limb B x 1) (limb B x 2) (limb B x 3)
                        (limb B x 4) (limb B x 5) (limb B x 6) (limb B x 7)).
  { change (x = eval8 B (limb B x 0) (limb B x 1) (limb B x 2) (limb B x 3)
                        (limb B x 4) (limb B x 5) (limb B x 6) (limb B x 7)).
    symmetry; assumption. }
  unfold eval8 in Heq.
  assert (Hlimb : forall i, 0 <= limb B x i < B)
    by (intro; unfold limb; apply Z.mod_pos_bound; lia).
  (* Peel digits 0–7: re-associate into [a + rest * B] form,
     apply [base_rep_unique_step], clear consumed hypothesis. *)
  assert (Heq0 : r0 + (r1 + r2*B + r3*B^2 + r4*B^3 + r5*B^4 + r6*B^5 + r7*B^6) * B =
    limb B x 0 + (limb B x 1 + limb B x 2*B + limb B x 3*B^2 + limb B x 4*B^3 +
     limb B x 5*B^4 + limb B x 6*B^5 + limb B x 7*B^6) * B) by nia.
  apply base_rep_unique_step in Heq0 as [H0 Heq1]; [|lia|assumption|apply Hlimb].
  clear Heq.
  assert (Heq1' : r1 + (r2 + r3*B + r4*B^2 + r5*B^3 + r6*B^4 + r7*B^5) * B =
    limb B x 1 + (limb B x 2 + limb B x 3*B + limb B x 4*B^2 +
     limb B x 5*B^3 + limb B x 6*B^4 + limb B x 7*B^5) * B) by nia.
  apply base_rep_unique_step in Heq1' as [H1 Heq2]; [|lia|assumption|apply Hlimb].
  clear Heq1.
  assert (Heq2' : r2 + (r3 + r4*B + r5*B^2 + r6*B^3 + r7*B^4) * B =
    limb B x 2 + (limb B x 3 + limb B x 4*B + limb B x 5*B^2 +
     limb B x 6*B^3 + limb B x 7*B^4) * B) by nia.
  apply base_rep_unique_step in Heq2' as [H2 Heq3]; [|lia|assumption|apply Hlimb].
  clear Heq2.
  assert (Heq3' : r3 + (r4 + r5*B + r6*B^2 + r7*B^3) * B =
    limb B x 3 + (limb B x 4 + limb B x 5*B +
     limb B x 6*B^2 + limb B x 7*B^3) * B) by nia.
  apply base_rep_unique_step in Heq3' as [H3 Heq4]; [|lia|assumption|apply Hlimb].
  clear Heq3.
  assert (Heq4' : r4 + (r5 + r6*B + r7*B^2) * B =
    limb B x 4 + (limb B x 5 + limb B x 6*B + limb B x 7*B^2) * B) by nia.
  apply base_rep_unique_step in Heq4' as [H4 Heq5]; [|lia|assumption|apply Hlimb].
  clear Heq4.
  assert (Heq5' : r5 + (r6 + r7*B) * B =
    limb B x 5 + (limb B x 6 + limb B x 7*B) * B) by nia.
  apply base_rep_unique_step in Heq5' as [H5 Heq6]; [|lia|assumption|apply Hlimb].
  clear Heq5.
  assert (Heq6' : r6 + r7*B = limb B x 6 + limb B x 7*B) by nia.
  apply base_rep_unique_step in Heq6' as [H6 H7]; [|lia|assumption|apply Hlimb].
  (* Rewrite [limb] back to [(x / B^k) mod B] *)
  clear - H0 H1 H2 H3 H4 H5 H6 H7.
  unfold limb in *; simpl Z.of_nat in *.
  rewrite ?Z.pow_0_r, ?Z.div_1_r, ?Z.pow_1_r in *.
  repeat split; assumption.
Qed.

(* ================================================================== *)
(** ** Main theorem *)
(* ================================================================== *)

(** Schoolbook 4×4 multiplication correctness.

    Given base [B > 1] and input limbs [a0..a3], [b0..b3] in [[0, B)],
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
Lemma schoolbook_mul_4x4 :
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
  { unfold eval8; subst acc0 acc1 acc2 acc3 acc4 acc5 acc6; nia. }
  clear Hprod_expand DM0 DM1 DM2 DM3 DM4 DM5 DM6.

  (* Step 2: Bound [carry6 = acc6 / B].
     Non-negativity: chain [Z.div_pos] through accumulator definitions.
     Upper bound: [carry6 * B^7 <= product < B^8] implies [carry6 < B]. *)
  assert (Hprod_range : 0 <= product < B ^ 8)
    by (subst product; apply eval4_mul_range; assumption).
  assert (Hcarry6_bound : 0 <= acc6 / B < B).
  { split.
    { apply Z.div_pos; [|lia].
      subst acc6.
      assert (0 <= acc5 / B) by (apply Z.div_pos; [|lia]; subst acc5;
        assert (0 <= acc4 / B) by (apply Z.div_pos; [|lia]; subst acc4;
          assert (0 <= acc3 / B) by (apply Z.div_pos; [|lia]; subst acc3;
            assert (0 <= acc2 / B) by (apply Z.div_pos; [|lia]; subst acc2;
              assert (0 <= acc1 / B) by (apply Z.div_pos; [|lia]; subst acc1;
                assert (0 <= acc0 / B) by (apply Z.div_pos; [|lia]; subst acc0; nia);
              nia); nia); nia); nia); nia).
      nia. }
    { (* Lower limbs sum is non-negative, so [carry6 * B^7 <= product] *)
      assert (Hlower_nn : 0 <= acc0 mod B + acc1 mod B * B + acc2 mod B * B^2 +
              acc3 mod B * B^3 + acc4 mod B * B^4 + acc5 mod B * B^5 +
              acc6 mod B * B^6).
      { assert (0 <= acc0 mod B < B) by (apply Z.mod_pos_bound; lia).
        assert (0 <= acc1 mod B < B) by (apply Z.mod_pos_bound; lia).
        assert (0 <= acc2 mod B < B) by (apply Z.mod_pos_bound; lia).
        assert (0 <= acc3 mod B < B) by (apply Z.mod_pos_bound; lia).
        assert (0 <= acc4 mod B < B) by (apply Z.mod_pos_bound; lia).
        assert (0 <= acc5 mod B < B) by (apply Z.mod_pos_bound; lia).
        assert (0 <= acc6 mod B < B) by (apply Z.mod_pos_bound; lia).
        assert (0 < B) by lia.
        assert (0 < B^2) by (apply Z.pow_pos_nonneg; lia).
        assert (0 < B^3) by (apply Z.pow_pos_nonneg; lia).
        assert (0 < B^4) by (apply Z.pow_pos_nonneg; lia).
        assert (0 < B^5) by (apply Z.pow_pos_nonneg; lia).
        assert (0 < B^6) by (apply Z.pow_pos_nonneg; lia).
        nia. }
      (* [carry6 * B^7 <= product < B^8 = B * B^7], so [carry6 < B] *)
      assert (acc6 / B * B^7 <= product) by (unfold eval8 in Heval; lia).
      assert (0 < B ^ 7) by (apply Z.pow_pos_nonneg; lia).
      apply Z.mul_lt_mono_pos_r with (p := B^7); [lia|].
      replace (B * B^7) with (B^8) by ring. lia. } }
  clear Hprod_range Hacc0 Hacc1 Hacc2 Hacc3 Hacc4 Hacc5 Hacc6
        Ha0 Ha1 Ha2 Ha3 Hb0 Hb1 Hb2 Hb3.

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
