(** * Verif_umul128: Proof of body_secp256k1_umul128 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** secp256k1_umul128 *)

(** Shift right 32 on Int64 equals Z division. *)
Lemma Int64_shru_32 : forall x,
  0 <= x <= Int64.max_unsigned ->
  Int64.shru (Int64.repr x) (Int64.repr 32) = Int64.repr (x / Int.modulus).
Proof.
  intros.
  rewrite Int64.shru_div_two_p.
  f_equal.
  rewrite Int64.unsigned_repr by assumption.
  rewrite Int64.unsigned_repr by rep_lia.
  reflexivity.
Qed.

(** Shift left 32 on Int64 equals Z multiplication. *)
Lemma Int64_shl_32 : forall x,
  0 <= x <= Int64.max_unsigned ->
  Int64.shl (Int64.repr x) (Int64.repr 32) = Int64.repr (x * Int.modulus).
Proof.
  intros.
  rewrite Int64.shl_mul_two_p.
  rewrite Int64.unsigned_repr by rep_lia.
  change (two_p 32) with Int.modulus.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_mult;
  apply Int64.eqm_sym;
  apply Int64.eqm_unsigned_repr.
Qed.

(* ----------------------------------------------------------------- *)

(** The mid-accumulator variant of 2x2 schoolbook multiplication.
    Given limbs [a0, a1, b0, b1] in [[0, B)], the C code computes:
    - [mid := ll / B + lh mod B + hl mod B]
    - [lo  := mid * B + ll mod B]
    - [hi  := hh + lh / B + hl / B + mid / B]

    This lemma connects these computations to [eval2] and proves
    [lo mod B^2 = product mod B^2] and [hi = product / B^2]. *)
Lemma schoolbook_mul_2x2_mid :
  forall B,
  B > 1 ->
  forall a0 a1 b0 b1,
  0 <= a0 < B -> 0 <= a1 < B ->
  0 <= b0 < B -> 0 <= b1 < B ->
  let mid := a0 * b0 / B + (a0 * b1) mod B + (a1 * b0) mod B in
  let lo := mid * B + (a0 * b0) mod B in
  let hi := a1 * b1 + a0 * b1 / B + a1 * b0 / B + mid / B in
  let product := eval2 B a0 a1 * eval2 B b0 b1 in
  lo mod (B * B) = product mod (B * B) /\
  hi = product / (B * B).
Proof.
  intros B HB a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1 mid lo hi product.
  assert (HB_pos : 0 < B) by lia.
  assert (Hprod : product = a0*b0 + (a0*b1 + a1*b0)*B + a1*b1*B*B)
    by (subst product; unfold eval2; ring).
  set (acc1 := a0*b0/B + a0*b1 + a1*b0).

  (* Get digit equalities from schoolbook_mul_2x2 *)
  pose proof (schoolbook_mul_2x2 B HB a0 a1 b0 b1 Ha0 Ha1 Hb0 Hb1
    (a0*b0) eq_refl (a0*b0/B) eq_refl
    acc1 ltac:(subst acc1; reflexivity)
    (acc1/B) eq_refl
    (acc1/B + a1*b1) eq_refl
    ((acc1/B + a1*b1)/B) eq_refl) as Hmul.
  cbv zeta in Hmul.
  fold product in Hmul.
  destruct Hmul as (Hr0 & Hr1 & _ & _).

  split.

  (* --- lo mod B^2 = product mod B^2 --- *)
  { subst lo.
    (* Decompose mid = mid/B * B + mid mod B, cancel mid/B * B^2 *)
    rewrite (Z_div_mod_eq_full mid B) at 1.
    replace ((B * (mid / B) + mid mod B) * B + (a0 * b0) mod B)
      with ((a0 * b0) mod B + mid mod B * B + mid / B * (B * B)) by ring.
    rewrite Z_mod_plus_full.

    (* mid mod B = acc1 mod B *)
    subst mid.
    rewrite Zmod_add_mod_idemp by lia.
    fold acc1.
    rewrite Zmod_small
      by (pose proof (Z.mod_pos_bound (a0*b0) B HB_pos);
          pose proof (Z.mod_pos_bound acc1 B HB_pos); nia).

    (* product mod B^2 = product mod B + (product/B) mod B * B *)
    rewrite <- (eval2_mod_mul B product) by lia.
    unfold eval2.
    rewrite Hr0, Hr1.
    reflexivity. }

  (* --- hi = product / B^2 --- *)
  { subst hi.
    replace (a1 * b1 + a0 * b1 / B + a1 * b0 / B + mid / B)
      with (a1 * b1 + (a0 * b1 / B + a1 * b0 / B + mid / B)) by ring.
    subst mid.
    rewrite <- (Zdiv_cross_product_split B (a0*b0/B) (a0*b1) (a1*b0)) by lia.
    fold acc1.

    (* a1*b1 + acc1/B = product / B^2 *)
    rewrite Hprod.
    replace (a0*b0 + (a0*b1 + a1*b0) * B + a1*b1 * B * B)
      with (a1*b1 * (B * B) + ((a0*b1 + a1*b0) * B + a0*b0)) by ring.
    rewrite Z.div_add_l by lia.
    f_equal.

    (* ((a0*b1 + a1*b0)*B + a0*b0) / B^2 = acc1/B *)
    rewrite <- Z.div_div by lia.
    replace ((a0 * b1 + a1 * b0) * B + a0 * b0)
      with (acc1 * B + (a0 * b0) mod B)
      by (subst acc1; pose proof (Z_div_mod_eq_full (a0*b0) B); nia).
    rewrite Z.div_add_l by lia.
    pose proof (Z.mod_pos_bound (a0*b0) B HB_pos).
    rewrite (Z.div_small ((a0*b0) mod B) B) by lia.
    rewrite Z.add_0_r.
    reflexivity. }
Qed.

Lemma body_secp256k1_umul128:
  semax_body Vprog Gprog
    f_secp256k1_umul128 secp256k1_umul128_spec.
Proof.
  start_function.

  (* Extract the Z values from the UInt64 records for arithmetic reasoning *)
  unfold uint64_to_val in *.
  set (av := u64_val a) in *.
  set (bv := u64_val b) in *.
  assert (Hav : 0 <= av <= Int64.max_unsigned).
  { subst av.
    destruct a as [v [Ha_lo Ha_hi]].
    simpl.
    rep_lia. }

  assert (Hbv : 0 <= bv <= Int64.max_unsigned).
  { subst bv.
    destruct b as [v [Hb_lo Hb_hi]].
    simpl.
    rep_lia. }

  (* Local tactic: normalise Int.unsigned_repr_eq and shift-by-32 *)
  Ltac norm_shru :=
    repeat first
      [ rewrite !Int.unsigned_repr_eq in *
      | change (32 mod Int.modulus) with 32 in * ].

  (* ll = (uint32_t)a * (uint32_t)b *)
  forward.
  (* lh = (uint32_t)a * (b >> 32) *)
  forward.
  (* hl = (a >> 32) * (uint32_t)b *)
  forward.
  (* hh = (a >> 32) * (b >> 32) *)
  forward.

  (* Normalize: resolve unsigned_repr_eq, shift amounts, shru *)
  autorewrite with norm in *.
  norm_shru.
  rewrite !(Int64_shru_32 av) in * by lia.
  rewrite !(Int64_shru_32 bv) in * by lia.
  autorewrite with norm in *.

  (* Introduce Z-level abbreviations for the 32-bit halves *)
  set (a_lo := av mod Int.modulus) in *.
  set (a_hi := av / Int.modulus) in *.
  set (b_lo := bv mod Int.modulus) in *.
  set (b_hi := bv / Int.modulus) in *.
  deadvars!.

  (* Half-word range bounds *)
  assert (Ha_lo : 0 <= a_lo <= Int.max_unsigned).
  { subst a_lo.
    unfold Int.max_unsigned.
    pose proof (Z.mod_pos_bound av Int.modulus ltac:(rep_lia)).
    rep_lia. }
  assert (Hb_lo : 0 <= b_lo <= Int.max_unsigned).
  { subst b_lo.
    unfold Int.max_unsigned.
    pose proof (Z.mod_pos_bound bv Int.modulus ltac:(rep_lia)).
    rep_lia. }
  assert (Ha_hi : 0 <= a_hi <= Int.max_unsigned).
  { subst a_hi.
    split; [apply Z.div_pos; rep_lia|].
    unfold Int.max_unsigned.
    enough (av / Int.modulus < Int.modulus) by lia.
    apply Z.div_lt_upper_bound.
    all: rep_lia. }
  assert (Hb_hi : 0 <= b_hi <= Int.max_unsigned).
  { subst b_hi.
    split; [apply Z.div_pos; rep_lia|].
    unfold Int.max_unsigned.
    enough (bv / Int.modulus < Int.modulus) by lia.
    apply Z.div_lt_upper_bound.
    all: rep_lia. }

  (* _mid34 = (ll >> 32) + (uint32_t)lh + (uint32_t)hl *)
  forward.

  (* Cross-product range bounds (needed for repr round-trips) *)
  assert (Hll : 0 <= a_lo * b_lo <= Int64.max_unsigned)
    by (apply mul_u32_range; lia).
  assert (Hlh : 0 <= a_lo * b_hi <= Int64.max_unsigned)
    by (apply mul_u32_range; lia).
  assert (Hhl : 0 <= a_hi * b_lo <= Int64.max_unsigned)
    by (apply mul_u32_range; lia).
  assert (Hhh : 0 <= a_hi * b_hi <= Int64.max_unsigned)
    by (apply mul_u32_range; lia).

  autorewrite with norm in *.
  norm_shru.
  rewrite !(Int64_shru_32 (a_lo * b_lo)) in * by lia.
  autorewrite with norm in *.

  (* Abbreviate mid34 *)
  set (mid34 := a_lo * b_lo / Int.modulus +
    (a_lo * b_hi) mod Int.modulus +
    (a_hi * b_lo) mod Int.modulus) in *.

  assert (Hmid34 : 0 <= mid34 <= Int64.max_unsigned).
  { subst mid34.
    pose proof (Z.mod_pos_bound (a_lo * b_hi) Int.modulus ltac:(rep_lia)).
    pose proof (Z.mod_pos_bound (a_hi * b_lo) Int.modulus ltac:(rep_lia)).
    pose proof (Z.div_pos (a_lo * b_lo) Int.modulus ltac:(lia) ltac:(rep_lia)).
    pose proof (Z.div_lt_upper_bound (a_lo * b_lo) Int.modulus Int.modulus
                  ltac:(rep_lia) ltac:(rep_lia)).
    rep_lia. }

  (* *hi = hh + (lh >> 32) + (hl >> 32) + (mid34 >> 32) *)
  forward.
  norm_shru.
  rewrite !(Int64_shru_32 (a_lo * b_hi)) by lia.
  rewrite !(Int64_shru_32 (a_hi * b_lo)) by lia.
  rewrite !(Int64_shru_32 mid34) in * by lia.
  autorewrite with norm in *.

  set (hi_val := a_hi * b_hi +
    a_lo * b_hi / Int.modulus +
    a_hi * b_lo / Int.modulus +
    mid34 / Int.modulus) in *.

  (* return mid34 << 32 + (uint32_t)ll *)
  forward.
  autorewrite with norm.
  norm_shru.
  rewrite !(Int64_shl_32 mid34) by lia.
  autorewrite with norm.

  set (lo_val := mid34 * Int.modulus + (a_lo * b_lo) mod Int.modulus) in *.

  (* --- Apply the glue lemma --- *)

  assert (Hprod_eq : eval2 Int.modulus a_lo a_hi *
                     eval2 Int.modulus b_lo b_hi = av * bv).
  { unfold eval2, a_lo, a_hi, b_lo, b_hi.
    pose proof (Z_div_mod_eq_full av Int.modulus).
    pose proof (Z_div_mod_eq_full bv Int.modulus).
    nia. }

  (* Strict half-word bounds for schoolbook_mul_2x2_mid *)
  assert (Ha_lo_s : 0 <= a_lo < Int.modulus)
    by (unfold a_lo; apply Z.mod_pos_bound; rep_lia).
  assert (Ha_hi_s : 0 <= a_hi < Int.modulus).
  { unfold a_hi.
    split; [apply Z.div_pos; rep_lia|].
    apply Z.div_lt_upper_bound; rep_lia. }
  assert (Hb_lo_s : 0 <= b_lo < Int.modulus)
    by (unfold b_lo; apply Z.mod_pos_bound; rep_lia).
  assert (Hb_hi_s : 0 <= b_hi < Int.modulus).
  { unfold b_hi.
    split; [apply Z.div_pos; rep_lia|].
    apply Z.div_lt_upper_bound; rep_lia. }

  (* Apply glue lemma and fold back into lo_val / hi_val *)
  pose proof (schoolbook_mul_2x2_mid Int.modulus ltac:(rep_lia)
    a_lo a_hi b_lo b_hi
    Ha_lo_s Ha_hi_s Hb_lo_s Hb_hi_s) as Hmul.
  cbv zeta in Hmul.
  rewrite Hprod_eq in Hmul.
  fold mid34 in Hmul.
  fold lo_val hi_val in Hmul.
  destruct Hmul as (Hlo & Hhi).

  (* --- Postcondition --- *)
  Exists (mul_64 a b).
  unfold mul_64, u128_lo, u128_hi, uint64_to_val.
  simpl.
  entailer!.

  (* Reduce both goals to equations *)
  1: f_equal.
  2: apply derives_refl'; do 2 f_equal.

  (* ===== Cleanup ===== *)
  clear - Hlo Hhi lo_val av bv.

  (* Goal 1: lo *)
  + apply Int64.eqm_samerepr.
    apply Int64.eqm_trans with (lo_val mod Int64.modulus). 
      { apply eqmod_mod. rep_lia. }
    change Int64.modulus with (Int.modulus * Int.modulus).
    rewrite Hlo.
    unfold limb64.
    simpl Z.of_nat.
    rewrite Z.mul_0_r, Z.div_1_r.
    change (2^64) with Int64.modulus.
    change (Int.modulus * Int.modulus) with Int64.modulus.
    apply Int64.eqm_refl.

  (* Goal 2: hi *)
  + apply Int64.eqm_samerepr.
    rewrite Hhi.
    change (Int.modulus * Int.modulus) with Int64.modulus.
    unfold limb64.
    simpl Z.of_nat.
    change (64 * 1)%Z with 64%Z.
    change (2^64) with Int64.modulus.
    apply eqmod_mod.
    rep_lia.
Qed.
