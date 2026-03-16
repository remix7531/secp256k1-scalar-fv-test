(** * Verif_scalar_4x64: Correctness proofs for scalar_4x64.c *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import VST.floyd.proofauto.
Require Import compcert.lib.Zbits.
Require Import scalar_4x64.scalar_4x64.
Require Import scalar_4x64.Spec_scalar_4x64.
Require Import scalar_4x64.Array_fold_lemmas.

(* ================================================================= *)
(** ** secp256k1_u128_to_u64 *)

(** The function body dereferences the struct pointer, reads the [lo]
    field, and returns it.  That is two [forward] steps. *)

Lemma body_secp256k1_u128_to_u64:
  semax_body Vprog Gprog
    f_secp256k1_u128_to_u64 secp256k1_u128_to_u64_spec.
Proof.
  start_function.
  forward. (* _t'1 = a->lo *)
  forward. (* return _t'1 *)
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_hi_u64 *)

(** Same structure: dereference, read [hi] field, return. *)

Lemma body_secp256k1_u128_hi_u64:
  semax_body Vprog Gprog
    f_secp256k1_u128_hi_u64 secp256k1_u128_hi_u64_spec.
Proof.
  start_function.
  forward. (* _t'1 = a->hi *)
  forward. (* return _t'1 *)
Qed.

(* ================================================================= *)
(** ** secp256k1_umul128 *)

(** Helper lemmas for 64-bit modular arithmetic. *)

(** Product of two 32-bit values fits in 64 bits. *)
Lemma mul_32_32_range : forall a b,
  0 <= a <= Int.max_unsigned ->
  0 <= b <= Int.max_unsigned ->
  0 <= a * b <= Int64.max_unsigned.
Proof.
  intros.
  unfold Int64.max_unsigned, Int.max_unsigned in *.
  simpl in *.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - assert (a * b <= (2^32 - 1) * (2^32 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
    lia.
Qed.

(** Shift right 32 on Int64 equals Z division. *)
Lemma Int64_shru_32 : forall x,
  0 <= x <= Int64.max_unsigned ->
  Int64.shru (Int64.repr x) (Int64.repr 32) = Int64.repr (x / Int.modulus).
Proof.
  intros.
  rewrite Int64.shru_div_two_p.
  f_equal.
  rewrite Int64.unsigned_repr by assumption.
  rewrite Int64.unsigned_repr.
  - reflexivity.
  - rep_lia.
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
  apply Int64.eqm_sym; apply Int64.eqm_unsigned_repr.
Qed.

(* ----------------------------------------------------------------- *)

(** Euclidean division identity with commuted multiplication. *)
Lemma div_mod_eq : forall a b, b <> 0 -> a = a / b * b + a mod b.
Proof. intros. pose proof (Z_div_mod_eq_full a b). lia. Qed.

(** The schoolbook multiplication low-half identity (modular form):
    ((mid34 << 32) + (uint32_t)ll) mod 2^64  =  (a * b) mod 2^64
    where mid34 = ll>>32 + (uint32_t)lh + (uint32_t)hl *)
Lemma umul128_lo_correct : forall a b,
  0 <= a <= Int64.max_unsigned ->
  0 <= b <= Int64.max_unsigned ->
  let M := Int.modulus in
  let a_lo := a mod M in
  let a_hi := a / M in
  let b_lo := b mod M in
  let b_hi := b / M in
  let mid34 := a_lo * b_lo / M + (a_lo * b_hi) mod M + (a_hi * b_lo) mod M in
  (mid34 * M + (a_lo * b_lo) mod M) mod (M * M) = (a * b) mod (M * M).
Proof.
  intros a b Ha Hb.
  cbv zeta.

  set (M := Int.modulus).
  set (al := a mod M).  set (ah := a / M).
  set (bl := b mod M).  set (bh := b / M).
  set (ll := al * bl).  set (lh := al * bh).
  set (hl := ah * bl).  set (hh := ah * bh).
  fold al bl ah bh ll lh hl.

  (* --- Setup --- *)
  assert (HM : 0 < M) by (subst M; rep_lia).
  assert (Ha_eq : a = ah * M + al) by (subst ah al; apply div_mod_eq; lia).
  assert (Hb_eq : b = bh * M + bl) by (subst bh bl; apply div_mod_eq; lia).
  assert (Hlh_eq : lh = lh / M * M + lh mod M) by (apply div_mod_eq; lia).
  assert (Hhl_eq : hl = hl / M * M + hl mod M) by (apply div_mod_eq; lia).
  assert (Hll_eq : ll = ll / M * M + ll mod M) by (apply div_mod_eq; lia).

  (* --- Main algebraic argument --- *)

  (* Step 1: Expand a*b using the schoolbook decomposition
       a*b = hh * M^2 + (lh + hl) * M + ll                     *)
  assert (Hab : a * b = hh * (M * M) + (lh + hl) * M + ll).
  { subst hh lh hl ll. rewrite Ha_eq, Hb_eq. ring. }
  rewrite Hab.

  (* Step 2: Cancel hh * M^2 by Z_mod_plus_full
       (x + k * M^2) mod M^2 = x mod M^2                       *)
  replace (hh * (M * M) + (lh + hl) * M + ll)
    with ((lh + hl) * M + ll + hh * (M * M)) by ring.
  rewrite Z_mod_plus_full.

  (* Step 3: Split each of lh, hl, ll into (high * M + low) and
     regroup so that high parts form another multiple of M^2:
       (lh + hl) * M + ll
         = (lh/M + hl/M) * M^2
           + ((lh%M + hl%M + ll/M) * M + ll%M)                 *)
  assert (Hexp : (lh + hl) * M + ll =
    (lh / M + hl / M) * (M * M) +
    ((lh mod M + hl mod M + ll / M) * M + ll mod M)).
  { rewrite Hlh_eq at 1. rewrite Hhl_eq at 1. rewrite Hll_eq at 1. ring. }
  rewrite Hexp.

  (* Step 4: Cancel the (lh/M + hl/M) * M^2 term *)
  replace ((lh / M + hl / M) * (M * M) +
           ((lh mod M + hl mod M + ll / M) * M + ll mod M))
    with ((lh mod M + hl mod M + ll / M) * M + ll mod M +
          (lh / M + hl / M) * (M * M)) by ring.
  rewrite Z_mod_plus_full.

  (* Step 5: Peel off [mod] and [+ ll%M] with [f_equal],
     cancel the common [* M] factor, then [lia] finishes. *)
  f_equal. f_equal.
  apply Z.mul_cancel_r with (p := M); lia.
Qed.

(** The schoolbook multiplication high-half identity:
    hh + (lh>>32) + (hl>>32) + (mid34>>32)  =  (a * b) / 2^64 *)
Lemma umul128_hi_correct : forall a b,
  0 <= a <= Int64.max_unsigned ->
  0 <= b <= Int64.max_unsigned ->
  let M := Int.modulus in
  let a_lo := a mod M in
  let a_hi := a / M in
  let b_lo := b mod M in
  let b_hi := b / M in
  let mid34 := a_lo * b_lo / M + (a_lo * b_hi) mod M + (a_hi * b_lo) mod M in
  a_hi * b_hi + a_lo * b_hi / M + a_hi * b_lo / M + mid34 / M = (a * b) / (M * M).
Proof.
  intros a b Ha Hb.
  cbv zeta.

  set (M := Int.modulus).
  set (al := a mod M).  set (ah := a / M).
  set (bl := b mod M).  set (bh := b / M).
  set (ll := al * bl).  set (lh := al * bh).
  set (hl := ah * bl).  set (hh := ah * bh).
  fold al bl ah bh ll lh hl.

  (* --- Setup --- *)
  assert (HM : 0 < M) by (subst M; rep_lia).
  assert (Hll_mod : 0 <= ll mod M < M) by (apply Z.mod_pos_bound; lia).
  assert (Ha_eq : a = ah * M + al) by (subst ah al; apply div_mod_eq; lia).
  assert (Hb_eq : b = bh * M + bl) by (subst bh bl; apply div_mod_eq; lia).
  assert (Hlh_eq : lh = lh / M * M + lh mod M) by (apply div_mod_eq; lia).
  assert (Hhl_eq : hl = hl / M * M + hl mod M) by (apply div_mod_eq; lia).
  assert (Hll_eq : ll = ll / M * M + ll mod M) by (apply div_mod_eq; lia).

  (* --- Main algebraic argument --- *)

  (* Step 1: Expand a*b using the schoolbook decomposition
       a*b = hh * M^2 + (lh + hl) * M + ll                     *)
  assert (Hab : a * b = hh * (M * M) + (lh + hl) * M + ll).
  { subst hh lh hl ll. rewrite Ha_eq, Hb_eq. ring. }
  rewrite Hab.

  (* Step 2: Split each of lh, hl, ll into (high * M + low) and
     regroup so that high parts form another multiple of M^2:
       (lh + hl) * M + ll
         = (lh/M + hl/M) * M^2
           + ((lh%M + hl%M + ll/M) * M + ll%M)                 *)
  assert (Hexp : (lh + hl) * M + ll =
    (lh / M + hl / M) * (M * M) +
    ((lh mod M + hl mod M + ll / M) * M + ll mod M)).
  { rewrite Hlh_eq at 1. rewrite Hhl_eq at 1. rewrite Hll_eq at 1. ring. }

  (* Step 3: Pull (hh + lh/M + hl/M) out of the division by
     Z.div_add_l, then cancel it on both sides with [f_equal]:
       ((k * M^2) + rest) / M^2  =  k + rest / M^2             *)
  replace (hh * (M * M) + (lh + hl) * M + ll)
    with ((hh + lh / M + hl / M) * (M * M) +
          ((lh mod M + hl mod M + ll / M) * M + ll mod M))
    by lia.
  rewrite Z.div_add_l by lia.
  f_equal.

  (* Step 4: Decompose division by M*M into two divisions by M,
     peel off the integer part, then kill the remainder:
       (x * M + r) / (M * M)  =  (x + r/M) / M  =  x / M
     because 0 <= r < M implies r / M = 0.                      *)
  replace (ll / M + lh mod M + hl mod M)
    with (lh mod M + hl mod M + ll / M) by lia.
  rewrite <- Z.div_div by lia.
  rewrite Z.div_add_l by lia.
  rewrite (Z.div_small (ll mod M) M) by lia.
  f_equal. lia.
Qed.

(* ----------------------------------------------------------------- *)

Lemma body_secp256k1_umul128:
  semax_body Vprog Gprog
    f_secp256k1_umul128 secp256k1_umul128_spec.
Proof.
  start_function.

  (* Local tactic: normalise Int.unsigned_repr_eq and shift-by-32 *)
  Ltac norm_shru :=
    repeat first
      [ rewrite !Int.unsigned_repr_eq in *
      | change (32 mod Int.modulus) with 32 in * ].

  (* Execute the four partial-product assignments *)
  do 4 forward.

  (* Normalize: resolve unsigned_repr_eq, shift amounts, shru *)
  autorewrite with norm in *.
  norm_shru.
  rewrite !(Int64_shru_32 a) in * by lia.
  rewrite !(Int64_shru_32 b) in * by lia.
  autorewrite with norm in *.

  (* Introduce Z-level abbreviations for the 32-bit halves *)
  set (a_lo := a mod Int.modulus) in *.
  set (a_hi := a / Int.modulus) in *.
  set (b_lo := b mod Int.modulus) in *.
  set (b_hi := b / Int.modulus) in *.
  deadvars!.

  (* Half-word range bounds *)
  assert (Ha_lo : 0 <= a_lo <= Int.max_unsigned).
  { subst a_lo. unfold Int.max_unsigned.
    pose proof (Z.mod_pos_bound a Int.modulus ltac:(rep_lia)). rep_lia. }
  assert (Hb_lo : 0 <= b_lo <= Int.max_unsigned).
  { subst b_lo. unfold Int.max_unsigned.
    pose proof (Z.mod_pos_bound b Int.modulus ltac:(rep_lia)). rep_lia. }
  assert (Ha_hi : 0 <= a_hi <= Int.max_unsigned).
  { subst a_hi. split; [apply Z.div_pos; rep_lia|].
    unfold Int.max_unsigned.
    enough (a / Int.modulus < Int.modulus) by lia.
    apply Z.div_lt_upper_bound; rep_lia. }
  assert (Hb_hi : 0 <= b_hi <= Int.max_unsigned).
  { subst b_hi. split; [apply Z.div_pos; rep_lia|].
    unfold Int.max_unsigned.
    enough (b / Int.modulus < Int.modulus) by lia.
    apply Z.div_lt_upper_bound; rep_lia. }

  (* _mid34 = (ll >> 32) + (uint32_t)lh + (uint32_t)hl *)
  forward.

  (* Cross-product range bounds (needed for repr round-trips) *)
  assert (Hll : 0 <= a_lo * b_lo <= Int64.max_unsigned)
    by (apply mul_32_32_range; lia).
  assert (Hlh : 0 <= a_lo * b_hi <= Int64.max_unsigned)
    by (apply mul_32_32_range; lia).
  assert (Hhl : 0 <= a_hi * b_lo <= Int64.max_unsigned)
    by (apply mul_32_32_range; lia).
  assert (Hhh : 0 <= a_hi * b_hi <= Int64.max_unsigned)
    by (apply mul_32_32_range; lia).

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

  (* --- Postcondition --- *)
  entailer!; repeat split.

  (* 0 <= umul128_lo a b *)
  + unfold umul128_lo. apply Z.mod_pos_bound. lia.

  (* umul128_lo a b <= max_unsigned *)
  + unfold umul128_lo.
    destruct (Z.mod_pos_bound (a * b) (2^64)); rep_lia.

  (* 0 <= umul128_hi a b *)
  + unfold umul128_hi. apply Z.div_pos; lia.

  (* umul128_hi a b <= max_unsigned *)
  + unfold umul128_hi.
    apply Z.le_trans with (2^64 - 1); [|rep_lia].
    apply Z.lt_le_pred.
    apply Z.div_lt_upper_bound; [lia|].
    apply Z.lt_le_trans with ((a + 1) * (b + 1)); try lia.
    apply Z.mul_le_mono_nonneg; rep_lia.

  (* return value = umul128_lo a b *)
  + f_equal. apply Int64.eqm_samerepr.
    apply Int64.eqm_trans with (lo_val mod Int64.modulus);
      [apply eqmod_mod; rep_lia|].
    subst lo_val mid34 a_lo a_hi b_lo b_hi.
    unfold umul128_lo.
    change Int64.modulus with (Int.modulus * Int.modulus).
    change (2^64) with (Int.modulus * Int.modulus).
    rewrite umul128_lo_correct by assumption.
    apply Int64.eqm_refl.

  (* *hi = umul128_hi a b *)
  + auto.
  + destruct H1 as [_ [_ [? _]]]; auto.
  + destruct H1 as [_ [_ [_ [? _]]]]; auto.
  + unfold data_at, field_at in H3; rewrite at_offset_eq in H3; simpl in H3;
    destruct H3 as [_ H3]; rewrite at_offset_eq.
    replace (umul128_hi a b) with hi_val; [exact H3|].
    subst hi_val mid34 a_lo a_hi b_lo b_hi.
    unfold umul128_hi.
    change (2^64) with (Int.modulus * Int.modulus).
    apply umul128_hi_correct; assumption.
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_mul *)

(** Plumbing around the umul128 spec. *)

Lemma body_secp256k1_u128_mul:
  semax_body Vprog Gprog
    f_secp256k1_u128_mul secp256k1_u128_mul_spec.
Proof.
  start_function.
  (* Split the uninitialised struct *r into field_at_ for .lo and .hi *)
  unfold data_at_, field_at_.
  unfold_data_at (field_at sh (Tstruct __191 noattr) [] _ r_ptr).

  (* We need field_compatible to form &r->hi for the forward_call *)
  assert_PROP (field_compatible (Tstruct __191 noattr) [StructField _hi] r_ptr)
    as Hfc by entailer!.

  (* Convert the .hi field_at_ to data_at_ to match umul128's SEP pre *)
  rewrite (field_at_data_at sh _ [StructField _hi]) by reflexivity.

  (* r->lo = secp256k1_umul128(a, b, &r->hi) *)
  forward_call (a, b,
    field_address (Tstruct __191 noattr) [StructField _hi] r_ptr, sh).
  forward. (* r->lo = return value *)

  (* Reassemble the struct for the postcondition *)
  unfold u128_val.
  unfold_data_at (data_at sh (Tstruct __191 noattr) _ r_ptr).
  rewrite (field_at_data_at sh _ [StructField _hi]) by reflexivity.
  entailer!.
Qed.

(* ================================================================= *)
(** ** muladd *)

Lemma umul128_lo_range : forall a b,
  0 <= a <= Int64.max_unsigned ->
  0 <= b <= Int64.max_unsigned ->
  0 <= umul128_lo a b <= Int64.max_unsigned.
Proof.
  intros a b Ha Hb.
  unfold umul128_lo. split.
  - apply Z.mod_pos_bound; lia.
  - assert (0 <= (a * b) mod 2^64 < 2^64).
    { apply Z.mod_pos_bound; lia. }
    rep_lia.
Qed.

Lemma umul128_hi_range : forall a b,
  0 <= a <= Int64.max_unsigned ->
  0 <= b <= Int64.max_unsigned ->
  0 <= umul128_hi a b <= Int64.max_unsigned.
Proof.
  intros a b Ha Hb.
  unfold umul128_hi. split.
  - apply Z.div_pos; nia.
  - assert (0 <= (a * b) / 2^64 < 2^64).
    { split.
      - apply Z.div_pos; [nia | lia].
      - apply Z.div_lt_upper_bound; [lia|].
        unfold Int64.max_unsigned in *; simpl in *; nia. }
    rep_lia.
Qed.

Lemma mod_64_range : forall x,
  0 <= x mod Int64.modulus <= Int64.max_unsigned.
Proof.
  intros.
  assert (H : 0 <= x mod Int64.modulus < Int64.modulus).
  { apply Z.mod_pos_bound; rep_lia. }
  rep_lia.
Qed.

(** Unsigned addition carry detection: comparing [c0 + tl < tl] after
    wrapping gives 0 when no overflow occurred, 1 otherwise. *)
Lemma carry_detect_b2z : forall c0 tl,
  0 <= c0 <= Int64.max_unsigned ->
  0 <= tl <= Int64.max_unsigned ->
  Z.b2z (Int64.ltu (Int64.repr (c0 + tl)) (Int64.repr tl)) =
  (if c0 + tl <? Int64.modulus then 0 else 1).
Proof.
  intros.
  destruct (c0 + tl <? Int64.modulus) eqn:Hcarry.
  + (* no overflow: c0 + tl fits, so repr is identity and (c0+tl) >= tl *)
    apply Z.ltb_lt in Hcarry.
    unfold Int64.ltu.
    rewrite !Int64.unsigned_repr by rep_lia.
    rewrite zlt_false by lia.
    reflexivity.
  + (* overflow: c0 + tl wraps to (c0+tl - 2^64), which is < tl *)
    apply Z.ltb_ge in Hcarry.
    unfold Int64.ltu.
    rewrite (Int64.unsigned_repr tl) by rep_lia.
    rewrite Int64.unsigned_repr_eq.
    replace ((c0 + tl) mod Int64.modulus) with (c0 + tl - Int64.modulus)
      by (symmetry; apply Zmod_unique with 1; rep_lia).
    rewrite zlt_true by rep_lia.
    reflexivity.
Qed.

Lemma body_muladd:
  semax_body Vprog Gprog f_muladd muladd_spec.
Proof.
  start_function.

  (* secp256k1_u128_mul(&t, a, b) *)
  forward_call.
  (* tl = secp256k1_u128_to_u64(&t) *)
  forward_call.
  { split; [apply umul128_lo_range | apply umul128_hi_range]; rep_lia. }
  (* th = secp256k1_u128_hi_u64(&t) *)
  forward_call.
  { split; [apply umul128_lo_range | apply umul128_hi_range]; rep_lia. }

  (* acc->c0 += tl *)
  forward.
  (* th += (acc->c0 < tl) *)
  forward.
  (* acc->c1 += th *)
  forward.
  forward.
  forward.
  forward.
  (* acc->c2 += (acc->c1 < th) *)
  forward.
  forward.
  forward.

  assert (Hab_mod: 0 <= (a * b) mod 2 ^ 64 <= Int64.max_unsigned). {
    split.
    + apply Z.mod_pos_bound; lia.
    + apply mod_64_range.
  }

  assert (Hab_div: 0 <= a * b / 2 ^ 64 <= Int64.max_unsigned). {
    split.
    + apply Z.div_pos; nia.
    + enough (a * b / 2 ^ 64 < 2 ^ 64) by rep_lia.
      apply Z.div_lt_upper_bound; try lia.
      unfold Int64.max_unsigned in *;
      simpl in *.
      nia.
  }

  (* th + carry fits in 64 bits because a*b <= (2^64-1)^2. *)
  assert (Hth_carry: 0 <= a * b / 2 ^ 64 + 1 <= Int64.max_unsigned).
  { split; try lia.
    enough (a * b / 2^64 < 2^64 - 1) by rep_lia.
    apply Z.div_lt_upper_bound; try lia.
    apply Z.le_lt_trans with ((2^64 - 1) * (2^64 - 1)); try rep_lia.
    apply Z.mul_le_mono_nonneg; rep_lia. }

  (* --- Postcondition --- *)
  entailer!.
  unfold acc_val, muladd_c0, muladd_c1, muladd_c2, muladd_th, umul128_lo, umul128_hi.
  apply derives_refl'.
  f_equal; f_equal; f_equal.
  + (* c0: repr (c0 + lo) = repr ((c0 + lo) mod 2^64) *)
    apply Int64.eqm_samerepr.
    apply Zbits.eqmod_mod; lia.
  + (* c1: repr (c1 + th + carry0) = repr ((c1 + th + carry0) mod 2^64) *)
    f_equal.
    apply Int64.eqm_samerepr.
    rewrite carry_detect_b2z; try assumption.
    destruct (_ <? _);
    apply Zbits.eqmod_mod; lia.
  + (* c2: repr (c2 + carry1) = repr ((c2 + carry1) mod 2^64) *)
    f_equal.
    apply Int64.eqm_samerepr.
    rewrite carry_detect_b2z; try assumption.
    - rewrite carry_detect_b2z; try assumption.
      rewrite Int.signed_repr by (destruct (_ <? _); rep_lia).
      rewrite Int.signed_repr by (destruct (_ <? _); rep_lia).
      apply Zbits.eqmod_mod; lia.
    - rewrite carry_detect_b2z; try assumption.
      rewrite Int.signed_repr by (destruct (_ <? _); rep_lia).
      destruct (_ <? _); lia.
Qed.

(* ================================================================= *)
(** ** muladd_fast *)

Lemma body_muladd_fast:
  semax_body Vprog Gprog f_muladd_fast muladd_fast_spec.
Proof.
  start_function.

  (* secp256k1_u128_mul(&t, a, b) *)
  forward_call.
  (* tl = secp256k1_u128_to_u64(&t) *)
  forward_call.
  { split; [apply umul128_lo_range | apply umul128_hi_range]; rep_lia. }
  (* th = secp256k1_u128_hi_u64(&t) *)
  forward_call.
  { split; [apply umul128_lo_range | apply umul128_hi_range]; rep_lia. }

  (* acc->c0 += tl *)
  forward.
  (* th += (acc->c0 < tl) *)
  forward.
  (* acc->c1 += th *)
  forward.
  forward.
  forward.
  forward.

  assert (Hab_mod: 0 <= (a * b) mod 2 ^ 64 <= Int64.max_unsigned). {
    split.
    + apply Z.mod_pos_bound; lia.
    + apply mod_64_range.
  }

  (* --- Postcondition --- *)
  entailer!.
  unfold acc_val, muladd_c0, muladd_c1, muladd_th, umul128_lo, umul128_hi.
  apply derives_refl'.
  f_equal; f_equal; f_equal.
  - (* c0: repr (c0 + lo) = repr ((c0 + lo) mod 2^64) *)
    apply Int64.eqm_samerepr.
    apply Zbits.eqmod_mod; lia.
  - (* c1: repr (c1 + th + carry) = repr ((c1 + th + carry) mod 2^64) *)
    f_equal.
    apply Int64.eqm_samerepr.
    rewrite carry_detect_b2z; try assumption.
    destruct (_ <? _);
    apply Zbits.eqmod_mod; lia.
Qed.

(* ================================================================= *)
(** ** extract *)

Lemma body_extract:
  semax_body Vprog Gprog f_extract extract_spec.
Proof.
  start_function.
  repeat forward.
  entailer!.
Qed.

(* ================================================================= *)
(** ** extract_fast *)

Lemma body_extract_fast:
  semax_body Vprog Gprog f_extract_fast extract_fast_spec.
Proof.
  start_function.
  repeat forward.
  entailer!.
Qed. 

(* ================================================================= *)
(** ** secp256k1_scalar_mul_512 *)

(** Decompose a list of known Zlength into its elements. *)
Lemma list_Z_Zlength_4 : forall (l : list Z),
  Zlength l = 4 -> l = [Znth 0 l; Znth 1 l; Znth 2 l; Znth 3 l].
Proof.
  intros l Hlen.
  rewrite Zlength_correct in Hlen.
  do 4 (destruct l as [| ? l]; [simpl in Hlen; lia |]).
  destruct l; [| simpl in Hlen; lia].
  reflexivity.
Qed.


(** The product of two 64-bit unsigned integers fits in 128 bits. *)
Lemma mul_64_64_lt_128 : forall a b,
  0 <= a < 2^64 ->
  0 <= b < 2^64 ->
  a * b < 2^128.
Proof.
  intros a b Ha Hb.
  assert (a * b <= (2^64 - 1) * (2^64 - 1))
    by (apply Z.mul_le_mono_nonneg; lia).
  lia.
Qed.

(** muladd_c0/c1/c2 always produce values in [0, Int64.max_unsigned]. *)
Lemma muladd_c0_range : forall c0 a b,
  0 <= muladd_c0 c0 a b <= Int64.max_unsigned.
Proof. intros; unfold muladd_c0; apply mod_64_range. Qed.

Lemma muladd_c1_range : forall c0 c1 a b,
  0 <= muladd_c1 c0 c1 a b <= Int64.max_unsigned.
Proof. intros; unfold muladd_c1; apply mod_64_range. Qed.

Lemma muladd_c2_range : forall c0 c1 c2 a b,
  0 <= muladd_c2 c0 c1 c2 a b <= Int64.max_unsigned.
Proof. intros; unfold muladd_c2; apply mod_64_range. Qed.

(** Solve range goals of the form [0 <= muladd_cX ...] or [muladd_cX ... <= _]. *)
Ltac solve_muladd_range :=
  try match goal with
  | |- 0 <= muladd_c0 _ _ _             => apply muladd_c0_range
  | |- muladd_c0 _ _ _ <= _             => apply muladd_c0_range
  | |- 0 <= muladd_c1 _ _ _ _           => apply muladd_c1_range
  | |- muladd_c1 _ _ _ _ <= _           => apply muladd_c1_range
  | |- 0 <= muladd_c2 _ _ _ _ _         => apply muladd_c2_range
  | |- muladd_c2 _ _ _ _ _ <= _         => apply muladd_c2_range
  end.

(** [muladd] preserves the mathematical value of the accumulator:
      acc_full after = acc_full before + a * b provided the 
      accumulator doesn't overflow (c2 doesn't wrap). *)
Lemma acc_full_muladd : forall c0 c1 c2 a b,
  0 <= c0 <= Int64.max_unsigned ->
  0 <= c1 <= Int64.max_unsigned ->
  0 <= c2 <= Int64.max_unsigned ->
  0 <= a <= Int64.max_unsigned ->
  0 <= b <= Int64.max_unsigned ->
  acc_full c0 c1 c2 + a * b < 2^192 ->
  acc_full (muladd_c0 c0 a b) (muladd_c1 c0 c1 a b) (muladd_c2 c0 c1 c2 a b)
  = acc_full c0 c1 c2 + a * b.
Proof.
  intros c0 c1 c2 a b Hc0 Hc1 Hc2 Ha Hb Hacc.
  unfold acc_full in *; unfold muladd_c2, muladd_c1, muladd_c0, muladd_th.
  change Int64.max_unsigned with (2^64 - 1) in *.

  (* --- Establish the bounds we will need in every case --- *)

  (* The low 64 bits of a*b *)
  assert (Hab_mod : 0 <= (a * b) mod 2^64 < 2^64)
    by (apply Z.mod_pos_bound; lia).
  (* The high 64 bits of a*b.  Because a,b <= 2^64-1,
     a*b <= (2^64-1)^2 = 2^128-2^65+1, so a*b/2^64 <= 2^64-2.
     This means a*b/2^64 + 1 (the carry case) still fits in 64 bits. *)
  assert (Hab_div : 0 <= (a * b) / 2^64 <= 2^64 - 2).
  { split; [apply Z.div_pos; lia|].
    enough ((a * b) / 2^64 < 2^64 - 1) by lia.
    apply Z.div_lt_upper_bound; [lia|]. nia. }
  (* The Euclidean decomposition, needed by [lia] to recombine
     (a*b) mod 2^64 and (a*b) / 2^64 back into a*b. *)
  pose proof (Z.div_mod (a * b) (2^64) ltac:(lia)) as Hab_decomp.

  (* --- Case-split on the two carry flags --- *)

  destruct (c0 + (a * b) mod 2 ^ 64 <? 2 ^ 64) eqn:Hc0_carry;
    [apply Z.ltb_lt in Hc0_carry | apply Z.ltb_ge in Hc0_carry].

  + (* ---- c0 + lo did NOT overflow ---- *)
    destruct (c1 + (a * b / 2 ^ 64 + 0) <? 2 ^ 64) eqn:Hc1_carry;
      [apply Z.ltb_lt in Hc1_carry | apply Z.ltb_ge in Hc1_carry].

    * (* Case 1: no carry from c0, no carry from c1.
         All three mods are identities (sums stay < 2^64). *)
      rewrite (Z.mod_small (c0 + _)) by lia.
      rewrite (Z.mod_small (c1 + _)) by lia.
      rewrite (Z.mod_small (c2 + 0)) by lia.
      lia.

    * (* Case 2: no carry from c0, carry from c1.
         c1 mod wraps (subtract 2^64), c2 absorbs +1. *)
      rewrite (Z.mod_small (c0 + _)) by lia.
      replace ((c1 + (a * b / 2 ^ 64 + 0)) mod 2 ^ 64)
        with (c1 + (a * b / 2 ^ 64 + 0) - 2^64)
        by (symmetry; apply Zmod_unique with 1; lia).
      (* c2+1 < 2^64 follows from the accumulator bound + the
         carry meaning c1 + hi >= 2^64. *)
      rewrite (Z.mod_small (c2 + 1)) by nia.
      lia.

  + (* ---- c0 + lo DID overflow ---- *)
    destruct (c1 + (a * b / 2 ^ 64 + 1) <? 2 ^ 64) eqn:Hc1_carry;
      [apply Z.ltb_lt in Hc1_carry | apply Z.ltb_ge in Hc1_carry].

    * (* Case 3: carry from c0, no carry from c1.
         c0 mod wraps, c1 absorbs +1, c2 unchanged. *)
      replace ((c0 + (a * b) mod 2 ^ 64) mod 2 ^ 64)
        with (c0 + (a * b) mod 2 ^ 64 - 2^64)
        by (symmetry; apply Zmod_unique with 1; lia).
      rewrite (Z.mod_small (c1 + _)) by lia.
      rewrite (Z.mod_small (c2 + 0)) by lia.
      lia.

    * (* Case 4: carry from both c0 and c1.
         Both c0 and c1 mods wrap, c2 absorbs +1. *)
      replace ((c0 + (a * b) mod 2 ^ 64) mod 2 ^ 64)
        with (c0 + (a * b) mod 2 ^ 64 - 2^64)
        by (symmetry; apply Zmod_unique with 1; lia).
      replace ((c1 + (a * b / 2 ^ 64 + 1)) mod 2 ^ 64)
        with (c1 + (a * b / 2 ^ 64 + 1) - 2^64)
        by (symmetry; apply Zmod_unique with 1; lia).
      rewrite (Z.mod_small (c2 + 1)) by nia.
      lia.
Qed.

(** [muladd_fast] is the same as [muladd] but leaves c2 untouched.
    The precondition c0 + c1*2^64 + a*b < 2^128 guarantees that c1
    never overflows, so there are only two cases (carry from c0 or not)
    instead of four. *)
Lemma acc_full_muladd_fast : forall c0 c1 c2 a b,
  0 <= c0 <= Int64.max_unsigned ->
  0 <= c1 <= Int64.max_unsigned ->
  0 <= c2 <= Int64.max_unsigned ->
  0 <= a <= Int64.max_unsigned ->
  0 <= b <= Int64.max_unsigned ->
  c0 + c1 * 2^64 + a * b < 2^128 ->
  acc_full (muladd_c0 c0 a b) (muladd_c1 c0 c1 a b) c2
  = acc_full c0 c1 c2 + a * b.
Proof.
  intros c0 c1 c2 a b Hc0 Hc1 Hc2 Ha Hb Hacc.
  (* Expose the raw arithmetic: two [(... + ...) mod 2^64] limbs,
     c2 is untouched. *)
  unfold acc_full in *; unfold muladd_c1, muladd_c0, muladd_th.
  change Int64.max_unsigned with (2^64 - 1) in *.

  (* --- Establish the bounds we will need in every case --- *)

  assert (Hab_mod : 0 <= (a * b) mod 2^64 < 2^64)
    by (apply Z.mod_pos_bound; lia).
  assert (Hab_div : 0 <= (a * b) / 2^64 <= 2^64 - 2).
  { split; [apply Z.div_pos; lia|].
    enough ((a * b) / 2^64 < 2^64 - 1) by lia.
    apply Z.div_lt_upper_bound; [lia|]. nia. }
  pose proof (Z.div_mod (a * b) (2^64) ltac:(lia)) as Hab_decomp.

  (* --- Case-split on the single carry flag --- *)

  destruct (c0 + (a * b) mod 2 ^ 64 <? 2 ^ 64) eqn:Hc0_carry;
    [apply Z.ltb_lt in Hc0_carry | apply Z.ltb_ge in Hc0_carry].

  + (* Case 1: c0 + lo did NOT overflow.
       Both mods are identities. *)
    rewrite (Z.mod_small (c0 + _)) by lia.
    rewrite (Z.mod_small (c1 + _)) by lia.
    lia.

  + (* Case 2: c0 + lo DID overflow.
       c0 mod wraps (subtract 2^64), c1 absorbs the +1.
       c1 + th still fits because c0 + c1*2^64 + a*b < 2^128. *)
    replace ((c0 + (a * b) mod 2 ^ 64) mod 2 ^ 64)
      with (c0 + (a * b) mod 2 ^ 64 - 2^64)
      by (symmetry; apply Zmod_unique with 1; lia).
    rewrite (Z.mod_small (c1 + _)) by lia.
    lia.
Qed.

(** Simpler: acc_full after extract is just c1 + c2 * 2^64. *)
Lemma acc_full_shift : forall c1 c2,
  acc_full c1 c2 0 = c1 + c2 * 2^64.
Proof.
  intros. unfold acc_full. lia.
Qed.

(** acc_full after extract_fast: (c0,c1,c2) → (c1,0,c2). *)
Lemma acc_full_shift_fast : forall c1 c2,
  acc_full c1 0 c2 = c1 + c2 * 2^128.
Proof.
  intros. unfold acc_full. lia.
Qed.

(** Proof outline for [secp256k1_scalar_mul_512].

    The C function computes a 4×4-limb schoolbook multiplication using a
    192-bit accumulator (c0, c1, c2).  Each round adds cross-products
    via [muladd] / [muladd_fast], then shifts the low 64 bits out via
    [extract] / [extract_fast].

    We track the mathematical value [acc_full c0 c1 c2 = c0 + c1·2^64 + c2·2^128]
    as an invariant through every operation:

    1. After each [muladd(a_i, b_j)]:
         acc_full_after = acc_full_before + a_i * b_j
       (proved by [acc_full_muladd]).  This gives a chain of equalities:
         Hacc_rN_0, Hacc_rN_1, …

    2. After each [extract(&l8[k])]:
         The output limb is c0.  The new accumulator is (c1, c2, 0)
         with [acc_full c1 c2 0 = c1 + c2·2^64] (by [acc_full_shift]).
         We record this as Hacc_r(N+1)_init and bound it by the
         previous round's total (Hacc_r(N+1)_init_bound).

    3. Overflow (no-wrap) obligations for each [muladd] are discharged
       by rewriting with the chain back to the round's starting value,
       then solving with [nia].

    4. Range goals [0 <= muladd_cX … <= max_unsigned] generated by
       [forward_call] are solved by [solve_muladd_range] (all three
       components are mod 2^64 results). *)

Lemma body_secp256k1_scalar_mul_512:
  semax_body Vprog Gprog f_secp256k1_scalar_mul_512 secp256k1_scalar_mul_512_spec.
Proof.
  start_function.

  (* acc = {0, 0, 0} *)
  do 3 forward.

  (* Need to fold the expanded acc struct into acc_val form for forward_call *)
  autorewrite with norm.
  change (Vlong (Int64.repr 0), (Vlong (Int64.repr 0), Vlong (Int64.repr 0)))
    with (acc_val 0 0 0).

  (* Abbreviate the scalar limbs for readability *)
  set (a0 := Znth 0 a) in *.
  set (a1 := Znth 1 a) in *.
  set (a2 := Znth 2 a) in *.
  set (a3 := Znth 3 a) in *.
  set (b0 := Znth 0 b) in *.
  set (b1 := Znth 1 b) in *.
  set (b2 := Znth 2 b) in *.
  set (b3 := Znth 3 b) in *.

  (* Limb range facts *)
  assert (Ha0 : 0 <= a0 <= Int64.max_unsigned)
    by (subst a0; apply (proj1 (Forall_Znth a _) H1 0); lia).
  assert (Ha1 : 0 <= a1 <= Int64.max_unsigned)
    by (subst a1; apply (proj1 (Forall_Znth a _) H1 1); lia).
  assert (Ha2 : 0 <= a2 <= Int64.max_unsigned)
    by (subst a2; apply (proj1 (Forall_Znth a _) H1 2); lia).
  assert (Ha3 : 0 <= a3 <= Int64.max_unsigned)
    by (subst a3; apply (proj1 (Forall_Znth a _) H1 3); lia).
  assert (Hb0 : 0 <= b0 <= Int64.max_unsigned)
    by (subst b0; apply (proj1 (Forall_Znth b _) H2 0); lia).
  assert (Hb1 : 0 <= b1 <= Int64.max_unsigned)
    by (subst b1; apply (proj1 (Forall_Znth b _) H2 1); lia).
  assert (Hb2 : 0 <= b2 <= Int64.max_unsigned)
    by (subst b2; apply (proj1 (Forall_Znth b _) H2 2); lia).
  assert (Hb3 : 0 <= b3 <= Int64.max_unsigned)
    by (subst b3; apply (proj1 (Forall_Znth b _) H2 3); lia).

  (* Decompose a and b into their limbs *)
  assert (Ha_eq : a = [a0; a1; a2; a3])
    by (subst a0 a1 a2 a3; apply list_Z_Zlength_4; auto).
  assert (Hb_eq : b = [b0; b1; b2; b3])
    by (subst b0 b1 b2 b3; apply list_Z_Zlength_4; auto).

  rewrite Ha_eq, Hb_eq in *.
  clearbody a0 a1 a2 a3 b0 b1 b2 b3.
  clear H H0 H1 H2.

  (* Product bounds: every ai*bj < 2^128 *)
  assert (Hmul_a0b0 : a0 * b0 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a0b1 : a0 * b1 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a0b2 : a0 * b2 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a0b3 : a0 * b3 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a1b0 : a1 * b0 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a1b1 : a1 * b1 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a1b2 : a1 * b2 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a1b3 : a1 * b3 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a2b0 : a2 * b0 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a2b1 : a2 * b1 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a2b2 : a2 * b2 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a2b3 : a2 * b3 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a3b0 : a3 * b0 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a3b1 : a3 * b1 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a3b2 : a3 * b2 < 2^128) by (apply mul_64_64_lt_128; rep_lia).
  assert (Hmul_a3b3 : a3 * b3 < 2^128) by (apply mul_64_64_lt_128; rep_lia).

  (* a0 = a->d[0], b0 = b->d[0] *)
  forward. 
  forward.

  (* muladd_fast(&acc, a0, b0) *)
  forward_call (v_acc, a0, b0, 0, 0, 0, Tsh).

  (* Track acc_full through round 0 *)
  assert (Hacc_r0 : acc_full (muladd_c0 0 a0 b0) (muladd_c1 0 0 a0 b0) 0
    = a0 * b0).
  { rewrite (acc_full_muladd_fast 0 0 0 a0 b0); try lia.
    unfold acc_full. 
    lia. }


  (* Establish field_compatible for the l8 array — needed for address matching *)
  assert_PROP (field_compatible (tarray tulong 8) [] l8_ptr) as Hfc by entailer!.

  (* extract_fast(&acc, &l8[0]) *)
  forward_call (v_acc, field_address (tarray tulong 8) [ArraySubsc 0] l8_ptr,
                muladd_c0 0 a0 b0,
                muladd_c1 0 0 a0 b0,
                0, Tsh, sh_l).
  { (* parameter matching *)
    entailer!.
    simpl firstn. 
    f_equal; f_equal.
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_offset.
    rewrite isptr_offset_val_zero; auto. }
  { (* frame: split l8[0] out of the 8-element array *)
    rewrite (arr_field_address tulong 8 l8_ptr 0 Hfc) by lia.
    simpl Z.mul. 
    rewrite isptr_offset_val_zero by (eapply field_compatible_isptr; eauto).
    rewrite (split2_data_at__Tarray_app 1 8 sh_l tulong l8_ptr) by lia.
    rewrite data__at_singleton_array_eq.
    cancel. }
  { (* bounds *)
     split; [unfold muladd_c0 | unfold muladd_c1]; apply mod_64_range. }
  
  deadvars!; simpl. 
    
  (* Abbreviate the extracted value for l8[0] *)
  set (r0_c0 := muladd_c0 0 a0 b0) in *.

  (* Abbreviate the accumulator input to round 1 *)
  set (r1_c0_in := muladd_c1 0 0 a0 b0) in *.

  (* After extract_fast, acc = (r1_c0_in, 0, 0) *)
  assert (Hacc_r1_init : acc_full r1_c0_in 0 0 = r1_c0_in).
  { unfold acc_full. lia. }

  (* Bound: r1_c0_in < 2^64 (since it's a mod 2^64 result) *)
  assert (Hr1_c0_in_range : 0 <= r1_c0_in <= Int64.max_unsigned).
  { subst r1_c0_in. unfold muladd_c1. apply mod_64_range. }

  (* Bound: acc_full before extract_fast was a0*b0, so r1_c0_in ≤ a0*b0 *)
  assert (Hacc_r1_init_bound : acc_full r1_c0_in 0 0 <= a0 * b0).
  { rewrite Hacc_r1_init.
    (* From Hacc_r0: muladd_c0 0 a0 b0 + r1_c0_in * 2^64 = a0*b0 *)
    assert (Hacc_r0' := Hacc_r0).
    unfold acc_full in Hacc_r0'. 
    (* muladd_c0 0 a0 b0 ≥ 0 *)
    assert (0 <= muladd_c0 0 a0 b0) by (unfold muladd_c0; apply Z.mod_pos_bound; lia).
    lia. }

  (* a1 = a->d[1], b1 = b->d[1] *)
  forward.
  forward.

  (* muladd(&acc, a0, b1) *)
  forward_call (v_acc, a0, b1,
                r1_c0_in, 0, 0, Tsh).
      
  deadvars!; simpl. 
  
  (* Abbreviate accumulator state after muladd(a0, b1) *)
  set (r1_c0_mid := muladd_c0 r1_c0_in a0 b1) in *.
  set (r1_c1_mid := muladd_c1 r1_c0_in 0 a0 b1) in *.
  set (r1_c2_mid := muladd_c2 r1_c0_in 0 0 a0 b1) in *.

  (* Track acc_full through muladd(a0, b1) *)
  assert (Hacc_r1_0 : acc_full r1_c0_mid r1_c1_mid r1_c2_mid
    = acc_full r1_c0_in 0 0 + a0 * b1).
  { subst r1_c0_mid r1_c1_mid r1_c2_mid.
    apply acc_full_muladd; try lia. }

  (* a1 = a->d[1], b0 = b->d[0] *)
  forward.
  forward.

  (* muladd(&acc, a1, b0) *)
  forward_call (v_acc, a1, b0,
                r1_c0_mid, r1_c1_mid, r1_c2_mid, Tsh).
  { (* range + overflow *)
    subst r1_c0_mid r1_c1_mid r1_c2_mid.
    repeat split; try solve_muladd_range. }

  deadvars!; simpl. 
        
  (* Abbreviate accumulator state after muladd(a1, b0) *)
  set (r1_c0 := muladd_c0 r1_c0_mid a1 b0) in *.
  set (r1_c1 := muladd_c1 r1_c0_mid r1_c1_mid a1 b0) in *.
  set (r1_c2 := muladd_c2 r1_c0_mid r1_c1_mid r1_c2_mid a1 b0) in *.

  (* Track acc_full through muladd(a1, b0) *)
  assert (Hacc_r1_1 : acc_full r1_c0 r1_c1 r1_c2
    = acc_full r1_c0_mid r1_c1_mid r1_c2_mid + a1 * b0).
  { subst r1_c0 r1_c1 r1_c2.
    apply acc_full_muladd; try lia.
    - subst r1_c0_mid. unfold muladd_c0. apply mod_64_range.
    - subst r1_c1_mid. unfold muladd_c1. apply mod_64_range.
    - subst r1_c2_mid. unfold muladd_c2. apply mod_64_range. }

  (* Full chain for round 1: acc_full = r1_c0_in + a0*b1 + a1*b0 *)
  assert (Hacc_r1 : acc_full r1_c0 r1_c1 r1_c2
    = r1_c0_in + a0 * b1 + a1 * b0).
  { rewrite Hacc_r1_1, Hacc_r1_0, Hacc_r1_init. lia. }

  (* extract(&acc, &l8[1]) *)
  forward_call (v_acc, field_address (tarray tulong 8) [ArraySubsc 1] l8_ptr,
                r1_c0, r1_c1, r1_c2, Tsh, sh_l).
  { (* 1: frame - extract l8[1] from the 7-element sub-array *)
    rewrite (split2_data_at__Tarray_app 1 7 sh_l tulong
               (field_address0 (tarray tulong 8) (SUB 1) l8_ptr)) by lia.
    rewrite data__at_singleton_array_eq.
    rewrite (arr_field_address0 tulong 8 l8_ptr 1 Hfc) by lia.
    rewrite (arr_field_address tulong 8 l8_ptr 1 Hfc) by lia.
    cancel. } 
  { (* 2: bounds *)
    repeat split;
    subst r1_c0 r1_c1 r1_c2;
    try (unfold muladd_c0; apply mod_64_range);
    try (unfold muladd_c1; apply mod_64_range);
    try (unfold muladd_c2; apply mod_64_range). }

  (* After extract, acc = (r1_c1, r1_c2, 0) *)
  assert (Hacc_r2_init : acc_full r1_c1 r1_c2 0 = r1_c1 + r1_c2 * 2^64).
  { apply acc_full_shift. }

  (* Bound: acc_full(r1_c1, r1_c2, 0) ≤ acc_full(r1_c0, r1_c1, r1_c2) < the round 1 total *)
  assert (Hacc_r2_init_bound : acc_full r1_c1 r1_c2 0 <= r1_c0_in + a0 * b1 + a1 * b0).
  { rewrite Hacc_r2_init.
    assert (acc_full r1_c0 r1_c1 r1_c2 = r1_c0_in + a0 * b1 + a1 * b0) by exact Hacc_r1.
    unfold acc_full in H.
    assert (0 <= r1_c0) by (subst r1_c0; unfold muladd_c0; apply Z.mod_pos_bound; lia).
    lia. }
    
  (* a0 = a->d[0], b2 = b->d[2] *)
  forward.
  forward.
  
  (* muladd(&acc, a0, b2) *)
  forward_call (v_acc, a0, b2,
                r1_c1, r1_c2, 0, Tsh).
  { subst r1_c1 r1_c2.
    repeat split; try solve_muladd_range; try lia. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a0, b2) *)
  set (r2_c0_0 := muladd_c0 r1_c1 a0 b2) in *.
  set (r2_c1_0 := muladd_c1 r1_c1 r1_c2 a0 b2) in *.
  set (r2_c2_0 := muladd_c2 r1_c1 r1_c2 0 a0 b2) in *.

  (* Track acc_full through muladd(a0, b2) *)
  assert (Hacc_r2_0 : acc_full r2_c0_0 r2_c1_0 r2_c2_0
    = acc_full r1_c1 r1_c2 0 + a0 * b2).
  { subst r2_c0_0 r2_c1_0 r2_c2_0.
    apply acc_full_muladd; try lia.
    - subst r1_c1. unfold muladd_c1. apply mod_64_range.
    - subst r1_c2. unfold muladd_c2. apply mod_64_range. }

  (* a1 = a->d[1], b1 = b->d[1] *)
  forward.
  forward.

  (* muladd(&acc, a1, b1) *)
  forward_call (v_acc, a1, b1,
                r2_c0_0, r2_c1_0, r2_c2_0, Tsh).
  { subst r2_c0_0 r2_c1_0 r2_c2_0.
    repeat split; try solve_muladd_range. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a1, b1) *)
  set (r2_c0_1 := muladd_c0 r2_c0_0 a1 b1) in *.
  set (r2_c1_1 := muladd_c1 r2_c0_0 r2_c1_0 a1 b1) in *.
  set (r2_c2_1 := muladd_c2 r2_c0_0 r2_c1_0 r2_c2_0 a1 b1) in *.

  (* Track acc_full through muladd(a1, b1) *)
  assert (Hacc_r2_1 : acc_full r2_c0_1 r2_c1_1 r2_c2_1
    = acc_full r2_c0_0 r2_c1_0 r2_c2_0 + a1 * b1).
  { subst r2_c0_1 r2_c1_1 r2_c2_1.
    apply acc_full_muladd; try lia.
    - subst r2_c0_0. unfold muladd_c0. apply mod_64_range.
    - subst r2_c1_0. unfold muladd_c1. apply mod_64_range.
    - subst r2_c2_0. unfold muladd_c2. apply mod_64_range. }

  (* a2 = a->d[2], b0 = b->d[0] *)
  forward.
  forward.

  (* muladd(&acc, a2, b0) *)
  forward_call (v_acc, a2, b0,
                r2_c0_1, r2_c1_1, r2_c2_1, Tsh).
  { subst r2_c0_1 r2_c1_1 r2_c2_1.
    repeat split; try solve_muladd_range. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a2, b0) *)
  set (r2_c0 := muladd_c0 r2_c0_1 a2 b0) in *.
  set (r2_c1 := muladd_c1 r2_c0_1 r2_c1_1 a2 b0) in *.
  set (r2_c2 := muladd_c2 r2_c0_1 r2_c1_1 r2_c2_1 a2 b0) in *.

  (* Track acc_full through muladd(a2, b0) *)
  assert (Hacc_r2_2 : acc_full r2_c0 r2_c1 r2_c2
    = acc_full r2_c0_1 r2_c1_1 r2_c2_1 + a2 * b0).
  { subst r2_c0 r2_c1 r2_c2.
    apply acc_full_muladd; try lia.
    - subst r2_c0_1. unfold muladd_c0. apply mod_64_range.
    - subst r2_c1_1. unfold muladd_c1. apply mod_64_range.
    - subst r2_c2_1. unfold muladd_c2. apply mod_64_range. }

  (* Full chain for round 2 *)
  assert (Hacc_r2 : acc_full r2_c0 r2_c1 r2_c2
    = acc_full r1_c1 r1_c2 0 + a0 * b2 + a1 * b1 + a2 * b0).
  { rewrite Hacc_r2_2, Hacc_r2_1, Hacc_r2_0. lia. }

  (* extract(&acc, &l8[2]) *)
  forward_call (v_acc, field_address (tarray tulong 8) [ArraySubsc 2] l8_ptr,
                r2_c0, r2_c1, r2_c2, Tsh, sh_l).
  { (* frame: peel l8[2] out of the 6-element sub-array *)
    (* Step 1: Normalize nested field_address0 to parent coordinates.
       The sub-array rest lives at:
         field_address0 (tarray tulong 7) (SUB 1) (offset_val 8 l8_ptr)
       First rewrite offset_val 8 = field_address0 (tarray tulong 8) (SUB 1),
       then collapse with field_address0_SUB_SUB. *)
    change (offset_val 8 l8_ptr)
      with (offset_val (sizeof tulong * 1) l8_ptr).
    rewrite <- (arr_field_address0 tulong 8 l8_ptr 1 Hfc) by lia.
    rewrite (field_address0_SUB_SUB tulong 7 8 1 1 l8_ptr) by lia.
    (* Now the 6-element sub-array is at field_address0 (tarray tulong 8) (SUB 2) l8_ptr *)
    (* Step 2: Split 6-element sub-array into 1 + 5 *)
    rewrite (split2_data_at__Tarray_app 1 6 sh_l tulong
               (field_address0 (tarray tulong 8) (SUB 2) l8_ptr)) by lia.
    (* Step 3: Collapse the singleton *)
    rewrite data__at_singleton_array_eq.
    (* Step 4: Normalize addresses to match *)
    rewrite (arr_field_address0 tulong 8 l8_ptr 2 Hfc) by lia.
    rewrite (arr_field_address tulong 8 l8_ptr 2 Hfc) by lia.
    cancel. }
  { repeat split;
    subst r2_c0 r2_c1 r2_c2;
    try (unfold muladd_c0; apply mod_64_range);
    try (unfold muladd_c1; apply mod_64_range);
    try (unfold muladd_c2; apply mod_64_range). }

  (* After extract, acc = (r2_c1, r2_c2, 0) *)
  assert (Hacc_r3_init : acc_full r2_c1 r2_c2 0 = r2_c1 + r2_c2 * 2^64).
  { apply acc_full_shift. }

  assert (Hacc_r3_init_bound : acc_full r2_c1 r2_c2 0
    <= acc_full r1_c1 r1_c2 0 + a0 * b2 + a1 * b1 + a2 * b0).
  { rewrite <- Hacc_r2.
    unfold acc_full.
    assert (0 <= r2_c0) by (subst r2_c1; unfold muladd_c0; apply Z.mod_pos_bound; lia).
    assert (0 <= r2_c1) by (subst r2_c1; unfold muladd_c0; apply Z.mod_pos_bound; lia).
    assert (0 <= r2_c2) by (subst r2_c2; unfold muladd_c2; apply Z.mod_pos_bound; lia).
    rep_lia. }

  (* a0 = a->d[0], b3 = b->d[3] *)
  forward.
  forward.

  (* muladd(&acc, a0, b3) *)
  forward_call (v_acc, a0, b3,
                r2_c1, r2_c2, 0, Tsh).
  { subst r2_c1 r2_c2.
    repeat split; try solve_muladd_range; try lia. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a0, b3) *)
  set (r3_c0_0 := muladd_c0 r2_c1 a0 b3) in *.
  set (r3_c1_0 := muladd_c1 r2_c1 r2_c2 a0 b3) in *.
  set (r3_c2_0 := muladd_c2 r2_c1 r2_c2 0 a0 b3) in *.

  (* Track acc_full through muladd(a0, b3) *)
  assert (Hacc_r3_0 : acc_full r3_c0_0 r3_c1_0 r3_c2_0
    = acc_full r2_c1 r2_c2 0 + a0 * b3).
  { subst r3_c0_0 r3_c1_0 r3_c2_0.
    apply acc_full_muladd; try lia.
    - subst r2_c1. unfold muladd_c1. apply mod_64_range.
    - subst r2_c2. unfold muladd_c2. apply mod_64_range. }

  (* a1 = a->d[1], b2 = b->d[2] *)
  forward.
  forward.

  (* muladd(&acc, a1, b2) *)
  forward_call (v_acc, a1, b2,
                r3_c0_0, r3_c1_0, r3_c2_0, Tsh).
  { subst r3_c0_0 r3_c1_0 r3_c2_0.
    repeat split; try solve_muladd_range. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a1, b2) *)
  set (r3_c0_1 := muladd_c0 r3_c0_0 a1 b2) in *.
  set (r3_c1_1 := muladd_c1 r3_c0_0 r3_c1_0 a1 b2) in *.
  set (r3_c2_1 := muladd_c2 r3_c0_0 r3_c1_0 r3_c2_0 a1 b2) in *.

  (* Track acc_full through muladd(a1, b2) *)
  assert (Hacc_r3_1 : acc_full r3_c0_1 r3_c1_1 r3_c2_1
    = acc_full r3_c0_0 r3_c1_0 r3_c2_0 + a1 * b2).
  { subst r3_c0_1 r3_c1_1 r3_c2_1.
    apply acc_full_muladd; try lia.
    - subst r3_c0_0. unfold muladd_c0. apply mod_64_range.
    - subst r3_c1_0. unfold muladd_c1. apply mod_64_range.
    - subst r3_c2_0. unfold muladd_c2. apply mod_64_range. }

  (* a2 = a->d[2], b1 = b->d[1] *)
  forward.
  forward.

  (* muladd(&acc, a2, b1) *)
  forward_call (v_acc, a2, b1,
                r3_c0_1, r3_c1_1, r3_c2_1, Tsh).
  { subst r3_c0_1 r3_c1_1 r3_c2_1.
    repeat split; try solve_muladd_range. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a2, b1) *)
  set (r3_c0_2 := muladd_c0 r3_c0_1 a2 b1) in *.
  set (r3_c1_2 := muladd_c1 r3_c0_1 r3_c1_1 a2 b1) in *.
  set (r3_c2_2 := muladd_c2 r3_c0_1 r3_c1_1 r3_c2_1 a2 b1) in *.

  (* Track acc_full through muladd(a2, b1) *)
  assert (Hacc_r3_2 : acc_full r3_c0_2 r3_c1_2 r3_c2_2
    = acc_full r3_c0_1 r3_c1_1 r3_c2_1 + a2 * b1).
  { subst r3_c0_2 r3_c1_2 r3_c2_2.
    apply acc_full_muladd; try lia.
    - subst r3_c0_1. unfold muladd_c0. apply mod_64_range.
    - subst r3_c1_1. unfold muladd_c1. apply mod_64_range.
    - subst r3_c2_1. unfold muladd_c2. apply mod_64_range. }

  (* a3 = a->d[3], b0 = b->d[0] *)
  forward.
  forward.

  (* muladd(&acc, a3, b0) *)
  forward_call (v_acc, a3, b0,
                r3_c0_2, r3_c1_2, r3_c2_2, Tsh).
  { subst r3_c0_2 r3_c1_2 r3_c2_2.
    repeat split; try solve_muladd_range. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a3, b0) *)
  set (r3_c0 := muladd_c0 r3_c0_2 a3 b0) in *.
  set (r3_c1 := muladd_c1 r3_c0_2 r3_c1_2 a3 b0) in *.
  set (r3_c2 := muladd_c2 r3_c0_2 r3_c1_2 r3_c2_2 a3 b0) in *.

  (* Track acc_full through muladd(a3, b0) *)
  assert (Hacc_r3_3 : acc_full r3_c0 r3_c1 r3_c2
    = acc_full r3_c0_2 r3_c1_2 r3_c2_2 + a3 * b0).
  { subst r3_c0 r3_c1 r3_c2.
    apply acc_full_muladd; try lia.
    - subst r3_c0_2. unfold muladd_c0. apply mod_64_range.
    - subst r3_c1_2. unfold muladd_c1. apply mod_64_range.
    - subst r3_c2_2. unfold muladd_c2. apply mod_64_range. }

  (* Full chain for round 3 *)
  assert (Hacc_r3 : acc_full r3_c0 r3_c1 r3_c2
    = acc_full r2_c1 r2_c2 0 + a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0).
  { rewrite Hacc_r3_3, Hacc_r3_2, Hacc_r3_1, Hacc_r3_0. lia. }

  (* extract(&acc, &l8[3]) *)
  forward_call (v_acc, field_address (tarray tulong 8) [ArraySubsc 3] l8_ptr,
                r3_c0, r3_c1, r3_c2, Tsh, sh_l).
  { (* frame: peel l8[3] out of the 5-element sub-array *)
    change (offset_val 16 l8_ptr)
      with (offset_val (sizeof tulong * 2) l8_ptr).
    rewrite <- (arr_field_address0 tulong 8 l8_ptr 2 Hfc) by lia.
    rewrite (field_address0_SUB_SUB tulong 6 8 1 2 l8_ptr) by lia.
    rewrite (split2_data_at__Tarray_app 1 5 sh_l tulong
               (field_address0 (tarray tulong 8) (SUB 3) l8_ptr)) by lia.
    rewrite data__at_singleton_array_eq.
    rewrite (arr_field_address0 tulong 8 l8_ptr 3 Hfc) by lia.
    rewrite (arr_field_address tulong 8 l8_ptr 3 Hfc) by lia.
    cancel. }
  { repeat split;
    subst r3_c0 r3_c1 r3_c2;
    try (unfold muladd_c0; apply mod_64_range);
    try (unfold muladd_c1; apply mod_64_range);
    try (unfold muladd_c2; apply mod_64_range). }

  (* After extract, acc = (r3_c1, r3_c2, 0) *)
  assert (Hacc_r4_init : acc_full r3_c1 r3_c2 0 = r3_c1 + r3_c2 * 2^64).
  { apply acc_full_shift. }

  assert (Hacc_r4_init_bound : acc_full r3_c1 r3_c2 0
    <= acc_full r2_c1 r2_c2 0 + a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0).
  { rewrite <- Hacc_r3.
    unfold acc_full.
    simpl (0 * _).
    rewrite Z.add_0_r.
    assert (0 <= r3_c0) by (subst r3_c0; unfold muladd_c0; apply Z.mod_pos_bound; lia).
    assert (0 <= r3_c1) by (subst r3_c1; unfold muladd_c1; apply Z.mod_pos_bound; lia).
    assert (0 <= r3_c2) by (subst r3_c2; unfold muladd_c2; apply Z.mod_pos_bound; lia).
    rep_lia. }

  (* a1 = a->d[1], b3 = b->d[3] *)
  forward.
  forward.

  (* muladd(&acc, a1, b3) *)
  forward_call (v_acc, a1, b3,
                r3_c1, r3_c2, 0, Tsh).
  { subst r3_c1 r3_c2.
    repeat split; try solve_muladd_range; try lia. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a1, b3) *)
  set (r4_c0_0 := muladd_c0 r3_c1 a1 b3) in *.
  set (r4_c1_0 := muladd_c1 r3_c1 r3_c2 a1 b3) in *.
  set (r4_c2_0 := muladd_c2 r3_c1 r3_c2 0 a1 b3) in *.

  (* Track acc_full through muladd(a1, b3) *)
  assert (Hacc_r4_0 : acc_full r4_c0_0 r4_c1_0 r4_c2_0
    = acc_full r3_c1 r3_c2 0 + a1 * b3).
  { subst r4_c0_0 r4_c1_0 r4_c2_0.
    apply acc_full_muladd; try lia.
    - subst r3_c1. unfold muladd_c1. apply mod_64_range.
    - subst r3_c2. unfold muladd_c2. apply mod_64_range. }

  (* a2 = a->d[2], b2 = b->d[2] *)
  forward.
  forward.

  (* muladd(&acc, a2, b2) *)
  forward_call (v_acc, a2, b2,
                r4_c0_0, r4_c1_0, r4_c2_0, Tsh).
  { subst r4_c0_0 r4_c1_0 r4_c2_0.
    repeat split; try solve_muladd_range. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a2, b2) *)
  set (r4_c0_1 := muladd_c0 r4_c0_0 a2 b2) in *.
  set (r4_c1_1 := muladd_c1 r4_c0_0 r4_c1_0 a2 b2) in *.
  set (r4_c2_1 := muladd_c2 r4_c0_0 r4_c1_0 r4_c2_0 a2 b2) in *.

  (* Track acc_full through muladd(a2, b2) *)
  assert (Hacc_r4_1 : acc_full r4_c0_1 r4_c1_1 r4_c2_1
    = acc_full r4_c0_0 r4_c1_0 r4_c2_0 + a2 * b2).
  { subst r4_c0_1 r4_c1_1 r4_c2_1.
    apply acc_full_muladd; try lia.
    - subst r4_c0_0. unfold muladd_c0. apply mod_64_range.
    - subst r4_c1_0. unfold muladd_c1. apply mod_64_range.
    - subst r4_c2_0. unfold muladd_c2. apply mod_64_range. }

  (* a3 = a->d[3], b1 = b->d[1] *)
  forward.
  forward.

  (* muladd(&acc, a3, b1) *)
  forward_call (v_acc, a3, b1,
                r4_c0_1, r4_c1_1, r4_c2_1, Tsh).
  { subst r4_c0_1 r4_c1_1 r4_c2_1.
    repeat split; try solve_muladd_range. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a3, b1) *)
  set (r4_c0 := muladd_c0 r4_c0_1 a3 b1) in *.
  set (r4_c1 := muladd_c1 r4_c0_1 r4_c1_1 a3 b1) in *.
  set (r4_c2 := muladd_c2 r4_c0_1 r4_c1_1 r4_c2_1 a3 b1) in *.

  (* Track acc_full through muladd(a3, b1) *)
  assert (Hacc_r4_2 : acc_full r4_c0 r4_c1 r4_c2
    = acc_full r4_c0_1 r4_c1_1 r4_c2_1 + a3 * b1).
  { subst r4_c0 r4_c1 r4_c2.
    apply acc_full_muladd; try lia.
    - subst r4_c0_1. unfold muladd_c0. apply mod_64_range.
    - subst r4_c1_1. unfold muladd_c1. apply mod_64_range.
    - subst r4_c2_1. unfold muladd_c2. apply mod_64_range. }

  (* Full chain for round 4 *)
  assert (Hacc_r4 : acc_full r4_c0 r4_c1 r4_c2
    = acc_full r3_c1 r3_c2 0 + a1 * b3 + a2 * b2 + a3 * b1).
  { rewrite Hacc_r4_2, Hacc_r4_1, Hacc_r4_0. lia. }

  (* extract(&acc, &l8[4]) *)
  forward_call (v_acc, field_address (tarray tulong 8) [ArraySubsc 4] l8_ptr,
                r4_c0, r4_c1, r4_c2, Tsh, sh_l).
  { (* frame: peel l8[4] out of the 4-element sub-array *)
    change (offset_val 24 l8_ptr)
      with (offset_val (sizeof tulong * 3) l8_ptr).
    rewrite <- (arr_field_address0 tulong 8 l8_ptr 3 Hfc) by lia.
    rewrite (field_address0_SUB_SUB tulong 5 8 1 3 l8_ptr) by lia.
    rewrite (split2_data_at__Tarray_app 1 4 sh_l tulong
               (field_address0 (tarray tulong 8) (SUB 4) l8_ptr)) by lia.
    rewrite data__at_singleton_array_eq.
    rewrite (arr_field_address0 tulong 8 l8_ptr 4 Hfc) by lia.
    rewrite (arr_field_address tulong 8 l8_ptr 4 Hfc) by lia.
    cancel. }
  { repeat split;
    subst r4_c0 r4_c1 r4_c2;
    try (unfold muladd_c0; apply mod_64_range);
    try (unfold muladd_c1; apply mod_64_range);
    try (unfold muladd_c2; apply mod_64_range). }

  (* After extract, acc = (r4_c1, r4_c2, 0) *)
  assert (Hacc_r5_init : acc_full r4_c1 r4_c2 0 = r4_c1 + r4_c2 * 2^64).
  { apply acc_full_shift. }

  assert (Hacc_r5_init_bound : acc_full r4_c1 r4_c2 0
    <= acc_full r3_c1 r3_c2 0 + a1 * b3 + a2 * b2 + a3 * b1).
  { rewrite <- Hacc_r4.
    unfold acc_full.
    simpl (0 * _).
    rewrite Z.add_0_r.
    assert (0 <= r4_c0) by (subst r4_c0; unfold muladd_c0; apply Z.mod_pos_bound; lia).
    assert (0 <= r4_c1) by (subst r4_c1; unfold muladd_c1; apply Z.mod_pos_bound; lia).
    assert (0 <= r4_c2) by (subst r4_c2; unfold muladd_c2; apply Z.mod_pos_bound; lia).
    rep_lia. }

  (* a2 = a->d[2], b3 = b->d[3] *)
  forward.
  forward.

  (* muladd(&acc, a2, b3) *)
  forward_call (v_acc, a2, b3,
                r4_c1, r4_c2, 0, Tsh).
  { subst r4_c1 r4_c2.
    repeat split; try solve_muladd_range; try lia. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a2, b3) *)
  set (r5_c0_0 := muladd_c0 r4_c1 a2 b3) in *.
  set (r5_c1_0 := muladd_c1 r4_c1 r4_c2 a2 b3) in *.
  set (r5_c2_0 := muladd_c2 r4_c1 r4_c2 0 a2 b3) in *.

  (* Track acc_full through muladd(a2, b3) *)
  assert (Hacc_r5_0 : acc_full r5_c0_0 r5_c1_0 r5_c2_0
    = acc_full r4_c1 r4_c2 0 + a2 * b3).
  { subst r5_c0_0 r5_c1_0 r5_c2_0.
    apply acc_full_muladd; try lia.
    - subst r4_c1. unfold muladd_c1. apply mod_64_range.
    - subst r4_c2. unfold muladd_c2. apply mod_64_range. }

  (* a3 = a->d[3], b2 = b->d[2] *)
  forward.
  forward.

  (* muladd(&acc, a3, b2) *)
  forward_call (v_acc, a3, b2,
                r5_c0_0, r5_c1_0, r5_c2_0, Tsh).
  { subst r5_c0_0 r5_c1_0 r5_c2_0.
    repeat split; try solve_muladd_range. }

  deadvars!; simpl.

  (* Abbreviate accumulator state after muladd(a3, b2) *)
  set (r5_c0 := muladd_c0 r5_c0_0 a3 b2) in *.
  set (r5_c1 := muladd_c1 r5_c0_0 r5_c1_0 a3 b2) in *.
  set (r5_c2 := muladd_c2 r5_c0_0 r5_c1_0 r5_c2_0 a3 b2) in *.

  (* Track acc_full through muladd(a3, b2) *)
  assert (Hacc_r5_1 : acc_full r5_c0 r5_c1 r5_c2
    = acc_full r5_c0_0 r5_c1_0 r5_c2_0 + a3 * b2).
  { subst r5_c0 r5_c1 r5_c2.
    apply acc_full_muladd; try lia.
    - subst r5_c0_0. unfold muladd_c0. apply mod_64_range.
    - subst r5_c1_0. unfold muladd_c1. apply mod_64_range.
    - subst r5_c2_0. unfold muladd_c2. apply mod_64_range. }

  (* Full chain for round 5 *)
  assert (Hacc_r5 : acc_full r5_c0 r5_c1 r5_c2
    = acc_full r4_c1 r4_c2 0 + a2 * b3 + a3 * b2).
  { rewrite Hacc_r5_1, Hacc_r5_0. lia. }

  (* extract(&acc, &l8[5]) *)
  forward_call (v_acc, field_address (tarray tulong 8) [ArraySubsc 5] l8_ptr,
                r5_c0, r5_c1, r5_c2, Tsh, sh_l).
  { (* frame: peel l8[5] out of the 3-element sub-array *)
    change (offset_val 32 l8_ptr)
      with (offset_val (sizeof tulong * 4) l8_ptr).
    rewrite <- (arr_field_address0 tulong 8 l8_ptr 4 Hfc) by lia.
    rewrite (field_address0_SUB_SUB tulong 4 8 1 4 l8_ptr) by lia.
    rewrite (split2_data_at__Tarray_app 1 3 sh_l tulong
               (field_address0 (tarray tulong 8) (SUB 5) l8_ptr)) by lia.
    rewrite data__at_singleton_array_eq.
    rewrite (arr_field_address0 tulong 8 l8_ptr 5 Hfc) by lia.
    rewrite (arr_field_address tulong 8 l8_ptr 5 Hfc) by lia.
    cancel. }
  { repeat split;
    subst r5_c0 r5_c1 r5_c2;
    try (unfold muladd_c0; apply mod_64_range);
    try (unfold muladd_c1; apply mod_64_range);
    try (unfold muladd_c2; apply mod_64_range). }

  (* After extract, acc = (r5_c1, r5_c2, 0) *)
  assert (Hacc_r6_init : acc_full r5_c1 r5_c2 0 = r5_c1 + r5_c2 * 2^64).
  { apply acc_full_shift. }

  assert (Hacc_r6_init_bound : acc_full r5_c1 r5_c2 0
    <= acc_full r4_c1 r4_c2 0 + a2 * b3 + a3 * b2).
  { rewrite <- Hacc_r5.
    unfold acc_full.
    simpl (0 * _).
    rewrite Z.add_0_r.
    assert (0 <= r5_c0) by (subst r5_c0; unfold muladd_c0; apply Z.mod_pos_bound; lia).
    assert (0 <= r5_c1) by (subst r5_c1; unfold muladd_c1; apply Z.mod_pos_bound; lia).
    assert (0 <= r5_c2) by (subst r5_c2; unfold muladd_c2; apply Z.mod_pos_bound; lia).
    rep_lia. }

  (* a3 = a->d[3], b3 = b->d[3] *)
  forward.
  forward.

  (* The accumulator + a3*b3 fits in 128 bits — needed for muladd_fast *)
  assert (Hr6_bound : r5_c1 + r5_c2 * 2^64 + a3 * b3 < 2^128).
  { (* Strategy: bound each carry tightly using carry_k * 2^64 <= total_k,
       which follows from acc_full c0 c1 c2 = total and c0 >= 0.
       Then derive concrete integer upper bounds on each carry, step by step.
       Let B = 2^64, M = B-1.  Each ai*bj <= M*M = B^2 - 2B + 1.

       Round 0 (1 product):  c0 * B <= a0*b0 <= M^2
                              => c0 <= (M^2) / B = B - 2
       Round 1 (2 products): c1 * B <= c0 + 2*M^2 <= (B-2) + 2*M^2 = 2B^2 - 3B
                              => c1 <= 2B - 3
       Round 2 (3 products): c2 * B <= c1 + 3*M^2 <= (2B-3) + 3*M^2 = 3B^2 - 4B - 2 + B
                              Careful: (2B-3) + 3*(B^2-2B+1) = 3B^2 - 4B
                              => c2 <= 3B - 4
       Round 3 (4 products): c3 * B <= c2 + 4*M^2 <= (3B-4) + 4*(B^2-2B+1) = 4B^2 - 5B
                              => c3 <= 4B - 5
       Round 4 (3 products): c4 * B <= c3 + 3*M^2 <= (4B-5) + 3*(B^2-2B+1) = 3B^2 - 2B - 2
                              => c4 <= (3B^2 - 2B - 2) / B = 3B - 3  (since 2B+2 > B)
       Round 5 (2 products): c5 * B <= c4 + 2*M^2 <= (3B-3) + 2*(B^2-2B+1) = 2B^2 - B - 1
                              => c5 <= (2B^2 - B - 1) / B = 2B - 2  (since B+1 > B)
       Finally: c5 + M^2 <= (2B-2) + (B^2-2B+1) = B^2 - 1 < B^2 = 2^128.  *)

    (* --- Step 0: r1_c0_in * B <= a0*b0 --- *)
    assert (Htight0 : r1_c0_in * 2^64 <= a0 * b0).
    { pose proof Hacc_r0 as H0'. unfold acc_full in H0'. simpl (0 * _) in H0'.
      assert (0 <= muladd_c0 0 a0 b0)
        by (unfold muladd_c0; apply Z.mod_pos_bound; lia).
      lia. }
    assert (Hc0_ub : r1_c0_in <= 2^64 - 2).
    { assert (Hrhs0 : a0 * b0 <= (2^64 - 1) * (2^64 - 1))
        by (apply Z.mul_le_mono_nonneg; rep_lia).
      nia. }

    (* --- Step 1: (r1_c1 + r1_c2 * B) * B <= r1_c0_in + a0*b1 + a1*b0 --- *)
    assert (Htight1 : (r1_c1 + r1_c2 * 2^64) * 2^64
                      <= r1_c0_in + a0 * b1 + a1 * b0).
    { pose proof Hacc_r1 as H1'. unfold acc_full in H1'.
      assert (0 <= r1_c0)
        by (subst r1_c0; unfold muladd_c0; apply Z.mod_pos_bound; lia).
      lia. }
    assert (Hc1_ub : r1_c1 + r1_c2 * 2^64 <= 2 * 2^64 - 3).
    { assert (Hrhs1 : r1_c0_in + a0 * b1 + a1 * b0
                      <= (2^64 - 2) + 2 * ((2^64 - 1) * (2^64 - 1))).
      { assert (a0 * b1 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        assert (a1 * b0 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        lia. }
      assert (0 <= r1_c1 + r1_c2 * 2^64).
      { assert (0 <= r1_c1)
          by (subst r1_c1; unfold muladd_c1; apply Z.mod_pos_bound; lia).
        assert (0 <= r1_c2)
          by (subst r1_c2; unfold muladd_c2; apply Z.mod_pos_bound; lia).
        lia. }
      nia. }

    (* --- Step 2: (r2_c1 + r2_c2 * B) * B <= c1 + a0*b2 + a1*b1 + a2*b0 --- *)
    assert (Htight2 : (r2_c1 + r2_c2 * 2^64) * 2^64
                      <= (r1_c1 + r1_c2 * 2^64) + a0 * b2 + a1 * b1 + a2 * b0).
    { pose proof Hacc_r2 as H2'. rewrite Hacc_r2_init in H2'.
      unfold acc_full in H2'.
      assert (0 <= r2_c0)
        by (subst r2_c0; unfold muladd_c0; apply Z.mod_pos_bound; lia).
      lia. }
    assert (Hc2_ub : r2_c1 + r2_c2 * 2^64 <= 3 * 2^64 - 4).
    { assert (Hrhs2 : (r1_c1 + r1_c2 * 2^64) + a0 * b2 + a1 * b1 + a2 * b0
                      <= (2 * 2^64 - 3) + 3 * ((2^64 - 1) * (2^64 - 1))).
      { assert (a0 * b2 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        assert (a1 * b1 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        assert (a2 * b0 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        lia. }
      assert (0 <= r2_c1 + r2_c2 * 2^64).
      { assert (0 <= r2_c1)
          by (subst r2_c1; unfold muladd_c1; apply Z.mod_pos_bound; lia).
        assert (0 <= r2_c2)
          by (subst r2_c2; unfold muladd_c2; apply Z.mod_pos_bound; lia).
        lia. }
      nia. }

    (* --- Step 3: (r3_c1 + r3_c2 * B) * B <= c2 + a0*b3 + a1*b2 + a2*b1 + a3*b0 --- *)
    assert (Htight3 : (r3_c1 + r3_c2 * 2^64) * 2^64
                      <= (r2_c1 + r2_c2 * 2^64)
                         + a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0).
    { pose proof Hacc_r3 as H3'. rewrite Hacc_r3_init in H3'.
      unfold acc_full in H3'.
      assert (0 <= r3_c0)
        by (subst r3_c0; unfold muladd_c0; apply Z.mod_pos_bound; lia).
      lia. }
    assert (Hc3_ub : r3_c1 + r3_c2 * 2^64 <= 4 * 2^64 - 5).
    { (* First bound the RHS of Htight3 concretely, then divide *)
      assert (Hrhs3 : (r2_c1 + r2_c2 * 2^64)
                      + a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
                      <= (3 * 2^64 - 4) + 4 * ((2^64 - 1) * (2^64 - 1))).
      { assert (a0 * b3 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        assert (a1 * b2 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        assert (a2 * b1 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        assert (a3 * b0 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        lia. }
      assert (0 <= r3_c1 + r3_c2 * 2^64).
      { assert (0 <= r3_c1)
          by (subst r3_c1; unfold muladd_c1; apply Z.mod_pos_bound; lia).
        assert (0 <= r3_c2)
          by (subst r3_c2; unfold muladd_c2; apply Z.mod_pos_bound; lia).
        lia. }
      (* Now: c3 * B <= RHS <= concrete.  concrete / B = 4B-5. *)
      nia. }

    (* --- Step 4: (r4_c1 + r4_c2 * B) * B <= c3 + a1*b3 + a2*b2 + a3*b1 --- *)
    assert (Htight4 : (r4_c1 + r4_c2 * 2^64) * 2^64
                      <= (r3_c1 + r3_c2 * 2^64) + a1 * b3 + a2 * b2 + a3 * b1).
    { pose proof Hacc_r4 as H4'. rewrite Hacc_r4_init in H4'.
      unfold acc_full in H4'.
      assert (0 <= r4_c0)
        by (subst r4_c0; unfold muladd_c0; apply Z.mod_pos_bound; lia).
      lia. }
    assert (Hc4_ub : r4_c1 + r4_c2 * 2^64 <= 3 * 2^64 - 3).
    { assert (Hrhs4 : (r3_c1 + r3_c2 * 2^64) + a1 * b3 + a2 * b2 + a3 * b1
                      <= (4 * 2^64 - 5) + 3 * ((2^64 - 1) * (2^64 - 1))).
      { assert (a1 * b3 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        assert (a2 * b2 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        assert (a3 * b1 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        lia. }
      assert (0 <= r4_c1 + r4_c2 * 2^64).
      { assert (0 <= r4_c1)
          by (subst r4_c1; unfold muladd_c1; apply Z.mod_pos_bound; lia).
        assert (0 <= r4_c2)
          by (subst r4_c2; unfold muladd_c2; apply Z.mod_pos_bound; lia).
        lia. }
      nia. }

    (* --- Step 5: (r5_c1 + r5_c2 * B) * B <= c4 + a2*b3 + a3*b2 --- *)
    assert (Htight5 : (r5_c1 + r5_c2 * 2^64) * 2^64
                      <= (r4_c1 + r4_c2 * 2^64) + a2 * b3 + a3 * b2).
    { pose proof Hacc_r5 as H5'. rewrite Hacc_r5_init in H5'.
      unfold acc_full in H5'.
      assert (0 <= r5_c0)
        by (subst r5_c0; unfold muladd_c0; apply Z.mod_pos_bound; lia).
      lia. }
    assert (Hc5_ub : r5_c1 + r5_c2 * 2^64 <= 2 * 2^64 - 2).
    { assert (Hrhs5 : (r4_c1 + r4_c2 * 2^64) + a2 * b3 + a3 * b2
                      <= (3 * 2^64 - 3) + 2 * ((2^64 - 1) * (2^64 - 1))).
      { assert (a2 * b3 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        assert (a3 * b2 <= (2^64 - 1) * (2^64 - 1))
          by (apply Z.mul_le_mono_nonneg; rep_lia).
        lia. }
      assert (Hc5_nn : 0 <= r5_c1 + r5_c2 * 2^64).
      { assert (0 <= r5_c1)
          by (subst r5_c1; unfold muladd_c1; apply Z.mod_pos_bound; lia).
        assert (0 <= r5_c2)
          by (subst r5_c2; unfold muladd_c2; apply Z.mod_pos_bound; lia).
        lia. }
      (* Clear irrelevant hypotheses so nia terminates *)
      clear - Htight5 Hrhs5 Hc5_nn.
      (* Replace 2^64 with a concrete number for nia *)
      change (2^64) with 18446744073709551616 in *.
      nia. }

    (* --- Final: c5 + a3*b3 <= (2B-2) + (B-1)^2 = B^2 - 1 < B^2 = 2^128 --- *)
    assert (Hprod33 : a3 * b3 <= (2^64 - 1) * (2^64 - 1))
      by (apply Z.mul_le_mono_nonneg; rep_lia).
    set (B := 2^64) in *.
    assert (HB128 : 2^128 = B * B).
    { unfold B. lia. }
    assert ((B - 1) * (B - 1) = B*B - 2*B + 1) by nia.
    lia.
  }

  (* muladd_fast(&acc, a3, b3) *)
  forward_call (v_acc, a3, b3, r5_c1, r5_c2, 0, Tsh).
  { repeat split; try lia.
    - subst r5_c1. unfold muladd_c1. apply mod_64_range.
    - subst r5_c2. unfold muladd_c2. apply mod_64_range.
    - subst r5_c2. unfold muladd_c2. apply mod_64_range. 
    - subst r5_c2. unfold muladd_c2. apply mod_64_range. }

  (* Track acc_full through round 6 *)
  assert (Hacc_r6_0 : acc_full (muladd_c0 r5_c1 a3 b3) (muladd_c1 r5_c1 r5_c2 a3 b3) 0
    = acc_full r5_c1 r5_c2 0 + a3 * b3).
  { rewrite (acc_full_muladd_fast r5_c1 r5_c2 0 a3 b3); try lia.
    - subst r5_c1. unfold muladd_c1. apply mod_64_range.
    - subst r5_c2. unfold muladd_c2. apply mod_64_range. }

  (* Abbreviate accumulator state after muladd_fast(a3, b3) *)
  set (r6_c0 := muladd_c0 r5_c1 a3 b3) in *.
  set (r6_c1 := muladd_c1 r5_c1 r5_c2 a3 b3) in *.

  (* Full chain for round 6 *)
  assert (Hacc_r6 : acc_full r6_c0 r6_c1 0
    = acc_full r5_c1 r5_c2 0 + a3 * b3).
  { exact Hacc_r6_0. }

  (* extract_fast(&acc, &l8[6]) *)
  forward_call (v_acc, field_address (tarray tulong 8) [ArraySubsc 6] l8_ptr,
                r6_c0, r6_c1, 0, Tsh, sh_l).
  { (* frame: peel l8[6] out of the 2-element sub-array *)
    change (offset_val 40 l8_ptr)
      with (offset_val (sizeof tulong * 5) l8_ptr).
    rewrite <- (arr_field_address0 tulong 8 l8_ptr 5 Hfc) by lia.
    rewrite (field_address0_SUB_SUB tulong 3 8 1 5 l8_ptr) by lia.
    rewrite (split2_data_at__Tarray_app 1 2 sh_l tulong
               (field_address0 (tarray tulong 8) (SUB 6) l8_ptr)) by lia.
    rewrite data__at_singleton_array_eq.
    rewrite (arr_field_address0 tulong 8 l8_ptr 6 Hfc) by lia.
    rewrite (arr_field_address tulong 8 l8_ptr 6 Hfc) by lia.
    cancel. }
  { split; [subst r6_c0; unfold muladd_c0; apply mod_64_range
           | subst r6_c1; unfold muladd_c1; apply mod_64_range]. }
           
  deadvars!. 

  (* After extract_fast, acc = (r6_c1, 0, 0) *)
  (* l8[7] = acc.c0: first read acc.c0 into temp *)
  forward.
  (* Now store to l8[7]. The remaining sub-array for l8[7] needs to be
     rewritten to a form that forward can match. *)
  change (2 - 1) with 1.
  change (offset_val (sizeof tulong * 6) l8_ptr)
    with (offset_val (sizeof tulong * 6) l8_ptr).
  rewrite <- (arr_field_address0 tulong 8 l8_ptr 6 Hfc) by lia.
  rewrite (field_address0_SUB_SUB tulong 2 8 1 6 l8_ptr) by lia.
  change (1 + 6) with 7.
  rewrite data__at_singleton_array_eq.
  rewrite (arr_field_address0 tulong 8 l8_ptr 7 Hfc) by lia.
  rewrite <- (arr_field_address tulong 8 l8_ptr 7 Hfc) by lia.
  (* Convert data_at_ sh_l tulong (field_address ...) into
     field_at_ sh_l (tarray tulong 8) [ArraySubsc 7] l8_ptr
     so that forward can match the store target. *)
  change tulong with (nested_field_type (tarray tulong 8) (SUB 7)).
  rewrite <- field_at__data_at_.
  forward. (* l8[7] = acc.c0 *)
  
  
  entailer!. 

  (* --- Postcondition: reassemble l8[0..7] into data_at (tarray tulong 8) --- *)
  (* Convert field_at for l8[7] into data_at at field_address *)
  rewrite (field_at_data_at sh_l (tarray tulong 8) (SUB 7)) by reflexivity.
  change (nested_field_type (tarray tulong 8) (SUB 7)) with tulong.
  
  (* Fold the 8 individual data_at into a single array data_at *)
  sep_apply (fold_data_at_tulong_8 sh_l l8_ptr
    (Vlong (Int64.repr r0_c0))
    (Vlong (Int64.repr r1_c0))
    (Vlong (Int64.repr r2_c0))
    (Vlong (Int64.repr r3_c0))
    (Vlong (Int64.repr r4_c0))
    (Vlong (Int64.repr r5_c0))
    (Vlong (Int64.repr r6_c0))
    (Vlong (Int64.repr r6_c1))
    Hfc).
  
  (* Now: data_at sh_l ... [Vlong ...; ...] l8_ptr |-- data_at sh_l ... (mul_512_result ...) l8_ptr *)
  (* Reduce to proving the two lists are equal *)
  apply derives_refl'.
  f_equal.
  
  unfold mul_512_result. 
  simpl (seq 0 8). simpl map.
  repeat (f_equal; [f_equal; f_equal |]); f_equal; f_equal; f_equal.

  (* Clean context: keep only Z-level hypotheses *)
  clear - a0 a1 a2 a3 b0 b1 b2 b3
          r0_c0 r1_c0 r2_c0 r3_c0 r4_c0 r5_c0 r6_c0 r6_c1. 

Admitted.