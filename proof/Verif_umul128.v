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
  set (al := a mod M).
  set (ah := a / M).
  set (bl := b mod M).
  set (bh := b / M).
  set (ll := al * bl).
  set (lh := al * bh).
  set (hl := ah * bl).
  set (hh := ah * bh).
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
  { subst hh lh hl ll.
    rewrite Ha_eq, Hb_eq.
    ring. }
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
  { rewrite Hlh_eq at 1.
    rewrite Hhl_eq at 1.
    rewrite Hll_eq at 1.
    ring. }
  rewrite Hexp.

  (* Step 4: Cancel the (lh/M + hl/M) * M^2 term *)
  replace ((lh / M + hl / M) * (M * M) +
           ((lh mod M + hl mod M + ll / M) * M + ll mod M))
    with ((lh mod M + hl mod M + ll / M) * M + ll mod M +
          (lh / M + hl / M) * (M * M)) by ring.
  rewrite Z_mod_plus_full.

  (* Step 5: Peel off [mod] and [+ ll%M] with [f_equal],
     cancel the common [* M] factor, then [lia] finishes. *)
  f_equal.
  f_equal.
  apply Z.mul_cancel_r with (p := M).
  all: lia.
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
  set (al := a mod M).
  set (ah := a / M).
  set (bl := b mod M).
  set (bh := b / M).
  set (ll := al * bl).
  set (lh := al * bh).
  set (hl := ah * bl).
  set (hh := ah * bh).
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
  { subst hh lh hl ll.
    rewrite Ha_eq, Hb_eq.
    ring. }
  rewrite Hab.

  (* Step 2: Split each of lh, hl, ll into (high * M + low) and
     regroup so that high parts form another multiple of M^2:
       (lh + hl) * M + ll
         = (lh/M + hl/M) * M^2
           + ((lh%M + hl%M + ll/M) * M + ll%M)                 *)
  assert (Hexp : (lh + hl) * M + ll =
    (lh / M + hl / M) * (M * M) +
    ((lh mod M + hl mod M + ll / M) * M + ll mod M)).
  { rewrite Hlh_eq at 1.
    rewrite Hhl_eq at 1.
    rewrite Hll_eq at 1.
    ring. }

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
  f_equal.
  lia.
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

  (* --- Postcondition --- *)
  Exists (mul_64 a b).
  unfold mul_64, u128_lo, u128_hi, uint64_to_val.
  simpl.
  entailer!.

  (* Goal 1: lo_val represents (av * bv) mod 2^64 *)
  + f_equal.
    apply Int64.eqm_samerepr.
    apply Int64.eqm_trans with (lo_val mod Int64.modulus);
      [apply eqmod_mod; rep_lia|].
    subst lo_val mid34 a_lo a_hi b_lo b_hi av bv.
    change Int64.modulus with (Int.modulus * Int.modulus).
    rewrite umul128_lo_correct by assumption.
    unfold limb64.
    simpl Z.of_nat.
    rewrite Z.mul_0_r, Z.div_1_r.
    change (Int.modulus * Int.modulus) with Int64.modulus.
    apply Int64.eqm_refl.

  (* Goal 2: hi_val represents limb64 (av * bv) 1 *)
  + apply derives_refl'.
    f_equal.
    f_equal.
    apply Int64.eqm_samerepr.
    subst hi_val mid34 a_lo a_hi b_lo b_hi av bv.
    rewrite umul128_hi_correct by assumption.
    unfold limb64.
    simpl Z.of_nat.
    change (64 * 1)%Z with 64%Z.
    change (2^64) with Int64.modulus.
    apply Int64.eqm_sym.
    change (Int.modulus * Int.modulus) with Int64.modulus.
    apply Int64.eqm_sym.
    apply eqmod_mod.
    rep_lia.
Qed.
