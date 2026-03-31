(** * Verif_muladd_fast: Proof of body_muladd_fast *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** muladd_fast *)

Lemma body_muladd_fast:
  semax_body Vprog Gprog f_muladd_fast muladd_fast_spec.
Proof.
  start_function.

  (* secp256k1_u128_mul(&t, a, b) *)
  forward_call.

  Intros vret.

  (* tl = secp256k1_u128_to_u64(&t) *)
  forward_call.

  Intros hi.

  (* th = secp256k1_u128_hi_u64(&t) *)
  forward_call.

  Intros lo.

  (* acc->c0 += tl *)
  forward. (* _t'5 = acc->c0 *)
  forward. (* acc->c0 = _t'5 + tl *)

  (* th += (acc->c0 < tl) *)
  forward. (* _t'4 = acc->c0 *)
  forward. (* th = th + (_t'4 < tl) *)

  (* acc->c1 += th *)
  forward. (* _t'3 = acc->c1 *)
  forward. (* acc->c1 = _t'3 + th *)

  Exists (acc_muladd acc a b ltac:(lia)).
  entailer!.

  (* --- Postcondition: C struct = acc_to_val of mathematical sum --- *)
  pose proof (acc_range acc) as Hacc.
  pose proof (u64_range a) as Ha.
  pose proof (u64_range b) as Hb.
  unfold acc_to_val, acc_muladd, u128_lo, u128_hi, mul_64.
  apply derives_refl'.
  simpl.
  do 3 f_equal.
  + (* limb 0 *)
    apply Int64.eqm_samerepr.
    apply eqm_of_mod_eq.
    apply limb_add_0; lia.
  + (* limb 1 *)
    f_equal.
    apply Int64.eqm_samerepr.
    apply muladd_limb1; lia.
  + (* limb 2: acc + a*b < 2^128 so limb 2 is 0 on both sides *)
    f_equal.
    apply Int64.eqm_samerepr.
    unfold limb64.
    simpl Z.of_nat.
    unfold Int64.eqm.
    replace Int64.modulus with (2^64) by reflexivity.
    rewrite !Z.div_small by lia.
    apply Zbits.eqmod_refl.
Qed.
