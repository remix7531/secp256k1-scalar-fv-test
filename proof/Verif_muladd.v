(** * Verif_muladd: Proof of body_muladd *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** muladd *)

Lemma body_muladd:
  semax_body Vprog Gprog f_muladd muladd_spec.
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
  forward. (* _t'7 = acc->c0 *)
  forward. (* acc->c0 = _t'7 + tl *)

  (* th += (acc->c0 < tl) *)
  forward. (* _t'6 = acc->c0 *)
  forward. (* th = th + (_t'6 < tl) *)

  (* acc->c1 += th *)
  forward. (* _t'5 = acc->c1 *)
  forward. (* acc->c1 = _t'5 + th *)

  (* acc->c2 += (acc->c1 < th) *)
  forward. (* _t'3 = acc->c2 *)
  forward. (* _t'4 = acc->c1 *)
  forward. (* acc->c2 = _t'3 + (_t'4 < th) *)

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
  + (* limb 2 *)
    f_equal.
    apply Int64.eqm_samerepr.
    apply (muladd_limb2 (acc_val acc) (u64_val a) (u64_val b)); lia.
Qed.
