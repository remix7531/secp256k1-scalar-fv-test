(** * Verif_u128_accum_u64: Proof of body_secp256k1_u128_accum_u64 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** secp256k1_u128_accum_u64 *)

Lemma body_secp256k1_u128_accum_u64:
  semax_body Vprog Gprog
    f_secp256k1_u128_accum_u64 secp256k1_u128_accum_u64_spec.
Proof.
  start_function.

  forward. (* t'3 = r->lo *)
  forward. (* r->lo = t'3 + a *)
  forward. (* t'1 = r->hi *)
  forward. (* t'2 = r->lo *)
  forward. (* r->hi = t'1 + (t'2 < a) *)

  Exists (mkUInt128 (u128_val r + u64_val a) ltac:(rep_lia)).
  entailer!.

  (* --- Postcondition: C struct = uint128_to_val of mathematical sum --- *)
  apply derives_refl'.
  unfold uint128_to_val.
  simpl u128_val.
  do 3 f_equal.
  - (* lo limb *)
    apply Int64.eqm_samerepr.
    apply Int64.eqm_trans with (y := limb64 (u128_val r) 0 + limb64 (u64_val a) 0).
    + rewrite limb64_u64_val_0.
      apply Int64.eqm_refl.
    + apply eqm_of_mod_eq.
      apply limb_add_0; rep_lia.
  - (* hi limb *)
    apply Int64.eqm_samerepr.
    rewrite Int.signed_repr by (destruct (Int64.ltu _ _); simpl; rep_lia).
    rewrite ltu_carry_b2z
      by (pose proof (limb64_u64_range (u128_val r) 0); rep_lia).
    change Int64.modulus with (2^64).
    apply Int64.eqm_trans with
      (y := limb64 (u128_val r) 1 +
            (limb64 (u64_val a) 1 +
             (if limb64 (u128_val r) 0 + limb64 (u64_val a) 0 <? 2^64 then 0 else 1))).
    + rewrite limb64_u64_val_0, limb64_u64_val_1.
      unfold Int64.eqm.
      apply Zbits.eqmod_refl.
    + apply eqm_of_mod_eq.
      apply limb_add_1; rep_lia.
Qed.
