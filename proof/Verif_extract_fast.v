(** * Verif_extract_fast: Proof of body_extract_fast *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** extract_fast *)

Lemma body_extract_fast:
  semax_body Vprog Gprog f_extract_fast extract_fast_spec.
Proof.
  start_function.

  (* *n = acc->c0 *)
  forward. (* _t'2 = acc->c0 *)
  forward. (* *n = _t'2 *)

  (* acc->c0 = acc->c1 *)
  forward. (* _t'1 = acc->c1 *)
  forward. (* acc->c0 = _t'1 *)

  (* acc->c1 = 0 *)
  forward. (* acc->c1 = 0 *)

  (* Witnesses: n = acc_lo acc, acc' = acc_shift acc *)
  Exists (acc_lo acc) (acc_shift acc).
  entailer!.

  (* --- Postcondition: C struct = acc_to_val (acc_shift acc) --- *)
  apply derives_refl'.
  unfold acc_to_val.
  replace (acc_val (acc_shift acc)) with (acc_val acc / 2^64)
    by (unfold acc_shift; reflexivity).
  simpl snd.
  do 4 f_equal.

  + (* limb 0 of shifted = limb 1 of original *)
    symmetry. apply limb64_shift. rep_lia.
  + (* limb 1 of shifted = 0 (since acc < 2^128, limb 2 = 0) *)
    rewrite limb64_shift by rep_lia.
    rewrite (limb64_high_zero (acc_val acc) 1) by rep_lia.
    reflexivity.
  + (* limb 2 of shifted = limb 2 of original (both 0) *)
    rewrite limb64_shift by rep_lia.
    rewrite (limb64_high_zero (acc_val acc) 1) by rep_lia.
    rewrite (limb64_high_zero (acc_val acc) 2) by rep_lia.
    reflexivity.
Qed.
