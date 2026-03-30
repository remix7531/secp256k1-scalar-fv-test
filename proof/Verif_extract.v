(** * Verif_extract: Proof of body_extract *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** extract *)

Lemma body_extract:
  semax_body Vprog Gprog f_extract extract_spec.
Proof.
  start_function.

  (* *n = acc->c0 *)
  forward. (* _t'3 = acc->c0 *)
  forward. (* *n = _t'3 *)

  (* acc->c0 = acc->c1 *)
  forward. (* _t'2 = acc->c1 *)
  forward. (* acc->c0 = _t'2 *)

  (* acc->c1 = acc->c2 *)
  forward. (* _t'1 = acc->c2 *)
  forward. (* acc->c1 = _t'1 *)

  (* acc->c2 = 0 *)
  forward. (* acc->c2 = 0 *)

  (* Witnesses: n = acc_lo acc, acc' = acc_shift acc *)
  Exists (acc_lo acc) (acc_shift acc).
  entailer!.

  (* --- Postcondition: C struct = acc_to_val (acc_shift acc) --- *)
  pose proof (acc_range acc) as Hacc.
  apply derives_refl'.
  unfold acc_to_val.
  replace (acc_val (acc_shift acc)) with (acc_val acc / 2^64)
    by (unfold acc_shift; reflexivity).
  do 4 f_equal.

  + (* limb 0 of shifted = limb 1 of original *)
    symmetry.
    apply limb64_shift.
    lia.
  + (* limb 1 of shifted = limb 2 of original *)
    f_equal.
    symmetry.
    apply limb64_shift.
    lia.
  + (* limb 2 of shifted = 0 *)
    rewrite limb64_shift by lia.
    rewrite (limb64_high_zero (acc_val acc) 2) by lia.
    reflexivity.
Qed.
