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
  apply derives_refl'.
  unfold acc_to_val.
  replace (acc_val (acc_shift acc)) with (acc_val acc / 2^64)
    by (unfold acc_shift; reflexivity).
  rewrite (Zdiv.Zdiv_Zdiv (acc_val acc) (2^64) (2^64)) by lia.
  change (2^64 * 2^64) with (2^128).
  rewrite (Zdiv.Zdiv_Zdiv (acc_val acc) (2^64) (2^128)) by lia.
  change (2^64 * 2^128) with (2^192).
  rewrite (Z.div_small (acc_val acc) (2^192)) by rep_lia.
  reflexivity.
Qed.
