(** * Verif_u128_to_u64: Proof of body_secp256k1_u128_to_u64 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

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
  Exists (u128_lo x).
  unfold u128_lo, uint64_to_val.
  simpl.
  entailer!.
Qed.
