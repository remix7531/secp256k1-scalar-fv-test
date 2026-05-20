(** * Verif_u128_rshift: Proof of body_secp256k1_u128_rshift *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** secp256k1_u128_rshift *)

Lemma body_secp256k1_u128_rshift:
  semax_body Vprog Gprog
    f_secp256k1_u128_rshift secp256k1_u128_rshift_spec.
Proof.
  start_function.

  (* r->lo = r->hi *)
  forward. (* _t'1 = r->hi *)
  forward. (* r->lo = _t'1 *)

  (* r->hi = 0 *)
  forward. (* r->hi = 0 *)

  rewrite Int.signed_repr by rep_lia.

  (* Witness: r' = r / 2^64 *)
  assert (Hshift : 0 <= u128_val r / 2^64 < 2^128).
  { split; [apply Z.div_pos; rep_lia | apply Z.div_lt_upper_bound; rep_lia]. }
  Exists (mkUInt128 (u128_val r / 2^64) Hshift).
  entailer!.

  (* --- Postcondition: C struct = uint128_to_val of shifted value --- *)
  apply derives_refl'.
  f_equal.

  unfold uint128_to_val, limb64.
  simpl Z.of_nat.
  simpl Z.mul.
  rewrite Z.div_1_r.

  (* hi limb of (v/2^64) is 0 since v < 2^128 *)
  do 3 f_equal.
  rewrite Z.div_small; [reflexivity|].
  split; [apply Z.div_pos; rep_lia | apply Z.div_lt_upper_bound; rep_lia].
Qed.
