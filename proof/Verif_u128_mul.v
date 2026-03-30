(** * Verif_u128_mul: Proof of body_secp256k1_u128_mul *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** secp256k1_u128_mul *)

(** Plumbing around the umul128 spec. *)

Lemma body_secp256k1_u128_mul:
  semax_body Vprog Gprog
    f_secp256k1_u128_mul secp256k1_u128_mul_spec.
Proof.
  start_function.

  (* Decompose uninitialised struct into .lo and .hi fields *)
  unfold data_at_, field_at_.
  unfold_data_at (field_at sh t_secp256k1_uint128 [] _ r_ptr).
  assert_PROP (field_compatible t_secp256k1_uint128 [StructField _hi] r_ptr)
    as Hfc by entailer!.
  rewrite (field_at_data_at sh _ [StructField _hi]) by reflexivity.

  (* r->lo = secp256k1_umul128(a, b, &r->hi) *)
  forward_call (a, b,
    field_address t_secp256k1_uint128 [StructField _hi] r_ptr, sh).
  Intros vret.

  (* r->lo = _t'1 *)
  forward.

  (* Provide witness and reassemble struct *)
  Exists vret.
  entailer!.
  unfold uint128_to_val.
  unfold_data_at (data_at sh t_secp256k1_uint128 _ r_ptr).
  rewrite (field_at_data_at sh _ [StructField _hi]) by reflexivity.
  cancel.
Qed.
