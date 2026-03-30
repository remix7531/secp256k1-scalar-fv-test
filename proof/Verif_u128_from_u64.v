(** * Verif_u128_from_u64: Proof of body_secp256k1_u128_from_u64 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** secp256k1_u128_from_u64 *)

Lemma u64_lt_u128 (a : UInt64) : 0 <= u64_val a < 2^128.
Proof.
  destruct a.
  simpl.
  lia.
Qed.

Lemma u64_uint128_repr (a : UInt64) :
  uint128_to_val (mkUInt128 (u64_val a) (u64_lt_u128 a)) =
  (uint64_to_val a, Vlong (Int64.repr 0)).
Proof.
  unfold uint128_to_val, uint64_to_val, limb64.
  simpl Z.of_nat.
  simpl Z.mul.
  simpl u128_val.
  simpl Z.pow.
  rewrite Z.div_1_r.
  pose proof (u64_range a) as Ha.
  do 4 f_equal.
  - apply Z.mod_small; lia.
  - rewrite Z.div_small by lia.
    reflexivity.
Qed.

Lemma body_secp256k1_u128_from_u64:
  semax_body Vprog Gprog
    f_secp256k1_u128_from_u64 secp256k1_u128_from_u64_spec.
Proof.
  start_function.

  forward. (* r->lo = a *)
  forward. (* r->hi = 0 *)

  Exists (mkUInt128 (u64_val a) (u64_lt_u128 a)).
  rewrite u64_uint128_repr.
  entailer!.
Qed.
