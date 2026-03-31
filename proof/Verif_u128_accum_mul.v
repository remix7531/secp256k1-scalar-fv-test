(** * Verif_u128_accum_mul: Proof of body_secp256k1_u128_accum_mul *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** secp256k1_u128_accum_mul *)

Lemma mk_u128_sum (r : UInt128) (a b : UInt64)
  (H : u128_val r + u64_val a * u64_val b < 2^128) :
  { r' : UInt128 | u128_val r' = u128_val r + u64_val a * u64_val b }.
Proof.
  refine (exist _ (mkUInt128 (u128_val r + u64_val a * u64_val b) _) eq_refl).
  pose proof (u128_range r).
  pose proof (u64_range a).
  pose proof (u64_range b).
  lia.
Defined.

Lemma body_secp256k1_u128_accum_mul:
  semax_body Vprog Gprog
    f_secp256k1_u128_accum_mul secp256k1_u128_accum_mul_spec.
Proof.
  start_function.

  (* secp256k1_u128_mul(&t, a, b) *)
  forward_call.
  Intros vret.
  subst vret.

  (* r->lo += t.lo *)
  forward. (* _t'5 = r->lo *)
  forward. (* _t'6 = t.lo *)
  forward. (* r->lo = _t'5 + _t'6 *)

  (* r->hi += t.hi + (r->lo < t.lo) *)
  forward. (* _t'1 = r->hi *)
  forward. (* _t'2 = t.hi *)
  forward. (* _t'3 = r->lo *)
  forward. (* _t'4 = t.lo *)
  forward. (* r->hi = _t'1 + _t'2 + (_t'3 < _t'4) *)

  (* Provide witness *)
  set (prod := u64_val a * u64_val b).
  set (rv := u128_val r).
  destruct (mk_u128_sum r a b H) as [r' Hr'].
  Exists r'.
  entailer!.

  (* --- Postcondition: C struct = uint128_to_val of mathematical sum --- *)
  apply derives_refl'.
  unfold uint128_to_val.
  rewrite Hr'.
  do 3 f_equal.
  + (* limb 0 *)
    apply Int64.eqm_samerepr.
    apply eqm_of_mod_eq. 
    apply limb_add_0.
    - destruct r; simpl; lia.
    - apply Z.mul_nonneg_nonneg; destruct a, b; simpl; lia.
  + (* limb 1 *)
    apply Int64.eqm_samerepr.
    apply muladd_limb1.
    - destruct r; simpl; lia.
    - apply Z.mul_nonneg_nonneg; destruct a, b; simpl; lia.
Qed.
