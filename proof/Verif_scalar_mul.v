(** * Verif_scalar_mul: Proof of body_secp256k1_scalar_mul *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** secp256k1_scalar_mul *)

Lemma body_secp256k1_scalar_mul:
  semax_body Vprog Gprog
    f_secp256k1_scalar_mul secp256k1_scalar_mul_spec.
Proof.
  start_function.

  (* Rewrite scalar representation to uint256 for mul_512 call *)
  rewrite !scalar_to_val_eq.
  change t_secp256k1_scalar with t_secp256k1_uint256.

  (* secp256k1_scalar_mul_512(l, a, b) *)
  forward_call (v_l, a_ptr, b_ptr,
    scalar_to_u256 a, scalar_to_u256 b,
    Tsh, sh_a, sh_b).

  Intros l.

  (* secp256k1_scalar_reduce_512(r, l) *)
  forward_call (r_ptr, v_l, l, sh_r, Tsh).

  Intros r.

  (* Postcondition *)
  Exists r.
  entailer!.
  - (* r = scalar_mul a b *)
    destruct r as [rv Hr].
    destruct a as [av Ha].
    destruct b as [bv Hb].
    unfold scalar_mul, scalar_to_u256, mul_256 in *.
    simpl in *.
    subst.
    f_equal.
    apply proof_irr.
  - (* Rewrite uint256 back to scalar representation *)
    rewrite <- !scalar_to_val_eq.
    change t_secp256k1_uint256 with t_secp256k1_scalar.
    cancel.
Qed.