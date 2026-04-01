(** * Verif_sumadd_fast: Proof of body_sumadd_fast *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** sumadd_fast *)

Lemma body_sumadd_fast:
  semax_body Vprog Gprog f_sumadd_fast sumadd_fast_spec.
Proof.
  start_function.

  (* acc->c0 += a *)
  forward. (* _t'3 = acc->c0 *)
  forward. (* acc->c0 = _t'3 + a *)

  (* acc->c1 += (acc->c0 < a) *)
  forward. (* _t'1 = acc->c1 *)
  forward. (* _t'2 = acc->c0 *)
  forward. (* acc->c1 = _t'1 + (_t'2 < a) *)

  Exists (mkAcc (acc_val acc + u64_val a)
    ltac:(pose proof (acc_range acc); pose proof (u64_range a); lia)).

  entailer!.

  apply derives_refl'.
  unfold acc_to_val.
  simpl.
  do 3 f_equal.
  + apply Int64.eqm_samerepr.
    apply sumadd_limb0; [pose proof (acc_range acc) | pose proof (u64_range a)]; lia.
  + f_equal. apply Int64.eqm_samerepr.
    rewrite Int.signed_repr
      by (unfold Z.b2z; destruct (Int64.ltu _ _); rep_lia).
    apply sumadd_limb1; [pose proof (acc_range acc) | pose proof (u64_range a)]; lia.
  + (* limb 2: acc + a < 2^128 so both sides are 0 *)
    f_equal. apply Int64.eqm_samerepr.
    unfold limb64. simpl Z.of_nat. replace (64 * 2) with 128 by lia.
    unfold Int64.eqm. change Int64.modulus with (2^64).
    rewrite !Z.div_small
      by (pose proof (acc_range acc); pose proof (u64_range a); lia).
    apply Zbits.eqmod_refl.
Qed.
