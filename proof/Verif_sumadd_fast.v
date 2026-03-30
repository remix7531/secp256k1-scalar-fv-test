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

  (* --- Postcondition: C struct = acc_to_val of mathematical sum --- *)
  apply derives_refl'.
  unfold acc_to_val.
  simpl.
  do 3 f_equal.

  + (* limb 0: (limb64 acc 0 + u64_val a) mod 2^64 = limb64 (acc+a) 0 *)
    apply Int64.eqm_samerepr.
    unfold Int64.eqm, limb64.
    simpl Z.of_nat.
    rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r.
    change Int64.modulus with (2^64).

    (* u64_val a < 2^64, so mod is identity; then fold back *)
    rewrite Z.add_mod by lia.
    rewrite (Z.mod_small (u64_val a))
      by (pose proof (u64_range a); lia).
    apply Zbits.eqmod_mod.
    lia.
  + (* limb 1: ltu carry bridge -> limb_add_1 *)
    f_equal.
    apply Int64.eqm_samerepr.
    pose proof (acc_range acc) as Hacc.
    pose proof (u64_range a) as Ha.
    pose proof (limb64_u64_range (acc_val acc) 0) as Hc0.

    (* Int.signed (Int.repr (b2z ...)) = b2z ... *)
    rewrite Int.signed_repr
      by (unfold Z.b2z; destruct (Int64.ltu _ _); rep_lia).

    (* Normalize ltu/b2z to if-then-else carry *)
    rewrite ltu_carry_b2z by rep_lia.
    change Int64.modulus with (2^64).

    (* Transitivity: rewrite u64_val a limbs, then apply limb_add_1 *)
    apply Int64.eqm_trans
      with (y := limb64 (acc_val acc) 1 +
                 (limb64 (u64_val a) 1 +
                  (if limb64 (acc_val acc) 0 + limb64 (u64_val a) 0 <? 2^64
                   then 0 else 1))).
    * (* limb64(u64_val a, 0) = u64_val a, limb64(u64_val a, 1) = 0 *)
      rewrite limb64_u64_val_0, limb64_u64_val_1.
      unfold Int64.eqm.
      apply Zbits.eqmod_refl.
    * (* Conclude via limb_add_1 *)
      apply limb_add_1; lia.
  + (* limb 2: acc + a < 2^128 so both sides are 0 *)
    f_equal.
    apply Int64.eqm_samerepr.
    unfold limb64.
    simpl Z.of_nat.
    replace (64 * 2) with 128 by lia.
    unfold Int64.eqm.
    change Int64.modulus with (2^64).
    rewrite !Z.div_small
      by (pose proof (acc_range acc); pose proof (u64_range a); lia).
    apply Zbits.eqmod_refl.
Qed.
