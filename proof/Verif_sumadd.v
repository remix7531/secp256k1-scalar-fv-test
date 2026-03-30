(** * Verif_sumadd: Proof of body_sumadd *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** sumadd *)

Lemma body_sumadd:
  semax_body Vprog Gprog f_sumadd sumadd_spec.
Proof.
  start_function.

  (* acc->c0 += a *)
  forward. (* _t'5 = acc->c0 *)
  forward. (* acc->c0 = _t'5 + a *)

  (* over = (acc->c0 < a) *)
  forward. (* _t'4 = acc->c0 *)
  forward. (* over = (_t'4 < a) *)

  (* acc->c1 += over *)
  forward. (* _t'3 = acc->c1 *)
  forward. (* acc->c1 = _t'3 + over *)

  (* acc->c2 += (acc->c1 < over) *)
  forward. (* _t'1 = acc->c2 *)
  forward. (* _t'2 = acc->c1 *)
  forward. (* acc->c2 = _t'1 + (_t'2 < over) *)

  Exists (mkAcc (acc_val acc + u64_val a)
    ltac:(pose proof (acc_range acc); pose proof (u64_range a); lia)).
  entailer!.

  pose proof (acc_range acc) as Hacc.
  pose proof (u64_range a) as Ha.
  unfold acc_to_val.
  apply derives_refl'.
  simpl.
  do 3 f_equal.
  + (* limb 0: (limb64 acc 0 + u64_val a) mod 2^64 = limb64 (acc+a) 0 *)
    apply Int64.eqm_samerepr.
    unfold Int64.eqm, limb64.
    simpl Z.of_nat.
    rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r.
    change Int64.modulus with (2^64).

    (* Transitivity through the mod/mod form *)
    apply Zbits.eqmod_trans
      with (y := acc_val acc mod 2^64 + u64_val a mod 2^64).
    * (* LHS eqmod mod+mod: u64_val a is already < 2^64 *)
      unfold Zbits.eqmod.
      exists 0.
      rewrite Z.mod_small with (a := u64_val a) (b := 2^64) by lia.
      lia.
    * (* mod+mod eqmod RHS: unfold mods, then fold back *)
      apply Zbits.eqmod_trans with (y := acc_val acc + u64_val a).
      - apply Zbits.eqmod_add;
        apply Zbits.eqmod_sym;
        apply Zbits.eqmod_mod;
        lia.
      - apply Zbits.eqmod_mod.
        lia.
  + (* limb 1: ltu carry bridge -> limb_add_1 *)
    f_equal.
    apply Int64.eqm_samerepr.
    pose proof (limb64_u64_range (acc_val acc) 0) as Hla0.

    (* Normalize ltu/b2z to if-then-else carry *)
    rewrite (ltu_carry_b2z (limb64 (acc_val acc) 0) (u64_val a)) by rep_lia.

    (* Int.unsigned (Int.repr (0 or 1)) = (0 or 1) *)
    assert (Hcu :
      Int.unsigned (Int.repr
        (if limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus
         then 0 else 1))
      = (if limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus
         then 0 else 1))
      by (destruct (limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus);
          reflexivity).
    rewrite Hcu.
    change Int64.modulus with (2^64).

    (* Transitivity: rewrite u64_val a limbs, then apply limb_add_1 *)
    apply Zbits.eqmod_trans
      with (y := limb64 (acc_val acc) 1 + (limb64 (u64_val a) 1 +
                 (if limb64 (acc_val acc) 0 + limb64 (u64_val a) 0 <? 2^64
                  then 0 else 1))).
    * (* limb64(u64_val a, 0) = u64_val a, limb64(u64_val a, 1) = 0 *)
      rewrite limb64_u64_val_0, limb64_u64_val_1.
      unfold Zbits.eqmod.
      exists 0.
      lia.
    * (* Conclude via limb_add_1 *)
      unfold Int64.eqm.
      apply limb_add_1; lia.
  + (* limb 2: two levels of carry -> limb_add_2_u64 *)
    f_equal.
    apply Int64.eqm_samerepr.
    pose proof (limb64_u64_range (acc_val acc) 0) as Hla0.
    pose proof (limb64_u64_range (acc_val acc) 1) as Hla1.

    (* Normalize inner (limb 0) carry *)
    rewrite (ltu_carry_b2z (limb64 (acc_val acc) 0) (u64_val a)) by rep_lia.
    set (carry0 :=
      if limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus then 0 else 1).
    assert (Hc0 : 0 <= carry0 <= 1)
      by (unfold carry0;
          destruct (limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus); lia).
    assert (Hcu : Int.unsigned (Int.repr carry0) = carry0)
      by (unfold carry0;
          destruct (limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus);
          reflexivity).
    rewrite Hcu.

    (* Normalize outer (limb 1) carry *)
    rewrite (ltu_carry_b2z (limb64 (acc_val acc) 1) carry0) by rep_lia.
    set (carry1 :=
      if limb64 (acc_val acc) 1 + carry0 <? Int64.modulus then 0 else 1).
    assert (Hcs : Int.signed (Int.repr carry1) = carry1)
      by (unfold carry1;
          destruct (limb64 (acc_val acc) 1 + carry0 <? Int64.modulus);
          reflexivity).
    rewrite Hcs.

    (* Conclude via limb_add_2_u64 *)
    subst carry0 carry1.
    apply limb_add_2_u64; lia.
Qed.
