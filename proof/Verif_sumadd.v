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

  unfold acc_to_val.
  apply derives_refl'.
  simpl.
  do 3 f_equal.
  + apply Int64.eqm_samerepr.
    apply sumadd_limb0; [pose proof (acc_range acc) | pose proof (u64_range a)]; lia.
  + f_equal. apply Int64.eqm_samerepr.
    rewrite Int.unsigned_repr
      by (unfold Z.b2z; destruct (Int64.ltu _ _); rep_lia).
    apply sumadd_limb1; [pose proof (acc_range acc) | pose proof (u64_range a)]; lia.
  + f_equal. apply Int64.eqm_samerepr.
    apply sumadd_limb2; [pose proof (acc_range acc) | pose proof (u64_range a)]; lia.
Qed.
