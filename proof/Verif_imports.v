(** * Verif_imports: Shared imports and infrastructure for verification proofs *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Export VST.floyd.proofauto.
Require Export compcert.lib.Zbits.
Require Export scalar_4x64.Source_scalar_4x64.

(* ================================================================= *)
(** ** CompSpecs / Vprog *)

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Struct type aliases *)

Definition t_secp256k1_scalar : type := Tstruct __185 noattr.
Definition t_secp256k1_uint128 : type := Tstruct __191 noattr.
Definition t_secp256k1_uint256 : type := Tstruct __185 noattr.
Definition t_secp256k1_acc : type := Tstruct __215 noattr.
