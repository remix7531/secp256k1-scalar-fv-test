(** * Spec_scalar_4x64: Public functional model and API spec for scalar_4x64.c *)
(** This file mirrors the public interface [scalar_4x64.h]:
    only [secp256k1_scalar_mul] and the supporting type
    definitions are exposed here.  Internal helper specs (u128,
    accumulator, muladd, extract, mul_512, reduce_512) live in
    [Impl_scalar_4x64]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import VST.floyd.proofauto.
Require Import scalar_4x64.Source_scalar_4x64.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Types *)

(** The secp256k1 group order. *)
Definition secp256k1_N : Z :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141.

(** A scalar modulo the group order of the secp256k1 curve. *)
Record Scalar := mkScalar {
  scalar_val : Z;
  scalar_range : 0 <= scalar_val < secp256k1_N
}.
Coercion scalar_val : Scalar >-> Z.

(* ================================================================= *)
(** ** Operations *)

(** Modular scalar multiplication: [a * b mod N]. *)
Program Definition scalar_mul (a b : Scalar) : Scalar :=
  mkScalar ((a * b) mod secp256k1_N) _.
Next Obligation.
  split.
  - apply Z.mod_pos_bound.
    unfold secp256k1_N.
    lia.
  - apply Z.mod_pos_bound.
    unfold secp256k1_N.
    lia.
Qed.

(* ================================================================= *)
(** ** C representation *)

Definition t_secp256k1_scalar : type := Tstruct __185 noattr.

(** Represent a [Scalar] as a 4-limb C scalar struct.
    Each limb is [(x / 2^(64*i)) mod 2^64]. *)
Definition scalar_to_val (x : Scalar) : reptype t_secp256k1_scalar :=
  [ Vlong (Int64.repr (x mod 2^64));
    Vlong (Int64.repr ((x / 2^64) mod 2^64));
    Vlong (Int64.repr ((x / 2^128) mod 2^64));
    Vlong (Int64.repr ((x / 2^192) mod 2^64)) ].

(* ================================================================= *)
(** ** secp256k1_scalar_mul *)

(** The public specification for [secp256k1_scalar_mul].

    Postcondition: the scalar at [r_ptr] equals [scalar_mul a b],
    i.e. [a * b mod N]. *)
Definition secp256k1_scalar_mul_spec : ident * funspec :=
  DECLARE _secp256k1_scalar_mul
    WITH r_ptr : val, a_ptr : val, b_ptr : val,
       a : Scalar, b : Scalar,
       sh_r : share, sh_a : share, sh_b : share
    PRE [tptr t_secp256k1_scalar,
         tptr t_secp256k1_scalar,
         tptr t_secp256k1_scalar ]
    PROP (writable_share sh_r;
          readable_share sh_a;
          readable_share sh_b)
    PARAMS (r_ptr; a_ptr; b_ptr)
      SEP (data_at_ sh_r t_secp256k1_scalar r_ptr;
           data_at sh_a t_secp256k1_scalar (scalar_to_val a) a_ptr;
           data_at sh_b t_secp256k1_scalar (scalar_to_val b) b_ptr)
  POST [ tvoid ]
    EX r : Scalar,
    PROP (r = scalar_mul a b)
    RETURN ()
      SEP (data_at sh_r t_secp256k1_scalar (scalar_to_val r) r_ptr;
           data_at sh_a t_secp256k1_scalar (scalar_to_val a) a_ptr;
           data_at sh_b t_secp256k1_scalar (scalar_to_val b) b_ptr).