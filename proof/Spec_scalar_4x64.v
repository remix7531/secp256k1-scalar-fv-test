(** * Spec_scalar_4x64: Public functional model and API spec for scalar_4x64.c *)
(** This file mirrors the public interface [scalar_4x64.h]:
    only [secp256k1_scalar_mul_512] and the supporting type
    definitions are exposed here.  Internal helper specs (u128,
    accumulator, muladd, extract) live in [Spec_scalar_4x64_internal]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import VST.floyd.proofauto.
Require Import scalar_4x64.scalar_4x64.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Types *)

(** A 256-bit unsigned integer. *)
Record UInt256 := mkUInt256 {
  u256_val : Z;
  u256_range : 0 <= u256_val < 2^256
}.

(** A 512-bit unsigned integer. *)
Record UInt512 := mkUInt512 {
  u512_val : Z;
  u512_range : 0 <= u512_val < 2^512
}.

(* ================================================================= *)
(** ** Operations *)

(** 256 x 256 -> 512-bit multiplication. *)
Program Definition mul_256 (a b : UInt256) : UInt512 :=
  mkUInt512 (u256_val a * u256_val b) _.
Next Obligation.
  destruct a as [av [Ha0 Ha1]], b as [bv [Hb0 Hb1]]. simpl.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - replace (Z.pow_pos 2 512) with (2^256 * 2^256) by reflexivity.
    apply Z.mul_lt_mono_nonneg; lia.
Qed.

(* ================================================================= *)
(** ** C representation *)

(** The [i]-th 64-bit limb of [x]: [(x / 2^(64*i)) mod 2^64]. *)
Definition limb64 (x : Z) (i : nat) : Z :=
  (x / 2^(64 * Z.of_nat i)) mod 2^64.

(** Represent a [UInt256] as a 4-limb C scalar struct. *)
Definition uint256_to_val (x : UInt256) : reptype (Tstruct __185 noattr) :=
  [ Vlong (Int64.repr (limb64 (u256_val x) 0));
    Vlong (Int64.repr (limb64 (u256_val x) 1));
    Vlong (Int64.repr (limb64 (u256_val x) 2));
    Vlong (Int64.repr (limb64 (u256_val x) 3)) ].

(** Represent a [UInt512] as an 8-limb C array. *)
Definition uint512_to_val (x : UInt512) : list val :=
  [ Vlong (Int64.repr (limb64 (u512_val x) 0));
    Vlong (Int64.repr (limb64 (u512_val x) 1));
    Vlong (Int64.repr (limb64 (u512_val x) 2));
    Vlong (Int64.repr (limb64 (u512_val x) 3));
    Vlong (Int64.repr (limb64 (u512_val x) 4));
    Vlong (Int64.repr (limb64 (u512_val x) 5));
    Vlong (Int64.repr (limb64 (u512_val x) 6));
    Vlong (Int64.repr (limb64 (u512_val x) 7)) ].

(* ================================================================= *)
(** ** secp256k1_scalar_mul_512 *)

(** The public specification for [secp256k1_scalar_mul_512].

    Postcondition: the 8-limb array at [l8_ptr], interpreted as a
    [UInt512], equals [mul_256 a b]. *)
Definition secp256k1_scalar_mul_512_spec : ident * funspec :=
  DECLARE _secp256k1_scalar_mul_512
  WITH l8_ptr : val, a_ptr : val, b_ptr : val,
       a : UInt256, b : UInt256,
       sh_l : share, sh_a : share, sh_b : share
  PRE [ tptr tulong, tptr (Tstruct __185 noattr), tptr (Tstruct __185 noattr) ]
    PROP (writable_share sh_l;
          readable_share sh_a;
          readable_share sh_b)
    PARAMS (l8_ptr; a_ptr; b_ptr)
    SEP (data_at_ sh_l (tarray tulong 8) l8_ptr;
         data_at sh_a (Tstruct __185 noattr) (uint256_to_val a) a_ptr;
         data_at sh_b (Tstruct __185 noattr) (uint256_to_val b) b_ptr)
  POST [ tvoid ]
    EX r : UInt512,
    PROP (r = mul_256 a b)
    RETURN ()
    SEP (data_at sh_l (tarray tulong 8) (uint512_to_val r) l8_ptr;
         data_at sh_a (Tstruct __185 noattr) (uint256_to_val a) a_ptr;
         data_at sh_b (Tstruct __185 noattr) (uint256_to_val b) b_ptr).