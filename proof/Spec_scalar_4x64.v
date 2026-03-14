(** * Spec_scalar_4x64: Functional model and API specs for scalar_4x64.c *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import VST.floyd.proofauto.
Require Import scalar_4x64.scalar_4x64.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Functional model *)

(** A 128-bit unsigned integer represented as two 64-bit limbs. *)
Definition u128_val (lo hi : Z) : reptype (Tstruct __191 noattr) :=
  (Vlong (Int64.repr lo), Vlong (Int64.repr hi)).

(** Full 64×64 → 128-bit multiplication at the Z level. *)
Definition umul128_full (a b : Z) : Z := a * b.
Definition umul128_lo   (a b : Z) : Z := (a * b) mod 2^64.
Definition umul128_hi   (a b : Z) : Z := (a * b) / 2^64.

(* ================================================================= *)
(** ** Function specifications *)

(** [secp256k1_u128_to_u64] simply returns the low 64 bits of a uint128. *)
Definition secp256k1_u128_to_u64_spec : ident * funspec :=
  DECLARE _secp256k1_u128_to_u64
  WITH a_ptr : val, lo : Z, hi : Z, sh : share
  PRE [ tptr (Tstruct __191 noattr) ]
    PROP (readable_share sh;
          0 <= lo <= Int64.max_unsigned;
          0 <= hi <= Int64.max_unsigned)
    PARAMS (a_ptr)
    SEP (data_at sh (Tstruct __191 noattr) (u128_val lo hi) a_ptr)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr lo))
    SEP (data_at sh (Tstruct __191 noattr) (u128_val lo hi) a_ptr).

(** [secp256k1_u128_hi_u64] returns the high 64 bits of a uint128. *)
Definition secp256k1_u128_hi_u64_spec : ident * funspec :=
  DECLARE _secp256k1_u128_hi_u64
  WITH a_ptr : val, lo : Z, hi : Z, sh : share
  PRE [ tptr (Tstruct __191 noattr) ]
    PROP (readable_share sh;
          0 <= lo <= Int64.max_unsigned;
          0 <= hi <= Int64.max_unsigned)
    PARAMS (a_ptr)
    SEP (data_at sh (Tstruct __191 noattr) (u128_val lo hi) a_ptr)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr hi))
    SEP (data_at sh (Tstruct __191 noattr) (u128_val lo hi) a_ptr).

(** [secp256k1_umul128] computes a*b as a 128-bit result.
    Returns the low 64 bits; writes the high 64 bits to [*hi]. *)
Definition secp256k1_umul128_spec : ident * funspec :=
  DECLARE _secp256k1_umul128
  WITH a : Z, b : Z, hi_ptr : val, sh : share
  PRE [ tulong, tulong, tptr tulong ]
    PROP (writable_share sh;
          0 <= a <= Int64.max_unsigned;
          0 <= b <= Int64.max_unsigned)
    PARAMS (Vlong (Int64.repr a); Vlong (Int64.repr b); hi_ptr)
    SEP (data_at_ sh tulong hi_ptr)
  POST [ tulong ]
    PROP (0 <= umul128_lo a b <= Int64.max_unsigned;
          0 <= umul128_hi a b <= Int64.max_unsigned)
    RETURN (Vlong (Int64.repr (umul128_lo a b)))
    SEP (data_at sh tulong (Vlong (Int64.repr (umul128_hi a b))) hi_ptr).

(** [secp256k1_u128_mul] stores a*b into the uint128 struct [*r]. *)
Definition secp256k1_u128_mul_spec : ident * funspec :=
  DECLARE _secp256k1_u128_mul
  WITH r_ptr : val, a : Z, b : Z, sh : share
  PRE [ tptr (Tstruct __191 noattr), tulong, tulong ]
    PROP (writable_share sh;
          0 <= a <= Int64.max_unsigned;
          0 <= b <= Int64.max_unsigned)
    PARAMS (r_ptr; Vlong (Int64.repr a); Vlong (Int64.repr b))
    SEP (data_at_ sh (Tstruct __191 noattr) r_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh (Tstruct __191 noattr)
           (u128_val (umul128_lo a b) (umul128_hi a b)) r_ptr).

(* ================================================================= *)
(** ** 192-bit accumulator model and specs *)

(** A 192-bit accumulator represented as (c0 : uint64, c1 : uint64, c2 : uint32). *)
Definition acc_val (c0 c1 : Z) (c2 : Z) : reptype (Tstruct __214 noattr) :=
  (Vlong (Int64.repr c0), (Vlong (Int64.repr c1), Vint (Int.repr c2))).

(** The full 192-bit value of an accumulator. *)
Definition acc_full (c0 c1 c2 : Z) : Z :=
  c0 + c1 * 2^64 + c2 * 2^128.

(** Functional model: muladd adds a*b to the 192-bit accumulator. *)
Definition muladd_c0 (c0 a b : Z) : Z := (c0 + (a * b) mod 2^64) mod 2^64.
Definition muladd_th (c0 a b : Z) : Z := (a * b) / 2^64 + (if c0 + (a * b) mod 2^64 <? 2^64 then 0 else 1).
Definition muladd_c1 (c0 c1 a b : Z) : Z := (c1 + muladd_th c0 a b) mod 2^64.
Definition muladd_c2 (c0 c1 c2 a b : Z) : Z := (c2 + (if c1 + muladd_th c0 a b <? 2^64 then 0 else 1)) mod 2^32.

(** [muladd] adds a*b to the 192-bit number (c0,c1,c2). c2 must never overflow. *)
Definition muladd_spec : ident * funspec :=
  DECLARE _muladd
  WITH acc_ptr : val, a : Z, b : Z, c0 : Z, c1 : Z, c2 : Z, sh : share
  PRE [ tptr (Tstruct __214 noattr), tulong, tulong ]
    PROP (writable_share sh;
          0 <= a <= Int64.max_unsigned;
          0 <= b <= Int64.max_unsigned;
          0 <= c0 <= Int64.max_unsigned;
          0 <= c1 <= Int64.max_unsigned;
          0 <= c2 <= Int.max_unsigned;
          (** c2 must not overflow after the addition *)
          acc_full c0 c1 c2 + a * b < 2^192)
    PARAMS (acc_ptr; Vlong (Int64.repr a); Vlong (Int64.repr b))
    SEP (data_at sh (Tstruct __214 noattr) (acc_val c0 c1 c2) acc_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh (Tstruct __214 noattr)
           (acc_val (muladd_c0 c0 a b)
                    (muladd_c1 c0 c1 a b)
                    (muladd_c2 c0 c1 c2 a b)) acc_ptr).

(** [muladd_fast] adds a*b to (c0,c1). c1 must never overflow; c2 is untouched. *)
Definition muladd_fast_spec : ident * funspec :=
  DECLARE _muladd_fast
  WITH acc_ptr : val, a : Z, b : Z, c0 : Z, c1 : Z, c2 : Z, sh : share
  PRE [ tptr (Tstruct __214 noattr), tulong, tulong ]
    PROP (writable_share sh;
          0 <= a <= Int64.max_unsigned;
          0 <= b <= Int64.max_unsigned;
          0 <= c0 <= Int64.max_unsigned;
          0 <= c1 <= Int64.max_unsigned;
          0 <= c2 <= Int.max_unsigned;
          (** c1 must not overflow after the addition *)
          c0 + c1 * 2^64 + a * b < 2^128)
    PARAMS (acc_ptr; Vlong (Int64.repr a); Vlong (Int64.repr b))
    SEP (data_at sh (Tstruct __214 noattr) (acc_val c0 c1 c2) acc_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh (Tstruct __214 noattr)
           (acc_val (muladd_c0 c0 a b)
                    (muladd_c1 c0 c1 a b)
                    c2) acc_ptr).

(** Collect all specs into Gprog. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [
    secp256k1_u128_to_u64_spec;
    secp256k1_u128_hi_u64_spec;
    secp256k1_umul128_spec;
    secp256k1_u128_mul_spec;
    muladd_spec;
    muladd_fast_spec
  ]).
