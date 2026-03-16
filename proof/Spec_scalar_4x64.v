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

(** A 192-bit accumulator represented as (c0 : uint64, c1 : uint64, c2 : uint64). *)
Definition acc_val (c0 c1 : Z) (c2 : Z) : reptype (Tstruct __214 noattr) :=
  (Vlong (Int64.repr c0), (Vlong (Int64.repr c1), Vlong (Int64.repr c2))).

(** The full 192-bit value of an accumulator. *)
Definition acc_full (c0 c1 c2 : Z) : Z :=
  c0 + c1 * 2^64 + c2 * 2^128.

(** Functional model: muladd adds a*b to the 192-bit accumulator. *)
Definition muladd_c0 (c0 a b : Z) : Z := (c0 + (a * b) mod 2^64) mod 2^64.
Definition muladd_th (c0 a b : Z) : Z := (a * b) / 2^64 + (if c0 + (a * b) mod 2^64 <? 2^64 then 0 else 1).
Definition muladd_c1 (c0 c1 a b : Z) : Z := (c1 + muladd_th c0 a b) mod 2^64.
Definition muladd_c2 (c0 c1 c2 a b : Z) : Z := (c2 + (if c1 + muladd_th c0 a b <? 2^64 then 0 else 1)) mod 2^64.

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
          0 <= c2 <= Int64.max_unsigned;
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
          0 <= c2 <= Int64.max_unsigned;
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

(* ================================================================= *)
(** ** extract / extract_fast *)

(** [extract] writes c0 to [*n] and shifts the accumulator:
    (c0, c1, c2) → (c1, c2, 0). *)
Definition extract_spec : ident * funspec :=
  DECLARE _extract
  WITH acc_ptr : val, n_ptr : val, c0 : Z, c1 : Z, c2 : Z, sh : share, sh_n : share
  PRE [ tptr (Tstruct __214 noattr), tptr tulong ]
    PROP (writable_share sh;
          writable_share sh_n;
          0 <= c0 <= Int64.max_unsigned;
          0 <= c1 <= Int64.max_unsigned;
          0 <= c2 <= Int64.max_unsigned)
    PARAMS (acc_ptr; n_ptr)
    SEP (data_at sh (Tstruct __214 noattr) (acc_val c0 c1 c2) acc_ptr;
         data_at_ sh_n tulong n_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh (Tstruct __214 noattr) (acc_val c1 c2 0) acc_ptr;
         data_at sh_n tulong (Vlong (Int64.repr c0)) n_ptr).

(** [extract_fast] writes c0 to [*n] and shifts: (c0, c1, c2) → (c1, 0, c2).
    c2 is required to be zero by contract, but we leave it untouched. *)
Definition extract_fast_spec : ident * funspec :=
  DECLARE _extract_fast
  WITH acc_ptr : val, n_ptr : val, c0 : Z, c1 : Z, c2 : Z, sh : share, sh_n : share
  PRE [ tptr (Tstruct __214 noattr), tptr tulong ]
    PROP (writable_share sh;
          writable_share sh_n;
          0 <= c0 <= Int64.max_unsigned;
          0 <= c1 <= Int64.max_unsigned;
          0 <= c2 <= Int64.max_unsigned)
    PARAMS (acc_ptr; n_ptr)
    SEP (data_at sh (Tstruct __214 noattr) (acc_val c0 c1 c2) acc_ptr;
         data_at_ sh_n tulong n_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh (Tstruct __214 noattr) (acc_val c1 0 c2) acc_ptr;
         data_at sh_n tulong (Vlong (Int64.repr c0)) n_ptr).

(* ================================================================= *)
(** ** secp256k1_scalar_mul_512 *)

(** A 256-bit scalar represented as four 64-bit limbs (little-endian). *)
Definition scalar_val (d : list Z) : reptype (Tstruct __185 noattr) :=
  map Vlong (map Int64.repr d).

(** The full 256-bit value of a scalar [d0..d3]. *)
Definition scalar_full (d : list Z) : Z :=
  Znth 0 d + Znth 1 d * 2^64 + Znth 2 d * 2^128 + Znth 3 d * 2^192.

(** The 512-bit product of two 256-bit scalars, represented as eight
    64-bit limbs.  We specify it abstractly: each output limb [l8[i]]
    is the [i]-th 64-bit word of [a * b]. *)
Definition mul_512_limb (a b : list Z) (i : nat) : Z :=
  (scalar_full a * scalar_full b / 2^(64 * Z.of_nat i)) mod 2^64.

Definition mul_512_result (a b : list Z) : list val :=
  map (fun i => Vlong (Int64.repr (mul_512_limb a b i))) (seq 0 8).

Definition secp256k1_scalar_mul_512_spec : ident * funspec :=
  DECLARE _secp256k1_scalar_mul_512
  WITH l8_ptr : val, a_ptr : val, b_ptr : val,
       a : list Z, b : list Z,
       sh_l : share, sh_a : share, sh_b : share
  PRE [ tptr tulong, tptr (Tstruct __185 noattr), tptr (Tstruct __185 noattr) ]
    PROP (writable_share sh_l;
          readable_share sh_a;
          readable_share sh_b;
          Zlength a = 4;
          Zlength b = 4;
          Forall (fun x => 0 <= x <= Int64.max_unsigned) a;
          Forall (fun x => 0 <= x <= Int64.max_unsigned) b)
    PARAMS (l8_ptr; a_ptr; b_ptr)
    SEP (data_at_ sh_l (tarray tulong 8) l8_ptr;
         data_at sh_a (Tstruct __185 noattr) (scalar_val a) a_ptr;
         data_at sh_b (Tstruct __185 noattr) (scalar_val b) b_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh_l (tarray tulong 8) (mul_512_result a b) l8_ptr;
         data_at sh_a (Tstruct __185 noattr) (scalar_val a) a_ptr;
         data_at sh_b (Tstruct __185 noattr) (scalar_val b) b_ptr).

(** Collect all specs into Gprog. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [
    secp256k1_u128_to_u64_spec;
    secp256k1_u128_hi_u64_spec;
    secp256k1_umul128_spec;
    secp256k1_u128_mul_spec;
    muladd_spec;
    muladd_fast_spec;
    extract_spec;
    extract_fast_spec;
    secp256k1_scalar_mul_512_spec
  ]).
