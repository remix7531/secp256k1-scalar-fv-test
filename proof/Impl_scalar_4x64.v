(** * Spec_scalar_4x64_internal: Internal helper specs for scalar_4x64.c *)
(** These are implementation details -- u128 arithmetic, the 192-bit
    accumulator, muladd/extract helpers, and limb conversion machinery.
    Clients of the public API should only depend on [Spec_scalar_4x64]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import VST.floyd.proofauto.
Require Import scalar_4x64.scalar_4x64.
Require Import scalar_4x64.Spec_scalar_4x64.

(* ================================================================= *)
(** ** Types *)

(** A 64-bit unsigned integer. *)
Record UInt64 := mkUInt64 {
  u64_val : Z;
  u64_range : 0 <= u64_val < 2^64
}.

(** A 128-bit unsigned integer. *)
Record UInt128 := mkUInt128 {
  u128_val : Z;
  u128_range : 0 <= u128_val < 2^128
}.

(** A 192-bit accumulator (c0, c1, c2). *)
Record Acc := mkAcc {
  acc_val : Z;
  acc_range : 0 <= acc_val < 2^192
}.

(* ================================================================= *)
(** ** Operations *)

(** 64 x 64 -> 128-bit multiplication. *)
Program Definition mul_64 (a b : UInt64) : UInt128 :=
  mkUInt128 (u64_val a * u64_val b) _.
Next Obligation.
  destruct a as [av [Ha0 Ha1]], b as [bv [Hb0 Hb1]].
  simpl.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - replace (Z.pow_pos 2 128) with (2^64 * 2^64) by reflexivity.
    apply Z.mul_lt_mono_nonneg; lia.
Qed.

(** Low 64 bits of a [UInt128]. *)
Program Definition u128_lo (x : UInt128) : UInt64 :=
  mkUInt64 (limb64 (u128_val x) 0) _.
Next Obligation. apply Z.mod_pos_bound. lia. Qed.

(** High 64 bits of a [UInt128]. *)
Program Definition u128_hi (x : UInt128) : UInt64 :=
  mkUInt64 (limb64 (u128_val x) 1) _.
Next Obligation. apply Z.mod_pos_bound. lia. Qed.

(** Add a*b to the accumulator: acc' = acc + a*b. *)
Program Definition acc_muladd (acc : Acc) (a b : UInt64)
  (H : acc_val acc + u64_val a * u64_val b < 2^192) : Acc :=
  mkAcc (acc_val acc + u64_val a * u64_val b) _.
Next Obligation.
  destruct acc as [v [Hv0 Hv1]].
  destruct a as [av [Ha0 Ha1]], b as [bv [Hb0 Hb1]].
  simpl in *.
  lia.
Qed.

(** Low 64 bits of an [Acc] (extracted limb). *)
Program Definition acc_lo (acc : Acc) : UInt64 :=
  mkUInt64 (limb64 (acc_val acc) 0) _.
Next Obligation. apply Z.mod_pos_bound. lia. Qed.

(** Right-shift the accumulator by 64 bits. *)
Program Definition acc_shift (acc : Acc) : Acc :=
  mkAcc (acc_val acc / 2^64) _.
Next Obligation.
  destruct acc as [v [Hv0 Hv1]]. 
  simpl.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

(* ================================================================= *)
(** ** C representation *)

(** Represent a [UInt64] as a C value. *)
Definition uint64_to_val (x : UInt64) : val :=
  Vlong (Int64.repr (u64_val x)).

(** Represent a [UInt128] as a C struct (lo, hi). *)
Definition uint128_to_val (x : UInt128) : reptype (Tstruct __191 noattr) :=
  let v := u128_val x in
  (Vlong (Int64.repr (limb64 v 0)), Vlong (Int64.repr (limb64 v 1))).

(** Represent an [Acc] as a C struct (c0, c1, c2). *)
Definition acc_to_val (x : Acc) : reptype (Tstruct __214 noattr) :=
  let v := acc_val x in
  (Vlong (Int64.repr (limb64 v 0)),
   (Vlong (Int64.repr (limb64 v 1)),
    Vlong (Int64.repr (limb64 v 2)))).

(** Reconstruct a [UInt64] from a raw Z value. *)
Program Definition val_to_uint64 (z : Z)
  (H : 0 <= z < 2^64) : UInt64 :=
  mkUInt64 z _.

(** Reconstruct a [UInt128] from two 64-bit Z limbs (lo, hi). *)
Program Definition val_to_uint128 (lo hi : Z)
  (Hlo : 0 <= lo < 2^64) (Hhi : 0 <= hi < 2^64) : UInt128 :=
  mkUInt128 (lo + hi * 2^64) _.
Next Obligation. nia. Qed.

(** Reconstruct an [Acc] from three 64-bit Z limbs (c0, c1, c2). *)
Program Definition val_to_acc (c0 c1 c2 : Z)
  (H0 : 0 <= c0 < 2^64) (H1 : 0 <= c1 < 2^64) (H2 : 0 <= c2 < 2^64)
  : Acc :=
  mkAcc (c0 + c1 * 2^64 + c2 * 2^128) _.
Next Obligation. nia. Qed.

(* ================================================================= *)
(** ** u128 function specifications *)

(** [secp256k1_u128_to_u64]: return the low 64 bits. *)
Definition secp256k1_u128_to_u64_spec : ident * funspec :=
  DECLARE _secp256k1_u128_to_u64
  WITH a_ptr : val, x : UInt128, sh : share
  PRE [ tptr (Tstruct __191 noattr) ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (data_at sh (Tstruct __191 noattr) (uint128_to_val x) a_ptr)
  POST [ tulong ]
    EX r : UInt64,
    PROP (r = u128_lo x)
    RETURN (uint64_to_val r)
    SEP (data_at sh (Tstruct __191 noattr) (uint128_to_val x) a_ptr).

(** [secp256k1_u128_hi_u64]: return the high 64 bits. *)
Definition secp256k1_u128_hi_u64_spec : ident * funspec :=
  DECLARE _secp256k1_u128_hi_u64
  WITH a_ptr : val, x : UInt128, sh : share
  PRE [ tptr (Tstruct __191 noattr) ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (data_at sh (Tstruct __191 noattr) (uint128_to_val x) a_ptr)
  POST [ tulong ]
    EX r : UInt64,
    PROP (r = u128_hi x)
    RETURN (uint64_to_val r)
    SEP (data_at sh (Tstruct __191 noattr) (uint128_to_val x) a_ptr).

(** [secp256k1_umul128]: compute a*b, return lo, write hi to [*hi]. *)
Definition secp256k1_umul128_spec : ident * funspec :=
  DECLARE _secp256k1_umul128
  WITH a : UInt64, b : UInt64, hi_ptr : val, sh : share
  PRE [ tulong, tulong, tptr tulong ]
    PROP (writable_share sh)
    PARAMS (uint64_to_val a; uint64_to_val b; hi_ptr)
    SEP (data_at_ sh tulong hi_ptr)
  POST [ tulong ]
    EX result : UInt128,
    PROP (result = mul_64 a b)
    RETURN (uint64_to_val (u128_lo result))
    SEP (data_at sh tulong (uint64_to_val (u128_hi result)) hi_ptr).

(** [secp256k1_u128_mul]: store a*b into uint128 struct [*r]. *)
Definition secp256k1_u128_mul_spec : ident * funspec :=
  DECLARE _secp256k1_u128_mul
  WITH r_ptr : val, a : UInt64, b : UInt64, sh : share
  PRE [ tptr (Tstruct __191 noattr), tulong, tulong ]
    PROP (writable_share sh)
    PARAMS (r_ptr; uint64_to_val a; uint64_to_val b)
    SEP (data_at_ sh (Tstruct __191 noattr) r_ptr)
  POST [ tvoid ]
    EX r : UInt128,
    PROP (r = mul_64 a b)
    RETURN ()
    SEP (data_at sh (Tstruct __191 noattr) (uint128_to_val r) r_ptr).

(* ================================================================= *)
(** ** Accumulator function specifications *)

(** [muladd]: add a*b to acc. c2 must never overflow. *)
Definition muladd_spec : ident * funspec :=
  DECLARE _muladd
  WITH acc_ptr : val, acc : Acc, a : UInt64, b : UInt64, sh : share
  PRE [ tptr (Tstruct __214 noattr), tulong, tulong ]
    PROP (writable_share sh;
          acc_val acc + Z.mul (u64_val a) (u64_val b) < 2^192)
    PARAMS (acc_ptr; uint64_to_val a; uint64_to_val b)
    SEP (data_at sh (Tstruct __214 noattr) (acc_to_val acc) acc_ptr)
  POST [ tvoid ]
    EX acc' : Acc,
    PROP (acc_val acc' = Z.add (acc_val acc) (Z.mul (u64_val a) (u64_val b)))
    RETURN ()
    SEP (data_at sh (Tstruct __214 noattr) (acc_to_val acc') acc_ptr).

(** [muladd_fast]: add a*b to (c0,c1). c1 must never overflow. *)
Definition muladd_fast_spec : ident * funspec :=
  DECLARE _muladd_fast
  WITH acc_ptr : val, acc : Acc, a : UInt64, b : UInt64, sh : share
  PRE [ tptr (Tstruct __214 noattr), tulong, tulong ]
    PROP (writable_share sh;
          acc_val acc + Z.mul (u64_val a) (u64_val b) < 2^128)
    PARAMS (acc_ptr; uint64_to_val a; uint64_to_val b)
    SEP (data_at sh (Tstruct __214 noattr) (acc_to_val acc) acc_ptr)
  POST [ tvoid ]
    EX acc' : Acc,
    PROP (acc_val acc' = Z.add (acc_val acc) (Z.mul (u64_val a) (u64_val b)))
    RETURN ()
    SEP (data_at sh (Tstruct __214 noattr) (acc_to_val acc') acc_ptr).

(** [extract]: extract lowest 64 bits, shift acc right by 64. *)
Definition extract_spec : ident * funspec :=
  DECLARE _extract
  WITH acc_ptr : val, acc : Acc, n_ptr : val, sh : share, sh_n : share
  PRE [ tptr (Tstruct __214 noattr), tptr tulong ]
    PROP (writable_share sh; writable_share sh_n)
    PARAMS (acc_ptr; n_ptr)
    SEP (data_at sh (Tstruct __214 noattr) (acc_to_val acc) acc_ptr;
         data_at_ sh_n tulong n_ptr)
  POST [ tvoid ]
    EX n : UInt64, EX acc' : Acc,
    PROP (n = acc_lo acc; acc_val acc' = acc_val acc / 2^64)
    RETURN ()
    SEP (data_at sh (Tstruct __214 noattr) (acc_to_val acc') acc_ptr;
         data_at sh_n tulong (uint64_to_val n) n_ptr).

(** [extract_fast]: extract lowest 64 bits, c2 required zero. *)
Definition extract_fast_spec : ident * funspec :=
  DECLARE _extract_fast
  WITH acc_ptr : val, acc : Acc, n_ptr : val, sh : share, sh_n : share
  PRE [ tptr (Tstruct __214 noattr), tptr tulong ]
    PROP (writable_share sh; writable_share sh_n;
          acc_val acc < 2^128)
    PARAMS (acc_ptr; n_ptr)
    SEP (data_at sh (Tstruct __214 noattr) (acc_to_val acc) acc_ptr;
         data_at_ sh_n tulong n_ptr)
  POST [ tvoid ]
    EX n : UInt64, EX acc' : Acc,
    PROP (n = acc_lo acc; acc_val acc' = acc_val acc / 2^64)
    RETURN ()
    SEP (data_at sh (Tstruct __214 noattr) (acc_to_val acc') acc_ptr;
         data_at sh_n tulong (uint64_to_val n) n_ptr).

(* ================================================================= *)
(** ** Gprog *)

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
