(** * Impl_scalar_4x64: Internal helper specs for scalar_4x64.c *)
(** These are implementation details -- u128 arithmetic, the 192-bit
    accumulator, muladd/extract helpers, and limb conversion machinery.
    Clients of the public API should only depend on [Spec_scalar_4x64]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
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

(** The [i]-th 64-bit limb of [x]: [(x / 2^(64*i)) mod 2^64]. *)
Definition limb64 (x : Z) (i : nat) : Z :=
  (x / 2^(64 * Z.of_nat i)) mod 2^64.

(** 64 x 64 -> 128-bit multiplication. *)
Program Definition mul_64 (a b : UInt64) : UInt128 :=
  mkUInt128 (u64_val a * u64_val b) _.
Next Obligation.
  destruct a as [av [Ha0 Ha1]], b as [bv [Hb0 Hb1]].
  simpl.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - change (Z.pow_pos 2 128) with (2^64 * 2^64).
    apply Z.mul_lt_mono_nonneg; lia.
Qed.

(** 256 x 256 -> 512-bit multiplication. *)
Program Definition mul_256 (a b : UInt256) : UInt512 :=
  mkUInt512 (u256_val a * u256_val b) _.
Next Obligation.
  destruct a as [av [Ha0 Ha1]], b as [bv [Hb0 Hb1]].
  simpl.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - change (Z.pow_pos 2 512) with (2^256 * 2^256).
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

(** Extract the [i]-th 64-bit limb of a [UInt256] as a [UInt64]. *)
Program Definition u256_limb (x : UInt256) (i : nat) : UInt64 :=
  mkUInt64 (limb64 (u256_val x) i) _.
Next Obligation. apply Z.mod_pos_bound. lia. Qed.

(* ================================================================= *)
(** ** C representation *)

(** Represent a [UInt64] as a C value. *)
Definition uint64_to_val (x : UInt64) : val :=
  Vlong (Int64.repr (u64_val x)).

(** Represent a [UInt128] as a C struct (lo, hi). *)
Definition uint128_to_val (x : UInt128) : reptype t_secp256k1_uint128 :=
  let v := u128_val x in
  (Vlong (Int64.repr (limb64 v 0)), Vlong (Int64.repr (limb64 v 1))).

(** Represent an [Acc] as a C struct (c0, c1, c2). *)
Definition acc_to_val (x : Acc) : reptype t_secp256k1_acc :=
  let v := acc_val x in
  (Vlong (Int64.repr (limb64 v 0)),
   (Vlong (Int64.repr (limb64 v 1)),
    Vlong (Int64.repr (limb64 v 2)))).

(** Represent a [UInt256] as a 4-limb C scalar struct. *)
Definition uint256_to_val (x : UInt256) : reptype t_secp256k1_uint256 :=
  let v := u256_val x in
  [ Vlong (Int64.repr (limb64 v 0));
    Vlong (Int64.repr (limb64 v 1));
    Vlong (Int64.repr (limb64 v 2));
    Vlong (Int64.repr (limb64 v 3)) ].

(** Widen a [Scalar] (< N < 2^256) to a [UInt256]. *)
Program Definition scalar_to_u256 (s : Scalar) : UInt256 :=
  mkUInt256 (scalar_val s) _.
Next Obligation.
  destruct s as [v [H0 H1]].
  simpl.
  split.
  - lia.
  - unfold secp256k1_N in H1.
    lia.
Qed.

(** [scalar_to_val] and [uint256_to_val o scalar_to_u256] agree. *)
Lemma scalar_to_val_eq (s : Scalar) :
  scalar_to_val s = uint256_to_val (scalar_to_u256 s).
Proof.
  destruct s as [v Hv].
  unfold scalar_to_val, uint256_to_val, scalar_to_u256.
  unfold limb64.
  simpl (Z.of_nat _).
  simpl (_ * _).
  rewrite Z.div_1_r.
  reflexivity.
Qed.

(** Represent a [UInt512] as an 8-limb C array. *)
Definition uint512_to_val (x : UInt512) : list val :=
  let v := u512_val x in
  [ Vlong (Int64.repr (limb64 v 0));
    Vlong (Int64.repr (limb64 v 1));
    Vlong (Int64.repr (limb64 v 2));
    Vlong (Int64.repr (limb64 v 3));
    Vlong (Int64.repr (limb64 v 4));
    Vlong (Int64.repr (limb64 v 5));
    Vlong (Int64.repr (limb64 v 6));
    Vlong (Int64.repr (limb64 v 7)) ].

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
(** ** Relating [uint256_to_val] to [uint64_to_val] / [u256_limb] *)

(** Each element of [uint256_to_val x] is [uint64_to_val (u256_limb x i)]. *)
Lemma uint256_to_val_Znth : forall (x : UInt256) (i : Z),
  0 <= i < 4 ->
  Znth i (uint256_to_val x) = uint64_to_val (u256_limb x (Z.to_nat i)).
Proof.
  intros x i Hi.
  unfold uint256_to_val, uint64_to_val, u256_limb.
  simpl.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct H as [Hi0|[Hi1|[Hi2|Hi3]]].
  all: subst i; reflexivity.
Qed.

(* ================================================================= *)
(** ** u128 function specifications *)

(** [secp256k1_u128_to_u64]: return the low 64 bits. *)
Definition secp256k1_u128_to_u64_spec : ident * funspec :=
  DECLARE _secp256k1_u128_to_u64
  WITH a_ptr : val, x : UInt128, sh : share
  PRE [ tptr t_secp256k1_uint128 ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val x) a_ptr)
  POST [ tulong ]
    EX r : UInt64,
    PROP (r = u128_lo x)
    RETURN (uint64_to_val r)
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val x) a_ptr).

(** [secp256k1_u128_hi_u64]: return the high 64 bits. *)
Definition secp256k1_u128_hi_u64_spec : ident * funspec :=
  DECLARE _secp256k1_u128_hi_u64
  WITH a_ptr : val, x : UInt128, sh : share
  PRE [ tptr t_secp256k1_uint128 ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val x) a_ptr)
  POST [ tulong ]
    EX r : UInt64,
    PROP (r = u128_hi x)
    RETURN (uint64_to_val r)
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val x) a_ptr).

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
  PRE [ tptr t_secp256k1_uint128, tulong, tulong ]
    PROP (writable_share sh)
    PARAMS (r_ptr; uint64_to_val a; uint64_to_val b)
    SEP (data_at_ sh t_secp256k1_uint128 r_ptr)
  POST [ tvoid ]
    EX r : UInt128,
    PROP (r = mul_64 a b)
    RETURN ()
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val r) r_ptr).

(* ================================================================= *)
(** ** Accumulator function specifications *)

(** [muladd]: add a*b to acc. c2 must never overflow. *)
Definition muladd_spec : ident * funspec :=
  DECLARE _muladd
  WITH acc_ptr : val, acc : Acc, a : UInt64, b : UInt64, sh : share
  PRE [ tptr t_secp256k1_acc, tulong, tulong ]
    PROP (writable_share sh;
          acc_val acc + Z.mul (u64_val a) (u64_val b) < 2^192)
    PARAMS (acc_ptr; uint64_to_val a; uint64_to_val b)
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc) acc_ptr)
  POST [ tvoid ]
    EX acc' : Acc,
    PROP (acc_val acc' = Z.add (acc_val acc) (Z.mul (u64_val a) (u64_val b)))
    RETURN ()
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc') acc_ptr).

(** [muladd_fast]: add a*b to (c0,c1). c1 must never overflow. *)
Definition muladd_fast_spec : ident * funspec :=
  DECLARE _muladd_fast
  WITH acc_ptr : val, acc : Acc, a : UInt64, b : UInt64, sh : share
  PRE [ tptr t_secp256k1_acc, tulong, tulong ]
    PROP (writable_share sh;
          acc_val acc + Z.mul (u64_val a) (u64_val b) < 2^128)
    PARAMS (acc_ptr; uint64_to_val a; uint64_to_val b)
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc) acc_ptr)
  POST [ tvoid ]
    EX acc' : Acc,
    PROP (acc_val acc' = Z.add (acc_val acc) (Z.mul (u64_val a) (u64_val b)))
    RETURN ()
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc') acc_ptr).

(** [sumadd]: add a to acc. c2 must never overflow. *)
Definition sumadd_spec : ident * funspec :=
  DECLARE _sumadd
  WITH acc_ptr : val, acc : Acc, a : UInt64, sh : share
  PRE [ tptr t_secp256k1_acc, tulong ]
    PROP (writable_share sh;
          Z.add (acc_val acc) (u64_val a) < 2^192)
    PARAMS (acc_ptr; uint64_to_val a)
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc) acc_ptr)
  POST [ tvoid ]
    EX acc' : Acc,
    PROP (acc_val acc' = Z.add (acc_val acc) (u64_val a))
    RETURN ()
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc') acc_ptr).

(** [sumadd_fast]: add a to (c0,c1). c1 must never overflow, c2 must be zero. *)
Definition sumadd_fast_spec : ident * funspec :=
  DECLARE _sumadd_fast
  WITH acc_ptr : val, acc : Acc, a : UInt64, sh : share
  PRE [ tptr t_secp256k1_acc, tulong ]
    PROP (writable_share sh;
          Z.add (acc_val acc) (u64_val a) < 2^128)
    PARAMS (acc_ptr; uint64_to_val a)
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc) acc_ptr)
  POST [ tvoid ]
    EX acc' : Acc,
    PROP (acc_val acc' = Z.add (acc_val acc) (u64_val a))
    RETURN ()
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc') acc_ptr).

(** [extract]: extract lowest 64 bits, shift acc right by 64. *)
Definition extract_spec : ident * funspec :=
  DECLARE _extract
  WITH acc_ptr : val, acc : Acc, n_ptr : val, sh : share, sh_n : share
  PRE [ tptr t_secp256k1_acc, tptr tulong ]
    PROP (writable_share sh; writable_share sh_n)
    PARAMS (acc_ptr; n_ptr)
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc) acc_ptr;
         data_at_ sh_n tulong n_ptr)
  POST [ tvoid ]
    EX n : UInt64, EX acc' : Acc,
    PROP (n = acc_lo acc; acc_val acc' = acc_val acc / 2^64)
    RETURN ()
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc') acc_ptr;
         data_at sh_n tulong (uint64_to_val n) n_ptr).

(** [extract_fast]: extract lowest 64 bits, c2 required zero. *)
Definition extract_fast_spec : ident * funspec :=
  DECLARE _extract_fast
  WITH acc_ptr : val, acc : Acc, n_ptr : val, sh : share, sh_n : share
  PRE [ tptr t_secp256k1_acc, tptr tulong ]
    PROP (writable_share sh; writable_share sh_n;
          acc_val acc < 2^128)
    PARAMS (acc_ptr; n_ptr)
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc) acc_ptr;
         data_at_ sh_n tulong n_ptr)
  POST [ tvoid ]
    EX n : UInt64, EX acc' : Acc,
    PROP (n = acc_lo acc; acc_val acc' = acc_val acc / 2^64)
    RETURN ()
    SEP (data_at sh t_secp256k1_acc (acc_to_val acc') acc_ptr;
         data_at sh_n tulong (uint64_to_val n) n_ptr).

(* ================================================================= *)
(** ** Additional u128 function specifications *)

(** [secp256k1_u128_from_u64]: set r to a (zero-extended to 128 bits). *)
Definition secp256k1_u128_from_u64_spec : ident * funspec :=
  DECLARE _secp256k1_u128_from_u64
  WITH r_ptr : val, a : UInt64, sh : share
  PRE [ tptr t_secp256k1_uint128, tulong ]
    PROP (writable_share sh)
    PARAMS (r_ptr; uint64_to_val a)
    SEP (data_at_ sh t_secp256k1_uint128 r_ptr)
  POST [ tvoid ]
    EX r : UInt128,
    PROP (u128_val r = u64_val a)
    RETURN ()
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val r) r_ptr).

(** [secp256k1_u128_accum_u64]: add a 64-bit value to a 128-bit accumulator. *)
Definition secp256k1_u128_accum_u64_spec : ident * funspec :=
  DECLARE _secp256k1_u128_accum_u64
  WITH r_ptr : val, r : UInt128, a : UInt64, sh : share
  PRE [ tptr t_secp256k1_uint128, tulong ]
    PROP (writable_share sh;
          Z.add (u128_val r) (u64_val a) < 2^128)
    PARAMS (r_ptr; uint64_to_val a)
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val r) r_ptr)
  POST [ tvoid ]
    EX r' : UInt128,
    PROP (u128_val r' = Z.add (u128_val r) (u64_val a))
    RETURN ()
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val r') r_ptr).

(** [secp256k1_u128_accum_mul]: add a*b to a 128-bit accumulator. *)
Definition secp256k1_u128_accum_mul_spec : ident * funspec :=
  DECLARE _secp256k1_u128_accum_mul
  WITH r_ptr : val, r : UInt128, a : UInt64, b : UInt64, sh : share
  PRE [ tptr t_secp256k1_uint128, tulong, tulong ]
    PROP (writable_share sh;
          Z.add (u128_val r) (Z.mul (u64_val a) (u64_val b)) < 2^128)
    PARAMS (r_ptr; uint64_to_val a; uint64_to_val b)
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val r) r_ptr)
  POST [ tvoid ]
    EX r' : UInt128,
    PROP (u128_val r' = Z.add (u128_val r) (Z.mul (u64_val a) (u64_val b)))
    RETURN ()
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val r') r_ptr).

(** [secp256k1_u128_rshift]: right-shift by 64 bits. *)
Definition secp256k1_u128_rshift_spec : ident * funspec :=
  DECLARE _secp256k1_u128_rshift
  WITH r_ptr : val, r : UInt128, n : Z, sh : share
  PRE [ tptr t_secp256k1_uint128, tuint ]
    PROP (writable_share sh; n = 64)
    PARAMS (r_ptr; Vint (Int.repr n))
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val r) r_ptr)
  POST [ tvoid ]
    EX r' : UInt128,
    PROP (u128_val r' = Z.div (u128_val r) (2^64))
    RETURN ()
    SEP (data_at sh t_secp256k1_uint128 (uint128_to_val r') r_ptr).

(* ================================================================= *)
(** ** secp256k1 order constants *)

(** Limbs of the secp256k1 group order N. *)
Definition N_0 : Z := 0xBFD25E8CD0364141.
Definition N_1 : Z := 0xBAAEDCE6AF48A03B.
Definition N_2 : Z := 0xFFFFFFFFFFFFFFFE.
Definition N_3 : Z := 0xFFFFFFFFFFFFFFFF.

(** Limbs of 2^256 - N (the "complement"). *)
Definition N_C_0 : Z := 0x402DA1732FC9BEBF.
Definition N_C_1 : Z := 0x4551231950B75FC4.
Definition N_C_2 : Z := 1.

(** N decomposes into its four 64-bit limbs. *)
Lemma secp256k1_N_limbs :
  secp256k1_N = N_0 + N_1 * 2^64 + N_2 * 2^128 + N_3 * 2^192.
Proof. unfold secp256k1_N, N_0, N_1, N_2, N_3. lia. Qed.

(** 2^256 - N decomposes into its three 64-bit limbs. *)
Lemma secp256k1_N_C_limbs :
  2^256 - secp256k1_N = N_C_0 + N_C_1 * 2^64 + N_C_2 * 2^128.
Proof. unfold secp256k1_N, N_C_0, N_C_1, N_C_2. lia. Qed.

(** Range facts for the limb constants. *)
Lemma N_0_range : 0 <= N_0 < 2^64. Proof. unfold N_0; lia. Qed.
Lemma N_1_range : 0 <= N_1 < 2^64. Proof. unfold N_1; lia. Qed.
Lemma N_2_range : 0 <= N_2 < 2^64. Proof. unfold N_2; lia. Qed.
Lemma N_3_range : 0 <= N_3 < 2^64. Proof. unfold N_3; lia. Qed.
Lemma N_C_0_range : 0 <= N_C_0 < 2^64. Proof. unfold N_C_0; lia. Qed.
Lemma N_C_1_range : 0 <= N_C_1 < 2^64. Proof. unfold N_C_1; lia. Qed.
Lemma N_C_2_range : 0 <= N_C_2 < 2^64. Proof. unfold N_C_2; lia. Qed.

(* ================================================================= *)
(** ** Overflow check and conditional reduction *)

(** [secp256k1_scalar_check_overflow]: return 1 if a >= N, 0 otherwise. *)
Definition secp256k1_scalar_check_overflow_spec : ident * funspec :=
  DECLARE _secp256k1_scalar_check_overflow
  WITH a_ptr : val, a : UInt256, sh : share
  PRE [ tptr t_secp256k1_uint256 ]
    PROP (readable_share sh)
    PARAMS (a_ptr)
    SEP (data_at sh t_secp256k1_uint256 (uint256_to_val a) a_ptr)
  POST [ tint ]
    PROP ()
    RETURN (Vint (Int.repr (if Z_lt_dec (u256_val a) secp256k1_N then 0 else 1)))
    SEP (data_at sh t_secp256k1_uint256 (uint256_to_val a) a_ptr).

(** [secp256k1_scalar_reduce]: add [overflow * (2^256 - N)] to [r].
    Returns [overflow] unchanged.

    The C code simply ripple-adds [overflow * N_C_i] across the four
    limbs, discarding the final carry; the result is
    [(r + overflow * (2^256 - N)) mod 2^256]. *)
Definition secp256k1_scalar_reduce_spec : ident * funspec :=
  DECLARE _secp256k1_scalar_reduce
  WITH r_ptr : val, r : UInt256, overflow : Z, sh : share
  PRE [ tptr t_secp256k1_uint256, tuint ]
    PROP (writable_share sh;
          0 <= overflow <= 2)
    PARAMS (r_ptr; Vint (Int.repr overflow))
    SEP (data_at sh t_secp256k1_uint256 (uint256_to_val r) r_ptr)
  POST [ tint ]
    EX r' : UInt256,
    PROP (u256_val r' = (Z.add (u256_val r) (Z.mul overflow (Z.sub (2^256) secp256k1_N))) mod 2^256)
    RETURN (Vint (Int.repr overflow))
    SEP (data_at sh t_secp256k1_uint256 (uint256_to_val r') r_ptr).

(* ================================================================= *)
(** ** secp256k1_scalar_mul_512 *)

(** Specification for [secp256k1_scalar_mul_512] (internal).

    Postcondition: the 8-limb array at [l8_ptr], interpreted as a
    [UInt512], equals [mul_256 a b]. *)
Definition secp256k1_scalar_mul_512_spec : ident * funspec :=
  DECLARE _secp256k1_scalar_mul_512
  WITH l8_ptr : val, a_ptr : val, b_ptr : val,
       a : UInt256, b : UInt256,
       sh_l : share, sh_a : share, sh_b : share
  PRE [ tptr tulong, tptr t_secp256k1_uint256, tptr t_secp256k1_uint256 ]
    PROP (writable_share sh_l;
          readable_share sh_a;
          readable_share sh_b)
    PARAMS (l8_ptr; a_ptr; b_ptr)
    SEP (data_at_ sh_l (tarray tulong 8) l8_ptr;
         data_at sh_a t_secp256k1_uint256 (uint256_to_val a) a_ptr;
         data_at sh_b t_secp256k1_uint256 (uint256_to_val b) b_ptr)
  POST [ tvoid ]
    EX r : UInt512,
    PROP (r = mul_256 a b)
    RETURN ()
    SEP (data_at sh_l (tarray tulong 8) (uint512_to_val r) l8_ptr;
         data_at sh_a t_secp256k1_uint256 (uint256_to_val a) a_ptr;
         data_at sh_b t_secp256k1_uint256 (uint256_to_val b) b_ptr).

(* ================================================================= *)
(** ** secp256k1_scalar_reduce_512 *)

(** Specification for [secp256k1_scalar_reduce_512] (internal).

    Postcondition: the scalar at [r_ptr] equals [l mod N]. *)
Definition secp256k1_scalar_reduce_512_spec : ident * funspec :=
  DECLARE _secp256k1_scalar_reduce_512
  WITH r_ptr : val, l_ptr : val,
       l : UInt512,
       sh_r : share, sh_l : share
  PRE [ tptr t_secp256k1_uint256, tptr tulong ]
    PROP (writable_share sh_r;
          readable_share sh_l)
    PARAMS (r_ptr; l_ptr)
    SEP (data_at_ sh_r t_secp256k1_uint256 r_ptr;
         data_at sh_l (tarray tulong 8) (uint512_to_val l) l_ptr)
  POST [ tvoid ]
    EX r : Scalar,
    PROP (scalar_val r = Z.modulo (u512_val l) secp256k1_N)
    RETURN ()
    SEP (data_at sh_r t_secp256k1_uint256 (scalar_to_val r) r_ptr;
         data_at sh_l (tarray tulong 8) (uint512_to_val l) l_ptr).

(* ================================================================= *)
(** ** Gprog *)

Definition Gprog : funspecs :=
  ltac:(with_library prog [
    secp256k1_u128_to_u64_spec;
    secp256k1_u128_hi_u64_spec;
    secp256k1_umul128_spec;
    secp256k1_u128_mul_spec;
    secp256k1_u128_from_u64_spec;
    secp256k1_u128_accum_u64_spec;
    secp256k1_u128_accum_mul_spec;
    secp256k1_u128_rshift_spec;
    muladd_spec;
    muladd_fast_spec;
    sumadd_spec;
    sumadd_fast_spec;
    extract_spec;
    extract_fast_spec;
    secp256k1_scalar_check_overflow_spec;
    secp256k1_scalar_reduce_spec;
    secp256k1_scalar_mul_512_spec;
    secp256k1_scalar_reduce_512_spec;
    secp256k1_scalar_mul_spec
  ]).
