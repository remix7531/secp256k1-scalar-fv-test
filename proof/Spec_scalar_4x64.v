(** * Spec_scalar_4x64: Functional model and API specs for scalar_4x64.c *)

Require Import VST.floyd.proofauto.
Require Import scalar_4x64.scalar_4x64.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(* ================================================================= *)
(** ** Functional model *)

(** A 128-bit unsigned integer represented as two 64-bit limbs. *)
Definition u128_val (lo hi : Z) : reptype (Tstruct __191 noattr) :=
  (Vlong (Int64.repr lo), Vlong (Int64.repr hi)).

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

(** Collect all specs into Gprog. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [
    secp256k1_u128_to_u64_spec;
    secp256k1_u128_hi_u64_spec
  ]).
