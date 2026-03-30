(** * Verif_scalar_check_overflow: Proof of body_secp256k1_scalar_check_overflow *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.

(* ================================================================= *)
(** ** secp256k1_scalar_check_overflow *)

(** The C cascade comparison correctly computes [a >= N].

    After [repeat forward], the postcondition is a single pure equality
    between an [Int.or/and/not] cascade and the spec.  We unfold
    [Int64.ltu] to expose [zlt] decisions on concrete N-limb values,
    destruct all six comparisons (2^6 = 64 branches), let [simpl]
    evaluate the boolean/Int arithmetic, and close every branch with
    [reflexivity], [discriminate], or [lia]. *)
Lemma body_secp256k1_scalar_check_overflow:
  semax_body Vprog Gprog
    f_secp256k1_scalar_check_overflow secp256k1_scalar_check_overflow_spec.
Proof.
  start_function.

  (* yes = 0 *)
  forward. (* _yes = 0 *)

  (* no = 0 *)
  forward. (* _no = 0 *)

  (* no |= (a->d[3] < N_3) *)
  forward. (* _t'6 = a->d[3] *)
  forward. (* _no = _no | (_t'6 < N_3) *)

  (* no |= (a->d[2] < N_2) *)
  forward. (* _t'5 = a->d[2] *)
  forward. (* _no = _no | (_t'5 < N_2) *)

  (* yes |= (a->d[2] > N_2) & ~no *)
  forward. (* _t'4 = a->d[2] *)
  forward. (* _yes = _yes | ((_t'4 > N_2) & ~_no) *)

  (* yes |= (a->d[1] > N_1) & ~no *)
  forward. (* _t'3 = a->d[1] *)
  forward. (* _no = _no | (_t'3 < N_1) *)

  (* no |= (a->d[1] < N_1) & ~yes *)
  forward. (* _t'2 = a->d[1] *)
  forward. (* _yes = _yes | ((_t'2 > N_1) & ~_no) *)

  (* yes |= (a->d[0] >= N_0) & ~no *)
  forward. (* _t'1 = a->d[0] *)
  forward. (* _yes = _yes | ((_t'1 >= N_0) & ~_no) *)

  (* return yes *)
  forward.
  apply prop_right.

  (* Expose Int64.ltu under the Int64.cmpu wrappers *)
  unfold Int64.cmpu.

  (* Name the four limbs and establish their ranges *)
  set (d0 := limb64 (u256_val a) 0).
  set (d1 := limb64 (u256_val a) 1).
  set (d2 := limb64 (u256_val a) 2).
  set (d3 := limb64 (u256_val a) 3).
  assert (Hd0 : 0 <= d0 < 2^64) by (subst d0; apply Z.mod_pos_bound; lia).
  assert (Hd1 : 0 <= d1 < 2^64) by (subst d1; apply Z.mod_pos_bound; lia).
  assert (Hd2 : 0 <= d2 < 2^64) by (subst d2; apply Z.mod_pos_bound; lia).
  assert (Hd3 : 0 <= d3 < 2^64) by (subst d3; apply Z.mod_pos_bound; lia).

  (* Limb decomposition via u256_as_eval4 *)
  assert (Hdecomp : u256_val a = d0 + d1 * 2^64 + d2 * 2^128 + d3 * 2^192).
  { subst d0 d1 d2 d3.
    pose proof (u256_as_eval4 a) as Heval.
    unfold eval4, u256_limb in Heval.
    simpl u64_val in Heval.
    change ((2^64)^2) with (2^128) in Heval.
    change ((2^64)^3) with (2^192) in Heval.
    lia. }

  (* Unfold Int64.ltu to zlt; replace limb unsigned_repr (in range)
     and evaluate the negative-constant unsigned values to N limbs *)
  unfold Int64.ltu.
  rewrite ?(Int64.unsigned_repr d0), ?(Int64.unsigned_repr d1),
          ?(Int64.unsigned_repr d2), ?(Int64.unsigned_repr d3) by rep_lia.
  change (Int64.unsigned (Int64.repr (-1))) with N_3 in *.
  change (Int64.unsigned (Int64.repr (-2))) with N_2 in *.
  change (Int64.unsigned (Int64.repr (-4994812053365940165))) with N_1 in *.
  change (Int64.unsigned (Int64.repr (-4624529908474429119))) with N_0 in *.

  (* Destruct all 6 zlt comparisons (d3<N_3, d2<N_2, N_2<d2, d1<N_1,
     N_1<d1, d0<N_0), creating 64 branches with concrete Z hypotheses *)
  do 6 match goal with |- context [zlt ?a ?b] => destruct (zlt a b) end.

  (* In each branch: evaluate Z.b2z/Z.lor to 0 or 1, simplify Int
     arithmetic on small concrete values, then split on the spec *)
  all: simpl Z.b2z.
  all: simpl Z.lor.
  all: rewrite ?Int.or_zero_l, ?Int.or_zero, ?Int.and_zero_l, ?Int.and_zero.
  all: destruct (Z_lt_dec (u256_val a) secp256k1_N).
  all: try reflexivity.
  all: try discriminate.

  (* Remaining goals: False from a contradictory combination of limb
     comparisons and Z_lt_dec.  Unfold N constants and close with lia. *)
  all: exfalso.
  all: unfold secp256k1_N, N_0, N_1, N_2, N_3 in *.
  all: lia.
Qed.
