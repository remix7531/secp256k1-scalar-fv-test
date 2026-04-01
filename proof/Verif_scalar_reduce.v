(** * Verif_scalar_reduce: Proof of body_secp256k1_scalar_reduce *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.
Require Import scalar_4x64.Helper_forward_call.

(* ================================================================= *)
(** ** secp256k1_scalar_reduce *)

(** [Int64.mul (repr a) (repr b) = repr (a * b)] when all values
    fit in unsigned 64-bit range. *)
Lemma Int64_mul_repr : forall a b,
  0 <= a <= Int64.max_unsigned ->
  0 <= b <= Int64.max_unsigned ->
  0 <= a * b <= Int64.max_unsigned ->
  Int64.mul (Int64.repr a) (Int64.repr b) = Int64.repr (a * b).
Proof.
  intros.
  unfold Int64.mul.
  rewrite !Int64.unsigned_repr by lia.
  reflexivity.
Qed.

(** The C expression [~(int64_t)N_0 + 1] evaluates to [N_C_0]. *)
Lemma N_C_0_expr :
  Int64.add (Int64.not (Int64.repr (-4624529908474429119))) (Int64.repr 1)
  = Int64.repr N_C_0.
Proof.
  unfold N_C_0.
  apply Int64.eqm_samerepr.
  vm_compute.
  exists 0.
  lia.
Qed.

(** The C expression [~(int64_t)N_1] evaluates to [N_C_1]. *)
Lemma N_C_1_expr :
  Int64.not (Int64.repr (-4994812053365940165)) = Int64.repr N_C_1.
Proof.
  unfold N_C_1.
  apply Int64.eqm_samerepr.
  vm_compute.
  exists 0.
  lia.
Qed.

(** Accumulator-fits-in-u128: carry (< 2*2^64) plus a 64-bit value. *)
Lemma reduce_accum_bound : forall x y,
  0 <= x -> x < 2 * 2^64 -> 0 <= y < 2^64 ->
  x + y < 2^128.
Proof. lia. Qed.

(** Each carry is [< 2] because the intermediate sum is [< 2*2^64]. *)
Lemma reduce_carry_lt_2 : forall a,
  0 <= a -> a < 2 * 2^64 ->
  0 <= a / 2^64 < 2.
Proof.
  intros.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

(** Solve VST expression-matching goals for [(uint64_t)overflow * N_C_i]. *)
Ltac solve_reduce_expr_match :=
  entailer!; simpl; unfold uint64_to_val; simpl u64_val;
  f_equal; f_equal; f_equal; simpl;
  first
    [ rewrite N_C_0_expr; apply Int64_mul_repr; unfold N_C_0; rep_lia
    | rewrite N_C_1_expr; apply Int64_mul_repr; unfold N_C_1; rep_lia
    | unfold N_C_2; rewrite Z.mul_1_r; reflexivity ].

(** Prove accumulator-fits-in-u128 by chaining carry bounds. *)
Ltac reduce_u128_bound :=
  simpl u64_val;
  unfold N_C_0, N_C_1, N_C_2 in *;
  repeat match goal with
  | |- context [?x / 2^64] =>
    let c := fresh "c" in
    set (c := x / 2^64) in *;
    pose proof (reduce_carry_lt_2 x ltac:(lia) ltac:(lia))
  end;
  apply reduce_accum_bound; lia.

Lemma body_secp256k1_scalar_reduce:
  semax_body Vprog Gprog
    f_secp256k1_scalar_reduce secp256k1_scalar_reduce_spec.
Proof.
  start_function.

  rename SH into Hsh_writable.
  rename H into Hov_range.       (* 0 <= overflow <= 2 *)

  (* --- Setup: name the four 64-bit limbs of r --- *)
  set (d0 := limb64 (u256_val r) 0).
  set (d1 := limb64 (u256_val r) 1).
  set (d2 := limb64 (u256_val r) 2).
  set (d3 := limb64 (u256_val r) 3).
  assert (Hd0 : 0 <= d0 < 2^64) by (subst d0; apply Z.mod_pos_bound; lia).
  assert (Hd1 : 0 <= d1 < 2^64) by (subst d1; apply Z.mod_pos_bound; lia).
  assert (Hd2 : 0 <= d2 < 2^64) by (subst d2; apply Z.mod_pos_bound; lia).
  assert (Hd3 : 0 <= d3 < 2^64) by (subst d3; apply Z.mod_pos_bound; lia).

  assert (Hov0 : 0 <= overflow * N_C_0 < 2^64) by rep_lia.
  assert (Hov1 : 0 <= overflow * N_C_1 < 2^64) by rep_lia.
  assert (Hov2 : 0 <= overflow * N_C_2 < 2^64) by rep_lia.

  (* ===== Round 0: t = d[0] + overflow*N_C_0 ===== *)

  (* _t'8 = r->d[0] *)
  forward.

  (* secp256k1_u128_from_u64(&t, r->d[0]) *)
  forward_call_u128_from_u64 v_t (mkUInt64 d0 Hd0) Tsh t_init Ht_init.

  (* secp256k1_u128_accum_u64(&t, (uint64_t)overflow * N_C_0) *)
  forward_call_u128_accum_u64 v_t t_init (mkUInt64 (overflow * N_C_0) Hov0) Tsh acc0 Hacc0_raw.
  { solve_reduce_expr_match. }

  assert (Hacc0 : u128_val acc0 = d0 + overflow * N_C_0)
    by (rewrite Hacc0_raw, Ht_init; simpl; lia).
  clear Ht_init Hacc0_raw t_init.

  (* r->d[0] = secp256k1_u128_to_u64(&t) *)
  forward_call_u128_to_u64 v_t acc0 Tsh lo0 Hlo0.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call_u128_rshift v_t acc0 Tsh carry0 Hcarry0.

  assert (Hcarry0_val : u128_val carry0 = (d0 + overflow * N_C_0) / 2^64)
    by (rewrite Hcarry0, Hacc0; reflexivity).
  clear Hcarry0.

  (* ===== Round 1: t += d[1] + overflow*N_C_1 ===== *)

  (* _t'7 = r->d[1] *)
  forward.

  (* secp256k1_u128_accum_u64(&t, r->d[1]) *)
  forward_call_u128_accum_u64 v_t carry0 (mkUInt64 d1 Hd1) Tsh t1a Ht1a.
  { rewrite Hcarry0_val.
    reduce_u128_bound. }

  (* secp256k1_u128_accum_u64(&t, (uint64_t)overflow * ~N_1) *)
  forward_call_u128_accum_u64 v_t t1a (mkUInt64 (overflow * N_C_1) Hov1) Tsh acc1 Hacc1_raw.
  { solve_reduce_expr_match. }
  { rewrite Ht1a.
    simpl u64_val.
    rewrite Hcarry0_val.
    reduce_u128_bound. }
  assert (Hacc1 : u128_val acc1 =
    (d0 + overflow * N_C_0) / 2^64 + d1 + overflow * N_C_1)
    by (rewrite Hacc1_raw, Ht1a; simpl u64_val; rewrite Hcarry0_val; lia).
  clear Ht1a Hacc1_raw Hcarry0_val carry0 t1a.

  (* r->d[1] = secp256k1_u128_to_u64(&t) *)
  forward_call_u128_to_u64 v_t acc1 Tsh lo1 Hlo1.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call_u128_rshift v_t acc1 Tsh carry1 Hcarry1.

  assert (Hcarry1_val : u128_val carry1 = u128_val acc1 / 2^64)
    by exact Hcarry1.
  clear Hcarry1.

  (* ===== Round 2: t += d[2] + overflow*N_C_2 ===== *)

  (* _t'6 = r->d[2] *)
  forward.

  (* secp256k1_u128_accum_u64(&t, r->d[2]) *)
  forward_call_u128_accum_u64 v_t carry1 (mkUInt64 d2 Hd2) Tsh t2a Ht2a.
  { rewrite Hcarry1_val, Hacc1.
    reduce_u128_bound. }

  (* secp256k1_u128_accum_u64(&t, (uint64_t)overflow * N_C_2) *)
  forward_call_u128_accum_u64 v_t t2a (mkUInt64 (overflow * N_C_2) Hov2) Tsh acc2 Hacc2_raw.
  { solve_reduce_expr_match. }
  { rewrite Ht2a.
    simpl u64_val.
    rewrite Hcarry1_val, Hacc1.
    reduce_u128_bound. }
  assert (Hacc2 : u128_val acc2 =
    ((d0 + overflow * N_C_0) / 2^64 + d1 + overflow * N_C_1) / 2^64
    + d2 + overflow * N_C_2)
    by (rewrite Hacc2_raw, Ht2a; simpl u64_val; rewrite Hcarry1_val, Hacc1; lia).
  clear Ht2a Hacc2_raw Hcarry1_val carry1 t2a.

  (* r->d[2] = secp256k1_u128_to_u64(&t) *)
  forward_call_u128_to_u64 v_t acc2 Tsh lo2 Hlo2.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call_u128_rshift v_t acc2 Tsh carry2 Hcarry2.

  assert (Hcarry2_val : u128_val carry2 = u128_val acc2 / 2^64)
    by exact Hcarry2.
  clear Hcarry2.

  (* ===== Round 3: t += d[3] (no complement term) ===== *)

  (* _t'5 = r->d[3] *)
  forward.

  (* secp256k1_u128_accum_u64(&t, r->d[3]) *)
  forward_call_u128_accum_u64 v_t carry2 (mkUInt64 d3 Hd3) Tsh acc3 Hacc3_raw.
  { rewrite Hcarry2_val, Hacc2.
    reduce_u128_bound. }
  assert (Hacc3 : u128_val acc3 =
    (((d0 + overflow * N_C_0) / 2^64 + d1 + overflow * N_C_1) / 2^64
     + d2 + overflow * N_C_2) / 2^64 + d3)
    by (rewrite Hacc3_raw; simpl u64_val; rewrite Hcarry2_val, Hacc2; lia).
  clear Hacc3_raw Hcarry2_val carry2.

  (* r->d[3] = secp256k1_u128_to_u64(&t) *)
  forward_call_u128_to_u64 v_t acc3 Tsh lo3 Hlo3.
  forward.

  (* return overflow *)
  forward.

  (* Clean up before postcondition *)
  clear Hov0 Hov1 Hov2.

  (* ===== Postcondition ===== *)

  set (result_val := (u256_val r + overflow * (2^256 - secp256k1_N)) mod 2^256).
  assert (Hresult_range' : 0 <= result_val < 2^256)
    by (subst result_val; apply Z.mod_pos_bound; lia).

  Exists (mkUInt256 result_val Hresult_range').
  entailer!.

  (* ---- VST cleanup ---- *)

  (* Goal: upd_Znth chain |-- uint256_to_val result *)
  apply derives_refl'.
  f_equal.

  (* Collapse the [upd_Znth] chain to a plain 4-element list *)
  transitivity [uint64_to_val (u128_lo acc0);
                uint64_to_val (u128_lo acc1);
                uint64_to_val (u128_lo acc2);
                uint64_to_val (u128_lo acc3)].
  { unfold uint256_to_val.
    simpl u256_val.
    reflexivity. }

  (* Unfold both sides to [Vlong (Int64.repr (limb64 ...))] form *)
  unfold uint256_to_val, uint64_to_val, u128_lo.
  simpl u64_val.
  simpl u256_val.

  (* Substitute accumulator values *)
  rewrite Hacc0, Hacc1, Hacc2, Hacc3.

  set (t0 := d0 + overflow * N_C_0).
  set (t1 := t0 / 2^64 + d1 + overflow * N_C_1).
  set (t2 := t1 / 2^64 + d2 + overflow * N_C_2).
  set (t3 := t2 / 2^64 + d3).

  (* Simplify [limb64 x 0 = x mod 2^64] on LHS *)
  unfold limb64 at 1 2 3 4.
  simpl Z.of_nat.
  simpl Z.mul.
  rewrite !Z.pow_0_r, !Z.div_1_r.

  (* Reduce to 4 pure Z equalities *)
  cut (t0 mod 2^64 = limb64 result_val 0 /\
       t1 mod 2^64 = limb64 result_val 1 /\
       t2 mod 2^64 = limb64 result_val 2 /\
       t3 mod 2^64 = limb64 result_val 3).
  { intros [-> [-> [-> ->]]].
    reflexivity. }

  assert (Hchain_bound :
    0 <= u256_val r + overflow * (2^256 - secp256k1_N) < 2 * 2^256).
  { pose proof (u256_range r). unfold secp256k1_N. lia. }

  clear - r overflow Hov_range Hchain_bound
          d0 d1 d2 d3 Hd0 Hd1 Hd2 Hd3
          t0 t1 t2 t3 result_val Hresult_range'.

  (* Bridge limb64 <-> limb: (x / 2^(64*i)) mod 2^64 = (x / (2^64)^i) mod 2^64 *)
  unfold limb64.
  rewrite !Z.pow_mul_r by lia.
  simpl (Z.of_nat _).

  (* ---- Pure Z ---- *)

  (* Decompose u256_val r into limbs *)
  assert (Hdecomp : u256_val r = d0 + d1 * 2^64 + d2 * 2^128 + d3 * 2^192).
  { subst d0 d1 d2 d3.
    pose proof (u256_as_eval4 r) as Heval.
    unfold eval4, u256_limb in Heval.
    simpl u64_val in Heval.
    change ((2^64)^2) with (2^128) in Heval.
    change ((2^64)^3) with (2^192) in Heval.
    lia. }

  (* Work with B = 2^64 *)
  set (B := 2^64) in *.

  (* Apply the carry-chain identity *)
  pose proof (reduce_carry_chain B d0 d1 d2 d3 N_C_0 N_C_1 N_C_2 overflow
    ltac:(subst B; lia) Hd0 Hd1 Hd2 Hd3
    ltac:(rep_lia) ltac:(rep_lia) ltac:(rep_lia)
    ltac:(lia)) as Hchain_raw.
  cbv zeta in Hchain_raw.
  fold t0 t1 t2 t3 in Hchain_raw.

  assert (HdecompB : u256_val r = d0 + d1 * B + d2 * (B*B) + d3 * (B*B*B))
    by (subst B; lia).
  rewrite <- HdecompB in Hchain_raw.
  set (C := N_C_0 + N_C_1 * B + N_C_2 * (B * B)) in *.
  assert (HC_eq : C = 2^256 - secp256k1_N) by (subst C B; rewrite secp256k1_N_C_limbs; ring).
  destruct (Hchain_raw ltac:(rewrite HC_eq; subst B; lia))
    as (Hchain_eq & Hr_z_bnd & Hhi_bnd).

  (* r_z = result_val via carry chain + mod *)
  set (r_z := (t0 mod B) + (t1 mod B) * B
            + (t2 mod B) * (B * B) + (t3 mod B) * (B * B * B)) in *.
  assert (Hchain : result_val = r_z).
  { subst result_val.
    rewrite <- HC_eq, <- Hchain_eq.
    replace (B * B * B * B) with (2^256) by (subst B; ring).
    rewrite Z_mod_plus_full.
    apply Z.mod_small. subst B. lia. }
  rewrite Hchain.
  clear Hchain Hchain_eq Hr_z_bnd Hhi_bnd Hchain_raw
        HC_eq result_val Hresult_range' Hchain_bound.

  (* Extract individual limbs via limbs_eval4 *)
  pose proof (limbs_eval4 B (t0 mod B) (t1 mod B) (t2 mod B) (t3 mod B)
    ltac:(subst B; lia)
    ltac:(apply Z.mod_pos_bound; subst B; lia)
    ltac:(apply Z.mod_pos_bound; subst B; lia)
    ltac:(apply Z.mod_pos_bound; subst B; lia)
    ltac:(apply Z.mod_pos_bound; subst B; lia)) as [Hl0 [Hl1 [Hl2 Hl3]]].
  unfold eval4 in Hl0, Hl1, Hl2, Hl3.
  replace (B^2) with (B * B) in Hl0, Hl1, Hl2, Hl3 by ring.
  replace (B^3) with (B * B * B) in Hl0, Hl1, Hl2, Hl3 by ring.
  clear - Hl0 Hl1 Hl2 Hl3.

  exact (conj (eq_sym Hl0) (conj (eq_sym Hl1) (conj (eq_sym Hl2) (eq_sym Hl3)))).
Qed.
