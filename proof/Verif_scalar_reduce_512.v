(** * Verif_scalar_reduce_512: Proof of body_secp256k1_scalar_reduce_512 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.
Require Import scalar_4x64.Helper_forward_call.

(* ================================================================= *)
(** ** secp256k1_scalar_reduce_512 *)
(** Three-stage modular folding: 512 -> 385 -> 258 -> 256 bits. *)

(* ----------------------------------------------------------------- *)
(** *** Helper lemmas and tactics *)

(** Normalize [limb64 x 0] to [x mod 2^64]. *)
Ltac norm_limb64_0 :=
  unfold limb64; simpl Z.of_nat; simpl Z.mul;
  rewrite ?Z.pow_0_r, ?Z.div_1_r.

Lemma round_identity : forall (acc : Acc) (lo : UInt64) (carry : Acc),
  lo = acc_lo acc ->
  acc_val carry = acc_val acc / 2^64 ->
  u64_val lo + acc_val carry * 2^64 = acc_val acc.
Proof.
  intros.
  rewrite H.
  unfold acc_lo.
  simpl u64_val.
  norm_limb64_0.
  rewrite H0.
  pose proof (Z_div_mod_eq_full (acc_val acc) (2^64)).
  lia.
Qed.

Lemma acc_init_eq : forall v (Hv : 0 <= v < 2^192),
  0 <= v < 2^64 ->
  (Vlong (Int64.repr v), (Vlong (Int64.repr 0), Vlong (Int64.repr 0)))
  = acc_to_val (mkAcc v Hv).
Proof.
  intros.
  unfold acc_to_val.
  simpl acc_val.
  norm_limb64_0.
  rewrite Zmod_small by lia.
  rewrite Z.div_small by lia.
  replace (v / 2^128) with 0 by (symmetry; apply Z.div_small; lia).
  reflexivity.
Qed.

Lemma u128_lo_val : forall x : UInt128,
  u64_val (u128_lo x) = u128_val x mod 2^64.
Proof.
  intros.
  unfold u128_lo.
  simpl u64_val.
  norm_limb64_0.
  reflexivity.
Qed.

Lemma u128_hi_val : forall x : UInt128,
  u64_val (u128_hi x) = u128_val x / 2^64.
Proof.
  intros.
  unfold u128_hi.
  simpl u64_val.
  unfold limb64.
  simpl Z.of_nat.
  simpl Z.mul.
  change (64 * 1) with 64.
  rewrite Zmod_small; [reflexivity|].
  pose proof (u128_range x).
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma Int_repr_mod_Int64 : forall x,
  Int.repr (x mod Int64.modulus) = Int.repr x.
Proof.
  intros.
  apply Int.eqm_samerepr.
  unfold Int.eqm, Zbits.eqmod.
  change Int64.modulus with (2^64).
  change Int.modulus with (2^32).
  exists (- (x / 2^64) * 2^32).
  rewrite Zmod_eq by lia.
  lia.
Qed.

Lemma limb64_is_limb : forall x i, limb64 x i = limb (2^64) x i.
Proof.
  intros.
  unfold limb64, limb.
  do 2 f_equal.
  rewrite <- Z.pow_mul_r by lia.
  reflexivity.
Qed.

Lemma uint256_from_limbs :
  forall (v0 v1 v2 v3 : UInt64),
  let r_z := u64_val v0 + u64_val v1 * 2^64
           + u64_val v2 * 2^128 + u64_val v3 * 2^192 in
  forall (Hr : 0 <= r_z < 2^256),
  [uint64_to_val v0; uint64_to_val v1;
   uint64_to_val v2; uint64_to_val v3]
  = uint256_to_val (mkUInt256 r_z Hr).
Proof.
  intros v0 v1 v2 v3 r_z Hr.
  pose proof (u64_range v0) as Hv0.
  pose proof (u64_range v1) as Hv1.
  pose proof (u64_range v2) as Hv2.
  pose proof (u64_range v3) as Hv3.
  assert (Hr_eval : r_z = eval4 (2^64) (u64_val v0) (u64_val v1) (u64_val v2) (u64_val v3)).
  { unfold eval4, r_z.
    change ((2^64)^2) with (2^128).
    change ((2^64)^3) with (2^192).
    ring. }
  pose proof (limbs_eval4 (2^64) (u64_val v0) (u64_val v1) (u64_val v2) (u64_val v3)
    ltac:(lia) Hv0 Hv1 Hv2 Hv3) as [Hl0 [Hl1 [Hl2 Hl3]]].
  rewrite <- limb64_is_limb in Hl0, Hl1, Hl2, Hl3.
  rewrite <- Hr_eval in Hl0, Hl1, Hl2, Hl3.
  unfold uint256_to_val.
  simpl u256_val.
  rewrite Hl0, Hl1, Hl2, Hl3.
  unfold uint64_to_val.
  reflexivity.
Qed.

(** Address arithmetic: [p + i] = field_address for tarray tulong 8. *)
Lemma array_access_hint : forall (p : val) (i : Z),
  field_compatible (tarray tulong 8) [] p ->
  0 <= i < 8 ->
  force_val (sem_add_ptr_int tulong Signed p (Vint (Int.repr i)))
  = field_address (tarray tulong 8) (SUB i) p.
Proof.
  intros p i Hfc Hi.
  rewrite arr_field_address by auto.
  rewrite sem_add_pi'.
  - reflexivity.
  - auto.
  - destruct Hfc; auto.
  - rep_lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Main proof *)

Lemma body_secp256k1_scalar_reduce_512:
  semax_body Vprog Gprog
    f_secp256k1_scalar_reduce_512 secp256k1_scalar_reduce_512_spec.
Proof.
  start_function.
  rename SH into Hsh_r_writable.
  rename SH0 into Hsh_l_readable.

  (* --- Setup --- *)

  assert_PROP (field_compatible (tarray tulong 8) [] l_ptr) as Hfc
    by entailer!.

  (* Name the 8 input limbs *)
  set (l0 := limb64 (u512_val l) 0).
  set (l1 := limb64 (u512_val l) 1).
  set (l2 := limb64 (u512_val l) 2).
  set (l3 := limb64 (u512_val l) 3).
  set (n0 := limb64 (u512_val l) 4).
  set (n1 := limb64 (u512_val l) 5).
  set (n2 := limb64 (u512_val l) 6).
  set (n3 := limb64 (u512_val l) 7).

  (* Range facts *)
  assert (Hl0 : 0 <= l0 < 2^64) by (subst l0; apply Z.mod_pos_bound; lia).
  assert (Hl1 : 0 <= l1 < 2^64) by (subst l1; apply Z.mod_pos_bound; lia).
  assert (Hl2 : 0 <= l2 < 2^64) by (subst l2; apply Z.mod_pos_bound; lia).
  assert (Hl3 : 0 <= l3 < 2^64) by (subst l3; apply Z.mod_pos_bound; lia).
  assert (Hn0 : 0 <= n0 < 2^64) by (subst n0; apply Z.mod_pos_bound; lia).
  assert (Hn1 : 0 <= n1 < 2^64) by (subst n1; apply Z.mod_pos_bound; lia).
  assert (Hn2 : 0 <= n2 < 2^64) by (subst n2; apply Z.mod_pos_bound; lia).
  assert (Hn3 : 0 <= n3 < 2^64) by (subst n3; apply Z.mod_pos_bound; lia).

  (* Inhabitant for Scalar -- needed by deadvars! *)
  assert (Inh_Scalar : Scalar)
    by exact (mkScalar 0 ltac:(unfold secp256k1_N; lia)).

  (* Concrete upper bounds for N_C constants *)
  assert (HNC0 : N_C_0 < 2^63) by rep_lia.
  assert (HNC1 : N_C_1 < 2^63) by rep_lia.
  assert (HNC0_nn : 0 <= N_C_0) by rep_lia.
  assert (HNC1_nn : 0 <= N_C_1) by rep_lia.

  (* Product bounds: x * N_C_j <= (2^64-1) * N_C_j < 2^127 *)
  assert (Hprod_NC0 : forall x, 0 <= x < 2^64 -> x * N_C_0 <= (2^64 - 1) * N_C_0)
    by (intros; apply Z.mul_le_mono_nonneg_r; rep_lia).
  assert (Hprod_NC1 : forall x, 0 <= x < 2^64 -> x * N_C_1 <= (2^64 - 1) * N_C_1)
    by (intros; apply Z.mul_le_mono_nonneg_r; rep_lia).
  assert (HNC0_prod_bound : (2^64 - 1) * N_C_0 < 2^127) by rep_lia.
  assert (HNC1_prod_bound : (2^64 - 1) * N_C_1 < 2^127) by rep_lia.

  (* Convert data_at -> field_at for array element access *)
  change (data_at sh_l (tarray tulong 8) (uint512_to_val l) l_ptr)
    with (field_at sh_l (tarray tulong 8) [] (uint512_to_val l) l_ptr).

  (* ===== Load n0..n3 from l[4..7] ===== *)

  (* n0 = l[4] *)
  pose proof (array_access_hint l_ptr 4 Hfc ltac:(lia)) as _.
  forward.

  (* n1 = l[5] *)
  pose proof (array_access_hint l_ptr 5 Hfc ltac:(lia)) as _.
  forward.

  (* n2 = l[6] *)
  pose proof (array_access_hint l_ptr 6 Hfc ltac:(lia)) as _.
  forward.

  (* n3 = l[7] *)
  pose proof (array_access_hint l_ptr 7 Hfc ltac:(lia)) as _.
  forward.

  (* ===== Stage 1: Reduce 512 -> 385 bits ===== *)
  (* m[0..6] = l[0..3] + n[0..3] * SECP256K1_N_C *)

  (* _t'26 = l[0] *)
  pose proof (array_access_hint l_ptr 0 Hfc ltac:(lia)) as _.
  forward.

  (* acc = { l[0], 0, 0 } *)
  forward. (* acc.c0 = _t'26 *)
  forward. (* acc.c1 = 0 *)
  forward. (* acc.c2 = 0 *)
  autorewrite with norm.

  (* Fold acc struct into acc_to_val form *)
  assert (Hacc_s1_init_range : 0 <= l0 < 2^192) by lia.
  set (acc_s1_init := mkAcc l0 Hacc_s1_init_range).
  assert (Hacc_eq : data_at Tsh t_secp256k1_acc
      (Vlong (Int64.repr l0), (Vlong (Int64.repr 0), Vlong (Int64.repr 0))) v_acc
    = data_at Tsh t_secp256k1_acc (acc_to_val acc_s1_init) v_acc)
    by (f_equal; exact (acc_init_eq l0 Hacc_s1_init_range Hl0)).
  sep_apply (derives_refl' _ _ Hacc_eq).
  clear Hacc_eq.

  (* ===== Round 0: muladd_fast(n0, N_C_0); extract_fast -> m0 ===== *)

  (* muladd_fast(&acc, n0, N_C_0) *)
  forward_call_muladd_fast v_acc acc_s1_init
                (mkUInt64 n0 Hn0) (mkUInt64 N_C_0 N_C_0_range) acc_s1_0 Hacc_s1_0.
  { (* acc_val acc_s1_init + n0 * N_C_0 < 2^128 *)
    simpl.
    pose proof (Hprod_NC0 n0 Hn0).
    lia. }

  assert (Hacc_s1_0v : acc_val acc_s1_0 = l0 + n0 * N_C_0)
    by (rewrite Hacc_s1_0; simpl; lia).

  (* extract_fast(&acc, &m0) *)
  forward_call_extract_fast v_acc acc_s1_0 v_m0 Tsh Tsh m0_u64 carry_s1_0 Hm0_eq Hcarry_s1_0_eq.

  assert (Hcarry_s1_0_ub : acc_val carry_s1_0 <= N_C_0).
  { rewrite Hcarry_s1_0_eq, Hacc_s1_0v.
    apply (Z.le_trans _ (((2^64 - 1) + (2^64 - 1) * N_C_0) / 2^64)).
    - apply Z.div_le_mono; [lia | pose proof (Hprod_NC0 n0 Hn0); lia].
    - unfold N_C_0.
      reflexivity. }

  clear acc_s1_init Hacc_s1_init_range Hacc_s1_0.

  (* ===== Round 1: sumadd_fast(l[1]); muladd(n1,NC0); muladd(n0,NC1); extract -> m1 ===== *)

  (* _t'25 = l[1] *)
  pose proof (array_access_hint l_ptr 1 Hfc ltac:(lia)) as _.
  forward.

  (* sumadd_fast(&acc, l[1]) *)
  forward_call_sumadd_fast v_acc carry_s1_0 (mkUInt64 l1 Hl1) acc_s1_1a Hacc_s1_1a.

  (* muladd(&acc, n1, N_C_0) *)
  forward_call_muladd v_acc acc_s1_1a
                (mkUInt64 n1 Hn1) (mkUInt64 N_C_0 N_C_0_range) acc_s1_1b Hacc_s1_1b.

  (* muladd(&acc, n0, N_C_1) *)
  forward_call_muladd v_acc acc_s1_1b
                (mkUInt64 n0 Hn0) (mkUInt64 N_C_1 N_C_1_range) acc_s1_1 Hacc_s1_1.

  (* extract(&acc, &m1) *)
  forward_call_extract v_acc acc_s1_1 v_m1 Tsh Tsh m1_u64 carry_s1_1 Hm1_eq Hcarry_s1_1_eq.

  (* Clean accumulator value for congruence proof *)
  assert (Hacc_s1_1_val : acc_val acc_s1_1 = acc_val carry_s1_0 + l1 + n1 * N_C_0 + n0 * N_C_1)
    by (rewrite Hacc_s1_1, Hacc_s1_1b, Hacc_s1_1a; simpl; lia).

  assert (Hcarry_s1_1_ub : acc_val carry_s1_1 <= N_C_0 + N_C_1).
  { rewrite Hcarry_s1_1_eq, Hacc_s1_1_val.
    apply (Z.le_trans _ ((N_C_0 + (2^64 - 1) + (2^64 - 1) * N_C_0 + (2^64 - 1) * N_C_1) / 2^64)).
    - apply Z.div_le_mono; try lia.
      pose proof (Hprod_NC0 n1 Hn1).
      pose proof (Hprod_NC1 n0 Hn0).
      lia.
    - unfold N_C_0, N_C_1.
      reflexivity. }

  clear acc_s1_1a Hacc_s1_1a acc_s1_1b Hacc_s1_1b Hacc_s1_1.

  (* ===== Round 2: sumadd(l[2]); muladd(n2,NC0); muladd(n1,NC1); sumadd(n0); extract -> m2 ===== *)

  (* _t'24 = l[2] *)
  pose proof (array_access_hint l_ptr 2 Hfc ltac:(lia)) as _.
  forward.

  (* sumadd(&acc, l[2]) *)
  forward_call_sumadd v_acc carry_s1_1 (mkUInt64 l2 Hl2) acc_s1_2a Hacc_s1_2a.

  (* muladd(&acc, n2, N_C_0) *)
  forward_call_muladd v_acc acc_s1_2a
                (mkUInt64 n2 Hn2) (mkUInt64 N_C_0 N_C_0_range) acc_s1_2b Hacc_s1_2b.

  (* muladd(&acc, n1, N_C_1) *)
  forward_call_muladd v_acc acc_s1_2b
                (mkUInt64 n1 Hn1) (mkUInt64 N_C_1 N_C_1_range) acc_s1_2c Hacc_s1_2c.

  (* sumadd(&acc, n0) *)
  forward_call_sumadd v_acc acc_s1_2c (mkUInt64 n0 Hn0) acc_s1_2 Hacc_s1_2.

  (* extract(&acc, &m2) *)
  forward_call_extract v_acc acc_s1_2 v_m2 Tsh Tsh m2_u64 carry_s1_2 Hm2_eq Hcarry_s1_2_eq.

  assert (Hacc_s1_2_val : acc_val acc_s1_2 =
    acc_val carry_s1_1 + l2 + n2 * N_C_0 + n1 * N_C_1 + n0)
    by (rewrite Hacc_s1_2, Hacc_s1_2c, Hacc_s1_2b, Hacc_s1_2a; simpl; lia).

  assert (Hcarry_s1_2_ub : acc_val carry_s1_2 <= N_C_0 + N_C_1 + 1).
  { rewrite Hcarry_s1_2_eq, Hacc_s1_2_val.
    apply (Z.le_trans _ (((N_C_0 + N_C_1) + (2^64 - 1)
      + (2^64 - 1) * N_C_0 + (2^64 - 1) * N_C_1 + (2^64 - 1)) / 2^64)).
    - apply Z.div_le_mono; try lia.
      pose proof (Hprod_NC0 n2 Hn2).
      pose proof (Hprod_NC1 n1 Hn1).
      lia.
    - unfold N_C_0, N_C_1.
      reflexivity. }

  clear acc_s1_2a Hacc_s1_2a acc_s1_2b Hacc_s1_2b acc_s1_2c Hacc_s1_2c Hacc_s1_2.

  (* ===== Round 3: sumadd(l[3]); muladd(n3,NC0); muladd(n2,NC1); sumadd(n1); extract -> m3 ===== *)

  (* _t'23 = l[3] *)
  pose proof (array_access_hint l_ptr 3 Hfc ltac:(lia)) as _.
  forward.

  (* sumadd(&acc, l[3]) *)
  forward_call_sumadd v_acc carry_s1_2 (mkUInt64 l3 Hl3) acc_s1_3a Hacc_s1_3a.

  (* muladd(&acc, n3, N_C_0) *)
  forward_call_muladd v_acc acc_s1_3a
                (mkUInt64 n3 Hn3) (mkUInt64 N_C_0 N_C_0_range) acc_s1_3b Hacc_s1_3b.

  (* muladd(&acc, n2, N_C_1) *)
  forward_call_muladd v_acc acc_s1_3b
                (mkUInt64 n2 Hn2) (mkUInt64 N_C_1 N_C_1_range) acc_s1_3c Hacc_s1_3c.

  (* sumadd(&acc, n1) *)
  forward_call_sumadd v_acc acc_s1_3c (mkUInt64 n1 Hn1) acc_s1_3 Hacc_s1_3.

  (* extract(&acc, &m3) *)
  forward_call_extract v_acc acc_s1_3 v_m3 Tsh Tsh m3_u64 carry_s1_3 Hm3_eq Hcarry_s1_3_eq.

  assert (Hacc_s1_3_val : acc_val acc_s1_3 =
    acc_val carry_s1_2 + l3 + n3 * N_C_0 + n2 * N_C_1 + n1)
    by (rewrite Hacc_s1_3, Hacc_s1_3c, Hacc_s1_3b, Hacc_s1_3a; simpl; lia).

  assert (Hcarry_s1_3_ub : acc_val carry_s1_3 <= N_C_0 + N_C_1 + 1).
  { rewrite Hcarry_s1_3_eq, Hacc_s1_3_val.
    apply (Z.le_trans _ (((N_C_0 + N_C_1 + 1) + (2^64 - 1)
      + (2^64 - 1) * N_C_0 + (2^64 - 1) * N_C_1 + (2^64 - 1)) / 2^64)).
    - apply Z.div_le_mono; try lia.
      pose proof (Hprod_NC0 n3 Hn3).
      pose proof (Hprod_NC1 n2 Hn2).
      lia.
    - unfold N_C_0, N_C_1.
      reflexivity. }

  clear acc_s1_3a Hacc_s1_3a acc_s1_3b Hacc_s1_3b acc_s1_3c Hacc_s1_3c Hacc_s1_3.

  (* ===== Round 4: muladd(n3,NC1); sumadd(n2); extract -> m4 ===== *)

  (* muladd(&acc, n3, N_C_1) *)
  forward_call_muladd v_acc carry_s1_3
                (mkUInt64 n3 Hn3) (mkUInt64 N_C_1 N_C_1_range) acc_s1_4a Hacc_s1_4a.

  (* sumadd(&acc, n2) *)
  forward_call_sumadd v_acc acc_s1_4a (mkUInt64 n2 Hn2) acc_s1_4 Hacc_s1_4.

  (* extract(&acc, &m4) *)
  forward_call_extract v_acc acc_s1_4 v_m4 Tsh Tsh m4_u64 carry_s1_4 Hm4_eq Hcarry_s1_4_eq.

  assert (Hacc_s1_4_val : acc_val acc_s1_4 = acc_val carry_s1_3 + n3 * N_C_1 + n2)
    by (rewrite Hacc_s1_4, Hacc_s1_4a; simpl; lia).

  assert (Hcarry_s1_4_ub : acc_val carry_s1_4 <= N_C_1 + 1).
  { rewrite Hcarry_s1_4_eq, Hacc_s1_4_val.
    apply (Z.le_trans _ (((N_C_0 + N_C_1 + 1) + (2^64 - 1) * N_C_1 + (2^64 - 1)) / 2^64)).
    - apply Z.div_le_mono; try lia.
      pose proof (Hprod_NC1 n3 Hn3).
      lia.
    - unfold N_C_0, N_C_1.
      reflexivity. }

  clear acc_s1_4a Hacc_s1_4a Hacc_s1_4.

  (* ===== Round 5: sumadd_fast(n3); extract_fast -> m5 ===== *)

  (* sumadd_fast(&acc, n3) *)
  forward_call_sumadd_fast v_acc carry_s1_4 (mkUInt64 n3 Hn3) acc_s1_5 Hacc_s1_5.

  (* extract_fast(&acc, &m5) *)
  forward_call_extract_fast v_acc acc_s1_5 v_m5 Tsh Tsh m5_u64 carry_s1_5 Hm5_eq Hcarry_s1_5_eq.

  assert (Hacc_s1_5_val : acc_val acc_s1_5 = acc_val carry_s1_4 + n3)
    by (rewrite Hacc_s1_5; simpl; lia).

  assert (Hcarry_s1_5_ub : acc_val carry_s1_5 <= 1).
  { rewrite Hcarry_s1_5_eq, Hacc_s1_5_val.
    apply (Z.le_trans _ (((N_C_1 + 1) + (2^64 - 1)) / 2^64)).
    - apply Z.div_le_mono; [lia|].
      pose proof (u64_range (mkUInt64 n3 Hn3)).
      lia.
    - unfold N_C_1.
      reflexivity. }

  clear Hacc_s1_5.

  (* m6 = (uint32_t)acc.c0 *)
  forward. (* _t'22 = acc.c0 *)
  forward. (* m6 = (uint32_t)_t'22 *)

  (* Stage 1 congruence: carry forward through the clear *)
  assert (Hstage1_mod :
    (u64_val m0_u64 + u64_val m1_u64 * 2^64 + u64_val m2_u64 * 2^128
     + u64_val m3_u64 * 2^192 + u64_val m4_u64 * 2^256
     + u64_val m5_u64 * 2^320 + acc_val carry_s1_5 * 2^384)
    mod secp256k1_N = u512_val l mod secp256k1_N).
  {
    (* Round identities: m_i + carry_i * 2^64 = acc_i, unfolded *)
    pose proof (round_identity acc_s1_0 m0_u64 carry_s1_0 Hm0_eq Hcarry_s1_0_eq) as HR0.
    rewrite Hacc_s1_0v in HR0.
    pose proof (round_identity acc_s1_1 m1_u64 carry_s1_1 Hm1_eq Hcarry_s1_1_eq) as HR1.
    rewrite Hacc_s1_1_val in HR1.
    pose proof (round_identity acc_s1_2 m2_u64 carry_s1_2 Hm2_eq Hcarry_s1_2_eq) as HR2.
    rewrite Hacc_s1_2_val in HR2.
    pose proof (round_identity acc_s1_3 m3_u64 carry_s1_3 Hm3_eq Hcarry_s1_3_eq) as HR3.
    rewrite Hacc_s1_3_val in HR3.
    pose proof (round_identity acc_s1_4 m4_u64 carry_s1_4 Hm4_eq Hcarry_s1_4_eq) as HR4.
    rewrite Hacc_s1_4_val in HR4.
    pose proof (round_identity acc_s1_5 m5_u64 carry_s1_5 Hm5_eq Hcarry_s1_5_eq) as HR5.
    rewrite Hacc_s1_5_val in HR5.

    (* Carry chain telescopes to lo + hi * N_C *)
    assert (Htotal : u64_val m0_u64 + u64_val m1_u64 * 2^64 + u64_val m2_u64 * 2^128
      + u64_val m3_u64 * 2^192 + u64_val m4_u64 * 2^256
      + u64_val m5_u64 * 2^320 + acc_val carry_s1_5 * 2^384
      = (l0 + l1 * 2^64 + l2 * 2^128 + l3 * 2^192)
        + (n0 + n1 * 2^64 + n2 * 2^128 + n3 * 2^192)
          * (N_C_0 + N_C_1 * 2^64 + N_C_2 * 2^128)).
    { unfold N_C_2.
      nia. }

    rewrite Htotal.
    rewrite <- secp256k1_N_C_limbs, fold_sub_mod.
    (* Goal: (lo + hi * 2^256) mod N = u512_val l mod N *)
    f_equal.

    (* 8-limb decomposition of u512_val l *)
    pose proof (eval8_limbs (2^64) (u512_val l) ltac:(lia)
      ltac:(change ((2^64)^8) with (2^512); exact (u512_range l))) as He8.
    rewrite <- !limb64_is_limb in He8.
    fold l0 l1 l2 l3 n0 n1 n2 n3 in He8.
    unfold eval8 in He8.
    cbv beta in He8.
    change ((2^64)^2) with (2^128) in He8.
    change ((2^64)^3) with (2^192) in He8.
    change ((2^64)^4) with (2^256) in He8.
    change ((2^64)^5) with (2^320) in He8.
    change ((2^64)^6) with (2^384) in He8.
    change ((2^64)^7) with (2^448) in He8.
    nia.
  }

  (* --- Clear Stage 1 intermediates, keep only outputs --- *)
  clear - Hsh_r_writable Hsh_l_readable Hfc
          l0 l1 l2 l3 n0 n1 n2 n3
          Hl0 Hl1 Hl2 Hl3 Hn0 Hn1 Hn2 Hn3
          HNC0 HNC1 HNC0_nn HNC1_nn
          Hprod_NC0 Hprod_NC1 HNC0_prod_bound HNC1_prod_bound
          Inh_Scalar
          m0_u64 m1_u64 m2_u64 m3_u64 m4_u64 m5_u64
          Hm0_eq Hm1_eq Hm2_eq Hm3_eq Hm4_eq Hm5_eq
          carry_s1_5 Hcarry_s1_5_ub
          Hstage1_mod.

  (* ===== Stage 2: Reduce 385 -> 258 bits ===== *)
  (* p[0..4] = m[0..3] + m[4..6] * SECP256K1_N_C *)

  (* acc__1 = { m0, 0, 0 } *)
  forward. (* _t'21 = m0 *)
  forward. (* acc__1.c0 = _t'21 *)
  forward. (* acc__1.c1 = 0 *)
  forward. (* acc__1.c2 = 0 *)
  autorewrite with norm.

  (* Fold acc__1 into acc_to_val form *)
  set (m0v := u64_val m0_u64).
  assert (Hm0v : 0 <= m0v < 2^64) by (subst m0v; exact (u64_range m0_u64)).
  assert (Hacc_s2_init_range : 0 <= m0v < 2^192) by lia.
  set (acc_s2_init := mkAcc m0v Hacc_s2_init_range).
  change (uint64_to_val m0_u64) with (Vlong (Int64.repr m0v)).
  assert (Hacc_s2_eq : data_at Tsh (Tstruct __215 noattr)
      (Vlong (Int64.repr m0v), (Vlong (Int64.repr 0), Vlong (Int64.repr 0))) v_acc__1
    = data_at Tsh (Tstruct __215 noattr) (acc_to_val acc_s2_init) v_acc__1)
    by (f_equal; exact (acc_init_eq m0v Hacc_s2_init_range Hm0v)).
  sep_apply (derives_refl' _ _ Hacc_s2_eq).
  clear Hacc_s2_eq.

  (* ===== Round 0: muladd_fast(m4, N_C_0); extract_fast -> p0 ===== *)

  (* _t'20 = m4 *)
  forward.

  (* muladd_fast(&acc__1, m4, N_C_0) *)
  forward_call_muladd_fast v_acc__1 acc_s2_init m4_u64
                (mkUInt64 N_C_0 N_C_0_range) acc_s2_0 Hacc_s2_0.
  { (* acc_val acc_s2_init + u64_val m4 * N_C_0 < 2^128 *)
    unfold acc_s2_init.
    simpl acc_val.
    simpl u64_val.
    pose proof (u64_range m4_u64).
    pose proof (Hprod_NC0 (u64_val m4_u64) ltac:(lia)).
    lia. }

  (* extract_fast(&acc__1, &p0) *)
  forward_call_extract_fast v_acc__1 acc_s2_0 v_p0 Tsh Tsh p0_u64 carry_s2_0 Hp0_eq Hcarry_s2_0_eq.
  { (* m0v + m4*NC0 < 2^128 *)
    rewrite Hacc_s2_0.
    unfold acc_s2_init.
    simpl acc_val.
    simpl u64_val.
    pose proof (u64_range m4_u64).
    pose proof (Hprod_NC0 (u64_val m4_u64) ltac:(lia)).
    lia. }

  assert (Hacc_s2_0_val : acc_val acc_s2_0 = m0v + u64_val m4_u64 * N_C_0)
    by (rewrite Hacc_s2_0; unfold acc_s2_init; simpl; lia).

  assert (Hcarry_s2_0_ub : acc_val carry_s2_0 <= N_C_0).
  { rewrite Hcarry_s2_0_eq, Hacc_s2_0_val.
    apply (Z.le_trans _ (((2^64 - 1) + (2^64 - 1) * N_C_0) / 2^64)).
    - apply Z.div_le_mono; [lia|].
      pose proof (u64_range m4_u64).
      assert (u64_val m4_u64 * N_C_0 <= (2^64-1) * N_C_0)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      lia.
    - unfold N_C_0.
      reflexivity. }

  clear acc_s2_init Hacc_s2_init_range Hacc_s2_0.

  (* ===== Round 1: sumadd_fast(m1); muladd(m5,NC0); muladd(m4,NC1); extract -> p1 ===== *)

  (* _t'19 = m1 *)
  forward.

  (* sumadd_fast(&acc__1, m1) *)
  forward_call_sumadd_fast v_acc__1 carry_s2_0 m1_u64 acc_s2_1a Hacc_s2_1a.
  { (* carry_s2_0 + m1 < 2^128 *)
    simpl u64_val.
    pose proof (u64_range m1_u64).
    lia. }

  (* _t'18 = m5 *)
  forward.

  (* muladd(&acc__1, m5, N_C_0) *)
  forward_call_muladd v_acc__1 acc_s2_1a m5_u64
                (mkUInt64 N_C_0 N_C_0_range) acc_s2_1b Hacc_s2_1b.
  { (* carry_s2_0 + m1 + m5*NC0 < 2^192 *)
    rewrite Hacc_s2_1a.
    simpl u64_val.
    pose proof (u64_range m1_u64).
    pose proof (u64_range m5_u64).
    pose proof (Hprod_NC0 (u64_val m5_u64) ltac:(lia)).
    lia. }

  (* _t'17 = m4 *)
  forward.

  (* muladd(&acc__1, m4, N_C_1) *)
  forward_call_muladd v_acc__1 acc_s2_1b m4_u64
                (mkUInt64 N_C_1 N_C_1_range) acc_s2_1 Hacc_s2_1.
  { (* carry_s2_0 + m1 + m5*NC0 + m4*NC1 < 2^192 *)
    rewrite Hacc_s2_1b, Hacc_s2_1a.
    simpl u64_val.
    pose proof (u64_range m1_u64).
    pose proof (u64_range m5_u64).
    pose proof (u64_range m4_u64).
    pose proof (Hprod_NC0 (u64_val m5_u64) ltac:(lia)).
    pose proof (Hprod_NC1 (u64_val m4_u64) ltac:(lia)).
    lia. }

  (* extract(&acc__1, &p1) *)
  forward_call_extract v_acc__1 acc_s2_1 v_p1 Tsh Tsh p1_u64 carry_s2_1 Hp1_eq Hcarry_s2_1_eq.

  assert (Hacc_s2_1_val : acc_val acc_s2_1 =
    acc_val carry_s2_0 + u64_val m1_u64 + u64_val m5_u64 * N_C_0 + u64_val m4_u64 * N_C_1)
    by (rewrite Hacc_s2_1, Hacc_s2_1b, Hacc_s2_1a; simpl; lia).

  assert (Hcarry_s2_1_ub : acc_val carry_s2_1 <= N_C_0 + N_C_1).
  { rewrite Hcarry_s2_1_eq, Hacc_s2_1_val.
    apply (Z.le_trans _ ((N_C_0 + (2^64 - 1) + (2^64 - 1) * N_C_0 + (2^64 - 1) * N_C_1) / 2^64)).
    - apply Z.div_le_mono; [lia|].
      pose proof (u64_range m1_u64).
      pose proof (u64_range m5_u64).
      pose proof (u64_range m4_u64).
      assert (u64_val m5_u64 * N_C_0 <= (2^64-1) * N_C_0) by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (u64_val m4_u64 * N_C_1 <= (2^64-1) * N_C_1) by (apply Z.mul_le_mono_nonneg_r; lia).
      lia.
    - unfold N_C_0, N_C_1.
      reflexivity. }

  clear acc_s2_1a Hacc_s2_1a acc_s2_1b Hacc_s2_1b Hacc_s2_1.

  (* ===== Round 2: sumadd(m2); muladd(m6,NC0); muladd(m5,NC1); sumadd(m4); extract -> p2 ===== *)

  (* _t'16 = m2 *)
  forward.

  (* sumadd(&acc__1, m2) *)
  forward_call_sumadd v_acc__1 carry_s2_1 m2_u64 acc_s2_2a Hacc_s2_2a.
  { (* carry_s2_1 + m2 < 2^192 *)
    pose proof (acc_range carry_s2_1).
    simpl u64_val.
    pose proof (u64_range m2_u64).
    lia. }

  (* muladd(&acc__1, m6, N_C_0) -- m6 is uint32_t, widened to uint64 *)
  set (m6_val := limb64 (acc_val carry_s1_5) 0).
  assert (Hm6_range : 0 <= m6_val <= Int.max_unsigned).
  { unfold m6_val.
    norm_limb64_0.
    rewrite Zmod_small by (pose proof (acc_range carry_s1_5); lia).
    pose proof (acc_range carry_s1_5).
    rep_lia. }
  assert (Hm6_u64_range : 0 <= m6_val < 2^64) by rep_lia.
  set (m6_u64 := mkUInt64 m6_val Hm6_u64_range).

  (* m6 * N_C_j product bounds -- used repeatedly in Stage 2 overflow checks *)
  assert (Hm6_NC0 : m6_val * N_C_0 < 2^127)
    by (apply (Z.le_lt_trans _ ((2^64-1)*N_C_0));
        [apply Z.mul_le_mono_nonneg_r; lia | exact HNC0_prod_bound]).
  assert (Hm6_NC1 : m6_val * N_C_1 < 2^127)
    by (apply (Z.le_lt_trans _ ((2^64-1)*N_C_1));
        [apply Z.mul_le_mono_nonneg_r; lia | exact HNC1_prod_bound]).

  (* muladd(&acc__1, m6, N_C_0) -- m6 is uint32_t, auto-widened *)
  forward_call_muladd v_acc__1 acc_s2_2a m6_u64
                (mkUInt64 N_C_0 N_C_0_range) acc_s2_2b Hacc_s2_2b.
  { entailer!.
    simpl firstn.
    do 2 f_equal.
    subst m6_val.
    rewrite Int.unsigned_repr by lia.
    subst m6_u64.
    reflexivity. }
  { (* carry_s2_1 + m2 + m6*NC0 < 2^192 *)
    rewrite Hacc_s2_2a.
    unfold m6_u64.
    simpl u64_val.
    pose proof (u64_range m2_u64).
    pose proof Hm6_NC0.
    lia. }

  (* _t'15 = m5 *)
  forward.

  (* muladd(&acc__1, m5, N_C_1) *)
  forward_call_muladd v_acc__1 acc_s2_2b m5_u64
                (mkUInt64 N_C_1 N_C_1_range) acc_s2_2c Hacc_s2_2c.
  { (* carry_s2_1 + m2 + m6*NC0 + m5*NC1 < 2^192 *)
    rewrite Hacc_s2_2b, Hacc_s2_2a.
    unfold m6_u64.
    simpl u64_val.
    pose proof (u64_range m2_u64).
    pose proof (u64_range m5_u64).
    pose proof Hm6_NC0.
    pose proof (Hprod_NC1 (u64_val m5_u64) ltac:(lia)).
    lia. }

  (* _t'14 = m4 *)
  forward.

  (* sumadd(&acc__1, m4) *)
  forward_call_sumadd v_acc__1 acc_s2_2c m4_u64 acc_s2_2 Hacc_s2_2.
  { (* carry_s2_1 + m2 + m6*NC0 + m5*NC1 + m4 < 2^192 *)
    rewrite Hacc_s2_2c, Hacc_s2_2b, Hacc_s2_2a.
    unfold m6_u64.
    simpl u64_val.
    pose proof (u64_range m2_u64).
    pose proof (u64_range m5_u64).
    pose proof (u64_range m4_u64).
    pose proof Hm6_NC0.
    pose proof (Hprod_NC1 (u64_val m5_u64) ltac:(lia)).
    lia. }

  (* extract(&acc__1, &p2) *)
  forward_call_extract v_acc__1 acc_s2_2 v_p2 Tsh Tsh p2_u64 carry_s2_2 Hp2_eq Hcarry_s2_2_eq.

  assert (Hacc_s2_2_val : acc_val acc_s2_2 =
    acc_val carry_s2_1 + u64_val m2_u64 + m6_val * N_C_0 + u64_val m5_u64 * N_C_1 + u64_val m4_u64)
    by (rewrite Hacc_s2_2, Hacc_s2_2c, Hacc_s2_2b, Hacc_s2_2a; unfold m6_u64; simpl; lia).

  assert (Hcarry_s2_2_ub : acc_val carry_s2_2 <= N_C_0 + N_C_1 + 1).
  { rewrite Hcarry_s2_2_eq, Hacc_s2_2_val.
    apply (Z.le_trans _ (((N_C_0 + N_C_1) + (2^64 - 1)
      + (2^64 - 1) * N_C_0 + (2^64 - 1) * N_C_1 + (2^64 - 1)) / 2^64)).
    - apply Z.div_le_mono; [lia|].
      pose proof (u64_range m2_u64).
      pose proof (u64_range m5_u64).
      pose proof (u64_range m4_u64).
      assert (m6_val * N_C_0 <= (2^64-1) * N_C_0)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (u64_val m5_u64 * N_C_1 <= (2^64-1) * N_C_1)
        by (apply Z.mul_le_mono_nonneg_r; lia).
      lia.
    - unfold N_C_0, N_C_1.
      reflexivity. }

  clear acc_s2_2a Hacc_s2_2a acc_s2_2b Hacc_s2_2b acc_s2_2c Hacc_s2_2c Hacc_s2_2.

  (* ===== Round 3: sumadd_fast(m3); muladd_fast(m6,NC1); sumadd_fast(m5); extract_fast -> p3 ===== *)

  (* _t'13 = m3 *)
  forward.

  (* sumadd_fast(&acc__1, m3) *)
  forward_call_sumadd_fast v_acc__1 carry_s2_2 m3_u64 acc_s2_3a Hacc_s2_3a.
  { (* carry_s2_2 + m3 < 2^128 *)
    simpl u64_val.
    pose proof (u64_range m3_u64).
    lia. }

  (* muladd_fast(&acc__1, m6, N_C_1) -- m6 is uint32, auto-widened *)
  forward_call_muladd_fast v_acc__1 acc_s2_3a m6_u64
                (mkUInt64 N_C_1 N_C_1_range) acc_s2_3b Hacc_s2_3b.
  { entailer!.
    simpl firstn.
    do 2 f_equal.
    rewrite Int.unsigned_repr by lia.
    subst m6_u64.
    reflexivity. }
  { (* carry_s2_2 + m3 + m6*NC1 < 2^128 *)
    rewrite Hacc_s2_3a.
    unfold m6_u64.
    simpl u64_val.
    pose proof (u64_range m3_u64).
    pose proof Hm6_NC1.
    lia. }

  (* _t'12 = m5 *)
  forward.

  (* sumadd_fast(&acc__1, m5) *)
  forward_call_sumadd_fast v_acc__1 acc_s2_3b m5_u64 acc_s2_3 Hacc_s2_3.
  { (* carry_s2_2 + m3 + m6*NC1 + m5 < 2^128 *)
    rewrite Hacc_s2_3b, Hacc_s2_3a.
    unfold m6_u64.
    simpl u64_val.
    pose proof (u64_range m3_u64).
    pose proof (u64_range m5_u64).
    pose proof Hm6_NC1.
    lia. }

  (* extract_fast(&acc__1, &p3) *)
  forward_call_extract_fast v_acc__1 acc_s2_3 v_p3 Tsh Tsh p3_u64 carry_s2_3 Hp3_eq Hcarry_s2_3_eq.
  { (* carry_s2_2 + m3 + m6*NC1 + m5 < 2^128 *)
    rewrite Hacc_s2_3, Hacc_s2_3b, Hacc_s2_3a.
    unfold m6_u64.
    simpl u64_val.
    pose proof (u64_range m3_u64).
    pose proof (u64_range m5_u64).
    pose proof Hm6_NC1.
    lia. }

  assert (Hacc_s2_3_val : acc_val acc_s2_3 =
    acc_val carry_s2_2 + u64_val m3_u64 + m6_val * N_C_1 + u64_val m5_u64)
    by (rewrite Hacc_s2_3, Hacc_s2_3b, Hacc_s2_3a; unfold m6_u64; simpl; lia).

  assert (Hm6_le1 : m6_val <= 1).
  { unfold m6_val.
    norm_limb64_0.
    pose proof (acc_range carry_s1_5).
    rewrite Zmod_small by lia.
    exact Hcarry_s1_5_ub. }

  assert (Hcarry_s2_3_ub : acc_val carry_s2_3 <= 2).
  { rewrite Hcarry_s2_3_eq, Hacc_s2_3_val.
    pose proof (u64_range m3_u64).
    pose proof (u64_range m5_u64).
    assert (m6_val * N_C_1 <= N_C_1) by nia.
    apply Z.lt_succ_r.
    apply Z.div_lt_upper_bound; [lia|].
    unfold N_C_0, N_C_1 in *.
    lia. }

  clear acc_s2_3a Hacc_s2_3a acc_s2_3b Hacc_s2_3b Hacc_s2_3.

  (* p4 = (uint32_t)(acc__1.c0 + m6) *)
  forward. (* _t'11 = acc__1.c0 *)
  forward. (* p4 = (uint32_t)(_t'11 + _m6) *)

  (* Name p4 value and create UInt64 for it *)
  set (p4_val := (limb64 (acc_val carry_s2_3) 0) + m6_val).
  assert (Hp4_range : 0 <= p4_val < 2^64).
  { unfold p4_val.
    norm_limb64_0.
    pose proof (acc_range carry_s2_3).
    rewrite Zmod_small by lia.
    lia. }

  set (p4_u64 := mkUInt64 p4_val Hp4_range).

  (* p4 fits in uint32 -- needed for the C cast (uint32_t)(acc.c0 + m6) *)
  assert (Hp4_u32 : p4_val <= Int.max_unsigned).
  { unfold p4_val.
    norm_limb64_0.
    pose proof (acc_range carry_s2_3).
    pose proof (acc_range carry_s1_5).
    rewrite !Zmod_small by lia.
    rep_lia. }

  (* Stage 2 congruence: carry forward through the clear *)
  assert (Hstage2_mod :
    (u64_val p0_u64 + u64_val p1_u64 * 2^64 + u64_val p2_u64 * 2^128
     + u64_val p3_u64 * 2^192 + p4_val * 2^256)
    mod secp256k1_N = u512_val l mod secp256k1_N).
  {
    (* Round identities, unfolded *)
    pose proof (round_identity acc_s2_0 p0_u64 carry_s2_0 Hp0_eq Hcarry_s2_0_eq) as HR0.
    rewrite Hacc_s2_0_val in HR0.
    pose proof (round_identity acc_s2_1 p1_u64 carry_s2_1 Hp1_eq Hcarry_s2_1_eq) as HR1.
    rewrite Hacc_s2_1_val in HR1.
    pose proof (round_identity acc_s2_2 p2_u64 carry_s2_2 Hp2_eq Hcarry_s2_2_eq) as HR2.
    rewrite Hacc_s2_2_val in HR2.
    pose proof (round_identity acc_s2_3 p3_u64 carry_s2_3 Hp3_eq Hcarry_s2_3_eq) as HR3.
    rewrite Hacc_s2_3_val in HR3.

    (* m6_val = acc_val carry_s1_5 *)
    assert (Hm6 : m6_val = acc_val carry_s1_5).
    { unfold m6_val.
      norm_limb64_0.
      rewrite Zmod_small by (pose proof (acc_range carry_s1_5); lia).
      reflexivity. }

    (* limb64(carry_s2_3, 0) = acc_val carry_s2_3 (small enough) *)
    assert (Hcarry_s2_3_lo : limb64 (acc_val carry_s2_3) 0 = acc_val carry_s2_3).
    { norm_limb64_0.
      rewrite Zmod_small by (pose proof (acc_range carry_s2_3); lia).
      reflexivity. }

    (* Carry chain telescopes to m_lo + m_hi * N_C *)
    assert (Htotal :
      u64_val p0_u64 + u64_val p1_u64 * 2^64 + u64_val p2_u64 * 2^128
      + u64_val p3_u64 * 2^192 + p4_val * 2^256
      = (m0v + u64_val m1_u64 * 2^64 + u64_val m2_u64 * 2^128 + u64_val m3_u64 * 2^192)
        + (u64_val m4_u64 + u64_val m5_u64 * 2^64 + m6_val * 2^128)
          * (N_C_0 + N_C_1 * 2^64 + N_C_2 * 2^128)).
    { unfold p4_val.
      rewrite Hcarry_s2_3_lo.
      unfold N_C_2.
      unfold m6_u64 in *.
      simpl u64_val in *.
      nia. }

    rewrite Htotal, <- secp256k1_N_C_limbs, fold_sub_mod.
    replace (m0v + u64_val m1_u64 * 2^64 + u64_val m2_u64 * 2^128 + u64_val m3_u64 * 2^192
             + (u64_val m4_u64 + u64_val m5_u64 * 2^64 + m6_val * 2^128) * 2^256)
      with (u64_val m0_u64 + u64_val m1_u64 * 2^64 + u64_val m2_u64 * 2^128
            + u64_val m3_u64 * 2^192 + u64_val m4_u64 * 2^256
            + u64_val m5_u64 * 2^320 + acc_val carry_s1_5 * 2^384)
      by (unfold m0v; rewrite Hm6; nia).
    exact Hstage1_mod.
  }

  (* p4 bound needed by reduce_stage3_mod -- prove before clearing *)
  assert (Hp4_le3 : 0 <= p4_val <= 3).
  { unfold p4_val.
    norm_limb64_0.
    pose proof (acc_range carry_s2_3).
    pose proof (acc_range carry_s1_5).
    rewrite !Zmod_small by lia.
    lia. }

  (* --- Clear Stage 2 intermediates, keep only outputs --- *)
  clear - Hsh_r_writable Hsh_l_readable Hfc
          l0 l1 l2 l3 n0 n1 n2 n3
          Hl0 Hl1 Hl2 Hl3 Hn0 Hn1 Hn2 Hn3
          HNC0 HNC1 HNC0_nn HNC1_nn
          Hprod_NC0 Hprod_NC1 HNC0_prod_bound HNC1_prod_bound
          Inh_Scalar
          p0_u64 p1_u64 p2_u64 p3_u64 p4_u64 Hp4_u32 Hp4_le3
          Hp0_eq Hp1_eq Hp2_eq Hp3_eq
          carry_s1_5 Hcarry_s1_5_ub
          m6_val Hm6_range Hm6_le1
          carry_s2_3
          Hstage2_mod.

  (* ===== Stage 3: Reduce 258 -> 256 bits + final reduction ===== *)
  (* r[0..3] = p[0..3] + p4 * SECP256K1_N_C *)
  (* Then: secp256k1_scalar_reduce(r, c + check_overflow(r)) *)

  (* ===== Round 0: from_u64(p0); accum_mul(NC0, p4); to_u64 -> r[0]; rshift ===== *)

  (* _t'10 = p0 *)
  forward.

  (* secp256k1_u128_from_u64(&c128, p0) *)
  forward_call_u128_from_u64 v_c128 p0_u64 Tsh c128_0 Hc128_0.

  (* secp256k1_u128_accum_mul(&c128, N_C_0, p4) -- p4 is uint32, needs cast *)
  forward_call_u128_accum_mul v_c128 c128_0
                (mkUInt64 N_C_0 N_C_0_range) p4_u64 Tsh c128_0a Hc128_0a.
  { entailer!.
    unfold uint64_to_val, p4_u64.
    simpl u64_val.
    unfold p4_val.
    simpl firstn.
    do 5 f_equal.
    rewrite !Int64.Z_mod_modulus_eq.
    change Int64.modulus with (2^64).
    rewrite !(Zmod_small m6_val) by rep_lia.
    rewrite (Int.unsigned_repr m6_val) by lia.
    rewrite (Zmod_small (limb64 (acc_val carry_s2_3) 0 + m6_val)) by rep_lia.
    rewrite Int.unsigned_repr by lia.
    reflexivity. }
  { (* u64_val p0 + N_C_0 * p4_val < 2^128 *)
    rewrite Hc128_0.
    simpl u64_val.
    pose proof (u64_range p0_u64).
    pose proof (u64_range p4_u64).
    pose proof (Hprod_NC0 (u64_val p4_u64) ltac:(lia)).
    pose proof HNC0_prod_bound.
    simpl u64_val in *.
    nia. }

  (* r->d[0] = secp256k1_u128_to_u64(&c128) *)
  forward_call_u128_to_u64 v_c128 c128_0a Tsh lo0 Hlo0.
  forward. (* r->d[0] = lo0 *)

  (* secp256k1_u128_rshift(&c128, 64) *)
  forward_call_u128_rshift v_c128 c128_0a Tsh carry_0 Hcarry_0.

  (* Clean u128 value for final mod proof *)
  assert (Hc128_0a_val : u128_val c128_0a = u64_val p0_u64 + N_C_0 * p4_val)
    by (rewrite Hc128_0a, Hc128_0; simpl u64_val; ring).
  assert (Hcarry_0_val : u128_val carry_0 = u128_val c128_0a / 2^64)
    by exact Hcarry_0.
  clear c128_0 Hc128_0 Hc128_0a Hcarry_0.

  (* ===== Round 1: accum_u64(p1); accum_mul(NC1, p4); to_u64 -> r[1]; rshift ===== *)

  (* _t'9 = p1 *)
  forward.

  (* secp256k1_u128_accum_u64(&c128, p1) *)
  forward_call_u128_accum_u64 v_c128 carry_0 p1_u64 Tsh c128_1a Hc128_1a.
  { (* carry_0 + p1 < 2^128 *)
    rewrite Hcarry_0_val.
    pose proof (u128_range c128_0a).
    assert (u128_val c128_0a / 2 ^ 64 < 2 ^ 64)
      by (apply Z.div_lt_upper_bound; lia).
    pose proof (u64_range p1_u64).
    lia. }

  (* secp256k1_u128_accum_mul(&c128, N_C_1, p4) *)
  forward_call_u128_accum_mul v_c128 c128_1a
                (mkUInt64 N_C_1 N_C_1_range) p4_u64 Tsh c128_1 Hc128_1.
  { entailer!.
    unfold uint64_to_val, p4_u64.
    simpl u64_val.
    unfold p4_val.
    simpl firstn.
    do 5 f_equal.
    rewrite !Int64.Z_mod_modulus_eq.
    change Int64.modulus with (2^64).
    rewrite !(Zmod_small m6_val) by rep_lia.
    rewrite (Int.unsigned_repr m6_val) by lia.
    rewrite (Zmod_small (limb64 (acc_val carry_s2_3) 0 + m6_val)) by rep_lia.
    rewrite Int.unsigned_repr by lia.
    reflexivity. }
  { (* c128_1a + NC1 * p4 < 2^128 *)
    simpl u64_val.
    rewrite (Z.mul_comm N_C_1 p4_val).
    rewrite Hc128_1a, Hcarry_0_val.
    pose proof (u128_range c128_0a).
    pose proof (u64_range p1_u64).
    assert (u128_val c128_0a / 2 ^ 64 < 2 ^ 64)
      by (apply Z.div_lt_upper_bound; lia).
    pose proof (Hprod_NC1 p4_val ltac:(lia)).
    pose proof HNC1_prod_bound.
    lia. }

  (* r->d[1] = secp256k1_u128_to_u64(&c128) *)
  forward_call_u128_to_u64 v_c128 c128_1 Tsh lo1 Hlo1.
  forward. (* r->d[1] = lo1 *)

  (* secp256k1_u128_rshift(&c128, 64) *)
  forward_call_u128_rshift v_c128 c128_1 Tsh carry_1 Hcarry_1.

  assert (Hc128_1_val : u128_val c128_1 = u128_val c128_0a / 2^64 + u64_val p1_u64 + N_C_1 * p4_val)
    by (rewrite Hc128_1, Hc128_1a, Hcarry_0_val; simpl u64_val; ring).
  assert (Hcarry_1_val : u128_val carry_1 = u128_val c128_1 / 2^64)
    by exact Hcarry_1.
  clear c128_1a Hc128_1a Hc128_1 Hcarry_0_val Hcarry_1.

  (* ===== Round 2: accum_u64(p2); accum_u64(p4); to_u64 -> r[2]; rshift ===== *)

  (* _t'8 = p2 *)
  forward.

  (* secp256k1_u128_accum_u64(&c128, p2) *)
  forward_call_u128_accum_u64 v_c128 carry_1 p2_u64 Tsh c128_2a Hc128_2a.
  { (* carry_1 + p2 < 2^128 *)
    rewrite Hcarry_1_val.
    pose proof (u128_range c128_1).
    pose proof (u64_range p2_u64).
    assert (u128_val c128_1 / 2 ^ 64 < 2 ^ 64)
      by (apply Z.div_lt_upper_bound; lia).
    lia. }

  (* secp256k1_u128_accum_u64(&c128, p4) -- N_C_2 = 1, so p4*N_C_2 = p4 *)
  forward_call_u128_accum_u64 v_c128 c128_2a p4_u64 Tsh c128_2 Hc128_2.
  { entailer!.
    unfold uint64_to_val, p4_u64.
    simpl u64_val.
    unfold p4_val.
    simpl firstn.
    do 3 f_equal.
    rewrite !Int64.Z_mod_modulus_eq.
    change Int64.modulus with (2^64).
    rewrite !(Zmod_small m6_val) by rep_lia.
    rewrite (Int.unsigned_repr m6_val) by lia.
    rewrite (Zmod_small (limb64 (acc_val carry_s2_3) 0 + m6_val)) by rep_lia.
    rewrite Int.unsigned_repr by lia.
    reflexivity. }
  { (* c128_2a + p4 < 2^128 *)
    rewrite Hc128_2a, Hcarry_1_val.
    simpl u64_val.
    pose proof (u128_range c128_1).
    pose proof (u64_range p2_u64).
    assert (u128_val c128_1 / 2 ^ 64 < 2 ^ 64)
      by (apply Z.div_lt_upper_bound; lia).
    lia. }

  (* r->d[2] = secp256k1_u128_to_u64(&c128) *)
  forward_call_u128_to_u64 v_c128 c128_2 Tsh lo2 Hlo2.
  forward. (* r->d[2] = lo2 *)

  (* secp256k1_u128_rshift(&c128, 64) *)
  forward_call_u128_rshift v_c128 c128_2 Tsh carry_2 Hcarry_2.

  assert (Hc128_2_val : u128_val c128_2 = u128_val c128_1 / 2^64 + u64_val p2_u64 + p4_val)
    by (rewrite Hc128_2, Hc128_2a, Hcarry_1_val; simpl u64_val; ring).
  assert (Hcarry_2_val : u128_val carry_2 = u128_val c128_2 / 2^64)
    by exact Hcarry_2.
  clear c128_2a Hc128_2a Hc128_2 Hcarry_1_val Hcarry_2.

  (* ===== Round 3: accum_u64(p3); to_u64 -> r[3]; c = hi_u64 ===== *)

  (* _t'7 = p3 *)
  forward.

  (* secp256k1_u128_accum_u64(&c128, p3) *)
  forward_call_u128_accum_u64 v_c128 carry_2 p3_u64 Tsh c128_3 Hc128_3.
  { (* carry_2 + p3 < 2^128 *)
    rewrite Hcarry_2_val.
    pose proof (u128_range c128_2).
    pose proof (u64_range p3_u64).
    assert (u128_val c128_2 / 2 ^ 64 < 2 ^ 64)
      by (apply Z.div_lt_upper_bound; lia).
    lia. }

  (* r->d[3] = secp256k1_u128_to_u64(&c128) *)
  forward_call_u128_to_u64 v_c128 c128_3 Tsh lo3 Hlo3.
  forward. (* r->d[3] = lo3 *)

  (* _t'5 = secp256k1_u128_hi_u64(&c128); _c = _t'5 *)
  forward_call_u128_hi_u64 v_c128 c128_3 Tsh hi Hhi.

  assert (Hc128_3_val : u128_val c128_3 = u128_val c128_2 / 2^64 + u64_val p3_u64)
    by (rewrite Hc128_3, Hcarry_2_val; ring).
  clear carry_2 Hcarry_2_val Hc128_3.

  (* ===== Final reduction: secp256k1_scalar_reduce(r, c + check_overflow(r)) ===== *)

  (* Create a UInt256 for the assembled r value *)
  set (r_z := u64_val lo0 + u64_val lo1 * 2^64 + u64_val lo2 * 2^128 + u64_val lo3 * 2^192).
  assert (Hr_z_range : 0 <= r_z < 2^256). {
    pose proof (u64_range lo0).
    pose proof (u64_range lo1).
    pose proof (u64_range lo2).
    pose proof (u64_range lo3).
    subst r_z.
    change (2^128) with ((2^64)^2).
    change (2^192) with ((2^64)^3).
    change (2^256) with ((2^64)^4).
    nia.
  }
  set (r_u256 := mkUInt256 r_z Hr_z_range).

  (* Replace upd_Znth chain with uint256_to_val *)
  assert (Hr_eq : data_at sh_r t_secp256k1_uint256
    (upd_Znth 3 (upd_Znth 2 (upd_Znth 1
      (upd_Znth 0 (default_val t_secp256k1_uint256) (uint64_to_val lo0))
      (uint64_to_val lo1)) (uint64_to_val lo2)) (uint64_to_val lo3)) r_ptr
    = data_at sh_r t_secp256k1_uint256 (uint256_to_val r_u256) r_ptr).
  { do 2 f_equal.
    transitivity [uint64_to_val lo0; uint64_to_val lo1;
                  uint64_to_val lo2; uint64_to_val lo3].
    - unfold default_val.
      simpl.
      reflexivity.
    - exact (uint256_from_limbs lo0 lo1 lo2 lo3 Hr_z_range). }
  sep_apply (derives_refl' _ _ Hr_eq).
  clear Hr_eq.

  (* _t'6 = secp256k1_scalar_check_overflow(r) *)
  forward_call_scalar_check_overflow r_ptr r_u256 sh_r.

  (* secp256k1_scalar_reduce(r, (uint)(c + _t'6)) *)
  set (ov := u64_val hi + (if Z_lt_dec (u256_val r_u256) secp256k1_N then 0 else 1)).

  (* Core modular arithmetic -- needed for precondition and postcondition.
     Chain: reduce_carry_chain gives Stage 3 carry identity,
            cond_sub_mod handles the conditional subtraction,
            fold_sub_mod + Hstage2_mod connect back to u512_val l. *)
  assert (Hmod_eq :
    (r_z + ov * (2^256 - secp256k1_N)) mod 2^256 = u512_val l mod secp256k1_N).
  {
    (* lo_i = c_i mod 2^64, hi = c3 / 2^64 *)
    assert (Hlo0_eq : u64_val lo0 = u128_val c128_0a mod 2^64)
      by (rewrite Hlo0, u128_lo_val; reflexivity).
    assert (Hlo1_eq : u64_val lo1 = u128_val c128_1 mod 2^64)
      by (rewrite Hlo1, u128_lo_val; reflexivity).
    assert (Hlo2_eq : u64_val lo2 = u128_val c128_2 mod 2^64)
      by (rewrite Hlo2, u128_lo_val; reflexivity).
    assert (Hlo3_eq : u64_val lo3 = u128_val c128_3 mod 2^64)
      by (rewrite Hlo3, u128_lo_val; reflexivity).
    assert (Hhi_eq : u64_val hi = u128_val c128_3 / 2^64)
      by (rewrite Hhi, u128_hi_val; reflexivity).

    (* Fully inline: rewrite each c128_i in terms of predecessors *)
    rewrite Hc128_0a_val in Hc128_1_val.
    rewrite Hc128_1_val in Hc128_2_val.
    rewrite Hc128_2_val in Hc128_3_val.

    (* Rewrite goal to pure Z expressions matching reduce_stage3_mod *)
    unfold ov, r_u256.
    simpl u256_val.
    unfold r_z.
    rewrite Hlo0_eq, Hlo1_eq, Hlo2_eq, Hlo3_eq, Hhi_eq.
    rewrite Hc128_0a_val, Hc128_1_val, Hc128_2_val, Hc128_3_val.

    (* val + p4*N_C < 2*B^4: val < B^4 by eval4_bound, p4*N_C < B^4 *)
    pose proof (eval4_bound (2^64)
      (u64_val p0_u64) (u64_val p1_u64) (u64_val p2_u64) (u64_val p3_u64)
      ltac:(lia) (u64_range p0_u64) (u64_range p1_u64) (u64_range p2_u64) (u64_range p3_u64))
      as Hval_bnd.

    assert (Hstage3_bound :
      0 <= u64_val p0_u64 + u64_val p1_u64 * 2^64
          + u64_val p2_u64 * (2^64 * 2^64) + u64_val p3_u64 * (2^64 * 2^64 * 2^64)
          + p4_val * (N_C_0 + N_C_1 * 2^64 + N_C_2 * (2^64 * 2^64))
        < 2 * (2^64 * 2^64 * 2^64 * 2^64)).
    { assert (p4_val * (N_C_0 + N_C_1 * 2^64 + N_C_2 * (2^64 * 2^64))
              <= 3 * (N_C_0 + N_C_1 * 2^64 + N_C_2 * (2^64 * 2^64)))
        by (apply Z.mul_le_mono_nonneg_r; rep_lia).
      assert (0 <= p4_val * (N_C_0 + N_C_1 * 2^64 + N_C_2 * (2^64 * 2^64)))
        by (apply Z.mul_nonneg_nonneg; rep_lia).
      unfold N_C_0, N_C_1, N_C_2 in *.
      lia. }

    pose proof (reduce_carry_chain (2^64)
      (u64_val p0_u64) (u64_val p1_u64) (u64_val p2_u64) (u64_val p3_u64)
      N_C_0 N_C_1 N_C_2 p4_val
      ltac:(lia) (u64_range p0_u64) (u64_range p1_u64) (u64_range p2_u64) (u64_range p3_u64)
      ltac:(rep_lia) ltac:(rep_lia) ltac:(rep_lia)
      ltac:(lia)
      Hstage3_bound) as Hchain_raw.
    clear Hstage3_bound.

    (* Normalize B*B products to 2^k and fix mul order *)
    cbv zeta in Hchain_raw.
    unfold N_C_2 in Hchain_raw.
    change (2^64 * 2^64 * 2^64 * 2^64) with (2^256) in Hchain_raw.
    change (2^64 * 2^64 * 2^64) with (2^192) in Hchain_raw.
    change (2^64 * 2^64) with (2^128) in Hchain_raw.
    rewrite (Z.mul_comm p4_val N_C_0), (Z.mul_comm p4_val N_C_1) in Hchain_raw.
    replace (p4_val * 1) with p4_val in Hchain_raw by ring.
    destruct Hchain_raw as (Hchain & Hr_z_bnd & Hhi_bnd).
    change (2^128 * 2^64) with (2^192) in *.
    change (2^128 * 2^64 * 2^64) with (2^256) in *.
    change (2^192 * 2^64) with (2^256) in *.

    (* cond_sub_mod: val mod N = val - ov * N *)
    pose proof (cond_sub_mod (2^256) _ _ _ secp256k1_N
      ltac:(unfold secp256k1_N; lia)
      ltac:(unfold secp256k1_N; lia)
      Hr_z_bnd Hhi_bnd (eq_sym Hchain)
      ltac:(intro; unfold secp256k1_N, N_C_0, N_C_1 in *; lia)) as Hcond.

    (* fold_sub_mod: val mod N = u512_val l mod N *)
    assert (Hmod_val :
      (u64_val p0_u64 + u64_val p1_u64 * 2 ^ 64
       + u64_val p2_u64 * 2 ^ 128 + u64_val p3_u64 * 2 ^ 192
       + p4_val * (N_C_0 + N_C_1 * 2 ^ 64 + 1 * 2 ^ 128))
      mod secp256k1_N = u512_val l mod secp256k1_N).
    { replace (N_C_0 + N_C_1 * 2^64 + 1 * 2^128)
        with (2^256 - secp256k1_N)
        by (unfold secp256k1_N, N_C_0, N_C_1; lia).
      rewrite fold_sub_mod.
      exact Hstage2_mod. }

    (* Derive: (r_z + ov*C) mod 2^256 = u512_val l mod N *)
    assert (Hmod_algebra : forall r h o N0 A : Z,
      0 <= (r + h * A) - o * N0 < A ->
      (r + o * (A - N0)) mod A = (r + h * A) - o * N0).
    { intros r0 h o N0 A ?.
      replace (r0 + o * (A - N0)) with ((r0 + h * A - o * N0) + (o - h) * A)
        by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. assumption. }
    rewrite <- Hmod_val, Hcond, <- Hchain.
    apply Hmod_algebra.
    rewrite Hchain, <- Hcond.
    split.
    + apply Z.mod_pos_bound. unfold secp256k1_N; lia.
    + eapply Z.lt_trans.
      * apply Z.mod_pos_bound. unfold secp256k1_N; lia.
      * unfold secp256k1_N; lia.
  }

  forward_call_scalar_reduce r_ptr r_u256 ov sh_r r_final Hr_final.
  { entailer!.
    simpl firstn.
    do 3 f_equal.
    rewrite Int64.Z_mod_modulus_eq, Int_repr_mod_Int64.
    unfold ov, u128_hi.
    simpl u64_val.
    unfold r_u256.
    simpl u256_val.
    do 2 f_equal.
    destruct (Z_lt_dec r_z secp256k1_N);
    rewrite Int.signed_repr by rep_lia; reflexivity. }
  { (* 0 <= ov <= 2 *)
    change Int.max_unsigned with 4294967295 in Hp4_u32.
    assert (HNC0p4 : N_C_0 * p4_val <= N_C_0 * 4294967295)
      by (apply Z.mul_le_mono_nonneg_l; [rep_lia | lia]).
    assert (HNC1p4 : N_C_1 * p4_val <= N_C_1 * 4294967295)
      by (apply Z.mul_le_mono_nonneg_l; [rep_lia | lia]).
    assert (Hc0 : u128_val c128_0a / 2^64 <= 2147483648).
    { rewrite Hc128_0a_val.
      pose proof (u64_range p0_u64).
      apply Z.div_le_upper_bound; [lia|].
      unfold N_C_0 in *.
      lia. }
    assert (Hc1 : u128_val c128_1 / 2^64 <= 4294967295).
    { rewrite Hc128_1_val.
      pose proof (u64_range p1_u64).
      apply Z.div_le_upper_bound; [lia|].
      unfold N_C_0, N_C_1 in *.
      lia. }
    assert (Hc2 : u128_val c128_2 / 2^64 <= 1).
    { rewrite Hc128_2_val.
      pose proof (u64_range p2_u64).
      apply Z.lt_succ_r.
      apply Z.div_lt_upper_bound; [lia|].
      lia. }
    assert (Hhi_le1 : u64_val hi <= 1).
    { rewrite Hhi, u128_hi_val, Hc128_3_val.
      pose proof (u64_range p3_u64).
      apply Z.div_le_upper_bound; lia. }
    unfold ov.
    simpl u256_val.
    pose proof (u64_range hi).
    destruct (Z_lt_dec r_z secp256k1_N); lia. }

  (* ===== Cleanup: provide witness and strip VST machinery ===== *)

  Exists (mkScalar (u512_val l mod secp256k1_N) ltac:(apply Z.mod_pos_bound; unfold secp256k1_N; lia)).

  change (field_at sh_l (tarray tulong 8) [] (uint512_to_val l) l_ptr)
    with (data_at sh_l (tarray tulong 8) (uint512_to_val l) l_ptr).

  entailer!.

  (* Reduce to list equality *)
  apply derives_refl'.
  f_equal.

  (* Remove all VST/pointer/bounds context -- keep only pure Z facts *)
  clear - r_final Hr_final Hmod_eq.

  (* ===== Postcondition: u256_val r_final = u512_val l mod N ===== *)

  unfold scalar_to_val.
  simpl scalar_val.
  unfold uint256_to_val.
  simpl u256_val.
  unfold limb64.
  simpl (Z.of_nat _).
  simpl (_ * 0).
  simpl (_ * 1).
  simpl (2 ^ 0).
  rewrite Z.div_1_r.
  change (64 * 2) with (128).
  change (64 * 3) with (192).
  rewrite Hr_final.
  simpl u256_val.
  rewrite Hmod_eq.
  reflexivity.
Qed.
