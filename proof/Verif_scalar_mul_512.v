(** * Verif_scalar_mul_512: Proof of body_secp256k1_scalar_mul_512 *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.
Require Import scalar_4x64.Helper_verif.
Require Import scalar_4x64.Helper_forward_call.

(* ================================================================= *)
(** ** secp256k1_scalar_mul_512 *)

(* Carry bound tactic: given [carry = acc / 2^64] and [acc = expr],
   prove [carry <= num_ub / 2^64] by bounding the numerator. *)
Local Ltac carry_bound Hcarry Hacc num_ub :=
  rewrite Hcarry, Hacc;
  apply (Z.le_trans _ (num_ub / 2^64));
  [ apply Z.div_le_mono; lia | reflexivity ].

Lemma body_secp256k1_scalar_mul_512:
  semax_body Vprog Gprog f_secp256k1_scalar_mul_512 secp256k1_scalar_mul_512_spec.
Proof.
  start_function.
  rename SH into Hsh_l_writable.
  rename SH0 into Hsh_a_readable.
  rename SH1 into Hsh_b_readable.

  (* Establish field_compatible for the l8 array - needed for address matching *)
  assert_PROP (field_compatible (tarray tulong 8) [] l8_ptr) as Hfc by entailer!.

  (* Provide Inhabitant witnesses for deadvars! *)
  assert (Inh_UInt512 : UInt512)
    by exact (mkUInt512 0 ltac:(lia)).
  assert (Inh_UInt64_Acc : (UInt64 * Acc)%type)
    by exact (mkUInt64 0 ltac:(lia), mkAcc 0 ltac:(lia)).

  (* acc = {0, 0, 0} *)
  forward. (* acc.c0 = 0 *)
  forward. (* acc.c1 = 0 *)
  forward. (* acc.c2 = 0 *)

  (* Need to fold the expanded acc struct into acc_to_val form for forward_call *)
  autorewrite with norm.

  (* Introduce the zero accumulator *)
  assert (Hacc_init_range : 0 <= 0 < 2^192) by lia.
  set (acc_init := mkAcc 0 Hacc_init_range).
  replace (Vlong (Int64.repr 0), (Vlong (Int64.repr 0), Vlong (Int64.repr 0)))
    with (acc_to_val acc_init)
    by (unfold acc_to_val, acc_init; reflexivity).

  (* Name the UInt64 limbs for all 8 scalar components *)
  set (a0 := u256_limb a 0).
  set (a1 := u256_limb a 1).
  set (a2 := u256_limb a 2).
  set (a3 := u256_limb a 3).
  set (b0 := u256_limb b 0).
  set (b1 := u256_limb b 1).
  set (b2 := u256_limb b 2).
  set (b3 := u256_limb b 3).

  (* Range facts for all limbs -- used throughout the proof *)
  pose proof (u64_range a0) as Ha0.
  pose proof (u64_range a1) as Ha1.
  pose proof (u64_range a2) as Ha2.
  pose proof (u64_range a3) as Ha3.
  pose proof (u64_range b0) as Hb0.
  pose proof (u64_range b1) as Hb1.
  pose proof (u64_range b2) as Hb2.
  pose proof (u64_range b3) as Hb3.

  (* All 16 limb products are bounded by (2^64-1)^2 *)
  assert (Hprod_bound : forall x y : UInt64,
    u64_val x * u64_val y <= (2^64 - 1) * (2^64 - 1))
    by (intros; apply Z.mul_le_mono_nonneg;
        pose proof (u64_range x); pose proof (u64_range y); lia).
  pose proof (Hprod_bound a0 b0) as Hab00.
  pose proof (Hprod_bound a0 b1) as Hab01.
  pose proof (Hprod_bound a0 b2) as Hab02.
  pose proof (Hprod_bound a0 b3) as Hab03.
  pose proof (Hprod_bound a1 b0) as Hab10.
  pose proof (Hprod_bound a1 b1) as Hab11.
  pose proof (Hprod_bound a1 b2) as Hab12.
  pose proof (Hprod_bound a1 b3) as Hab13.
  pose proof (Hprod_bound a2 b0) as Hab20.
  pose proof (Hprod_bound a2 b1) as Hab21.
  pose proof (Hprod_bound a2 b2) as Hab22.
  pose proof (Hprod_bound a2 b3) as Hab23.
  pose proof (Hprod_bound a3 b0) as Hab30.
  pose proof (Hprod_bound a3 b1) as Hab31.
  pose proof (Hprod_bound a3 b2) as Hab32.
  pose proof (Hprod_bound a3 b3) as Hab33.
  clear Hprod_bound.

  (* Pre-split the uninitialized l8 array into 8 individual slots.
     This lets each extract call find its target via cancel. *)
  sep_apply (unfold_data_at__tulong_8 sh_l l8_ptr Hfc).
  Intros.

  (* ===== Round 0: l8[0] = a0*b0 (1 product, uses muladd_fast + extract_fast) ===== *)

  forward. (* a0 = a->d[0] *)
  forward. (* b0 = b->d[0] *)

  (* muladd_fast(&acc, a0, b0) *)
  forward_call_muladd_fast v_acc acc_init a0 b0 acc0 Hacc0_post.
  { (* overflow: 0 + a0*b0 < 2^128 *)
    apply mul_u64_lt_u128; lia. }

  (* Track acc_val through round 0 *)
  assert (Hacc0 : acc_val acc0 = u64_val a0 * u64_val b0).
  { unfold acc_init in *.
    simpl in *.
    lia. }
  clear Hacc0_post.

  (* extract_fast(&acc, &l8[0]) -- precondition: acc < 2^128 *)
  forward_call_extract_fast v_acc acc0
    (field_address (tarray tulong 8) [ArraySubsc 0] l8_ptr)
    Tsh sh_l r0 carry0 Hr0_eq Hcarry0_eq.
  { (* parameter matching *)
    entailer!.
    simpl firstn.
    do 2 f_equal.
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_offset.
    rewrite isptr_offset_val_zero; auto. }

  assert (Hcarry0_ub : acc_val carry0 <= 2^64 - 2)
    by (carry_bound Hcarry0_eq Hacc0 ((2^64 - 1) * (2^64 - 1))).

  (* ===== Round 1: l8[1] = a0*b1 + a1*b0 (2 products, uses muladd + extract) ===== *)

  forward. (* a0 = a->d[0] *)
  forward. (* b1 = b->d[1] *)

  forward_call_muladd v_acc carry0 a0 b1 acc1a Hacc1a_eq.

  forward. (* a1 = a->d[1] *)
  forward. (* b0 = b->d[0] *)

  forward_call_muladd v_acc acc1a a1 b0 acc1 Hacc1_eq.

  (* Full chain for round 1 *)
  assert (Hacc1 : acc_val acc1 =
    acc_val carry0 + u64_val a0 * u64_val b1 + u64_val a1 * u64_val b0).
  { rewrite Hacc1_eq, Hacc1a_eq.
    reflexivity. }

  (* extract(&acc, &l8[1]) *)
  forward_call_extract v_acc acc1
    (field_address (tarray tulong 8) [ArraySubsc 1] l8_ptr)
    Tsh sh_l r1 carry1 Hr1_eq Hcarry1_eq.

  assert (Hcarry1_ub : acc_val carry1 <= 2 * 2^64 - 3)
    by (carry_bound Hcarry1_eq Hacc1 ((2^64 - 2) + 2 * ((2^64 - 1) * (2^64 - 1)))).

  (* ===== Round 2: l8[2] = a0*b2 + a1*b1 + a2*b0 (3 products) ===== *)

  forward. (* a0 = a->d[0] *)
  forward. (* b2 = b->d[2] *)

  (* muladd(&acc, a0, b2) *)
  forward_call_muladd v_acc carry1 a0 b2 acc2a Hacc2a_eq.

  forward. (* a1 = a->d[1] *)
  forward. (* b1 = b->d[1] *)

  (* muladd(&acc, a1, b1) *)
  forward_call_muladd v_acc acc2a a1 b1 acc2b Hacc2b_eq.

  forward. (* a2 = a->d[2] *)
  forward. (* b0 = b->d[0] *)

  (* muladd(&acc, a2, b0) *)
  forward_call_muladd v_acc acc2b a2 b0 acc2 Hacc2_eq.

  (* Full chain for round 2 *)
  assert (Hacc2 : acc_val acc2 =
    acc_val carry1 + u64_val a0 * u64_val b2 + u64_val a1 * u64_val b1 + u64_val a2 * u64_val b0).
  { rewrite Hacc2_eq, Hacc2b_eq, Hacc2a_eq.
    lia. }

  (* extract(&acc, &l8[2]) *)
  forward_call_extract v_acc acc2
    (field_address (tarray tulong 8) [ArraySubsc 2] l8_ptr)
    Tsh sh_l r2 carry2 Hr2_eq Hcarry2_eq.

  assert (Hcarry2_ub : acc_val carry2 <= 3 * 2^64 - 4)
    by (carry_bound Hcarry2_eq Hacc2 ((2 * 2^64 - 3) + 3 * ((2^64 - 1) * (2^64 - 1)))).

  (* ===== Round 3: l8[3] = a0*b3 + a1*b2 + a2*b1 + a3*b0 (4 products) ===== *)

  forward. (* a0 = a->d[0] *)
  forward. (* b3 = b->d[3] *)

  (* muladd(&acc, a0, b3) *)
  forward_call_muladd v_acc carry2 a0 b3 acc3a Hacc3a_eq.

  forward. (* a1 = a->d[1] *)
  forward. (* b2 = b->d[2] *)

  (* muladd(&acc, a1, b2) *)
  forward_call_muladd v_acc acc3a a1 b2 acc3b Hacc3b_eq.

  forward. (* a2 = a->d[2] *)
  forward. (* b1 = b->d[1] *)

  (* muladd(&acc, a2, b1) *)
  forward_call_muladd v_acc acc3b a2 b1 acc3c Hacc3c_eq.

  forward. (* a3 = a->d[3] *)
  forward. (* b0 = b->d[0] *)

  (* muladd(&acc, a3, b0) *)
  forward_call_muladd v_acc acc3c a3 b0 acc3 Hacc3_eq.

  (* Full chain for round 3 *)
  assert (Hacc3 : acc_val acc3 =
    acc_val carry2 + u64_val a0 * u64_val b3 + u64_val a1 * u64_val b2
    + u64_val a2 * u64_val b1 + u64_val a3 * u64_val b0).
  { rewrite Hacc3_eq, Hacc3c_eq, Hacc3b_eq, Hacc3a_eq.
    lia. }

  (* extract(&acc, &l8[3]) *)
  forward_call_extract v_acc acc3
    (field_address (tarray tulong 8) [ArraySubsc 3] l8_ptr)
    Tsh sh_l r3 carry3 Hr3_eq Hcarry3_eq.

  assert (Hcarry3_ub : acc_val carry3 <= 4 * 2^64 - 5)
    by (carry_bound Hcarry3_eq Hacc3 ((3 * 2^64 - 4) + 4 * ((2^64 - 1) * (2^64 - 1)))).

  (* ===== Round 4: l8[4] = a1*b3 + a2*b2 + a3*b1 (3 products) ===== *)

  forward. (* a1 = a->d[1] *)
  forward. (* b3 = b->d[3] *)

  (* muladd(&acc, a1, b3) *)
  forward_call_muladd v_acc carry3 a1 b3 acc4a Hacc4a_eq.

  forward. (* a2 = a->d[2] *)
  forward. (* b2 = b->d[2] *)

  (* muladd(&acc, a2, b2) *)
  forward_call_muladd v_acc acc4a a2 b2 acc4b Hacc4b_eq.

  forward. (* a3 = a->d[3] *)
  forward. (* b1 = b->d[1] *)

  (* muladd(&acc, a3, b1) *)
  forward_call_muladd v_acc acc4b a3 b1 acc4 Hacc4_eq.

  (* Full chain for round 4 *)
  assert (Hacc4 : acc_val acc4 =
    acc_val carry3 + u64_val a1 * u64_val b3 + u64_val a2 * u64_val b2
    + u64_val a3 * u64_val b1).
  { rewrite Hacc4_eq, Hacc4b_eq, Hacc4a_eq. lia. }

  (* extract(&acc, &l8[4]) *)
  forward_call_extract v_acc acc4
    (field_address (tarray tulong 8) [ArraySubsc 4] l8_ptr)
    Tsh sh_l r4 carry4 Hr4_eq Hcarry4_eq.

  assert (Hcarry4_ub : acc_val carry4 <= 3 * 2^64 - 3)
    by (carry_bound Hcarry4_eq Hacc4 ((4 * 2^64 - 5) + 3 * ((2^64 - 1) * (2^64 - 1)))).

  (* ===== Round 5: l8[5] = a2*b3 + a3*b2 (2 products) ===== *)

  forward. (* a2 = a->d[2] *)
  forward. (* b3 = b->d[3] *)

  (* muladd(&acc, a2, b3) *)
  forward_call_muladd v_acc carry4 a2 b3 acc5a Hacc5a_eq.

  forward. (* a3 = a->d[3] *)
  forward. (* b2 = b->d[2] *)

  (* muladd(&acc, a3, b2) *)
  forward_call_muladd v_acc acc5a a3 b2 acc5 Hacc5_eq.

  (* Full chain for round 5 *)
  assert (Hacc5 : acc_val acc5 =
    acc_val carry4 + u64_val a2 * u64_val b3 + u64_val a3 * u64_val b2).
  { rewrite Hacc5_eq, Hacc5a_eq. lia. }

  (* extract(&acc, &l8[5]) *)
  forward_call_extract v_acc acc5
    (field_address (tarray tulong 8) [ArraySubsc 5] l8_ptr)
    Tsh sh_l r5 carry5 Hr5_eq Hcarry5_eq.

  assert (Hcarry5_ub : acc_val carry5 <= 2 * 2^64 - 2)
    by (carry_bound Hcarry5_eq Hacc5 ((3 * 2^64 - 3) + 2 * ((2^64 - 1) * (2^64 - 1)))).

  (* ===== Round 6: l8[6],l8[7] = a3*b3 (1 product, uses muladd_fast + extract_fast + store) ===== *)

  forward. (* a3 = a->d[3] *)
  forward. (* b3 = b->d[3] *)

  (* muladd_fast(&acc, a3, b3) -- precondition: acc + a3*b3 < 2^128 *)
  forward_call_muladd_fast v_acc carry5 a3 b3 acc6 Hacc6_eq.

  (* Full chain for round 6 *)
  assert (Hacc6 : acc_val acc6 = acc_val carry5 + u64_val a3 * u64_val b3).
  { exact Hacc6_eq. }

  (* extract_fast(&acc, &l8[6]) -- precondition: acc < 2^128 *)
  forward_call_extract_fast v_acc acc6
    (field_address (tarray tulong 8) [ArraySubsc 6] l8_ptr)
    Tsh sh_l r6 carry6 Hr6_eq Hcarry6_eq.

  (* l8[7] = acc.c0: first read acc.c0 into temp *)
  forward.
  (* Now store to l8[7] *)
  change tulong with (nested_field_type (tarray tulong 8) (SUB 7)).
  rewrite <- field_at__data_at_.
  forward. (* l8[7] = acc.c0 *)

  (* ===== Cleanup: reassemble l8[0..7] array and strip VST machinery ===== *)

  (* Provide the existential witness *)
  Exists (mul_256 a b).
  entailer!.

  (* Normalize types: nested_field_type (tarray tulong 8) (SUB 7) = tulong *)
  change (nested_field_type (tarray tulong 8) (SUB 7)) with tulong in *.
  change (tarray tulong 8) with (tarray tulong 8) in *.

  (* Convert field_at for l8[7] into data_at *)
  rewrite (field_at_data_at sh_l (tarray tulong 8) (SUB 7)) by reflexivity.
  change (nested_field_type (tarray tulong 8) (SUB 7)) with tulong.

  (* Normalize l8[7] value to uint64_to_val form *)
  change (Vlong (Int64.repr (limb64 (acc_val carry6) 0)))
    with (uint64_to_val (acc_lo carry6)).

  (* Fold the 8 individual data_at into a single array data_at *)
  sep_apply (fold_data_at_tulong_8 sh_l l8_ptr
    (uint64_to_val (acc_lo acc0))
    (uint64_to_val (acc_lo acc1))
    (uint64_to_val (acc_lo acc2))
    (uint64_to_val (acc_lo acc3))
    (uint64_to_val (acc_lo acc4))
    (uint64_to_val (acc_lo acc5))
    (uint64_to_val (acc_lo acc6))
    (uint64_to_val (acc_lo carry6))
    Hfc).

  (* Reduce to list equality *)
  apply derives_refl'.
  f_equal.

  (* Remove all VST/pointer/bounds context -- keep only pure Z facts *)
  clear - a b
    acc0 Hacc0
    carry0 Hcarry0_eq
    acc1 Hacc1
    carry1 Hcarry1_eq
    acc2 Hacc2
    carry2 Hcarry2_eq
    acc3 Hacc3
    carry3 Hcarry3_eq
    acc4 Hacc4
    carry4 Hcarry4_eq
    acc5 Hacc5
    carry5 Hcarry5_eq
    acc6 Hacc6
    carry6 Hcarry6_eq.

  (* Strip Vlong/Int64.repr wrappers *)
  unfold uint512_to_val, uint64_to_val.
  change (map (fun z => Vlong (Int64.repr z))
    [u64_val (acc_lo acc0); u64_val (acc_lo acc1);
     u64_val (acc_lo acc2); u64_val (acc_lo acc3);
     u64_val (acc_lo acc4); u64_val (acc_lo acc5);
     u64_val (acc_lo acc6); u64_val (acc_lo carry6)] =
   map (fun z => Vlong (Int64.repr z))
    [limb64 (u512_val (mul_256 a b)) 0; limb64 (u512_val (mul_256 a b)) 1;
     limb64 (u512_val (mul_256 a b)) 2; limb64 (u512_val (mul_256 a b)) 3;
     limb64 (u512_val (mul_256 a b)) 4; limb64 (u512_val (mul_256 a b)) 5;
     limb64 (u512_val (mul_256 a b)) 6; limb64 (u512_val (mul_256 a b)) 7]).
  f_equal.

  (* Unfold record wrappers to pure Z mod/div *)
  unfold acc_lo.
  simpl u64_val.
  unfold limb64.
  simpl Z.of_nat.
  rewrite !Z.mul_0_r, !Z.pow_0_r, !Z.div_1_r.

  (* ===== Postcondition: prove mul_256 correctness via schoolbook lemma ===== *)

  (* Apply the general schoolbook multiplication lemma *)
  set (B := 2^64).
  pose proof (schoolbook_mul_4x4 B ltac:(unfold B; lia)
    (u64_val a0) (u64_val a1) (u64_val a2) (u64_val a3)
    (u64_val b0) (u64_val b1) (u64_val b2) (u64_val b3)
    ltac:(pose proof (u64_range a0); lia)
    ltac:(pose proof (u64_range a1); lia)
    ltac:(pose proof (u64_range a2); lia)
    ltac:(pose proof (u64_range a3); lia)
    ltac:(pose proof (u64_range b0); lia)
    ltac:(pose proof (u64_range b1); lia)
    ltac:(pose proof (u64_range b2); lia)
    ltac:(pose proof (u64_range b3); lia)
    (acc_val acc0) Hacc0
    (acc_val carry0) Hcarry0_eq
    (acc_val acc1) Hacc1
    (acc_val carry1) Hcarry1_eq
    (acc_val acc2) Hacc2
    (acc_val carry2) Hcarry2_eq
    (acc_val acc3) Hacc3
    (acc_val carry3) Hcarry3_eq
    (acc_val acc4) Hacc4
    (acc_val carry4) Hcarry4_eq
    (acc_val acc5) Hacc5
    (acc_val carry5) Hcarry5_eq
    (acc_val acc6) Hacc6
    (acc_val carry6) Hcarry6_eq
  ) as Hschoolbook.

  (* The schoolbook lemma talks about eval4, connect to u256_val *)
  assert (Heval_a : eval4 B (u64_val a0) (u64_val a1) (u64_val a2) (u64_val a3) = u256_val a)
    by (subst a0 a1 a2 a3; exact (u256_as_eval4 a)).
  assert (Heval_b : eval4 B (u64_val b0) (u64_val b1) (u64_val b2) (u64_val b3) = u256_val b)
    by (subst b0 b1 b2 b3; exact (u256_as_eval4 b)).

  rewrite Heval_a, Heval_b in Hschoolbook.
  unfold mul_256.
  simpl u512_val.
  destruct Hschoolbook as (-> & -> & -> & -> & -> & -> & -> & ->).
  subst B.
  reflexivity.
Qed.
