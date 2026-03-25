(** * Verif_scalar_4x64: Correctness proofs for scalar_4x64.c *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import VST.floyd.proofauto.
Require Import compcert.lib.Zbits.
Require Import scalar_4x64.Source_scalar_4x64.
Require Import scalar_4x64.Spec_scalar_4x64.
Require Import scalar_4x64.Impl_scalar_4x64.
Require Import scalar_4x64.Helper_array_fold.
Require Import scalar_4x64.Helper_arithmetic.


(* ================================================================= *)
(** ** Proof infrastructure *)

(* Inhabitant instances needed by deadvars! *)
Instance Inhabitant_UInt64_ : Inhabitant UInt64 := mkUInt64 0 ltac:(lia).
Instance Inhabitant_UInt128_ : Inhabitant UInt128 := mkUInt128 0 ltac:(lia).
Instance Inhabitant_Acc_ : Inhabitant Acc := mkAcc 0 ltac:(lia).
Instance Inhabitant_UInt256_ : Inhabitant UInt256 := mkUInt256 0 ltac:(lia).
Instance Inhabitant_UInt512_ : Inhabitant UInt512 := mkUInt512 0 ltac:(lia).

(* ----------------------------------------------------------------- *)
(** *** limb64 properties *)

(** [limb64 x i] is in unsigned 64-bit range. *)
Lemma limb64_u64_range : forall x i,
  0 <= limb64 x i <= Int64.max_unsigned.
Proof.
  intros. unfold limb64.
  pose proof (Z.mod_pos_bound (x / 2^(64 * Z.of_nat i)) (2^64) ltac:(lia)).
  rep_lia.
Qed.

(** For a value in [0, 2^64), limb 0 is the value itself. *)
Lemma limb64_u64_val_0 : forall (a : UInt64), limb64 (u64_val a) 0 = u64_val a.
Proof.
  intros. unfold limb64. simpl Z.of_nat.
  rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
  apply Z.mod_small. pose proof (u64_range a). lia.
Qed.

(** For a value in [0, 2^64), limb 1 is 0. *)
Lemma limb64_u64_val_1 : forall (a : UInt64), limb64 (u64_val a) 1 = 0.
Proof.
  intros. unfold limb64. simpl Z.of_nat. rewrite Z.mul_1_r.
  rewrite Z.div_small by (pose proof (u64_range a); lia). reflexivity.
Qed.

(** Shifting by 64 bits advances the limb index:
    [limb64 (x / 2^64) i = limb64 x (S i)]. *)
Lemma limb64_shift : forall x i,
  0 <= x ->
  limb64 (x / 2^64) i = limb64 x (S i).
Proof.
  intros. unfold limb64.
  simpl Z.of_nat.
  rewrite Zdiv.Zdiv_Zdiv by lia.
  rewrite <- Z.pow_add_r by lia.
  f_equal. f_equal. f_equal. lia.
Qed.

(** Top limb of a value bounded by [2^(64*(i+1))] is 0. *)
Lemma limb64_high_zero : forall x i,
  0 <= x < 2^(64 * Z.of_nat (S i)) ->
  limb64 x (S i) = 0.
Proof.
  intros. unfold limb64.
  rewrite Z.div_small by lia.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Multiplication bounds *)

(** The product of two 64-bit unsigned integers is at most [(2^64-1)^2]. *)
Lemma u64_mul_bound : forall (a b : UInt64),
  u64_val a * u64_val b <= (2^64 - 1) * (2^64 - 1).
Proof.
  intros. apply Z.mul_le_mono_nonneg;
  pose proof (u64_range a); pose proof (u64_range b); lia.
Qed.

(** Product of two 32-bit values fits in 64 bits. *)
Lemma mul_u32_range : forall a b,
  0 <= a <= Int.max_unsigned ->
  0 <= b <= Int.max_unsigned ->
  0 <= a * b <= Int64.max_unsigned.
Proof.
  intros.
  unfold Int64.max_unsigned, Int.max_unsigned in *.
  simpl in *.
  split.
  - apply Z.mul_nonneg_nonneg; lia.
  - assert (a * b <= (2^32 - 1) * (2^32 - 1)) by (apply Z.mul_le_mono_nonneg; lia).
    lia.
Qed.

(** The product of two 64-bit unsigned integers fits in 128 bits. *)
Lemma mul_u64_lt_u128 : forall a b,
  0 <= a < 2^64 ->
  0 <= b < 2^64 ->
  a * b < 2^128.
Proof.
  intros a b Ha Hb.
  assert (a * b <= (2^64 - 1) * (2^64 - 1))
    by (apply Z.mul_le_mono_nonneg; lia).
  lia.
Qed.

(** The high half of a 64x64 multiplication fits strictly:
    [(a * b) / 2^64 <= 2^64 - 2]. *)
Lemma mul_u64_hi_le : forall a b,
  0 <= a < 2^64 -> 0 <= b < 2^64 ->
  (a * b) / 2^64 <= 2^64 - 2.
Proof.
  intros.
  enough ((a * b) / 2^64 < 2^64 - 1) by lia.
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

(** Euclidean division identity with commuted multiplication. *)
Lemma div_mod_eq : forall a b, b <> 0 -> a = a / b * b + a mod b.
Proof. intros. pose proof (Z_div_mod_eq_full a b). lia. Qed.

(* ----------------------------------------------------------------- *)
(** *** eval4 / u256 *)

(** [eval4 (2^64) (u64_val (u256_limb x 0)) ... = u256_val x]. *)
Lemma u256_as_eval4 : forall (x : UInt256),
  eval4 (2^64)
    (u64_val (u256_limb x 0)) (u64_val (u256_limb x 1))
    (u64_val (u256_limb x 2)) (u64_val (u256_limb x 3))
  = u256_val x.
Proof.
  intros. unfold u256_limb; simpl u64_val.
  change (limb64 (u256_val x) 0) with (limb (2^64) (u256_val x) 0).
  change (limb64 (u256_val x) 1) with (limb (2^64) (u256_val x) 1).
  change (limb64 (u256_val x) 2) with (limb (2^64) (u256_val x) 2).
  change (limb64 (u256_val x) 3) with (limb (2^64) (u256_val x) 3).
  apply eval4_limbs; [lia | pose proof (u256_range x); lia].
Qed.

(* ----------------------------------------------------------------- *)
(** *** Carry arithmetic *)

(**
    These lemmas justify the limb-by-limb addition used across all
    carry-propagating proofs (muladd, sumadd, accum_u64, etc.).
    The core identity is

      [(a + b) / M  =  a/M  +  b/M  +  (a mod M + b mod M) / M]

    where the last term is the carry (0 or 1).  From this we derive
    that each 64-bit limb of [a + b] equals the corresponding limb
    sum plus carry-in, modulo [2^64]. *)

(** Carry decomposition of integer division. *)
Lemma Z_div_add_carry : forall a b M,
  0 < M -> 0 <= a -> 0 <= b ->
  (a + b) / M = a / M + b / M + (a mod M + b mod M) / M.
Proof.
  intros.
  rewrite (Z.div_mod a M) at 1 by lia.
  rewrite (Z.div_mod b M) at 1 by lia.
  replace (M * (a / M) + a mod M + (M * (b / M) + b mod M))
    with ((a / M + b / M) * M + (a mod M + b mod M)) by ring.
  rewrite Z.div_add_l by lia.
  reflexivity.
Qed.

(** The carry from adding two residues is 0 or 1. *)
Lemma carry_value : forall a b M,
  0 < M -> 0 <= a -> 0 <= b ->
  (a mod M + b mod M) / M = if a mod M + b mod M <? M then 0 else 1.
Proof.
  intros.
  destruct (a mod M + b mod M <? M) eqn:Hc.
  - apply Z.ltb_lt in Hc.
    apply Z.div_small.
    split; [apply Z.add_nonneg_nonneg; apply Z.mod_pos_bound |]; lia.
  - apply Z.ltb_ge in Hc.
    symmetry. apply Z.div_unique with (r := a mod M + b mod M - M).
    + assert (a mod M < M) by (apply Z.mod_pos_bound; lia).
      assert (b mod M < M) by (apply Z.mod_pos_bound; lia). lia.
    + lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Limb-wise addition *)

(** Limb 0: sum of low limbs = low limb of sum (mod 2^64).
    No incoming carry for the lowest digit. *)
Lemma limb_add_0 : forall a b,
  0 <= a -> 0 <= b ->
  Int64.eqm (limb64 a 0 + limb64 b 0)
             (limb64 (a + b) 0).
Proof.
  intros. unfold limb64, Int64.eqm.
  replace Int64.modulus with (2^64) by reflexivity.
  simpl Z.of_nat. rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r.
  rewrite Z.add_mod by lia.
  apply Zbits.eqmod_mod; lia.
Qed.

(** Limb 1: sum of middle limbs + carry-in = middle limb of sum (mod 2^64). *)
Lemma limb_add_1 : forall a b,
  0 <= a -> 0 <= b ->
  Int64.eqm (limb64 a 1 + (limb64 b 1 +
               (if limb64 a 0 + limb64 b 0 <? 2^64 then 0 else 1)))
             (limb64 (a + b) 1).
Proof.
  intros. unfold limb64. simpl Z.of_nat.
  rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r, Z.mul_1_r.
  unfold Int64.eqm. replace Int64.modulus with (2^64) by reflexivity.
  replace ((a + b) / 2^64) with
    (a / 2^64 + b / 2^64 + (a mod 2^64 + b mod 2^64) / 2^64)
    by (symmetry; apply Z_div_add_carry; lia).
  rewrite carry_value by lia.
  apply Zbits.eqmod_trans with
    (y := a / 2^64 + b / 2^64 +
          (if a mod 2^64 + b mod 2^64 <? 2^64 then 0 else 1)).
  - replace (a / 2^64 + b / 2^64 +
             (if a mod 2^64 + b mod 2^64 <? 2^64 then 0 else 1))
      with (a / 2^64 + (b / 2^64 +
             (if a mod 2^64 + b mod 2^64 <? 2^64 then 0 else 1))) by lia.
    apply Zbits.eqmod_add; [| apply Zbits.eqmod_add;
      [| apply Zbits.eqmod_refl]];
    apply Zbits.eqmod_sym; apply Zbits.eqmod_mod; lia.
  - apply Zbits.eqmod_mod; lia.
Qed.

(** Limb 2: sum of high limbs + carry-in = high limb of sum (mod 2^64).
    Requires [b < 2^128] (i.e. b fits in 2 limbs) so that [b/(M*M) = 0]. *)
Lemma limb_add_2 : forall a b,
  0 <= a -> 0 <= b -> b < 2^128 ->
  Int64.eqm (limb64 a 2 + (if limb64 a 1 + limb64 b 1 +
               (if limb64 a 0 + limb64 b 0 <? 2^64 then 0 else 1) <? 2^64 then 0 else 1))
             (limb64 (a + b) 2).
Proof.
  intros a b Ha Hb Hb128. unfold limb64. simpl Z.of_nat.
  rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r, Z.mul_1_r.
  replace (64 * 2) with (64 + 64) by lia.
  rewrite Z.pow_add_r by lia.
  set (M := (2^64)%Z).
  unfold Int64.eqm. replace Int64.modulus with M by (unfold M; reflexivity).
  assert (Hbdiv : b / (M * M) = 0).
  { apply Z.div_small. unfold M in *. lia. }
  replace ((a + b) / (M * M)) with
    (a / (M * M) + b / (M * M) +
     (a mod (M * M) + b mod (M * M)) / (M * M))
    by (symmetry; apply Z_div_add_carry; [unfold M; lia | lia | lia]).
  rewrite Hbdiv, Z.add_0_r.
  set (la0 := a mod M).
  set (lb0 := b mod M).
  set (la1 := a / M mod M).
  set (lb1 := b / M mod M).
  assert (Hla0 : 0 <= la0 < M) by (unfold la0, M; apply Z.mod_pos_bound; lia).
  assert (Hlb0 : 0 <= lb0 < M) by (unfold lb0, M; apply Z.mod_pos_bound; lia).
  assert (Hla1 : 0 <= la1 < M) by (unfold la1, M; apply Z.mod_pos_bound; lia).
  assert (Hlb1 : 0 <= lb1 < M) by (unfold lb1, M; apply Z.mod_pos_bound; lia).
  set (carry2 := if la0 + lb0 <? M
                 then if la1 + lb1 <? M then 0 else 1
                 else if la1 + lb1 + 1 <? M then 0 else 1).
  assert (Hcarry2_lhs :
    (if la1 + lb1 + (if la0 + lb0 <? M then 0 else 1) <? M then 0 else 1) = carry2). {
    unfold carry2.
    destruct (la0 + lb0 <? M) eqn:Ec0; destruct (la1 + lb1 <? M) eqn:Ec1;
    replace (la1 + lb1 + 0) with (la1 + lb1) by lia ||
    replace (la1 + lb1 + 1) with (la1 + lb1 + 1) by lia;
    try rewrite Ec1; try reflexivity;
    destruct (la1 + lb1 + 1 <? M); reflexivity.
  }
  rewrite Hcarry2_lhs.
  replace (a mod (M * M)) with (la0 + la1 * M)
    by (unfold la0, la1, M; rewrite Zmod_recombine by lia; ring).
  replace (b mod (M * M)) with (lb0 + lb1 * M)
    by (unfold lb0, lb1, M; rewrite Zmod_recombine by lia; ring).
  assert (Hcarry_val : (la0 + la1 * M + (lb0 + lb1 * M)) / (M * M) = carry2). {
    unfold carry2.
    destruct (la0 + lb0 <? M) eqn:Ec0; destruct (la1 + lb1 <? M) eqn:Ec1.
    - apply Z.ltb_lt in Ec0; apply Z.ltb_lt in Ec1.
      apply Z.div_small; lia.
    - apply Z.ltb_lt in Ec0; apply Z.ltb_ge in Ec1.
      symmetry; apply Z.div_unique with (r := la0 + lb0 + (la1 + lb1 - M) * M); lia.
    - apply Z.ltb_ge in Ec0; apply Z.ltb_lt in Ec1.
      destruct (la1 + lb1 + 1 <? M) eqn:Ec1'.
      + apply Z.ltb_lt in Ec1'. apply Z.div_small; lia.
      + apply Z.ltb_ge in Ec1'.
        symmetry; apply Z.div_unique with (r := la0 + lb0 - M + (la1 + lb1 + 1 - M) * M); lia.
    - apply Z.ltb_ge in Ec0; apply Z.ltb_ge in Ec1.
      destruct (la1 + lb1 + 1 <? M) eqn:Ec1'.
      + apply Z.ltb_lt in Ec1'.
        symmetry; apply Z.div_unique with (r := la0 + lb0 - M + (la1 + lb1 + 1) * M); lia.
      + apply Z.ltb_ge in Ec1'.
        symmetry; apply Z.div_unique with (r := la0 + lb0 - M + (la1 + lb1 + 1 - M) * M); lia.
  }
  rewrite Hcarry_val.
  apply Zbits.eqmod_trans with (y := a / (M * M) + carry2).
  - apply Zbits.eqmod_add.
    + apply Zbits.eqmod_sym. apply Zbits.eqmod_mod. lia.
    + apply Zbits.eqmod_refl.
  - apply Zbits.eqmod_mod. lia.
Qed.

(** Limb 2 for addition with a u64: [b < 2^64] so [limb64 b 1 = 0]. *)
Lemma limb_add_2_u64 : forall a b,
  0 <= a -> 0 <= b < 2^64 ->
  Int64.eqm (limb64 a 2 +
    (if limb64 a 1 + (if limb64 a 0 + b <? 2^64 then 0 else 1) <? 2^64 then 0 else 1))
    (limb64 (a + b) 2).
Proof.
  intros a b Ha [Hb0 Hb1].
  unfold limb64. simpl Z.of_nat.
  rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r, Z.mul_1_r.
  replace (64 * 2) with (64 + 64) by lia.
  rewrite Z.pow_add_r by lia.
  set (M := (2^64)%Z).
  unfold Int64.eqm. replace Int64.modulus with M by (unfold M; reflexivity).
  assert (Hbdiv : b / (M * M) = 0) by (apply Z.div_small; unfold M; lia).
  replace ((a + b) / (M * M)) with
    (a / (M * M) + b / (M * M) + (a mod (M * M) + b mod (M * M)) / (M * M))
    by (symmetry; apply Z_div_add_carry; [unfold M; lia | lia | lia]).
  rewrite Hbdiv, Z.add_0_r.
  set (la0 := a mod M).
  set (la1 := a / M mod M).
  assert (Hla0 : 0 <= la0 < M) by (unfold la0, M; apply Z.mod_pos_bound; lia).
  assert (Hla1 : 0 <= la1 < M) by (unfold la1, M; apply Z.mod_pos_bound; lia).
  assert (Hb_mod : b mod (M * M) = b) by (apply Z.mod_small; unfold M; lia).
  rewrite Hb_mod.
  replace (a mod (M * M)) with (la0 + la1 * M)
    by (unfold la0, la1, M; rewrite Zmod_recombine by lia; ring).
  set (carry0 := if la0 + b <? M then 0 else 1).
  assert (Hc0 : 0 <= carry0 <= 1)
    by (unfold carry0; destruct (la0 + b <? M); lia).
  assert (Hcarry_val : (la0 + la1 * M + b) / (M * M) = if la1 + carry0 <? M then 0 else 1).
  { unfold carry0.
    destruct (la0 + b <? M) eqn:Ec0.
    - apply Z.ltb_lt in Ec0.
      destruct (la1 + 0 <? M) eqn:Ec1; [apply Z.ltb_lt in Ec1 | apply Z.ltb_ge in Ec1].
      + replace (la1 + 0) with la1 by lia.
        apply Z.div_small. lia.
      + lia.
    - apply Z.ltb_ge in Ec0.
      destruct (la1 + 1 <? M) eqn:Ec1; [apply Z.ltb_lt in Ec1 | apply Z.ltb_ge in Ec1].
      + apply Z.div_small. lia.
      + symmetry; apply Z.div_unique with (r := la0 + la1 * M + b - M * M); lia.
  }
  rewrite Hcarry_val.
  apply Zbits.eqmod_trans with (y := a / (M * M) + (if la1 + carry0 <? M then 0 else 1)).
  - apply Zbits.eqmod_add.
    + apply Zbits.eqmod_sym. apply Zbits.eqmod_mod. lia.
    + apply Zbits.eqmod_refl.
  - apply Zbits.eqmod_mod. lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** VST carry bridge lemmas

    The C code propagates carries through 64-bit limbs using
    [c0 < tl] as a carry-detect idiom.  After VST symbolic execution,
    the postcondition contains nested [Int64.ltu] / [Int.signed] /
    [Int.repr] expressions.

    These bridge lemmas translate each limb's C-level expression
    into the pure-math [limb_add_N] form in a single step, keeping
    the body proofs to one [apply] per limb. *)

(** Carry detection via [ltu]: [b2z (repr(c0+tl) < repr(tl))] equals
    the arithmetic carry (0 if no wrap, 1 if wrap). *)
Lemma ltu_carry_b2z : forall c0 tl,
  0 <= c0 <= Int64.max_unsigned ->
  0 <= tl <= Int64.max_unsigned ->
  Z.b2z (Int64.ltu (Int64.repr (c0 + tl)) (Int64.repr tl)) =
  (if c0 + tl <? Int64.modulus then 0 else 1).
Proof.
  intros.
  destruct (c0 + tl <? Int64.modulus) eqn:Hcarry;
    [apply Z.ltb_lt in Hcarry | apply Z.ltb_ge in Hcarry];
    unfold Int64.ltu.
  - rewrite !Int64.unsigned_repr by rep_lia.
    rewrite zlt_false by lia. reflexivity.
  - rewrite (Int64.unsigned_repr tl) by rep_lia.
    rewrite Int64.unsigned_repr_eq.
    replace ((c0 + tl) mod Int64.modulus) with (c0 + tl - Int64.modulus)
      by (symmetry; apply Zmod_unique with 1; rep_lia).
    rewrite zlt_true by rep_lia. reflexivity.
Qed.

(** Bridge for limb 1: normalize [ltu]/[signed]/[repr] into the
    carry form that [limb_add_1] uses. *)
Lemma muladd_limb1 : forall acc_v prod,
  0 <= acc_v -> 0 <= prod ->
  Int64.eqm
    (limb64 acc_v 1 + (limb64 prod 1 +
      Int.signed (Int.repr
        (Z.b2z (Int64.ltu
          (Int64.repr (limb64 acc_v 0 + limb64 prod 0))
          (Int64.repr (limb64 prod 0)))))))
    (limb64 (acc_v + prod) 1).
Proof.
  intros acc_v prod Hacc Hprod.
  pose proof (limb64_u64_range acc_v 0) as Hla0.
  pose proof (limb64_u64_range prod 0) as Hlb0.
  rewrite (ltu_carry_b2z (limb64 acc_v 0) (limb64 prod 0)) by assumption.
  assert (Hinner :
    Int.signed (Int.repr (if limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus then 0 else 1))
    = (if limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus then 0 else 1)).
  { destruct (limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus); reflexivity. }
  rewrite Hinner.
  replace Int64.modulus with (2^64) by reflexivity.
  apply limb_add_1; lia.
Qed.

(** Bridge for limb 2: normalize two levels of [ltu]/[signed]/[repr]
    into the carry form that [limb_add_2] uses.

    Takes [av] and [bv] as separate u64 factors (not just their
    product) because we need [(av * bv) / 2^64 <= 2^64 - 2] to
    prove the intermediate carry fits in a u64. *)
Lemma muladd_limb2 : forall acc_v av bv,
  0 <= acc_v ->
  0 <= av < 2^64 -> 0 <= bv < 2^64 ->
  let prod := av * bv in
  let c0_carry :=
    Z.b2z (Int64.ltu
      (Int64.repr (limb64 acc_v 0 + limb64 prod 0))
      (Int64.repr (limb64 prod 0))) in
  let th := limb64 prod 1 + Int.signed (Int.repr c0_carry) in
  Int64.eqm
    (limb64 acc_v 2 +
      Int.signed (Int.repr
        (Z.b2z (Int64.ltu
          (Int64.repr (limb64 acc_v 1 + th))
          (Int64.repr th)))))
    (limb64 (acc_v + prod) 2).
Proof.
  intros acc_v av bv Hacc Hav Hbv prod c0_carry th.
  pose proof (limb64_u64_range acc_v 0) as Hla0.
  pose proof (limb64_u64_range prod 0) as Hlb0.
  pose proof (limb64_u64_range acc_v 1) as Hla1.
  pose proof (limb64_u64_range prod 1) as Hlb1.
  subst c0_carry th.
  rewrite (ltu_carry_b2z (limb64 acc_v 0) (limb64 prod 0)) by assumption.
  assert (Hinner :
    Int.signed (Int.repr
      (if limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus then 0 else 1))
    = (if limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus then 0 else 1)).
  { destruct (limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus); reflexivity. }
  rewrite Hinner. clear Hinner.
  set (c0' := if limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus then 0 else 1).
  assert (Hc0' : 0 <= c0' <= 1)
    by (subst c0'; destruct (limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus); lia).
  assert (Hlb1' : limb64 prod 1 <= Int64.max_unsigned - 1).
  { unfold limb64. simpl Z.of_nat. change (64 * 1)%Z with 64.
    subst prod. change (2^64) with Int64.modulus.
    pose proof (mul_u64_hi_le av bv Hav Hbv).
    change (2^64) with Int64.modulus in H.
    rewrite Z.mod_small by (split; [apply Z.div_pos; rep_lia | rep_lia]).
    rep_lia. }
  assert (Hth : 0 <= limb64 prod 1 + c0' <= Int64.max_unsigned)
    by (subst c0'; destruct (limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus); lia).
  rewrite (ltu_carry_b2z (limb64 acc_v 1) (limb64 prod 1 + c0'))
    by (try assumption; lia).
  assert (Houter :
    Int.signed (Int.repr
      (if limb64 acc_v 1 + (limb64 prod 1 + c0') <? Int64.modulus then 0 else 1))
    = (if limb64 acc_v 1 + (limb64 prod 1 + c0') <? Int64.modulus then 0 else 1)).
  { destruct (limb64 acc_v 1 + (limb64 prod 1 + c0') <? Int64.modulus); reflexivity. }
  rewrite Houter. clear Houter.
  replace (limb64 acc_v 1 + (limb64 prod 1 + c0'))
    with (limb64 acc_v 1 + limb64 prod 1 + c0') by lia.
  replace Int64.modulus with (2^64) by reflexivity.
  subst c0'.
  apply limb_add_2; [lia | subst prod; nia | subst prod; nia].
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_to_u64 *)

(** The function body dereferences the struct pointer, reads the [lo]
    field, and returns it.  That is two [forward] steps. *)

Lemma body_secp256k1_u128_to_u64:
  semax_body Vprog Gprog
    f_secp256k1_u128_to_u64 secp256k1_u128_to_u64_spec.
Proof.
  start_function.
  forward. (* _t'1 = a->lo *)
  forward. (* return _t'1 *)
  Exists (u128_lo x).
  unfold u128_lo, uint64_to_val.
  simpl.
  entailer!.
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_hi_u64 *)

(** Same structure: dereference, read [hi] field, return. *)

Lemma body_secp256k1_u128_hi_u64:
  semax_body Vprog Gprog
    f_secp256k1_u128_hi_u64 secp256k1_u128_hi_u64_spec.
Proof.
  start_function.
  forward. (* _t'1 = a->hi *)
  forward. (* return _t'1 *)
  Exists (u128_hi x).
  unfold u128_hi, uint128_to_val.
  entailer!.
Qed.

(* ================================================================= *)
(** ** secp256k1_umul128 *)

(** Shift right 32 on Int64 equals Z division. *)
Lemma Int64_shru_32 : forall x,
  0 <= x <= Int64.max_unsigned ->
  Int64.shru (Int64.repr x) (Int64.repr 32) = Int64.repr (x / Int.modulus).
Proof.
  intros.
  rewrite Int64.shru_div_two_p.
  f_equal.
  rewrite Int64.unsigned_repr by assumption.
  rewrite Int64.unsigned_repr.
  - reflexivity.
  - rep_lia.
Qed.

(** Shift left 32 on Int64 equals Z multiplication. *)
Lemma Int64_shl_32 : forall x,
  0 <= x <= Int64.max_unsigned ->
  Int64.shl (Int64.repr x) (Int64.repr 32) = Int64.repr (x * Int.modulus).
Proof.
  intros.
  rewrite Int64.shl_mul_two_p.
  rewrite Int64.unsigned_repr by rep_lia.
  change (two_p 32) with Int.modulus.
  apply Int64.eqm_samerepr.
  apply Int64.eqm_mult;
  apply Int64.eqm_sym;
  apply Int64.eqm_unsigned_repr.
Qed.

(* ----------------------------------------------------------------- *)

(** The schoolbook multiplication low-half identity (modular form):
    ((mid34 << 32) + (uint32_t)ll) mod 2^64  =  (a * b) mod 2^64
    where mid34 = ll>>32 + (uint32_t)lh + (uint32_t)hl *)
Lemma umul128_lo_correct : forall a b,
  0 <= a <= Int64.max_unsigned ->
  0 <= b <= Int64.max_unsigned ->
  let M := Int.modulus in
  let a_lo := a mod M in
  let a_hi := a / M in
  let b_lo := b mod M in
  let b_hi := b / M in
  let mid34 := a_lo * b_lo / M + (a_lo * b_hi) mod M + (a_hi * b_lo) mod M in
  (mid34 * M + (a_lo * b_lo) mod M) mod (M * M) = (a * b) mod (M * M).
Proof.
  intros a b Ha Hb.
  cbv zeta.

  set (M := Int.modulus).
  set (al := a mod M).  set (ah := a / M).
  set (bl := b mod M).  set (bh := b / M).
  set (ll := al * bl).  set (lh := al * bh).
  set (hl := ah * bl).  set (hh := ah * bh).
  fold al bl ah bh ll lh hl.

  (* --- Setup --- *)
  assert (HM : 0 < M) by (subst M; rep_lia).
  assert (Ha_eq : a = ah * M + al) by (subst ah al; apply div_mod_eq; lia).
  assert (Hb_eq : b = bh * M + bl) by (subst bh bl; apply div_mod_eq; lia).
  assert (Hlh_eq : lh = lh / M * M + lh mod M) by (apply div_mod_eq; lia).
  assert (Hhl_eq : hl = hl / M * M + hl mod M) by (apply div_mod_eq; lia).
  assert (Hll_eq : ll = ll / M * M + ll mod M) by (apply div_mod_eq; lia).

  (* --- Main algebraic argument --- *)

  (* Step 1: Expand a*b using the schoolbook decomposition
       a*b = hh * M^2 + (lh + hl) * M + ll                     *)
  assert (Hab : a * b = hh * (M * M) + (lh + hl) * M + ll).
  { subst hh lh hl ll. rewrite Ha_eq, Hb_eq. ring. }
  rewrite Hab.

  (* Step 2: Cancel hh * M^2 by Z_mod_plus_full
       (x + k * M^2) mod M^2 = x mod M^2                       *)
  replace (hh * (M * M) + (lh + hl) * M + ll)
    with ((lh + hl) * M + ll + hh * (M * M)) by ring.
  rewrite Z_mod_plus_full.

  (* Step 3: Split each of lh, hl, ll into (high * M + low) and
     regroup so that high parts form another multiple of M^2:
       (lh + hl) * M + ll
         = (lh/M + hl/M) * M^2
           + ((lh%M + hl%M + ll/M) * M + ll%M)                 *)
  assert (Hexp : (lh + hl) * M + ll =
    (lh / M + hl / M) * (M * M) +
    ((lh mod M + hl mod M + ll / M) * M + ll mod M)).
  { rewrite Hlh_eq at 1. rewrite Hhl_eq at 1. rewrite Hll_eq at 1. ring. }
  rewrite Hexp.

  (* Step 4: Cancel the (lh/M + hl/M) * M^2 term *)
  replace ((lh / M + hl / M) * (M * M) +
           ((lh mod M + hl mod M + ll / M) * M + ll mod M))
    with ((lh mod M + hl mod M + ll / M) * M + ll mod M +
          (lh / M + hl / M) * (M * M)) by ring.
  rewrite Z_mod_plus_full.

  (* Step 5: Peel off [mod] and [+ ll%M] with [f_equal],
     cancel the common [* M] factor, then [lia] finishes. *)
  f_equal. f_equal.
  apply Z.mul_cancel_r with (p := M); lia.
Qed.

(** The schoolbook multiplication high-half identity:
    hh + (lh>>32) + (hl>>32) + (mid34>>32)  =  (a * b) / 2^64 *)
Lemma umul128_hi_correct : forall a b,
  0 <= a <= Int64.max_unsigned ->
  0 <= b <= Int64.max_unsigned ->
  let M := Int.modulus in
  let a_lo := a mod M in
  let a_hi := a / M in
  let b_lo := b mod M in
  let b_hi := b / M in
  let mid34 := a_lo * b_lo / M + (a_lo * b_hi) mod M + (a_hi * b_lo) mod M in
  a_hi * b_hi + a_lo * b_hi / M + a_hi * b_lo / M + mid34 / M = (a * b) / (M * M).
Proof.
  intros a b Ha Hb.
  cbv zeta.

  set (M := Int.modulus).
  set (al := a mod M).  set (ah := a / M).
  set (bl := b mod M).  set (bh := b / M).
  set (ll := al * bl).  set (lh := al * bh).
  set (hl := ah * bl).  set (hh := ah * bh).
  fold al bl ah bh ll lh hl.

  (* --- Setup --- *)
  assert (HM : 0 < M) by (subst M; rep_lia).
  assert (Hll_mod : 0 <= ll mod M < M) by (apply Z.mod_pos_bound; lia).
  assert (Ha_eq : a = ah * M + al) by (subst ah al; apply div_mod_eq; lia).
  assert (Hb_eq : b = bh * M + bl) by (subst bh bl; apply div_mod_eq; lia).
  assert (Hlh_eq : lh = lh / M * M + lh mod M) by (apply div_mod_eq; lia).
  assert (Hhl_eq : hl = hl / M * M + hl mod M) by (apply div_mod_eq; lia).
  assert (Hll_eq : ll = ll / M * M + ll mod M) by (apply div_mod_eq; lia).

  (* --- Main algebraic argument --- *)

  (* Step 1: Expand a*b using the schoolbook decomposition
       a*b = hh * M^2 + (lh + hl) * M + ll                     *)
  assert (Hab : a * b = hh * (M * M) + (lh + hl) * M + ll).
  { subst hh lh hl ll. rewrite Ha_eq, Hb_eq. ring. }
  rewrite Hab.

  (* Step 2: Split each of lh, hl, ll into (high * M + low) and
     regroup so that high parts form another multiple of M^2:
       (lh + hl) * M + ll
         = (lh/M + hl/M) * M^2
           + ((lh%M + hl%M + ll/M) * M + ll%M)                 *)
  assert (Hexp : (lh + hl) * M + ll =
    (lh / M + hl / M) * (M * M) +
    ((lh mod M + hl mod M + ll / M) * M + ll mod M)).
  { rewrite Hlh_eq at 1. rewrite Hhl_eq at 1. rewrite Hll_eq at 1. ring. }

  (* Step 3: Pull (hh + lh/M + hl/M) out of the division by
     Z.div_add_l, then cancel it on both sides with [f_equal]:
       ((k * M^2) + rest) / M^2  =  k + rest / M^2             *)
  replace (hh * (M * M) + (lh + hl) * M + ll)
    with ((hh + lh / M + hl / M) * (M * M) +
          ((lh mod M + hl mod M + ll / M) * M + ll mod M))
    by lia.
  rewrite Z.div_add_l by lia.
  f_equal.

  (* Step 4: Decompose division by M*M into two divisions by M,
     peel off the integer part, then kill the remainder:
       (x * M + r) / (M * M)  =  (x + r/M) / M  =  x / M
     because 0 <= r < M implies r / M = 0.                      *)
  replace (ll / M + lh mod M + hl mod M)
    with (lh mod M + hl mod M + ll / M) by lia.
  rewrite <- Z.div_div by lia.
  rewrite Z.div_add_l by lia.
  rewrite (Z.div_small (ll mod M) M) by lia.
  f_equal. lia.
Qed.

Lemma body_secp256k1_umul128:
  semax_body Vprog Gprog
    f_secp256k1_umul128 secp256k1_umul128_spec.
Proof.
  start_function.

  (* Extract the Z values from the UInt64 records for arithmetic reasoning *)
  unfold uint64_to_val in *.
  set (av := u64_val a) in *.
  set (bv := u64_val b) in *.
  assert (Hav : 0 <= av <= Int64.max_unsigned).
  { subst av.
    destruct a as [v [Ha_lo Ha_hi]].
    simpl.
    rep_lia. }

  assert (Hbv : 0 <= bv <= Int64.max_unsigned).
  { subst bv.
    destruct b as [v [Hb_lo Hb_hi]].
    simpl.
    rep_lia. }

  (* Local tactic: normalise Int.unsigned_repr_eq and shift-by-32 *)
  Ltac norm_shru :=
    repeat first
      [ rewrite !Int.unsigned_repr_eq in *
      | change (32 mod Int.modulus) with 32 in * ].

  (* Execute the four partial-product assignments *)
  do 4 forward.

  (* Normalize: resolve unsigned_repr_eq, shift amounts, shru *)
  autorewrite with norm in *.
  norm_shru.
  rewrite !(Int64_shru_32 av) in * by lia.
  rewrite !(Int64_shru_32 bv) in * by lia.
  autorewrite with norm in *.

  (* Introduce Z-level abbreviations for the 32-bit halves *)
  set (a_lo := av mod Int.modulus) in *.
  set (a_hi := av / Int.modulus) in *.
  set (b_lo := bv mod Int.modulus) in *.
  set (b_hi := bv / Int.modulus) in *.
  deadvars!.

  (* Half-word range bounds *)
  assert (Ha_lo : 0 <= a_lo <= Int.max_unsigned).
  { subst a_lo. unfold Int.max_unsigned.
    pose proof (Z.mod_pos_bound av Int.modulus ltac:(rep_lia)). rep_lia. }
  assert (Hb_lo : 0 <= b_lo <= Int.max_unsigned).
  { subst b_lo. unfold Int.max_unsigned.
    pose proof (Z.mod_pos_bound bv Int.modulus ltac:(rep_lia)). rep_lia. }
  assert (Ha_hi : 0 <= a_hi <= Int.max_unsigned).
  { subst a_hi. split; [apply Z.div_pos; rep_lia|].
    unfold Int.max_unsigned.
    enough (av / Int.modulus < Int.modulus) by lia.
    apply Z.div_lt_upper_bound; rep_lia. }
  assert (Hb_hi : 0 <= b_hi <= Int.max_unsigned).
  { subst b_hi. split; [apply Z.div_pos; rep_lia|].
    unfold Int.max_unsigned.
    enough (bv / Int.modulus < Int.modulus) by lia.
    apply Z.div_lt_upper_bound; rep_lia. }

  (* _mid34 = (ll >> 32) + (uint32_t)lh + (uint32_t)hl *)
  forward.

  (* Cross-product range bounds (needed for repr round-trips) *)
  assert (Hll : 0 <= a_lo * b_lo <= Int64.max_unsigned)
    by (apply mul_u32_range; lia).
  assert (Hlh : 0 <= a_lo * b_hi <= Int64.max_unsigned)
    by (apply mul_u32_range; lia).
  assert (Hhl : 0 <= a_hi * b_lo <= Int64.max_unsigned)
    by (apply mul_u32_range; lia).
  assert (Hhh : 0 <= a_hi * b_hi <= Int64.max_unsigned)
    by (apply mul_u32_range; lia).

  autorewrite with norm in *.
  norm_shru.
  rewrite !(Int64_shru_32 (a_lo * b_lo)) in * by lia.
  autorewrite with norm in *.

  (* Abbreviate mid34 *)
  set (mid34 := a_lo * b_lo / Int.modulus +
    (a_lo * b_hi) mod Int.modulus +
    (a_hi * b_lo) mod Int.modulus) in *.

  assert (Hmid34 : 0 <= mid34 <= Int64.max_unsigned).
  { subst mid34.
    pose proof (Z.mod_pos_bound (a_lo * b_hi) Int.modulus ltac:(rep_lia)).
    pose proof (Z.mod_pos_bound (a_hi * b_lo) Int.modulus ltac:(rep_lia)).
    pose proof (Z.div_pos (a_lo * b_lo) Int.modulus ltac:(lia) ltac:(rep_lia)).
    pose proof (Z.div_lt_upper_bound (a_lo * b_lo) Int.modulus Int.modulus
                  ltac:(rep_lia) ltac:(rep_lia)).
    rep_lia. }

  (* *hi = hh + (lh >> 32) + (hl >> 32) + (mid34 >> 32) *)
  forward.
  norm_shru.
  rewrite !(Int64_shru_32 (a_lo * b_hi)) by lia.
  rewrite !(Int64_shru_32 (a_hi * b_lo)) by lia.
  rewrite !(Int64_shru_32 mid34) in * by lia.
  autorewrite with norm in *.

  set (hi_val := a_hi * b_hi +
    a_lo * b_hi / Int.modulus +
    a_hi * b_lo / Int.modulus +
    mid34 / Int.modulus) in *.

  (* return mid34 << 32 + (uint32_t)ll *)
  forward.
  autorewrite with norm.
  norm_shru.
  rewrite !(Int64_shl_32 mid34) by lia.
  autorewrite with norm.

  set (lo_val := mid34 * Int.modulus + (a_lo * b_lo) mod Int.modulus) in *.

  (* --- Postcondition --- *)
  Exists (mul_64 a b).
  unfold mul_64, u128_lo, u128_hi, uint64_to_val; simpl.
  entailer!.

  (* Goal 1: lo_val represents (av * bv) mod 2^64 *)
  + f_equal. apply Int64.eqm_samerepr.
    apply Int64.eqm_trans with (lo_val mod Int64.modulus);
      [apply eqmod_mod; rep_lia|].
    subst lo_val mid34 a_lo a_hi b_lo b_hi av bv.
    change Int64.modulus with (Int.modulus * Int.modulus).
    rewrite umul128_lo_correct by assumption.
    unfold limb64. simpl Z.of_nat. rewrite Z.mul_0_r, Z.div_1_r.
    change (Int.modulus * Int.modulus) with Int64.modulus.
    apply Int64.eqm_refl.

  (* Goal 2: hi_val represents limb64 (av * bv) 1 *)
  + apply derives_refl'. f_equal. f_equal.
    apply Int64.eqm_samerepr.
    subst hi_val mid34 a_lo a_hi b_lo b_hi av bv.
    rewrite umul128_hi_correct by assumption.
    unfold limb64. simpl Z.of_nat. change (64 * 1)%Z with 64%Z.
    change (2^64) with Int64.modulus.
    apply Int64.eqm_sym.
    change (Int.modulus * Int.modulus) with Int64.modulus.
    apply Int64.eqm_sym.
    apply eqmod_mod.
    rep_lia.
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_mul *)

(** Plumbing around the umul128 spec. *)

Lemma body_secp256k1_u128_mul:
  semax_body Vprog Gprog
    f_secp256k1_u128_mul secp256k1_u128_mul_spec.
Proof.
  start_function.

  (* Decompose uninitialised struct into .lo and .hi fields *)
  unfold data_at_, field_at_.
  unfold_data_at (field_at sh t_secp256k1_uint128 [] _ r_ptr).
  assert_PROP (field_compatible t_secp256k1_uint128 [StructField _hi] r_ptr)
    as Hfc by entailer!.
  rewrite (field_at_data_at sh _ [StructField _hi]) by reflexivity.

  (* r->lo = secp256k1_umul128(a, b, &r->hi) *)
  forward_call (a, b,
    field_address t_secp256k1_uint128 [StructField _hi] r_ptr, sh).
  Intros vret.
  forward. (* r->lo = _t'1 *)

  (* Provide witness and reassemble struct *)
  Exists vret.
  entailer!.
  unfold uint128_to_val.
  unfold_data_at (data_at sh t_secp256k1_uint128 _ r_ptr).
  rewrite (field_at_data_at sh _ [StructField _hi]) by reflexivity.
  cancel.
Qed.

(* ================================================================= *)
(** ** muladd *)

Lemma body_muladd:
  semax_body Vprog Gprog f_muladd muladd_spec.
Proof.
  start_function.

  (* secp256k1_u128_mul(&t, a, b) *)
  forward_call.

  Intros vret.

  (* tl = secp256k1_u128_to_u64(&t) *)
  forward_call.

  Intros hi.

  (* th = secp256k1_u128_hi_u64(&t) *)
  forward_call.

  Intros lo.

  (* acc->c0 += tl *)
  forward.
  (* th += (acc->c0 < tl) *)
  forward.
  (* acc->c1 += th *)
  forward.
  forward.
  forward.
  forward.
  (* acc->c2 += (acc->c1 < th) *)
  forward.
  forward.
  forward.

  Exists (acc_muladd acc a b ltac:(lia)).
  entailer!.

  (* --- Postcondition: C struct = acc_to_val of mathematical sum --- *)
  pose proof (acc_range acc) as Hacc.
  pose proof (u64_range a) as Ha.
  pose proof (u64_range b) as Hb.
  apply derives_refl'.
  f_equal.
  unfold acc_to_val, acc_muladd. simpl.
  unfold u128_lo, u128_hi, mul_64.
  simpl u64_val. simpl u128_val.
  f_equal; f_equal.
  + (* limb 0 *)
    apply Int64.eqm_samerepr.
    apply limb_add_0; lia.
  + (* limb 1 *)
    f_equal.
    apply Int64.eqm_samerepr.
    apply muladd_limb1; lia.
  + (* limb 2 *)
    f_equal.
    apply Int64.eqm_samerepr.
    apply (muladd_limb2 (acc_val acc) (u64_val a) (u64_val b)); lia.
Qed.

(* ================================================================= *)
(** ** muladd_fast *)

Lemma body_muladd_fast:
  semax_body Vprog Gprog f_muladd_fast muladd_fast_spec.
Proof.
  start_function.

  (* secp256k1_u128_mul(&t, a, b) *)
  forward_call.

  Intros vret.

  (* tl = secp256k1_u128_to_u64(&t) *)
  forward_call.

  Intros hi.

  (* th = secp256k1_u128_hi_u64(&t) *)
  forward_call.

  Intros lo.

  (* acc->c0 += tl *)
  forward.
  (* th += (acc->c0 < tl) *)
  forward.
  (* acc->c1 += th *)
  forward.
  forward.
  forward.
  forward.

  Exists (acc_muladd acc a b ltac:(lia)).
  entailer!.

  (* --- Postcondition: C struct = acc_to_val of mathematical sum --- *)
  pose proof (acc_range acc) as Hacc.
  pose proof (u64_range a) as Ha.
  pose proof (u64_range b) as Hb.
  apply derives_refl'.
  f_equal.
  unfold acc_to_val, acc_muladd. simpl.
  unfold u128_lo, u128_hi, mul_64.
  simpl u64_val. simpl u128_val.
  f_equal; f_equal.
  + (* limb 0 *)
    apply Int64.eqm_samerepr.
    apply limb_add_0; lia.
  + (* limb 1 *)
    f_equal.
    apply Int64.eqm_samerepr.
    apply muladd_limb1; lia.
  + (* limb 2: acc + a*b < 2^128 so limb 2 is 0 on both sides *)
    f_equal.
    apply Int64.eqm_samerepr.
    unfold limb64. simpl Z.of_nat.
    unfold Int64.eqm. replace Int64.modulus with (2^64) by reflexivity.
    rewrite !Z.div_small by lia.
    apply Zbits.eqmod_refl.
Qed.

(* ================================================================= *)
(** ** sumadd *)

Lemma body_sumadd:
  semax_body Vprog Gprog f_sumadd sumadd_spec.
Proof.
  start_function.
  (* acc->c0 = acc->c0 + a *)
  forward. forward.
  (* over = (acc->c0 < a) *)
  forward. forward.
  (* acc->c1 = acc->c1 + over *)
  forward. forward.
  (* acc->c2 = acc->c2 + (acc->c1 < over) *)
  forward. forward. forward.

  Exists (mkAcc (acc_val acc + u64_val a)
    ltac:(pose proof (acc_range acc); pose proof (u64_range a); lia)).
  entailer!.

  pose proof (acc_range acc) as Hacc.
  pose proof (u64_range a) as Ha.
  apply derives_refl'.
  f_equal.
  unfold acc_to_val. simpl.
  f_equal; f_equal.

  + (* limb 0: Int64.repr (limb64 acc 0 + u64_val a) = Int64.repr (limb64 (acc+a) 0) *)
    apply Int64.eqm_samerepr.
    unfold Int64.eqm, limb64. simpl Z.of_nat.
    rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r.
    replace Int64.modulus with (2^64) by reflexivity.
    apply Zbits.eqmod_trans with (y := acc_val acc mod 2^64 + u64_val a mod 2^64).
    * unfold Zbits.eqmod. exists 0.
      rewrite Z.mod_small with (a := u64_val a) (b := 2^64) by lia. lia.
    * apply Zbits.eqmod_trans with (y := acc_val acc + u64_val a).
      -- apply Zbits.eqmod_add; apply Zbits.eqmod_sym; apply Zbits.eqmod_mod; lia.
      -- apply Zbits.eqmod_mod. lia.

  + (* limb 1: uses Int.unsigned for carry *)
    f_equal. apply Int64.eqm_samerepr.
    pose proof (limb64_u64_range (acc_val acc) 0) as Hla0.
    rewrite (ltu_carry_b2z (limb64 (acc_val acc) 0) (u64_val a)) by rep_lia.
    assert (Hcu :
      Int.unsigned (Int.repr (if limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus then 0 else 1))
      = (if limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus then 0 else 1))
      by (destruct (limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus); reflexivity).
    rewrite Hcu. replace Int64.modulus with (2^64) by reflexivity.
    apply Zbits.eqmod_trans
      with (y := limb64 (acc_val acc) 1 + (limb64 (u64_val a) 1 +
                 (if limb64 (acc_val acc) 0 + limb64 (u64_val a) 0 <? 2^64 then 0 else 1))).
    * rewrite limb64_u64_val_0, limb64_u64_val_1.
      unfold Zbits.eqmod. exists 0. lia.
    * unfold Int64.eqm. apply limb_add_1; lia.

  + (* limb 2: Int.unsigned for inner carry, Int.signed for outer carry *)
    f_equal. apply Int64.eqm_samerepr.
    pose proof (limb64_u64_range (acc_val acc) 0) as Hla0.
    pose proof (limb64_u64_range (acc_val acc) 1) as Hla1.
    rewrite (ltu_carry_b2z (limb64 (acc_val acc) 0) (u64_val a)) by rep_lia.
    set (carry0 := if limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus then 0 else 1).
    assert (Hc0 : 0 <= carry0 <= 1)
      by (unfold carry0; destruct (limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus); lia).
    assert (Hcu : Int.unsigned (Int.repr carry0) = carry0)
      by (unfold carry0; destruct (limb64 (acc_val acc) 0 + u64_val a <? Int64.modulus); reflexivity).
    rewrite Hcu.
    rewrite (ltu_carry_b2z (limb64 (acc_val acc) 1) carry0) by rep_lia.
    set (carry1 := if limb64 (acc_val acc) 1 + carry0 <? Int64.modulus then 0 else 1).
    assert (Hcs : Int.signed (Int.repr carry1) = carry1)
      by (unfold carry1; destruct (limb64 (acc_val acc) 1 + carry0 <? Int64.modulus); reflexivity).
    rewrite Hcs. replace Int64.modulus with (2^64) by reflexivity.
    subst carry0 carry1.
    apply limb_add_2_u64; lia.
Qed.

(* ================================================================= *)
(** ** sumadd_fast *)

Lemma body_sumadd_fast:
  semax_body Vprog Gprog f_sumadd_fast sumadd_fast_spec.
Proof.
  start_function.
  do 5 forward.
  Exists (mkAcc (acc_val acc + u64_val a) ltac:(pose proof (acc_range acc); pose proof (u64_range a); lia)).
  entailer!.
  apply derives_refl'. f_equal.
  unfold acc_to_val. simpl.
  f_equal; f_equal.
  + (* limb 0: (limb64 acc 0 + u64_val a) mod 2^64 = limb64 (acc + a) 0 *)
    apply Int64.eqm_samerepr.
    unfold Int64.eqm, limb64. simpl Z.of_nat.
    rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r.
    replace Int64.modulus with (2^64) by reflexivity.
    rewrite Z.add_mod by lia.
    rewrite (Z.mod_small (u64_val a)) by (pose proof (u64_range a); lia).
    apply Zbits.eqmod_mod; lia.
  + (* limb 1: c1 + carry = limb64 (acc + a) 1 *)
    f_equal. apply Int64.eqm_samerepr.
    pose proof (acc_range acc) as Hacc.
    pose proof (u64_range a) as Ha.
    pose proof (limb64_u64_range (acc_val acc) 0) as Hc0.
    rewrite Int.signed_repr.
    2: { unfold Z.b2z. destruct (Int64.ltu _ _); simpl; rep_lia. }
    rewrite ltu_carry_b2z by rep_lia.
    replace Int64.modulus with (2^64) by reflexivity.
    apply Int64.eqm_trans with
      (y := limb64 (acc_val acc) 1 +
            (limb64 (u64_val a) 1 +
             (if limb64 (acc_val acc) 0 + limb64 (u64_val a) 0 <? 2^64 then 0 else 1))).
    - rewrite limb64_u64_val_0, limb64_u64_val_1.
      unfold Int64.eqm. apply Zbits.eqmod_refl.
    - apply limb_add_1; lia.
  + (* limb 2: acc + a < 2^128 so both sides are 0 *)
    f_equal. apply Int64.eqm_samerepr.
    unfold limb64. simpl Z.of_nat.
    replace (64 * 2) with 128 by lia.
    unfold Int64.eqm. replace Int64.modulus with (2^64) by reflexivity.
    rewrite !Z.div_small by (pose proof (acc_range acc); pose proof (u64_range a); lia).
    apply Zbits.eqmod_refl.
Qed.

(* ================================================================= *)
(** ** extract *)

Lemma body_extract:
  semax_body Vprog Gprog f_extract extract_spec.
Proof.
  start_function.

  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.

  (* Witnesses: n = acc_lo acc, acc' = acc_shift acc *)
  Exists (acc_lo acc) (acc_shift acc).
  entailer!.

  (* --- Postcondition: C struct = acc_to_val (acc_shift acc) --- *)
  pose proof (acc_range acc) as Hacc.

  apply derives_refl'.
  f_equal.
  unfold acc_to_val.
  (* Normalize acc_val (acc_shift acc) to acc_val acc / 2^64 *)
  replace (acc_val (acc_shift acc)) with (acc_val acc / 2^64)
    by (unfold acc_shift; reflexivity).
  f_equal; f_equal; f_equal. 
  + (* limb 0 of shifted = limb 1 of original *)
    symmetry. apply limb64_shift. lia.
  + (* limb 1 of shifted = limb 2 of original *)
    f_equal. symmetry. apply limb64_shift. lia.
  + (* limb 2 of shifted = 0 *)
    rewrite limb64_shift by lia.
    rewrite (limb64_high_zero (acc_val acc) 2) by lia.
    reflexivity. 
Qed.

(* ================================================================= *)
(** ** extract_fast *)

Lemma body_extract_fast:
  semax_body Vprog Gprog f_extract_fast extract_fast_spec.
Proof.
  start_function.

  forward.
  forward.
  forward.
  forward.
  forward.

  (* Witnesses: n = acc_lo acc, acc' = acc_shift acc *)
  Exists (acc_lo acc) (acc_shift acc).
  entailer!.

  (* --- Postcondition: C struct = acc_to_val (acc_shift acc) --- *)
  pose proof (acc_range acc) as Hacc.

  apply derives_refl'.
  f_equal.
  unfold acc_to_val.
  replace (acc_val (acc_shift acc)) with (acc_val acc / 2^64)
    by (unfold acc_shift; reflexivity).
  simpl snd.
  f_equal; f_equal; f_equal. 
  + (* limb 0 of shifted = limb 1 of original *)
    symmetry. apply limb64_shift. lia.
  + (* limb 1 of shifted = 0 (since acc < 2^128, limb 2 = 0) *)
    rewrite limb64_shift by lia.
    rewrite (limb64_high_zero (acc_val acc) 1) by lia.
    reflexivity.
  + (* limb 2 of shifted = limb 2 of original (both 0) *)
    rewrite limb64_shift by lia.
    rewrite (limb64_high_zero (acc_val acc) 1) by lia.
    rewrite (limb64_high_zero (acc_val acc) 2) by lia.
    reflexivity.
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_from_u64 *)

Lemma u64_lt_u128 (a : UInt64) : 0 <= u64_val a < 2^128.
Proof. destruct a; simpl; lia. Qed.

Lemma u64_uint128_repr (a : UInt64) :
  uint128_to_val (mkUInt128 (u64_val a) (u64_lt_u128 a)) =
  (uint64_to_val a, Vlong (Int64.repr 0)).
Proof.
  unfold uint128_to_val, uint64_to_val, limb64.
  simpl Z.of_nat. simpl Z.mul. simpl u128_val. simpl Z.pow.
  rewrite Z.div_1_r.
  f_equal.
  - f_equal. f_equal. apply Z.mod_small. destruct a; simpl; lia.
  - f_equal. f_equal. rewrite Z.div_small by (destruct a; simpl; lia).
    reflexivity.
Qed.

Lemma body_secp256k1_u128_from_u64:
  semax_body Vprog Gprog
    f_secp256k1_u128_from_u64 secp256k1_u128_from_u64_spec.
Proof.
  start_function.
  forward. (* r->lo = a *)
  forward. (* r->hi = 0 *)
  Exists (mkUInt128 (u64_val a) (u64_lt_u128 a)).
  rewrite u64_uint128_repr.
  entailer!.
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_accum_u64 *)

Lemma accum_u64_result_range (r : UInt128) (a : UInt64) :
  u128_val r + u64_val a < 2^128 ->
  0 <= u128_val r + u64_val a < 2^128.
Proof. pose proof (u128_range r). pose proof (u64_range a). lia. Qed.

Lemma body_secp256k1_u128_accum_u64:
  semax_body Vprog Gprog
    f_secp256k1_u128_accum_u64 secp256k1_u128_accum_u64_spec.
Proof.
  start_function.
  forward. (* t'3 = r->lo *)
  forward. (* r->lo = t'3 + a *)
  forward. (* t'1 = r->hi *)
  forward. (* t'2 = r->lo *)
  forward. (* r->hi = t'1 + (t'2 < a) *)
  Exists (mkUInt128 (u128_val r + u64_val a) (accum_u64_result_range r a H)).
  entailer!.
  (* SEP: match C values with uint128_to_val witness *)
  apply derives_refl'. f_equal.
  unfold uint128_to_val. simpl u128_val. f_equal.
  - (* lo limb *)
    f_equal. apply Int64.eqm_samerepr.
    pose proof (u128_range r). pose proof (u64_range a).
    apply Int64.eqm_trans with (y := limb64 (u128_val r) 0 + limb64 (u64_val a) 0).
    + rewrite limb64_u64_val_0. apply Int64.eqm_refl.
    + apply limb_add_0; lia.
  - (* hi limb *)
    f_equal. apply Int64.eqm_samerepr.
    pose proof (u128_range r) as Hr. pose proof (u64_range a) as Ha.
    rewrite Int.signed_repr by (destruct (Int64.ltu _ _); simpl; rep_lia).
    rewrite ltu_carry_b2z
      by (pose proof (limb64_u64_range (u128_val r) 0); rep_lia).
    replace Int64.modulus with (2^64) by reflexivity.
    apply Int64.eqm_trans with
      (y := limb64 (u128_val r) 1 +
            (limb64 (u64_val a) 1 +
             (if limb64 (u128_val r) 0 + limb64 (u64_val a) 0 <? 2^64 then 0 else 1))).
    + rewrite limb64_u64_val_0, limb64_u64_val_1.
      unfold Int64.eqm. apply Zbits.eqmod_refl.
    + apply limb_add_1; lia.
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_accum_mul *)

Lemma mk_u128_sum (r : UInt128) (a b : UInt64)
  (H : u128_val r + u64_val a * u64_val b < 2^128) :
  { r' : UInt128 | u128_val r' = u128_val r + u64_val a * u64_val b }.
Proof.
  refine (exist _ (mkUInt128 (u128_val r + u64_val a * u64_val b) _) eq_refl).
  pose proof (u128_range r). pose proof (u64_range a). pose proof (u64_range b). lia.
Defined.

Lemma body_secp256k1_u128_accum_mul:
  semax_body Vprog Gprog
    f_secp256k1_u128_accum_mul secp256k1_u128_accum_mul_spec.
Proof.
  start_function.

  (* secp256k1_u128_mul(&t, a, b) *)
  forward_call.
  Intros vret. subst vret.

  (* r->lo += t.lo *)
  forward. forward. forward.

  (* r->hi += t.hi + (r->lo < t.lo) *)
  forward. forward. forward. forward.
  forward.

  (* Provide witness *)
  set (prod := u64_val a * u64_val b).
  set (rv := u128_val r).
  destruct (mk_u128_sum r a b H) as [r' Hr'].
  Exists r'.
  entailer!.

  (* Prove SEP: data_at values match *)
  apply derives_refl'.
  f_equal.
  unfold uint128_to_val.
  rewrite Hr'. fold rv. fold prod.
  f_equal; f_equal.
  + (* limb 0 *)
    apply Int64.eqm_samerepr.
    apply limb_add_0.
    all: subst rv prod;
      try (destruct r; simpl; lia);
      apply Z.mul_nonneg_nonneg; destruct a, b; simpl; lia.
  + (* limb 1 *)
    apply Int64.eqm_samerepr.
    apply muladd_limb1.
    all: subst rv prod;
      try (destruct r; simpl; lia);
      apply Z.mul_nonneg_nonneg; destruct a, b; simpl; lia.
Qed.

(* ================================================================= *)
(** ** secp256k1_u128_rshift *)

Lemma u128_rshift64_range (r : UInt128) :
  0 <= u128_val r / 2^64 < 2^128.
Proof.
  destruct r as [v [H0 H1]]; simpl.
  split.
  - apply Z.div_pos; lia.
  - apply Z.lt_trans with (2^64).
    + apply Z.div_lt_upper_bound; lia.
    + lia.
Qed.

Lemma u128_rshift64_repr (r : UInt128) :
  uint128_to_val (mkUInt128 (u128_val r / 2^64) (u128_rshift64_range r)) =
  (Vlong (Int64.repr (limb64 (u128_val r) 1)), Vlong (Int64.repr 0)).
Proof.
  destruct r as [v [H0 H1]].
  unfold uint128_to_val, limb64.
  simpl Z.of_nat. simpl Z.mul. simpl u128_val.
  change (Z.pow_pos 2 64) with (2^64).
  change (let (q, _) := Z.div_eucl v (2^64) in q) with (v / 2^64).
  rewrite Z.div_1_r.
  f_equal. f_equal. f_equal.
  rewrite Z.div_small by
    (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  reflexivity.
Qed.

Lemma body_secp256k1_u128_rshift:
  semax_body Vprog Gprog
    f_secp256k1_u128_rshift secp256k1_u128_rshift_spec.
Proof.
  start_function.
  forward. (* _t'1 = r->hi *)
  forward. (* r->lo = _t'1 *)
  forward. (* r->hi = 0 *)
  rewrite Int.signed_repr by rep_lia.
  Exists (mkUInt128 (u128_val r / 2^64) (u128_rshift64_range r)).
  rewrite u128_rshift64_repr.
  entailer!.
Qed.

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
  (* Step through all 14 C statements + the return *)
  do 15 forward.
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
    unfold eval4, u256_limb in Heval. simpl u64_val in Heval.
    change ((2^64)^2) with (2^128) in Heval.
    change ((2^64)^3) with (2^192) in Heval. lia. }

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
  all: simpl Z.b2z; simpl Z.lor;
       rewrite ?Int.or_zero_l, ?Int.or_zero, ?Int.and_zero_l, ?Int.and_zero;
       destruct (Z_lt_dec (u256_val a) secp256k1_N);
       try reflexivity;
       try discriminate.

  (* Remaining goals: False from a contradictory combination of limb
     comparisons and Z_lt_dec.  Unfold N constants and close with lia. *)
  all: exfalso; unfold secp256k1_N, N_0, N_1, N_2, N_3 in *; lia.
Qed.

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
  intros. split.
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
  rename H0 into Hresult_range.  (* 0 <= r + overflow*(2^256-N) < 2^256 *)

  (* --- Setup: name the four 64-bit limbs of r --- *)
  set (d0 := limb64 (u256_val r) 0).
  set (d1 := limb64 (u256_val r) 1).
  set (d2 := limb64 (u256_val r) 2).
  set (d3 := limb64 (u256_val r) 3).
  assert (Hd0 : 0 <= d0 < 2^64) by (subst d0; apply Z.mod_pos_bound; lia).
  assert (Hd1 : 0 <= d1 < 2^64) by (subst d1; apply Z.mod_pos_bound; lia).
  assert (Hd2 : 0 <= d2 < 2^64) by (subst d2; apply Z.mod_pos_bound; lia).
  assert (Hd3 : 0 <= d3 < 2^64) by (subst d3; apply Z.mod_pos_bound; lia).

  assert (Hov0 : 0 <= overflow * N_C_0 < 2^64) by (unfold N_C_0; lia).
  assert (Hov1 : 0 <= overflow * N_C_1 < 2^64) by (unfold N_C_1; lia).
  assert (Hov2 : 0 <= overflow * N_C_2 < 2^64) by (unfold N_C_2; lia).

  (* ===== Round 0: t = d[0] + overflow*N_C_0 ===== *)

  (* _t'8 = r->d[0] *)
  forward.

  (* secp256k1_u128_from_u64(&t, r->d[0]) *)
  forward_call (v_t, mkUInt64 d0 Hd0, Tsh).
  Intros t_init.
  rename H into Ht_init.

  (* secp256k1_u128_accum_u64(&t, (uint64_t)overflow * N_C_0) *)
  forward_call (v_t, t_init, mkUInt64 (overflow * N_C_0) Hov0, Tsh).
  { solve_reduce_expr_match. }
  { simpl u64_val. rewrite Ht_init. simpl. lia. }

  Intros acc0.
  rename H into Hacc0_raw.
  assert (Hacc0 : u128_val acc0 = d0 + overflow * N_C_0)
    by (rewrite Hacc0_raw, Ht_init; simpl; lia).
  clear Ht_init Hacc0_raw t_init.

  (* r->d[0] = secp256k1_u128_to_u64(&t) *)
  forward_call (v_t, acc0, Tsh).
  Intros lo0.
  rename H into Hlo0.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call (v_t, acc0, 64, Tsh).
  Intros carry0.
  rename H into Hcarry0.
  deadvars!.

  assert (Hcarry0_val : u128_val carry0 = (d0 + overflow * N_C_0) / 2^64)
    by (rewrite Hcarry0, Hacc0; reflexivity).
  clear Hcarry0.

  (* ===== Round 1: t += d[1] + overflow*N_C_1 ===== *)

  (* _t'7 = r->d[1] *)
  forward.

  (* secp256k1_u128_accum_u64(&t, r->d[1]) *)
  forward_call (v_t, carry0, mkUInt64 d1 Hd1, Tsh).
  { rewrite Hcarry0_val. reduce_u128_bound. }

  Intros t1a.
  rename H into Ht1a.

  (* secp256k1_u128_accum_u64(&t, (uint64_t)overflow * ~N_1) *)
  forward_call (v_t, t1a, mkUInt64 (overflow * N_C_1) Hov1, Tsh).
  { solve_reduce_expr_match. }
  { rewrite Ht1a. simpl u64_val. rewrite Hcarry0_val. reduce_u128_bound. }

  Intros acc1.
  rename H into Hacc1_raw.
  assert (Hacc1 : u128_val acc1 =
    (d0 + overflow * N_C_0) / 2^64 + d1 + overflow * N_C_1)
    by (rewrite Hacc1_raw, Ht1a; simpl u64_val; rewrite Hcarry0_val; lia).
  clear Ht1a Hacc1_raw Hcarry0_val carry0 t1a.

  (* r->d[1] = secp256k1_u128_to_u64(&t) *)
  forward_call (v_t, acc1, Tsh).
  Intros lo1.
  rename H into Hlo1.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call (v_t, acc1, 64, Tsh).
  Intros carry1.
  rename H into Hcarry1.
  deadvars!.

  assert (Hcarry1_val : u128_val carry1 = u128_val acc1 / 2^64)
    by exact Hcarry1.
  clear Hcarry1.

  (* ===== Round 2: t += d[2] + overflow*N_C_2 ===== *)

  (* _t'6 = r->d[2] *)
  forward.

  (* secp256k1_u128_accum_u64(&t, r->d[2]) *)
  forward_call (v_t, carry1, mkUInt64 d2 Hd2, Tsh).
  { rewrite Hcarry1_val, Hacc1. reduce_u128_bound. }

  Intros t2a.
  rename H into Ht2a.

  (* secp256k1_u128_accum_u64(&t, (uint64_t)overflow * N_C_2) *)
  forward_call (v_t, t2a, mkUInt64 (overflow * N_C_2) Hov2, Tsh).
  { solve_reduce_expr_match. }
  { rewrite Ht2a. simpl u64_val. rewrite Hcarry1_val, Hacc1. reduce_u128_bound. }

  Intros acc2.
  rename H into Hacc2_raw.
  assert (Hacc2 : u128_val acc2 =
    ((d0 + overflow * N_C_0) / 2^64 + d1 + overflow * N_C_1) / 2^64
    + d2 + overflow * N_C_2)
    by (rewrite Hacc2_raw, Ht2a; simpl u64_val; rewrite Hcarry1_val, Hacc1; lia).
  clear Ht2a Hacc2_raw Hcarry1_val carry1 t2a.

  (* r->d[2] = secp256k1_u128_to_u64(&t) *)
  forward_call (v_t, acc2, Tsh).
  Intros lo2.
  rename H into Hlo2.
  forward.

  (* secp256k1_u128_rshift(&t, 64) *)
  forward_call (v_t, acc2, 64, Tsh).
  Intros carry2.
  rename H into Hcarry2.
  deadvars!.

  assert (Hcarry2_val : u128_val carry2 = u128_val acc2 / 2^64)
    by exact Hcarry2.
  clear Hcarry2.

  (* ===== Round 3: t += d[3] (no complement term) ===== *)

  (* _t'5 = r->d[3] *)
  forward.

  (* secp256k1_u128_accum_u64(&t, r->d[3]) *)
  forward_call (v_t, carry2, mkUInt64 d3 Hd3, Tsh).
  { rewrite Hcarry2_val, Hacc2. reduce_u128_bound. }

  Intros acc3.
  rename H into Hacc3_raw.
  assert (Hacc3 : u128_val acc3 =
    (((d0 + overflow * N_C_0) / 2^64 + d1 + overflow * N_C_1) / 2^64
     + d2 + overflow * N_C_2) / 2^64 + d3)
    by (rewrite Hacc3_raw; simpl u64_val; rewrite Hcarry2_val, Hacc2; lia).
  clear Hacc3_raw Hcarry2_val carry2.

  (* r->d[3] = secp256k1_u128_to_u64(&t) *)
  forward_call (v_t, acc3, Tsh).
  Intros lo3.
  rename H into Hlo3.
  forward.

  (* return overflow *)
  forward.

  (* Clean up before postcondition *)
  clear Hov0 Hov1 Hov2.

  (* ================================================================= *)
  (** *** Postcondition *)

  set (result_val := u256_val r + overflow * (2^256 - secp256k1_N)).
  assert (Hresult_range' : 0 <= result_val < 2^256)
    by (subst result_val; exact Hresult_range).

  Exists (mkUInt256 result_val Hresult_range').
  entailer!.

  (* ---- VST cleanup ---- *)

  (* Goal: upd_Znth chain |-- uint256_to_val result *)
  apply derives_refl'. f_equal.

  (* Collapse the [upd_Znth] chain to a plain 4-element list *)
  transitivity [uint64_to_val (u128_lo acc0);
                uint64_to_val (u128_lo acc1);
                uint64_to_val (u128_lo acc2);
                uint64_to_val (u128_lo acc3)].
  { unfold uint256_to_val. simpl u256_val. reflexivity. }

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
  { intros [-> [-> [-> ->]]]. reflexivity. }

  clear - r overflow Hov_range Hresult_range
          d0 d1 d2 d3 Hd0 Hd1 Hd2 Hd3
          t0 t1 t2 t3 result_val Hresult_range'.

  (* Bridge limb64 ↔ limb: (x / 2^(64*i)) mod 2^64 = (x / (2^64)^i) mod 2^64 *)
  unfold limb64; rewrite !Z.pow_mul_r by lia.

  (* ---- Pure Z ---- *)

  (* Decompose u256_val r into limbs *)
  assert (Hdecomp : u256_val r = d0 + d1 * 2^64 + d2 * 2^128 + d3 * 2^192).
  { subst d0 d1 d2 d3.
    pose proof (u256_as_eval4 r) as Heval.
    unfold eval4, u256_limb in Heval. simpl u64_val in Heval.
    change ((2^64)^2) with (2^128) in Heval.
    change ((2^64)^3) with (2^192) in Heval.
    lia. }

  (* Work with B = 2^64 *)
  set (B := 2^64) in *.

  (* Apply the carry-chain identity *)
  pose proof (reduce_carry_chain B d0 d1 d2 d3 N_C_0 N_C_1 N_C_2 overflow
    ltac:(subst B; lia) Hd0 Hd1 Hd2 Hd3
    ltac:(unfold N_C_0; lia) ltac:(unfold N_C_1; lia) ltac:(unfold N_C_2; lia)
    ltac:(lia)) as Hchain.
  cbv zeta in Hchain.
  fold t0 t1 t2 t3 in Hchain.

  assert (HdecompB : u256_val r = d0 + d1 * B + d2 * (B*B) + d3 * (B*B*B))
    by (subst B; lia).
  rewrite <- HdecompB in Hchain.
  set (C := N_C_0 + N_C_1 * B + N_C_2 * (B * B)) in *.
  specialize (Hchain ltac:(subst B C; exact Hresult_range)).

  (* Connect result_val to the chain *)
  assert (Hresult_eq : result_val = u256_val r + overflow * C)
    by (subst result_val C B; rewrite secp256k1_N_C_limbs; ring).
  rewrite Hresult_eq. clear Hresult_eq result_val Hresult_range'.

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
  rewrite Hchain in Hl0, Hl1, Hl2, Hl3.
  clear - Hl0 Hl1 Hl2 Hl3.

  exact (conj (eq_sym Hl0) (conj (eq_sym Hl1) (conj (eq_sym Hl2) (eq_sym Hl3)))).
Qed.

(* ================================================================= *)
(** ** secp256k1_scalar_reduce_512 *)

Lemma body_secp256k1_scalar_reduce_512:
  semax_body Vprog Gprog
    f_secp256k1_scalar_reduce_512 secp256k1_scalar_reduce_512_spec.
Proof. Admitted.

(* ================================================================= *)
(** ** secp256k1_scalar_mul_512 *)

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
  do 3 forward.

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

  (* Range facts for all limbs — used throughout the proof *)
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

  (* ===== Round 0: l8[0] = a0*b0 (1 product, uses muladd_fast + extract_fast) ===== *)

  (* a0 = a->d[0], b0 = b->d[0] *)
  forward.
  forward.

  (* muladd_fast(&acc, a0, b0) *)
  forward_call (v_acc, acc_init, a0, b0, Tsh).
  { (* overflow: 0 + a0*b0 < 2^128 *)
    apply mul_u64_lt_u128; lia. }

  (* Intro the accumulator after muladd_fast *)
  Intros acc0.
  rename H into Hacc0_post. (* acc_val acc0 = acc_val acc_init + a0*b0 *)

  (* Track acc_val through round 0 *)
  assert (Hacc0 : acc_val acc0 = u64_val a0 * u64_val b0).
  { unfold acc_init in *. simpl in *. lia. }
  clear Hacc0_post.

  (* extract_fast(&acc, &l8[0]) — precondition: acc < 2^128 *)
  forward_call (v_acc, acc0,
                field_address (tarray tulong 8) [ArraySubsc 0] l8_ptr,
                Tsh, sh_l).
  { (* parameter matching *)
    entailer!.
    simpl firstn.
    f_equal; f_equal.
    rewrite field_address_offset by auto with field_compatible.
    simpl nested_field_offset.
    rewrite isptr_offset_val_zero; auto. }
  { (* frame: split l8[0] out of the 8-element array *)
    rewrite (arr_field_address tulong 8 l8_ptr 0 Hfc) by lia.
    simpl Z.mul.
    rewrite isptr_offset_val_zero by (eapply field_compatible_isptr; eauto).
    rewrite (split2_data_at__Tarray_app 1 8 sh_l tulong l8_ptr) by lia.
    rewrite data__at_singleton_array_eq.
    cancel. }

  (* Intro extracted limb and shifted accumulator *)
  Intros vret.
  rename H into Hr0_eq.     (* r0 = acc_lo acc0 *)
  rename H0 into Hcarry0_eq.  (* acc_val carry0 = acc_val acc0 / 2^64 *)
  destruct vret as [r0 carry0].
  simpl fst in *. 
  simpl snd in *. 
  deadvars!.

  (* Carry bound: acc_val carry0 <= 2^64 - 2 *)
  assert (Hcarry0_ub : acc_val carry0 <= 2^64 - 2).
  { rewrite Hcarry0_eq, Hacc0.
    apply (Z.le_trans _ (((2^64 - 1) * (2^64 - 1)) / 2^64)).
    - apply Z.div_le_mono; lia.
    - reflexivity. }

  (* ===== Round 1: l8[1] = a0*b1 + a1*b0 (2 products, uses muladd + extract) ===== *)

  (* a0 = a->d[0], b1 = b->d[1] *)
  forward.
  forward.

  (* muladd(&acc, a0, b1) *)
  forward_call (v_acc, carry0, a0, b1, Tsh).

  Intros acc1a.
  rename H into Hacc1a_eq.
  deadvars!.

  (* a1 = a->d[1], b0 = b->d[0] *)
  forward.
  forward.

  (* muladd(&acc, a1, b0) *)
  forward_call (v_acc, acc1a, a1, b0, Tsh).

  Intros acc1.
  rename H into Hacc1_eq.
  deadvars!.

  (* Full chain for round 1 *)
  assert (Hacc1 : acc_val acc1 =
    acc_val carry0 + u64_val a0 * u64_val b1 + u64_val a1 * u64_val b0).
  { rewrite Hacc1_eq, Hacc1a_eq. reflexivity. }

  (* extract(&acc, &l8[1]) *)
  forward_call (v_acc, acc1,
                field_address (tarray tulong 8) [ArraySubsc 1] l8_ptr,
                Tsh, sh_l).
  { (* frame: extract l8[1] from the 7-element sub-array *)
    sep_apply (peel_array_slot sh_l l8_ptr 1 Hfc ltac:(lia) ltac:(lia)).
    cancel. }

  (* Intro extracted limb and shifted accumulator for round 1 *)
  Intros vret1.
  rename H into Hr1_eq.
  rename H0 into Hcarry1_eq.
  destruct vret1 as [r1 carry1].
  simpl fst in *. 
  simpl snd in *.

  (* Carry bound: acc_val carry1 <= 2 * 2^64 - 3 *)
  assert (Hcarry1_ub : acc_val carry1 <= 2 * 2^64 - 3).
  { rewrite Hcarry1_eq, Hacc1.
    apply (Z.le_trans _ (((2^64 - 2) + 2 * ((2^64 - 1) * (2^64 - 1))) / 2^64)).
    - apply Z.div_le_mono; lia.
    - reflexivity. }

  (* ===== Round 2: l8[2] = a0*b2 + a1*b1 + a2*b0 (3 products) ===== *)

  (* a0 = a->d[0], b2 = b->d[2] *)
  forward.
  forward.

  (* muladd(&acc, a0, b2) *)
  forward_call (v_acc, carry1, a0, b2, Tsh).

  Intros acc2a.
  rename H into Hacc2a_eq.
  deadvars!.

  (* a1 = a->d[1], b1 = b->d[1] *)
  forward.
  forward.

  (* muladd(&acc, a1, b1) *)
  forward_call (v_acc, acc2a, a1, b1, Tsh).

  Intros acc2b.
  rename H into Hacc2b_eq.
  deadvars!.

  (* a2 = a->d[2], b0 = b->d[0] *)
  forward.
  forward.

  (* muladd(&acc, a2, b0) *)
  forward_call (v_acc, acc2b, a2, b0, Tsh).

  Intros acc2.
  rename H into Hacc2_eq.
  deadvars!.

  (* Full chain for round 2 *)
  assert (Hacc2 : acc_val acc2 =
    acc_val carry1 + u64_val a0 * u64_val b2 + u64_val a1 * u64_val b1 + u64_val a2 * u64_val b0).
  { rewrite Hacc2_eq, Hacc2b_eq, Hacc2a_eq. lia. }

  (* extract(&acc, &l8[2]) *)
  forward_call (v_acc, acc2,
                field_address (tarray tulong 8) [ArraySubsc 2] l8_ptr,
                Tsh, sh_l).
  { (* frame: peel l8[2] out of the 6-element sub-array *)
    sep_apply (peel_array_slot sh_l l8_ptr 2 Hfc ltac:(lia) ltac:(lia)).
    cancel. }

  (* Intro extracted limb and shifted accumulator for round 2 *)
  Intros vret2.
  rename H into Hr2_eq.
  rename H0 into Hcarry2_eq.
  destruct vret2 as [r2 carry2].
  simpl fst in *.
  simpl snd in *.

  (* Carry bound: acc_val carry2 <= 3 * 2^64 - 4 *)
  assert (Hcarry2_ub : acc_val carry2 <= 3 * 2^64 - 4).
  { rewrite Hcarry2_eq, Hacc2.
    apply (Z.le_trans _ (((2 * 2^64 - 3) + 3 * ((2^64 - 1) * (2^64 - 1))) / 2^64)).
    - apply Z.div_le_mono; lia.
    - reflexivity. }

  (* ===== Round 3: l8[3] = a0*b3 + a1*b2 + a2*b1 + a3*b0 (4 products) ===== *)

  (* a0 = a->d[0], b3 = b->d[3] *)
  forward.
  forward.

  (* muladd(&acc, a0, b3) *)
  forward_call (v_acc, carry2, a0, b3, Tsh).

  Intros acc3a.
  rename H into Hacc3a_eq.
  deadvars!.

  (* a1 = a->d[1], b2 = b->d[2] *)
  forward.
  forward.

  (* muladd(&acc, a1, b2) *)
  forward_call (v_acc, acc3a, a1, b2, Tsh).

  Intros acc3b.
  rename H into Hacc3b_eq.
  deadvars!.

  (* a2 = a->d[2], b1 = b->d[1] *)
  forward.
  forward.

  (* muladd(&acc, a2, b1) *)
  forward_call (v_acc, acc3b, a2, b1, Tsh).

  Intros acc3c.
  rename H into Hacc3c_eq.
  deadvars!.

  (* a3 = a->d[3], b0 = b->d[0] *)
  forward.
  forward.

  (* muladd(&acc, a3, b0) *)
  forward_call (v_acc, acc3c, a3, b0, Tsh).

  Intros acc3.
  rename H into Hacc3_eq.
  deadvars!.

  (* Full chain for round 3 *)
  assert (Hacc3 : acc_val acc3 =
    acc_val carry2 + u64_val a0 * u64_val b3 + u64_val a1 * u64_val b2
    + u64_val a2 * u64_val b1 + u64_val a3 * u64_val b0).
  { rewrite Hacc3_eq, Hacc3c_eq, Hacc3b_eq, Hacc3a_eq. lia. }

  (* extract(&acc, &l8[3]) *)
  forward_call (v_acc, acc3,
                field_address (tarray tulong 8) [ArraySubsc 3] l8_ptr,
                Tsh, sh_l).
  { (* frame: peel l8[3] out of the 5-element sub-array *)
    sep_apply (peel_array_slot sh_l l8_ptr 3 Hfc ltac:(lia) ltac:(lia)).
    cancel. }

  (* Intro extracted limb and shifted accumulator for round 3 *)
  Intros vret3.
  rename H into Hr3_eq.
  rename H0 into Hcarry3_eq.
  destruct vret3 as [r3 carry3].
  simpl fst in *.
  simpl snd in *.

  (* Carry bound: acc_val carry3 <= 4 * 2^64 - 5 *)
  assert (Hcarry3_ub : acc_val carry3 <= 4 * 2^64 - 5).
  { rewrite Hcarry3_eq, Hacc3.
    apply (Z.le_trans _ (((3 * 2^64 - 4) + 4 * ((2^64 - 1) * (2^64 - 1))) / 2^64)).
    - apply Z.div_le_mono; lia.
    - reflexivity. }

  (* ===== Round 4: l8[4] = a1*b3 + a2*b2 + a3*b1 (3 products) ===== *)

  (* a1 = a->d[1], b3 = b->d[3] *)
  forward.
  forward.

  (* muladd(&acc, a1, b3) *)
  forward_call (v_acc, carry3, a1, b3, Tsh).

  Intros acc4a.
  rename H into Hacc4a_eq.
  deadvars!.

  (* a2 = a->d[2], b2 = b->d[2] *)
  forward.
  forward.

  (* muladd(&acc, a2, b2) *)
  forward_call (v_acc, acc4a, a2, b2, Tsh).

  Intros acc4b.
  rename H into Hacc4b_eq.
  deadvars!.

  (* a3 = a->d[3], b1 = b->d[1] *)
  forward.
  forward.

  (* muladd(&acc, a3, b1) *)
  forward_call (v_acc, acc4b, a3, b1, Tsh).

  Intros acc4.
  rename H into Hacc4_eq.
  deadvars!.

  (* Full chain for round 4 *)
  assert (Hacc4 : acc_val acc4 =
    acc_val carry3 + u64_val a1 * u64_val b3 + u64_val a2 * u64_val b2
    + u64_val a3 * u64_val b1).
  { rewrite Hacc4_eq, Hacc4b_eq, Hacc4a_eq. lia. }

  (* extract(&acc, &l8[4]) *)
  forward_call (v_acc, acc4,
                field_address (tarray tulong 8) [ArraySubsc 4] l8_ptr,
                Tsh, sh_l).
  { (* frame: peel l8[4] out of the 4-element sub-array *)
    sep_apply (peel_array_slot sh_l l8_ptr 4 Hfc ltac:(lia) ltac:(lia)).
    cancel. }

  (* Intro extracted limb and shifted accumulator for round 4 *)
  Intros vret4.
  rename H into Hr4_eq.
  rename H0 into Hcarry4_eq.
  destruct vret4 as [r4 carry4].
  simpl fst in *.
  simpl snd in *.

  (* Carry bound: acc_val carry4 <= 3 * 2^64 - 3 *)
  assert (Hcarry4_ub : acc_val carry4 <= 3 * 2^64 - 3).
  { rewrite Hcarry4_eq, Hacc4.
    apply (Z.le_trans _ (((4 * 2^64 - 5) + 3 * ((2^64 - 1) * (2^64 - 1))) / 2^64)).
    - apply Z.div_le_mono; lia.
    - reflexivity. }

  (* ===== Round 5: l8[5] = a2*b3 + a3*b2 (2 products) ===== *)

  (* a2 = a->d[2], b3 = b->d[3] *)
  forward.
  forward.

  (* muladd(&acc, a2, b3) *)
  forward_call (v_acc, carry4, a2, b3, Tsh).

  Intros acc5a.
  rename H into Hacc5a_eq.
  deadvars!.

  (* a3 = a->d[3], b2 = b->d[2] *)
  forward.
  forward.

  (* muladd(&acc, a3, b2) *)
  forward_call (v_acc, acc5a, a3, b2, Tsh).

  Intros acc5.
  rename H into Hacc5_eq.
  deadvars!.

  (* Full chain for round 5 *)
  assert (Hacc5 : acc_val acc5 =
    acc_val carry4 + u64_val a2 * u64_val b3 + u64_val a3 * u64_val b2).
  { rewrite Hacc5_eq, Hacc5a_eq. lia. }

  (* extract(&acc, &l8[5]) *)
  forward_call (v_acc, acc5,
                field_address (tarray tulong 8) [ArraySubsc 5] l8_ptr,
                Tsh, sh_l).
  { (* frame: peel l8[5] out of the 3-element sub-array *)
    sep_apply (peel_array_slot sh_l l8_ptr 5 Hfc ltac:(lia) ltac:(lia)).
    cancel. }

  (* Intro extracted limb and shifted accumulator for round 5 *)
  Intros vret5.
  rename H into Hr5_eq.
  rename H0 into Hcarry5_eq.
  destruct vret5 as [r5 carry5].
  simpl fst in *.
  simpl snd in *.

  (* Carry bound: acc_val carry5 <= 2 * 2^64 - 2 *)
  assert (Hcarry5_ub : acc_val carry5 <= 2 * 2^64 - 2).
  { rewrite Hcarry5_eq, Hacc5.
    apply (Z.le_trans _ (((3 * 2^64 - 3) + 2 * ((2^64 - 1) * (2^64 - 1))) / 2^64)).
    - apply Z.div_le_mono; lia.
    - reflexivity. }

  (* ===== Round 6: l8[6],l8[7] = a3*b3 (1 product, uses muladd_fast + extract_fast + store) ===== *)

  (* a3 = a->d[3], b3 = b->d[3] *)
  forward.
  forward.

  (* muladd_fast(&acc, a3, b3) — precondition: acc + a3*b3 < 2^128 *)
  forward_call (v_acc, carry5, a3, b3, Tsh).

  Intros acc6.
  rename H into Hacc6_eq.
  deadvars!.

  (* Full chain for round 6 *)
  assert (Hacc6 : acc_val acc6 = acc_val carry5 + u64_val a3 * u64_val b3).
  { exact Hacc6_eq. }

  (* extract_fast(&acc, &l8[6]) — precondition: acc < 2^128 *)
  forward_call (v_acc, acc6,
                field_address (tarray tulong 8) [ArraySubsc 6] l8_ptr,
                Tsh, sh_l).
  { (* frame: peel l8[6] out of the 2-element sub-array *)
    sep_apply (peel_array_slot sh_l l8_ptr 6 Hfc ltac:(lia) ltac:(lia)).
    cancel. }

  (* Intro extracted limb and shifted accumulator for round 6 *)
  Intros vret6.
  rename H into Hr6_eq.
  rename H0 into Hcarry6_eq.
  destruct vret6 as [r6 carry6].
  simpl fst in *.
  simpl snd in *.

  (* l8[7] = acc.c0: first read acc.c0 into temp *)
  forward.
  (* Now store to l8[7] *)
  change (8 - 6 - 1) with 1.
  change (6 + 1) with 7.
  rewrite data__at_singleton_array_eq.
  rewrite (arr_field_address0 tulong 8 l8_ptr 7 Hfc) by lia.
  rewrite <- (arr_field_address tulong 8 l8_ptr 7 Hfc) by lia.
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

  (* Remove all VST/pointer/bounds context — keep only pure Z facts *)
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
  unfold uint512_to_val, uint64_to_val;
  change (map (fun z => Vlong (Int64.repr z))
    [u64_val (acc_lo acc0); u64_val (acc_lo acc1);
     u64_val (acc_lo acc2); u64_val (acc_lo acc3);
     u64_val (acc_lo acc4); u64_val (acc_lo acc5);
     u64_val (acc_lo acc6); u64_val (acc_lo carry6)] =
   map (fun z => Vlong (Int64.repr z))
    [limb64 (u512_val (mul_256 a b)) 0; limb64 (u512_val (mul_256 a b)) 1;
     limb64 (u512_val (mul_256 a b)) 2; limb64 (u512_val (mul_256 a b)) 3;
     limb64 (u512_val (mul_256 a b)) 4; limb64 (u512_val (mul_256 a b)) 5;
     limb64 (u512_val (mul_256 a b)) 6; limb64 (u512_val (mul_256 a b)) 7]);
  f_equal.

  (* Unfold record wrappers to pure Z mod/div *)
  unfold acc_lo; simpl u64_val.
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
  unfold mul_256; simpl u512_val.
  destruct Hschoolbook as (-> & -> & -> & -> & -> & -> & -> & ->).
  subst B.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** secp256k1_scalar_mul *)

Lemma body_secp256k1_scalar_mul:
  semax_body Vprog Gprog
    f_secp256k1_scalar_mul secp256k1_scalar_mul_spec.
Proof.
  start_function.

  (* Rewrite scalar representation to uint256 for mul_512 call *)
  rewrite !scalar_to_val_eq.
  change t_secp256k1_scalar with t_secp256k1_uint256.

  (* secp256k1_scalar_mul_512(l, a, b) *)
  forward_call (v_l, a_ptr, b_ptr,
    scalar_to_u256 a, scalar_to_u256 b,
    Tsh, sh_a, sh_b).

  Intros l.

  (* secp256k1_scalar_reduce_512(r, l) *)
  forward_call (r_ptr, v_l, l, sh_r, Tsh).

  Intros r.

  (* Postcondition *)
  Exists r.
  entailer!.
  - (* r = scalar_mul a b *)
    destruct r as [rv Hr].
    destruct a as [av Ha].
    destruct b as [bv Hb].
    unfold scalar_mul, scalar_to_u256, mul_256 in *.
    simpl in *.
    subst. 
    f_equal.
    apply proof_irr.
  - (* Rewrite uint256 back to scalar representation *)
    rewrite <- !scalar_to_val_eq.
    change t_secp256k1_uint256 with t_secp256k1_scalar.
    cancel.
Qed.