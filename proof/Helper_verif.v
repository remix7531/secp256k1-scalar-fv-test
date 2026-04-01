(** * Helper_verif: Shared verification helper lemmas *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Export scalar_4x64.Verif_imports.
Require Export scalar_4x64.Spec_scalar_4x64.
Require Export scalar_4x64.Impl_scalar_4x64.
Require Export scalar_4x64.Helper_array_fold.
Require Export scalar_4x64.Helper_arithmetic.

(* ================================================================= *)
(** ** rep_lia hints for secp256k1 constants

    Registering the N and N_C limb values with the [rep_lia] hint
    database lets [rep_lia] expand these constants automatically,
    replacing manual [unfold N_C_0; lia] patterns. *)

Lemma N_C_0_eq : N_C_0 = 4624529908474429119. Proof. reflexivity. Qed.
Lemma N_C_1_eq : N_C_1 = 4994812053365940164. Proof. reflexivity. Qed.
Lemma N_C_2_eq : N_C_2 = 1. Proof. reflexivity. Qed.
#[export] Hint Rewrite N_C_0_eq N_C_1_eq N_C_2_eq : rep_lia.

(** Reduction rules for record projections.
    These let [rep_lia] and VST's internal solvers see through
    [mkUInt64]/[mkAcc] wrappers without manual [simpl]. *)
Lemma u64_val_mk : forall z H, u64_val (mkUInt64 z H) = z.
Proof. reflexivity. Qed.
Lemma acc_val_mk : forall z H, acc_val (mkAcc z H) = z.
Proof. reflexivity. Qed.
#[export] Hint Rewrite u64_val_mk acc_val_mk : rep_lia.

(* ================================================================= *)
(** ** Inhabitant instances (needed by deadvars!) *)

#[export] Instance Inhabitant_UInt64_ : Inhabitant UInt64 := mkUInt64 0 ltac:(lia).
#[export] Instance Inhabitant_UInt128_ : Inhabitant UInt128 := mkUInt128 0 ltac:(lia).
#[export] Instance Inhabitant_Acc_ : Inhabitant Acc := mkAcc 0 ltac:(lia).
#[export] Instance Inhabitant_UInt256_ : Inhabitant UInt256 := mkUInt256 0 ltac:(lia).
#[export] Instance Inhabitant_UInt512_ : Inhabitant UInt512 := mkUInt512 0 ltac:(lia).
#[export] Instance Inhabitant_Scalar_ : Inhabitant Scalar :=
  mkScalar 0 ltac:(unfold secp256k1_N; lia).

(* ----------------------------------------------------------------- *)
(** *** limb64 properties *)

(** [limb64 x i] is in unsigned 64-bit range. *)
Lemma limb64_u64_range : forall x i,
  0 <= limb64 x i <= Int64.max_unsigned.
Proof.
  intros.
  unfold limb64.
  pose proof (Z.mod_pos_bound (x / 2^(64 * Z.of_nat i)) (2^64) ltac:(lia)).
  rep_lia.
Qed.

(** For a value in [0, 2^64), limb 0 is the value itself. *)
Lemma limb64_u64_val_0 : forall (a : UInt64), limb64 (u64_val a) 0 = u64_val a.
Proof.
  intros.
  unfold limb64.
  simpl Z.of_nat.
  rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
  apply Z.mod_small.
  pose proof (u64_range a).
  lia.
Qed.

(** For a value in [0, 2^64), limb 1 is 0. *)
Lemma limb64_u64_val_1 : forall (a : UInt64), limb64 (u64_val a) 1 = 0.
Proof.
  intros.
  unfold limb64.
  simpl Z.of_nat.
  rewrite Z.mul_1_r.
  rewrite Z.div_small by (pose proof (u64_range a); lia).
  reflexivity.
Qed.

(** Shifting by 64 bits advances the limb index:
    [limb64 (x / 2^64) i = limb64 x (S i)]. *)
Lemma limb64_shift : forall x i,
  0 <= x ->
  limb64 (x / 2^64) i = limb64 x (S i).
Proof.
  intros.
  unfold limb64.
  simpl Z.of_nat.
  rewrite Zdiv.Zdiv_Zdiv by lia.
  rewrite <- Z.pow_add_r by lia.
  do 3 f_equal.
  lia.
Qed.

(** Top limb of a value bounded by [2^(64*(i+1))] is 0. *)
Lemma limb64_high_zero : forall x i,
  0 <= x < 2^(64 * Z.of_nat (S i)) ->
  limb64 x (S i) = 0.
Proof.
  intros.
  unfold limb64.
  rewrite Z.div_small by lia.
  reflexivity.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Multiplication bounds *)

(** The product of two 64-bit unsigned integers is at most [(2^64-1)^2]. *)
Lemma u64_mul_bound : forall (a b : UInt64),
  u64_val a * u64_val b <= (2^64 - 1) * (2^64 - 1).
Proof.
  intros.
  apply Z.mul_le_mono_nonneg.
  all: pose proof (u64_range a).
  all: pose proof (u64_range b).
  all: lia.
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
  apply Z.div_lt_upper_bound; [lia|].
  nia.
Qed.

(** Euclidean division identity with commuted multiplication. *)
Lemma div_mod_eq : forall a b, b <> 0 -> a = a / b * b + a mod b.
Proof.
  intros.
  pose proof (Z_div_mod_eq_full a b).
  lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** eval4 / u256 *)

(** [eval4 (2^64) (u64_val (u256_limb x 0)) ... = u256_val x]. *)
Lemma u256_as_eval4 : forall (x : UInt256),
  eval4 (2^64)
    (u64_val (u256_limb x 0)) (u64_val (u256_limb x 1))
    (u64_val (u256_limb x 2)) (u64_val (u256_limb x 3))
  = u256_val x.
Proof.
  intros.
  unfold u256_limb.
  simpl u64_val.
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
    split.
    + apply Z.add_nonneg_nonneg; apply Z.mod_pos_bound; lia.
    + assumption.
  - apply Z.ltb_ge in Hc.
    symmetry.
    apply Z.div_unique with (r := a mod M + b mod M - M).
    + assert (a mod M < M) by (apply Z.mod_pos_bound; lia).
      assert (b mod M < M) by (apply Z.mod_pos_bound; lia).
      lia.
    + lia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Limb-wise addition *)

(** Bridge: [x mod 2^64 = y] implies [Int64.eqm x y]. *)
Lemma eqm_of_mod_eq : forall x y,
  x mod 2^64 = y -> Int64.eqm x y.
Proof.
  intros x y H.
  unfold Int64.eqm.
  change Int64.modulus with (2^64).
  rewrite <- H.
  apply Zbits.eqmod_mod.
  lia.
Qed.

(** Limb 0: sum of low limbs mod 2^64 = low limb of sum.
    No incoming carry for the lowest digit. *)
Lemma limb_add_0 : forall a b,
  0 <= a -> 0 <= b ->
  (limb64 a 0 + limb64 b 0) mod 2^64 = limb64 (a + b) 0.
Proof.
  intros.
  unfold limb64.
  simpl Z.of_nat.
  rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r.
  rewrite Z.add_mod by lia.
  rewrite Z.mod_mod by lia.
  rewrite Z.mod_mod by lia.
  rewrite <- Z.add_mod by lia.
  reflexivity.
Qed.

(** Limb 1: sum of middle limbs + carry-in mod 2^64 = middle limb of sum. *)
Lemma limb_add_1 : forall a b,
  0 <= a -> 0 <= b ->
  (limb64 a 1 + (limb64 b 1 +
    (if limb64 a 0 + limb64 b 0 <? 2^64 then 0 else 1))) mod 2^64
  = limb64 (a + b) 1.
Proof.
  intros.
  unfold limb64.
  simpl Z.of_nat.
  rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r, Z.mul_1_r.

  (* Decompose (a+b)/2^64 via carry identity *)
  replace ((a + b) / 2^64)
    with (a / 2^64 + b / 2^64 + (a mod 2^64 + b mod 2^64) / 2^64)
    by (symmetry; apply Z_div_add_carry; lia).
  rewrite carry_value by lia.

  (* Strip inner mods through the outer mod *)
  rewrite Zplus_mod_idemp_l.
  replace (a / 2^64 + ((b / 2^64) mod 2^64 +
    (if a mod 2^64 + b mod 2^64 <? 2^64 then 0 else 1)))
    with ((a / 2^64 +
    (if a mod 2^64 + b mod 2^64 <? 2^64 then 0 else 1)) +
    (b / 2^64) mod 2^64) by lia.
  rewrite Zplus_mod_idemp_r.
  f_equal.
  lia.
Qed.

(** Limb 2: sum of high limbs + carry-in mod 2^64 = high limb of sum.
    Requires [b < 2^128] (i.e. b fits in 2 limbs) so that [b/(M*M) = 0]. *)
Lemma limb_add_2 : forall a b,
  0 <= a -> 0 <= b -> b < 2^128 ->
  (limb64 a 2 + (if limb64 a 1 + limb64 b 1 +
    (if limb64 a 0 + limb64 b 0 <? 2^64 then 0 else 1) <? 2^64 then 0 else 1))
  mod 2^64 = limb64 (a + b) 2.
Proof.
  intros a b Ha Hb Hb128.

  (* Setup: unfold limb64, introduce M = 2^64 *)
  unfold limb64.
  simpl Z.of_nat.
  rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r, Z.mul_1_r.
  replace (64 * 2) with (64 + 64) by lia.
  rewrite Z.pow_add_r by lia.
  set (M := (2^64)%Z).

  (* b < M^2, so b / (M*M) = 0 *)
  assert (Hbdiv : b / (M * M) = 0).
  { apply Z.div_small.
    unfold M in *.
    lia. }

  (* Decompose (a+b)/(M*M) via carry identity, cancel b/(M*M) = 0 *)
  replace ((a + b) / (M * M))
    with (a / (M * M) + b / (M * M) +
          (a mod (M * M) + b mod (M * M)) / (M * M))
    by (symmetry; apply Z_div_add_carry; [unfold M; lia | lia | lia]).
  rewrite Hbdiv, Z.add_0_r.

  (* Name the four half-limbs and establish ranges *)
  set (la0 := a mod M).
  set (lb0 := b mod M).
  set (la1 := a / M mod M).
  set (lb1 := b / M mod M).
  assert (Hla0 : 0 <= la0 < M) by (unfold la0, M; apply Z.mod_pos_bound; lia).
  assert (Hlb0 : 0 <= lb0 < M) by (unfold lb0, M; apply Z.mod_pos_bound; lia).
  assert (Hla1 : 0 <= la1 < M) by (unfold la1, M; apply Z.mod_pos_bound; lia).
  assert (Hlb1 : 0 <= lb1 < M) by (unfold lb1, M; apply Z.mod_pos_bound; lia).

  (* Define the carry from limb 1 -> limb 2 *)
  set (carry2 := if la0 + lb0 <? M
                 then if la1 + lb1 <? M then 0 else 1
                 else if la1 + lb1 + 1 <? M then 0 else 1).

  (* Show the LHS carry expression equals carry2 *)
  assert (Hcarry2_lhs :
    (if la1 + lb1 + (if la0 + lb0 <? M then 0 else 1) <? M
     then 0 else 1) = carry2).
  { unfold carry2.
    destruct (la0 + lb0 <? M) eqn:Ec0.
    all: destruct (la1 + lb1 <? M) eqn:Ec1.
    all: first [ replace (la1 + lb1 + 0) with (la1 + lb1) by lia
               | replace (la1 + lb1 + 1) with (la1 + lb1 + 1) by lia ].
    all: try rewrite Ec1.
    all: try reflexivity.
    all: destruct (la1 + lb1 + 1 <? M); reflexivity. }
  rewrite Hcarry2_lhs.

  (* Recombine a mod (M*M) and b mod (M*M) into two-limb form *)
  replace (a mod (M * M)) with (la0 + la1 * M)
    by (unfold la0, la1, M; rewrite Zmod_recombine by lia; ring).
  replace (b mod (M * M)) with (lb0 + lb1 * M)
    by (unfold lb0, lb1, M; rewrite Zmod_recombine by lia; ring).

  (* Show the combined two-limb sum / (M*M) equals carry2 *)
  assert (Hcarry_val :
    (la0 + la1 * M + (lb0 + lb1 * M)) / (M * M) = carry2).
  { unfold carry2.
    destruct (la0 + lb0 <? M) eqn:Ec0; destruct (la1 + lb1 <? M) eqn:Ec1.
    - (* no carry from limb 0, no carry from limb 1 *)
      apply Z.ltb_lt in Ec0.
      apply Z.ltb_lt in Ec1.
      apply Z.div_small.
      lia.
    - (* no carry from limb 0, carry from limb 1 *)
      apply Z.ltb_lt in Ec0.
      apply Z.ltb_ge in Ec1.
      symmetry.
      apply Z.div_unique with (r := la0 + lb0 + (la1 + lb1 - M) * M); lia.
    - (* carry from limb 0, no carry from limb 1 *)
      apply Z.ltb_ge in Ec0.
      apply Z.ltb_lt in Ec1.
      destruct (la1 + lb1 + 1 <? M) eqn:Ec1'.
      + apply Z.ltb_lt in Ec1'.
        apply Z.div_small.
        lia.
      + apply Z.ltb_ge in Ec1'.
        symmetry.
        apply Z.div_unique
          with (r := la0 + lb0 - M + (la1 + lb1 + 1 - M) * M); lia.
    - (* carry from limb 0, carry from limb 1 *)
      apply Z.ltb_ge in Ec0.
      apply Z.ltb_ge in Ec1.
      destruct (la1 + lb1 + 1 <? M) eqn:Ec1'.
      + apply Z.ltb_lt in Ec1'.
        symmetry.
        apply Z.div_unique
          with (r := la0 + lb0 - M + (la1 + lb1 + 1) * M); lia.
      + apply Z.ltb_ge in Ec1'.
        symmetry.
        apply Z.div_unique
          with (r := la0 + lb0 - M + (la1 + lb1 + 1 - M) * M); lia. }
  rewrite Hcarry_val.

  (* Final step: strip inner mod through outer mod *)
  rewrite Zplus_mod_idemp_l.
  reflexivity.
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
  destruct (c0 + tl <? Int64.modulus) eqn:Hcarry.
  - (* no wrap: c0+tl fits, so repr preserves order and ltu = false *)
    apply Z.ltb_lt in Hcarry.
    unfold Int64.ltu.
    rewrite !Int64.unsigned_repr by rep_lia.
    rewrite zlt_false by lia.
    reflexivity.
  - (* wrap: c0+tl overflows, repr wraps around, so ltu is true *)
    apply Z.ltb_ge in Hcarry.
    unfold Int64.ltu.
    rewrite (Int64.unsigned_repr tl) by rep_lia.
    rewrite Int64.unsigned_repr_eq.
    replace ((c0 + tl) mod Int64.modulus)
      with (c0 + tl - Int64.modulus)
      by (symmetry; apply Zmod_unique with 1; rep_lia).
    rewrite zlt_true by rep_lia.
    reflexivity.
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

  (* Limb ranges *)
  pose proof (limb64_u64_range acc_v 0) as Hla0.
  pose proof (limb64_u64_range prod 0) as Hlb0.

  (* Normalize ltu/b2z to the if-then-else carry *)
  rewrite (ltu_carry_b2z (limb64 acc_v 0) (limb64 prod 0)) by assumption.

  (* Int.signed (Int.repr (0 or 1)) = (0 or 1) *)
  assert (Hinner :
    Int.signed (Int.repr
      (if limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus then 0 else 1))
    = (if limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus then 0 else 1)).
  { destruct (limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus); reflexivity. }
  rewrite Hinner.

  (* Conclude via limb_add_1 *)
  change Int64.modulus with (2^64).
  apply eqm_of_mod_eq.
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

  (* Limb ranges *)
  pose proof (limb64_u64_range acc_v 0) as Hla0.
  pose proof (limb64_u64_range prod 0) as Hlb0.
  pose proof (limb64_u64_range acc_v 1) as Hla1.
  pose proof (limb64_u64_range prod 1) as Hlb1.

  (* Inline the let-bindings *)
  subst c0_carry th.

  (* ===== Normalize the inner (limb 0) carry ===== *)

  (* ltu/b2z -> if-then-else carry *)
  rewrite (ltu_carry_b2z (limb64 acc_v 0) (limb64 prod 0)) by assumption.

  (* Int.signed (Int.repr (0 or 1)) = (0 or 1) *)
  assert (Hinner :
    Int.signed (Int.repr
      (if limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus then 0 else 1))
    = (if limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus then 0 else 1)).
  { destruct (limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus); reflexivity. }
  rewrite Hinner.
  clear Hinner.

  (* Name the carry and bound it *)
  set (c0' := if limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus then 0 else 1).
  assert (Hc0' : 0 <= c0' <= 1)
    by (subst c0'; destruct (limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus); lia).

  (* prod high limb <= 2^64 - 2, so th = prod_hi + c0' fits in u64 *)
  assert (Hlb1' : limb64 prod 1 <= Int64.max_unsigned - 1).
  { unfold limb64.
    simpl Z.of_nat.
    change (64 * 1)%Z with 64.
    subst prod.
    change (2^64) with Int64.modulus.
    pose proof (mul_u64_hi_le av bv Hav Hbv).
    change (2^64) with Int64.modulus in H.
    rewrite Z.mod_small by (split; [apply Z.div_pos; rep_lia | rep_lia]).
    rep_lia. }
  assert (Hth : 0 <= limb64 prod 1 + c0' <= Int64.max_unsigned)
    by (subst c0'; destruct (limb64 acc_v 0 + limb64 prod 0 <? Int64.modulus); lia).

  (* ===== Normalize the outer (limb 1) carry ===== *)

  (* ltu/b2z -> if-then-else carry *)
  rewrite (ltu_carry_b2z (limb64 acc_v 1) (limb64 prod 1 + c0'))
    by (try assumption; lia).

  (* Int.signed (Int.repr (0 or 1)) = (0 or 1) *)
  assert (Houter :
    Int.signed (Int.repr
      (if limb64 acc_v 1 + (limb64 prod 1 + c0') <? Int64.modulus
       then 0 else 1))
    = (if limb64 acc_v 1 + (limb64 prod 1 + c0') <? Int64.modulus
       then 0 else 1)).
  { destruct (limb64 acc_v 1 + (limb64 prod 1 + c0') <? Int64.modulus);
    reflexivity. }
  rewrite Houter.
  clear Houter.

  (* Re-associate addition for limb_add_2 *)
  replace (limb64 acc_v 1 + (limb64 prod 1 + c0'))
    with (limb64 acc_v 1 + limb64 prod 1 + c0') by lia.
  change Int64.modulus with (2^64).

  (* Conclude via limb_add_2 *)
  subst c0'.
  apply eqm_of_mod_eq.
  apply limb_add_2; nia.
Qed.

(* ----------------------------------------------------------------- *)
(** *** sumadd carry bridge lemmas

    Same idea as [muladd_limb1] / [muladd_limb2], but for adding a
    plain u64 value [av] (rather than a product) to an accumulator.
    Since [av < 2^64], its high limbs are 0, which simplifies the
    carry chain.

    Stated as [Int64.repr] equalities so that callers can [apply]
    directly after [f_equal], without an intermediate [eqm] step. *)

(** Bridge for sumadd limb 0. *)
Lemma sumadd_limb0 : forall acc_v av,
  0 <= acc_v -> 0 <= av < 2^64 ->
  Int64.eqm (limb64 acc_v 0 + av) (limb64 (acc_v + av) 0).
Proof.
  intros.
  apply eqm_of_mod_eq.
  unfold limb64; simpl Z.of_nat;
    rewrite Z.mul_0_r, Z.pow_0_r, !Z.div_1_r.
  apply Zplus_mod_idemp_l.
Qed.

(** Bridge for sumadd limb 1: normalize [ltu] / [b2z] into
    [limb_add_1] form.  The caller strips [Int.unsigned] or
    [Int.signed] (one rewrite) before applying this lemma. *)
Lemma sumadd_limb1 : forall acc_v av,
  0 <= acc_v -> 0 <= av < 2^64 ->
  Int64.eqm
    (limb64 acc_v 1 +
      Z.b2z (Int64.ltu
        (Int64.repr (limb64 acc_v 0 + av))
        (Int64.repr av)))
    (limb64 (acc_v + av) 1).
Proof.
  intros acc_v av Hacc Hav.
  pose proof (limb64_u64_range acc_v 0).

  rewrite (ltu_carry_b2z (limb64 acc_v 0) av) by rep_lia.
  change Int64.modulus with (2^64).

  apply eqm_of_mod_eq.
  assert (Hav0 : limb64 av 0 = av).
  { unfold limb64. simpl Z.of_nat.
    rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
    apply Z.mod_small. lia. }
  assert (Hav1 : limb64 av 1 = 0)
    by (apply limb64_high_zero; simpl Z.of_nat; lia).
  transitivity ((limb64 acc_v 1 + (limb64 av 1 +
    (if limb64 acc_v 0 + limb64 av 0 <? 2^64 then 0 else 1))) mod 2^64).
  - f_equal. rewrite Hav0, Hav1. lia.
  - apply limb_add_1; lia.
Qed.

(** Bridge for sumadd limb 2: normalize two levels of carry
    (unsigned inner, signed outer) into [limb_add_2_u64] form. *)
Lemma sumadd_limb2 : forall acc_v av,
  0 <= acc_v -> 0 <= av < 2^64 ->
  let c0_carry :=
    Z.b2z (Int64.ltu
      (Int64.repr (limb64 acc_v 0 + av))
      (Int64.repr av)) in
  let over := Int.unsigned (Int.repr c0_carry) in
  Int64.eqm
    (limb64 acc_v 2 +
      Int.signed (Int.repr
        (Z.b2z (Int64.ltu
          (Int64.repr (limb64 acc_v 1 + over))
          (Int64.repr over)))))
    (limb64 (acc_v + av) 2).
Proof.
  intros acc_v av Hacc Hav c0_carry over.
  pose proof (limb64_u64_range acc_v 0) as Hla0.
  pose proof (limb64_u64_range acc_v 1) as Hla1.

  subst c0_carry over.

  (* Normalize inner (limb 0) carry *)
  rewrite (ltu_carry_b2z (limb64 acc_v 0) av) by rep_lia.
  set (c0' := if limb64 acc_v 0 + av <? Int64.modulus then 0 else 1).
  assert (Hc0' : 0 <= c0' <= 1)
    by (subst c0'; destruct (limb64 acc_v 0 + av <? Int64.modulus); lia).
  assert (Hcu : Int.unsigned (Int.repr c0') = c0')
    by (subst c0'; destruct (limb64 acc_v 0 + av <? Int64.modulus); reflexivity).
  rewrite Hcu.

  (* Normalize outer (limb 1) carry *)
  rewrite (ltu_carry_b2z (limb64 acc_v 1) c0') by rep_lia.
  assert (Hcs :
    Int.signed (Int.repr
      (if limb64 acc_v 1 + c0' <? Int64.modulus then 0 else 1))
    = (if limb64 acc_v 1 + c0' <? Int64.modulus then 0 else 1))
    by (destruct (limb64 acc_v 1 + c0' <? Int64.modulus); reflexivity).
  rewrite Hcs.
  change Int64.modulus with (2^64).

  (* Derive from limb_add_2: substitute limb64 av 0 = av, limb64 av 1 = 0 *)
  subst c0'.
  apply eqm_of_mod_eq.
  pose proof (limb_add_2 acc_v av Hacc ltac:(lia) ltac:(lia)) as H.
  rewrite (limb64_high_zero av 0) in H by (simpl Z.of_nat; lia).
  replace (limb64 av 0) with av in H
    by (unfold limb64; simpl Z.of_nat;
        rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r;
        symmetry; apply Z.mod_small; lia).
  replace (limb64 acc_v 1 + 0 +
    (if limb64 acc_v 0 + av <? 2 ^ 64 then 0 else 1))
    with (limb64 acc_v 1 +
    (if limb64 acc_v 0 + av <? 2 ^ 64 then 0 else 1)) in H by lia.
  exact H.
Qed.
