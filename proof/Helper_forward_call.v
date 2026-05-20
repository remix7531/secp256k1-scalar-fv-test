(** * Helper_forward_call: forward_call wrapper Ltacs for helper functions
    Each helper function has the same post-call boilerplate:
    [Intros], [rename], [destruct], [deadvars!].  These Ltacs
    bundle the [forward_call] with the boilerplate so that a
    single call replaces 3-6 lines.

    Each wrapper has the shape
    {[
        Ltac forward_call_X args... :=
          forward_call (...);
          [ try solve_param_match; try (simpl; rep_lia) ..
          | Intros ret; rename H into Hret; try deadvars! ].
    ]}
    The first column auto-discharges the parameter-matching
    obligation via [solve_param_match] (which rewrites with the
    [to_val_limb] Hint database) and any linear PROP via
    [try (simpl; rep_lia)].  The trailing column introduces the
    EX postcondition and gives it a stable hypothesis name.

    When obligations remain (overflow bounds, frame), the caller
    solves them with focused [{...}] blocks after the Ltac call. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Export scalar_4x64.Helper_verif.

(** Solve the parameter-matching [firstn ... = [...]] equation that
    appears when the C-representation uses inline splits but the spec
    arguments are [u256_limb x k] / [uint64_to_val _].  Rewrites with
    the bridge lemmas [uint128/acc/uint256/uint512_to_val_limb] to
    convert inline splits to [limb (2^64) v i] form. *)
Ltac solve_param_match :=
  entailer!;
  autorewrite with to_val_limb;
  unfold u256_limb, uint64_to_val;
  simpl;
  reflexivity.

(** Accumulator helpers (muladd, muladd_fast, sumadd, sumadd_fast). *)

Ltac forward_call_muladd acc_ptr acc a b acc' Hacc' :=
  forward_call (acc_ptr, acc, a, b, Tsh);
  [ try solve_param_match; try (simpl; rep_lia) .. | Intros acc'; rename H into Hacc'; try deadvars!].

Ltac forward_call_muladd_fast acc_ptr acc a b acc' Hacc' :=
  forward_call (acc_ptr, acc, a, b, Tsh);
  [ try solve_param_match; try (simpl; rep_lia) .. | Intros acc'; rename H into Hacc'; try deadvars!].

Ltac forward_call_sumadd acc_ptr acc a acc' Hacc' :=
  forward_call (acc_ptr, acc, a, Tsh);
  [ try solve_param_match; try (simpl; rep_lia) .. | Intros acc'; rename H into Hacc'; try deadvars!].

Ltac forward_call_sumadd_fast acc_ptr acc a acc' Hacc' :=
  forward_call (acc_ptr, acc, a, Tsh);
  [ try solve_param_match; try (simpl; rep_lia) .. | Intros acc'; rename H into Hacc'; try deadvars!].

(** Extract helpers (extract, extract_fast).
    Returns a [(UInt64 * Acc)] pair that is destructured. *)

Ltac forward_call_extract acc_ptr acc n_ptr sh sh_n lo carry Hlo Hcarry :=
  forward_call (acc_ptr, acc, n_ptr, sh, sh_n);
  [ try (simpl; rep_lia) .. | let vret := fresh "vret" in
        Intros vret; destruct vret as [lo carry];
        rename H into Hlo; rename H0 into Hcarry;
        simpl fst in *; simpl snd in *;
        try deadvars!].

Ltac forward_call_extract_fast acc_ptr acc n_ptr sh sh_n lo carry Hlo Hcarry :=
  forward_call (acc_ptr, acc, n_ptr, sh, sh_n);
  [ try (simpl; rep_lia) .. | let vret := fresh "vret" in
        Intros vret; destruct vret as [lo carry];
        rename H into Hlo; rename H0 into Hcarry;
        simpl fst in *; simpl snd in *;
        try deadvars!].

(** u128 helpers. *)

Ltac forward_call_u128_mul r_ptr a b sh r Hr :=
  forward_call (r_ptr, a, b, sh);
  [ try (simpl; rep_lia) .. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_from_u64 r_ptr a sh r Hr :=
  forward_call (r_ptr, a, sh);
  [ try (simpl; rep_lia) .. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_accum_u64 r_ptr r a sh r' Hr' :=
  forward_call (r_ptr, r, a, sh);
  [ try (simpl; rep_lia) .. | Intros r'; rename H into Hr'; try deadvars!].

Ltac forward_call_u128_accum_mul r_ptr r a b sh r' Hr' :=
  forward_call (r_ptr, r, a, b, sh);
  [ try (simpl; rep_lia) .. | Intros r'; rename H into Hr'; try deadvars!].

Ltac forward_call_u128_to_u64 a_ptr x sh r Hr :=
  forward_call (a_ptr, x, sh);
  [ try (simpl; rep_lia) .. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_hi_u64 a_ptr x sh r Hr :=
  forward_call (a_ptr, x, sh);
  [ try (simpl; rep_lia) .. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_rshift r_ptr r sh r' Hr' :=
  forward_call (r_ptr, r, 64, sh);
  [ try (simpl; rep_lia) .. | Intros r'; rename H into Hr'; try deadvars!].

(** umul128: compute a*b, return lo, write hi to *hi_ptr. *)

Ltac forward_call_umul128 a b hi_ptr sh result Hresult :=
  forward_call (a, b, hi_ptr, sh);
  [.. | Intros result; rename H into Hresult; try deadvars!].

(** Higher-level functions. *)

Ltac forward_call_scalar_check_overflow a_ptr a sh :=
  forward_call (a_ptr, a, sh).

Ltac forward_call_scalar_reduce r_ptr r overflow sh r' Hr' :=
  forward_call (r_ptr, r, overflow, sh);
  [.. | Intros r'; rename H into Hr'; try deadvars!].

Ltac forward_call_scalar_mul_512 l8_ptr a_ptr b_ptr a b sh_l sh_a sh_b r Hr :=
  forward_call (l8_ptr, a_ptr, b_ptr, a, b, sh_l, sh_a, sh_b);
  [.. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_scalar_reduce_512 r_ptr l_ptr l sh_r sh_l r' Hr' :=
  forward_call (r_ptr, l_ptr, l, sh_r, sh_l);
  [.. | Intros r'; rename H into Hr'; try deadvars!].
