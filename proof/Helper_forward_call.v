(** * Helper_forward_call: forward_call wrapper Ltacs for helper functions
    Each helper function has the same post-call boilerplate:
    [Intros], [rename], [destruct], [deadvars!].  These Ltacs
    bundle the [forward_call] with the boilerplate so that a
    single call replaces 3-6 lines.

    When all PROP obligations are auto-solved, these Ltacs
    complete in one step.  When obligations remain (overflow
    bounds, frame, parameter matching), the caller solves them
    with focused [{...}] blocks after the Ltac call. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Export scalar_4x64.Helper_verif.

(** Accumulator helpers (muladd, muladd_fast, sumadd, sumadd_fast). *)

Ltac forward_call_muladd acc_ptr acc a b acc' Hacc' :=
  forward_call (acc_ptr, acc, a, b, Tsh);
  [.. | Intros acc'; rename H into Hacc'; try deadvars!].

Ltac forward_call_muladd_fast acc_ptr acc a b acc' Hacc' :=
  forward_call (acc_ptr, acc, a, b, Tsh);
  [.. | Intros acc'; rename H into Hacc'; try deadvars!].

Ltac forward_call_sumadd acc_ptr acc a acc' Hacc' :=
  forward_call (acc_ptr, acc, a, Tsh);
  [.. | Intros acc'; rename H into Hacc'; try deadvars!].

Ltac forward_call_sumadd_fast acc_ptr acc a acc' Hacc' :=
  forward_call (acc_ptr, acc, a, Tsh);
  [.. | Intros acc'; rename H into Hacc'; try deadvars!].

(** Extract helpers (extract, extract_fast).
    Returns a [(UInt64 * Acc)] pair that is destructured. *)

Ltac forward_call_extract acc_ptr acc n_ptr sh sh_n lo carry Hlo Hcarry :=
  forward_call (acc_ptr, acc, n_ptr, sh, sh_n);
  [.. | let vret := fresh "vret" in
        Intros vret; destruct vret as [lo carry];
        rename H into Hlo; rename H0 into Hcarry;
        simpl fst in *; simpl snd in *;
        try deadvars!].

Ltac forward_call_extract_fast acc_ptr acc n_ptr sh sh_n lo carry Hlo Hcarry :=
  forward_call (acc_ptr, acc, n_ptr, sh, sh_n);
  [.. | let vret := fresh "vret" in
        Intros vret; destruct vret as [lo carry];
        rename H into Hlo; rename H0 into Hcarry;
        simpl fst in *; simpl snd in *;
        try deadvars!].

(** u128 helpers. *)

Ltac forward_call_u128_mul r_ptr a b sh r Hr :=
  forward_call (r_ptr, a, b, sh);
  [.. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_from_u64 r_ptr a sh r Hr :=
  forward_call (r_ptr, a, sh);
  [.. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_accum_u64 r_ptr r a sh r' Hr' :=
  forward_call (r_ptr, r, a, sh);
  [.. | Intros r'; rename H into Hr'; try deadvars!].

Ltac forward_call_u128_accum_mul r_ptr r a b sh r' Hr' :=
  forward_call (r_ptr, r, a, b, sh);
  [.. | Intros r'; rename H into Hr'; try deadvars!].

Ltac forward_call_u128_to_u64 a_ptr x sh r Hr :=
  forward_call (a_ptr, x, sh);
  [.. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_hi_u64 a_ptr x sh r Hr :=
  forward_call (a_ptr, x, sh);
  [.. | Intros r; rename H into Hr; try deadvars!].

Ltac forward_call_u128_rshift r_ptr r sh r' Hr' :=
  forward_call (r_ptr, r, 64, sh);
  [.. | Intros r'; rename H into Hr'; try deadvars!].

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
