# Proof Style Guide

## Tactics

- **One tactic per line.** Never chain independent tactics with `;` on one line.
- Semicolons are allowed inside `by (...)` or `ltac:(...)` for short inline proofs:
  ```coq
  assert (H : 0 <= x) by (apply Z.div_pos; lia).
  ```
- A trailing `; solver` is allowed when the solver (e.g. `lia`, `nia`, `reflexivity`)
  closes all remaining subgoals in one shot:
  ```coq
  apply limb_add_0; lia.
  apply limb_add_2_u64; lia.
  ```
- A `; ` chain is allowed when all generated subgoals use the same tactic sequence:
  ```coq
  apply Zbits.eqmod_add;
      apply Zbits.eqmod_sym;
      apply Zbits.eqmod_mod;
      lia.
  ```
- `by (...)` is for proofs that fit on one line (1-3 tactics). Use `{ }` blocks for anything longer.
- `do N tactic` is allowed for repeated identical tactics (e.g. `do 3 f_equal.`), but not for VST tactics like `forward` -- each `forward` should be on its own line with a comment.
- `ltac:(...)` is for very short proof obligations passed as arguments (1-2 tactics). If longer than ~60 characters, assert separately first.
- Break multi-line arguments at the opening parenthesis, align continuations:
  ```coq
  forward_call (v_acc, acc_s1_1a,
                mkUInt64 n1 Hn1, mkUInt64 N_C_0 N_C_0_range, Tsh).
  ```

## Assertions

- Short proof: `assert (H : statement) by (tactic1; tactic2).`
- Long proof:
  ```coq
  assert (H : statement).
  { tactic1.
    tactic2.
    tactic3. }
  ```
- Group similar assertions together without blank lines between them:
  ```coq
  assert (Hm0 : 0 <= m0 < B) by (subst m0; apply Z.mod_pos_bound; lia).
  assert (Hm1 : 0 <= m1 < B) by (subst m1; apply Z.mod_pos_bound; lia).
  assert (Hm2 : 0 <= m2 < B) by (subst m2; apply Z.mod_pos_bound; lia).
  ```

## Branching

- Use `{ }` blocks with bullets (up to 3 nesting levels): `-` (level 1), `+` (level 2), `*` (level 3).
- `[ | ]` syntax is allowed in short single-line proofs (e.g. inside `by (...)`).
  For multi-line branching, use `{ }` with bullets instead.
- Each branch gets its own line:
  ```coq
  assert (0 <= t0).
  { subst t0. apply Z.add_nonneg_nonneg.
    - lia.
    - apply Z.mul_nonneg_nonneg; lia. }
  ```
- Closing `}` goes on the last line of the block when short, or on its own line when the block is long.
- Add a short comment on each major branch or conjunct explaining what it proves:
  ```coq
  repeat split.
  - (* conjunct 0: (sum / B^0) mod B = a0 *)
    rewrite Z.pow_0_r, Z.div_1_r.
    ...
  - (* conjunct 1: (sum / B^1) mod B = a1 *)
    rewrite Z.pow_1_r.
    ...
  ```

## Formatting

- 2-space indentation throughout.
- Contents of `{ }` blocks are indented by 2 relative to the `assert` or tactic that opened them.
- Bullet points (`-`, `+`, `*`) are indented to the block level, with their body indented by 2 more.
- Blank lines separate logical phases within a proof (e.g. after setup, between steps).
- No blank lines between grouped similar tactics (e.g. a block of `set` or `assert`).
- For complex proofs, document the proof strategy in the lemma's doc comment before `Proof.`
- ASCII only. No Unicode characters (use `->` not `→`, `x` not `×`, `--` not `—`).
- Prefer repetition over premature abstraction.
- Do not compress whitespace or join lines for compactness.

## Comments

Three levels:

1. **Section headers** (file-level):
   ```coq
   (* ================================================================= *)
   (** ** Section Name *)
   (* ================================================================= *)
   ```
   Subsections use `(** *** Subsection Name *)`.

2. **Proof phases** (inside proof bodies):
   ```coq
   (* ===== Stage 1: Reduce 512 -> 385 bits ===== *)
   ```

3. **Inline** (tactic-level):
   ```coq
   (* muladd_fast(&acc, n0, N_C_0) *)
   ```

- Use `(** ... *)` doc comments only for lemma/definition descriptions outside proofs.
- Use `(* ... *)` regular comments for everything inside proofs.
- Separator lines are 67 characters total: `(* ================================================================= *)`.

## Context & Naming

- Hypothesis names: `H` prefix + descriptive (`Hd0`, `Hchain`, `Hr_z_bnd`).
- Intermediate values: `set (name := expr).` with short descriptive names.
- `clear` intermediates as soon as they are no longer needed. Large VST contexts slow down tactics significantly.
- Use `clear -` (keep only listed hypotheses) at stage boundaries to reset the context.
- `rename H into Hname` immediately after `Intros` to give hypotheses meaningful names.

## Imports

- Standard library: `From Stdlib Require Import ZArith.`
- Group imports by origin (stdlib, project, external) with a blank line between groups.

## VST proof style

- Comment before each `forward_call` explaining the C operation.
- Side condition proofs in `{ }` blocks.
- `Intros` / `rename H` / `assert` / `clear` each on their own line:
  ```coq
  (* secp256k1_u128_from_u64(&t, d0) *)
  forward_call (v_t, mkUInt64 d0 Hd0, Tsh).
  Intros t_init.
  rename H into Ht_init.
  ```

## Proof automation

The project ships a small automation layer in `proof/Helper_verif.v` and
`proof/Helper_forward_call.v`. Prefer it over hand-rolled patterns:

- **`rep_lia` over `lia`** for goals involving `UInt64` / `UInt128` / `Acc`
  values. The `rep_lia_setup2` hook in `Helper_verif.v` auto-poses the
  carried range fact for every `u64_val ?x`, `u128_val ?x`, `acc_val ?x`,
  `u256_val ?x` in the goal, eliminating manual
  `pose proof (u64_range x)` calls.
- **`forward_call_*` wrappers** in `Helper_forward_call.v` bundle each
  `forward_call` with `Intros`, `rename H`, optional `destruct`, and
  `deadvars!`. They auto-discharge the parameter-matching obligation via
  `solve_param_match` (which rewrites with the `to_val_limb` Hint database)
  and the linear PROP via `try (simpl; rep_lia)`. Use them in preference to
  raw `forward_call (...) ; Intros ...`.
- **Constants**: use `N_C_0_u64`, `N_C_1_u64`, `N_C_2_u64` (declared in
  `Helper_verif.v`), not the verbose `mkUInt64 N_C_i N_C_i_range`. They
  are registered with `Hint Rewrite` in the `rep_lia` database so
  `u64_val N_C_i_u64` reduces automatically.
- **Limbs**: use the generic `limb (2^64) v i` from `Helper_arithmetic.v`.
  The C-representation
  definitions (`uint128_to_val`, `acc_to_val`, `uint256_to_val`,
  `uint512_to_val`) use **inline splits** `(v / 2^k) mod 2^64` in their
  bodies, matching the spec style. Bridge lemmas
  `uint128/acc/uint256/uint512_to_val_limb` (registered with
  `Hint Rewrite … : to_val_limb`) equate the inline form to
  `limb (2^64) v i`, so proofs can convert with `autorewrite with to_val_limb`.
- **`limb_at_0` lemma**: rewrites `limb (2^64) v 0` back to `v mod 2^64`.
  Replaces the older `norm_limb_0` Ltac. Use `rewrite ?limb_at_0` in
  proofs that prefer the mod form.
- **`Hint Rewrite ... : rep_lia`** is the registry for any lemma that
  `rep_lia` should auto-apply (e.g. constant unfoldings, projector
  reductions, limb-of-known-value identities).
