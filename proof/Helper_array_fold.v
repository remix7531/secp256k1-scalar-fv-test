(** * Helper_array_fold: Fold/unfold between element-wise and array [data_at]

    When VST's [forward] processes stores into array slots one at a time,
    the proof state ends up with N separate [data_at sh tulong vi ...]
    predicates.  The postcondition requires a single
    [data_at sh (tarray tulong N) [v0; ...; vN-1] p], or vice versa.

    These lemmas bridge that gap in both directions for sizes 2, 4, and 8.

    Strategy (same for fold and unfold):
      1. Split the array into singletons via [split2_data_at_Tarray_app].
      2. Simplify subtraction remnants ([change (N-1) with ...]).
      3. Convert singletons via [data_at_singleton_array_eq].
      4. Collapse nested [field_address0] via [field_address0_SUB_SUB].
      5. Normalize addresses to [offset_val] and [cancel]. *)

(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.

(* ================================================================= *)
(** ** Helper: [isptr] from [field_compatible] *)

Local Ltac solve_isptr :=
  match goal with
  | H : field_compatible _ _ ?p |- isptr ?p =>
      destruct H as [? _]; destruct p; simpl in *; auto
  end.


(** Peel one slot off the front of an uninitialized tulong sub-array
    at index [k] inside [tarray tulong 8].  Preconditions:
    - [0 < k < 8]
    - The sub-array has exactly [8 - k] elements. *)
Lemma peel_array_slot : forall sh p k,
  field_compatible (tarray tulong 8) [] p ->
  0 < k -> k < 8 ->
  data_at_ sh (tarray tulong (8 - k))
    (field_address0 (tarray tulong 8) (SUB k) p)
  |-- data_at_ sh tulong (field_address (tarray tulong 8) (SUB k) p) *
      data_at_ sh (tarray tulong (8 - k - 1))
        (field_address0 (tarray tulong 8) (SUB (k + 1)) p).
Proof.
  intros sh p k Hfc Hk0 Hk8.
  rewrite (split2_data_at__Tarray_app 1 (8 - k) sh tulong
             (field_address0 (tarray tulong 8) (SUB k) p)) by lia.
  replace (8 - k - 1) with (8 - (k + 1)) by lia.
  rewrite data__at_singleton_array_eq.
  rewrite (field_address0_SUB_SUB tulong (8 - k) 8 1 k p) by lia.
  replace (1 + k) with (k + 1) by lia.
  rewrite (arr_field_address0 tulong 8 p (k + 1) Hfc) by lia.
  rewrite (arr_field_address0 tulong 8 p k Hfc) by lia.
  rewrite (arr_field_address tulong 8 p k Hfc) by lia.
  cancel.
Qed.

(** Decompose an uninitialized 8-element array into 8 individual slots.
    This lets [forward_call] for [extract] find its target slot
    automatically via [cancel], without manual [peel_array_slot] calls. *)
Lemma unfold_data_at__tulong_8 :
  forall (sh : share) (p : val),
  field_compatible (tarray tulong 8) [] p ->
  data_at_ sh (tarray tulong 8) p
  |-- data_at_ sh tulong (field_address (tarray tulong 8) (SUB 0) p) *
      data_at_ sh tulong (field_address (tarray tulong 8) (SUB 1) p) *
      data_at_ sh tulong (field_address (tarray tulong 8) (SUB 2) p) *
      data_at_ sh tulong (field_address (tarray tulong 8) (SUB 3) p) *
      data_at_ sh tulong (field_address (tarray tulong 8) (SUB 4) p) *
      data_at_ sh tulong (field_address (tarray tulong 8) (SUB 5) p) *
      data_at_ sh tulong (field_address (tarray tulong 8) (SUB 6) p) *
      data_at_ sh tulong (field_address (tarray tulong 8) (SUB 7) p).
Proof.
  intros sh p H.

  (* --- Phase 1: Split the 8-element array into singletons --- *)
  rewrite (split2_data_at__Tarray_app 1 8 sh tulong p) by lia.
  rewrite (split2_data_at__Tarray_app 1 7 sh tulong
    (field_address0 (tarray tulong 8) (SUB 1) p)) by lia.
  rewrite (split2_data_at__Tarray_app 1 6 sh tulong
    (field_address0 (tarray tulong 7) (SUB 1)
      (field_address0 (tarray tulong 8) (SUB 1) p))) by lia.
  rewrite (split2_data_at__Tarray_app 1 5 sh tulong
    (field_address0 (tarray tulong 6) (SUB 1)
      (field_address0 (tarray tulong 7) (SUB 1)
        (field_address0 (tarray tulong 8) (SUB 1) p)))) by lia.
  rewrite (split2_data_at__Tarray_app 1 4 sh tulong
    (field_address0 (tarray tulong 5) (SUB 1)
      (field_address0 (tarray tulong 6) (SUB 1)
        (field_address0 (tarray tulong 7) (SUB 1)
          (field_address0 (tarray tulong 8) (SUB 1) p))))) by lia.
  rewrite (split2_data_at__Tarray_app 1 3 sh tulong
    (field_address0 (tarray tulong 4) (SUB 1)
      (field_address0 (tarray tulong 5) (SUB 1)
        (field_address0 (tarray tulong 6) (SUB 1)
          (field_address0 (tarray tulong 7) (SUB 1)
            (field_address0 (tarray tulong 8) (SUB 1) p)))))) by lia.
  rewrite (split2_data_at__Tarray_app 1 2 sh tulong
    (field_address0 (tarray tulong 3) (SUB 1)
      (field_address0 (tarray tulong 4) (SUB 1)
        (field_address0 (tarray tulong 5) (SUB 1)
          (field_address0 (tarray tulong 6) (SUB 1)
            (field_address0 (tarray tulong 7) (SUB 1)
              (field_address0 (tarray tulong 8) (SUB 1) p))))))) by lia.

  (* --- Phase 2: Simplify subtraction remnants --- *)
  change (8-1) with 7.
  change (7-1) with 6.
  change (6-1) with 5.
  change (5-1) with 4.
  change (4-1) with 3.
  change (3-1) with 2.
  change (2-1) with 1.

  (* --- Phase 3: Convert all singletons --- *)
  rewrite !data__at_singleton_array_eq.

  (* --- Phase 4: Collapse nested field_address0 to field_address --- *)
  rewrite !field_address0_SUB_SUB by lia.
  change (1 + 1) with 2.
  change (1 + (1 + 1)) with 3.
  change (1 + (1 + (1 + 1))) with 4.
  change (1 + (1 + (1 + (1 + 1)))) with 5.
  change (1 + (1 + (1 + (1 + (1 + 1))))) with 6.
  change (1 + (1 + (1 + (1 + (1 + (1 + 1)))))) with 7.

  (* Normalize addresses to offset_val *)
  rewrite !(arr_field_address0 tulong 8 p _ H) by lia.
  rewrite !(arr_field_address tulong 8 p _ H) by lia.
  simpl (sizeof tulong * _).
  rewrite isptr_offset_val_zero by solve_isptr.
  cancel.
Qed.


(* ================================================================= *)
(** ** Size 2 *)

(** Fold 2 individual [data_at] into [data_at (tarray tulong 2)]. *)
Lemma fold_data_at_tulong_2 :
  forall (sh : share) (p : val) (v0 v1 : val),
  field_compatible (tarray tulong 2) [] p ->
  data_at sh tulong v0 (field_address (tarray tulong 2) (SUB 0) p) *
  data_at sh tulong v1 (field_address (tarray tulong 2) (SUB 1) p)
  |-- data_at sh (tarray tulong 2) [v0; v1] p.
Proof.
  intros.

  (* Split RHS: [v0; v1] = [v0] ++ [v1] *)
  change [v0; v1] with ([v0] ++ [v1]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 2 sh tulong
    [v0] [v1] p eq_refl eq_refl).
  change (2 - 1) with 1.

  (* Convert singletons *)
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v0 [v0] p eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v1 [v1]
    (field_address0 (tarray tulong 2) (SUB 1) p) eq_refl).

  (* Normalize addresses to offset_val *)
  rewrite !(arr_field_address0 tulong 2 p _ H) by lia.
  rewrite !(arr_field_address tulong 2 p _ H) by lia.
  simpl (sizeof tulong * _).
  rewrite isptr_offset_val_zero by solve_isptr.
  cancel.
Qed.

(* ================================================================= *)
(** ** Size 4 *)

(** Fold 4 individual [data_at] into [data_at (tarray tulong 4)]. *)
Lemma fold_data_at_tulong_4 :
  forall (sh : share) (p : val) (v0 v1 v2 v3 : val),
  field_compatible (tarray tulong 4) [] p ->
  data_at sh tulong v0 (field_address (tarray tulong 4) (SUB 0) p) *
  data_at sh tulong v1 (field_address (tarray tulong 4) (SUB 1) p) *
  data_at sh tulong v2 (field_address (tarray tulong 4) (SUB 2) p) *
  data_at sh tulong v3 (field_address (tarray tulong 4) (SUB 3) p)
  |-- data_at sh (tarray tulong 4) [v0; v1; v2; v3] p.
Proof.
  intros.

  (* Split RHS: [v0;v1;v2;v3] = [v0] ++ [v1;v2;v3] *)
  change [v0; v1; v2; v3] with ([v0] ++ [v1; v2; v3]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 4 sh tulong
    [v0] [v1;v2;v3] p eq_refl eq_refl).
  change [v1; v2; v3] with ([v1] ++ [v2; v3]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 3 sh tulong
    [v1] [v2;v3]
    (field_address0 (tarray tulong 4) (SUB 1) p) eq_refl eq_refl).
  change [v2; v3] with ([v2] ++ [v3]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 2 sh tulong
    [v2] [v3]
    (field_address0 (tarray tulong 3) (SUB 1)
      (field_address0 (tarray tulong 4) (SUB 1) p)) eq_refl eq_refl).

  (* Simplify arithmetic *)
  change (4 - 1) with 3.
  change (3 - 1) with 2.
  change (2 - 1) with 1.

  (* Convert singletons *)
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v0 [v0] p eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v1 [v1]
    (field_address0 (tarray tulong 4) (SUB 1) p) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v2 [v2]
    (field_address0 (tarray tulong 3) (SUB 1)
      (field_address0 (tarray tulong 4) (SUB 1) p)) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v3 [v3]
    (field_address0 (tarray tulong 2) (SUB 1)
      (field_address0 (tarray tulong 3) (SUB 1)
        (field_address0 (tarray tulong 4) (SUB 1) p))) eq_refl).

  (* Collapse nested field_address0 *)
  rewrite !field_address0_SUB_SUB by lia.
  change (1 + 1) with 2.
  change (1 + (1 + 1)) with 3.

  (* Normalize addresses to offset_val *)
  rewrite !(arr_field_address0 tulong 4 p _ H) by lia.
  rewrite !(arr_field_address tulong 4 p _ H) by lia.
  simpl (sizeof tulong * _).
  rewrite isptr_offset_val_zero by solve_isptr.

  cancel.
Qed.

(*
(** Decompose a 4-element [data_at_ (tarray tulong 4)] into individual elements. *)
Lemma unfold_data_at__tulong_4 :
  forall (sh : share) (p : val),
  field_compatible (tarray tulong 4) [] p ->
  data_at_ sh (tarray tulong 4) p
  |-- data_at_ sh tulong (field_address (tarray tulong 4) (SUB 0) p) *
      data_at_ sh tulong (field_address (tarray tulong 4) (SUB 1) p) *
      data_at_ sh tulong (field_address (tarray tulong 4) (SUB 2) p) *
      data_at_ sh tulong (field_address (tarray tulong 4) (SUB 3) p).
*)

(* ================================================================= *)
(** ** Size 8 *)

(** Fold 8 individual [data_at] into [data_at (tarray tulong 8)]. *)
Lemma fold_data_at_tulong_8 :
  forall (sh : share) (p : val) (v0 v1 v2 v3 v4 v5 v6 v7 : val),
  field_compatible (tarray tulong 8) [] p ->
  data_at sh tulong v0 (field_address (tarray tulong 8) (SUB 0) p) *
  data_at sh tulong v1 (field_address (tarray tulong 8) (SUB 1) p) *
  data_at sh tulong v2 (field_address (tarray tulong 8) (SUB 2) p) *
  data_at sh tulong v3 (field_address (tarray tulong 8) (SUB 3) p) *
  data_at sh tulong v4 (field_address (tarray tulong 8) (SUB 4) p) *
  data_at sh tulong v5 (field_address (tarray tulong 8) (SUB 5) p) *
  data_at sh tulong v6 (field_address (tarray tulong 8) (SUB 6) p) *
  data_at sh tulong v7 (field_address (tarray tulong 8) (SUB 7) p)
  |-- data_at sh (tarray tulong 8) [v0; v1; v2; v3; v4; v5; v6; v7] p.
Proof.
  intros.

  (* --- Phase 1: Split the 8-element array into singletons --- *)
  change [v0; v1; v2; v3; v4; v5; v6; v7]
    with ([v0] ++ [v1; v2; v3; v4; v5; v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 8 sh tulong
    [v0] [v1;v2;v3;v4;v5;v6;v7] p eq_refl eq_refl).
  change [v1; v2; v3; v4; v5; v6; v7]
    with ([v1] ++ [v2; v3; v4; v5; v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 7 sh tulong
    [v1] [v2;v3;v4;v5;v6;v7]
    (field_address0 (tarray tulong 8) (SUB 1) p) eq_refl eq_refl).
  change [v2; v3; v4; v5; v6; v7]
    with ([v2] ++ [v3; v4; v5; v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 6 sh tulong
    [v2] [v3;v4;v5;v6;v7]
    (field_address0 (tarray tulong 7) (SUB 1)
      (field_address0 (tarray tulong 8) (SUB 1) p)) eq_refl eq_refl).
  change [v3; v4; v5; v6; v7]
    with ([v3] ++ [v4; v5; v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 5 sh tulong
    [v3] [v4;v5;v6;v7]
    (field_address0 (tarray tulong 6) (SUB 1)
      (field_address0 (tarray tulong 7) (SUB 1)
        (field_address0 (tarray tulong 8) (SUB 1) p))) eq_refl eq_refl).
  change [v4; v5; v6; v7]
    with ([v4] ++ [v5; v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 4 sh tulong
    [v4] [v5;v6;v7]
    (field_address0 (tarray tulong 5) (SUB 1)
      (field_address0 (tarray tulong 6) (SUB 1)
        (field_address0 (tarray tulong 7) (SUB 1)
          (field_address0 (tarray tulong 8) (SUB 1) p)))) eq_refl eq_refl).
  change [v5; v6; v7] with ([v5] ++ [v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 3 sh tulong
    [v5] [v6;v7]
    (field_address0 (tarray tulong 4) (SUB 1)
      (field_address0 (tarray tulong 5) (SUB 1)
        (field_address0 (tarray tulong 6) (SUB 1)
          (field_address0 (tarray tulong 7) (SUB 1)
            (field_address0 (tarray tulong 8) (SUB 1) p))))) eq_refl eq_refl).
  change [v6; v7] with ([v6] ++ [v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 2 sh tulong
    [v6] [v7]
    (field_address0 (tarray tulong 3) (SUB 1)
      (field_address0 (tarray tulong 4) (SUB 1)
        (field_address0 (tarray tulong 5) (SUB 1)
          (field_address0 (tarray tulong 6) (SUB 1)
            (field_address0 (tarray tulong 7) (SUB 1)
              (field_address0 (tarray tulong 8) (SUB 1) p)))))) eq_refl eq_refl).

  (* --- Phase 2: Simplify subtraction remnants --- *)
  change (8-1) with 7.
  change (7-1) with 6.
  change (6-1) with 5.
  change (5-1) with 4.
  change (4-1) with 3.
  change (3-1) with 2.
  change (2-1) with 1.

  (* --- Phase 3: Convert all singleton arrays to plain data_at --- *)
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v0 [v0]
    p eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v1 [v1]
    (field_address0 (tarray tulong 8) (SUB 1) p) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v2 [v2]
    (field_address0 (tarray tulong 7) (SUB 1)
      (field_address0 (tarray tulong 8) (SUB 1) p)) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v3 [v3]
    (field_address0 (tarray tulong 6) (SUB 1)
      (field_address0 (tarray tulong 7) (SUB 1)
        (field_address0 (tarray tulong 8) (SUB 1) p))) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v4 [v4]
    (field_address0 (tarray tulong 5) (SUB 1)
      (field_address0 (tarray tulong 6) (SUB 1)
        (field_address0 (tarray tulong 7) (SUB 1)
          (field_address0 (tarray tulong 8) (SUB 1) p)))) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v5 [v5]
    (field_address0 (tarray tulong 4) (SUB 1)
      (field_address0 (tarray tulong 5) (SUB 1)
        (field_address0 (tarray tulong 6) (SUB 1)
          (field_address0 (tarray tulong 7) (SUB 1)
            (field_address0 (tarray tulong 8) (SUB 1) p))))) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v6 [v6]
    (field_address0 (tarray tulong 3) (SUB 1)
      (field_address0 (tarray tulong 4) (SUB 1)
        (field_address0 (tarray tulong 5) (SUB 1)
          (field_address0 (tarray tulong 6) (SUB 1)
            (field_address0 (tarray tulong 7) (SUB 1)
              (field_address0 (tarray tulong 8) (SUB 1) p)))))) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v7 [v7]
    (field_address0 (tarray tulong 2) (SUB 1)
      (field_address0 (tarray tulong 3) (SUB 1)
        (field_address0 (tarray tulong 4) (SUB 1)
          (field_address0 (tarray tulong 5) (SUB 1)
            (field_address0 (tarray tulong 6) (SUB 1)
              (field_address0 (tarray tulong 7) (SUB 1)
                (field_address0 (tarray tulong 8) (SUB 1) p))))))) eq_refl).

  (* --- Phase 4: Collapse nested field_address0 --- *)
  rewrite !field_address0_SUB_SUB by lia.
  change (1 + 1) with 2.
  change (1 + (1 + 1)) with 3.
  change (1 + (1 + (1 + 1))) with 4.
  change (1 + (1 + (1 + (1 + 1)))) with 5.
  change (1 + (1 + (1 + (1 + (1 + 1))))) with 6.
  change (1 + (1 + (1 + (1 + (1 + (1 + 1)))))) with 7.

  (* --- Phase 5: Normalize all addresses to offset_val --- *)
  rewrite !(arr_field_address0 tulong 8 p _ H) by lia.
  rewrite !(arr_field_address tulong 8 p _ H) by lia.
  simpl (sizeof tulong * _).
  rewrite isptr_offset_val_zero by solve_isptr.
  cancel.
Qed.

(** Unfold [data_at (tarray tulong 8)] into 8 individual [data_at]. *)
Lemma unfold_data_at_tulong_8 :
  forall (sh : share) (p : val) (v0 v1 v2 v3 v4 v5 v6 v7 : val),
  field_compatible (tarray tulong 8) [] p ->
  data_at sh (tarray tulong 8) [v0; v1; v2; v3; v4; v5; v6; v7] p
  |-- data_at sh tulong v0 (field_address (tarray tulong 8) (SUB 0) p) *
      data_at sh tulong v1 (field_address (tarray tulong 8) (SUB 1) p) *
      data_at sh tulong v2 (field_address (tarray tulong 8) (SUB 2) p) *
      data_at sh tulong v3 (field_address (tarray tulong 8) (SUB 3) p) *
      data_at sh tulong v4 (field_address (tarray tulong 8) (SUB 4) p) *
      data_at sh tulong v5 (field_address (tarray tulong 8) (SUB 5) p) *
      data_at sh tulong v6 (field_address (tarray tulong 8) (SUB 6) p) *
      data_at sh tulong v7 (field_address (tarray tulong 8) (SUB 7) p).
Proof.
  intros sh p v0 v1 v2 v3 v4 v5 v6 v7 H.

  (* --- Phase 1: Split the 8-element array into singletons --- *)
  change [v0; v1; v2; v3; v4; v5; v6; v7]
    with ([v0] ++ [v1; v2; v3; v4; v5; v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 8 sh tulong
    [v0] [v1;v2;v3;v4;v5;v6;v7] p eq_refl eq_refl).
  change [v1; v2; v3; v4; v5; v6; v7]
    with ([v1] ++ [v2; v3; v4; v5; v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 7 sh tulong
    [v1] [v2;v3;v4;v5;v6;v7]
    (field_address0 (tarray tulong 8) (SUB 1) p) eq_refl eq_refl).
  change [v2; v3; v4; v5; v6; v7]
    with ([v2] ++ [v3; v4; v5; v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 6 sh tulong
    [v2] [v3;v4;v5;v6;v7]
    (field_address0 (tarray tulong 7) (SUB 1)
      (field_address0 (tarray tulong 8) (SUB 1) p)) eq_refl eq_refl).
  change [v3; v4; v5; v6; v7]
    with ([v3] ++ [v4; v5; v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 5 sh tulong
    [v3] [v4;v5;v6;v7]
    (field_address0 (tarray tulong 6) (SUB 1)
      (field_address0 (tarray tulong 7) (SUB 1)
        (field_address0 (tarray tulong 8) (SUB 1) p))) eq_refl eq_refl).
  change [v4; v5; v6; v7]
    with ([v4] ++ [v5; v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 4 sh tulong
    [v4] [v5;v6;v7]
    (field_address0 (tarray tulong 5) (SUB 1)
      (field_address0 (tarray tulong 6) (SUB 1)
        (field_address0 (tarray tulong 7) (SUB 1)
          (field_address0 (tarray tulong 8) (SUB 1) p)))) eq_refl eq_refl).
  change [v5; v6; v7] with ([v5] ++ [v6; v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 3 sh tulong
    [v5] [v6;v7]
    (field_address0 (tarray tulong 4) (SUB 1)
      (field_address0 (tarray tulong 5) (SUB 1)
        (field_address0 (tarray tulong 6) (SUB 1)
          (field_address0 (tarray tulong 7) (SUB 1)
            (field_address0 (tarray tulong 8) (SUB 1) p))))) eq_refl eq_refl).
  change [v6; v7] with ([v6] ++ [v7]).
  setoid_rewrite (@split2_data_at_Tarray_app _ 1 2 sh tulong
    [v6] [v7]
    (field_address0 (tarray tulong 3) (SUB 1)
      (field_address0 (tarray tulong 4) (SUB 1)
        (field_address0 (tarray tulong 5) (SUB 1)
          (field_address0 (tarray tulong 6) (SUB 1)
            (field_address0 (tarray tulong 7) (SUB 1)
              (field_address0 (tarray tulong 8) (SUB 1) p)))))) eq_refl eq_refl).

  (* --- Phase 2: Simplify subtraction remnants --- *)
  change (8-1) with 7.
  change (7-1) with 6.
  change (6-1) with 5.
  change (5-1) with 4.
  change (4-1) with 3.
  change (3-1) with 2.
  change (2-1) with 1.

  (* --- Phase 3: Convert all singleton arrays to plain data_at --- *)
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v0 [v0] p eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v1 [v1]
    (field_address0 (tarray tulong 8) (SUB 1) p) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v2 [v2]
    (field_address0 (tarray tulong 7) (SUB 1)
      (field_address0 (tarray tulong 8) (SUB 1) p)) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v3 [v3]
    (field_address0 (tarray tulong 6) (SUB 1)
      (field_address0 (tarray tulong 7) (SUB 1)
        (field_address0 (tarray tulong 8) (SUB 1) p))) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v4 [v4]
    (field_address0 (tarray tulong 5) (SUB 1)
      (field_address0 (tarray tulong 6) (SUB 1)
        (field_address0 (tarray tulong 7) (SUB 1)
          (field_address0 (tarray tulong 8) (SUB 1) p)))) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v5 [v5]
    (field_address0 (tarray tulong 4) (SUB 1)
      (field_address0 (tarray tulong 5) (SUB 1)
        (field_address0 (tarray tulong 6) (SUB 1)
          (field_address0 (tarray tulong 7) (SUB 1)
            (field_address0 (tarray tulong 8) (SUB 1) p))))) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v6 [v6]
    (field_address0 (tarray tulong 3) (SUB 1)
      (field_address0 (tarray tulong 4) (SUB 1)
        (field_address0 (tarray tulong 5) (SUB 1)
          (field_address0 (tarray tulong 6) (SUB 1)
            (field_address0 (tarray tulong 7) (SUB 1)
              (field_address0 (tarray tulong 8) (SUB 1) p)))))) eq_refl).
  setoid_rewrite (@data_at_singleton_array_eq _ sh tulong v7 [v7]
    (field_address0 (tarray tulong 2) (SUB 1)
      (field_address0 (tarray tulong 3) (SUB 1)
        (field_address0 (tarray tulong 4) (SUB 1)
          (field_address0 (tarray tulong 5) (SUB 1)
            (field_address0 (tarray tulong 6) (SUB 1)
              (field_address0 (tarray tulong 7) (SUB 1)
                (field_address0 (tarray tulong 8) (SUB 1) p))))))) eq_refl).

  (* --- Phase 4: Collapse nested field_address0 --- *)
  rewrite !field_address0_SUB_SUB by lia.
  change (1 + 1) with 2.
  change (1 + (1 + 1)) with 3.
  change (1 + (1 + (1 + 1))) with 4.
  change (1 + (1 + (1 + (1 + 1)))) with 5.
  change (1 + (1 + (1 + (1 + (1 + 1))))) with 6.
  change (1 + (1 + (1 + (1 + (1 + (1 + 1)))))) with 7.

  (* --- Phase 5: Normalize all addresses to offset_val --- *)
  rewrite !(arr_field_address0 tulong 8 p _ H) by lia.
  rewrite !(arr_field_address tulong 8 p _ H) by lia.
  simpl (sizeof tulong * _).
  rewrite isptr_offset_val_zero by solve_isptr.
  cancel.
Qed.
