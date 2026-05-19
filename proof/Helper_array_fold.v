(** * Helper_array_fold: Equality between an array [data_at] and the
      sepcon of its element-wise [data_at]s.

    When VST's [forward] processes stores into array slots one at a time,
    the proof state ends up with N separate [data_at sh tulong vi ...]
    predicates.  The postcondition wants one
    [data_at sh (tarray tulong 8) [v0; ...; v7] p].

    A single equality lemma covers both directions; [rewrite] picks. *)

(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

Require Import scalar_4x64.Verif_imports.

Local Open Scope logic.

(* ================================================================= *)
(** ** Generic decomposition for arbitrary-length arrays *)

Section ArrayIter.
Context {cs : compspecs}.

(** Iterated [data_at] over a list of values, stepping by [sizeof t] each
    element.  Right-associated, terminating in [emp]. *)
Fixpoint iter_data_at_offset (sh : share) (t : type) (p : val)
                             (vs : list (reptype t)) {struct vs} : mpred :=
  match vs with
  | [] => emp
  | v :: vs' => data_at sh t v p
              * iter_data_at_offset sh t (offset_val (sizeof t) p) vs'
  end.

(** Split one element off the front of an array. *)
Lemma data_at_tarray_cons :
  forall sh t v (vs : list (reptype t)) p,
    field_compatible (tarray t (Z.succ (Zlength vs))) [] p ->
    data_at sh (tarray t (Z.succ (Zlength vs))) (v :: vs) p =
    data_at sh t v p *
    data_at sh (tarray t (Zlength vs)) vs (offset_val (sizeof t) p).
Proof.
  intros.
  change (v :: vs) with ([v] ++ vs).
  rewrite (split2_data_at_Tarray_app 1 (Z.succ (Zlength vs)) sh t [v] vs p)
    by (rewrite ?Zlength_cons, ?Zlength_nil; lia).
  rewrite (data_at_singleton_array_eq sh t v [v] p eq_refl).
  replace (Z.succ (Zlength vs) - 1) with (Zlength vs) by lia.
  rewrite (arr_field_address0 t (Z.succ (Zlength vs)) p 1 H)
    by (pose proof (Zlength_nonneg vs); lia).
  rewrite Z.mul_1_r.
  reflexivity.
Qed.

(** Shifting [field_compatible] one cell to the right. *)
Lemma field_compatible_tarray_shift :
  forall t k p,
    0 < k ->
    field_compatible (tarray t k) [] p ->
    field_compatible (tarray t (k - 1)) [] (offset_val (sizeof t) p).
Proof.
  intros t k p Hk Hfc.
  pose proof (proj1 (field_compatible_Tarray_split t 1 k p ltac:(lia)) Hfc)
    as [_ Hfc'].
  rewrite (arr_field_address0 t k p 1 Hfc) in Hfc' by lia.
  rewrite Z.mul_1_r in Hfc'. exact Hfc'.
Qed.

(** Main theorem: the array [data_at] equals the iterated form. *)
Lemma data_at_tarray_iter_offset :
  forall sh t (vs : list (reptype t)) p,
    field_compatible (tarray t (Zlength vs)) [] p ->
    data_at sh (tarray t (Zlength vs)) vs p = iter_data_at_offset sh t p vs.
Proof.
  intros sh t vs. induction vs as [|v vs' IH]; intros p Hfc;
    cbn [iter_data_at_offset].
  - rewrite Zlength_nil in *.
    destruct Hfc as [Hptr [Hcosu _]]. cbn in Hcosu.
    apply data_at_zero_array_eq; auto.
  - rewrite Zlength_cons in *.
    rewrite data_at_tarray_cons by auto.
    f_equal. apply IH.
    pose proof (Zlength_nonneg vs').
    apply field_compatible_tarray_shift in Hfc; [|lia].
    replace (Z.succ (Zlength vs') - 1) with (Zlength vs') in Hfc by lia.
    exact Hfc.
Qed.

(** Same iteration but with [field_address] in place of raw [offset_val] —
    matches the form produced by VST's [forward] on array stores. *)
Fixpoint iter_data_at_at (sh : share) (t : type) (n : Z) (p : val) (i : Z)
                         (vs : list (reptype t)) {struct vs} : mpred :=
  match vs with
  | [] => emp
  | v :: vs' => data_at sh t v (field_address (tarray t n) (SUB i) p)
              * iter_data_at_at sh t n p (Z.succ i) vs'
  end.

(** Bridge: the offset-stepping iter equals the indexed iter when [p] is
    field-compatible. *)
Lemma iter_data_at_offset_eq_at :
  forall sh t (vs : list (reptype t)) n i p,
    field_compatible (tarray t n) [] p ->
    0 <= i -> i + Zlength vs <= n ->
    iter_data_at_offset sh t (offset_val (sizeof t * i) p) vs =
    iter_data_at_at sh t n p i vs.
Proof.
  intros sh t vs. induction vs as [|v vs' IH]; intros n i p Hfc Hi Hsum;
    cbn [iter_data_at_offset iter_data_at_at]; [reflexivity|].
  rewrite Zlength_cons in *.
  pose proof (Zlength_nonneg vs').
  rewrite (arr_field_address t n p i Hfc) by lia.
  f_equal.
  rewrite offset_offset_val.
  rewrite <- Z.mul_succ_r.
  apply IH; [auto | lia | lia].
Qed.

(** Indexed iter form of the main theorem. *)
Lemma data_at_tarray_iter_at :
  forall sh t (vs : list (reptype t)) p,
    field_compatible (tarray t (Zlength vs)) [] p ->
    data_at sh (tarray t (Zlength vs)) vs p =
    iter_data_at_at sh t (Zlength vs) p 0 vs.
Proof.
  intros sh t vs p Hfc.
  rewrite data_at_tarray_iter_offset by auto.
  pose proof (Zlength_nonneg vs).
  rewrite <- (iter_data_at_offset_eq_at sh t vs (Zlength vs) 0 p) by (auto || lia).
  rewrite Z.mul_0_r.
  rewrite isptr_offset_val_zero by (destruct Hfc as [? _]; auto).
  reflexivity.
Qed.

(** Same as [data_at_tarray_iter_at] with [n] introduced as a separate parameter,
    so callers don't need to massage [Zlength vs] into position. *)
Lemma data_at_tarray_iter_at' :
  forall sh t (vs : list (reptype t)) n p,
    Zlength vs = n ->
    field_compatible (tarray t n) [] p ->
    data_at sh (tarray t n) vs p = iter_data_at_at sh t n p 0 vs.
Proof. intros. subst. apply data_at_tarray_iter_at; auto. Qed.

(** Uninitialized variant: equality for [data_at_] over a [tarray]. *)
Lemma data_at__tarray_iter_at :
  forall sh t n p,
    0 <= n ->
    field_compatible (tarray t n) [] p ->
    data_at_ sh (tarray t n) p =
    iter_data_at_at sh t n p 0 (Zrepeat (default_val t) n).
Proof.
  intros sh t n p Hn Hfc.
  rewrite data_at__tarray.
  apply data_at_tarray_iter_at'; [apply Zlength_Zrepeat; lia | auto].
Qed.

End ArrayIter.

(* ================================================================= *)
(** ** Size-8 [sep_apply]-friendly entailment wrappers *)

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
  rewrite (data_at_tarray_iter_at' sh tulong
            [v0;v1;v2;v3;v4;v5;v6;v7] 8 p eq_refl H).
  cbn [iter_data_at_at]. cancel.
Qed.

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
  intros.
  rewrite (data_at__tarray_iter_at sh tulong 8 p ltac:(lia) H).
  cbn [iter_data_at_at Zrepeat repeat Z.to_nat Pos.to_nat Pos.iter_op
       Nat.add].
  change (data_at sh tulong (default_val tulong))
    with (data_at_ sh tulong).
  cancel.
Qed.
