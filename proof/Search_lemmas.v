(** Scratch file to search for field_address / array lemmas *)
Require Import VST.floyd.proofauto.
Require Import scalar_4x64.scalar_4x64.
#[export] Instance CompSpecs' : compspecs. make_compspecs prog. Defined.

(* What lemmas rewrite field_address (tarray ...) (SUB 0) to the base pointer? *)
Search (field_address _ [ArraySubsc 0] _ = _).
Search (field_address _ (ArraySubsc 0 :: _) _ = _).

(* Is there a lemma saying field_address (tarray t n) (SUB 0) p = p ? *)
Search (field_address (tarray _ _) _ _ = _).

(* offset_val 0 *)
Search (offset_val 0 _ = _).

(* What about field_address0 vs field_address at index 0? *)
Search (field_address0 _ [ArraySubsc 0] _).
Search (field_address0 _ (ArraySubsc 0 :: _) _).
Search (field_address0 _ _ _ = field_address _ _ _).

(* Tarray element access *)
Search (data_at_ _ (tarray _ _) _ |-- data_at_ _ _ _).
Search (data_at_ _ (tarray _ _) _ = data_at_ _ _ _ * _).

(* Split an array into sub-arrays *)
Search "split2_data_at".
Search (data_at_ _ (tarray _ _) _ = _ * _).

(* field_address0 vs field_address *)
Search (field_address0 _ _ _ = field_address _ _ _).
Search field_address0 field_address.

(* Splitting an array data_at_ into first element + rest *)
Search "data__at_singleton".

(* arr_field_address *)
Search arr_field_address.

(* field_compatible for array subscript *)
Search (field_compatible (tarray _ _) [ArraySubsc _] _).
Search (field_compatible (tarray _ _) (SUB _) _).

(* field_address0 to offset_val *)
Search (field_address0 (tarray _ _) (SUB _) _ = offset_val _ _).
Search (field_address0 (tarray _ _) _ _ = _).

(* data_at_ array into list of data_at_ elements *)
Search "data_at__tarray_value".
Search (data_at_ _ (tarray _ _) _ = sepcon_list _).
Search (data_at_ _ (tarray _ _) _ |-- _ _ _).

(* How about rewriting field_address0 of a sub-array in terms of the parent? *)
Search field_address0_SUB_SUB.

(* ================================================================= *)
(* Additional searches for solving extract frame goals *)

(* Can we simplify nested field_address0 (tarray t (n-k)) (SUB 1) (field_address0 (tarray t n) (SUB k) p) ? *)
(* field_address0_SUB_SUB should do this *)

(* How does offset_val compose? *)
Search (offset_val _ (offset_val _ _)).

(* sizeof tulong *)
Eval compute in (sizeof tulong).

(* Can we cancel data_at with data_at_ in sep? *)
Search (data_at _ _ _ _ |-- data_at_ _ _ _).

(* field_address vs field_address0 when index is in range *)
Search (field_address0 _ _ _ = field_address _ _ _).

(* Useful: field_address0 at index 0 *)
Search (field_address0 _ (SUB 0) _).
Search (field_address0 _ [ArraySubsc 0] _).

(* data_at to data_at_ weakening *)
Search "data_at_data_at_".

(* Can we split a data_at (written element) from a data_at_ (uninitialized rest)? *)
Search (data_at _ _ _ _ * data_at_ _ _ _ |-- data_at_ _ _ _).

(* memory_block and data_at_ equivalence *)
Search (data_at_ _ _ _ = memory_block _ _ _).

(* Is there a tactic or lemma for splitting tarray into element + rest? *)
Search "split_array".
Search "array_at".

(* Check whether there is a general entailer for array element extraction *)
Search (data_at_ _ (tarray _ _) _ |-- _ * _).

(* field_compatible0 vs field_compatible *)
Search (field_compatible0 _ _ _ -> field_compatible _ _ _).
Search field_compatible0 field_compatible.

(* arr_field_address with specific sizeof *)
Check arr_field_address.
Check arr_field_address0.
Check field_address0_SUB_SUB.
Check split2_data_at__Tarray_app.
Check data__at_singleton_array_eq.

(* Can we find a tactic that does array frame solving? *)
Search "cancel".

(* data_at weakening to data_at_ *)
Check @data_at_data_at_.

(* offset_val arithmetic simplification *)
Search (offset_val _ (offset_val _ _) = _).

(* Are there any automation tactics for separating arrays? *)
Search "sep_apply".

(* field_address0 (tarray t n) (SUB 0) p = p ? *)
Goal forall (p : val),
  field_compatible (tarray tulong 8) [] p ->
  field_address0 (tarray tulong 8) (SUB 0) p = p.
Proof.
  intros.
  rewrite (arr_field_address0 tulong 8 p 0 H) by lia.
  simpl.
  (* offset_val 0 p = p needs isptr p *)
  apply isptr_offset_val_zero.
  destruct H as [? _]; destruct p; simpl in *; auto.
Qed.

(* Verify: for sub-array rest, can we chain field_address0_SUB_SUB? *)
(* e.g. field_address0 (tarray tulong 6) (SUB 1) (field_address0 (tarray tulong 8) (SUB 2) p)
        = field_address0 (tarray tulong 8) (SUB 3) p *)
Goal forall (p : val),
  field_address0 (tarray tulong 6) (SUB 1) (field_address0 (tarray tulong 8) (SUB 2) p)
  = field_address0 (tarray tulong 8) (SUB 3) p.
Proof.
  intros.
  rewrite field_address0_SUB_SUB by lia.
  reflexivity.
Qed.

(* Verify: the complete pattern for Goal 3 *)
(* Starting from: data_at_ sh (tarray tulong 6) (field_address0 (tarray tulong 7) (SUB 1) (offset_val 8 p))
   We want to get: data_at_ sh tulong (field_address (tarray tulong 8) (SUB 2) p) * data_at_ sh (tarray tulong 5) ... *)
(* Step 1: simplify nested field_address0 using field_address0_SUB_SUB *)
(* Step 2: rewrite field_address0 of parent to offset_val using arr_field_address0 *)
(* Step 3: split the 6-element sub-array with split2_data_at__Tarray_app *)
(* Step 4: use data__at_singleton_array_eq on the 1-element piece *)

(* Key insight: offset_val 8 p = field_address0 (tarray tulong 8) (SUB 1) p
   when field_compatible (tarray tulong 8) [] p, since sizeof tulong = 8 *)
Goal forall (p : val),
  field_compatible (tarray tulong 8) [] p ->
  offset_val 8 p = field_address0 (tarray tulong 8) (SUB 1) p.
Proof.
  intros. rewrite (arr_field_address0 tulong 8 p 1 H) by lia. reflexivity.
Qed.

(* So: field_address0 (tarray tulong 7) (SUB 1) (offset_val 8 p)
     = field_address0 (tarray tulong 7) (SUB 1) (field_address0 (tarray tulong 8) (SUB 1) p)
     = field_address0 (tarray tulong 8) (SUB 2) p *)
Goal forall (p : val),
  field_compatible (tarray tulong 8) [] p ->
  field_address0 (tarray tulong 7) (SUB 1) (offset_val 8 p)
  = field_address0 (tarray tulong 8) (SUB 2) p.
Proof.
  intros.
  change (offset_val 8 p) with (offset_val (sizeof tulong * 1) p).
  rewrite <- (arr_field_address0 tulong 8 p 1 H) by lia.
  rewrite field_address0_SUB_SUB by lia.
  reflexivity.
Qed.

(* Likewise for deeper nesting *)
Goal forall (p : val),
  field_compatible (tarray tulong 8) [] p ->
  field_address0 (tarray tulong 6) (SUB 1)
    (field_address0 (tarray tulong 7) (SUB 1) (offset_val 8 p))
  = field_address0 (tarray tulong 8) (SUB 3) p.
Proof.
  intros.
  change (offset_val 8 p) with (offset_val (sizeof tulong * 1) p).
  rewrite <- (arr_field_address0 tulong 8 p 1 H) by lia.
  rewrite !field_address0_SUB_SUB by lia.
  reflexivity.
Qed.

(* ================================================================= *)
(* Alternative approach: normalize everything to offset_val *)
(* This avoids field_address0_SUB_SUB entirely *)
(* ================================================================= *)

(* All field_address0 (tarray tulong N) (SUB k) p for parent array
   become offset_val (8 * k) p via arr_field_address0.
   All field_address (tarray tulong N) (SUB k) p
   become offset_val (8 * k) p via arr_field_address.
   Then nested field_address0 become offset_val compositions:
   offset_val j (offset_val i p) = offset_val (i + j) p
   by offset_offset_val. *)

(* Example: Normalize the third extraction point *)
Goal forall (p : val),
  field_compatible (tarray tulong 8) [] p ->
  field_address0 (tarray tulong 6) (SUB 1)
    (field_address0 (tarray tulong 7) (SUB 1) (offset_val 8 p))
  = offset_val 24 p.
Proof.
  intros.
  change (offset_val 8 p) with (offset_val (sizeof tulong * 1) p).
  rewrite <- (arr_field_address0 tulong 8 p 1 H) by lia.
  rewrite !field_address0_SUB_SUB by lia.
  (* After SUB_SUB: field_address0 (tarray tulong 8) (SUB (1+1+1)) p *)
  rewrite (arr_field_address0 _ _ _ _ H) by lia.
  reflexivity.
Qed.

(* And the parent field_address also normalizes: *)
Goal forall (p : val),
  field_compatible (tarray tulong 8) [] p ->
  field_address (tarray tulong 8) (SUB 3) p = offset_val 24 p.
Proof.
  intros. rewrite (arr_field_address tulong 8 p 3 H) by lia. reflexivity.
Qed.

(* ================================================================= *)
(* Summary of the recipe for solving extract frame goals:
   
   Given a goal of the form:
     ... * data_at_ sh (tarray tulong K) <nested_addr> * ...
     |-- data_at_ sh tulong (field_address (tarray tulong 8) (SUB N) p) * Frame
   
   Strategy:
   1. Normalize all addresses to offset_val:
      - rewrite (arr_field_address tulong 8 p N Hfc) for the RHS target
      - unfold field_address0; simpl; rewrite !offset_offset_val for LHS nested addrs
      (or use change + arr_field_address0 + field_address0_SUB_SUB)
   
   2. Split the K-element sub-array into 1 + (K-1):
      rewrite (split2_data_at__Tarray_app 1 K sh tulong <addr>) by lia
   
   3. Collapse the singleton:
      rewrite data__at_singleton_array_eq
   
   4. Let cancel/entailer! handle the rest.
   
   The key lemmas are:
   - arr_field_address    : field_address (tarray t n) (SUB i) p = offset_val (sizeof t * i) p
   - arr_field_address0   : field_address0 (tarray t n) (SUB i) p = offset_val (sizeof t * i) p
   - field_address0_SUB_SUB : collapses nested field_address0 into parent
   - offset_offset_val    : offset_val j (offset_val i v) = offset_val (i+j) v
   - split2_data_at__Tarray_app : splits data_at_ (tarray t n) into two pieces
   - data__at_singleton_array_eq : data_at_ sh (tarray t 1) p = data_at_ sh t p
   - data_at_data_at_     : data_at sh t v p |-- data_at_ sh t p (weakening)
*)

(* Diagnostic: check the exact types of arr_field_address0 and field_address0_SUB_SUB *)
Print arr_field_address0.
Print arr_field_address.
Check @field_address0_SUB_SUB.
About arr_field_address0.
About arr_field_address.

(* How to fold field_at entries back into data_at for arrays *)
Search (field_at _ (tarray _ _) (SUB _) _ _ * _ |-- data_at _ (tarray _ _) _ _).
Search "data_at_tarray".
Search "fold" "array".
Search (_ |-- data_at _ (tarray _ _) _ _).
Check @data_at_tarray_value_eq.
Check @split2_data_at_Tarray_app.
Print split2_data_at_Tarray_app.
Check @data_at_Tarray_split.
Check @data_at_singleton_array.
