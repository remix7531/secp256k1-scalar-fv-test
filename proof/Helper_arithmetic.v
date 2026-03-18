(** * Helper_arithmetic: General 4×4 limb schoolbook multiplication correctness *)
(** This is a pure Z lemma, completely independent of VST, secp256k1,
    or any specific word size.  It states that the standard
    accumulate-extract-carry schoolbook algorithm correctly computes
    the product of two 4-limb numbers into 8 limbs.

    We use Z rather than N because [lia]/[nia] are weaker over N,
    and key stdlib lemmas ([Z.div_mod_eq], [Z.mod_pos_bound],
    [Z.div_le_mono], etc.) lack mature N counterparts.  Staying
    in Z also avoids coercion noise at the VST/CompCert call sites
    which represent all machine integers as Z. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Open Scope Z_scope.

(** Convert a 4-limb little-endian representation to a value. *)
Definition eval4 (B : Z) (a0 a1 a2 a3 : Z) : Z :=
  a0 + a1 * B + a2 * B^2 + a3 * B^3.

(** Convert an 8-limb little-endian representation to a value. *)
Definition eval8 (B : Z) (r0 r1 r2 r3 r4 r5 r6 r7 : Z) : Z :=
  r0 + r1 * B + r2 * B^2 + r3 * B^3 + r4 * B^4 + r5 * B^5 + r6 * B^6 + r7 * B^7.

(** Limb extraction: the [i]-th limb of [x] in base [B]. *)
Definition limb (B : Z) (x : Z) (i : nat) : Z :=
  (x / B ^ Z.of_nat i) mod B.

(** A value in [0, B^4) is equal to its 4-limb reconstruction. *)
Lemma eval4_limbs : forall B x,
  B > 1 -> 0 <= x < B^4 ->
  eval4 B (limb B x 0) (limb B x 1) (limb B x 2) (limb B x 3) = x.
Proof.
Admitted.

(** The main theorem: schoolbook 4×4 multiplication.

    Given base [B > 1], limbs [a0..a3] and [b0..b3] in [0, B),
    the accumulate-and-carry algorithm produces limbs [r0..r7]
    such that [eval8 B r0..r7 = eval4 B a0..a3 * eval4 B b0..b3].

    The algorithm is defined by:
    - Round k: accumulate all cross-products aᵢ·bⱼ with i+j=k
      into the carry from the previous round, then extract the
      low limb (mod B) and carry (div B).
*)
Lemma schoolbook_mul_4x4 :
  forall (B : Z),
  B > 1 ->
  forall (a0 a1 a2 a3 b0 b1 b2 b3 : Z),
  0 <= a0 < B -> 0 <= a1 < B -> 0 <= a2 < B -> 0 <= a3 < B ->
  0 <= b0 < B -> 0 <= b1 < B -> 0 <= b2 < B -> 0 <= b3 < B ->
  (* Round 0: acc0 = a0*b0 *)
  forall (acc0 : Z),
  acc0 = a0 * b0 ->
  forall (carry0 : Z),
  carry0 = acc0 / B ->
  (* Round 1: acc1 = carry0 + a0*b1 + a1*b0 *)
  forall (acc1 : Z),
  acc1 = carry0 + a0 * b1 + a1 * b0 ->
  forall (carry1 : Z),
  carry1 = acc1 / B ->
  (* Round 2: acc2 = carry1 + a0*b2 + a1*b1 + a2*b0 *)
  forall (acc2 : Z),
  acc2 = carry1 + a0 * b2 + a1 * b1 + a2 * b0 ->
  forall (carry2 : Z),
  carry2 = acc2 / B ->
  (* Round 3: acc3 = carry2 + a0*b3 + a1*b2 + a2*b1 + a3*b0 *)
  forall (acc3 : Z),
  acc3 = carry2 + a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0 ->
  forall (carry3 : Z),
  carry3 = acc3 / B ->
  (* Round 4: acc4 = carry3 + a1*b3 + a2*b2 + a3*b1 *)
  forall (acc4 : Z),
  acc4 = carry3 + a1 * b3 + a2 * b2 + a3 * b1 ->
  forall (carry4 : Z),
  carry4 = acc4 / B ->
  (* Round 5: acc5 = carry4 + a2*b3 + a3*b2 *)
  forall (acc5 : Z),
  acc5 = carry4 + a2 * b3 + a3 * b2 ->
  forall (carry5 : Z),
  carry5 = acc5 / B ->
  (* Round 6: acc6 = carry5 + a3*b3 *)
  forall (acc6 : Z),
  acc6 = carry5 + a3 * b3 ->
  forall (carry6 : Z),
  carry6 = acc6 / B ->
  (* Conclusion: the 8 extracted limbs equal the product limb-by-limb *)
  let r0 := acc0 mod B in
  let r1 := acc1 mod B in
  let r2 := acc2 mod B in
  let r3 := acc3 mod B in
  let r4 := acc4 mod B in
  let r5 := acc5 mod B in
  let r6 := acc6 mod B in
  let r7 := carry6 mod B in
  let product := eval4 B a0 a1 a2 a3 * eval4 B b0 b1 b2 b3 in
  r0 = product mod B /\
  r1 = (product / B) mod B /\
  r2 = (product / B^2) mod B /\
  r3 = (product / B^3) mod B /\
  r4 = (product / B^4) mod B /\
  r5 = (product / B^5) mod B /\
  r6 = (product / B^6) mod B /\
  r7 = (product / B^7) mod B.
Proof.
Admitted.
