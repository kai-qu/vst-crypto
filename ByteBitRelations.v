Require Import List. Import ListNotations.
Require Import Coq.ZArith.BinInt. (* Z *)
Require Import XorCorrespondence. (* Blist *)
Require Import Integers.          (* byte *)
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import HMAC_functional_prog_Z.

Require Import Coq.Strings.Ascii.
Require Import Coq.Program.Tactics.
Require Import Bruteforce.

Open Scope Z_scope.

(* ----- Inductive *)

(* In XorCorrespondence *)
(* Definition asZ (x : bool) : Z := if x then 1 else 0. *)

(*
Definition convertByteBits (bits : Blist) (byte : Z) : Prop :=
  exists (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
   bits = [b0; b1; b2; b3; b4; b5; b6; b7] /\
   byte =  (1 * (asZ b0) + 2 * (asZ b1) + 4 * (asZ b2) + 8 * (asZ b3)
         + 16 * (asZ b4) + 32 * (asZ b5) + 64 * (asZ b6) + 128 * (asZ b7)).
*)

Inductive bytes_bits_lists : Blist -> list Z -> Prop :=
  | eq_empty : bytes_bits_lists nil nil
  | eq_cons : forall (bits : Blist) (bytes : list Z)
                     (b0 b1 b2 b3 b4 b5 b6 b7 : bool) (byte : Z),
                bytes_bits_lists bits bytes ->
                convertByteBits [b0; b1; b2; b3; b4; b5; b6; b7] byte ->
                bytes_bits_lists (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bits)
                                 (byte :: bytes).

(* ----- Computational *)

(* TODO: assumes Z is positive and in range, does not use Z.positive *)

Definition div_mod (num : Z) (denom : Z) : bool * Z :=
  (Z.gtb (num / denom) 0, num mod denom).

Eval compute in div_mod 129 128.
Eval compute in div_mod 1 64.

Definition byteToBits (byte : Z) : Blist :=
  let (b7, rem7) := div_mod byte 128 in
  let (b6, rem6) := div_mod rem7 64 in
  let (b5, rem5) := div_mod rem6 32 in
  let (b4, rem4) := div_mod rem5 16 in
  let (b3, rem3) := div_mod rem4 8 in
  let (b2, rem2) := div_mod rem3 4 in
  let (b1, rem1) := div_mod rem2 2 in
  let (b0, rem0) := div_mod rem1 1 in
  [b0; b1; b2; b3; b4; b5; b6; b7].

Fixpoint bytesToBits (bytes : list Z) : Blist :=
  match bytes with
    | [] => []
    | byte :: xs => byteToBits byte ++ bytesToBits xs
  end.

Definition bitsToByte (bits : Blist) : Z :=
  match bits with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: nil =>
      1 * (asZ b0) + 2 * (asZ b1) + 4 * (asZ b2) + 8 * (asZ b3)
      + 16 * (asZ b4) + 32 * (asZ b5) + 64 * (asZ b6) + 128 * (asZ b7)
    | _ => -1                   (* should not happen *)
  end.

Fixpoint bitsToBytes (bits : Blist) : list Z :=
  match bits with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: xs =>
      bitsToByte [b0; b1; b2; b3; b4; b5; b6; b7] :: bitsToBytes xs
    | _ => []
  end.

(* -------------------- Various theorems and lemmas *)

Lemma bytes_bits_length : forall (bits : Blist) (bytes : list Z),
  bytes_bits_lists bits bytes -> length bits = (length bytes * 8)%nat.
Proof.
  intros bits bytes corr.
  induction corr.
  - reflexivity.
  - simpl. repeat f_equal. apply IHcorr.
Qed.

Lemma bytesToBits_app : forall (l1 l2 : list Z),
                          bytesToBits (l1 ++ l2) = bytesToBits l1 ++ bytesToBits l2.
Proof.
  induction l1; intros.
  * reflexivity.
  *
    simpl. rewrite -> IHl1. reflexivity.
Qed.    

Lemma bytesToBits_len : forall (l : list Z),
                          length (bytesToBits l) = (length l * 8)%nat.
Proof.
  induction l; intros; try reflexivity.
  -
    simpl.
    rewrite -> IHl.
    reflexivity.
Qed.    

(* Prove by brute force (test all Z in range) *)
Theorem byte_bit_byte_id : forall (byte : Z),
                             0 <= byte < 256 ->
                                bitsToByte (byteToBits byte) = byte.
Proof.
  intros byte range.
  do_range range reflexivity.
Qed.

Theorem bits_byte_bits_id : forall (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
                              [b0; b1; b2; b3; b4; b5; b6; b7] =
                              byteToBits (bitsToByte [b0; b1; b2; b3; b4; b5; b6; b7]).
Proof.
  intros.
  destruct b0; destruct b1; destruct b2; destruct b3;
  destruct b4; destruct b5; destruct b6; destruct b7;
  reflexivity.
Qed.

Theorem bytes_bits_bytes_id : forall (bytes : list Z),
                                Forall (fun b => 0 <= b < 256) bytes ->
                                bitsToBytes (bytesToBits bytes) = bytes.
Proof.
  intros range bytes.
  induction bytes as [ | byte bytes].
  - reflexivity.
  -
    unfold bytesToBits.
    fold bytesToBits.
    unfold byteToBits.
    unfold bitsToBytes.
    Opaque bitsToByte. Opaque bitsToBytes. Opaque bytesToBits.
    simpl.
    Transparent bitsToBytes. fold bitsToBytes.
    rewrite -> IHbytes.
    
    Transparent bitsToByte.
    unfold bitsToByte. f_equal.
    apply byte_bit_byte_id.
    
    apply H. Transparent bytesToBits.
Qed.

Close Scope string_scope.

(* ------------------ Theorems relating inductive and computational definitions *)

Theorem bytes_bits_def_eq : forall (bytes : list Z),
                              Forall (fun b => 0 <= b < 256) bytes ->
                              bytes_bits_lists (bytesToBits bytes) bytes.
Proof.
  intros range bytes.
  induction bytes as [ | byte bytes ].
  -
    simpl. apply eq_empty.
  -
    apply eq_cons.

    *
      apply IHbytes.
    *
      unfold convertByteBits.
      do 8 eexists.
      split.
      +
        reflexivity.
      +
        do_range H reflexivity.
Qed.

Theorem bytes_bits_comp_ind : forall (bits : Blist) (bytes : list Z),
                               Forall (fun b => 0 <= b < 256) bytes ->
                               bits = bytesToBits bytes ->
                               bytes_bits_lists bits bytes.
Proof.
  intros bits bytes range corr.
  rewrite -> corr.
  apply bytes_bits_def_eq.
  assumption.
Qed.

Theorem bytes_bits_ind_comp : forall (bits : Blist) (bytes : list Z),
                                 Forall (fun b => 0 <= b < 256) bytes ->
                                 bytes_bits_lists bits bytes ->
                                 bytes = bitsToBytes bits.
Proof.
  intros bits bytes range corr.
  induction corr.
  - reflexivity.
  -
    rewrite -> IHcorr.
    *
      unfold convertByteBits in H.
      unfold bitsToBytes.
      fold bitsToBytes.
      f_equal.

      assert (range' : 0 <= byte < 256). admit.

      unfold bitsToByte.
      Print convertByteBits.
      destruct_exists. destruct H7. inversion H7.
      subst. reflexivity.

      * admit.                  (* bytes in range *)
Qed.

Theorem bits_bytes_ind_comp : forall (bits : Blist) (bytes : list Z),
                                 Forall (fun b => 0 <= b < 256) bytes ->
                                 bytes_bits_lists bits bytes ->
                                 bits = bytesToBits bytes.
Proof.
  intros bits bytes range corr.
  induction corr.
  - reflexivity.
  -
    unfold convertByteBits in H.
    destruct_exists.
    destruct H7.
    inversion H7.
    subst.
    clear H7.
    rewrite -> IHcorr.
    unfold bytesToBits.
    fold bytesToBits.
    assert (list_8 : forall {A : Type} (e0 e1 e2 e3 e4 e5 e6 e7 : A) (l : list A),
                       e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: e7 :: l =
                       [e0; e1; e2; e3; e4; e5; e6; e7] ++ l).
    reflexivity.
    rewrite -> list_8.
    f_equal.
    apply bits_byte_bits_id.

    admit.                      (* in range *)
Qed.
    