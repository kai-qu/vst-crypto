(* admits: 14 + 1 (generate_and_pad)

- front ~ FRONT, back ~ BACK

- generate_and_pad
- SHA proofs related to generate_and_pad
- in SHA, need to prove that pad -> InBlocks 512 and pad' -> InBlocks 16

- range: bytes in range, pad + intlist_to_Zlist preserve in range, fix the Forall

*)

Set Implicit Arguments.

(* Require Import Bvector. *)
Require Import List.
Require Import Arith.

Require Import HMAC_functional_prog_Z.
Require Import Integers.
Require Import Coqlib.
Require Import sha_padding_lemmas.
Require Import functional_prog.
Require Import hmac_common_lemmas.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Strings.String.
Require Import SHA256.
Require Import XorCorrespondence.
Require Import Bruteforce.

Require Import Coq.Program.Basics. (* for function composition: ∘ *)
Local Open Scope program_scope.

Require Import List. Import ListNotations.

(* In XorCorrespondence *)
(* Definition Blist := list bool. *)

Definition splitList {A : Type} (h : nat) (t : nat) (l : list A) : (list A * list A) :=
  (firstn h l, skipn t l).

Definition concat {A : Type} (l : list (list A)) : list A :=
  flat_map id l.


(* TODO: length proofs (length xs = length ys) *)
Definition BLxor (xs : Blist) (ys : Blist) :=
  map (fun p => xorb (fst p) (snd p)) (combine xs ys).

Print fold_left.
(*
Function hash_blocks (r: registers) (msg: list int) {measure length msg} : registers :=
  match msg with
  | nil => r
  | _ => hash_blocks (hash_block r (firstn 16 msg)) (skipn 16 msg)
  end.
Proof. intros.
 destruct (lt_dec (length msg) 16).
 rewrite skipn_length_short. simpl; omega. rewrite <- teq; auto.
 rewrite skipn_length. simpl; omega. rewrite <- teq; omega.
Defined.
*)
(* block size 512, possibly use take 512 l instead, though it might be harder to prove things about *)
Function hash_blocks_bits (hash_block_bit : Blist -> Blist -> Blist) (r: Blist)
         (msg: Blist) {measure length msg} : Blist :=
  match msg with
  | nil => r
  | _ => hash_blocks_bits hash_block_bit (hash_block_bit r (firstn 512 msg)) (skipn 512 msg)
  end.
Proof. intros.
 destruct (lt_dec (length msg) 512).
 rewrite skipn_length_short. simpl; omega. rewrite <- teq; auto.
 rewrite skipn_length. simpl; omega. rewrite <- teq; omega.
Defined.

Lemma firstn_exact : 
  forall {A : Type} (l1 l2 : list A) (n : nat),
    (length l1 = n)%nat -> firstn n (l1 ++ l2) = l1.
Proof.
  induction l1; destruct n; intros; simpl; try reflexivity; inversion H.
  * f_equal. apply IHl1. reflexivity.
Qed.    

Lemma skipn_exact :
  forall {A : Type} (l1 l2 : list A) (n : nat),
    (length l1 = n)%nat -> skipn n (l1 ++ l2) = l2.
Proof.
  induction l1; destruct n; intros; simpl; try reflexivity; inversion H.
  * apply IHl1. reflexivity.
Qed.

Section HMAC.

(* b = block size
   c = digest (output) size
   p = padding = b - c (fixed) *)
  Variable c p : nat.
  Definition b := (c + p)%nat.

  (* The compression function *)
  Variable h : Blist -> Blist -> Blist.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Blist.
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Print fold_left.
  Locate fold_left.

  Definition h_star k (m : Blist) :=
    hash_blocks_bits h k m.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  (* Check hash_words. *)
  Check h_star.

  (* NOTE: this is the new design without fpad TODO *)
  (* NOTE: this is the new design with concat and with two hash_words_padded *)
  (* Variable splitAndPad : Blist -> list (Blist). *)
  Variable splitAndPad : Blist -> Blist.

  Definition hash_words_padded : Blist -> Blist :=
    hash_words ∘ splitAndPad.

  (* ----- *)

  Hypothesis splitAndPad_1_1 :
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.

  (* constant-length padding. *)
  Variable fpad : Blist.

  Definition app_fpad (x : Blist) : Blist :=
    x ++ fpad.
  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  (* TODO fix this *)
  Definition GNMAC k m :=
    let (k_Out, k_In) := splitList c c k in
    h k_Out (h_star_pad k_In m). (* could take head of list *)

  Check GNMAC.
  (*  list bool -> list Blist -> Blist *)
  Check h.
  (* Blist -> Blist -> Blist *)

Check hash_words.               (* list Blist -> Blist *)

  (* The "two-key" version of GHMAC and HMAC. *)
  (* Concatenate (K xor opad) and (K xor ipad) *)
  Definition GHMAC_2K (k : Blist) m :=
    let (k_Out, k_In) := splitList b b k in (* concat earlier, then split *)
      let h_in := (hash_words_padded (k_In ++ m)) in
        hash_words_padded (k_Out ++ h_in).

  Definition HMAC_2K (k : Blist) (m : Blist) :=
    (* GHMAC_2K k (splitAndPad m). *)
    GHMAC_2K k m.

Check HMAC_2K.
(* Blist -> Blist -> Blist *)

(* opad and ipad are constants defined in the HMAC spec. *)
Variable opad ipad : Blist.

Print BLxor.

Definition GHMAC (k : Blist) :=
  GHMAC_2K (BLxor k opad ++ BLxor k ipad).

Definition HMAC (k : Blist) :=
  HMAC_2K (BLxor k opad ++ BLxor k ipad).

Check HMAC.

End HMAC.

(* ----------------------------------- DEFINITIONS *)

Module Equiv.

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

Definition byte_to_64list (byte : byte) : list Z :=
   map Byte.unsigned (HMAC_SHA256.sixtyfour byte).

Definition Z_to_64list (num : Z) : list Z :=
   HMAC_SHA256.sixtyfour num.

(* ----- Computational *)

(* byte = Z (not byte type), bit = bool *)
(* endianness: TODO *)

(* bytes to bits *)

(* TODO: assumes Z is positive and in range, does not use Z.positive
-- does this make the following proofs false? *)

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

Fixpoint bitsToBytes' (bits : Blist) : list Z :=
  match bits with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: xs =>
      let byte := 1 * (asZ b0) + 2 * (asZ b1) + 4 * (asZ b2) + 8 * (asZ b3)
         + 16 * (asZ b4) + 32 * (asZ b5) + 64 * (asZ b6) + 128 * (asZ b7) in
      byte :: bitsToBytes xs
    | _ => []
  end.


Require Import Coq.Strings.Ascii.
Require Import Coq.Program.Tactics.

Open Scope string_scope.

Definition asStr (x : bool) : string := if x then "1" else "0".

Definition toStr (bits : Blist) : list string :=
  map asStr bits.

Eval compute in toStr (bytesToBits [8]).
Eval compute in toStr (bytesToBits [127]).
Eval compute in toStr (bytesToBits [128]).
Eval compute in toStr (bytesToBits [255]).

Lemma bytes_bits_length : forall (bits : Blist) (bytes : list Z),
  bytes_bits_lists bits bytes -> length bits = (length bytes * 8)%nat.
Proof.
  intros bits bytes corr.
  induction corr.
  - reflexivity.
  - simpl. repeat f_equal. apply IHcorr.
Qed.

(* Prove by brute force (test all Z in range) *)
Theorem byte_bit_byte_id : forall (byte : Z),
                             0 <= byte < 256 ->
                                bitsToByte (byteToBits byte) = byte.
Proof.
  intros byte range.
  do_range range reflexivity.
Qed.
(* TODO move this into a different file; takes a while to check *)

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

(* ------- *)

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

(* unsure if this one is easier than the previous *)
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

Lemma bytesToBits_app : forall (l1 l2 : list Z),
                          bytesToBits (l1 ++ l2) = bytesToBits l1 ++ bytesToBits l2.
Proof.
  induction l1; intros.
  * reflexivity.
  *
    simpl. rewrite -> IHl1. reflexivity.
Qed.    


(* ----------------------------------------------- *)

Check HMAC.

(* HMAC
     : nat ->
       nat ->
       (Blist -> Blist -> Blist) ->
       Blist ->
       (Blist -> list Blist) -> Blist -> Blist -> Blist -> Blist -> Blist *)

(*
Parameter sha_iv : Bvector (SHA256_.DigestLength * 8).
Parameter sha_h : Bvector c -> Bvector (c + p) -> Bvector c.
Parameter sha_splitandpad_vector :
  Blist -> list (Bvector (SHA256_.DigestLength * 8 + p)).

(* Parameter fpad : Bvector p. *)
*)

Definition c:nat := (SHA256_.DigestLength * 8)%nat.
Definition p:=(32 * 8)%nat.

Definition sha_iv : Blist :=
  bytesToBits (SHA256.intlist_to_Zlist SHA256.init_registers).

Check SHA256.hash_blocks.       (* SHA256.registers -> list int -> SHA256.registers *)
Definition sha_h (regs : Blist) (block : Blist) : Blist :=
  bytesToBits (SHA256.intlist_to_Zlist
                 (SHA256.hash_block (SHA256.Zlist_to_intlist (bitsToBytes regs))
                                     (SHA256.Zlist_to_intlist (bitsToBytes block))
              )).

(* Parameter sha_splitandpad : Blist -> Blist. *)
Definition sha_splitandpad (msg : Blist) : Blist :=
  bytesToBits (sha_padding_lemmas.pad (bitsToBytes msg)).

(* -------------------------------------------------------- LEMMAS *)

(* Lemma 1: ++ equivalence on list *)
(* Lemma 2: xor equivalence on list *)
(* Lemma 3: SHA (iterated hash) equivalence on list *)

Lemma concat_equiv :
  forall (l1 : Blist) (l2 : list Z) (m1 : Blist) (m2 : list Z),
    bytes_bits_lists l1 l2
    -> bytes_bits_lists m1 m2
    -> bytes_bits_lists (l1 ++ m1) (l2 ++ m2).
(* bytes_bits_lists l1 l2 -> bytes_bits_lists m1 m2 -> bytes_bits_lists (l1 ++ m1) (l2 ++ m2) *)
Proof.
  intros l1 l2 m1 m2.
  intros fst_eq snd_eq.
  generalize dependent m1. generalize dependent m2.
  induction fst_eq; intros.
  - repeat rewrite app_nil_l.
    apply snd_eq.
  - simpl.
    apply eq_cons.
    + apply IHfst_eq.
      apply snd_eq.
    + apply H.
Qed.

(* --------------------------------- *)

SearchAbout length.
Check splitList.
Eval compute in splitList 0%nat 0%nat [].

Lemma split_append_id : forall {A : Type} (len : nat) (l1 l2 : list A),
                               length l1 = len -> length l2 = len ->
                               splitList len len (l1 ++ l2) = (l1, l2).
Proof.
  induction len; intros l1 l2 len1 len2.
  -
    assert (H: forall {A : Type} (l : list A), length l = 0%nat -> l = []).
      intros. destruct l.
      reflexivity. inversion H.
    apply H in len1. apply H in len2.
    subst. reflexivity.
  -
    unfold splitList.
    rewrite -> firstn_exact. rewrite -> skipn_exact.
    * reflexivity. * assumption. * assumption.
Qed.

(* ------- *)

(* Lemma 2 *)

(* Prove that the inner xor lemma is true on at least one example *)
Section Example.

 Definition k:Blist := concat (list_repeat 64 [true; true; false; false; true; false; true; true]).
 Definition K:list Z := list_repeat 64 211.

 Lemma conv : convertByteBits [true; true; false; false; true; false; true; true] 211.
   repeat eexists.
  (* eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists. *)
  (* split. reflexivity. simpl. reflexivity. *)
 Qed.
 Lemma kKcorrect: bytes_bits_lists k K.
   unfold K, k. simpl.
   repeat constructor; try apply conv.
  Qed.


 Definition ip:Blist := concat (list_repeat 64 [false; true; false; false; true; false; true; true]).
 Definition IP:Z := 210.
 Transparent Byte.repr.

 Lemma ip_conv : convertByteBits [false; true; false; false; true; false; true; true] 210.
   repeat eexists.
 Qed.
 Lemma ipcorrect: bytes_bits_lists ip (HMAC_SHA256.sixtyfour IP).
   unfold ip, IP. simpl. unfold byte_to_64list, HMAC_SHA256.sixtyfour. simpl.
   repeat constructor; try apply ip_conv.
  Qed.

Lemma ONE: convertByteBits [true; false; false; false; false; false; false; false] 1.
  repeat eexists. Qed.

Lemma inner_fst_equiv_example : exists k (ip  : Blist) K (IP : Z),
                          ((length K) * 8)%nat = (c + p)%nat /\
                          Zlength K = Z.of_nat SHA256_.BlockSize /\
                          (* TODO: first implies this *)
                          bytes_bits_lists k K /\
                          bytes_bits_lists ip (HMAC_SHA256.sixtyfour IP) /\
                          bytes_bits_lists (BLxor k ip)
                                           ((HMAC_SHA256.mkArg (HMAC_SHA256.mkKey K) IP)).

Proof.
  exists k, ip, K, IP. repeat split.
   apply kKcorrect. apply ipcorrect.
  unfold k, K, ip, IP. simpl. unfold BLxor. simpl.
  repeat constructor; apply ONE.
Qed.

(* See XorCorrespondence.v *)

Lemma inner_general_map : forall (ip : Blist) (IP_list : list Z) (k : Blist) (K : list Z),
                            bytes_bits_lists ip IP_list ->
                            bytes_bits_lists k K ->
     bytes_bits_lists (BLxor k ip)
                      (map (fun p0 : Z * Z => Z.lxor (fst p0) (snd p0))
                           (combine K IP_list)).
Proof.
  intros ip IP_list k K ip_eq k_eq.
  unfold BLxor. simpl.
  generalize dependent ip. generalize dependent IP_list.
  induction k_eq; intros.
  - simpl. constructor.
  -
    induction ip_eq.
    +
      simpl. constructor.
    +
      simpl.
      constructor.
      * apply IHk_eq.
        apply ip_eq.            (* ??? *)
      *
        apply xor_correspondence.
        apply H. apply H0.
Qed.

Lemma xor_equiv_Z : forall (xpad  : Blist) (XPAD : Z)
                                           (k : Blist) (K : list Z),
                          bytes_bits_lists xpad (HMAC_SHA256.sixtyfour XPAD) ->
                          ((length K) * 8)%nat = (c + p)%nat ->
                          Zlength K = Z.of_nat SHA256_.BlockSize ->
                          (* TODO: first implies this *)
                          bytes_bits_lists k K ->
                          bytes_bits_lists (BLxor k xpad)
       (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey K) XPAD).
Proof.
  intros xpad XPAD k K.
  intros xpad_equiv len_k zlen_k k_equiv.
  unfold HMAC_SHA256.mkArg, HMAC_SHA256.mkKey.
  Opaque HMAC_SHA256.sixtyfour.
  simpl. rewrite zlen_k. simpl. unfold HMAC_SHA256.zeroPad.
  assert (byte_key_length_blocksize: length K = 64%nat).
    * unfold p, c in *. simpl in *. omega.
  *
    rewrite byte_key_length_blocksize.  simpl.  rewrite app_nil_r.
    apply inner_general_map.

  - apply xpad_equiv.
  - apply k_equiv.
Qed.

Eval compute in Byte.xor (Byte.repr 0) (Byte.repr 100).
Eval compute in Byte.xor (Byte.repr 100) (Byte.repr 100).
Eval compute in Byte.xor (Byte.repr 50) (Byte.repr 5).

End Example.

(* ------------------------------------------------------ *)
(* Lemma 3 *)

(* --- abstract version *)

Parameter A B : Type.
Parameter convert_BA : B -> A.
Parameter convert_AB : A -> B.

Fixpoint iterate {A : Type} (n : nat) (f : A -> A) (x : A) :=
  match n with
    | O => x
    | S n' => f (iterate n' f x) (* or [iterate n' f (f x)] *)
  end.

Definition id {X : A} (x : A) : A := x.

Lemma once_eq :
    forall (x : A) (X : B) (f : A -> A) (F : B -> B),
      x = convert_BA X ->
      convert_AB (convert_BA X) = X ->
      f = convert_BA ∘ F ∘ convert_AB ->
      f x = convert_BA (F X).
Proof.
  intros x X f F inputs_eq roundtrip f_def.
  rewrite -> inputs_eq.
  rewrite -> f_def.
  change ((convert_BA ∘ F ∘ convert_AB) (convert_BA X)) with
     (convert_BA (F (convert_AB (convert_BA X)))).
  rewrite -> roundtrip.
  reflexivity.
Qed.

Lemma roundtrip :
  forall (X : B), convert_AB (convert_BA X) = X.
Proof. Admitted.

(* a simplified version of fold_equiv *)
Lemma iterate_equiv :
  forall (x : A) (X : B) (f : A -> A) (F : B -> B) (n : nat),
    f = convert_BA ∘ F ∘ convert_AB ->
    x = convert_BA X ->
    convert_AB (convert_BA X) = X ->
    iterate n f x = convert_BA (iterate n F X).
Proof.
  intros. revert x X f F H H0 H1.
  induction n as [ | n']; intros x X f F func_wrap input_eq roundtrip'.
  -
    simpl. apply input_eq.
  -
    simpl.
    pose proof once_eq as once_eq.
    apply once_eq.
    apply IHn'.
    apply func_wrap.
    apply input_eq.
    *
      apply roundtrip'.
    *
      apply roundtrip.
    * apply func_wrap.
Qed.

(* ----- *)

Lemma length_not_emp :
  forall {A B : Type} (l : list A) (z y : B),
    (Datatypes.length l > 0)%nat -> match l with [] => z | _ => y end = y.
    (* exists (x : A) (xs : list A), l = x :: xs. *)
Proof.
  intros.
  induction l as [ | x xs].
  - inversion H.
  - reflexivity.
Qed.

(* TODO: computational correspondence with length *)
Inductive InBlocks {A : Type} (n : nat) : list A -> Prop :=
  | list_nil : InBlocks n []
  | list_block : forall (front back full : list A),
                   length front = n ->
                   full = front ++ back ->
                   InBlocks n back ->
                   InBlocks n full. (* not easy to do inversion on *)

Lemma test : InBlocks 512 (list_repeat 512 true).
Proof.
  eapply list_block.
  instantiate (1 := list_repeat 512 true).
  - reflexivity.
  - instantiate (1 := []). rewrite -> app_nil_r. reflexivity.
  - apply list_nil.
Qed.

Lemma splitandpad_equiv : forall (bits : Blist) (bytes : list Z),
                            bytes_bits_lists bits bytes ->
                            bytes_bits_lists
                              (sha_splitandpad bits)
                              (sha_padding_lemmas.pad bytes).
Proof.
  intros bits bytes inputs_eq.
  unfold concat.
  unfold sha_splitandpad.

  apply bytes_bits_ind_comp in inputs_eq.
  rewrite inputs_eq.
  apply bytes_bits_def_eq.
  admit.                        (* padding preserve in-range *)
  admit.
Qed.

Lemma hash_block_equiv :
  forall (bits : Blist) (bytes : list Z)
         (regs : Blist) (REGS : SHA256.registers),
    (length bits)%nat = 512%nat ->
    (length bytes)%nat = 64%nat -> (* removes firstn 16 (Zlist->intlist bytes) *)

    regs = bytesToBits (SHA256.intlist_to_Zlist REGS) ->
    bits = bytesToBits bytes ->

    sha_h regs bits =
    bytesToBits (SHA256.intlist_to_Zlist
                   (SHA256.hash_block REGS
                                      (SHA256.Zlist_to_intlist bytes))).
Proof.
  intros bits bytes regs REGS bits_blocksize bytes_blocksize regs_eq input_eq.
  unfold sha_h.
  apply f_equal.
  apply f_equal.

  rewrite -> regs_eq.
  rewrite -> input_eq.
  rewrite -> bytes_bits_bytes_id.
  rewrite -> bytes_bits_bytes_id.
  rewrite -> pure_lemmas.intlist_to_Zlist_to_intlist.
  reflexivity.
(* TODO: make sure this proof is right / useful *)
  admit. admit.                 (* intlist_to_Zlist preserves in-range *)
Qed.

Definition convert (l : list int) : list bool :=
  bytesToBits (SHA256.intlist_to_Zlist l).

Lemma front_equiv :
  (* forall (front back : Blist) (FRONT BACK : list int), *)
  forall (back : Blist) (BACK : list int) (front : Blist) (FRONT : list int),
    Forall (fun b : Z => 0 <= b < 256) (SHA256.intlist_to_Zlist (FRONT ++ BACK)) ->
    (length front)%nat = 512%nat ->
    (length FRONT)%nat = 16%nat ->
    InBlocks 512 back ->
    InBlocks 16 BACK ->         (* shouldn't need these two *)
    front ++ back = convert (FRONT ++ BACK) ->
    front = convert FRONT.
Proof.
  intros back BACK front FRONT range f_len F_len bblocks Bblocks concat_eq.
  unfold convert in *.
  rewrite -> pure_lemmas.intlist_to_Zlist_app in concat_eq.
  (* can prove InBlocks 512 (convert (FRONT ++ BACK)) *)
  rewrite -> bytesToBits_app in concat_eq.
  revert front FRONT BACK Bblocks range f_len F_len concat_eq.
  induction bblocks; intros. 


revert front FRONT range f_len F_len concat_eq;
    induction Bblocks; intros; repeat rewrite -> app_nil_r in *.
  -
    apply concat_eq.
  -
    (* take length of each term in concat_eq, rewrite with f_len, contradiction *)
    admit.
  -                             (* same as before, contradiction with length FRONT *)
    admit.
  -
    (* don't think this is a very good form for ind hyp? *)
    specialize (IHback front FRONT BACK).
    apply IHback; auto.
    * admit.                    (* range *)
    *
      (* inverse induction?? *)
      (* simpl in concat_eq. *)
      (* this is not necessarily true?? since we're cons'ing a single element on each one
         it might be true if back and BACK had some guarantees about their lengths
         and relative lengths

         weird -- it is true for SOME non-empty backs -- e.g. if we inducted on
         InBlocks 512 and InBlocks 16

         or maybe it's always false: concat_eq NEVER implies the conclusion
         so it's not false, but not provable using the given assumption
         might want to use bytes_bits_lists and inwords and induct / 
         use properties of bytes_bits_lists to remove the :: and ++
       *)


      
      
    
    
    
    

(* is this necessarily true? the other direction is true *)
Lemma blocks_equiv :
  forall (front back : Blist) (FRONT BACK : list int),
    Forall (fun b : Z => 0 <= b < 256) (SHA256.intlist_to_Zlist (FRONT ++ BACK)) ->
    (* TODO: fix proof below *)
    InBlocks 16 FRONT ->
    InBlocks 16 BACK ->
    InBlocks 512 front ->
    InBlocks 512 back ->
    front ++ back = convert (FRONT ++ BACK) ->
    front = convert FRONT /\ back = convert BACK.
Proof.
  intros front back FRONT BACK range Fblock Bblock fblock bblock concat_eq.
  unfold convert in *.
  split.
  (* split; apply bits_bytes_ind_comp. *)

  * admit.                      (* range *)
  *                             (* front *)
    pose proof bytes_bits_comp_ind range concat_eq as bytes_bits_comp_ind.
    rewrite -> pure_lemmas.intlist_to_Zlist_app in concat_eq.
    (* can prove InBlocks 512 (convert (FRONT ++ BACK)) *)
    rewrite -> pure_lemmas.intlist_to_Zlist_app in bytes_bits_comp_ind.
    rewrite -> bytesToBits_app in concat_eq.

    revert front back BACK range Bblock fblock bblock concat_eq bytes_bits_comp_ind.
    induction Fblock; intros.
    -
      revert back BACK range Bblock bblock concat_eq bytes_bits_comp_ind0.
      induction fblock; intros.
      + 
        simpl in *.
        apply concat_eq.
      +
        simpl in *.
        rewrite -> H0 in concat_eq.
        (* is concat_eq actually going to lead to a contradiction? bad feeling my proof is wrong... *)
        (* this is actually not true -- need that 32 * length FRONT = length front,
         likewise for BACK and back -- do i have this in fold_equiv?
         have concrete lengths (16 and 512) for front, only InBlocks for back...
         + full0 = convert full
         so i can prove it for the front, which then implies it for the back
         (they are not equally easy to prove)
*)

    (* --- *)
(*

    (* induction bytes_bits_comp_ind. *)
    induction fblock.
    -
      induction Fblock.
      + apply eq_empty.
      +
        Print InBlocks.
        simpl in concat_eq.
        rewrite -> H0 in concat_eq.
        (* need to do inversion here... *)

        admit.
        
        
      
  (* rewrite -> bytesToBits_app in concat_eq. *)
    admit.

  *
    admit.                      (* range *)

  *
    admit.
*)
Admitted.

(* it's more of an iteration theorem than a fold theorem *)
Lemma fold_equiv_blocks :
  forall (l : Blist) (acc : Blist)
         (L : list int) (ACC : list int),
    (* length assumptions about list *)
    (* conversion function: bytesToBits @ SHA256.intlist_to_Zlist *)
      InBlocks 512 l ->         (* TODO: need to prove padding implies this *)
      (* TODO: need to prove that each block corresponds? applied lemma should ask for that *)
      InBlocks 16 L ->
      l = convert L ->
      acc = convert ACC ->
      hash_blocks_bits sha_h acc l = convert (SHA256.hash_blocks ACC L).
Proof.
  intros l acc L ACC bit_blocks bytes_blocks inputs_eq acc_eq.

  (* remember (bytesToBits ∘ SHA256.intlist_to_Zlist) as convert. *)
  (* assert (conv_replace: *)
  (*           forall (x : list int), bytesToBits (SHA256.intlist_to_Zlist x) = convert x). *)
  (*   rewrite -> Heqconvert. reflexivity. *)
  
  revert acc ACC L inputs_eq acc_eq bytes_blocks.
  induction bit_blocks; intros.
  *
    revert acc ACC inputs_eq acc_eq.
    induction bytes_blocks; intros.

    -                             (* both empty *)
      rewrite -> SHA256.hash_blocks_equation.
      rewrite -> hash_blocks_bits_equation.
      apply acc_eq.

    -
      rewrite -> H0 in *.
      unfold convert in inputs_eq. 
      destruct front.
      { inversion H. }
      { simpl in inputs_eq. inversion inputs_eq. }

  *
    revert front back full H H0 bit_blocks IHbit_blocks acc ACC
           inputs_eq acc_eq.
    induction bytes_blocks; intros.
    (* TODO: clear IHbytes_blocks *)

    -
      simpl in inputs_eq.
      rewrite -> H0 in inputs_eq.
      unfold convert in inputs_eq.
      destruct front.
      { inversion H. }
      { simpl in inputs_eq. inversion inputs_eq. }

    - 
      rewrite -> SHA256.hash_blocks_equation.
      rewrite -> hash_blocks_bits_equation.
      repeat rewrite -> length_not_emp.

      rewrite -> H0.
      rewrite -> H2.
      (* TODO: generalize these (it's true by hyp) *)
      assert (H_first_512 : firstn 512 (front0 ++ back0) = front0).
        apply firstn_exact. assumption.
      assert (H_skip_512 : skipn 512 (front0 ++ back0) = back0).
        apply skipn_exact. assumption.
      assert (H_first_16 : firstn 16 (front ++ back) = front).
        apply firstn_exact. assumption.
      assert (H_skip_16 : skipn 16 (front ++ back) = back).
        apply skipn_exact. assumption.

      rewrite -> H_first_512.
      rewrite -> H_skip_512.
      rewrite -> H_first_16.
      rewrite -> H_skip_16.

      apply IHbit_blocks; auto; clear IHbytes_blocks IHbit_blocks.
      +                         (* TODO: backs are equivalent *)
        rewrite -> H0 in inputs_eq.
        rewrite -> H2 in inputs_eq.
        (* could refactor out the pose/destruct but leaves more stuff in context *)
        pose proof blocks_equiv front0 back0 front back as blocks_equiv.
        
        destruct blocks_equiv.
        apply inputs_eq.
        apply H4.
      +
        Check hash_block_equiv.

        pose proof hash_block_equiv as hash_block_equiv.
        specialize (hash_block_equiv front0 (SHA256.intlist_to_Zlist front) acc ACC).
        rewrite -> hash_block_equiv; auto. clear hash_block_equiv.
        rewrite -> pure_lemmas.intlist_to_Zlist_to_intlist.
        (* rewrite -> conv_replace in *. *)
        reflexivity.
        {
          rewrite -> pure_lemmas.length_intlist_to_Zlist.
          rewrite -> H.
          omega.
        }
        {
          (* TODO: prove the fronts are equivalent *)
          rewrite -> H0 in inputs_eq.
          rewrite -> H2 in inputs_eq.
          pose proof blocks_equiv front0 back0 front back as blocks_equiv.
          destruct blocks_equiv.
          apply inputs_eq.
          apply H3.
        }
     +
       rewrite -> H0. rewrite -> app_length. rewrite -> H. omega.
     +
       rewrite -> H2. rewrite -> app_length. rewrite -> H1. omega.
Qed.

(* proof residue
      apply IHbytes_blocks.

- was double induction necessary?
- what about IHbytes_blocks?
- better to rewrite into front and back, then break that up, then apply the *first* induction hypothesis,
  then apply theorem to front

- TODO: prove that they are InBlocks after padding and that front~front0, back~back0
 *)

Lemma SHA_equiv_pad : forall (bits : Blist) (bytes : list Z),
                        (* add length assumptions here + intros them *)
                    bytes_bits_lists bits bytes ->
                    bytes_bits_lists
                      (hash_words_padded sha_h sha_iv sha_splitandpad bits)
                      (SHA256_.Hash bytes).

Proof.
  intros bits bytes input_eq.
  unfold SHA256_.Hash.
  rewrite -> functional_prog.SHA_256'_eq.
  unfold SHA256.SHA_256.
  unfold hash_words_padded.
  change ((hash_words sha_h sha_iv ∘ sha_splitandpad) bits) with
  (hash_words sha_h sha_iv (sha_splitandpad bits)).

  -
    repeat rewrite <- sha_padding_lemmas.pad_compose_equal in *.
    unfold sha_padding_lemmas.generate_and_pad' in *.
    unfold hash_words.
    unfold h_star.

    Check SHA256.hash_blocks_equation.

    pose proof splitandpad_equiv as splitandpad_equiv.
    specialize (splitandpad_equiv bits bytes input_eq).

      apply bytes_bits_comp_ind.
      pose proof fold_equiv_blocks as fold_equiv_blocks. (* delete later *)
      admit.
      (* TODO: in-range preserved by hash_blocks and intlist_to_Zlist *)
      apply fold_equiv_blocks.
      *                         (* padding -> blocks of 512 *)
        unfold sha_splitandpad.
        unfold pad.
        admit.
       (* might need InWords *)
       (* probably a subcase of the below proof *)
      *
        (* TODO: check that my new padding func preserves the 16 property *)
        SearchAbout SHA256.hash_blocks.
        (* see pure_lemmas.length_hash_blocks *)
        Check pure_lemmas.length_hash_blocks.
        Print SHA256.LBLOCKz.   (* 16, and registers have length 8 *)
        SearchAbout SHA256.generate_and_pad.
        Print common_lemmas.roundup.
        (* can use length_generate_and_pad if you finish proving them equal *)
        pose proof sha_padding_lemmas.pad_inwords.
        unfold pad.
        (* eapply list_block. *)
        (* instantiate (1 := ). *)
        Print SHA256.generate_and_pad.
        (* 1/4 * 64n = 16n *)

        SearchAbout pad.
        SearchAbout InWords.
        admit.

      * unfold sha_splitandpad.
        rewrite -> pure_lemmas.Zlist_to_intlist_to_Zlist.
        f_equal.
        apply bytes_bits_ind_comp in input_eq.
        rewrite -> input_eq.
        reflexivity.
        + admit.                (* bytes in range *)
        +
          Print SHA256.WORD.    (* 4 *)
          admit.                        (* padding length lemma *)
        + admit.                        (* padding in range *)

     * unfold sha_iv. reflexivity.
Qed.


(* --------------------------------------- *)

(* MAIN THEOREM *)

Theorem HMAC_spec_equiv : forall
                            (K M H : list Z) (OP IP : Z)
                            (k m h : Blist) (op ip : Blist),
  ((length K) * 8)%nat = (c + p)%nat ->
  Zlength K = Z.of_nat SHA256_.BlockSize ->
(* TODO: first implies this *)
  (* TODO: might need more hypotheses about lengths *)
  bytes_bits_lists k K ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HMAC_SHA256.sixtyfour OP) ->
  bytes_bits_lists ip (HMAC_SHA256.sixtyfour IP) ->
  HMAC c p sha_h sha_iv sha_splitandpad op ip k m = h ->
  HMAC_SHA256.HMAC IP OP M K = H ->
  bytes_bits_lists h H.
Proof.
  intros K M H OP IP k m h op ip.
  intros padded_key_len padded_key_len_byte padded_keys_eq msgs_eq ops_eq ips_eq.
  intros HMAC_abstract HMAC_concrete.

  intros.
  unfold p, c in *.
  simpl in *.

  rewrite <- HMAC_abstract. rewrite <- HMAC_concrete.

  unfold HMAC. unfold HMAC_SHA256.HMAC. unfold HMAC_SHA256.OUTER. unfold HMAC_SHA256.INNER.
  unfold HMAC_SHA256.outerArg. unfold HMAC_SHA256.innerArg.

  unfold HMAC_2K. unfold GHMAC_2K. rewrite -> split_append_id.

  simpl.

  apply SHA_equiv_pad.
  apply concat_equiv.
  apply xor_equiv_Z; try assumption.

  *
    apply SHA_equiv_pad.
    apply concat_equiv.

  - apply xor_equiv_Z; try assumption.
  - assumption.
    (* xors preserve length *)
    *
      unfold b in *. simpl. unfold BLxor. rewrite -> list_length_map.
      rewrite -> combine_length.
      pose proof bytes_bits_length ops_eq as ops_len.
      rewrite -> ops_len.
      pose proof bytes_bits_length padded_keys_eq as keys_len.
      rewrite -> keys_len.
      rewrite -> padded_key_len.
      unfold HMAC_SHA256.sixtyfour.
      rewrite -> length_list_repeat.
      reflexivity.

    * 
      unfold b in *. simpl. unfold BLxor. rewrite -> list_length_map.
      rewrite -> combine_length.
      pose proof bytes_bits_length ips_eq as ips_len.
      rewrite -> ips_len.
      pose proof bytes_bits_length padded_keys_eq as keys_len.
      rewrite -> keys_len.
      rewrite -> padded_key_len.
      unfold HMAC_SHA256.sixtyfour.
      rewrite -> length_list_repeat.
      reflexivity.
Qed.
