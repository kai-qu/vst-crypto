Set Implicit Arguments.

Require Import List.
Require Import Bvector.
Require Import HMAC_common_defs.
Require Import SHA256.
Require Import HMAC_spec_pad.
Require Import Coq.Program.Basics.
Require Import Coqlib.
Require Import ByteBitRelations.
Require Import sha_padding_lemmas.

Module HMAC_Concat.

Section HMAC.

  Variable c p : nat.
  Definition b := (c + p)%nat.
  
  (* The compression function *)
  Variable h : Blist -> Blist -> Blist.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Blist.

  (* splitAndPad concat'ed, normal fold replaced by firstn/splitn manual fold *)

  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : Blist) :=
    hash_blocks_bits h k m.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  Variable splitAndPad : Blist -> Blist.
  Hypothesis splitAndPad_1_1 : 
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.

  (* fpad can be a constant *)
  Variable fpad : Blist -> Blist. 
  Definition app_fpad (x : Blist) : Blist :=
    x ++ fpad x.

  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  Definition GNMAC k m :=
    let (k_Out, k_In) := splitList c k in
    h k_Out (app_fpad (h_star k_In m)).

  (* The "two-key" version of GHMAC and HMAC. *)
  Definition GHMAC_2K (k : Blist) m :=
    let (k_Out, k_In) := splitList b k in
      let h_in := (hash_words (k_In ++ m)) in 
        hash_words (k_Out ++ app_fpad h_in).
  
  Definition HMAC_2K (k : Blist) (m : Blist) :=
    GHMAC_2K k (splitAndPad m).

  (* opad and ipad are constants defined in the HMAC spec. *)
  Variable opad ipad : Blist.
  Hypothesis opad_ne_ipad : opad <> ipad.

  Definition GHMAC (k : Blist) :=
    GHMAC_2K (BLxor k opad ++ BLxor k ipad).

  Definition HMAC (k : Blist) :=
    HMAC_2K (BLxor k opad ++ BLxor k ipad).

End HMAC.

End HMAC_Concat.


Lemma h_star_eq :
  HMAC_Pad.h_star = HMAC_Concat.h_star.
Proof. reflexivity. Qed.

(* TODO add assumptions, prove, prove assumptions where used, and move to ByteBitRelations *)

Lemma bitsToBytes_len : forall (l : Blist),
                          True ->
                          Zlength (bitsToBytes l) = BlockSize.
Proof.

Admitted.

Lemma bitsToBytes_app : forall (l m : Blist),
                          True ->
                          True ->
                          bitsToBytes (l ++ m) = bitsToBytes l ++ bitsToBytes m.
Proof.

Admitted.

Lemma bits_bytes_bits_id : forall (l : Blist),
                             True ->
                             bytesToBits (bitsToBytes l) = l.
Proof.

Admitted.

Lemma splitandpad_eq : forall (l m : Blist),
                         length l = b ->
                         (* TODO m is InBlocks *)
                         sha_splitandpad (l ++ m) = l ++ sha_splitandpad_inc m.
Proof.
  intros l m len.
  unfold sha_splitandpad. unfold sha_splitandpad_inc.
  unfold pad. unfold pad_inc.

  rewrite -> bitsToBytes_app.
  rewrite -> common_lemmas.Zlength_app.
  repeat rewrite -> bytesToBits_app.
  rewrite -> bits_bytes_bits_id.
  rewrite <- app_assoc.
  repeat f_equal.
  unfold c, p, b in *.

  apply bitsToBytes_len.
    admit.
  apply bitsToBytes_len.
    admit.
  apply bitsToBytes_len.
    admit.
  admit.
  admit.
  admit.
Qed.

Lemma fpad_eq : forall (l m : Blist),
                  length l = b ->
                  (* TODO m is in blocks *)
                  sha_splitandpad (l ++ m) = l ++ HMAC_Concat.app_fpad fpad m.
Proof.
  intros l m len.
  unfold HMAC_Concat.app_fpad.
  unfold sha_splitandpad. unfold fpad.
  unfold pad. unfold fpad_inner.

  rewrite -> bitsToBytes_app.
  repeat rewrite -> bytesToBits_app.
  repeat rewrite -> bits_bytes_bits_id.
  rewrite <- app_assoc.
  rewrite -> common_lemmas.Zlength_app.
  repeat f_equal.

  apply bitsToBytes_len.
    admit.
  apply bitsToBytes_len.
    admit.
  apply bitsToBytes_len.
    admit.
  admit.
  admit.
  admit.
  admit.
Qed. 

Theorem HMAC_concat_pad : forall (k m : Blist) (op ip : Blist),
                            (* TODO length guarantees on k, ip, and op *)
  HMAC_Pad.HMAC c p sha_h sha_iv sha_splitandpad op ip k m =
  HMAC_Concat.HMAC c p sha_h sha_iv sha_splitandpad_inc fpad op ip k m.
Proof.
  intros k m op ip.
  unfold c, p in *. simpl in *.
  unfold HMAC_Pad.HMAC. unfold HMAC_Concat.HMAC.
  unfold HMAC_Pad.HMAC_2K. unfold HMAC_Concat.HMAC_2K.
  unfold HMAC_Pad.GHMAC_2K. unfold HMAC_Concat.GHMAC_2K.

  repeat rewrite -> split_append_id.
  unfold HMAC_Pad.hash_words_padded. unfold compose.
  unfold HMAC_Concat.hash_words.
  unfold HMAC_Pad.hash_words.
  rewrite -> h_star_eq.
  
  (* show the two inputs to h_star are equal *)
  f_equal.

  rewrite <- splitandpad_eq.
  rewrite <- fpad_eq.
  reflexivity.

(* TODO split out lemma that BLxor preserves length given 2 of block size *)
  admit.
  admit.
  admit.
  admit.
  admit.
  admit.
Qed.
