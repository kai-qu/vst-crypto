Set Implicit Arguments.

Require Import List.
Require Import Bvector.
Require Import HMAC_common_defs.
Require Import SHA256.
Require Import HMAC_spec_pad.
Require Import Coq.Program.Basics.

Module HMAC_Concat.

Section HMAC.

  Variable c p : nat.
  Definition b := c + p.
  
  (* The compression function *)
  Variable h : Blist -> Blist -> Blist.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Blist.

  (* splitAndPad concat'ed, normal fold replaced by firstn/splitn manual fold *)

  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : Blist) :=
    hash_blocks_bits h m k.
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

Check HMAC_Concat.HMAC.
Check HMAC_Pad.HMAC.

(* TODO fill these in *)
(* TODO move splitAndPad to HMAC_common *)
Parameter splitAndPad : Blist -> Blist.
Parameter fpad : Blist -> Blist.

Theorem HMAC_concat_pad : forall (k m : Blist) (op ip : Blist),
  HMAC_Pad.HMAC c p sha_h sha_iv sha_splitandpad op ip k m =
  HMAC_Concat.HMAC c p sha_h sha_iv splitAndPad fpad op ip k m.
Proof.
  intros k m op ip.
  unfold c, p in *. simpl in *.
  unfold HMAC_Pad.HMAC. unfold HMAC_Concat.HMAC.
  unfold HMAC_Pad.HMAC_2K. unfold HMAC_Concat.HMAC_2K.
  unfold HMAC_Pad.GHMAC_2K. unfold HMAC_Concat.GHMAC_2K.

  repeat rewrite -> split_append_id.
  unfold HMAC_Pad.hash_words_padded.
  unfold HMAC_Concat.hash_words.
  unfold HMAC_Concat.app_fpad.
  unfold compose.
  
  


Admitted.

