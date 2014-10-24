(* Import ListNotations. *)
(* Local Open Scope logic. *)

Require Import HMAC_functional_prog.
Require Import SHA256.

Lemma mkKey_length l: length (HMAC_SHA256.mkKey l) = SHA256_.BlockSize.
Proof. intros. unfold HMAC_SHA256.mkKey.
  remember (Zlength l >? Z.of_nat SHA256_.BlockSize) as z. 
  destruct z. apply zeroPad_BlockSize.
    rewrite length_SHA256'.  
    apply Nat2Z.inj_le. simpl. omega. 
  apply zeroPad_BlockSize.
    rewrite Zlength_correct in Heqz. 
    apply Nat2Z.inj_le. 
    specialize (Zgt_cases (Z.of_nat (Datatypes.length l)) (Z.of_nat SHA256.BlockSize)). rewrite <- Heqz. trivial.
Qed.