Set Implicit Arguments.

(* Require Import Bvector. *)
Require Import List.
Require Import Arith.

Require Import HMAC_functional_prog.
Require Import Integers.
Require Import Coqlib.
Require Import sha_padding_lemmas.
Require Import functional_prog.

Require Import List. Import ListNotations.

Definition Blist := list bool.

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) (x : A) := f (g x).
Notation "f @ g" := (compose f g) (at level 80, right associativity).

Definition splitVector {A : Type} (h : nat) (t : nat) (l : list A) : (list A * list A) :=
  (firstn h l, skipn t l).

(* 
Definition mkArg (key:list byte) (pad:byte): list byte := 
       (map (fun p => Byte.xor (fst p) (snd p))
          (combine key (sixtyfour pad))).
Definition mkArgZ key (pad:byte): list Z := 
     map Byte.unsigned (mkArg key pad). *)

(* TODO: length proofs (length xs = length ys) *)
Definition BLxor (xs : Blist) (ys : Blist) :=
  map (fun p => xorb (fst p) (snd p)) (combine xs ys).
(* TODO pattern match on tuples? *)

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
  Definition h_star k (m : list (Blist)) :=
    fold_left h m k.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  Check hash_words.
  Check h_star.

  (* NOTE: this is the new design without fpad TODO *)
  Variable splitAndPad : Blist -> list (Blist).

  Definition hash_words_padded : Blist -> Blist :=
    hash_words @ splitAndPad.

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
    let (k_Out, k_In) := splitVector c c k in
    h k_Out (h_star_pad k_In m). (* could take head of list *)

  Check GNMAC. 
  (*  list bool -> list Blist -> Blist *)
  Check h.
  (* Blist -> Blist -> Blist *)

Check hash_words.               (* list Blist -> Blist *)

  (* The "two-key" version of GHMAC and HMAC. *)
  (* Concatenate (K xor opad) and (K xor ipad) *)
  Definition GHMAC_2K (k : Blist) m :=
    let (k_Out, k_In) := splitVector b b k in (* concat earlier, then split *)
      let h_in := (hash_words (k_In :: m)) in
        hash_words_padded (k_Out ++ h_in).

  Definition HMAC_2K (k : Blist) (m : Blist) :=
    GHMAC_2K k (splitAndPad m).

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

Check HMAC.

(* HMAC
     : nat ->
       nat ->
       (Blist -> Blist -> Blist) ->
       Blist ->
       (Blist -> list Blist) -> Blist -> Blist -> Blist -> Blist -> Blist *)


