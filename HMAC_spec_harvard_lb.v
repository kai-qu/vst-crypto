Set Implicit Arguments.


Require Import Bvector.
Require Import List.
Require Import Arith.

Require Import HMAC_functional_prog_new.
Require Import Integers.
Require Import Coqlib.

(* Require Import List. Import ListNotations. *)

Definition Blist := list bool.

Fixpoint splitVector(A : Set)(n m : nat) : Vector.t A (n + m) -> (Vector.t A n * Vector.t A m) :=
  match n with
    | 0%nat => 
      fun (v : Vector.t A (O + m)) => (@Vector.nil A, v)
    | S n' => 
      fun (v : Vector.t A (S n' + m)) => 
        let (v1, v2) := splitVector _ _ (Vector.tl v) in
          (Vector.cons _ (Vector.hd v) _ v1, v2)
  end.

Section HMAC.

SearchAbout Bvector.
Print Bvector.
Check Bvector 10.
Check [true]. 
Print Vector.

(* b = block size
   c = digest (output) size
   p = padding = b - c (fixed) *)
  Variable c p : nat.
  Definition b := (c + p)%nat.
  
  (* The compression function *)
  Variable h : Bvector c -> Bvector b -> Bvector c.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Bvector c.
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : list (Bvector b)) :=
    fold_left h m k.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  (* TODO check how this corresponds to SHA
     Seems that h = SHA compression function
     hash_words with SHA's iv is SHA
   *)
  Check hash_words.
  Check h_star.

  Variable splitAndPad : Blist -> list (Bvector b).

  (* TODO examine this hypothesis, prove that MD lemmas imply it *)
  Hypothesis splitAndPad_1_1 : 
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.
  
  (* constant-length padding. *)
  Variable fpad : Bvector p.

  Definition app_fpad (x : Bvector c) : Bvector b :=
    (Vector.append x fpad).
  Definition h_star_pad k x :=
    app_fpad (h_star k x).

  Definition GNMAC k m :=
    let (k_Out, k_In) := splitVector c c k in
    h k_Out (app_fpad (h_star k_In m)).

  (* The "two-key" version of GHMAC and HMAC. *)
  (* Concatenate (K xor opad) and (K xor ipad) *)
  Definition GHMAC_2K (k : Bvector (b + b)) m :=
    let (k_Out, k_In) := splitVector b b k in (* concat earlier, then split *)
      let h_in := (hash_words (k_In :: m)) in 
        hash_words (k_Out :: (app_fpad h_in) :: nil).
  
  Definition HMAC_2K (k : Bvector (b + b)) (m : Blist) :=
    GHMAC_2K k (splitAndPad m).

Check HMAC_2K.
(* HMAC_2K
     : Bvector (b + b) -> Blist -> Bvector c *)

(* opad and ipad are constants defined in the HMAC spec. *)
Variable opad ipad : Bvector b.
Definition GHMAC (k : Bvector b) :=
  GHMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

Print BVxor.


Definition HMAC (k : Bvector b) :=
  HMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

Check HMAC.                     (*  : Bvector b -> Blist -> Bvector c *)

End HMAC.

(* ----------------------------------------------------------- Theorem definitions *)

Require Import HMAC_functional_prog_2.

Check HMAC_SHA256.HMAC.            (* list Z -> list Z -> list Z *)

  (* Bvector is little-endian (least significant bit at head; list Z are just translated
from the string (ascii -> nat -> Z); but Int are packed big-endian (with 4 Z -> 1 Int)

each Z is one byte (8 bits) *)

(* TODO: add isbyteZ (from SHA256.v), 0 <= i <= 256 *)

(* *************** byte/bit computational *)

(* TODO: finish this

The term "Vector.append (iterate n' num_new) [bool_digit]" has type
 "Vector.t bool (n' + 1)" while it is expected to have type 
"Bvector (S n')".

Function with proof of equivalence? see hash_blocks  *)

(*
Fixpoint iterate (n : nat) (byte : nat) : Bvector n :=
  match n as x return Bvector x with
    | O => Vector.nil bool
    | S n' =>
      let byte_subtract := (byte - NPeano.pow 2 (n - 1))%nat in
      let bool_digit := leb byte_subtract 0 in
      let num_new := if bool_digit then byte_subtract else byte in
      Vector.append (iterate n' num_new) [bool_digit] (* could reverse instead *)
  end.

Fixpoint byte_to_bits (byte : Z) : Bvector 8 :=
  let max_pow_two := 7 in
  iterate (max_pow_two + 1) (nat_of_Z byte).
*)

Parameter byte_to_bits : Z -> Bvector 8.

(* Or: concatMap byte_to_bit bytes *)
Check Bvector.
SearchAbout Bvector.
Print Vector.t.

(* how to prove that it's length bytes * 8? *)
(* list of bytes? (type) *)
Fixpoint bytes_to_bits (bytes : list Z) : Bvector (length bytes * 8) :=
  match bytes as x return Bvector (length x * 8) with (* CPDT *)
    | nil => Vector.nil bool
    | x :: xs => Vector.append (byte_to_bits x) (bytes_to_bits xs)
  end.

(* ************* inductive defs *)
  
SearchAbout Bvector.

Definition asZ (x : bool) : Z := if x then 1 else 0.

(* TODO: maybe prefer b : byte, with Byte.repr? *)
Definition convertByteBits (b : Z) (B : Bvector 8) : Prop :=
  exists (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
   B = [b0; b1; b2; b3; b4; b5; b6; b7] /\
   b =  (1 * (asZ b0) + 2 * (asZ b1) + 4 * (asZ b2) + 8 * (asZ b3)
         + 16 * (asZ b4) + 32 * (asZ b5) + 64 * (asZ b6) + 128 * (asZ b7)).

(* *** *)

(* relationship between a list Z (of bytes) and a Bvector of size (c + p):
toBvector (bytes_to_bits k) = K?

This definition is not easy to use; replaced with bytes_bits_vector' in theorem
 *)
Inductive bytes_bits_vector (c p : nat) (k : list Z) : Bvector (plus c p) -> Prop :=
  | test_n : forall (K : Bvector (plus c p)),
               bytes_bits_vector c p k K (* TODO *)
.

(* relating list Z to Blist
bytes_to_bits m = length M

TODO: big-endian, little-endian?
*)
Inductive bytes_bits_lists : list Z -> Blist -> Prop :=
  | eq_empty : bytes_bits_lists nil nil
  | eq_cons : forall (bytes : list Z) (bits : Blist)
                     (byte : Z) (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
                bytes_bits_lists bytes bits ->
                convertByteBits byte ([b0; b1; b2; b3; b4; b5; b6; b7]) ->
                bytes_bits_lists (byte :: bytes)
                                (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bits)
.

(* the hashes are "the same": list Z vs Bvector c

toBvector (bytes_to_bits h) = H
this is *almost* the same as bytes_bits_vector, except just c, not c + p
 *)
(* note: need to name c in order to use in Bvector c -- but then need to use names *)
Inductive bytes_bits_vector' (len : nat) (bytes : list Z) (bits : Bvector len) : Prop :=
  | eq_empty_v : bytes = nil -> len = 0%nat -> bytes_bits_vector' bytes bits
  (* remove -> from eq_empty_v TODO *)
  | eq_cons_v : bytes_bits_vector' bytes bits
      (* forall (len' : nat) (bytes' : list Z) (bits' : Bvector len)
                       (byte : Z) (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
                  bytes_bits_vector' bytes' bits' ->
                  convertByteBits byte ([b0; b1; b2; b3; b4; b5; b6; b7]) ->
                  bytes_bits_vector' (byte :: bytes')
                                   (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bits')
      *) (* TODO *)
.
(* TODO: compare to rel1. How do dependent types and inductive props work? *)

Check bytes_bits_vector.
Check HMAC_SHA256.HMAC.         (* ? *)
Check HMAC.
(* HMAC
     : forall c p : nat,
       (Bvector c -> Bvector (b c p) -> Bvector c) ->   // compression function h
       Bvector c ->                          // iv, h's initialization vector
       (Blist -> list (Bvector (b c p))) ->  // splitAndPad (e.g. generate_and_pad)
       Bvector p ->                          // fpad, constant-length padding
       Bvector (b c p) ->                    // opad
       Bvector (b c p) ->                    // ipad

^ Note: this has to do with the internals of SHA256 and HMAC too
SHA's compression function, iv, generate_and_pad (with block vectors),
HMAC's key padding function, HMAC's opad and ipad.
How to convert?

       Bvector (b c p) -> Blist -> Bvector c        // key, message, outputted hash

k is of length b
b = block size
c = output size
p = padding = b - c

why pad the key? why not just let it be size b?
 *)

(* ----------------------------------------- Theorem and parameters *)

Parameter sha_iv : Bvector (SHA256_.DigestLength * 8).

(* Definition sha_h : list Z -> list Z := SHA256_.Hash. *)
(* TODO: c = 32, p = 32 *)
Parameter sha_h : forall (c p : nat) (b:nat -> nat -> nat), Bvector c -> Bvector (b c p) -> Bvector c.

(* corresponds to block size. b = plus *)

(* TODO: email adam about fpad: it's not padding the key *)

(*  "Blist -> list (Bvector (b SHA256_.DigestLength c))" *)
Parameter sha_splitandpad_vector :
  forall (p: nat), Blist -> list (Bvector (SHA256_.DigestLength * 8 + p)).

Parameter fpad : forall (p : nat), Bvector p.

(* want Bvector b = 512 bits *)
Print Byte.int.
Print Byte.repr.
Check HMAC_SHA256.sixtyfour HMAC_SHA256.Opad.
Check Byte.unsigned.
Definition opad := 
     bytes_to_bits
                     (map Byte.unsigned (HMAC_SHA256.sixtyfour HMAC_SHA256.Opad)).
Check opad. 
Definition ipad := bytes_to_bits
                     (map Byte.unsigned (HMAC_SHA256.sixtyfour HMAC_SHA256.Ipad)).

(*
TODO: 8/20/14

Key is not being padded? Need to assume the padded key is of length b
Email Adam about fpad: it's not used to pad the key
Figure out what parameters are
Fill in the relations

Byte to bits: computational vs. prop
  bytes_bits_vector: problem
  bytes_to_bits: 2 problems
  still need the computational version for opad?

Modify the theorem:
 parametrize C HMAC by OPAD and IPAD + they need to be different in at least one bit
   (email adam: does he use this in his proof?)

Now, write individual functions and prove them equivalent? they have different types
Still abstract: sha_h, sha_splitandpad, fpad?

Figure out what lemmas to prove (Look in HMAC_Lemmas)

Lennart: update spec to take ipad and opad as parameters
 *)
Check HMAC.

(* ------------------------------------- *)
Module Equiv.

Definition c:nat := (SHA256_.DigestLength * 8)%nat.
(*Variable p:nat.
Locate HMAC.
Check @HMAC. Check @sha_h.
Check (@HMAC _ p (@sha_h _ p plus) sha_iv (sha_splitandpad_vector p) (fpad p)). 
Check (HMAC (sha_h p plus) sha_iv).
*)
Definition p:=(32 * 8)%nat.

(* Define opad, define ipad, pass converted ipad/opad to respective hmacs *)

(* Is this the theorem we want? Is it useful for the rest of the proofs?
Should it be more abstract? *)

Theorem HMAC_spec_equiv : forall
                            (k m h : list Z)
                            (K : Bvector (plus c p)) (M : Blist) (H : Bvector c) OP IP,
                            
  ((length k) * 8)%nat = b c p ->
  bytes_bits_vector' k K ->
  (* 1. not separating c and p 2. inductive prop / dep types? 3. computation / dep types?
     bytes_bits_vector' k K vs. bytes_to_bits k = K <- can't prove lens equal?*)
  bytes_bits_lists m M ->
  HMAC (sha_h p plus) sha_iv (sha_splitandpad_vector p) (fpad p) OP IP K M = H ->
  HMAC_SHA256.HMAC m k = h ->
  bytes_bits_vector' h H.
Proof.  
  intros k m h K M H OP IP.
  intros padded_key_len padded_keys_eq msgs_eq HMAC_abstract HMAC_concrete.
  unfold p,c, b in *.
  simpl in *.

  unfold HMAC in *.
  unfold HMAC_SHA256.HMAC in *.

  unfold HMAC_2K in *. unfold GHMAC_2K in *. (* unfold splitVector in *. *)
  (* Still abstract: sha_h, sha_splitandpad_vector, fpad *)

  unfold HMAC_SHA256.OUTER in *. unfold HMAC_SHA256.INNER in *.
    unfold HMAC_SHA256.outerArg in *. unfold HMAC_SHA256.innerArg in *.

  rewrite <- HMAC_abstract.
  rewrite <- HMAC_concrete.


Abort.
