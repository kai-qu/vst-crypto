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

  Variable c p : nat.
  (* b is block size, c is digest (output) size, p is padding *)
  Definition b := (c + p)%nat.
  Check b.
  
  (* The compression function *)
  (* hash_blocks: registers -> block -> registers *)
  Variable h : Bvector c -> Bvector b -> Bvector c.
  (* The initialization vector is part of the spec of the hash function. *)
  (* TODO: is the IV standardized in the spec? does it need to have certain properties for
   the proof? *)
  Variable iv : Bvector c.
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : list (Bvector b)) :=
    fold_left h m k.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  (* TODO check how this corresponds to SHA *)
  Definition hash_words := h_star iv.
Check hash_words.
Check h_star.

  Variable splitAndPad : Blist -> list (Bvector b).

  (* TODO examine this hypothesis *)
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
  
  (* b + b comes from ( *)
  Definition HMAC_2K (k : Bvector (b + b)) (m : Blist) :=
    GHMAC_2K k (splitAndPad m).

Check HMAC_2K.
(* HMAC_2K
     : Bvector (b + b) -> Blist -> Bvector c *)
SearchAbout Bvector.
(* Bvector (b + b) -> Blist -> BVector c *)

Print splitVector.

Theorem test : forall (k : Bvector (b + b)) (m : Blist),
  HMAC_2K k m = HMAC_2K k m.
Proof.
  intros k m.
  unfold HMAC_2K.               (* splitAndPad is abstract *)
  unfold GHMAC_2K.
  unfold hash_words.
  unfold h_star. 
  (* unfold splitVector. *)
Abort.

Print Bvector.                  (* Vector.t bool : nat -> Set *)
(* Check [true]%(Bvector 1). *)
(* Cannot compute since Variables are not instantiated  -- TODO, how to instantiate 
(e.g. with SHA256? does it have the right type? 
SHA256 : list Z -> list Z *)
(* Eval compute in HMAC_2K [true; true] [false]. *)

  (* opad and ipad are constants defined in the HMAC spec. *)
  Variable opad ipad : Bvector b. (* c + p *)
  Definition GHMAC (k : Bvector b) :=
    GHMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

Print BVxor.

  (* Doesn't seem to take into account the hash function's input block size (see mkKey in P. spec) *)
  Definition HMAC (k : Bvector b) :=
    HMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

Check HMAC.                     (*  : Bvector b -> Blist -> Bvector c *)

  (* Bvector or Blist? *)
Check HMAC_2K.                  (* TODO confirm that this is actually the right version *)

End HMAC.

(* -------------- *)

Require Import HMAC_functional_prog_2.

(* How to get the other HMAC? *)
(* TODO: compile HMAC_functional_prog_2 *)
Check HMAC_FUN.HMAC.            (* list Z -> list Z -> list Z *)

(* Bvector (plus c p)  *)

(* relationship between a list Z (of bytes) and a Bvector of size (c + p):
toBvector (bytes_to_bits k) = K?
(don't actually need the Bvector, just c + p, or its length) <-- deprecated,
want equality
 *)
Inductive bytes_bits_vector (c p : nat) (k : list Z) : Bvector (plus c p) -> Prop :=
  | test_n : forall (K : Bvector (plus c p)), bytes_bits_vector c p k K (* ?? TODO *)
.

(* relating list Z to Blist
bytes_to_bits m = length M

TODO: big-endian, little-endian?
*)
Inductive bytes_bits_lists (m : list Z) : Blist -> Prop :=
  | test_n' : forall M : Blist, bytes_bits_lists m M
.

(* the hashes are "the same": list Z vs Bvector c

toBvector (bytes_to_bits h) = H
this is *almost* the same as bytes_bits_vector, except just c, not c + p
 *)
Inductive bytes_bits_vector' (c : nat) (h : list Z) : Bvector c -> Prop :=
  | test_n'' : forall (H : Bvector c), bytes_bits_vector' h H
.
(* TODO: compare to rel1. How do dependent types and inductive props work? *)



(* TODO:
Definition convertByteBits (b: byte) (B: Bvector 8): Prop :=
  exists b0, ... b7 (*all of type bool*),
   B = [b0, b1, ... b7] /\
   b = (asZ b0) + 2 * (asZ b1) * 4 * (asZ b2) + .. + 128 * (asZ b7).

where Definition asZ (x:bool):Z := if x then 1 else 0.
*)

Check bytes_bits_vector.
Check HMAC_FUN.HMAC.
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
HMAC's key padding function, HMAC's opad and ipad

How to convert?

Bvector (b c p) -> Blist -> Bvector c        // key, message, outputted hash
k is of length b
b = block size
c = output size
c + p = output size padded to block size

why pad the key? why not just let it be size b?
 *)

(* Is this the theorem we want? Is it useful for the rest of the proofs?
Should it be more abstract? 

also, no key padding
add assumption that the key is padded to the right length (b)
password of length b
modify?
*)

Print Blist.

(* maybe bvector of length 8, convert to Blist later? 
TODO big-endian vs. little-endian *)
(* Parameter byte_to_bits : Z -> Bvector 8. *)
  (* Vector.nil bool. TODO *)
SearchAbout Vector.t.

(* Bvector is little-endian (least significant bit at head; list Z are just translated
from the string (ascii -> nat -> Z); but Int are packed big-endian (with 4 Z -> 1 Int)

each Z is one byte (8 bits) *

bytes -> bits is ok
bits -> bytes is not ok
*)
(*
Don't have an assurance that 0 <= byte < 256 
TODO: add isbyteZ (from SHA256.v), 0 <= i <= 256 

1 2 3 4 5 6 7 8
*)

SearchAbout Z.
Eval compute in zle 5 10.
Check zle.
Check zle_true.
SearchAbout nat.
Check N.

(* TODO: finish this

The term "Vector.append (iterate n' num_new) [bool_digit]" has type
 "Vector.t bool (n' + 1)" while it is expected to have type 
"Bvector (S n')".

Function with proof of equivalence? see hash_blocks
 *)

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

(* reverse? 
0 <= byte < 256, integer 

[0, 1, 2, 3, 4, 5, 6, 7] <-- bool
*)
Fixpoint byte_to_bits (byte : Z) : Bvector 8 :=
  let max_pow_two := 7 in
  iterate (max_pow_two + 1) (nat_of_Z byte).    (* or iterate 8? *)
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

(* -------------------------------- *)

Parameter sha_iv : Bvector (8 * SHA256_.DigestLength).

(* Definition sha_h : list Z -> list Z := SHA256_.Hash. *)
Parameter sha_h : forall (c p : nat) (b:nat -> nat -> nat),
                    Bvector c -> Bvector (b c p) -> Bvector c.
(* due to implicit parameters, only requires c or p, and b *)

(* corresponds to block size, b = plus *)

(* TODO: email adam about fpad: it's not padding the key *)

(*  "Blist -> list (Bvector (b SHA256_.DigestLength c))" *)
Parameter sha_splitandpad_vector :
  forall (p : nat), Blist -> list (Bvector ((SHA256_.DigestLength * 8) + p)).

Parameter fpad : forall (p : nat), Bvector p.

(* want Bvector b = 512 bits *)
Print Byte.int.
Print Byte.repr.
Check HMAC_SHA256.sixtyfour HMAC_SHA256.Opad.
Check Byte.unsigned.
Definition opad := bytes_to_bits
                     (map Byte.unsigned (HMAC_SHA256.sixtyfour HMAC_SHA256.Opad)).
Definition ipad := bytes_to_bits
                     (map Byte.unsigned (HMAC_SHA256.sixtyfour HMAC_SHA256.Ipad)).

Check HMAC.

(* 
Email Adam about fpad
Figure out what parameters are
Fill in the relations
Byte to bits

New theorem
Parametrize C HMAC by OPAD and IPAD + they need to be different in at least one bit
   (does adam need this?)

Now, write individual functions (e.g. sha_h, which is still abstract)
and prove them equivalent? different types....

Lennart: update spec, ipad and opad
email andrew about lennart coming to meeting + hmac refactoring

 *)

Check sha_h.

Module Equiv.
Definition c := (8 * SHA256_.DigestLength)%nat.
Variable p : nat.
Check HMAC (sha_h c plus). 
Check HMAC (sha_h c plus) sha_iv.

(* c needs to be not forall, should be 8 * digest length *)
Theorem HMAC_spec_equiv : forall
                            (c p : nat)
                            (k m h : list Z)
                            (K : Bvector (plus c p)) (M : Blist) (H : Bvector c),
                            
                            (* assuming k is already padded? *)
  (8 * (length (HMAC_FUN.mkKey k)))%nat = (c + p)%nat ->
  bytes_bits_vector c p k K -> bytes_bits_lists m M ->
  HMAC (sha_h c plus) sha_iv (sha_splitandpad_vector c p) (fpad p) opad ipad K M = H ->
  HMAC_FUN.HMAC k m = h ->
  (* TODO fix HMAC h iv splitAndPad fpad opad ipad K M *)
  bytes_bits_vector' h H.
Proof.

Abort.

