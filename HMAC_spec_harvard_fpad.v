Set Implicit Arguments.

Require Import Bvector.
Require Import List.
Require Import Arith.

Require Import HMAC_functional_prog.
Require Import Integers.
Require Import Coqlib.

(* Require Import List. Import ListNotations. *)

Definition Blist := list bool.

Fixpoint splitVector (A : Set) (n m : nat) :
  Vector.t A (n + m) -> (Vector.t A n * Vector.t A m) :=
  match n with
    | 0%nat =>
      fun (v : Vector.t A (O + m)) => (@Vector.nil A, v) (* TODO *)
    | S n' =>
      fun (v : Vector.t A (S n' + m)) =>
        let (v1, v2) := splitVector _ _ (Vector.tl v) in
          (Vector.cons _ (Vector.hd v) _ v1, v2)
  end.

Definition concatToList (n m : nat) (v1 : Bvector n) (v2 : Bvector m) : Blist :=
  Vector.to_list v1 ++ Vector.to_list v2.

Section HMAC.

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

  Check hash_words.
  Check h_star.

  Variable splitAndPad : Blist -> list (Bvector b).

  Definition compose {A B C : Type} (f : B -> C) (g : A -> B) (x : A) := f (g x).
  Notation "f @ g" := (compose f g) (at level 80, right associativity).

  Definition hash_words_padded : Blist -> Bvector c :=
    hash_words @ splitAndPad.

(* New design:

hash_words : list (Bvector b) -> Bvector c

split_and_pad : Blist -> list (Bvector b)

hash_words_padded : Blist -> Bvector c
   hash_words_padded := hash_words . split_and_pad

concatToList : Bvector n -> Bvector m -> Blist

(p, fpad, app_fpad removed; c <= b)

In line 3 of GHMAC_2K:
hash_words_padded (concatToList k_out h_in 

GNMAC? *)

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

  (* TODO fix this *)
  Definition GNMAC k m :=
    let (k_Out, k_In) := splitVector c c k in
    h k_Out (h_star_pad k_In m). (* could take head of list *)

  Check GNMAC. 
  (* Vector.t bool (c + c) -> list (Bvector b) -> Bvector c *)
  Check h.

Check hash_words.

  (* The "two-key" version of GHMAC and HMAC. *)
  (* Concatenate (K xor opad) and (K xor ipad) *)
  Definition GHMAC_2K (k : Bvector (b + b)) m :=
    let (k_Out, k_In) := splitVector b b k in (* concat earlier, then split *)
      let h_in := (hash_words (k_In :: m)) in
        hash_words_padded (concatToList k_Out h_in).

SearchAbout Bvector.

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

Check HMAC_SHA256.HMAC.            (* list Z -> list Z -> list Z *)

  (* Bvector is little-endian (least significant bit at head; list Z are just translated
from the string (ascii -> nat -> Z); but Int are packed big-endian (with 4 Z -> 1 Int)

each Z is one byte (8 bits) *)

(* TODO: add isbyteZ (from SHA256.v), 0 <= i <= 256 *)

(* *************** byte/bit computational *)

Lemma add_1_r_S : forall (n : nat), (n + 1)%nat = S n.
Proof.
  induction n.
    reflexivity.
    simpl. rewrite -> IHn. reflexivity.
Defined.

(* TODO step through this *)
Locate leb. Check negb.
(* little-endian *)
Fixpoint iterate (n : nat) (byte : nat) : Bvector n.
Proof.
  destruct n.
     apply (Vector.nil bool).
  remember ((byte - NPeano.pow 2 n)%nat) as byte_subtract.
  remember (negb (leb byte_subtract 0)) as bool_digit. (* changed from leb: gt now *)
  remember (if bool_digit then byte_subtract else byte) as num_new.
  rewrite <- add_1_r_S.
  apply (Vector.append (iterate n num_new) [bool_digit]). (* n' *)
Defined.

Print iterate.
Eval compute in iterate 1 255.
Check eq_rec. Print eq_rec. Print eq_rect. Check eq_rect.
Print NPeano.Nat.add_1_r.

(* TODO: fix the latter + 1 *)
Fixpoint byte_to_bits (byte : Z) : Bvector 8 :=
  let max_pow_two := 7%nat in
  iterate (max_pow_two + 1) (nat_of_Z byte + 1).

  Print add_1_r_S.
Eval compute in iterate 8 2.
Eval compute in byte_to_bits 0.
Eval compute in byte_to_bits 1.
Eval compute in byte_to_bits 2.

Eval compute in byte_to_bits 127.
Eval compute in byte_to_bits 128.
Eval compute in byte_to_bits 129.
Eval compute in byte_to_bits 200.
Eval compute in byte_to_bits 255.
Eval compute in byte_to_bits 256. (* not valid *)

(* Or: concatMap byte_to_bit bytes *)

Fixpoint bytes_to_bits (bytes : list Z) : Bvector (length bytes * 8) :=
  match bytes as x return Bvector (length x * 8) with (* CPDT *)
    | nil => Vector.nil bool
    | x :: xs => Vector.append (byte_to_bits x) (bytes_to_bits xs)
  end.


(* ************* inductive defs *)

Definition asZ (x : bool) : Z := if x then 1 else 0.

(* TODO: maybe prefer b : byte, with Byte.repr? *)
Definition convertByteBits (b : Z) (B : Bvector 8) : Prop :=
  exists (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
   B = [b0; b1; b2; b3; b4; b5; b6; b7] /\
   b =  (1 * (asZ b0) + 2 * (asZ b1) + 4 * (asZ b2) + 8 * (asZ b3)
         + 16 * (asZ b4) + 32 * (asZ b5) + 64 * (asZ b6) + 128 * (asZ b7)).

(* *** *)

(* relating list Z to Blist
bytes_to_bits m = length M

TODO: big-endian, little-endian?
*)
Inductive bytes_bits_lists : list Z -> Blist -> Prop :=
  | eq_empty : bytes_bits_lists nil nil
  | eq_cons : forall (bytes : list Z) (bits : Blist)
                     (byte : Z) (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
                bytes_bits_lists bytes bits ->
                convertByteBits byte [b0; b1; b2; b3; b4; b5; b6; b7] ->
                bytes_bits_lists (byte :: bytes)
                                (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bits).

(* *** *)

Lemma list_cons_len {A : Type} :
      forall (x : A) (xs : list A), length (x :: xs) = (1 + length xs)%nat.
Proof. intros. reflexivity. Defined.

Lemma mul_dist : forall (n m : nat), (n * (1 + m))%nat = (n + n * m)%nat.
Proof.
  intros. simpl.
  rewrite -> mult_succ_r. rewrite -> plus_comm. reflexivity.
Defined.

Print mult_succ_r.
Print plus_comm.

Fixpoint squash_list_vector
         (bits_list : list (Bvector 8)) : Bvector (8 * length bits_list).
Proof.
  destruct bits_list.
    apply (Vector.nil bool).
    rewrite -> list_cons_len.
    rewrite -> mul_dist.
    (* TODO watch out for endianness *)
  apply (Vector.append b0 (squash_list_vector bits_list)).
Defined.

SearchAbout Vector.cons.
Check Vector.cons.
Check Vector.cons bool true 1 [false].

(* TODO: how to write a better dependent pattern match? doesn't use the equality of their len
writing it as a proof and destructing n or b1/b2 doesn't work
*)
Fixpoint bvector_eq (n : nat) (m : nat) (b1 : Bvector n) (b2 : Bvector m) : bool :=
  match b1, b2 with             (*  match n as n0 return (Bvector n0) with *)
    | Vector.nil, Vector.nil => true
    | Vector.cons x1 _ xs1, Vector.cons x2 _ xs2 =>
      eqb x1 x2 && bvector_eq xs1 xs2
    | _, _ => false
  end.

(* TODO watch out for endianness *)

Definition bytes_bits_vector_comp
         (n : nat) (bytes : list Z) (bits : Bvector n) : bool.
Proof.
  remember (map byte_to_bits bytes) as bits_list_vector.
  remember (squash_list_vector bits_list_vector) as bvector.
  apply (bvector_eq bvector bits).
Defined.

Print bytes_bits_vector_comp.
(* Seems hard to use in a proof... *)

(* TODO: get this to be required *)
Eval compute in
    bytes_bits_vector_comp (0 :: nil) [true; true; true; true; true; true; true; true].

Lemma bytes_bits_vector_comp_len : forall (n : nat) (bytes : list Z) (bits : Bvector n),
                                     bytes_bits_vector_comp bytes bits = true
                                     -> n = (8 * length bytes)%nat.
Proof.
  (* TODO: bvector_eq is true iff the vectors are the same length *)
Admitted.

(* --------------------- *)

(* Lennart's definitions: *)

Definition bveqF :=
fix bveqF (n : nat) (b1 b2 : Bvector n) {struct n} : bool :=
  match n as n0 return (Bvector n0 -> Bvector n0 -> bool) with
  | 0%nat => fun _ _ : Bvector 0 => true
  | S n0 =>
      fun b3 b4 : Bvector (S n0) =>
      eqb (Vector.hd b3) (Vector.hd b4) &&
      bveqF n0 (Vector.tl b3) (Vector.tl b4)
  end b1 b2.

Fixpoint bveq (n:nat) (b1 b2:Bvector n): bool.
destruct n; intros. apply true. remember (S n) as m.
destruct b1. inversion Heqm. inversion Heqm. subst.  inversion b2. subst.
apply (eqb h h0 && bveq _ b1 H0).
(*  apply (eqb (Vector.hd b1) (Vector.hd b2) && (bveq _ (Vector.tl b1) (Vector.tl b2))).*)
Defined.

Print bveq.

Definition bveq1 (n:nat) (b1 b2:Bvector n): bool.
  induction n; intros. apply true.
  apply (eqb (Vector.hd b1) (Vector.hd b2) && (IHn (Vector.tl b1) (Vector.tl b2))).
Defined.

Definition bveqD :=
fun (n : nat) (b1 b2 : Bvector n) =>
nat_rec (fun n0 : nat => Bvector n0 -> Bvector n0 -> bool)
  (fun _ _ : Bvector 0 => true)
  (fun (n0 : nat) (IHn : Bvector n0 -> Bvector n0 -> bool)
     (b3 b4 : Bvector (S n0)) =>
   eqb (Vector.hd b3) (Vector.hd b4) && IHn (Vector.tl b3) (Vector.tl b4)) n
  b1 b2.

Eval compute in (bveqD [true; true; false] [true; true; false]).

(* TODO watch out for endianness *)

Definition bytes_bits_vector_comp'
         (bytes : list Z) (bits : Bvector (8 * length bytes)) : bool.
Proof.
  remember (map byte_to_bits bytes) as bits_list_vector.
  remember (squash_list_vector bits_list_vector) as bvector.
  assert (len_eq: length bytes = length bits_list_vector).
    rewrite -> Heqbits_list_vector.
    rewrite -> list_length_map.
    reflexivity.
  rewrite -> len_eq in bits.
  apply (bvector_eq bvector bits).
Defined.

(* *** *)

Inductive bytes_bits_vector : forall n
         (bytes : list Z) (bits : Bvector n), Prop :=
| bvv_nil: bytes_bits_vector nil []
| bvv_cons: forall n bytes1 bits1
                   (bt : Z) (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
              @bytes_bits_vector n bytes1 bits1 ->
              convertByteBits bt [b0; b1; b2; b3; b4; b5; b6; b7] ->
              @bytes_bits_vector (8 + n) (bt :: bytes1)
                                     (* TODO: is this the right endianness? *)
                                     (Vector.append [b0; b1; b2; b3; b4; b5; b6; b7] bits1).


(* ----------------------------------------- Theorem and parameters *)

Check HMAC_SHA256.HMAC.
Check HMAC.
(* HMAC
     : forall c p : nat,
       (Bvector c -> Bvector (b c p) -> Bvector c) ->   // compression function h
       Bvector c ->                          // iv, h's initialization vector
       (Blist -> list (Bvector (b c p))) ->  // splitAndPad (e.g. generate_and_pad)
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


for h: convert iv and chunk from bits to bytes, run SHA h, convert result from bytes to bits
for iv: SHA uses a list of 64 ints (block size), but here, we want 512 bits.
   normal bytes to bits conversion should work
for splitAndPad: convert msg from bits to bytes, run SHA generate_and_pad',
   convert to bits, split into list of block-size chunks (with proof that this is possible)
 *)

(* ------------------------------------- *)
Module Equiv.

Definition c:nat := (SHA256_.DigestLength * 8)%nat.

Definition p:=(32 * 8)%nat.

Parameter sha_iv : Bvector (SHA256_.DigestLength * 8).

(* Definition sha_h : list Z -> list Z := SHA256_.Hash. *)
Parameter sha_h : Bvector c -> Bvector (c + p) -> Bvector c.

Parameter sha_splitandpad_vector :
  Blist -> list (Bvector (SHA256_.DigestLength * 8 + p)).

(* Parameter fpad : Bvector p. *)

Definition bytes_bits_conv_vector'
           (byte_pad : byte) (bits_pad : Bvector (c + p)) : Prop :=
  let bytes_pad := map Byte.unsigned (HMAC_SHA256.sixtyfour byte_pad) in
  bytes_bits_vector bytes_pad bits_pad.

(* -------------- *)
(* Theorem lemmas *)

(*  (let (k_Out, k_In) :=
                       splitVector (b 256 256) (b 256 256)
                         (Vector.append (BVxor (b 256 256) K OP)
                            (BVxor (b 256 256) K IP)) in
Possibly try n = m -> splitVector n m...
*)

SearchAbout Bvector.

Lemma empty_vector : forall (v : Bvector 0),
                       v = [].
Proof.
  intros v.
  (* destruct v. *)

Admitted.

Lemma split_append_id : forall (len : nat) (v1 v2 : Bvector len),
                          splitVector len len (Vector.append v1 v2) = (v1, v2).
Proof.
  induction len; intros v1 v2.
  (* Case len = 0 *)
    (* simpl. rewrite -> empty_vector. *)


    Admitted.

(* Is this the theorem we want? Is it useful for the rest of the proofs?
Should it be more abstract? *)

(* TODO: 10/25/14

- add lemma for xor **
   - lennart: B2b (Byte.xor B1 B2) = Vector.map2 xorb (B2b B1) (B2b B2)
- fill in parameters: sha_h, sha_iv, sha_splitandpad_vector, (fpad) **
   - write bits to bytes function
- step through theorem
  - figure out how to use relations in theorem: compositional? f property? **

- clean up file
- look at ASCII library
   - rewrite iterate to emulate their conversion
- check bytes_bits_vector' fixpoint
   - look at new definitions, inductive?
   - see if induction works with it

- figure out how to get split lemmas to work
- skim Bellare proof and Adam's proof
- some other paper with a good approach?
- generalize technique for crypto
 *)

(* Options:
bytes_bits_vector (inductive, returns prop)
bytes_bits_vector_comp (returns bool)
bytes_bits_vector_comp' (returns bool) *)

Theorem HMAC_spec_equiv : forall
                            (k m h : list Z)
                            (K : Bvector (plus c p)) (M : Blist) (H : Bvector c)
                            (op ip : byte) (OP IP : Bvector (plus c p)),
  ((length k) * 8)%nat = (c + p)%nat ->
  bytes_bits_vector k K ->
  bytes_bits_lists m M ->
  bytes_bits_conv_vector' op OP ->
  bytes_bits_conv_vector' ip IP ->
  HMAC c sha_h sha_iv sha_splitandpad_vector OP IP K M = H ->
  HMAC_SHA256.HMAC op ip m k = h -> (* m k, not k m *)
  bytes_bits_vector h H.
Proof.
  intros k m h K M H op ip OP IP.
  intros padded_key_len padded_keys_eq msgs_eq ops_eq ips_eq.
  intros HMAC_abstract HMAC_concrete.
  unfold p, c in *.
  simpl in *.

  unfold HMAC in *. simpl in *.
  unfold HMAC_SHA256.HMAC in *.

  unfold HMAC_2K in *. unfold GHMAC_2K in *. (* unfold splitVector in *. *)
  (* Still abstract: sha_h, sha_splitandpad_vector *)
  Check sha_h. 
  rewrite -> split_append_id in HMAC_abstract.

  unfold HMAC_SHA256.OUTER in *. unfold HMAC_SHA256.INNER in *.
    unfold HMAC_SHA256.outerArg in *. unfold HMAC_SHA256.innerArg in *.
    unfold HMAC_SHA256.mkArgZ in *. unfold HMAC_SHA256.mkArg in *.

    unfold SHA256_.Hash in *. unfold functional_prog.SHA_256' in *.
    Print SHA256_.Hash.
    Print functional_prog.SHA_256'.
    Print functional_prog.generate_and_pad'.    
    simpl in *.
    Check hash_words. Print hash_words. Print h_star. Print fold_left.
    (*  : forall c p : nat,
       (Bvector c -> Bvector (b c p) -> Bvector c) ->
       Bvector c -> list (Bvector (b c p)) -> Bvector c  *)
    Check sha_h.    (*  : Bvector c -> Bvector (c + p) -> Bvector c *)

  unfold BVxor in *. unfold xorb in *. (* unfold Vector.map2 in *. *) 
  unfold Byte.xor in *. unfold Z.lxor in *.

  (* Lemma:

BVxor (b 256 256) K OP = Vector.map2 xorb K OP (can unfold xorb)
     ~
                          (map
                          (fun p0 : byte * byte => Byte.xor (fst p0) (snd p0))
                          (combine (map Byte.repr (HMAC_SHA256.mkKey k))
                             (HMAC_SHA256.sixtyfour ip)))

probably want a meta-lemma for composition of relations
r1 x X -> r2 y Y -> ?f ? -> f x y ~ F X Y

try with smaller examples first

figure out how to approach proof: avoid 4-way induction
 *)


  rewrite <- HMAC_abstract.
  rewrite <- HMAC_concrete.


  induction msgs_eq.


Abort.
