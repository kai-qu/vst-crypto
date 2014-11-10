Set Implicit Arguments.

Require Import Bvector.
Require Import List.
Require Import Arith.

Require Import HMAC_functional_prog.
Require Import Integers.
Require Import Coqlib.
Require Import sha_padding_lemmas.
Require Import functional_prog.

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

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) (x : A) := f (g x).
Notation "f @ g" := (compose f g) (at level 80, right associativity).

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

(* ---------------------------------------------------------------- *)
(* Some more computational bytes/bits conversion definitions *)
(* TODO: plural or singular? e.g. bit to byte *)

(* Bytes to bits *)


(* Bits to bytes *)


(* Bytes to bits to bytes *)


(* Bits to bytes to bits *)


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

Definition bytes_bits_conv_vector
           (byte_pad : byte) (bits_pad : Bvector (c + p)) : Prop :=
  let bytes_pad := map Byte.unsigned (HMAC_SHA256.sixtyfour byte_pad) in
  bytes_bits_vector bytes_pad bits_pad.

(*
TODO define computational version

Definition bytes_bits_conv_vector'
           (byte_pad : byte) -> Bvector (c + p)) :=
  let bytes_pad := map Byte.unsigned (HMAC_SHA256.sixtyfour byte_pad) in
  bytes_bits_vector bytes_pad bits_pad.
*)

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

- fill in parameters: sha_h, sha_iv, sha_splitandpad_vector, (fpad) **
   - write bits to bytes function
   - rewrite bytes to bits
   - replace inductive defs with computational?
   - functional_prog.generate_and_pad' has type list Z -> Z -> list int... rewrite it?
   - g_a_p has type list Z -> list int
   - Zlist_to_intlist?
   - using new fpad version: prove equivalence
   - prove SHA256.hash_blocks equivalence with fold
   - need inner lemmas, gradually build up to full theorem + composition lemmas
- step through theorem
  - figure out how to use relations in theorem: compositional? f property? **
- add lemma for xor **
   - lennart: B2b (Byte.xor B1 B2) = Vector.map2 xorb (B2b B1) (B2b B2)

- clean up file
- look at ASCII library
   - rewrite iterate to emulate their conversion
- check bytes_bits_vector' fixpoint
   - look at new definitions, inductive?
   - see if induction works with it
- figure out how to get split lemmas to work

- skim Bellare proof and Adam's proof
- read Adam's papers on FCF, etc.
- some other paper with a good approach?
- generalize technique for crypto
 *)

(* Options:
bytes_bits_vector (inductive, returns prop)
bytes_bits_vector_comp (returns bool)
bytes_bits_vector_comp' (returns bool) *)

  (*  (hash_words 256 sha_h sha_iv
                          (BVxor 512 K IP :: sha_splitandpad_vector M))

HMAC_SHA256.INNER op
                       (map Byte.repr (HMAC_SHA256.mkKey k)) m

Bvector c vs. list Z
 *)

Theorem HMAC_inner_equiv : forall
                             (k m : list Z)
                             (K : Bvector (plus c p)) (M : Blist)
                             (bits_inner : Bvector c) (bytes_inner : list Z)
                             (ip : byte) (IP : Bvector (plus c p)),
 ((length k) * 8)%nat = (c + p)%nat ->
  bytes_bits_vector k K ->
  bytes_bits_lists m M ->
  bytes_bits_conv_vector ip IP ->

  (* or-- hash_words_padded? *)
  hash_words 256 sha_h sha_iv
             (BVxor 512 K IP :: sha_splitandpad_vector M) = bits_inner ->

  HMAC_SHA256.INNER ip
                    (map Byte.repr (HMAC_SHA256.mkKey k)) m = bytes_inner ->

  bytes_bits_vector bytes_inner bits_inner.
Proof.
  intros k m K M bits_inner bytes_inner ip IP.
  intros padded_key_len padded_keys_eq msgs_eq ips_eq.
  intros HMAC_abs HMAC_con.
  


Admitted.  

(* ------------------ *)

Lemma comp : forall {A B C : Type} (f : B -> C) (g : A -> B) (x : A),
               (f @ g) x = f (g x).
Proof. intros.  reflexivity. Qed.



(*
Theorem equiv : forall {t T : Type}
                  (tT : t -> T) (Tt : T -> t)
                  (f : t -> t) (F : T -> T)
                  (x : t) (X : T),
                  x = Tt X      (* x ~ X *)
                  -> F = (tT @ f @ Tt) (* f = Tt @ F @ tT *)
                  -> f (Tt X) = Tt (tT (f (Tt X)))
                  -> f x = Tt (F X).
Proof.
  intros t T tT Tt f F x X.
  intros relation composition roundtrip.
  (* x ~ y := x = Tt y *)
  rewrite composition.
  rewrite relation.
  repeat rewrite -> comp.
  apply roundtrip.              (* specific to input-roundtrip-preserving property of f *)
Qed.  
*)

(* TODO look in Algebra lib *)
(* x ~ y -> f x ~ f y  , x y : a  *)

Theorem equiv' : forall {t T : Type} (* t = bits, T = bytes --
                                        list Z or list byte, Bvector Blist *)
                  (tT : t -> T) (Tt : T -> t)
                  (f : t -> t) (F : T -> T)
                  (x : t) (X : T),
                  x = Tt X      (* x ~ X *)
                  -> f = (Tt @ F @ tT)
                  -> (tT @ Tt) = id (* @ - comp *)
                  -> f x = Tt (F X). (* f x ~ F X -- byte_bits_vector *)
(* HMAC_abs (bytes_to_bytes m1) = bytes_to_bits (HMAC_CONCRETE m1) *)

(* TODO: start a section parametrized by ~, axioms about ~ *)
Proof.
  intros t T tT Tt f F x X.
  intros relation composition roundtrip.
  (* x ~ y := x = Tt y *)
  rewrite composition.
  rewrite relation.
  repeat rewrite -> comp.
  change (tT (Tt X)) with ((tT @ Tt) X).
  rewrite roundtrip.
  unfold id.
  reflexivity.
Qed.
  (* apply roundtrip.              (* specific to input-roundtrip-preserving property of f *) *)

Require Import JMeq.

Theorem equiv_JM : forall {t T : Type} (* t = bits, T = bytes --
                                        list Z or list byte, Bvector Blist *)
                  (tT : t -> T) (Tt : T -> t)
                  (f : t -> t) (F : T -> T)
                  (x : t) (X : T),
                  JMeq x X      (* x ~ X *)
                  -> JMeq f (Tt @ F @ tT)
                  -> (tT @ Tt) = id
                  -> JMeq (f x) (F X). (* f x ~ F X -- byte_bits_vector *)

(* TODO: start a section parametrized by ~, axioms about ~ *)
Proof.
  intros t T tT Tt f F x X.
  intros relation composition roundtrip.
  (* x ~ y := x = Tt y *)
  rewrite composition.
  apply eq_dep_id_JMeq.

  SearchAbout EqdepFacts.eq_dep.
  SearchAbout JMeq.
Abort.
(*
  rewrite relation.
    repeat rewrite -> comp.
  change (tT (Tt X)) with ((tT @ Tt) X).
  rewrite roundtrip.
  unfold id.
  reflexivity.
Qed.
*)

Theorem equiv_comp : forall {t T : Type}
                  (tT : t -> T) (Tt : T -> t)
                  (f : t -> t) (F : T -> T) (g : t -> t) (G : T -> T)
                  (x : t) (X : T),
                  x = Tt X
                  -> f = (Tt @ F @ tT)
                  -> f x = Tt (F X) (* inner composition *)

                  -> g = (Tt @ G @ tT) (* not sure if true *)
                  -> (tT @ Tt) = id
                  -> g (f x) = Tt (G (F X)).
Proof.
  intros t T tT Tt f F g G x X.
  intros relation composition_f inner composition_g roundtrip.
  apply equiv' with tT.
  (* Assump 1 *)
    apply inner.
  (* Assump 2 *)
    apply composition_g.
  (* Assump 3  *)
    apply roundtrip.
Qed.    

(* needs to be computational due to function composition? *)
Theorem equiv_prop : forall {t T : Type}
                  (tT : t -> T) (Tt : T -> t)
                  (* (Tt_prop : T -> t -> Prop) *)
                  (tT_prop : t -> T -> Prop)
                  (f : t -> t) (F : T -> T)
                  (x : t) (X : T),
                  tT_prop x X
                  -> f = (Tt @ F @ tT)
                  -> tT_prop (f x) (F X).
Proof.
  intros t T tT Tt tT_prop f F x X.
  intros relation composition.
  rewrite composition.
  (* rewrite relation. *)
  (* x = Tt X  <- bytes_to_bits *)

  repeat rewrite -> comp.
  
Admitted.

Parameter bB : forall m, Bvector m -> list Z.
Check bytes_to_bits.
Print bytes_bits_vector.

Theorem equiv_prop' : forall (m : nat)
                  (f : (forall n, Bvector n -> Bvector n)) (F : list Z -> list Z)
                  (x : Bvector m) (X : list Z),
                  bytes_bits_vector X x
                  -> F X = bB (f (length X * 8)%nat (bytes_to_bits X))
                  -> bytes_bits_vector (bB (f (length X * 8)%nat (bytes_to_bits X)))
                                       (f (length X * 8)%nat (bytes_to_bits X))
                  -> bytes_bits_vector (F X) (f m x).
Proof.
  intros m f F x X.
  intros relation composition roundtrip.
  (* rewrite composition. repeat rewrite -> comp. *)
  induction relation.
  (* Case nil *)
    assert (H1: F nil = nil). admit.
    assert (H2: f 0%nat [] = []). admit.
    rewrite -> H1. rewrite -> H2.
    apply bvv_nil.
  (* Case ind *)
    (* Vector.append is a problem *)
    rewrite -> composition.
    Print bytes_bits_vector. 
    
Admitted.
  

  (* true if

   bytes_to_bits bits_to_bytes x = x iff len x is divisible by 8
   (x : Bvector n)

   f (x : Bvector n * 8) : Bvector n' * 8 -- when?

   plus, how does the composition work?

       (hash_words_padded 256 sha_h sha_iv sha_splitandpad_vector
        (concatToList (BVxor 512 K OP)
           (hash_words 256 sha_h sha_iv
              (BVxor 512 K IP :: sha_splitandpad_vector M))))


 (hash_words_padded 256 sha_h sha_iv sha_splitandpad_vector
        (concatToList (BVxor 512 K OP) bits_inner)
 )

   *)
  
(* ------------------ *)

Require Import JMeq.

(* Parameter bbv (bytes : list Z) -> Bvector (length bytes). *)
Parameter bbl : (list Z -> Blist).
Parameter bbv_byte : forall n, (byte -> Bvector n).
Check JMeq.
Print JMeq.


(* TODO *)
Definition conv : forall (m n : nat) (e : Bvector n) (E : m = n), Bvector m.
Proof.
  intros m n h1 h2.
  rewrite -> h2.
  apply h1.
Defined.  

Lemma sn_eq : forall (n : nat), (n + 1)%nat = S n. Proof. Admitted.

Lemma test' : forall (n : nat) (b1 : Bvector (S n)) (b2 : Bvector (n + 1)),
               conv b1 (sn_eq n) = b2.
Proof.
Abort.  

(*
Doesn't typecheck, whereas the above does 
Lemma test : forall (n : nat) (b1 : Bvector (S n)) (b2 : Bvector (n + 1)),
               b1 = b2.
Proof.
  *)


Theorem HMAC_spec_equiv : forall
                            (k m h : list Z)
                            (K : Bvector (c + p)) (M : Blist) (H : Bvector c)
                            (op ip : byte) (OP IP : Bvector (plus c p))
                          (bits_inner : Bvector c) (bytes_inner : list Z),
  ((length k) * 8)%nat = (c + p)%nat ->
  (* bytes_to_bits k = K -> *)
  JMeq (bytes_to_bits k) K ->                  (* vector *)
  (* TODO: dependent equality / John Major
     to substitute K for k, need theorems about JM equality?
     finish specifying theorem, intro and elim JMeq
   *)
  (* bbl m = M ->                  (* list *) *)
  (* bbv_byte op = OP -> *)
  (* bbv_byte ip = IP -> *)
  True -> True -> True -> 
  HMAC p sha_h sha_iv sha_splitandpad_vector OP IP K M = H ->
  HMAC_SHA256.HMAC ip op m k = h -> (* m k, not k m *)
  (* bytes_to_bits h = H. *)
  JMeq (bytes_to_bits h) H.     (* H ~ h <- bytes_to_bits_vector, inductive def *)
(* computational CONVERTS bytes to bits *)

  (* inductive works because it defers the type-level computation,
     but function composition is computational... *)
Proof.
  intros k m h K M H op ip OP IP bits_inner bytes_inner.
  intros padded_key_len padded_keys_eq msgs_eq ops_eq ips_eq.
  intros HMAC_abstract HMAC_concrete.
  Check bytes_to_bits.
  Print c.
  (* apply equiv. *) (* TODO *)

SearchAbout JMeq.


  unfold p, c in *.
  simpl in *.

  unfold HMAC in *. simpl in *.
  unfold HMAC_SHA256.HMAC in *.

  unfold HMAC_2K in *. unfold GHMAC_2K in *. (* unfold splitVector in *. *)
  (* Still abstract: sha_h, sha_splitandpad_vector *)
  Check sha_h. 
  rewrite -> split_append_id in HMAC_abstract.

Check (hash_words 256 sha_h sha_iv
                          (BVxor 512 K IP :: sha_splitandpad_vector M)).

Check HMAC_SHA256.INNER ip
                       (map Byte.repr (HMAC_SHA256.mkKey k)) m.

  unfold HMAC_SHA256.OUTER in *. unfold HMAC_SHA256.INNER in *.
  pose proof HMAC_inner_equiv as inner_equiv.
  specialize inner_equiv with k m K M bits_inner bytes_inner ip IP.
  rewrite <- HMAC_abstract. rewrite <- HMAC_concrete.
Abort.
  (* apply equiv. *)
  

(* 
  Show: x ~ X -> f x ~ F X
  or: x ~ X -> y ~ Y -> f x y ~ F X Y
  or: f : b -> b, F -> B -> B

      SHOW: x:b ~ X:B -> F = bB . f . Bb ->  f x ~ F X
      f x ~ (bB . f . Bb) X
      f x ~ bB (f (Bb X))
      
      x ~ X means that x = Bb X
      so I need to show that f x = Bb (bB (f (Bb X))), given that x = Bb X

      or: f x = bytes_to_bits bits_to_bytes f bytes_to_bits X
          f bytes_to_bits x = bytes_to_bits bits_to_bytes f bytes_to_bits x
          bytes_to_bits bits_to_bytes = id ON f bytes_to_bits x 
          this depends on a property of f

question: how is bits_to_bytes defined? TODO

bytes = list Z (of length n)
  bytes to bits: convert each Z to Bvector 8; concat (maybe reversing for endianness) 
    into Bvector 8 * n
bits = Bvector m
  bits to bytes: 
   0100010101110 : pad with front zeroes until multiple of 8? (possibly reverse and pad)
     OR throw away the rest of the bits
     OR return nothing 
   e.g. 100 to a byte = 00000100 to a byte = 4 (as Z) 

-> 
 *)




Theorem HMAC_spec_equiv' : forall
                            (k m h : list Z)
                            (K : Bvector (plus c p)) (M : Blist) (H : Bvector c)
                            (op ip : byte) (OP IP : Bvector (plus c p)),
  ((length k) * 8)%nat = (c + p)%nat ->
  bytes_bits_vector k K ->
  bytes_bits_lists m M ->
  bytes_bits_conv_vector op OP ->
  bytes_bits_conv_vector ip IP ->
  HMAC c sha_h sha_iv sha_splitandpad_vector OP IP K M = H -> (* bits: h <- conversion . byte_h *)
  HMAC_SHA256.HMAC ip op m k = h -> (* m k, not k m *) (* bytes *)
  bytes_bits_vector h H.            (* TODO reverse capital/lowercase *)
Proof.
  intros k m h K M H op ip OP IP.
  intros padded_key_len padded_keys_eq msgs_eq ops_eq ips_eq.
  intros HMAC_abstract HMAC_concrete.

subst h.
subst H.
induction msgs_eq.
Focus 2.
(*
  + admit.
    +*) 
(*
  remember K as K'.
  assert (JMeq K K') by (subst; reflexivity).
  clear HeqK'.
  rewrite <- H0 in HMAC_abstract.

  unfold bytes_bits_conv_vector in ops_eq, ips_eq.
  pose (c + p)%nat as n0.
  assert (c + p = n0)%nat by auto.
  clearbody n0.
  revert OP IP padded_key_len K' padded_keys_eq ops_eq ips_eq H.

  Print bytes_bits_vector.
  Print HMAC.
  Print Vector.t.
  Print bytes_bits_lists.

  
  Set Printing All.
+
Check HMAC.
Print bytes_bits_conv_vector.
  remember (c + p)%nat as n0.
  revert HMAC_abstract.
Check @HMAC.
  + induction padded_keys_eq.
  
    
  induction h.                  (* TODO:  h nil -> H nil *)
  (* or -- induction on m *)
    + admit.                      (* use bullets *)
    +                             (* a :: h <-> H1 :: H@ .... H8 ... :: H *)
      rewrite <- HMAC_concrete.
      rewrite <- HMAC_abstract.
*)      
  intros.
  unfold p, c in *.
  simpl in *.

  (*  *)
  unfold HMAC in *. simpl in *.
  unfold HMAC_SHA256.HMAC in *.

  Check equiv'.
  Print bytes_bits_vector.

(* TODO: relate first byte of input with first byte of output?
        but the output is fixed length?
        f (x :: xs) = ? ... f xs

f x = g (h x)
h (x :: xs) = H x (h xs)



 *)

  unfold HMAC_2K in *. unfold GHMAC_2K in *. (* unfold splitVector in *. *)

Print HMAC_SHA256.OUTER.
(*
  apply IHmsgs_eq.
  (* Still abstract: sha_h, sha_splitandpad_vector *)
  Check sha_h.  *)

  rewrite -> split_append_id.

Print bytes_bits_conv_vector.
  
(* Check (hash_words 256 sha_h sha_iv *)
                          (* (BVxor 512 K IP :: sha_splitandpad_vector M)). *)

(* Check HMAC_SHA256.INNER ip *)
                       (* (map Byte.repr (HMAC_SHA256.mkKey k)) m. *)

  unfold HMAC_SHA256.OUTER in *. unfold HMAC_SHA256.INNER in *. 

    unfold SHA256_.Hash in *.
    
    (* -- *)

    unfold HMAC_SHA256.innerArg. unfold HMAC_SHA256.mkArgZ. unfold HMAC_SHA256.mkArg.
    

    (* -- *)

    rewrite -> functional_prog.SHA_256'_eq in *.
    unfold SHA256.SHA_256 in *.
    repeat rewrite <- sha_padding_lemmas.pad_compose_equal in *.
    unfold sha_padding_lemmas.generate_and_pad' in *.

    unfold hash_words_padded in *.
    unfold hash_words in *.
    unfold compose in *.
    (* hash_words_padded 256 sha_h sha_iv sha_splitandpad_vector
        ~ SHA256.hash_blocks SHA256.init_registers *)
    Check h_star 256 sha_h sha_iv. Check SHA256.hash_blocks SHA256.init_registers.
    Check hash_words_padded 256 sha_h sha_iv sha_splitandpad_vector.
    Print SHA256.registers.
    (* Blist -> Bvector c vs.
       list int -> SHA256.registers = list int *)
    (* unfold h_star in *. *)
    (* pad : list Z -> list Z *)

    (* unfold SHA256.hash_blocks in *. *)

    unfold HMAC_SHA256.outerArg in *. unfold HMAC_SHA256.innerArg in *.
    unfold HMAC_SHA256.mkArgZ in *. unfold HMAC_SHA256.mkArg in *.
    
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



Abort.

    (* just try on hash function?
       bytes_bits_vector (SHA (byte :: bytes))
                          (bytes_to_bits . SHA . bits_to_bytes) (b0 :: ... :: b7 :: bits))

just try on concatenation?

msgs_eq: 
c ++ m_bytes = c' ++' m_bits
induction 

c ++ (byte :: bytes) = c' ++' (b0 :: ... :: b7 :: bits)
(it's actually c' :: sha_splitandpad_vector (b0 :: ... :: b7 :: bits) -- try later)
given: c' = bytes_to_bits c (need to prove)
       ++' = Vector.append (or list cons)
       

TODO: HMAC_lemmas proof techniques?
maybe i should prove that it's impossible to prove equiv
   

     *)
Check Byte.unsigned.

Lemma xor_equiv : forall (ip : byte) (k : list Z) (r_bytes : list Z)
                  (IP : Bvector (c + p)) (K : Bvector (c + p)) (r_bits : Bvector (c + p)),
                    (length k * 8)%nat = (c + p) %nat ->
                    bytes_bits_conv_vector ip IP ->
                    bytes_bits_vector k K ->
                    map Byte.unsigned (
                          map
                            (fun p0 : Integers.byte * Integers.byte =>
                               Byte.xor (fst p0) (snd p0))
                            (combine (map Byte.repr (HMAC_SHA256.mkKey k))
                                     (HMAC_SHA256.sixtyfour ip))) = r_bytes ->
                    BVxor 512 K IP = r_bits ->
                    bytes_bits_vector r_bytes r_bits.
Proof.
  intros ip k r_bytes IP K r_bits.
  intros ips_eq keys_eq bytes_xor bits_xor.
  subst. unfold bytes_bits_conv_vector in *.
  unfold BVxor. SearchAbout Vector.map2.
(* problem: k and ip are both fixed length -- might want to do computationally *)
  (* induction keys_eq. *)
  
Admitted.

(* Lemma xor_equiv_comp : forall (ip : byte) (k : list Z) (r_bytes : list Z) *)
(*                   (IP : Bvector (c + p)) (K : Bvector (c + p)) (r_bits : Bvector (c + p)), *)
(*                     (length k * 8)%nat = (c + p) %nat -> *)

Lemma concat_equiv :
  forall (l1 : list Z) (l2 : Blist) (m1 : list Z) (m2 : Blist),
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

(* If inducting on the second param *)
Lemma concat_equiv_snd :
  forall (l1 : list Z) (l2 : Blist) (m1 : list Z) (m2 : Blist),
    bytes_bits_lists l1 l2
    -> bytes_bits_lists m1 m2
    -> bytes_bits_lists (l1 ++ m1) (l2 ++ m2).
(* bytes_bits_lists l1 l2 -> bytes_bits_lists m1 m2 -> bytes_bits_lists (l1 ++ m1) (l2 ++ m2) *)
Proof.
  intros l1 l2 m1 m2.
  intros fst_eq snd_eq.
  generalize dependent l1. generalize dependent l2.
  induction snd_eq; intros.
    + repeat rewrite app_nil_r.
      apply fst_eq.
    + induction fst_eq.           (* might need to generalize *)
      * repeat rewrite app_nil_l in *.
        apply eq_cons.
        apply snd_eq.
        - apply H.
      * simpl.
        apply eq_cons.
        apply IHfst_eq.
        - apply H0.
Qed.                            



