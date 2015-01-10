Require Import HMAC_functional_prog.
Require Import SHA256.
Require Import ByteBitRelations.
Require Import Integers.
Require Import sha_padding_lemmas.
Require Import Recdef.
Require Import List.
Require Import Arith.
Require Import Coqlib.

Definition Blist := list bool.

Definition concat {A : Type} (l : list (list A)) : list A :=
  flat_map id l.

(* Replacing splitVector *)
Definition splitList {A : Type} (n : nat) (l : list A) : (list A * list A) :=
  (firstn n l, skipn n l).

(* Replacing BVxor *)
Definition BLxor (xs : Blist) (ys : Blist) :=
  map (fun p => xorb (fst p) (snd p)) (combine xs ys).

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


(* TODO use neater definition with conversion functions *)
(* TODO split out of HMAC_spec_pad *)

Definition c := (SHA256_.DigestLength * 8)%nat.
Definition p := (32 * 8)%nat.
Definition b := (c + p)%nat.
Definition BlockSize := 64.

Definition intsToBits (l : list int) : list bool :=
  bytesToBits (SHA256.intlist_to_Zlist l).

Definition bitsToInts (l : Blist) : list int :=
  SHA256.Zlist_to_intlist (bitsToBytes l).

Definition sha_iv : Blist :=
  intsToBits SHA256.init_registers.

Definition sha_h (regs : Blist) (block : Blist) : Blist :=
  intsToBits (SHA256.hash_block (bitsToInts regs) (bitsToInts block)).

Definition sha_splitandpad (msg : Blist) : Blist :=
  bytesToBits (sha_padding_lemmas.pad (bitsToBytes msg)).

(* modified version of sha_padding_lemmas.pad *)
Definition pad_inc (msg : list Z) : list Z := 
  let n := BlockSize + Zlength msg in
  msg ++ [128%Z] 
      ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0
      ++ intlist_to_Zlist ([Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)]).

Definition sha_splitandpad_inc (msg : Blist) : Blist :=
  bytesToBits (pad_inc (bitsToBytes msg)).

(* artifact of app_fpad definition *)
Definition fpad_inner (msg : list Z) : list Z :=
  let n := BlockSize + Zlength msg in
  [128%Z] 
    ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0
    ++ intlist_to_Zlist ([Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)]).

Definition fpad (msg : Blist) : Blist :=
  bytesToBits (fpad_inner (bitsToBytes msg)).

(* --------------- *)

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

Lemma length_not_emp :
  forall {A B : Type} (l : list A) (z y : B),
    (Datatypes.length l > 0)%nat -> match l with [] => z | _ => y end = y.
Proof.
  intros.
  induction l as [ | x xs].
  - inversion H.
  - reflexivity.
Qed.

Lemma split_append_id : forall {A : Type} (len : nat) (l1 l2 : list A),
                               length l1 = len -> length l2 = len ->
                               splitList len (l1 ++ l2) = (l1, l2).
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
