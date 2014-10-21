Require Import SHA256.
Require Import pure_lemmas.
Require Import Coqlib.
Require Import Integers.

(* Lemma 1: M = Prefix(Pad(M)) *)

Inductive Prefix {X : Type} : list X -> list X -> Prop :=
  | p_nil : forall (l : list X), Prefix [] l
  | p_self : forall (l : list X), Prefix l l
  | p_cons : forall (l1 l2 : list X) (x : X), Prefix l1 l2 -> Prefix (x :: l1) (x :: l2)
  | p_append : forall (l1 l2 : list X) (l3 : list X), Prefix l1 l2 -> Prefix l1 (l2 ++ l3).
  (* | p_trans : forall (l1 l2 l3 : list X), Prefix l1 l2 -> Prefix l2 l3 -> Prefix l1 l2. *)

Inductive InWords : list Z -> Prop :=
  | words_nil : InWords []
  | words_word : forall (a b c d : Z) (msg : list Z),
                   InWords msg -> InWords (a :: b :: c :: d :: msg).

(* ----------------- ^ Definitions *)

Check NPeano.divide.
Print NPeano.divide.
Check list_repeat.
Print list_repeat.

Lemma fstpad_len :
  forall (msg : list Z),
    Datatypes.length (msg ++ [128]
                 ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0)
= (Datatypes.length msg + (S (Z.to_nat (- (Zlength msg + 9) mod 64))))%nat.
Proof.
  intros msg.
  simpl.
  SearchAbout length.
  rewrite -> app_length.
  simpl.
  SearchAbout list_repeat.
  rewrite -> length_list_repeat.
  reflexivity.
Qed.  

(* Originally from Lemma 2: *)

Print NPeano.div.

Lemma total_pad_len_Zlist : forall (msg : list Z), 
     length
       (msg ++ [128] ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0)
     = (
         (NPeano.div (Z.to_nat (Zlength msg) + 8) 4%nat + 14%nat)
          * Z.to_nat WORD
     )%nat.
Proof.
  intros msg.
  repeat rewrite -> fstpad_len.
  replace (S (Z.to_nat (- (Zlength msg + 9) mod 64)))
    with (1 + (Z.to_nat (- (Zlength msg + 9) mod 64)))%nat by omega.
  
  (* simpl. *)
  (* TODO *)

Admitted.

Print NPeano.divide.
SearchAbout NPeano.divide.

Lemma InWords_len4 : forall (l : list Z),
                       NPeano.divide (Z.to_nat WORD) (length l) -> InWords l.
Proof.
  intros l [x H].
  revert l H.
  induction x.
  intros l H. simpl in H. 
  destruct l.
    apply words_nil.
    simpl in H. inversion H.
  intros l H.
  destruct l as [ | a [ | b [ | c [ | d ? ]]]].
    inversion H.
    inversion H.
    inversion H.
    inversion H.
    specialize (IHx l).
      apply words_word.
      apply IHx.
      simpl in H. inversion H.
      simpl. apply H1.
Qed.  

Lemma pad_inwords :
  forall (msg : list Z),
    InWords (msg ++ [128]
                 ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0).
Proof.
  intros msg.
  apply InWords_len4.
  pose proof total_pad_len_Zlist.
  specialize (H msg).
  unfold NPeano.divide.
  exists (NPeano.div (Z.to_nat (Zlength msg) + 8) 4 + 14)%nat.
  apply H.
Qed.  

Definition fulllen (len : Z) :=
  len + 1%Z + (- (len + 9) mod 64).

Eval compute in fulllen 0.      (* 56 / 4 = 14 32-bit ints;
                                   56 + 8 = 64 bytes;
                                   64 / 4 = 16 32-bit ints;
                                   16 * 32 = 512 bits; 512 / 256 = 2 blocks of length 256 *)
Eval compute in fulllen 1.      (* 56 / 4 = 14 *)
Eval compute in fulllen 2.      (* 56 / 4 = 14 *)
Eval compute in fulllen 55.      (* 56 / 4 = 14 *)
Eval compute in fulllen 56.      (* 120 / 4 = 30 *)
Eval compute in fulllen 119.     (* 120 *)
Eval compute in fulllen 120.    (* 184 *)
Eval compute in fulllen 121.
Eval compute in fulllen 200.    (* 248 + 8 = 256 *)

Eval compute in (-1) mod 5.
(* SearchAbout modulo. *)
(* SearchAbout mod. *)

(* *** New definition for this lemma. *)
Definition pad (msg : list Z) : list Z := 
  let n := Zlength msg in
  msg ++ [128%Z] 
      ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0
      ++ intlist_to_Zlist ([Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)]).

Definition generate_and_pad' (msg : list Z) : list int :=
  Zlist_to_intlist (pad msg).

(* C-c C-l *)
SearchAbout Zlist_to_intlist.

Lemma app_left : forall (a b c d : list Z),
   a ++ b ++ c ++ d = (a ++ b ++ c) ++ d.
(* a ++ (b ++ (c ++ d)) = (a ++ (b ++ c)) ++ d *)
Proof.
   intros a b c d.
   assert (b ++ (c ++ d) = (b ++ c) ++ d) as assert1.
     rewrite -> app_assoc. reflexivity.
   rewrite -> assert1.
   rewrite -> app_assoc.
   reflexivity.
Qed.

Theorem pad_compose_equal : forall (msg : list Z),
                              generate_and_pad' msg = generate_and_pad msg.
Proof.
  intros msg.
  unfold generate_and_pad'.
  unfold pad.
  unfold generate_and_pad.
  (* need il => ZIL (IZL il), and
     ZIL a ++ Zil b = ZIL (a ++ b) (with length a being a multiple of 4)
   *)
  pose proof pad_inwords as pad_inwords.
  specialize (pad_inwords msg).
  rewrite -> app_left.
  induction pad_inwords.
  (* case none *)
    assert (forall l : list Z, [] ++ l = l) as Happend. reflexivity.
    specialize (Happend (intlist_to_Zlist
        [Int.repr (Zlength msg * 8 / Int.modulus),
        Int.repr (Zlength msg * 8)])).
    rewrite -> Happend.
    rewrite -> intlist_to_Zlist_to_intlist.
    reflexivity.
  (* case a :: b :: c :: d :: msg0 *)
    Opaque intlist_to_Zlist.
    simpl.
    apply f_equal.
    apply IHpad_inwords.
Qed.    

(* Proof easy with pad definition *)
Theorem prefix : forall (msg : list Z),
                   Prefix msg (pad msg).
Proof.
  intros msg.
  unfold pad.
  apply p_append.
  apply p_self.
Qed.  
  
  
(* ------------------------------------------------ *)

(* Lemma 2: |M1| = |M2| -> |Pad(M1)| = |Pad(M2)| *)

Print NPeano.divide.
Print NPeano.div.
Check NPeano.div.
            
(* Alternatively, could use my equivalent gap function,
or the proof about first part *)
(* see length_Zlist_to_intlist in pure_lemmas *)

Lemma total_pad_len_intlist : forall (msg : list Z),
      length (generate_and_pad msg) =
      ((NPeano.div (Z.to_nat (Zlength msg) + 8) 4 + 14)%nat
      + 2%nat)%nat. (* n + 2 *)
Proof.  
  intros msg.
  remember (NPeano.div (Z.to_nat (Zlength msg) + 8) 4 + 14)%nat as quot.
  unfold generate_and_pad.
  rewrite -> app_length.
  assert (Datatypes.length
      (Zlist_to_intlist
         (msg ++
          128%Z :: list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0%Z))
          = quot) as assert_fstlen.
    apply length_Zlist_to_intlist.
    rewrite -> mult_comm.
    rewrite -> Heqquot.
    apply total_pad_len_Zlist.
  Opaque NPeano.div.
  simpl.
  rewrite -> assert_fstlen.
  reflexivity.
Qed.  
  
Theorem length_equal_pad_length : forall (msg1 : list Z) (msg2 : list Z),
     Zlength msg1  = Zlength msg2 ->
     Zlength (generate_and_pad msg1) = Zlength (generate_and_pad msg2).
Proof.
  intros m1 m2 H.
  SearchAbout Zlength.
  repeat rewrite -> Zlength_correct.
  repeat rewrite -> total_pad_len_intlist.
  rewrite -> H.
  reflexivity.
Qed.  

(* ------------------------------------------------ *)

(* Lemma 3: |M1| =/= |M2| ->
last block of Pad(M1) =/= last block of Pad(M2) *)

Definition generate_and_pad_copy msg := 
  let n := Zlength msg in
   Zlist_to_intlist (msg ++ [128%Z] 
                ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0)
           ++ [Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)].

(* Probably easier to use the rewritten version; already "proved"
 that that's in blocks of 4 *)

(* TODO *)

