(* Andrew W. Appel and Stephen Yi-Hsien Lin,
    May 2013, October 2013, March 2014 *)

Require Recdef.
Require Import Integers.
(* Add LoadPath "~/Desktop/Code/research/vst/compcert/lib". *)
Require Import Coqlib.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import List. 

Require Import pure_lemmas.

(* THIS BLOCK OF STUFF is not needed to define SHA256,
  but is useful for reasoning about it *)
Definition LBLOCKz : Z := 16. (* length of a block, in 32-bit integers *)
Definition WORD : Z := 4.  (* length of a word, in bytes *)
Definition CBLOCKz : Z := (LBLOCKz * WORD)%Z. (* length of a block, in characters *)
Definition hilo hi lo := (Int.unsigned hi * Int.modulus + Int.unsigned lo)%Z.
Definition isbyteZ (i: Z) := (0 <= i < 256)%Z.
Definition big_endian_integer (contents: Z -> int) : int :=
  Int.or (Int.shl (contents 0) (Int.repr 24))
  (Int.or (Int.shl (contents 1) (Int.repr 16))
   (Int.or (Int.shl (contents 2) (Int.repr 8))
      (contents 3))).
(* END OF "THIS BLOCK OF STUFF" *)

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).

Lemma skipn_length:
  forall {A} n (al: list A), 
    (length al >= n)%nat -> 
    (length (skipn n al) = length al - n)%nat.
Proof.
 induction n; destruct al; simpl; intros; auto.
 apply IHn. omega.
Qed.

Lemma skipn_length_short:
  forall {A} n (al: list A), 
    (length al < n)%nat -> 
    (length (skipn n al) = 0)%nat.
Proof.
 induction n; destruct al; simpl; intros; auto.
 omega.
 apply IHn. omega.
Qed.

(* PREPROCESSING: CONVERTING STRINGS TO PADDED MESSAGE BLOCKS *)

(*converting a string to a list of Z *)
Fixpoint str_to_Z (str : string) : list Z :=
  match str with
    |EmptyString => nil
    |String c s => Z.of_N (N_of_ascii c) :: str_to_Z s
    end.

(*combining four Z into a Integer*)
Definition Z_to_Int (a b c d : Z) : Int.int :=
  Int.or (Int.or (Int.or (Int.shl (Int.repr a) (Int.repr 24)) (Int.shl (Int.repr b) (Int.repr 16)))
            (Int.shl (Int.repr c) (Int.repr 8))) (Int.repr d).

Fixpoint Zlist_to_intlist (nl: list Z) : list int :=
  match nl with
  | h1::h2::h3::h4::t => Z_to_Int h1 h2 h3 h4 :: Zlist_to_intlist t
  | _ => nil
  end.

Definition generate_and_pad msg := 
  let n := Zlength msg in
   Zlist_to_intlist (msg ++ [128%Z] 
                ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0)
           ++ [Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)].

(* ------------------------------------ LEMMAS *)

(* Lemma 1: M = Prefix(Pad(M)) *)
(* see end *)

(* ------- *)

(* Lemma 2: |M1| = |M2| -> |Pad(M1)| = |Pad(M2)| *)






(* ------- *)

(* Lemma 3: |M1| =/= |M2| -> last block of Pad(M1) =/= last block of Pad(M2) *)




(* ------------------------------------------- *)

(*ROUND FUNCTION*)

(*hardcoding the constants, first 32 bits of the fractional parts of the cube roots of the first 64 prime numbers*)
Definition K256 := map Int.repr
  [1116352408 , 1899447441, 3049323471, 3921009573,
   961987163   , 1508970993, 2453635748, 2870763221,
   3624381080, 310598401  , 607225278  , 1426881987,
   1925078388, 2162078206, 2614888103, 3248222580,
   3835390401, 4022224774, 264347078  , 604807628,
   770255983  , 1249150122, 1555081692, 1996064986,
   2554220882, 2821834349, 2952996808, 3210313671,
   3336571891, 3584528711, 113926993  , 338241895,
   666307205  , 773529912  , 1294757372, 1396182291,
   1695183700, 1986661051, 2177026350, 2456956037,
   2730485921, 2820302411, 3259730800, 3345764771,
   3516065817, 3600352804, 4094571909, 275423344,
   430227734  , 506948616  , 659060556  , 883997877,
   958139571  , 1322822218, 1537002063, 1747873779,
   1955562222, 2024104815, 2227730452, 2361852424,
   2428436474, 2756734187, 3204031479, 3329325298].

(*functions used for round function*)
Definition Ch (x y z : int) : int :=
  Int.xor (Int.and x y) (Int.and (Int.not x) z).

Definition Maj (x y z : int) : int :=
  Int.xor (Int.xor (Int.and x z) (Int.and y z) ) (Int.and x y).

Definition Rotr b x := Int.ror x (Int.repr b).
Definition Shr b x := Int.shru x (Int.repr b).

Definition Sigma_0 (x : int) : int := 
          Int.xor (Int.xor (Rotr 2 x) (Rotr 13 x)) (Rotr 22 x).
Definition Sigma_1 (x : int) : int := 
          Int.xor (Int.xor (Rotr 6 x) (Rotr 11 x)) (Rotr 25 x).
Definition sigma_0 (x : int) : int := 
          Int.xor (Int.xor (Rotr 7 x) (Rotr 18 x)) (Shr 3 x).
Definition sigma_1 (x : int) : int := 
          Int.xor (Int.xor (Rotr 17 x) (Rotr 19 x)) (Shr 10 x).

(* word function *)
Function W (M: Z -> int) (t: Z) {measure Z.to_nat t} : int :=
  if zlt t 16 
  then M t 
  else  (Int.add (Int.add (sigma_1 (W M (t-2))) (W M (t-7)))
               (Int.add (sigma_0 (W M (t-15))) (W M (t-16)))).
Proof.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
intros; apply Z2Nat.inj_lt; omega.
Qed.

(*registers that represent intermediate and final hash values*)
Definition registers := list int.

Fixpoint map2 {A B C: Type} (f: A -> B -> C) (al: list A) (bl: list B) : list C :=
 match al, bl with
  | a::al', b::bl' => f a b :: map2 f al' bl'
  | _, _ => nil
  end.

(*initializing the values of registers, first thirty-two bits of the fractional
    parts of the square roots of the first eight prime numbers*)
Definition init_registers : registers := 
  map Int.repr  [1779033703, 3144134277, 1013904242, 2773480762,
                        1359893119, 2600822924, 528734635, 1541459225].

Definition nthi (il: list int) (t: Z) := nth (Z.to_nat t) il Int.zero.

Definition rnd_function (x : registers) (k : int) (w : int) : registers:=
  match x with 
  |  [a, b, c, d, e, f, g, h] => 
     let T1 := Int.add (Int.add (Int.add (Int.add h (Sigma_1 e)) (Ch e f g)) k) w in
     let T2 := Int.add (Sigma_0 a) (Maj a b c) in
       [Int.add T1 T2, a, b, c, Int.add d T1, e, f, g]
  | _ => nil  (* impossible *)
  end.

Function Round  (regs: registers) (M: Z ->int) (t: Z) 
        {measure (fun t => Z.to_nat(t+1)) t} : registers :=
 if zlt t 0 then regs 
 else rnd_function (Round regs M (t-1)) (nthi K256 t) (W M t).
Proof. intros; apply Z2Nat.inj_lt; omega.
Qed.

Definition hash_block (r: registers) (block: list int) : registers :=
      map2 Int.add r (Round r (nthi block) 63).

Function hash_blocks (r: registers) (msg: list int) {measure length msg} : registers :=
  match msg with
  | nil => r
  | _ => hash_blocks (hash_block r (firstn 16 msg)) (skipn 16 msg)
  end.
Proof. intros.
 destruct (lt_dec (length msg) 16).
 rewrite skipn_length_short. simpl; omega. rewrite <- teq; auto.
 rewrite skipn_length. simpl; omega. rewrite <- teq; omega.
Qed.

Fixpoint intlist_to_Zlist (l: list int) : list Z :=
 match l with
 | nil => nil
 | i::r =>
     Int.unsigned (Shr 24 i) ::
     Int.unsigned (Int.and (Shr 16 i) (Int.repr 255)) ::
     Int.unsigned (Int.and (Shr 8 i) (Int.repr 255)) ::
     Int.unsigned (Int.and i (Int.repr 255)) ::
     intlist_to_Zlist r
 end.

Definition SHA_256 (str : list Z) : list Z :=
    intlist_to_Zlist (hash_blocks init_registers (generate_and_pad str)).

(* ------------ *)
(* TODO remove *)
Definition generate_and_pad_c msg := 
  let n := Zlength msg in
   Zlist_to_intlist (msg ++ [128%Z] 
                ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0)
           ++ [Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)].

(* ------------------------------------ LEMMAS *)

(* Lemma 1: M = Prefix(Pad(M)) *)
(* see end *)

Inductive Prefix {X : Type} : list X -> list X -> Prop :=
  | p_nil : forall (l : list X), Prefix [] l
  | p_self : forall (l : list X), Prefix l l
  | p_cons : forall (l1 l2 : list X) (x : X), Prefix l1 l2 -> Prefix (x :: l1) (x :: l2)
  | p_append : forall (l1 l2 : list X) (l3 : list X), Prefix l1 l2 -> Prefix l1 (l2 ++ l3)
  | p_trans : forall (l1 l2 l3 : list X), Prefix l1 l2 -> Prefix l2 l3 -> Prefix l1 l2.
                               (* might want to prove some of these -- too powerful *)

Inductive InWords : list Z -> Prop :=
  | words_nil : InWords []
  | words_word : forall (a b c d : Z) (msg : list Z),
                   InWords msg -> InWords (a :: b :: c :: d :: msg).

Lemma split_Zlist_to_intlist : forall (l1 : list Z) (l2 : list Z),
   InWords l1 -> Zlist_to_intlist (l1 ++ l2) = Zlist_to_intlist l1 ++ Zlist_to_intlist l2.
Proof.
  intros l1 l2 E.                 (* careful *)
  induction E.
  (* case none *)
    reflexivity.
  (* case cons 4 *)
    simpl.
    rewrite -> IHE.
    reflexivity.
Qed.    

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

(* Similar to prev for lemma 1 *)
  
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
  exists (16 * Z.to_nat (- (Zlength msg + 9) mod 64) - 2)%nat.
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


(* Think about it -- what is the goal of this padding function? *)

(* - (n + 9) mod 64 = -n - 9 mod 64 = -n + 55 mod 64 = (64 - n) + 55 mod 64, where n >= 0 
or it's (-n -8 -1) mod 64 = (64m - n - 1 - 8) mod 64
honestly it might be easier to add the +8 in...
*)

(* n + 1 + (- (n + 9)) + 64m, m minimum S.T. entire thing is a multiple of... something
n + 1 + (-n - 9) + 64m 
-8 + 64m, such that -8 + 64m > 0? not right, but kind of makes sense 
(multiple of 64 minus 8 for length)


 *)

(* 
WTS: (n + 1 + (- (n + 9) mod 64)) = 0 (mod 4)
(we have no assumptions about n)

Why mod 64?

We want the entire length to be a multiple of 512 bits = 64 bytes (64 Zs)
k bytes 0, k such that the length is 448 bits = 56 bytes (56 Zs) **mod 64 (bytes)**

This is SHA-256. msg of length 1 byte (1 Z) -> pad1 to 56 byte
-> add length, pad2 to 64 byte
-> divide by 4 (4 byte per 32-bit int) = 16 32-bit integers
 *)

  
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
   (* forall (A : Type) (l m n : list A), l ++ m ++ n = (l ++ m) ++ n *)
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

(* TODO: this lemma is not used *)
Lemma zlength_intlist_zlist' :
  forall (msg1 : list Z) (msg2 : list Z) (pad : list Z),
    Zlength msg1 = Zlength msg2 ->
    Zlength (Zlist_to_intlist (msg1 ++ pad)) =
    Zlength (Zlist_to_intlist (msg2 ++ pad)).
Proof.
  intros msg1 msg2 pad Hlen.

Admitted.

Print NPeano.divide.
Print NPeano.div.
Check NPeano.div.
            
(* Alternatively, could use my equivalent gap function,
or the proof about first part *)
(* see length_Zlist_to_intlist in pure_lemmas *)

(* Lemma fstpad_len :
  forall (msg : list Z),
    Datatypes.length (msg ++ [128]
                 ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0)
= (Datatypes.length msg + (S (Z.to_nat (- (Zlength msg + 9) mod 64))))%nat. *)

Lemma total_pad_len_intlist : forall (msg : list Z),
      length (generate_and_pad msg) = 7%nat. (* n + 2 *)
(* TODO *)
(* Something as a function of Zlength msg? or something independent
(0 mod 512)?  *)
Proof.  
  intros msg.
  unfold generate_and_pad.
  rewrite -> app_length.
  simpl.
  assert (Datatypes.length
      (Zlist_to_intlist
         (msg ++
          128%Z :: list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0%Z))
      = 5%nat) as assert_fstlen.
    apply length_Zlist_to_intlist.
    apply total_pad_len_Zlist.
  rewrite -> assert_fstlen.
  reflexivity.
Qed.  
  
(* length (
(Zlist_to_intlist
        (msg ++
         [128] ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0) ) *)
  
Theorem length_equal_pad_length : forall (msg1 : list Z) (msg2 : list Z),
     Zlength msg1  = Zlength msg2 ->
     Zlength (generate_and_pad msg1) = Zlength (generate_and_pad msg2).
Proof.
  intros m1 m2 H.
  SearchAbout Zlength.
  repeat rewrite -> Zlength_correct.
  repeat rewrite -> total_pad_len_intlist.
  reflexivity.
Qed.  
  

