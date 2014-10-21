(* Andrew W. Appel and Stephen Yi-Hsien Lin,
    May 2013, October 2013, March 2014 *)

Require Recdef.
Require Import Integers.
Require Import Coqlib.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import List. 

Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).

Transparent Int.repr.

Check skipn.
Print skipn.
Eval compute in skipn 2 [1, 2, 3, 4].

Lemma skipn_length:
  forall {A} n (al: list A), 
    (length al >= n)%nat -> 
    (length (skipn n al) = length al - n)%nat.
Proof.
 induction n; destruct al; simpl; intros; auto.
 apply IHn; omega.
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

Print string.
Print Z.of_N.

(*converting a string to a list of Z *)
Fixpoint str_to_Z (str : string) : list Z :=
  match str with
    |EmptyString => nil
    |String c s => Z.of_N (N_of_ascii c) :: str_to_Z s
    end.

Eval compute in str_to_Z "abc".

Print Int.repr.
Print Int.shl.

(*combining four Z into a Integer*)
(* list nl of byte values -- if length nl is a multiple of 4, easy to define corresponding list of bid-endian 32-bit integers *)

(* ?!?! TODO *)


Transparent Int.repr Int.or Int.shl.

(* is there a bitstring rep? that might make things clearer *)
Definition Z_to_Int (a b c d : Z) : Int.int :=
  Int.or
    (Int.or (Int.or
               (Int.shl (Int.repr a) (Int.repr 24))
               (Int.shl (Int.repr b) (Int.repr 16))
            )
               (Int.shl (Int.repr c) (Int.repr 8))
    )
    (Int.repr d).

(* TODO prove lemma about Z_to_int? *)
Transparent Z_to_Int.

Eval compute in Int.repr 24.
Eval compute in Int.or (Int.repr 24) (Int.repr 10).
Check Int.shl.
Eval compute in Int.shl (Int.repr 4) (Int.repr 1). (* 8 *)
Eval compute in Int.shl (Int.repr 4) (Int.repr 8). (* 8 *)
(* Eval compute in Z_to_Int 0. *)
Eval compute in
      Int.or (Int.or (Int.or (Int.shl (Int.repr 0) (Int.repr 24)) (Int.shl (Int.repr 0) (Int.repr 16)))
            (Int.shl (Int.repr 0) (Int.repr 8))) (Int.repr 900). (* ??? but generate_and_pad works fine *)

Print Int.repr.
Print Int.Z_mod_modulus.
Print Int.wordsize. Print Wordsize_32.wordsize. (* 32 *)
Print Int.P_mod_two_p.                          (* ??? *)
Print positive.

Goal Int.repr 5 = Z_to_Int 2 0 0 0.
  unfold Z_to_Int.
  unfold Int.repr.
  simpl.
  unfold Int.or.
  simpl.
  unfold Int.repr.
  unfold Int.shl.
  simpl.                        (* this can eval Z_to_Int just fine... *)

  (* is it actually an error for one of these to be > 8 bytes? (256 bits) *)
  (*
     1 0 0 0 = 16777216
     0 1 0 0 = 65526
     0 0 257 0 = 65792
     0 0 1 0 = 256
     0 0 0 257 = 257
     0 0 0 2 = 2
     0 0 0 1 = 1
*)

  (* TODO maybe better with coq bitstrings?? *)


  (* takes 4 big-endian bytes (each byte is 8 bits -> 32 bits -> 1 32-bit int, or 1 word)

so anyway, the result is (len nl) / 4 (int division)
  *)

  (* so is nl always a multiple of 4? yes, but ... you assumed that msg was a multiple of 4

TODO: prove
InWords (msg ++ [128%Z] (* 1 *) ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0) 
(is multiple of 4)


 *)
  
Fixpoint Zlist_to_intlist (nl: list Z) : list int :=
  match nl with
  | h1::h2::h3::h4::t => Z_to_Int h1 h2 h3 h4 :: Zlist_to_intlist t
  | _ => nil
  end.

Eval compute in Int.repr (2^24).
Eval compute in Int.intval (Int.repr (2^24)).
Eval compute in Zlist_to_intlist [2, 0, 0, 0, 0, 0, 0, 1].

Print Z.to_nat.
Eval compute in (-5) mod 64.

(* TODO: figure out length of list_repeat *)
Definition generate_and_pad msg := 
  let n := Zlength msg in
   Zlist_to_intlist (msg ++ [128%Z] (* 1 *)
                ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0) (* 00...0 *)
           ++ [Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)]. (* length? in bytes *)

Eval compute in generate_and_pad [1].
Check generate_and_pad.

Definition lenint (n : Z) : list int :=
   [Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)]
.

Eval compute in lenint 4.
Eval compute in map Int.unsigned (lenint 4).

Print Int.unsigned.
Print Int.intval.

(* TODO is there an Int_to_Z... *)
Lemma length_pad_z_int :
  (* forall (n : Z), *)
   [Int.repr (5 * 8 / Int.modulus), Int.repr (5 * 8)]
   = Zlist_to_intlist [0, 0, 0, 0, 0, 0, 0, 0].
(* TODO figure out -- mult of 4? *)
Proof.
  simpl.
  unfold Z_to_Int.
  unfold Int.repr.
  simpl.
  unfold Int.or.
  simpl.
  unfold Int.repr.
  simpl.

  
Admitted.

Definition gap_nolen (msg : list Z) : list Z := 
  let n := Zlength msg in
    (msg ++ [128%Z] (* 1 *)
                ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0) (* 00...0 *)
.

Check gap_nolen.

Definition gap_len (msg : list Z) : list int := 
  let n := Zlength msg in
           [Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)]. (* length? in bytes *)


(* no length attached *)
Eval compute in gap_nolen [9, 9, 9].
(* 128%Z = ? *)


Fixpoint rep_helper {A : Type} (n : nat) (a : A) (l : list A) : list A :=
  match n with
    | 0%nat => l
    | S n' => rep_helper n' a (a :: l)
  end.

Definition rep {A : Type} (n : nat) (a : A) := rep_helper n a [].

Eval compute in rep_helper 10 5 [].
                      
Eval compute in gap_len [1, 1, 1, 1].
(* if n * 8 > 2^32, then make it the first bit?? *)
Definition modl : nat := Z.to_nat Int.modulus.
Eval compute in gap_len (rep 200 2).
(* try doing rep modl 2, and Coq shuts down, even though rep_helper is tail-recursive *)

Print Zpos.
Check Zpos 5.
Print Z.
(* Inductive Z : Set :=  Z0 : Z | Zpos : positive -> Z | Zneg : positive -> Z *)
Print nat_iter.
Check (1%positive).
Print positive.                 (* ??? *)

Print Int.modulus.              (* 2^32 *)
Print Int.wordsize.
Goal 2^32 = Int.modulus.           (* neat! *)
  unfold Int.modulus.
  unfold Int.wordsize.
  unfold Wordsize_32.wordsize.
  (* stop here? *)
  unfold two_power_nat.
  unfold shift_nat.
  (* unfold Zpos. *)
  unfold nat_iter.              (* ?? *)
  reflexivity.
Qed.  

Print Zlength_aux.

Transparent Int.repr.

Print Int.modulus.
Check Int.modulus.
Print Int.repr.
Check Int.repr.

(* block length? how to run? *)
(* can I change the spec? *)

Check generate_and_pad.
Eval compute in generate_and_pad nil.
Eval compute in map Int.unsigned (generate_and_pad nil).
Eval compute in length(map Int.unsigned (generate_and_pad [0])).
Eval compute in map Int.unsigned (generate_and_pad [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 999999, 99999, 99999, 9999]).
(* how do I make the resulting length change?? *)
Eval compute in generate_and_pad [0].

(* list Z -> list int *)
(* Zlength? *)
Theorem equal_pad_length : forall (msg1 : list Z) (msg2 : list Z),
     msg1 = msg2 -> Zlength (generate_and_pad msg1) = Zlength (generate_and_pad msg2).
Proof.
  intros m1 m2 H.
  rewrite -> H.
  reflexivity.
Qed.  

(* might need to rephrase this theorem,
e.g. len m1 = a -> len m2 = a -> len (gap m1) = b -> len (gap m2) = b... etc *)

(* What is the actual length of the padded message *)
(* Would be very if msg were inductively defined as a :: b :: c :: d :: list...
 nice induction on evidence (here we know msg % 4 = 0....) 
*)
Theorem length_padded : forall (msg : list Z) (n : Z), (* or type nat? *)
                          Zlength msg = n -> Zlength (Zlist_to_intlist msg) = n / 4.
Proof.
  
Abort.

(* What is the actual length of the padded message *)
Theorem length_padded : forall (msg : list Z) (n : Z), (* or type nat? *)
                          Zlength msg = n -> Zlength (generate_and_pad msg) = n.
Proof.
  
Abort.

(* Theorem: length msg + 1 + length (repeat whatever -- TODO) + 2 *)
SearchAbout Zlength.

Lemma zlength_out : forall (l1 : list Z) (l2 : list Z),
                      Zlength (l1 ++ l2) = Zlength l1 + Zlength l2.
Proof.
  intros l1 l2.
  rewrite -> Zlength_correct.
  rewrite -> Zlength_correct.
  rewrite -> Zlength_correct.
  induction l1 as [ | x xs].
  (* l1 = nil *)
    simpl. reflexivity.
  (* l1 = x :: xs *)
    simpl.
    unfold Zlength.
    simpl.
    unfold Zlength in IHxs.
Admitted.                       (* ??? *)

(* i don't think InWords msg is actually a necessary implication
but it might make the proof a lot easier
 *)
Inductive InWords : list Z -> Prop :=
  | words_nil : InWords []
  | words_word : forall (a b c d : Z) (msg : list Z),
                   InWords msg -> InWords (a :: b :: c :: d :: msg).


Lemma pad_inwords :
  forall (msg : list Z),
    InWords (msg ++ [128]
                 ++ list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0).
Proof.
  intros msg.
  
Admitted.  


Lemma zlength_intlist_zlist' :
  forall (msg1 : list Z) (msg2 : list Z) (pad : list Z),
    Zlength msg1 = Zlength msg2 ->
    Zlength (Zlist_to_intlist (msg1 ++ pad)) =
    Zlength (Zlist_to_intlist (msg2 ++ pad)).
Proof.
  intros msg1 msg2 pad Hlen.
  unfold Zlength.
  unfold Zlist_to_intlist.
  (* stuck *)
  
      
      
      

  
Admitted.  


(* there are problems with Zlength too, especially the aux business *)

Lemma zlength_intlist_zlist :
  forall (msg1 : list Z) (msg2 : list Z) (pad : list Z),
    InWords (msg1 ++ pad) -> InWords (msg2 ++ pad) (* messy, fix *) ->
    Zlength msg1 = Zlength msg2 ->
    Zlength (Zlist_to_intlist (msg1 ++ pad)) =
    Zlength (Zlist_to_intlist (msg2 ++ pad)).
Proof.
  intros msg1 msg2 pad Hi1 Hi2 Hlen.
  generalize dependent msg2.
  induction Hi1.
    intros msg2 Hi2 Hlen. induction Hi2.              (* hmm, may have messed up double ind *)
      reflexivity.
      simpl. unfold Zlength. simpl. admit. (* contradiction *)
    intros msg2 Hi2 Hlen. induction Hi2.
      simpl. unfold Zlength. simpl. admit. (* contra *)
      simpl.
      unfold Zlength. simpl. unfold Zlength in IHHi2. simpl in IHHi2. 
      
      
      

  
Admitted.

SearchAbout Zlength.
Print Zlength_aux.

(* TODO: would this lemma be easier if I rewrote generate and pad? 
probably not

gap' = 
  Zlist_to_intlist
  (msg ++ [128] ++ list_repeat (...) 0 ++ [lengthb1, lengthb2])

 *)
Theorem length_equal_pad_length : forall (msg1 : list Z) (msg2 : list Z),
     Zlength msg1  = Zlength msg2 ->
     Zlength (generate_and_pad msg1) = Zlength (generate_and_pad msg2).
Proof.
  intros m1 m2 H.
  unfold generate_and_pad.
  (* But Zlist_to_intlist is in the way :( *)
  rewrite -> H.
  
Abort.  
  
(* ------ *)

(* Lemma 1 *)
(* maybe prefix is easier... *)
(* but message is *not* a prefix of the padded list, since it's Z list?
or, ok, intlist msg = Prefix (generate_and_pad msg)?
 *)

Inductive Prefix {X : Type} : list X -> list X -> Prop :=
  | p_nil : forall (l : list X), Prefix [] l
  | p_self : forall (l : list X), Prefix l l
  | p_cons : forall (l1 l2 : list X) (x : X), Prefix l1 l2 -> Prefix (x :: l1) (x :: l2)
  | p_append : forall (l1 l2 : list X) (l3 : list X), Prefix l1 l2 -> Prefix l1 (l2 ++ l3)
  | p_trans : forall (l1 l2 l3 : list X), Prefix l1 l2 -> Prefix l2 l3 -> Prefix l1 l2.
                               (* might want to prove some of these... too powerful *)
                     (* TODO *)

(* computational... (++) is not a constructor *)

Inductive Msg {X : Type} : Type :=
| Empty : Msg
| Word : X -> X -> X -> X -> Msg -> Msg.
(* not [Msg X -> Msg X]? *)


(* is this less efficient than list Z? nah *)

(* this is true for all msgs of type 4-block message, but not in general,
 since Zlist_to_intlist throws away trailing chunkc % 4 *)

(* TODO: define a 4-block message? *)
Theorem Zlist_to_intlist_dist : forall (l1 l2 : list Z),
     InWords l1
         -> Zlist_to_intlist (l1 ++ l2) = Zlist_to_intlist l1 ++ Zlist_to_intlist l2.
(* Prefix (Zlist_to_intlist l1) (Zlist_to_intlist l1 ++ l2) instead?? *)
Proof.
  intros l1 l2 Ewords.
  induction Ewords.
  (* words_nil *)
    reflexivity.
  (* words_word *)
    simpl.
    rewrite -> IHEwords.
    reflexivity.
Qed.

Lemma Zlist_to_intlist_prefix : forall (l1 l2 : list Z),
                                  InWords l1 ->
                                  Prefix (Zlist_to_intlist l1) (Zlist_to_intlist (l1 ++ l2)).
Proof.
  intros l1 l2 Ewords.
  induction Ewords.
  (* words_nil *)
    simpl. apply p_nil.
  (* words_word *)
    simpl. apply p_cons. apply IHEwords.
Qed.
  
(* TODO add case ltac *)
Theorem message_prefix_padded' : forall (msg : list Z),
              InWords msg -> Prefix (Zlist_to_intlist msg) (generate_and_pad msg).
Proof.
  intros msg Ewords.
  induction Ewords.             (* fix names *)
  (* words_nil *)
    simpl. apply p_nil.
  (* words_word *)
    unfold generate_and_pad.
    simpl.
    apply p_cons.
    apply p_append.
    apply Zlist_to_intlist_prefix.
    apply Ewords.
Qed.    

(* TODO rewrite with implication? *)
(* OK, the premise is flawed, because we never do Zlist_to_intlist msg.
so we don't need InWords msg technically. But then how can we prove prefix?
is this good enough?
 *)
Theorem message_prefix_padded : forall (msg : list Z),
                                  Prefix (Zlist_to_intlist msg) (generate_and_pad msg).
Proof.
  intro msg.
  unfold generate_and_pad.
  apply p_append.
  induction msg as [ | x xs].
  (* msg = [] *)
    apply p_nil.
  (* msg = x :: xs *)
    simpl.
    
Admitted.

(* TODO: separate generate_and_pad function to generate . pad *)

(*ROUND FUNCTION*)

(*hardcoding the constants, first 32 bits of the fractional parts of the cube roots of the first 64 prime numbers*)
Print Int.repr.
Print Int.int.

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

Eval compute in Int.repr 1116352408.

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

(* ---------- Lemma 2 *)

Eval compute in intlist_to_Zlist [Int.repr 256].
Eval compute in intlist_to_Zlist [Int.repr 512].
Eval compute in intlist_to_Zlist [Int.repr 1024].
Eval compute in intlist_to_Zlist [Int.repr 2048].
Eval compute in intlist_to_Zlist [Int.repr 4096].

Definition g_a_p msg := 
  let n := Zlength msg in
   Zlist_to_intlist (msg ++ [128%Z] (* 1 *)
                ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0) (* 00...0 *)
           ++ [Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)]. (* length? in bytes *)

Eval compute in length (g_a_p [1]). (* 16 32 bit ints * 32 = 512 bits = 2 blocks *)
Eval compute in map Int.unsigned (g_a_p [1]). (* 16 32 bit ints * 32 = 512 bits = 2 blocks *)

(* TODO types *)

Definition pad (msg : list Z) : list Z := 
  let n := Zlength msg in
  msg ++ [128%Z] 
      ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0
      ++ intlist_to_Zlist ([Int.repr (n * 8 / Int.modulus), Int.repr (n * 8)]).

Definition g_a_p' (msg : list Z) : list int :=
  Zlist_to_intlist (pad msg).

Transparent Int.repr Int.or Int.shl Int.and.

SearchAbout app.                (* app_assoc, app_assoc_reverse *)

Lemma app_left : forall (a b c d : list Z),
   a ++ b ++ c ++ d = (a ++ b ++ c) ++ d.
Proof.
   intros a b c d.
   (* rewrite -> app_assoc.  do later*)
Admitted.

Definition fulllen (len : Z) :=
  len + 1%Z + (- (len + 9) mod 64). (* = -8 mod 64 = 56 mod 64??? not quite *)

Eval compute in fulllen 10.     (* + 8 = 64 *)
Eval compute in fulllen 1.
Eval compute in fulllen 0.
Eval compute in fulllen 100.    (* + 8 = 128 *)
Eval compute in fulllen 200.    (* + 8 = 256 *)
(* SHA-256 = block size 256 bits = 32 bit words (256 bits / (8 bits / byte) = 32 bytes?*)
(* Zlist to intlist: each Z is a byte; 4 bytes = 32 bit integer *)
Eval compute in 

Theorem gap_compose_equal : forall (msg : list Z),
                              g_a_p' msg = generate_and_pad msg.
Proof.
  intros msg.
  unfold g_a_p'. unfold pad.
  unfold generate_and_pad.
  (* simpl. *) (* TODO doesn't work *)
  pose proof pad_inwords as pad_inwords.
  specialize (pad_inwords msg).
  remember (msg ++
                [128] ++
                list_repeat (Z.to_nat (- (Zlength msg + 9) mod 64)) 0) as pad_nolen.
  rewrite -> app_left.
  rewrite <- Heqpad_nolen.
  induction pad_inwords.
    (* case none *)
    (* simpl. *)                (* ? *)
    inversion Heqpad_nolen.     (* ? *)


(* x : list int

InWords (a ++ b ++ ... ++ c) ->

Zlist_to_intlist (a ++ b ++ ... ++ c ++ intlist_to_Zlist x)
= Zlist_to_intilst (a ++ b ++ ... ++ c) ++ x *)
(* see pad_inwords *)

Admitted.

Eval compute in g_a_p' [1].
Check g_a_p'.

Theorem prefix : forall (msg : list Z),
                   Prefix msg (pad msg).
Proof.
  intros msg.
  unfold pad.
  apply p_append.
  apply p_self.
Qed.  

  (* --------- Lemma 2 ^ *)

Definition SHA_256 (str : list Z) : list Z :=
    intlist_to_Zlist (hash_blocks init_registers (generate_and_pad str)).
