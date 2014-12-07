(* Admitted/admitted lemmas:

39 - 12 = 27?
 *)

Set Implicit Arguments.

(* Require Import Bvector. *)
Require Import List.
Require Import Arith.

Require Import HMAC_functional_prog_Z.
Require Import Integers.
Require Import Coqlib.
Require Import sha_padding_lemmas.
Require Import functional_prog.
Require Import hmac_common_lemmas.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Strings.String.

Require Import List. Import ListNotations.

Definition Blist := list bool.

Definition compose {A B C : Type} (f : B -> C) (g : A -> B) (x : A) := f (g x).
Notation "f @ g" := (compose f g) (at level 80, right associativity).

Definition splitList {A : Type} (h : nat) (t : nat) (l : list A) : (list A * list A) :=
  (firstn h l, skipn t l).

Definition concat {A : Type} (l : list (list A)) : list A :=
  flat_map id l.


(* TODO: length proofs (length xs = length ys) *)
Definition BLxor (xs : Blist) (ys : Blist) :=
  map (fun p => xorb (fst p) (snd p)) (combine xs ys).

Print fold_left.
(*
Function hash_blocks (r: registers) (msg: list int) {measure length msg} : registers :=
  match msg with
  | nil => r
  | _ => hash_blocks (hash_block r (firstn 16 msg)) (skipn 16 msg)
  end.
Proof. intros.
 destruct (lt_dec (length msg) 16).
 rewrite skipn_length_short. simpl; omega. rewrite <- teq; auto.
 rewrite skipn_length. simpl; omega. rewrite <- teq; omega.
Defined.
*)
(* block size 512, possibly use take 512 l instead, though it might be harder to prove things about *)
Function hash_blocks_bits (hash_block_bit : Blist -> Blist -> Blist) (r: Blist)
         (msg: Blist) {measure length msg} : Blist :=
  match msg with
  | nil => r
  | _ => hash_blocks_bits hash_block_bit (hash_block_bit r (firstn 512 msg)) (skipn 512 msg)
  end.
Proof. intros.
(*
 destruct (lt_dec (length msg) 512).
 rewrite skipn_length_short. simpl; omega. rewrite <- teq; auto.
 rewrite skipn_length. simpl; omega. rewrite <- teq; omega. *)
Admitted.
(* Defined. *)
(* TODO *)
                                                                                    

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
  Print fold_left.
  Locate fold_left.
  
  Definition h_star k (m : Blist) :=
    hash_blocks_bits h k m.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  (* Check hash_words. *)
  Check h_star.

  (* NOTE: this is the new design without fpad TODO *)
  (* NOTE: this is the new design with concat and with two hash_words_padded *)
  (* Variable splitAndPad : Blist -> list (Blist). *)
  Variable splitAndPad : Blist -> Blist.

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
    let (k_Out, k_In) := splitList c c k in
    h k_Out (h_star_pad k_In m). (* could take head of list *)

  Check GNMAC.
  (*  list bool -> list Blist -> Blist *)
  Check h.
  (* Blist -> Blist -> Blist *)

Check hash_words.               (* list Blist -> Blist *)

  (* The "two-key" version of GHMAC and HMAC. *)
  (* Concatenate (K xor opad) and (K xor ipad) *)
  Definition GHMAC_2K (k : Blist) m :=
    let (k_Out, k_In) := splitList b b k in (* concat earlier, then split *)
      let h_in := (hash_words_padded (k_In ++ m)) in
        hash_words_padded (k_Out ++ h_in).

  Definition HMAC_2K (k : Blist) (m : Blist) :=
    (* GHMAC_2K k (splitAndPad m). *)
    GHMAC_2K k m.

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

(* ----------------------------------- DEFINITIONS *)

Module Equiv.

  (* ----- Inductive *)

Definition asZ (x : bool) : Z := if x then 1 else 0.

Definition convertByteBits (bits : Blist) (byte : Z) : Prop :=
  exists (b0 b1 b2 b3 b4 b5 b6 b7 : bool),
   bits = [b0; b1; b2; b3; b4; b5; b6; b7] /\
   byte =  (1 * (asZ b0) + 2 * (asZ b1) + 4 * (asZ b2) + 8 * (asZ b3)
         + 16 * (asZ b4) + 32 * (asZ b5) + 64 * (asZ b6) + 128 * (asZ b7)).

Inductive bytes_bits_lists : Blist -> list Z -> Prop :=
  | eq_empty : bytes_bits_lists nil nil
  | eq_cons : forall (bits : Blist) (bytes : list Z)
                     (b0 b1 b2 b3 b4 b5 b6 b7 : bool) (byte : Z),
                bytes_bits_lists bits bytes ->
                convertByteBits [b0; b1; b2; b3; b4; b5; b6; b7] byte ->
                bytes_bits_lists (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bits)
                                 (byte :: bytes).

Definition byte_to_64list (byte : byte) : list Z :=
   map Byte.unsigned (HMAC_SHA256.sixtyfour byte).

Definition Z_to_64list (num : Z) : list Z :=
   HMAC_SHA256.sixtyfour num.

(* ----- Computational *)

(* byte = Z (not byte type), bit = bool *)
(* endianness: TODO *)

(* bytes to bits *)

(* TODO: assumes Z is positive and in range, does not use Z.positive 
-- does this make the following proofs false? *)

Definition div_mod (num : Z) (denom : Z) : bool * Z :=
  (Z.gtb (num / denom) 0, num mod denom).

Eval compute in div_mod 129 128.
Eval compute in div_mod 1 64.

Definition byteToBits (byte : Z) : Blist :=
  let (b7, rem7) := div_mod byte 128 in
  let (b6, rem6) := div_mod rem7 64 in
  let (b5, rem5) := div_mod rem6 32 in
  let (b4, rem4) := div_mod rem5 16 in
  let (b3, rem3) := div_mod rem4 8 in
  let (b2, rem2) := div_mod rem3 4 in
  let (b1, rem1) := div_mod rem2 2 in
  let (b0, rem0) := div_mod rem1 1 in
  [b0; b1; b2; b3; b4; b5; b6; b7].

Fixpoint bytesToBits (bytes : list Z) : Blist :=
  match bytes with
    | [] => []
    | byte :: xs => byteToBits byte ++ bytesToBits xs
  end.

Definition bitsToByte (bits : Blist) : Z :=
  match bits with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: nil =>
      1 * (asZ b0) + 2 * (asZ b1) + 4 * (asZ b2) + 8 * (asZ b3)
      + 16 * (asZ b4) + 32 * (asZ b5) + 64 * (asZ b6) + 128 * (asZ b7)
    | _ => -1                   (* should not happen *)
  end.

Fixpoint bitsToBytes (bits : Blist) : list Z :=
  match bits with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: xs =>
      let byte := 1 * (asZ b0) + 2 * (asZ b1) + 4 * (asZ b2) + 8 * (asZ b3)
         + 16 * (asZ b4) + 32 * (asZ b5) + 64 * (asZ b6) + 128 * (asZ b7) in
      byte :: bitsToBytes xs
    | _ => []
  end.

Require Import Coq.Strings.Ascii.
Open Scope string_scope.

Definition asStr (x : bool) : string := if x then "1" else "0".

Definition toStr (bits : Blist) : list string :=
  map asStr bits.

Eval compute in toStr (bytesToBits [8]).
Eval compute in toStr (bytesToBits [127]).
Eval compute in toStr (bytesToBits [128]).
Eval compute in toStr (bytesToBits [255]).

(* id for one composition *)

Lemma byte_bit_byte_ex : forall (x : Z), x = 68 -> bitsToByte (byteToBits x) = x.
Proof. intros. rewrite H. simpl. reflexivity. Qed.

(* can prove by testing all bytes in range... *)
Theorem byte_bit_byte_id : forall (byte : Z),
                             0 <= byte < 256 ->
                                bitsToByte (byteToBits byte) = byte.
Proof.
  intros byte range.
  destruct range as [lower upper].
  unfold byteToBits.
  unfold bitsToByte.
  (* Opaque asZ. *)
  (* Opaque div_mod. *)
  
  (* destruct b0. *)

  (* destruct (byteToBits byte) as *)
  (*     [ | x0 [ | x1 [ | x2 [ | x3 [ | x4 [ | x5 [ | x6 [ | x7 xs] ] ]  ]  ] ] ] ]. *)
  (* admit. admit. admit. admit. admit. admit. admit. admit. (* TODO *) *)

  (* unfold bitsToByte. *)

(* need that byte = ... *)

  (* destruct x0. destruct x1. destruct x2. destruct x3. *)
  (* destruct x4. destruct x5. destruct x6. destruct x7. *)
  


  (* list needs to be of right length *)
  (* unfold bitsToByte. *)
  
Admitted.

Theorem bytes_bits_bytes_id : forall (bytes : list Z),
                                bitsToBytes (bytesToBits bytes) = bytes.
Proof.
  intros bytes.
  induction bytes as [ | byte bytes].
  - reflexivity.
  - unfold bytesToBits.
    unfold bitsToBytes.

Admitted.

(* could also do proof by enumeration *)
Lemma bit_byte_bit_ex : forall (b0 b1 b2 b3 b4 b5 b6 b7 : bool) (x : Blist),
                          x = [true; true; true; false; true; true; true; true]
                          -> byteToBits (bitsToByte x) = x.
Proof. intros. rewrite H. simpl. reflexivity. Qed.

(* conditional id for other composition *)
Theorem bytes_bits_bytes_id_len : forall (bits : Blist),
                                (length bits mod 8)%nat = 0%nat ->
                                bytesToBits (bitsToBytes bits) = bits.
Proof.
  intros bytes.
  unfold bytesToBits.
  unfold bitsToBytes.

Admitted.

(* try proving equivalance on sample function (e.g. byte addition) *)

(* unary *)
Definition byte_neg (bytes : list Z) : list Z :=
  map (fun byte => -1 * byte) bytes.

Definition wrap (f : list Z -> list Z) : Blist -> Blist :=
  bytesToBits @ f @ bitsToBytes.

Definition bit_neg : Blist -> Blist :=
  wrap byte_neg.

Lemma test_neg : forall (bits : Blist) (bytes : list Z),
                   bits = [true; true; true; true; true; true; true; true] ->
                   bytes = [127] -> (* relation *)
                   bits = bytesToBits bytes ->
                   bit_neg bits = bytesToBits (byte_neg bytes). (* relation *)
Proof.
  intros bits bytes bits_eq bytes_eq input_eq.
  unfold bit_neg. unfold wrap.
  replace ((bytesToBits @ byte_neg @ bitsToBytes) bits) with
  (bytesToBits (byte_neg (bitsToBytes bits))).

  rewrite bits_eq. rewrite bytes_eq.
  simpl.
  reflexivity.

  admit.
Qed.  
  

(* binary TODO *)
(* Definition bit_add (x : Blist) (y : Blist) := *)
  

Close Scope string_scope.

(* ------- *)

(* Lemma range_proof : forall (x : Z) (lower : Z) (upper : Z), *)
(*                       lower <= upper -> *)
(*                       lower <= x <= upper -> *)
(*                       ... *)
                      
(* TODO: range_proof above, or prove for all things in range *)
(* need that all bytes are in range *)
Theorem bytes_bits_def_eq : forall (bytes : list Z),
                              bytes_bits_lists (bytesToBits bytes) bytes.
Proof.
  intros bytes.
  induction bytes as [ | byte bytes ].
  -
    simpl. apply eq_empty.
  -
    Print bytes_bits_lists.
    apply eq_cons.

    *
      apply IHbytes.
    *
      unfold convertByteBits.
      do 8 eexists.
      split.
      +
        reflexivity.
      + 
        assert (byte_range : 0 <= byte < 256). admit.
        assert (byte_val : byte = 200). admit.
        rewrite byte_val.
        simpl.
        reflexivity.
Qed.      
      

(* not sure which to use / which is true *)
(* TODO *)
Theorem bytes_bits_imp_ok : forall (bits : Blist) (bytes : list Z),
                           bytes_bits_lists bits bytes -> bits = bytesToBits bytes.
Proof.
  intros.
  induction H.
  +
    reflexivity.

  +
    unfold bytesToBits.
    


Admitted.

Theorem bytes_bits_imp_ok' : forall (bits : Blist) (bytes : list Z),
                           bits = bytesToBits bytes -> bytes_bits_lists bits bytes.
Proof.
    


Admitted.

Theorem bytes_bits_imp_other : forall (bits : Blist) (bytes : list Z),
                           bytes_bits_lists bits bytes -> bytes = bitsToBytes bits.
Proof.

Admitted.

(* ----------------------------------------------- *)

Check HMAC.

(* HMAC
     : nat ->
       nat ->
       (Blist -> Blist -> Blist) ->
       Blist ->
       (Blist -> list Blist) -> Blist -> Blist -> Blist -> Blist -> Blist *)

(*
Parameter sha_iv : Bvector (SHA256_.DigestLength * 8).
Parameter sha_h : Bvector c -> Bvector (c + p) -> Bvector c.
Parameter sha_splitandpad_vector :
  Blist -> list (Bvector (SHA256_.DigestLength * 8 + p)).

(* Parameter fpad : Bvector p. *)
*)

Definition c:nat := (SHA256_.DigestLength * 8)%nat.
Definition p:=(32 * 8)%nat.

Definition sha_iv : Blist :=
  bytesToBits (SHA256.intlist_to_Zlist SHA256.init_registers).

Check SHA256.hash_blocks.       (* SHA256.registers -> list int -> SHA256.registers *)
Definition sha_h (regs : Blist) (block : Blist) : Blist :=
  bytesToBits (SHA256.intlist_to_Zlist
                 (SHA256.hash_block (SHA256.Zlist_to_intlist (bitsToBytes regs))
                                     (SHA256.Zlist_to_intlist (bitsToBytes block))
              )).

(* Parameter sha_splitandpad : Blist -> Blist. *)
Definition sha_splitandpad (msg : Blist) : Blist :=
  bytesToBits (sha_padding_lemmas.pad (bitsToBytes msg)).

(* -------------------------------------------------------- LEMMAS *)

(* Lemma 1: ++ equivalence on list *)
(* Lemma 2: xor equivalence on list *)
(* Lemma 3: SHA (iterated hash) equivalence on list *)

Lemma concat_equiv :
  forall (l1 : Blist) (l2 : list Z) (m1 : Blist) (m2 : list Z),
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

(* --------------------------------- *)

SearchAbout length.
Check splitList.
Eval compute in splitList 0%nat 0%nat [].

Lemma split_append_id : forall {A : Type} (len : nat) (l1 l2 : list A),
                               length l1 = len -> length l2 = len ->
                               splitList len len (l1 ++ l2) = (l1, l2).
Proof.
  induction len; intros h1 h2 l1 l2.
  -
    assert (H: forall {A : Type} (l : list A), length l = 0%nat -> l = []). admit.
    apply H in l1. apply H in l2.
    subst. reflexivity.
  -
    admit.                      (* TODO *)
      
    

Admitted.

(* ------- *)

(* Lemma 2 *)

(* Prove that the inner xor lemma is true on at least one example *)
Section Example. 

 Definition k:Blist := concat (list_repeat 64 [true; true; false; false; true; false; true; true]).
 Definition K:list Z := list_repeat 64 211. 

 Lemma conv : convertByteBits [true; true; false; false; true; false; true; true] 211.
   repeat eexists.
  (* eexists; eexists; eexists; eexists; eexists; eexists; eexists; eexists. *)
  (* split. reflexivity. simpl. reflexivity. *)
 Qed.
 Lemma kKcorrect: bytes_bits_lists k K.
   unfold K, k. simpl.
   repeat constructor; try apply conv.
  Qed. 


 Definition ip:Blist := concat (list_repeat 64 [false; true; false; false; true; false; true; true]).
 Definition IP:Z := 210.
 Transparent Byte.repr. 

 Lemma ip_conv : convertByteBits [false; true; false; false; true; false; true; true] 210.
   repeat eexists.
 Qed.
 Lemma ipcorrect: bytes_bits_lists ip (HMAC_SHA256.sixtyfour IP).
   unfold ip, IP. simpl. unfold byte_to_64list, HMAC_SHA256.sixtyfour. simpl.
   repeat constructor; try apply ip_conv.
  Qed. 

Lemma ONE: convertByteBits [true; false; false; false; false; false; false; false] 1.
  repeat eexists. Qed.

Lemma inner_fst_equiv_example : exists k (ip  : Blist) K (IP : Z), 
                          ((length K) * 8)%nat = (c + p)%nat /\
                          Zlength K = Z.of_nat SHA256_.BlockSize /\
                          (* TODO: first implies this *)
                          bytes_bits_lists k K /\
                          bytes_bits_lists ip (HMAC_SHA256.sixtyfour IP) /\
                          bytes_bits_lists (BLxor k ip) 
                                           ((HMAC_SHA256.mkArg (HMAC_SHA256.mkKey K) IP)).

Proof.
  exists k, ip, K, IP. repeat split.
   apply kKcorrect. apply ipcorrect. 
  unfold k, K, ip, IP. simpl. unfold BLxor. simpl.
  repeat constructor; apply ONE.
Qed.

(* TODO: stuck here *)
Lemma xor_correspondence :
  forall (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : bool)
         (byte0 byte1 : Z),
    convertByteBits [b0; b1; b2; b3; b4; b5; b6; b7] byte0 ->
    convertByteBits [b8; b9; b10; b11; b12; b13; b14; b15] byte1 ->

    convertByteBits
      [xorb b0 b8; xorb b1 b9; xorb b2 b10; xorb b3 b11; 
       xorb b4 b12; xorb b5 b13; xorb b6 b14; xorb b7 b15]
      (Z.lxor byte0 byte1).
Proof.
  intros.
  generalize dependent H. generalize dependent H0. intros H0 H1.
  unfold convertByteBits. unfold asZ.

  do 8 eexists. split. reflexivity.
  unfold convertByteBits in *.

  destruct H0 as [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ]] ]] ].  (* nested 8 *)
  destruct H.
  symmetry in H.
  inversion H. clear H.
  subst.

  destruct H1 as [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ]] ]] ].  (* nested 8 *)
  destruct H.
  symmetry in H.
  inversion H. clear H.
  subst.

  unfold asZ.

  (* destruct b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15; reflexivity. *)
  (* TODO *)
  
  (* simpl. *)
  Print Z.lxor. Print Pos.lxor.
  SearchAbout Z.lxor.
  (* need to exhibit b16 ... b23 *)
   

Admitted.  


Lemma inner_general_map : forall (ip : Blist) (IP_list : list Z) (k : Blist) (K : list Z),
                            bytes_bits_lists ip IP_list ->
                            bytes_bits_lists k K ->
     bytes_bits_lists (BLxor k ip) 
                      (map (fun p0 : Z * Z => Z.lxor (fst p0) (snd p0))
                           (combine K IP_list)).
Proof.
  intros ip IP_list k K ip_eq k_eq.
  unfold BLxor. simpl.
  generalize dependent ip. generalize dependent IP_list.
  induction k_eq; intros.
  - simpl. constructor.
  - (* unfold byte_to_64list in ip_eq. simpl in ip_eq. *)
    (* map Byte.unsigned
           (map ((x,y) -> f x y)
            (combine (map Byte.repr xs) (map Byte.repr ys)))
     *)
    (* Eval compute in HMAC_SHA256.sixtyfour []. *)
    induction ip_eq.
    + 
      simpl. constructor.
    +
      simpl.
      constructor.
      * apply IHk_eq.
        apply ip_eq.            (* ??? *)
      *
        apply xor_correspondence.
        apply H. apply H0.
Qed.
(*
H : convertByteBits [b0; b1; b2; b3; b4; b5; b6; b7] byte 
H0 : convertByteBits [b8; b9; b10; b11; b12; b13; b14; b15] byte0

 convertByteBits
     [xorb b0 b8; xorb b1 b9; xorb b2 b10; xorb b3 b11; 
     xorb b4 b12; xorb b5 b13; xorb b6 b14; xorb b7 b15]
     (Byte.Z_mod_modulus
        (Z.lxor (Byte.Z_mod_modulus byte) (Byte.Z_mod_modulus byte0)))

*)

(*
Lemma inner_fst_equiv_ipbyte : exists (ip  : Blist) (IP : byte), 
                          bytes_bits_lists ip (byte_to_64list IP) /\
                      forall (k : Blist) (K : list Z),
                          ((length K) * 8)%nat = (c + p)%nat ->
                          Zlength K = Z.of_nat SHA256_.BlockSize ->
                          (* TODO: first implies this *)
                          bytes_bits_lists k K ->
                          bytes_bits_lists (BLxor k ip) (map Byte.unsigned
       (HMAC_SHA256.mkArg (map Byte.repr (HMAC_SHA256.mkKey K)) IP)) .
Proof.
  exists ip, IP. repeat split.
  apply ipcorrect.
  intros. 
  unfold HMAC_SHA256.mkArg, HMAC_SHA256.mkArgZ, HMAC_SHA256.mkKey.
   simpl. rewrite H0. simpl. unfold HMAC_SHA256.zeroPad.
   assert (KL: length K0 = 64%nat). admit.
   rewrite KL.  simpl.  rewrite app_nil_r.
   unfold HMAC_SHA256.sixtyfour.
   (* unfold HMAC_SHA256.Nlist. *)

   (* apply inner_general_map.      *)

Print HMAC_SHA256.mkArg.
   
Admitted.
*)

Lemma xor_equiv_Z : forall (xpad  : Blist) (XPAD : Z)
                                           (k : Blist) (K : list Z),
                          bytes_bits_lists xpad (HMAC_SHA256.sixtyfour XPAD) ->
                          ((length K) * 8)%nat = (c + p)%nat ->
                          Zlength K = Z.of_nat SHA256_.BlockSize ->
                          (* TODO: first implies this *)
                          bytes_bits_lists k K ->
                          bytes_bits_lists (BLxor k xpad)
       (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey K) XPAD).
Proof.
  (* intros xpad XPAD k K. intros xpad_equiv len_k zlen_k k_equiv.   *)
  (* apply xpadcorrect. *)
  (* Check xpadcorrect. *)
  intros.
  unfold HMAC_SHA256.mkArg, HMAC_SHA256.mkKey.
  Opaque HMAC_SHA256.sixtyfour.
   simpl. rewrite H1. simpl. unfold HMAC_SHA256.zeroPad.
   assert (KL: length K0 = 64%nat). admit.
   rewrite KL.  simpl.  rewrite app_nil_r.
   apply inner_general_map.

   - apply H.
   - apply H2.
Qed.


Eval compute in Byte.xor (Byte.repr 0) (Byte.repr 100).
Eval compute in Byte.xor (Byte.repr 100) (Byte.repr 100).
Eval compute in Byte.xor (Byte.repr 50) (Byte.repr 5).

End Example.

(* ------------------------------------------------------ *)
(* Lemma 3 *)

Check sha_h.                    (* Blist -> Blist -> Blist *)
(* registers -> block -> registers *)
(* see Round and rnd_function in SHA256 *)
Check sha_iv.
Print sha_padding_lemmas.generate_and_pad'.
Check sha_padding_lemmas.pad.

(* TODO: 11/16/14 

- figure out Rnd/Round
- define sha_h
   - figure out how to work with hash_blocks_terminate
- define sha_splitandpad
- figure out how to unfold the proofs involving SHA & which lemma to start with
- figure out how they would compose
   - e.g. if you admit one of the lemmas, how would you use it in the main proof?
 *)

Lemma splitandpad_equiv : forall (bits : Blist) (bytes : list Z),
                            bytes_bits_lists bits bytes ->
                            bytes_bits_lists
                              (sha_splitandpad bits)
                              (sha_padding_lemmas.pad bytes).
Proof.
  intros bits bytes inputs_eq.
  unfold concat.
  unfold sha_splitandpad.

  apply bytes_bits_imp_ok in inputs_eq.
  rewrite inputs_eq.
  rewrite bytes_bits_bytes_id.
  apply bytes_bits_def_eq.
Qed.

(* induct in block sizes? (512 bits, 64 bytes respectively): 
fold equivalence:
given any iv, equivalent inputs -> one round of hashing -> equivalent outputs

sha_h sha_iv (firstn 512 bits)
 = 
bytesToBits
           (SHA256.intlist_to_Zlist
              (SHA256.hash_block
                 (SHA256.Zlist_to_intlist (bitsToBytes sha_iv))
                 (SHA256.Zlist_to_intlist
                    (bitsToBytes
                       (firstn 512
                          bits)))))

want: ~

SHA256.hash_block SHA256.init_registers
                 (firstn 16 (SHA256.Zlist_to_intlist bytes)) 
*)

Lemma hash_block_equiv :
  forall (bits : Blist) (bytes : list Z)
         (regs : Blist) (REGS : SHA256.registers),
                     (* can't induct
(not true for registers of any length), use computational instead *)
                     (* relation for int -> Z? *)
    (length bits)%nat = 512%nat ->
    (length bytes)%nat = 64%nat -> (* removes firstn 16 (Zlist->intlist bytes) *)

    regs = bytesToBits (SHA256.intlist_to_Zlist REGS) ->
    bits = bytesToBits bytes ->

    sha_h regs bits =
    bytesToBits (SHA256.intlist_to_Zlist
                   (SHA256.hash_block REGS
                                      (SHA256.Zlist_to_intlist bytes))).
Proof.
  intros bits bytes regs REGS bits_blocksize bytes_blocksize regs_eq input_eq.
  unfold sha_h.
  apply f_equal.
  apply f_equal.
  
  rewrite -> regs_eq.
  rewrite -> input_eq.
  rewrite -> bytes_bits_bytes_id.
  rewrite -> bytes_bits_bytes_id.
  rewrite -> pure_lemmas.intlist_to_Zlist_to_intlist.
  reflexivity.
(* TODO: need to apply fold_equiv below with inducting on block size *)
(* TODO: make sure this proof is right / useful *)
Qed.

Check fold_left.
Print fold_left.
Check sha_h.
Check SHA256.hash_blocks.
Check sha_iv.
Check SHA256.hash_blocks. Print SHA256.registers.

Lemma length_not_emp :
  forall {A B : Type} (l : list A) (z y : B),
    (Datatypes.length l > 0)%nat -> match l with [] => z | _ => y end = y.
    (* exists (x : A) (xs : list A), l = x :: xs. *)
Proof.
  intros.
  induction l as [ | x xs].
  - inversion H.
  - reflexivity.
Qed.    

Parameter A B : Type.
Parameter convert_BA : B -> A.
Parameter convert_AB : A -> B.

Fixpoint iterate {A : Type} (n : nat) (f : A -> A) (x : A) :=
  match n with
    | O => x
    | S n' => f (iterate n' f x) (* or [iterate n' f (f x)] *)
  end.

Definition id {X : A} (x : A) : A := x.

Lemma once_eq :
    forall (x : A) (X : B) (f : A -> A) (F : B -> B),
      x = convert_BA X ->
      (* (convert_BA @ convert_AB) = id -> *)
      f = (convert_BA @ F @ convert_AB) ->
      f x = convert_BA (F X).
Proof.
  intros x X f F inputs_eq f_def.
  rewrite -> inputs_eq.
  rewrite -> f_def.
  replace ((convert_BA @ F @ convert_AB) (convert_BA X)) with
     (convert_BA (F (convert_AB (convert_BA X)))).
  replace (convert_AB (convert_BA X)) with (X).
  reflexivity.
  -                             (* Id proof *)
    admit.
  -                             (* composition *)
    admit.
Qed.

(* a simplified version of fold_equiv *)
Lemma iterate_equiv :
  forall (x : A) (X : B) (f : A -> A) (F : B -> B) (n : nat),
  x = convert_BA X ->
  iterate n f x = convert_BA (iterate n F X).
Proof.
  intros. revert x X f F H.
  induction n as [ | n']; intros x X f F input_eq.
  - 
    simpl. apply input_eq.
  - 
    simpl.
    pose proof once_eq as once_eq.
    apply once_eq.
    apply IHn'.
    apply input_eq.
    *                           (* f is wrapped (here, f is sha_h?) *)
      admit.
Qed.    

Inductive InBlocks {A : Type} (n : nat) : list A -> Prop :=
  | list_nil : InBlocks n []
  | list_block : forall (front back full : list A),
                   length front = n ->
                   full = front ++ back ->
                   InBlocks n back ->
                   InBlocks n full. (* not easy to do inversion on *)

Lemma test : InBlocks 512 (list_repeat 512 true).
Proof.
  eapply list_block.
  instantiate (1 := list_repeat 512 true).
  - reflexivity.
  - instantiate (1 := []). admit.
  - apply list_nil.
Qed.  

Lemma test2 : forall (l : Blist) (L : list int),
                InBlocks 512 l ->
                InBlocks 16 L ->
                InBlocks 512 (bytesToBits (SHA256.intlist_to_Zlist L) ++ l).
Proof.
  intros l L bit_blocks byte_blocks.
  revert L byte_blocks.
  induction bit_blocks; intros.
  -
    induction byte_blocks.
    * simpl. apply list_nil.
    * eapply list_block.
      + instantiate (1 := bytesToBits (SHA256.intlist_to_Zlist back)).
        admit.                  (* 16 * 4 * 8 = 512 *)
      + instantiate (1 := []). 
        admit.
Admitted.        
      
      
            

(* it's more of an iteration theorem than a fold theorem *)
Lemma fold_equiv_blocks :
  forall (l : Blist) (acc : Blist)
         (L : list int) (ACC : list int),
    (* length assumptions about list *)
    (* conversion function: bytesToBits @ SHA256.intlist_to_Zlist *)
      InBlocks 512 l ->         (* TODO: need to prove padding implies this *)
      InBlocks 16 L ->
      l = bytesToBits (SHA256.intlist_to_Zlist L) ->
      acc = bytesToBits (SHA256.intlist_to_Zlist ACC) ->
      hash_blocks_bits sha_h acc l = bytesToBits (SHA256.intlist_to_Zlist
                                                    (SHA256.hash_blocks ACC L)).
Proof.
  intros l acc L ACC bit_blocks bytes_blocks inputs_eq acc_eq.

  pose (convert := (bytesToBits @ SHA256.intlist_to_Zlist)).
  assert (conv_replace:
            forall (x : list int), bytesToBits (SHA256.intlist_to_Zlist x) = convert x).
  admit.

  rewrite -> conv_replace in *.
  
  revert acc ACC L inputs_eq acc_eq bytes_blocks conv_replace.
 (* pose proof hash_block_equiv as hash_block_equiv. *)
  
  induction bit_blocks; intros.
  * 
    revert acc ACC inputs_eq acc_eq.
    induction bytes_blocks; intros.

    -                             (* both empty *)
      rewrite -> SHA256.hash_blocks_equation.
      rewrite -> hash_blocks_bits_equation.
      apply acc_eq.

    -
      rewrite -> H0 in *.
      inversion inputs_eq.
      (* impossible, TODO: front is not empty, so intlist_to_Zlist (m ++ l) is not empty *)
      admit.

  *

    Print InBlocks.
    (* revert front back full H H0 bit_blocks convert IHbit_blocks acc ACC L *)
    (*        inputs_eq acc_eq bytes_blocks conv_replace. *)
    revert front back full H H0 bit_blocks convert IHbit_blocks acc ACC
           inputs_eq acc_eq conv_replace.
    (* TODO *)
    induction bytes_blocks; intros.

    -
      simpl in inputs_eq.
      rewrite -> H0 in inputs_eq.
      (* again, impossible: is not empty *)
      admit.
    -
      rewrite -> SHA256.hash_blocks_equation.
      rewrite -> hash_blocks_bits_equation.
      repeat rewrite -> length_not_emp. (* induction step, use H and H1 *)

      pose proof hash_block_equiv as hash_block_equiv.
      specialize (hash_block_equiv (firstn 512 full0)
                                   (SHA256.intlist_to_Zlist (firstn 16 full))
                                   acc ACC).
      rewrite -> hash_block_equiv; auto. clear hash_block_equiv.
      rewrite -> pure_lemmas.intlist_to_Zlist_to_intlist.
      rewrite -> conv_replace in *.

      remember (SHA256.hash_block ACC (firstn 16 full)) as inner_result.

      rewrite -> inputs_eq.

      (* this has a nice form. ----- *)
(*
      rewrite -> H2.
      rewrite -> H0.

      (* front = firstn, back = skipn *)
      specialize (IHbytes_blocks (firstn 512 full0) (skipn 512 full0) full0).
      
      apply IHbytes_blocks.

      specialize (IHbytes_blocks (skipn 512 full0)).
      replace convert with (bytesToBits @ SHA256.intlist_to_Zlist).
      apply IHbytes_blocks.
      

     (* how does double induction work? do you usually use both induction hypotheses? *)
      (* repeat rewrite <- conv_replace. *)
 *)  
  
Admitted.


(* it's more of an iteration theorem than a fold theorem *)
Lemma fold_equiv_limited :
  forall (l : Blist) (acc : Blist)
         (L : list int) (ACC : list int),
    (* length assumptions about list *)
    (* conversion function: bytesToBits @ SHA256.intlist_to_Zlist *)
      (16 | length L)%nat ->
      l = bytesToBits (SHA256.intlist_to_Zlist L) ->
      acc = bytesToBits (SHA256.intlist_to_Zlist ACC) ->
      hash_blocks_bits sha_h acc l = bytesToBits (SHA256.intlist_to_Zlist
                                                    (SHA256.hash_blocks ACC L)).
Proof.
  intros l acc L ACC byte_len inputs_eq acc_eq.

  pose proof hash_block_equiv as hash_block_equiv.
  
  destruct byte_len.
  
  revert l L acc ACC H acc_eq inputs_eq.
  induction x; intros.

  destruct L; inversion H.
  (* TODO *)
  (* simpl on compose later *)
  (* replace ((bytesToBits @ SHA256.intlist_to_Zlist) []) with *)
  (* (bytesToBits @ SHA256.intlist_to_Zlist) *)
  (* simpl in inputs_eq. *)
  -
    simpl in inputs_eq.
    rewrite -> inputs_eq.
    rewrite -> SHA256.hash_blocks_equation.
    rewrite -> hash_blocks_bits_equation.
    apply acc_eq.

  -
    (* H doesn't say where the length is added (front, back, every other element... *)
    (* need Datatypes.length l = (S x * 512)%nat *)
    rewrite -> SHA256.hash_blocks_equation.
    rewrite -> hash_blocks_bits_equation.
    (* there's an extra conversion to/from in hash_block_equiv *)
    repeat rewrite -> length_not_emp. (* induction step *)
    specialize (hash_block_equiv (firstn 512 l) (SHA256.intlist_to_Zlist (firstn 16 L))
                                 acc ACC).
    rewrite -> hash_block_equiv.
    rewrite -> pure_lemmas.intlist_to_Zlist_to_intlist.

    (* -------- *)

    rewrite -> SHA256.hash_blocks_equation.
    rewrite -> hash_blocks_bits_equation.
   (* here: they're equivalent for equiv block lengths (look at the respective []) (512, 16)
       and if there is another block, 
*)
    assert (H_skip_bit : forall {A : Type} (x y : A),
                       match skipn 512 l with | [] => x | _ => y end = y). admit.
    assert (H_skip_byte : forall {A : Type} (x y : A),
                       match skipn 16 L with | [] => x | _ => y end = y). admit.
    rewrite -> H_skip_bit. rewrite -> H_skip_byte.
    clear H_skip_bit H_skip_byte IHx hash_block_equiv. (* TODO *)

    * pose proof hash_block_equiv as hash_block_equiv.
      specialize (hash_block_equiv
                       (firstn 512 (skipn 512 l))
                        (SHA256.intlist_to_Zlist (firstn 16 (skipn 16 L)))
                        (bytesToBits
                           (SHA256.intlist_to_Zlist (SHA256.hash_block ACC (firstn 16 L))))
                        (SHA256.hash_block ACC (firstn 16 L))
                     
                 ).
      rewrite -> hash_block_equiv.
      rewrite -> pure_lemmas.intlist_to_Zlist_to_intlist.
      clear hash_block_equiv.
      (* same accumulated inner structure! *)
    
    (* unfold sha_h. *)
    (* maybe what I want is an equivalence between hash_blocks and hash_blocks_bits *)
    
    (*
   convert = bytesToBits @ SHA256.intlist_to_Zlist

   hash_blocks_bits sha_h (convert res) (skipn 512 (convert L)) 
      =
   convert ((SHA256.hash_blocks res) (skipn 16 L)) *)

    rewrite -> hash_blocks_bits_equation.
    

    (* firstn and skipn lemma *)
(* SearchAbout firstn. *)
  

(* prove by inducting in blocks *)
  

Admitted.
    
SearchAbout fold_left.

Lemma SHA_equiv_pad : forall (bits : Blist) (bytes : list Z),
(* do equivalent inputs really guarantee equivalent outputs?
this seems like an important central theorem.

is it true for +, +b?
do I have to prove 10 inner lemmas about various SHA ops?
will a wrapper function around SHA work?
is there a name for this type of function invariant under conversion? / mathematical theory?

now
  - ints are very different from Zs (see Z_to_int, Zlist_to_intlist)
  - what if the specs AREN'T equivalent? doing operations on packed ints may differ from
    doing them on bits
  - what if i write a bits to int conversion? (bits -> bytes (Z) -> int)
    - bits -> bytes = len % 8 = 0, bytes -> ints -> len % 4 = 0 --> len bits % 32 = 0
    - TODO: which is a *stronger* condition than we had
 *)
                        (* add assumptions here + intros them *)
                    bytes_bits_lists bits bytes ->
                    bytes_bits_lists
                      (hash_words_padded sha_h sha_iv sha_splitandpad bits)
                      (SHA256_.Hash bytes).

Proof.
  intros bits bytes input_eq.
  unfold SHA256_.Hash.
  rewrite -> functional_prog.SHA_256'_eq.
  unfold SHA256.SHA_256.
  unfold hash_words_padded.
  replace ((hash_words sha_h sha_iv @ sha_splitandpad) bits) with
  (hash_words sha_h sha_iv (sha_splitandpad bits)).
  -
    repeat rewrite <- sha_padding_lemmas.pad_compose_equal in *.
    unfold sha_padding_lemmas.generate_and_pad' in *.
    unfold hash_words.
    unfold h_star.

    Check SHA256.hash_blocks_equation.
    
    pose proof splitandpad_equiv as splitandpad_equiv.
    specialize (splitandpad_equiv bits bytes input_eq).

    (* induction splitandpad_equiv. (* <-- want to induct in block size here *) *)

    (* + *)
    (*   (* [pad bytes] = [] *) *)
    (*   (* byte side *) *)
    (*   assert (conv_empty: SHA256.Zlist_to_intlist [] = []). reflexivity. *)
    (*   rewrite -> conv_empty. *)
    (*   rewrite -> SHA256.hash_blocks_equation. *)

    (*   (* bit side *) *)
    (*   rewrite -> hash_blocks_bits_equation. *)
    (*   unfold sha_iv. *)
    (*   (* note: i'm defining sha_iv according to what is needed here *) *)

    (*   apply bytes_bits_def_eq. *)
      
    (* + *)
      (* rewrite -> SHA256.hash_blocks_equation. *)
      (* rewrite -> hash_blocks_bits_equation. *)
      apply bytes_bits_imp_ok'.
      pose proof fold_equiv_limited as fold_equiv_limited. (* delete later *)
      (* TODO: factor out the sha_h as lemma from statement; use hash_blocks_equiv in the proof *)
      apply fold_equiv_limited.
      * admit.
      * unfold sha_splitandpad. rewrite -> pure_lemmas.Zlist_to_intlist_to_Zlist.
        apply bytes_bits_imp_other in input_eq.
        rewrite -> input_eq.
        reflexivity.
        + admit.                        (* padding length lemma *)
        + Print SHA256.isbyteZ. Print Forall. (* TODO: show each byte is in range *)
          admit.

     * unfold sha_iv. reflexivity.

  - admit.                      (* TODO: compose lemma *)
Qed.    
          (* TODO is this right? *)

      Check SHA256.hash_blocks_equation.
      Check hash_blocks_bits_equation.
      (* unfold sha_h. *)

      
(* does the theorem above use splitandpad_equiv? yes *)
(* won't be able to relate directly, since it's a hash function *)
      (* see above theorem *)
(* TODO: need to figure out how to **induct** in block size
   (maybe without having x0 :: ... :: x511 on-screen)
if theorem above is correct,
and how to apply it here 

maybe define another inductive relation, inBlocks (like in sha_padding_lemmas)
and prove that it's inBlocks
*)


(* ---------- *)

Theorem HMAC_spec_equiv : forall
                            (K M H : list Z) (OP IP : Z)
                            (k m h : Blist) (op ip : Blist),
  ((length K) * 8)%nat = (c + p)%nat ->
  Zlength K = Z.of_nat SHA256_.BlockSize ->
(* TODO: first implies this *)
  (* TODO: might need more hypotheses about lengths *)
  bytes_bits_lists k K ->
  bytes_bits_lists m M ->
  bytes_bits_lists op (HMAC_SHA256.sixtyfour OP) ->
  bytes_bits_lists ip (HMAC_SHA256.sixtyfour IP) ->
  HMAC c p sha_h sha_iv sha_splitandpad op ip k m = h ->
  HMAC_SHA256.HMAC IP OP M K = H ->
  bytes_bits_lists h H.
Proof.
  intros K M H OP IP k m h op ip.
  intros padded_key_len padded_key_len_byte padded_keys_eq msgs_eq ops_eq ips_eq.
  intros HMAC_abstract HMAC_concrete.

  intros.
  unfold p, c in *.
  simpl in *.

  rewrite <- HMAC_abstract. rewrite <- HMAC_concrete.

    (* code repeated between cases here *)
    unfold HMAC. unfold HMAC_SHA256.HMAC. unfold HMAC_SHA256.OUTER. unfold HMAC_SHA256.INNER.
    
    unfold HMAC_2K. unfold GHMAC_2K. rewrite -> split_append_id.

    unfold HMAC_SHA256.outerArg. unfold HMAC_SHA256.innerArg. (* unfold HMAC_SHA256.mkArg. *)
    
    simpl.

    apply SHA_equiv_pad.
    
    apply concat_equiv.
    apply xor_equiv_Z; try assumption.
    *
      apply SHA_equiv_pad.
      apply concat_equiv.

      - apply xor_equiv_Z; try assumption.

      (* bytes_bits_lists (sha_splitandpad m) M -- TODO  *)
      (* 
this looks like an actual difference in the specs.
       see HMAC_2K (line 90) in HMAC_spec_harvard_v, or Theorem HMAC_unfold

       is this different from the HMAC paper spec itself?
       the message can be variable length

to make this work, you can either use ^, or use
hash_words_padded sha_h sha_iv sha_splitandpad
           (BLxor k ip ++ sha_splitandpad m)))
= 
hash_words_padded sha_h sha_iv sha_splitandpad
           (BLxor k ip ++ m)))

which isn't true due to the nature of the padding function (depends on length of input).

his spec will also have that problem with fpad (it'll need to be a specific fpad:
10..0[length], at that point should be baked into hash_words as hash_words_padded.


---

proposed solution: since i've already made many changes,
and sha_splitandpad is included in hash_words_padded, delete sha_splitandpad, completing the proof

      *)
      (* - apply splitandpad_equiv. *)
      - assumption.
        * admit.
        * admit.
Qed.