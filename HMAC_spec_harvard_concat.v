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

    induction splitandpad_equiv.

    +
      (* [pad bytes] = [] *)
      (* byte side *)
      assert (conv_empty: SHA256.Zlist_to_intlist [] = []). reflexivity.
      rewrite -> conv_empty.
      rewrite -> SHA256.hash_blocks_equation.

      (* bit side *)
      rewrite -> hash_blocks_bits_equation.
      unfold sha_iv.
      (* note: i'm definining sha_iv according to what is needed here *)

      apply bytes_bits_def_eq.
      
    +
(* won't be able to relate directly, since it's a hash function *)
(*   *)
      


Admitted

.

(*
TODO: list Blist instead of Blist? Types don't work here
Maybe I should rewrite SHA to operate on list Blist

Lemma SHA_equiv_nopad : forall (bits_list : list Blist) (bytes : list Z),
                    (* assumptions *)
                    bytes_bits_lists' bits_list bytes ->
                    bytes_bits_lists'
                      (* note that bits_list is:
                         [thing of block size] :: [thing padded to be of block size] *)
                      (hash_words sha_h sha_iv bits_list)
                      (SHA256_.Hash bytes).

Proof.


Admitted.
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

    (* rewrite -> app_nil_r. *)

    Check SHA_equiv_pad.
    apply SHA_equiv_pad.
    
    (* assert (splitandpad_nil: sha_splitandpad [] = []). admit. (* TODO *) *)
    (* rewrite -> splitandpad_nil. *)
    (* simpl. (* this makes hash_words go away -- why? *) *)

    apply concat_equiv.
    apply xor_equiv_Z; try assumption.
    * apply SHA_equiv_pad.
      apply concat_equiv.
      - apply xor_equiv_Z; try assumption.
      (* bytes_bits_lists (sha_splitandpad m) M -- TODO  *)
      (* - apply splitandpad_equiv. *)
      - admit.
        * admit.
        * admit.
Qed.


(* induction doesn't work *)
Theorem HMAC_spec_equiv_ind : forall
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

  induction msgs_eq.

  -
    (* code repeated between cases here *)
    unfold HMAC. unfold HMAC_SHA256.HMAC. unfold HMAC_SHA256.OUTER. unfold HMAC_SHA256.INNER.
    
    unfold HMAC_2K. unfold GHMAC_2K. rewrite -> split_append_id.

    unfold HMAC_SHA256.outerArg. unfold HMAC_SHA256.innerArg. (* unfold HMAC_SHA256.mkArg. *)
    
    simpl.

    rewrite -> app_nil_r.

    Check SHA_equiv_pad.
    apply SHA_equiv_pad.
    
    assert (splitandpad_nil: sha_splitandpad [] = []). admit. (* TODO *)
    rewrite -> splitandpad_nil.
    (* simpl. (* this makes hash_words go away -- why? *) *)

    apply concat_equiv.
    apply xor_equiv_Z; try assumption.
    * apply SHA_equiv_pad.
      rewrite -> app_nil_r.
      apply xor_equiv_Z; try assumption.
    * admit.
    * admit.

    (* Eval compute in HMAC_SHA256.HMAC 54 92 []. *)

  -
    unfold HMAC.
    unfold HMAC_SHA256.HMAC.

    unfold HMAC_SHA256.INNER.
    unfold HMAC_SHA256.innerArg.
    (* unfold HMAC_SHA256.mkArgZ. *)
    (* Print HMAC_SHA256.mkArg. *)
    (* unfold HMAC_SHA256.mkArg. *)

    unfold HMAC_SHA256.OUTER.
    unfold HMAC_SHA256.outerArg.
    (* unfold HMAC_SHA256.mkArgZ. *)
    (* unfold HMAC_SHA256.mkArg. *)

    unfold HMAC_2K.
    unfold GHMAC_2K.
    Print split_append_id.
    rewrite -> split_append_id.

    
Abort.


(* HMAC IP OP M K =
    H ( K (+) OP      ++
        H ((K (+) IP) ++ M)
      ) 
*)
    

    (* Use these when working on SHA and generate_and_pad *)
    (*
    unfold HMAC_SHA256.OUTER in *.
    unfold SHA256_.Hash in *.
    rewrite -> functional_prog.SHA_256'_eq in *.

    unfold SHA256.SHA_256 in *.
    repeat rewrite <- sha_padding_lemmas.pad_compose_equal in *.
    unfold sha_padding_lemmas.generate_and_pad' in *.
     *)

