Set Implicit Arguments.


Require Import Bvector.
Require Import List.
Require Import Arith.
Require Import HMAC_spec_list.
Require Import HMAC_common_defs.

Module HMAC_Abstract.

Definition Blist := list bool.

Fixpoint splitVector (A : Set) (n m : nat) :
  Vector.t A (n + m) -> (Vector.t A n * Vector.t A m) :=
  match n with
    | 0 => 
      fun (v : Vector.t A (O + m)) => (@Vector.nil A, v)
    | S n' => 
      fun (v : Vector.t A (S n' + m)) => 
        let (v1, v2) := splitVector _ _ (Vector.tl v) in
          (Vector.cons _ (Vector.hd v) _ v1, v2)
  end.

Section HMAC.

  (* c is the output size, b is the block size (larger than the output size),
     and p is the difference between them *)
  Variable c p : nat.
  Definition b := c + p.
  
  (* The compression function *)
  Variable h : Bvector c -> Bvector b -> Bvector c.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Bvector c.
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star (k : Bvector c) (m : list (Bvector b)) : Bvector c :=
    fold_left h m k.

  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words : list (Bvector b) -> Bvector c :=
    h_star iv.

  Variable splitAndPad : Blist -> list (Bvector b).
  Hypothesis splitAndPad_1_1 : 
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.
  
  Variable fpad : Bvector c -> Bvector p. 
  Definition app_fpad (x : Bvector c) : Bvector b :=
    (Vector.append x (fpad x)).

  Definition h_star_pad (k : Bvector c) (x : list (Bvector b)) : Bvector b :=
    app_fpad (h_star k x).

  Definition GNMAC (k : Bvector (c + c)) (m : list (Bvector b)) : Bvector c :=
    let (k_Out, k_In) := splitVector c c k in
    h k_Out (app_fpad (h_star k_In m)).

  (* The "two-key" version of GHMAC and HMAC. *)
  Definition GHMAC_2K (k : Bvector (b + b)) (m : list (Bvector b)) : Bvector c :=
    let (k_Out, k_In) := splitVector b b k in
      let h_in := (hash_words (k_In :: m)) in 
        hash_words (k_Out :: (app_fpad h_in) :: nil).
  
  Definition HMAC_2K (k : Bvector (b + b)) (m : Blist) : Bvector c :=
    GHMAC_2K k (splitAndPad m).

  (* opad and ipad are constants defined in the HMAC spec. *)
  Variable opad ipad : Bvector b.
  Hypothesis opad_ne_ipad : opad <> ipad.

  Definition GHMAC (k : Bvector b) : list (Bvector b) -> Bvector c :=
    GHMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

  Definition HMAC (k : Bvector b) : Blist -> Bvector c :=
    HMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

End HMAC.

End HMAC_Abstract.

Theorem xor_eq : forall (n : nat) (v1 v2 : Bvector n) (l1 l2 : Blist),
                   l1 = Vector.to_list v1 ->
                   l2 = Vector.to_list v2 ->
                   BLxor l1 l2 = Vector.to_list (BVxor n v1 v2).
Proof.
  intros n v1 v2 l1 l2 vl1_eq vl2_eq.
  rewrite vl1_eq. rewrite vl2_eq.
  unfold BLxor.
  unfold BVxor.
  SearchAbout Vector.map2.

  induction n as [ | n'].
  *
    SearchAbout Vector.t 0.
    assert (v1 = Bnil). admit.
    assert (v2 = Bnil). admit.
    subst.
    simpl.
    reflexivity.
  *
    admit.                      (* not sure *)
Qed.

SearchAbout Vector.append.

Theorem app_eq : forall (n : nat) (v1 v2 : Bvector n) (l1 l2 : Blist),
                   l1 = Vector.to_list v1 ->
                   l2 = Vector.to_list v2 ->
                   l1 ++ l2 = Vector.to_list (Vector.append v1 v2).
Proof.
  intros n v1 v2 l1 l2 vl1_eq vl2_eq.
  subst.
  unfold Vector.append.

Admitted.
Check HMAC_Abstract.splitVector.

Theorem split_eq : forall (n m : nat) (v : Bvector (n + m)) (l : Blist),
                     l = Vector.to_list v ->
                     fst (splitList n l) =
                     Vector.to_list (fst (HMAC_Abstract.splitVector n m v))
                     /\
                     snd (splitList n l) =
                     Vector.to_list (snd (HMAC_Abstract.splitVector n m v)).
Proof.
  intros n m v l vl_eq.
  split.
  * 
    unfold splitList.
    unfold HMAC_Abstract.splitVector.
    simpl.

Admitted.

(* TODO: will prove that the list equivalents have this type *)
Parameter h_v : Bvector c -> Bvector b -> Bvector c.
Parameter iv_v : Bvector c.
Parameter splitAndPad_v : Blist -> list (Bvector b).
Parameter fpad_v : Bvector c -> Bvector p. 
Parameter opad_v ipad_v : Bvector b.

(* TODO: prove fpad has right type *)
Lemma fpad_eq : forall (v : Bvector c) (l : Blist),
                  l = Vector.to_list v ->
                  fpad l = Vector.to_list (fpad_v v).
Proof.
  intros v l inputs_eq.
Admitted.  

Lemma app_fpad_eq : forall (v : Bvector c) (l : Blist),
                      l = Vector.to_list v ->
                      HMAC_List.app_fpad fpad l =
                      Vector.to_list (HMAC_Abstract.app_fpad fpad_v v).
Proof.
  intros v l inputs_eq.
  subst.
  unfold HMAC_List.app_fpad. unfold HMAC_Abstract.app_fpad.
  apply app_eq.
  *  reflexivity.
  *  apply fpad_eq.
     reflexivity.
Qed.     

(* iv *)
Lemma iv_eq : sha_iv = Vector.to_list iv_v.
Proof. Admitted.

(* h *)
Lemma h_eq : forall (block_v : Bvector b) (block_l : Blist),
               block_l = Vector.to_list block_v ->
               sha_h sha_iv block_l = Vector.to_list (h_v iv_v block_v).
Proof.
  intros block_v block_l blocks_eq.
  pose proof iv_eq as iv_eq.
  subst.
  rewrite -> iv_eq.
  
Admitted.

Check HMAC_Abstract.h_star.

(* also h_star *)
Lemma hash_words_eq : forall (v : list (Bvector b)) (l : list Blist),
                      (* l = Vector.to_list v -> *)
                      HMAC_List.hash_words sha_h sha_iv l =
                      Vector.to_list (HMAC_Abstract.hash_words p h_v iv_v v).
Proof.
  intros v l. (* inputs_eq.*)
  unfold HMAC_List.hash_words. unfold HMAC_Abstract.hash_words.
  unfold HMAC_List.h_star. unfold HMAC_Abstract.h_star.
  generalize dependent v.
  induction l as [ | bl bls].
  *
    admit.
  *
    intros v. generalize dependent bl.
    generalize dependent bls. induction v as [| bv bvs].
    -
      intros.
      simpl.
      admit.
    - intros.
      simpl.
      (* apply IHbls. *)
      (* TODO order of params? *)
      (* TODO each element of v and l are equal, and the lists themselves are the same length *)
      (* TODO should be able to use h_eq *)
      admit.
Qed.   

(* TODO: opad and ipad should be in HMAC_common_parameters (factor out of all spec) *)
Theorem HMAC_eq : forall (kv : Bvector b) (kl m op ip : Blist),
                    kl = Vector.to_list kv ->
                    HMAC_List.HMAC c p sha_h sha_iv sha_splitandpad_blocks fpad op ip kl m
                    = Vector.to_list
                        (HMAC_Abstract.HMAC h_v iv_v splitAndPad_v
                                            fpad_v opad_v ipad_v kv m).
Proof.
  intros kv kl m op ip keys_eq.
  unfold HMAC_List.HMAC. unfold HMAC_Abstract.HMAC.
  unfold HMAC_List.HMAC_2K. unfold HMAC_Abstract.HMAC_2K.
  unfold HMAC_List.GHMAC_2K. unfold HMAC_Abstract.GHMAC_2K.
  rewrite -> split_append_id.
  Check split_append_id.
  assert (forall (n : nat) (v1 v2 : Bvector n),
            HMAC_Abstract.splitVector n n (Vector.append v1 v2) = (v1, v2))
         as v_split_append_id.
    admit.                      (* TODO *)
  rewrite -> v_split_append_id.

  apply hash_words_eq.          (* TODO why does it freeze here *)
  
  * admit.                      (* xor preserves lengths -- ok *)
  * admit.

Qed.  

(* Can't directly prove equality here, just equivalence via length preservation.

-----

1. 
Prove the following functions are equivalent when Vector is converted to List:

Rewritten functions:
Vector.append ~ ++
BVxor ~ BLxor
splitVector ~ splitList

TODO: May need to admit the equivalence of these three functions.
Need more lemmas that relate vectors and lists.

Functions changed mostly just in type:
h_star <-- correct if h is
hash_words <-- correct if h_star is
app_fpad <-- correct if ++ and fpad are 
h_star_pad (not used in HMAC)
GNMAC (not used in HMAC)
GHMAC (not used in HMAC)
GHMAC_2K <-- correct if splitList, app_fpad, and hash_words are 
HMAC_2K <-- correct if GHMAC_2K and splitAndPad are 
HMAC <-- correct if HMAC_2K, BLxor, and ++ are 

TODO: does this compose correctly if the three functions above are admitted?

Primitives: BLxor, ++, splitList, splitAndPad, h, app_fpad (and the constants)

Let f_l ~. f_v := 
    l ~ v -> f_l l ~ f_v v
(function equivalence given input equivalence)
where l ~ v :=
      l = Vector.to_list v.

2. Prove that the given parameters (e.g. fpad) have the right type. Correctness isn't needed; there's no vector specification to check the list version against.

> For all parameters, prove that given an input of the right size, they will give an output of the right size. Then, prove that the initial input is of the right size. 

constants: c, p, iv, opad, ipad
functions: h, splitAndPad, fpad

-----

This should be informally equal to HMAC_Abstract, though I don't think there is a formal way to do and check module equivalence in Coq. *)





