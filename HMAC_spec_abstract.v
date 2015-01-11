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



(* Can't directly prove equality here, just equivalence via length preservation.

-----

1. 
Prove the following functions are equivalent when Vector is converted to List:

Rewritten functions:
Vector.append ~ ++
BVxor ~ BLxor
splitVector ~ splitList

TODO: May need to admit the equivalence of these three functions.

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

2. Prove that the given parameters (e.g. fpad) have the right type as stated below above in TYPE. Correctness isn't needed; that will be done later.

> For all parameters, prove that given an input of the right size, they will give an output of the right size. Then, prove that the initial input is of the right size. 

constants: c, p, iv, opad, ipad
functions: h, splitAndPad, fpad

-----

This should be informally equal to HMAC_Abstract, though I don't think there is a formal way to do and check module equivalence in Coq. *)





