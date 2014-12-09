Set Implicit Arguments.


Require Import Bvector.
Require Import List.
Require Import Arith.

Require Import Coq.Program.Basics.
Local Open Scope program_scope.

Definition Blist := list bool.

Fixpoint splitVector(A : Set)(n m : nat) : Vector.t A (n + m) -> (Vector.t A n * Vector.t A m) :=
  match n with
    | 0 => 
      fun (v : Vector.t A (O + m)) => (@Vector.nil A, v)
    | S n' => 
      fun (v : Vector.t A (S n' + m)) => 
        let (v1, v2) := splitVector _ _ (Vector.tl v) in
          (Vector.cons _ (Vector.hd v) _ v1, v2)
  end.

Section HMAC.

  Variable c p : nat.
  Definition b := c + p.
  
  (* The compression function *)
  Variable h : Bvector c -> Bvector b -> Bvector c.
  (* The initialization vector is part of the spec of the hash function. *)
  Variable iv : Bvector c.
  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : list (Bvector b)) :=
    fold_left h m k.
  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.


  Variable splitAndPad : Blist -> list (Bvector b).
  Hypothesis splitAndPad_1_1 : 
    forall b1 b2,
      splitAndPad b1 = splitAndPad b2 ->
      b1 = b2.

  Definition hash_words_padded := hash_words ∘ splitAndPad.
  
  (* Variable fpad : Bvector c -> Bvector p. *)
  (* Definition app_fpad (x : Bvector c) : Bvector b := *)
  (*   (Vector.append x (fpad x)). *)
  Variable pad_output_to_blocksize : Bvector c -> Bvector b.

  (* This doesn't seem to be used *)
  (* Definition h_star_pad k x := *)
  (*   app_fpad (h_star k x). *)

  (* : Vector.t bool (c + c) -> list (Bvector b) -> Bvector c *)
  (* Theoretically SHA's splitAndPad would work here, since it would pad it to a list of 
     exactly one block (since c < b), and then you could take the head of the list. 
     But splitAndPad is left abstract here.

     Not quite sure what to do with GNMAC. It doesn't show up in my proof.
 *)
  Definition GNMAC k m :=
    let (k_Out, k_In) := splitVector c c k in
    h k_Out (pad_output_to_blocksize (h_star k_In m)).

  (* The "two-key" version of GHMAC and HMAC. *)
  Definition GHMAC_2K (k : Bvector (b + b)) m :=
    let (k_Out, k_In) := splitVector b b k in
      let h_in := (hash_words_padded (Vector.to_list k_In ++ m)) in 
        hash_words_padded (Vector.to_list k_Out ++ Vector.to_list h_in).
  
  Definition HMAC_2K (k : Bvector (b + b)) (m : Blist) :=
    GHMAC_2K k m.

  (* opad and ipad are constants defined in the HMAC spec. *)
  Variable opad ipad : Bvector b.
  Hypothesis opad_ne_ipad : opad <> ipad.

  Definition GHMAC (k : Bvector b) :=
    GHMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

  Definition HMAC (k : Bvector b) :=
    HMAC_2K (Vector.append (BVxor _ k opad) (BVxor _ k ipad)).

End HMAC.