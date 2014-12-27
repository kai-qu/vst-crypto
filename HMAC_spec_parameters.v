  (* c is the output size, b is the block size 
     (larger than the output size),
     and p is the difference between them *)
  Variable c p : nat.
  Definition b := c + p.
  
  (* compression function *)
  Variable h : Bvector c -> Bvector b -> Bvector c.

  (* initialization vector *)
  Variable iv : Bvector c.

  Variable splitAndPad : Blist -> list (Bvector b).
  
  Variable fpad : Bvector c -> Bvector p. 
  Definition app_fpad (x : Bvector c) : Bvector b :=
    (Vector.append x (fpad x)).

  Variable opad ipad : Bvector b.

  (* ----- Definitions *)

  (* The iteration of the compression function gives a keyed hash function on lists of words. *)
  Definition h_star k (m : list (Bvector b)) :=
    fold_left h m k.

  (* The composition of the keyed hash function with the IV gives a hash function on lists of words. *)
  Definition hash_words := h_star iv.

  (* ----- Instantiation *)

  Definition c := (SHA256_.DigestLength * 8)%nat.
  Definition p := (32 * 8)%nat.

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

