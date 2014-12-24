Require Import Coqlib.
Require Import Integers.
Require Import List. Import ListNotations.
Require Import sha.pure_lemmas.

Lemma skipn_add {A}: forall t n (ch:list A),
      skipn (t+n) ch = skipn n (skipn t ch).
Proof.
  induction t; simpl. trivial.
  intros. destruct ch. 
    rewrite skipn_nil; trivial. 
  rewrite IHt; trivial.
Qed.

Lemma firstn_app1 {A}: forall n (l t:list A),
   (n >= length l)%nat -> firstn n (l++t) = l ++ firstn (n-length l) t.
Proof. intros n; induction n; simpl; intros.
  destruct l; simpl in *; trivial. omega.
  destruct l; simpl in *. trivial. rewrite IHn. trivial. omega.
Qed.

Lemma firstn_nil {A}: forall m, firstn m (nil:list A) = (nil:list A).
Proof. intros. rewrite firstn_same. trivial. simpl. omega. Qed.

Lemma skipn_all {A}: forall l, skipn (length l) l = (nil:list A).
Proof. intros l.
  induction l; simpl; trivial.
Qed.
Lemma skipn_all' {A}: forall n l, (n>=length l)%nat -> skipn n l = (nil:list A).
Proof. intros n.
  induction n; simpl; trivial. intros. destruct l; simpl in *; trivial. omega. 
  intros. destruct l; simpl in *; trivial. apply IHn. omega.
Qed.

Lemma firstn_list_repeat1 {A} k n (x:A) (N: (n>=k)%nat):
      firstn n (list_repeat k x) = list_repeat k x.
Proof.
  intros. specialize (firstn_app1 n (list_repeat k x) nil).
  rewrite app_nil_r. intros. rewrite H. 
   rewrite firstn_nil. apply app_nil_r.
  rewrite length_list_repeat. apply N. 
Qed.

Lemma firstn_list_repeat2 {A}: forall k n (x:A) (N: (n<=k)%nat),
      firstn n (list_repeat k x) = list_repeat n x.
Proof.
  intros k.
  induction k. simpl. intros. destruct n; simpl. trivial. omega.
  simpl; intros. destruct n; simpl in *.  trivial.
  rewrite IHk. trivial. omega. 
Qed.

Lemma firstn_geq {A}: forall k (l:list A),
    (k>=length l)%nat ->  firstn k l = l.
Proof. 
  induction k; simpl; intros. destruct l; trivial. simpl in *; omega.
destruct l. trivial. f_equal. apply IHk. simpl in *; omega.
Qed.

Lemma rev_list_repeat {A} (a:A): forall n, rev (list_repeat n a) = list_repeat n a.
Proof. induction n; simpl; trivial. rewrite IHn; clear IHn.
specialize (list_repeat_app A); intros Q.
rewrite (Q n (1%nat)).
specialize (Q (1%nat) n). rewrite plus_comm in Q. simpl in Q. rewrite Q; trivial.
Qed.  

Lemma zadd_zero_nonneg p q: 0 = p + q -> 0 <=p -> q>= 0 -> p=0 /\ q=0.
Proof. omega. Qed.

Lemma list_nil_length {A} (l:list A): l= [] -> (length l <= 0)%nat.
Proof. intros. subst. trivial. Qed.

