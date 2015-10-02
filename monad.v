Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section StateMonadDefs.

Implicit Types (A B C : Type).

Variable D : Type.

Record store A : Type := Store {data : A; hidden : D}.

Definition state A :=  D -> store A.

Definition sreturn {A} (a : A) : state A := fun c => Store a c.

Definition sbind {A B} (sa : state A) (f : A -> state B) : state B :=
  fun x => let: Store a c := sa x in f a c.

(* A convenient notation for programming, borrowed to Cyril :) *)
Notation "'sdo' x <- y ; z" :=
  (sbind y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' 'sdo'  x  <-  y ;  '/' z ']'").

(* The three laws of the monad. *)
Lemma sbind_return A B (a : A) (f : A -> state B) :
  (sdo x <- (sreturn a); f x) = f a.
Proof. by []. Qed.

Lemma sreturn_bind A (sa : state A) : (sdo x <- sa; sreturn x) =1 sa.
Proof. by move=> c; rewrite /sbind; case: (sa c). Qed.

Lemma sbind_comp A B C (f : A -> state B) (g : B -> state C) (sa : state A) :
(sdo b <- (sdo a <- sa; f a); g b) =1 (sdo a <- sa; sdo b <- (f a); g b).
Proof. by move=> c; rewrite /sbind; case: (sa c). Qed.

(* Pointwise equalities *)
Lemma sbind_extl {A B} {s1 s2 : state A} {f : A -> state B} :
  s1 =1 s2 -> (sdo x <- s1; f x) =1 (sdo x <- s2; f x).
Proof. move=> eqs c; by rewrite /sbind eqs. Qed.

Lemma sbind_extr {A B} {s : state A} {f1 f2 : A -> state B} :
  (forall a, f1 a =1 f2 a) -> (sdo x <- s; f1 x) =1 (sdo x <- s; f2 x).
Proof. by move=> ef c; rewrite /sbind; case: s => *; rewrite ef. Qed.

Lemma sbind_eqr {A B} {s : state A} {f1 f2 : A -> state B} c (s1 := s c) :
  f1 (data s1)  (hidden s1) = f2 (data s1) (hidden s1) ->
  (sdo x <- s; f1 x) c = (sdo x <- s; f2 x) c.
Proof. by rewrite /sbind {}/s1; case: (s c)=> d1 c1 /=. Qed.

Lemma sbind_eql {A B} {s1 s2 : state A} {f : A -> state B} c :
  s1 c = s2 c -> (sdo x <- s1; f x) c = (sdo x <- s2; f x) c.
Proof. by rewrite /sbind => ->. Qed.

(* spipe f l c "maps" f on l, threading the value of c along the way. *)
Fixpoint spipe {A B} (f : A -> state B) (l : seq A) : state (seq B) :=
  if l is a :: l then
    sdo s1 <- f a;
    sdo l1 <- spipe f l;
    sreturn (s1 :: l1)
 else sreturn [::].

Lemma spipe_nil A B (f : A -> state B) : spipe f [::] = sreturn [::]. by []. Qed.

Lemma spipe_cons A B (f : A -> state B) (l : seq A) (a : A) :
  spipe f (a :: l) = sdo s1 <- f a; sdo l1 <- spipe f l; sreturn (s1 :: l1).
Proof. by []. Qed.

Lemma spipe_cat {A B} (f : A -> state B) l1 l2 :
 spipe f (l1 ++ l2) =1 sdo l1 <- spipe f l1; sdo l2 <- spipe f l2;
                      sreturn (l1 ++ l2).
Proof.
elim: l1 l2 => [| s l1 ihl1] l2 //= c1.
  by rewrite sbind_return sreturn_bind.
rewrite sbind_comp; apply: sbind_extr => b c2.
rewrite (sbind_extl (ihl1 l2)) !sbind_comp; apply: sbind_extr => lb1 c.
by rewrite sbind_return sbind_comp.
Qed.

Lemma spipe_rcons {A B} (f : A -> state B) l a :
 spipe f (rcons l a) =1
 sdo l1 <- spipe f l; sdo s1 <- f a; sreturn (rcons l1 s1).
Proof.
move=> c1; rewrite -cats1 spipe_cat; apply: sbind_extr => lb /= c2.
by rewrite sbind_comp; apply: sbind_extr=> b c3; rewrite sbind_return -cats1.
Qed.

Lemma hidden_spipe_nil {A B} (f : A -> state B) c : hidden (spipe f [::] c) = c.
Proof. by []. Qed.

Lemma data_spipe_nil {A B} (f : A -> state B) c : data (spipe f [::] c) = [::].
Proof. by []. Qed.

Lemma hidden_spipe_cons  {A B} (f : A -> state B) s l c :
  hidden (spipe f (s :: l) c) = hidden (spipe f l (hidden (f s c))).
Proof.
by rewrite /sbind /= /sbind; case: (f s c) => d1 c1 /=; case: (spipe f l c1).
Qed.

Lemma data_spipe_cons  {A B} (f : A -> state B) s l c :
  data (spipe f (s :: l) c) = data (f s c) :: data (spipe f l (hidden (f s c))).
Proof.
by rewrite /sbind /= /sbind; case: (f s c) => d1 c1 /=; case: (spipe f l c1).
Qed.

Lemma hidden_spipe_cat {A B} (f : A -> state B) l1 l2 c :
  hidden (spipe f (l1 ++ l2) c) = hidden (spipe f l2 (hidden (spipe f l1 c))).
Proof.
elim: l1 l2 c => [| s l1 ihl1 l2 c] //; rewrite cat_cons [LHS]hidden_spipe_cons.
by rewrite ihl1 hidden_spipe_cons.
Qed.


Lemma data_spipe_cat {A B} (f : A -> state B) l1 l2 c :
  data (spipe f (l1 ++ l2) c) =
  data (spipe f l1 c) ++ data (spipe f l2 (hidden (spipe f l1 c))).
Proof.
elim: l1 l2 c => [| s l1 ihl1 l2 c] //; rewrite cat_cons [LHS]data_spipe_cons.
by rewrite ihl1 data_spipe_cons hidden_spipe_cons.
Qed.

Lemma hidden_spipe_rcons {A B} (f : A -> state B) s l c :
  hidden (spipe f (rcons l s) c) = hidden (f s (hidden (spipe f l c))).
Proof. by rewrite -cats1 hidden_spipe_cat hidden_spipe_cons. Qed.

Lemma data_spipe_rcons {A B} (f : A -> state B) s l c :
  data (spipe f (rcons l s) c) =
  rcons (data (spipe f l c)) (data (f s (hidden (spipe f l c)))).
Proof. by rewrite -cats1 data_spipe_cat data_spipe_cons /= cats1. Qed.

End StateMonadDefs.

Notation "'sdo' x <- y ; z" :=
  (sbind y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' 'sdo'  x  <-  y ;  '/' z ']'").
