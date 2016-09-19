From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* This should ultimately go to the MathComp library... *)

Lemma count_mem_rcons {T : eqType} (t : T) (w : seq T) (a : T) :
  count_mem t (rcons w a) =
  if (a == t) then (count_mem t w).+1 else count_mem t w.
Proof.
by rewrite -cats1 count_cat /=; case: ifP=> _; rewrite ?addn0 ?addn1.
Qed.

Lemma drop_add {T : Type} (d : T) (w : seq T) (n1 n2 : nat) :
   drop (n1 + n2) w = drop n1 (drop n2 w).
Proof.
elim: n1 n2 w => [| n1 ihn1] //= n2 w; first by rewrite add0n drop0.
rewrite addSn -addnS ihn1 -(addn1 n1) ihn1.
case: (ltnP n2 (size w)) => hn2; first by rewrite (drop_nth d hn2) /= drop0.
by rewrite ![drop _ w]drop_oversize //=; apply: leq_trans hn2 _.
Qed.


Section ExtraScanPairmapFoldl.

Variables (T1 : Type) (x1 : T1) (T2 : Type) (x2 : T2).
Variables (f : T1 -> T1 -> T2) (g : T1 -> T2 -> T1).

Lemma last_scanl s : last x1 (scanl g x1 s) = foldl g x1 s.
Proof.
case: s => [| a s] //=.
rewrite (last_nth (g x1 a)) size_scanl -/(scanl g x1 (a :: s)) nth_scanl //.
by rewrite -[_.+1]/(size (a :: s)) take_size.
Qed.

Lemma scanl_rcons s t :
  scanl g x1 (rcons s t) = rcons (scanl g x1 s) (foldl g x1 (rcons s t)).
Proof. by rewrite -cats1 scanl_cat /= foldl_cat cats1. Qed.

Lemma foldl_rcons s t :
  foldl g x1 (rcons s t) = g (foldl g x1 s) t.
Proof. by rewrite -cats1 foldl_cat. Qed.

Lemma take_scanl n s : take n (scanl g x1 s) = scanl g x1 (take n s).
Proof.
rewrite -[in LHS](cat_take_drop n s) scanl_cat; case: (ltnP n (size s))=> hssn.
  rewrite takel_cat; last by rewrite size_scanl size_take hssn.
  by rewrite take_oversize // size_scanl size_take hssn.
by rewrite take_cat size_scanl size_take !ltnNge !hssn drop_oversize //= cats0.
Qed.

Lemma take_pairmap n s : take n (pairmap f x1 s) = pairmap f x1 (take n s).
Proof.
rewrite -[in LHS](cat_take_drop n s) pairmap_cat; case: (ltnP n (size s))=> hssn.
  rewrite takel_cat; last by rewrite size_pairmap size_take hssn.
  by rewrite take_oversize // size_pairmap size_take hssn.
by rewrite take_cat size_pairmap size_take !ltnNge !hssn drop_oversize //= cats0.
Qed.

Lemma take_take n m (s : seq T1) : take n (take m s) = take (minn n m) s.
Proof.
rewrite /minn; case: ltnP=> [ltnm | lemn]; last first.
  by rewrite take_oversize // size_take; case: ltnP=> // /leq_trans; apply.
rewrite -[in RHS](cat_take_drop m s) take_cat size_take.
case: (ltnP m _) => // lessm; rewrite ?ltnm //; case: ltnP => // leqssn.
rewrite [LHS]take_oversize; first by rewrite drop_oversize ?cats0.
by rewrite size_take? ltnNge lessm.
Qed.

Lemma pairmap_rcons s y :
  pairmap f x1 (rcons s y) = rcons (pairmap f x1 s) (f (last x1 s) y).
Proof. by rewrite -cats1 pairmap_cat /= cats1. Qed.

Lemma rev_pairmap y z :
  rev (pairmap f x1 (rcons z y)) =
  pairmap (fun x y => f y x) y (rcons (rev z) x1).
Proof.
elim/last_ind: z y => [| z c ihz] //= y.
by rewrite pairmap_rcons rev_rcons last_rcons rev_rcons rcons_cons /= ihz.
Qed.


End ExtraScanPairmapFoldl.
