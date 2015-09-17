Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice tuple finfun fintype finset.
Require Import finfun bigop ssralg ssrnum poly ssrint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Type step is the three-letter alphabet of the words we want to count.
   The names of the letters reminds how they will be interpreted as
   (the direction of) small step moves on a grid.*)

Inductive step : Type := N | W | SE.

(* Type step has a canonical decidable comparison, is a countable, even finite
   type, thus equipped with a choice function. We obtain these properties, and
   the associated generic notations and theory by expliciting an isomorphism
   bewteen type step and the finite type 'I_3 of natural numbers {0,1,2}:
   - North (N) is coded by 0
   - West (W) is coded by 1
   - SouthEast (SW) is coded by 2
 *)

(* Installing  structures of equality, countable, choice,
   finite type on type step, plus a coercion from step to finite ordinals. We
   proceed by showing that ord_of_step : step -> 'I_3 has a left inverse, where
   I_3 is the enumerated type type with elements 0, 1, 2. Then some boilerplate
  code declares the appropriate canonical structures *)

Definition ord_of_step (s : step) : 'I_3 :=
  match s with
    |N => @Ordinal 3 0 (refl_equal true)
    |W => @Ordinal 3 1 (refl_equal true)
    |SE => @Ordinal 3 2 (refl_equal true)
  end.

Definition step_of_ord (o : 'I_3) : step :=
  match nat_of_ord o with
      |0 => N
      |1 => W
      |_ => SE
  end.

Lemma ord_of_stepK : cancel ord_of_step step_of_ord.
Proof. by case. Qed.

(* Starting boilerplate code *)

Definition step_eqMixin := CanEqMixin ord_of_stepK.
Canonical  step_eqType  := EqType step step_eqMixin.

Definition step_choiceMixin := CanChoiceMixin ord_of_stepK.
Canonical  step_choiceType  := ChoiceType step step_choiceMixin.


Definition step_countMixin := CanCountMixin ord_of_stepK.
Canonical  step_countType  := CountType step step_countMixin.

Definition step_finMixin   := CanFinMixin ord_of_stepK.
Canonical  step_finType    := FinType step step_finMixin.

(* End of boilerplate code *)

(* Boolean predicates characterizing each nature of step *)
Definition is_N := pred1 N.
Definition is_W := pred1 W.
Definition is_SE := pred1 SE.

(* Words are represented as sequences (lists) of letters *)
Definition count_N : seq step -> nat := count is_N.
Definition count_W : seq step -> nat := count is_W.
Definition count_SE : seq step -> nat := count is_SE.

(* (#N w) is the number of occurrences of N in word w, etc. *)

Notation "#N" := count_N.
Notation "#W" := count_W.
Notation "#SE" := count_SE.

Lemma count_steps_size (w : seq step) : (#N w) + (#W w) + (#SE w) = size w.
Proof.
elim: w => // [[]] l /= <-. rewrite !add0n.
- by rewrite -[RHS]add1n !addnA.
- by rewrite [_ + (1 + _)]addnCA -!addnA add1n.
- by rewrite [_ + (1 + _)]addnCA add1n.
Qed.

(* We consider a family A of words on alphabet step. A word w is in A iff:
   - for any prefix p of w, #SE p <= #N p
   - #N w = #SE w = #W w
   Intuitively (we do not verify this formally), words in A can be generated
   by taking:
   - a Dyck word d on (N, SE) of lenght 2*k;
   - with k letters W randomly inserted in d.
 *)

Definition preAword (w : seq step) : bool :=
  [forall n : 'I_(size w).+1, #SE (take n w) <= #N (take n w)].

Lemma preAwordP w :
  reflect (forall n : nat, #SE (take n w) <= #N (take n w)) (preAword w).
Proof.
apply: (iffP forallP) => h n //; case: (ltnP n (size w).+1) => [ltnsl | /ltnW ?].
  by have := h (Ordinal ltnsl).
by have := h (ord_max);  rewrite take_size take_oversize.
Qed.

Lemma preAword_rcons w a : preAword (rcons w a) -> preAword w.
Proof.
move/preAwordP=> preAwordla; apply/forallP=> [] [n hn] /=.
by move: (preAwordla n); rewrite -cats1 takel_cat.
Qed.

Definition Aword (w : seq step) : bool :=
  [&& (preAword w), #N w == #SE w & #SE w == #W w].

Lemma AwordP w :
  reflect [/\ (preAword w), #N w = #SE w & #SE w = #W w] (Aword w).
Proof. by apply: (iffP and3P); case=> preAw /eqP-> /eqP->. Qed.

Lemma ApreAword l : Aword l -> preAword l. Proof. by case/and3P. Qed.


(* We consider a family B of words on alphabet step. A word w is in B iff:
   - for any prefix p of w, #W p <= #SE p <= #N p
   -  #SE w - #W w = #N w - %SE w
  Intuitively (we do not verify this formally), words in B can be generated
   by taking:
   - a Dyck word d1 on (N, SEW) of lenght 3*k1 (the closing parenthesis is the
   concatenation of letters SE and W);
   - shuffled with a Dyck word d2 on (N, SE) of length 2*k2
   - with k2 letters N randomly inserted in the resulting entanglement of d1 and d2.
*)

Definition preBword (w : seq step) : bool :=
  [forall n : 'I_(size w).+1, #W (take n w) <= #SE (take n w) <= #N (take n w)].

Lemma preBwordP w :
  reflect (forall n : nat, #W (take n w) <= #SE (take n w) <= #N (take n w))
          (preBword w).
Proof.
apply: (iffP forallP) => h n //; case: (ltnP n (size w).+1) => [ltnsl | /ltnW ?].
  by have := h (Ordinal ltnsl).
by have := h (ord_max);  rewrite take_size take_oversize.
Qed.

Lemma preBword_rcons l a : preBword (rcons l a) -> preBword l.
Proof.
move/preBwordP=> preBwordla; apply/forallP=> [] [n hn] /=.
by move: (preBwordla n); rewrite -cats1 takel_cat.
Qed.

Definition Bword (w : seq step) : bool :=
  [&& (preBword w) & #SE w - #W w == #N w - #SE w].

Lemma BpreBword l : Bword l -> preBword l. Proof. by case/andP. Qed.

(* We prove that for a given n, there are as many words of length n
   in A and in B. *)

Definition cmpt2 := (nat * nat)%type.

(* The intuition is to represent the word transformations using automatons,
   with steps labelled with pairs of natural numbers and transitions labelled
   with 'step' letters. *)


Section StateMonadDefs.

Context {A B C : Type}.

Record store (A : Type) : Type := Store {data : A; ct : cmpt2}.

Definition mkStore {A} a n1 n2 : store A := Store a (n1, n2).

Definition state (A : Type) :=  cmpt2 -> store A.

Definition sreturn {A} (a : A) : state A := fun c => Store a c.

Definition sbind {A B} (sa : state A) (f : A -> state B) : state B :=
  fun x => let: Store a c := sa x in f a c.


(* A convenient notation for programming in monadic style, borrowed to Cyril :) *)
Notation "'sdo' x <- y ; z" :=
  (sbind y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' 'sdo'  x  <-  y ;  '/' z ']'").

Lemma sbind_return (a : A) (f : A -> state B) :
  (sdo x <- (sreturn a); f x) = f a.
Proof. by []. Qed.

Lemma sreturn_bind (sa : state A) : (sdo x <- sa; sreturn x) =1 sa.
Proof. by move=> c; rewrite /sbind; case: (sa c). Qed.

Lemma sbind_comp (f : A -> state B) (g : B -> state C) (sa : state A) :
(sdo b <- (sdo a <- sa; f a); g b) =1 (sdo a <- sa; sdo b <- (f a); g b).
Proof. by move=> c; rewrite /sbind; case: (sa c). Qed.

Fixpoint spipe (f : A -> state B) (l : seq A) : state (seq B) :=
  if l is a :: l then
    sdo s1 <- f a;
    sdo l1 <- spipe f l;
    sreturn (s1 :: l1)
 else sreturn [::].

Lemma spipe_nil f : spipe f [::] = sreturn [::]. by []. Qed.

Lemma spipe_cons f l a :
  spipe f (a :: l) = sdo s1 <- f a; sdo l1 <- spipe f l; sreturn (s1 :: l1).
Proof. by []. Qed.

Lemma data_spipe_nil f c : data (spipe f [::] c) = [::].
Proof. by []. Qed.

Lemma data_spipe_cons f s l c :
  data (spipe f (s :: l) c) =
  data (f s c) :: data (spipe f l (ct (f s c))).
Proof.
by rewrite /sbind /= /sbind; case: (f s c) => d1 c1 /=; case: (spipe f l c1).
Qed.

Lemma ct_spipe_nil f c : ct (spipe f [::] c) = c.
Proof. by []. Qed.

Lemma ct_spipe_cons f s l c :
  ct (spipe f (s :: l) c) = ct (spipe f l (ct (f s c))).
Proof.
by rewrite /sbind /= /sbind; case: (f s c) => d1 c1 /=; case: (spipe f l c1).
Qed.


Lemma data_spipe_cat f l1 l2 c :
  data (spipe f (cat l1 l2) c) =
  (data (spipe f l1 c)) ++ (data (spipe f l2 (ct (spipe f l1 c)))).
Proof.
elim: l1 l2 c => [| s l1 ihl1 l2 c] //; rewrite cat_cons [LHS]data_spipe_cons.
by rewrite ihl1 data_spipe_cons ct_spipe_cons cat_cons.
Qed.

Lemma data_spipe_rcons f s l c :
  data (spipe f (rcons l s) c) =
  rcons (data (spipe f l c)) (data (f s (ct (spipe f l c)))).
Proof. by rewrite -cats1 data_spipe_cat -cats1 data_spipe_cons. Qed.

Lemma ct_spipe_cat f l1 l2 c :
  ct (spipe f (l1 ++ l2) c) = ct (spipe f l2 (ct (spipe f l1 c))).
Proof.
elim: l1 l2 c => [| s l1 ihl1 l2 c] //; rewrite cat_cons [LHS]ct_spipe_cons.
by rewrite ihl1 ct_spipe_cons.
Qed.

Lemma ct_spipe_rcons f s l c :
  ct (spipe f (rcons l s) c) = ct (f s (ct (spipe f l c))).
Proof. by rewrite -cats1 ct_spipe_cat ct_spipe_cons. Qed.

End StateMonadDefs.

Notation "'sdo' x <- y ; z" :=
  (sbind y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' 'sdo'  x  <-  y ;  '/' z ']'").


Lemma bind_extl {A B} {s1 s2 : state A} {f : A -> state B} :
  s1 =1 s2 -> (sdo x <- s1; f x) =1 (sdo x <- s2; f x).
Proof. move=> eqs c; by rewrite /sbind eqs. Qed.

Lemma bind_extr {A B} {s : state A} {f1 f2 : A -> state B} :
  (forall a, f1 a =1 f2 a) -> (sdo x <- s; f1 x) =1 (sdo x <- s; f2 x).
Proof. by move=> ef c; rewrite /sbind; case: s => *; rewrite ef. Qed.

Lemma bind_eqr {A B} {s : state A} {f1 f2 : A -> state B} c (s1 := s c):
  f1 (data s1)  (ct s1) = f2 (data s1) (ct s1) ->
  (sdo x <- s; f1 x) c = (sdo x <- s; f2 x) c.
Proof. by rewrite /sbind {}/s1; case: (s c)=> d1 c1 /=. Qed.

Lemma bind_eql {A B} {s1 s2 : state A} {f : A -> state B} c :
  s1 c = s2 c ->(sdo x <- s1; f x) c = (sdo x <- s2; f x) c.
Proof. by rewrite /sbind=> ->. Qed.


Lemma spipe_cat {A B} (f : A -> state B) l1 l2 :
 spipe f (l1 ++ l2) =1 sdo l1 <- spipe f l1; sdo l2 <- spipe f l2;
                      sreturn (l1 ++ l2).
Proof.
elim: l1 l2 => [| s l1 ihl1] l2 //= c1.
  by rewrite sbind_return -[LHS]sreturn_bind; apply: bind_extr.
rewrite sbind_comp; apply: bind_extr=> b c2.
rewrite (bind_extl (ihl1 l2)) !sbind_comp; apply: bind_extr=> lb1 c.
by rewrite sbind_return sbind_comp; apply: bind_extr=> lb2 c3.
Qed.

Lemma spipe_rcons {A B} (f : A -> state B) l a :
 spipe f (rcons l a) =1
 sdo l1 <- spipe f l; sdo s1 <- f a; sreturn (rcons l1 s1).
Proof. move=> c1; rewrite -cats1 spipe_cat.
apply: bind_extr => lb /= c2; rewrite sbind_comp; apply: bind_extr=> b c3.
by rewrite sbind_comp !sbind_return cats1.
Qed.

(* Step by step transformation of an A-word into a B-word. The two counters are
   used to discriminate interleaved Dyck-words:
   - c2 checks for Dyck words on the alphabet (N-W, SE), where N-W is the
     concatenation of the two letters N and W, used as a single opening
     parenthesis. Each pair of such parentheses found by c2 is translated into
     (N-SE, W).
   - c1 checks for Dyck words on the alphabet (N, SE). Each pair of such parentheses
     found by c1 is translated into (N, SE).
   - remaining occurrences of letter W are translated to N
   - the last case of the match (SE, (0, 0)) is never reached when scanning an A-word. *)

Definition sA2B (s : step) : state step := fun c =>
  match s, c with
    |  W, (0, c2)      =>  mkStore N 0 c2
    |  W, (c1.+1, c2)  =>  mkStore SE c1 c2.+1
    |  N, (c1, c2)     =>  mkStore N c1.+1 c2
    |  SE, (c1, c2.+1) =>  mkStore W c1 c2
    |  SE, (c1.+1, 0)  =>  mkStore SE c1 0
    |  SE, (0, 0)      =>  mkStore N 0 0 (* junk *)
  end.

Arguments sA2B s c : simpl never.

(* Inverse transformation. *)
Definition sB2A (s : step) : state step := fun c =>
  match s, c with
    | N, (0, c2)      => mkStore W 0 c2
    | SE, (c1, c2.+1) => mkStore W c1.+1 c2
    | N, (c1.+1, c2)  => mkStore N c1 c2
    | W, (c1, c2)     => mkStore SE c1 c2.+1
    | SE, (c1, 0)     => mkStore SE c1.+1 0
  end.

Arguments sB2A s c : simpl never.

(* For any state x, if the counter statisfies the premisse, performing one step
   transformation after the other keeps x unchanged. Note that an A-word
   cannot start with SE hence in particular, this premisse condition is
   verified initially. *)

Lemma sA2BK (s : step) (c : cmpt2) :
  [|| (c.1 != 0%N), (c.2 != 0%N) | (s != SE)] ->
  (sdo x <- (sB2A s); sA2B x) c = sreturn s c.
Proof. by case: s; case: c => [] [| n1] [|n2]. Qed.

Lemma sB2AK  (s : step) (c : cmpt2) :
  [|| (c.1 != 0%N), (c.2 != 0%N) | (s != SE)] ->
  (sdo x <- (sA2B s); sB2A x) c = sreturn s c.
Proof. by case: s; case: c => [] [| n1] [|n2]. Qed.

Definition readA2B : seq step -> state (seq step) := spipe sA2B.
Definition readB2A : seq step -> state (seq step) := spipe sB2A.

Definition csum (c : cmpt2) : nat := (c.1 + c.2)%N.

Lemma csum0 c : csum c = 0%N -> c = (0%N, 0%N).
Proof. by case: c => [[| c1]] [| c2]. Qed.

Lemma csum0l c : csum (0%N, c) = c. by []. Qed.

Lemma csum0r c : csum (c, 0%N) = c. by rewrite /csum addn0. Qed.

Lemma csum_A2B_N c : csum (ct (sA2B N c)) = (csum c).+1.
Proof. by rewrite /csum; case: c => [[| c1]] [| c2]. Qed.


Lemma csum_A2B_W c : csum (ct (sA2B W c)) = csum c.
Proof.
by rewrite /csum; case: c => [[| c1]] [| c2]; rewrite ?addn0 ?addn1 ?addnS.
Qed.

(* This one is a bit clumsy. *)
Lemma csum_A2B_SE c : csum c = (csum (ct (sA2B SE c)) + (csum c != 0))%N.
Proof.
by rewrite /csum; case: c => [[| c1]] [| c2]; rewrite ?addn0 ?addn1 ?addnS.
Qed.


Lemma count_mem_rcons {T : eqType} l (a b : T) :
  count_mem a (rcons l b) = ((count_mem a l) + (b == a))%N.
Proof. by rewrite -cats1 count_cat /= addn0. Qed.

(* d1 is the number of Dyck words on (NW, SE) aready processed
   d2 is the number of Dyck words on (N, SE) aready processed
   fw is the number of "free" occurrences (i.e. which did not contribute to
   d1) already processed. *)
Record sA2B_invariant_data := InvData {d1 : nat; d2 : nat; fw : nat}.

Lemma preAword_rA2B_inv l ci (c := ct (readA2B l ci)) :
  preAword l ->
  exists i : sA2B_invariant_data,
    [/\ (csum ci + #N l = (d1 i) + (d2 i) + csum c)%N,
        (#SE l = (d1 i) + (d2 i))%N &
        (ci.2 + #W l = (d1 i) + c.2 + (fw i))%N].
Proof.
rewrite {}/c; elim/last_ind: l => [| l h ihl] /= preAwordlh.
   by exists (InvData 0%N 0%N 0%N); rewrite /= addn0.
rewrite !ct_spipe_rcons -/readA2B.
have {ihl} /ihl [[dl1 dl2 fwl /=]] : preAword l by exact: preAword_rcons.
move: (ct (readA2B l ci)) => c [eN eSE eW].
case: h preAwordlh => /preAwordP preAwordlh.
- have -> : #N (rcons l N) = (#N l).+1 by rewrite /count_N count_mem_rcons addn1.
  have -> : #W (rcons l N) = #W l by rewrite /count_W count_mem_rcons addn0.
  have -> : #SE (rcons l N) = #SE l by rewrite -cats1 /count_SE count_cat addn0.
  rewrite !csum_A2B_N !addnS eN; exists (InvData dl1 dl2 fwl); split => //=.
  suff {eN eW} -> : (ct (sA2B N c)).2 = c.2 by [].
  by case: c.
- have -> : #N (rcons l W) = #N l by rewrite /count_N count_mem_rcons addn0.
  have -> : #W (rcons l W) = (#W l).+1 by rewrite /count_W count_mem_rcons addn1.
  have -> : #SE (rcons l W) = #SE l by rewrite -cats1 /count_SE count_cat addn0.
  rewrite !csum_A2B_W !addnS {}eW {}eN {}eSE {preAwordlh}; case: c => [[| c1]] c2 /=.
    by rewrite csum0l /=; exists (InvData dl1 dl2 fwl.+1) => /=.
  by exists (InvData dl1 dl2 fwl); split => //=; rewrite addnS addSn.
- have nN : #N (rcons l SE) = #N l by rewrite /count_N count_mem_rcons addn0.
  have nW : #W (rcons l SE) = #W l by rewrite /count_W count_mem_rcons addn0.
  have nSE : #SE (rcons l SE) = (#SE l).+1.
    by rewrite /count_SE count_mem_rcons addn1.
  have {preAwordlh} lt_SE_N : (#SE l < #N l)%N.
    by move: (preAwordlh (size (rcons l SE))); rewrite take_size nSE nN.
  have {lt_SE_N} : csum c != 0%N.
    apply: contraL lt_SE_N => /eqP sumc0.
    by rewrite -leqNgt -[#SE l]addn0 eSE -sumc0 -eN leq_addl.
  rewrite {}nN {}nW {}nSE {}eN {}eSE {}eW.
  case: c => [[|c1]] [| c2] // _; rewrite ?csum0r ?csum0l /=.
  - by exists (InvData dl1.+1 dl2 fwl); rewrite ?addnS ?addSn.
  - by exists (InvData dl1 dl2.+1 fwl); rewrite /= addn0 !addnS !addSn.
  - by exists (InvData dl1.+1 dl2 fwl); rewrite /csum /= addnS !addSn !addnS.
Qed.

Lemma preAword_rA2B_noex l a ci (c := ct (readA2B l ci)) :
  preAword (rcons l a) -> [|| (c.1 != 0%N), (c.2 != 0%N) | (a != SE)].
Proof.
move=> laA.
have /(preAword_rA2B_inv ci) [[lad1 lad2 lafw] /=] : preAword l by apply: preAword_rcons.
rewrite -/c; case: c => [[|c1]] [|c2] //=; case: a laA => // laA.
rewrite addn0 addn0; case=> eN eSE eW.
suff : (#SE l < #N l)%N.
  by apply: contraL; rewrite -leqNgt eSE -eN leq_addl.
move/preAwordP/(_ (size (rcons l SE))): laA; rewrite take_size.
have -> : #N (rcons l SE) = #N l by rewrite /count_N count_mem_rcons addn0.
suff -> : #SE (rcons l SE) = (#SE l).+1 by [].
by rewrite /count_SE count_mem_rcons addn1.
Qed.

Lemma readA2BK l : preAword l ->
               (sdo x <- spipe sA2B l; spipe sB2A (rev x)) =1 sreturn (rev l).
Proof.
elim/last_ind: l => [| l a ihl] // preAword_la ci.
rewrite (bind_extl (spipe_rcons _ _ _)).
rewrite sbind_comp.
have /bind_extr -> a0 :
     (sdo b <- (sdo s1 <- (sA2B a); sreturn (rcons a0 s1)); spipe sB2A (rev b))
  =1 (sdo s1 <- (sA2B a); (sdo b <- sreturn (rcons a0 s1); spipe sB2A (rev b))).
  by move=> c; rewrite sbind_comp.
have /bind_extr -> x :
    (sdo s1 <- (sA2B a); (sdo b <- (sreturn (rcons x s1)); spipe sB2A (rev b)))
  =1 (sdo s1 <- (sA2B a); spipe sB2A (rev (rcons x s1))).
  by apply: bind_extr=> s; rewrite sbind_return.
have /bind_extr -> x :
    (sdo s1 <- (sA2B a); spipe sB2A (rev (rcons x s1)))
 =1 (sdo s1 <- (sA2B a); spipe sB2A (s1 :: (rev x))).
  by apply: bind_extr=> s; rewrite rev_rcons.
have -> :
  (sdo x <- (spipe sA2B l); (sdo s1 <- (sA2B a); spipe sB2A (s1 :: rev x))) ci =
  (sdo x <- (spipe sA2B l); sdo s1 <- sreturn a; sdo l1 <- spipe sB2A (rev x);
                             sreturn (s1 :: l1)) ci.
  apply: bind_eqr.
  have /bind_extr -> s1 :
  spipe sB2A (s1 :: rev (data (spipe sA2B l ci))) =1
  sdo s2 <- sB2A s1; sdo l1 <- spipe sB2A (rev (data (spipe sA2B l ci)));
  sreturn (s2 :: l1).
    by move=> c; rewrite spipe_cons.
  by rewrite -sbind_comp; apply: bind_eql; apply: sB2AK; exact: preAword_rA2B_noex.
rewrite -sbind_comp.
have /ihl  {ihl} /bind_extl -> : preAword l by apply: preAword_rcons.
by rewrite sbind_return rev_rcons.
Qed.



(* Characterization via trajectories.*)

(* A two-dimentional grid, as (a  warpper around) pairs of  integers *)

Import GRing.Theory Num.Theory.
Open Scope ring_scope.

Inductive grid := Grid of int * int.

(* Boilerplate code to install the structures of equality, countable, choice
   type on type step, plus a coercion from grid to paris of integers. *)

Coercion int_pair_of_grid (p : grid) := let: Grid xy := p in xy.

Canonical grid_subType := Eval hnf in [newType for int_pair_of_grid].

Definition grid_eqMixin := [eqMixin of grid by <:].
Canonical  grid_eqType  := EqType grid grid_eqMixin.

Definition grid_choiceMixin := [choiceMixin of grid by <:].
Canonical  grid_choiceType  := ChoiceType grid grid_choiceMixin.

Definition grid_countMixin   := [countMixin of grid by <:].
Canonical  grid_countType    := CountType grid grid_countMixin.
Canonical  grid_subCountType := Eval hnf in [subCountType of grid].
(* End boilerplate code *)

(* Origin of the grid *)
Definition origin := Grid (0, 0).

(* Abscissia and ordinate of a point of the grid *)
Definition abs  := (fun g : grid => g.1).
Definition ord  := (fun g : grid => g.2).

Lemma grid_eq g1 g2 : (g1 == g2) = (abs g1 == abs g2) && (ord g1 == ord g2).
Proof. by []. Qed.

(* Several predicates describing zones of interest in the grid *)
Definition diag (g : grid) : bool := abs g == ord g.

(* North (closed) half plane *)
Definition nhalf (g : grid) : bool := 0 <= ord g.

(* South (closed) half plane *)
Definition shalf (g : grid) : bool := ord g <= 0.

(* East (closed) half plane *)
Definition ehalf (g : grid) : bool := 0 <= abs g.

(* West (closed) half plane *)
Definition whalf (g : grid) : bool := abs g <= 0.

(* Quadrant I *)
Definition Iquadrant := predI nhalf ehalf.

Arguments Iquadrant : simpl never.

(* (* Quadrant II *) *)
(* Definition IIquadrant : bool := predI nhalf whalf. *)

(* (* Quadrant III *) *)
(* Definition IIIquadrant : bool := predI shalf whalf. *)

(* (* Quadrant IV *) *)
(* Definition IVquadrant : bool := predI shalf ehalf. *)


(* We interpret each step as a function : grid -> grid, with the following
   semantic:
   - North (coded by 0) means increasing ordinate of 1, leaving abscissia unchanged
   - West (coded by 1) means decreasing abscissia of 1, leaving ordinate unchanged
   - SouthEast (coded by 2) means decreading both ordinate and abscissia. *)


Definition move_of_step (g : grid) (s : step) : grid :=
  let: Grid (g1, g2) := g in
  match s with
    |N  => Grid (g1, g2 + 1)
    |W  => Grid (g1 - 1, g2)
    |SE => Grid (g1 + 1, g2 - 1)
  end.

Arguments move_of_step : simpl never.

Lemma move_of_north g : move_of_step g N = Grid (abs g, ord g + 1).
Proof. by case: g; case=> g1 g2. Qed.

Lemma move_of_west g : move_of_step g W = Grid (abs g - 1, ord g).
Proof.  by case: g; case=> g1 g2. Qed.

Lemma move_of_seast g : move_of_step g SE = Grid (abs g + 1, ord g - 1).
Proof.  by case: g; case=> g1 g2. Qed.

Lemma abs_move_N g : abs (move_of_step g N) = abs g.
Proof. by rewrite move_of_north. Qed.

Lemma abs_move_W g : abs (move_of_step g W) = abs g - 1.
Proof. by rewrite move_of_west. Qed.

Lemma abs_move_SE g : abs (move_of_step g SE) = abs g + 1.
Proof. by rewrite move_of_seast. Qed.

Lemma ord_move_N g : ord (move_of_step g N) = ord g + 1.
Proof. by rewrite move_of_north. Qed.

Lemma ord_move_W g : ord (move_of_step g W) = ord g.
Proof. by rewrite move_of_west. Qed.

Lemma ord_move_SE g : ord (move_of_step g SE) = ord g - 1.
Proof. by rewrite move_of_seast. Qed.


(* We call (trajectory g w) the sequence of positions prescribed by a sequence of
   steps w , from a starting point g of the grid. If the list of steps is of the
   form s :: w, the move coded by s is executed first. (final_pos g w) is the
   final position on the grid reached at the end of the trajectory.*)

Definition final_pos := foldl move_of_step.

Lemma final_pos_nil g : final_pos g [::] = g. Proof. by []. Qed.

Lemma final_pos_cons g s w :
  final_pos g (s :: w) = final_pos (move_of_step g s) w.
Proof. by []. Qed.

Lemma final_pos_cat g w1 w2 :
  final_pos g (w1 ++ w2) = final_pos (final_pos g w1) w2.
Proof. by rewrite /final_pos foldl_cat. Qed.

Lemma abs_final g w :
  abs (final_pos g w) = abs g + (count_SE w)%:Z - (count_W w)%:Z.
Proof.
elim: w g => [| s w ihw] /= g; first by rewrite addrK.
rewrite ihw; case: s => /=; rewrite !add0n ?add1n; first by rewrite abs_move_N.
- by rewrite abs_move_W intS opprD addrACA addrA.
- by rewrite abs_move_SE intS addrA.
Qed.

Lemma ord_final g w :
  ord (final_pos g w) = ord g + (count_N w)%:Z - (count_SE w)%:Z.
Proof.
elim: w g => [| s w ihw] /= g; first by rewrite addrK.
rewrite ihw; case: s => /=; rewrite !add0n ?add1n ?intS.
- by rewrite ord_move_N addrA.
- by rewrite ord_move_W.
- by rewrite ord_move_SE opprD addrACA addrA.
Qed.

Definition trajectory := scanl move_of_step.

Lemma trajectory_nil g : trajectory g [::] = [::]. by []. Qed.

Lemma trajectory_cons g s w :
  trajectory g (s :: w) = (move_of_step g s) :: trajectory (move_of_step g s) w.
Proof. by []. Qed.

Lemma last_trajectory g w : last g (trajectory g w) = final_pos g w.
Proof.
rewrite /final_pos /trajectory (last_nth g) size_scanl; case: w => [| s w] //.
by rewrite [size _]/= [LHS]nth_scanl // -[(size w).+1]/(size (s :: w)) take_size.
Qed.

Lemma trajectory_cat g w1 w2 :
  trajectory g (w1 ++ w2) = trajectory g w1 ++ (trajectory (final_pos g w1) w2).
Proof. by rewrite /trajectory scanl_cat. Qed.

Lemma size_trajectory g w : size (trajectory g w) = size w.
Proof. by rewrite /trajectory size_scanl. Qed.

Lemma nth_trajectory g1 g2 w n : (n < size w)%N ->
   nth g1 (trajectory g2 w) n = final_pos g2 (take n.+1 w).
Proof. by move=> ltnsw; rewrite nth_scanl. Qed.

Lemma final_pos_take g w n :
  final_pos g (take n.+1 w) = nth (final_pos g w) (trajectory g w) n.
Proof.
case: (ltnP n (size  w)) => hnsw; first by rewrite nth_scanl.
rewrite take_oversize; last by apply: leq_trans hnsw _.
by rewrite nth_default // size_trajectory.
Qed.

Lemma abs_nth_trajectory g1 g2 w n : (n < size w)%N ->
  abs (nth g1 (trajectory g2 w) n) =
  abs g2 + (count_SE (take n.+1 w))%:Z - (count_W (take n.+1 w))%:Z.
Proof. by move=> ?; rewrite nth_trajectory // abs_final. Qed.

Lemma ord_nth_trajectory g1 g2 w n : (n < size w)%N ->
  ord (nth g1 (trajectory g2 w) n) =
  ord g2 + (count_N (take n.+1 w))%:Z - (count_SE (take n.+1 w))%:Z.
Proof. by move=> ?; rewrite nth_trajectory // ord_final. Qed.

Lemma trajectory_final g w : final_pos g w \in g :: trajectory g w.
Proof.
case: w => [|s w]; first by rewrite /= mem_seq1.
rewrite -[X in final_pos g X \in _]take_size [size _]/= -(nth_trajectory g) //.
by rewrite in_cons mem_nth ?orbT // size_trajectory.
Qed.

Lemma trajectory_final_cons g s w :
  final_pos g (s :: w) \in trajectory g (s :: w).
Proof. by rewrite /=; exact: trajectory_final. Qed.

(* Several predicates on the final position of a trajectory *)

Definition to_diag_traj (g : grid) (w : seq step) : bool :=
  diag (final_pos g w).

(* Not sure this is the usefull form... *)
Lemma to_diag_trajP g w :
 reflect (abs g + (count_SE w)%:Z -  (count_W w)%:Z =
          ord g + (count_N w)%:Z - (count_SE w)%:Z)
         (to_diag_traj g w).
Proof. by apply: (iffP eqP); rewrite /to_diag_traj abs_final ord_final. Qed.

Lemma oto_diag_trajP w :
 reflect ((count_SE w)%:Z - (count_W w)%:Z = (count_N w)%:Z - (count_SE w)%:Z)
         (to_diag_traj origin w).
Proof.
rewrite -[LHS]add0r -[RHS]add0r !addrA; exact: (to_diag_trajP origin).
Qed.

Definition loop_traj (g : grid) (w : seq step) : bool := final_pos g w == g.

Lemma loop_trajP (g : grid) (w : seq step) :
  reflect (count_N w = count_SE w /\ count_SE w = count_W w) (loop_traj g w).
Proof.
rewrite /loop_traj grid_eq.
apply: (iffP andP); rewrite ord_final abs_final; case; last first.
  by move=> -> ->; rewrite !addrK.
rewrite -!addrA ![_ + (_ - _) == _](can2_eq (addKr _) (addNKr _)) !addNr !subr_eq0.
by move=> /eqP [] <- /eqP [] ->.
Qed.


(* Properties of trajectories that start and stay in the north half plane *)
Definition nhalf_traj (g : grid) (w : seq step) : bool :=
  all nhalf (g :: (trajectory g w)).

Lemma nhalf_trajE g w : nhalf_traj g w = nhalf g && all nhalf (trajectory g w).
Proof. by []. Qed.

Lemma nhalf_traj_cat  g w1 w2 :
  nhalf_traj g (w1 ++ w2) =
  nhalf_traj g w1 && nhalf_traj (final_pos g w1) w2.
Proof.
rewrite [in LHS]/nhalf_traj trajectory_cat -cat_cons all_cat.
apply: andb_id2l; rewrite nhalf_trajE; move/allP/(_ _ (trajectory_final _ _))->.
done.
Qed.

(* If the trajectory along w from the origin stays in the north half-plane,
  then the number of SE in w is smaller than the number of N *)
Lemma nhalf_otraj_le w : nhalf_traj origin w ->
  (count_SE w <= count_N w)%N.
Proof.
move/allP/(_ _ (trajectory_final _ _)); rewrite /nhalf ord_final add0r subr_ge0.
done.
Qed.

(* If  the trajectory along w from the origin stays in the north half-plane,
  then for every of its prefixes w' the number of SE in w' is smaller than
  the number of N *)


Lemma nhalf_otraj_pre w1 w2 : nhalf_traj origin (w1 ++ w2) ->
  (count_SE w1 <= count_N w1)%N.
Proof. by rewrite nhalf_traj_cat; case/andP=> /nhalf_otraj_le. Qed.

(* This is in fact characterizing trajectories from the origin that stay in
   the north plane *)
Lemma nhalf_otrajP w :
  reflect (forall n, count_SE (take n w) <= count_N (take n w))%N
          (nhalf_traj origin w).
Proof.
apply: (iffP idP) => [ntw n| countle].
  by move: ntw; rewrite -{1}[w](cat_take_drop n); move/nhalf_otraj_pre.
rewrite nhalf_trajE /=; apply/(all_nthP origin) => i ltisw.
rewrite /nhalf ord_nth_trajectory -?(size_trajectory origin) // subr_ge0.
exact: countle.
Qed.

(* The analogue theory for trajectories staying in the east half plane.
   Copy-paste mutatis mutandis. *)

Definition ehalf_traj (g : grid) (w : seq step) : bool :=
  all ehalf (g :: (trajectory g w)).

Lemma ehalf_trajE g w :
  ehalf_traj g w = ehalf g && all ehalf (trajectory g w).
Proof. by []. Qed.

Lemma ehalf_traj_cat  g w1 w2 :
  ehalf_traj g (w1 ++ w2) =
  ehalf_traj g w1 && ehalf_traj (final_pos g w1) w2.
Proof.
rewrite [in LHS]/ehalf_traj trajectory_cat -cat_cons all_cat.
apply: andb_id2l; rewrite ehalf_trajE; move/allP/(_ _ (trajectory_final _ _))->.
done.
Qed.

(* If  the trajectory along w from the origin stays in the east half-plane,
  then the number of W in w is smaller than the number of SE *)
Lemma ehalf_otraj_le w : ehalf_traj origin w -> (count_W w <= count_SE w)%N.
Proof.
move/allP/(_ _ (trajectory_final _ _)); rewrite /ehalf abs_final add0r subr_ge0.
done.
Qed.

(* If  the trajectory along w from the origin stays in the north half-plane,
  then for every of its prefixes w' the number of W in w' is smaller than
  the number of SE *)

Lemma ehalf_otraj_pre w1 w2 : ehalf_traj origin (w1 ++ w2) ->
  (count_W w1 <= count_SE w1)%N.
Proof. by rewrite ehalf_traj_cat; case/andP=> /ehalf_otraj_le. Qed.

(* This is in fact characterizing trajectories from the origin that stay in
   the east plane *)
Lemma ehalf_otrajP w :
  reflect (forall n, count_W (take n w) <= count_SE (take n w))%N
          (ehalf_traj origin w).
Proof.
apply: (iffP idP) => [ntw n| countle].
  by move: ntw; rewrite -{1}[w](cat_take_drop n); move/ehalf_otraj_pre.
rewrite ehalf_trajE /=; apply/(all_nthP origin) => i ltisw.
rewrite /ehalf abs_nth_trajectory -?(size_trajectory origin) // subr_ge0.
exact: countle.
Qed.

Definition Iquadrant_traj (g : grid) (w : seq step) : bool :=
  all Iquadrant (g :: (trajectory g w)).

Lemma Iquadrant_trajE g w :
  Iquadrant_traj g w = Iquadrant g && all Iquadrant (trajectory g w).
Proof. by []. Qed.

Lemma Iquadrant_nhalf_traj g w : Iquadrant_traj g w -> nhalf_traj g w.
Proof. by rewrite [Iquadrant_traj _ _]all_predI; case/andP. Qed.

Lemma Iquadrant_ehalf_traj g w : Iquadrant_traj g w -> ehalf_traj g w.
Proof. by rewrite [Iquadrant_traj _ _]all_predI; case/andP. Qed.

Lemma Iquadrant_nehalf_traj g w :
  Iquadrant_traj g w = (nhalf_traj g w) && (ehalf_traj g w).
Proof. by rewrite /Iquadrant_traj /Iquadrant all_predI. Qed.

Lemma Iquadrant_traj_cat  g w1 w2 :
  Iquadrant_traj g (w1 ++ w2) =
  Iquadrant_traj g w1 && Iquadrant_traj (final_pos g w1) w2.
Proof.
rewrite [in LHS]/Iquadrant_traj trajectory_cat -cat_cons all_cat.
apply: andb_id2l => /allP/(_ _ (trajectory_final _ _)).
by rewrite Iquadrant_trajE; move->.
Qed.

Lemma Iquadrant_otraj_le w : Iquadrant_traj origin w ->
  (count_W w <= count_SE w <= count_N w)%N.
Proof.
move=> itow; rewrite ehalf_otraj_le; last exact: Iquadrant_ehalf_traj.
rewrite nhalf_otraj_le //; exact: Iquadrant_nhalf_traj.
Qed.

Lemma Iquadrant_otraj_pre w1 w2 : Iquadrant_traj origin (w1 ++ w2) ->
  (count_W w1 <= count_SE w1 <= count_N w1)%N.
Proof.
by rewrite Iquadrant_traj_cat; case/andP=> itow1 _; apply: Iquadrant_otraj_le.
Qed.

Lemma Iquadrant_otrajP w :
  reflect (forall n, count_W (take n w) <= count_SE (take n w)
                                       <= count_N (take n w))%N
          (Iquadrant_traj origin w).
Proof.
apply: (iffP idP) => [ntw n| countle].
  move/Iquadrant_nhalf_traj: (ntw) => /nhalf_otrajP ->.
  by move/Iquadrant_ehalf_traj: (ntw) => /ehalf_otrajP ->.
rewrite Iquadrant_nehalf_traj.
have /nhalf_otrajP -> :
  forall n, (count_SE (take n w))%:Z <= (count_N (take n w))%:Z.
  by move=> n; case/andP: (countle n).
by apply/ehalf_otrajP=> n; case/andP: (countle n).
Qed.


(* A sequence is an Asequence if its associated trajectory from the origin stays in
   the upper (north) half-plane and ends at the origin: *)

Definition Aseq (w : seq step) := nhalf_traj origin w && loop_traj origin w.

Lemma Aseq_nhalf w : w \in Aseq -> nhalf_traj origin w.
Proof. by case/andP. Qed.

Lemma Aseq_oloop w : w \in Aseq -> loop_traj origin w.
Proof. by case/andP. Qed.

(* An Aseq necessarily has an equal number of N, W and SE *)
Lemma Aseq_count_NW : {in Aseq, count_N =1 count_W}.
Proof. by move=> w /Aseq_oloop /loop_trajP; case=> ->. Qed.

Lemma Aseq_count_SEW : {in Aseq, count_SE =1 count_W}.
Proof. by move=> w /Aseq_oloop /loop_trajP; case=> _ ->. Qed.

Lemma Aseq_count_NSE : {in Aseq, count_N =1 count_SE}.
Proof. by move=> w Aw; rewrite /= Aseq_count_NW // Aseq_count_SEW. Qed.

(* Any prefix of an Aseq has more N than SE: *)
Lemma Aseq_pre w1 w2 : w1 ++ w2 \in Aseq ->
  (count_SE w1)%:Z <= (count_N w1)%:Z.
Proof. by move/Aseq_nhalf/nhalf_otraj_pre. Qed.

Lemma AseqP w : reflect
                [/\ forall n, (count_SE (take n w))%:Z <= (count_N (take n w))%:Z,
                    count_N w = count_SE w & count_SE w = count_W w]
                (Aseq w).
Proof.
apply: (iffP idP).
  by rewrite /Aseq; case/andP => /nhalf_otrajP=> ? /loop_trajP; case.
by rewrite /Aseq; case=> /nhalf_otrajP => -> /= he1 he2; apply/loop_trajP.
Qed.

(* A sequence is a B-sequence if its trajectory from the origin stays in
   quadrant I and ends somewhere on the diagonal: *)
Definition Bseq (w : seq step) :=
  Iquadrant_traj origin w && to_diag_traj origin w.

Lemma Bseq_Iquadrant w : w \in Bseq -> Iquadrant_traj origin w.
Proof. by case/andP. Qed.

Lemma Bseq_oto_diag w : w \in Bseq -> to_diag_traj origin w.
Proof. by case/andP. Qed.

(* A Bseq necessarily has less W than SE than N *)
Lemma Bseq_count_le w : w \in Bseq ->
   (count_W w)%:Z <= (count_SE w)%:Z <= (count_N w)%:Z.
Proof. by move/Bseq_Iquadrant/Iquadrant_otraj_le. Qed.

Lemma Bseq_pre w1 w2 : w1 ++ w2 \in Bseq ->
   (count_W w1)%:Z <= (count_SE w1)%:Z <= (count_N w1)%:Z.
Proof. by move/Bseq_Iquadrant/Iquadrant_otraj_pre. Qed.

(* Again we inherit from the tentative statement of
   to_diagP, probably not in its most convenient form. *)
Lemma Bseq_count w : w \in Bseq ->
  (count_SE w)%:Z - (count_W w)%:Z = (count_N w)%:Z - (count_SE w)%:Z.
Proof. by move/Bseq_oto_diag/oto_diag_trajP. Qed.

Lemma BseqP w : reflect
                  ((forall n, (count_W (take n w))%:Z <= (count_SE (take n w))%:Z
                                                      <= (count_N (take n w))%:Z)
                  /\
                    (count_SE w)%:Z - (count_W w)%:Z =
                    (count_N w)%:Z - (count_SE w)%:Z)
                  (Bseq w).
Proof.
apply: (iffP idP).
  by rewrite /Bseq; case/andP => /Iquadrant_otrajP=> ? /oto_diag_trajP.
by case=> /Iquadrant_otrajP iw /oto_diag_trajP odw; rewrite /Bseq iw.
Qed.

(* A state monad for datas of type A equipped with two counters *)

(* Now we have all the necessary vocabulary to describe the families of walks
   the exercise is about *)


(* A (walk n) is (a wrapper around) a sequence of size n  *)

Inductive walk (n : nat) := Walk of n.-tuple step.


(* Boilerplate code to install the structures of equality, countable, choice and
   finite type on type (walk n), plus a coercion from (walk n) to n-tuple. *)

Coercion tuple_of_walk (n : nat) (w : walk n) := let: Walk t := w in t.

Canonical walk_subType (n : nat) := Eval hnf in [newType for (@tuple_of_walk n)].

Definition walk_eqMixin (n : nat) := [eqMixin of (walk n) by <:].
Canonical  walk_eqType (n : nat) := EqType (walk n) (walk_eqMixin n).

Definition walk_choiceMixin (n : nat) := [choiceMixin of (walk n) by <:].
Canonical  walk_choiceType (n : nat) := ChoiceType (walk n) (walk_choiceMixin n).

Definition walk_countMixin (n : nat) := [countMixin of (walk n) by <:].
Canonical  walk_countType (n : nat)  := CountType (walk n) (walk_countMixin n).
Canonical  walk_subCountType (n : nat) := Eval hnf in [subCountType of (walk n)].

Definition walk_finMixin (n : nat)  := [finMixin of (walk n) by <:].
Canonical  walk_finType (n : nat)   := FinType (walk n) (walk_finMixin n).
Canonical  walk_subFinType (n : nat) := Eval hnf in [subFinType of (walk n)].
(* End boilerplate code *)

(* An n-Awalk is an Asequence of length n *)
Definition Awalk (n : nat) (w : walk n) := Aseq w.

(* An n-Bwalk is a B-sequence  of length n *)
Definition Bwalk (n : nat) (w : walk n) := Bseq w.

(* And the conjecture is the following: *)
(* Conjecture card_Awalks_Bwalks : forall n : nat, #|@Awalk n| = #|@Bwalk n|. *)

(* Rmk : I would like n to be implicit in definitions Aseq and Bseq, but
   I do not manage to overrid the flag set by my global options, even
   with the Argument command. Is it possible? *)
