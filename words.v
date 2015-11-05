Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice tuple fintype (* finfun finset *).

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
    |N  => @Ordinal 3 0 (refl_equal true)
    |W  => @Ordinal 3 1 (refl_equal true)
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
(* (#N w) is the number of occurrences of N in word w, etc. *)

Notation "#N" := (count_mem N).
Notation "#W" := (count_mem W).
Notation "#SE" := (count_mem SE).

Lemma count_steps_size (w : seq step) : (#N w) + (#W w) + (#SE w) = size w.
Proof.
elim: w => // [[]] l /= <-. rewrite !add0n.
- by rewrite -[RHS]add1n !addnA.
- by rewrite [_ + (1 + _)]addnCA -!addnA add1n.
- by rewrite [_ + (1 + _)]addnCA add1n.
Qed.

Lemma count_mem_rcons {T : eqType} (t : T) (w : seq T) (a : T) :
  count_mem t (rcons w a) =
  if (a == t) then (count_mem t w).+1 else count_mem t w.
Proof.
by rewrite -cats1 count_cat /=; case: ifP=> _; rewrite ?addn0 ?addn1.
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
by have := h (ord_max); rewrite take_size take_oversize.
Qed.

Lemma preA_rcons a w : (rcons w a) \in preAword  -> w \in preAword.
Proof.
move/preAwordP=> preAwordla; apply/forallP=> [] [n hn] /=.
by move: (preAwordla n); rewrite -cats1 takel_cat.
Qed.

Arguments preA_rcons a {w} _.

Definition Aword (w : seq step) : bool :=
  [&& (preAword w), #N w == #SE w & #SE w == #W w].

Lemma AwordP w :
  reflect [/\ (preAword w), #N w = #SE w & #SE w = #W w] (Aword w).
Proof. by apply: (iffP and3P); case=> preAw /eqP-> /eqP->. Qed.

Lemma ApreAword l : l \in Aword -> l \in preAword. Proof. by case/and3P. Qed.


(* We consider a family B of words on alphabet step. A word w is in B iff:
   - for any prefix p of w, #W p <= #SE p <= #N p
   -  #SE w - #W w = #N w - %SE w
  Intuitively (we do not verify this formally), words in B can be generated
  by taking:
   - a Dyck word d1 on (N, SEW) of lenght 3*k1 (the closing parenthesis is the
   concatenation of letters SE and W);
   - shuffled with a Dyck word d2 on (N, SE) of length 2*k2
    - with k2 letters N randomly inserted in the resulting entanglement of d1
  and d2.
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
   in family A and in family B by constructing a bijection from A to B. *)

Inductive state := State of nat * nat.

Notation "'{|' c1 ; c2 '|}'" := (State (c1, c2)).

Coercion nat2_of_state s : (nat * nat) := let: State c := s in c.

Canonical state_subType := [newType for nat2_of_state].

Definition state_eqMixin := Eval hnf in [eqMixin of state by <:].
Canonical state_eqType := Eval hnf in EqType state state_eqMixin.
Definition state_choiceMixin := [choiceMixin of state by <:].
Canonical state_choiceType :=
  Eval hnf in ChoiceType state state_choiceMixin.
Definition state_countMixin := [countMixin of state by <:].
Canonical state_countType := Eval hnf in CountType state state_countMixin.
Canonical state_subCountType := [subCountType of state].

Definition tA2B (c : state) (s : step) : step * state :=
  match s, c with
    |  W,  {|0    ; c2   |} => (N,  {|0    ; c2   |}) (* _ , _  *)
    |  W,  {|c1.+1; c2   |} => (SE, {|c1   ; c2.+1|}) (* -1, +1 *)
    |  N,  {|c1   ; c2   |} => (N,  {|c1.+1; c2   |}) (* +1, _  *)
    |  SE, {|c1   ; c2.+1|} => (W,  {|c1   ; c2   |}) (* _ , -1 *)
    |  SE, {|c1.+1; 0    |} => (SE, {|c1   ; 0    |}) (* -1, _  *)
    |  SE, {|0    ; 0    |} => (N,  {|0    ; 0    |}) (* junk *)
  end.

Arguments tA2B c s : simpl never.

Definition sA2B nn s := snd (tA2B nn s).

Definition cA2B (cf ci : state) : step :=
  let: {|ci1; ci2|} := ci in
  let: {|cf1; cf2|} := cf in
  if [&& ci1 == 0, cf1 == 0 & (ci2 == cf2)] then W
  else if (ci1 == cf1.+1) && (cf2 == ci2.+1) then W
  else if (cf1 == ci1.+1) && (ci2 == cf2) then N
  else if (ci2 == cf2.+1) && (ci2 == cf2) then SE
  else if (ci1 == cf1.+1) && (ci2 == 0) && (cf2 == 0) then SE
  else SE (* junk *).

(* Converse transducer *)
Definition tB2A (c : state) (s : step) : step * state :=
  match s, c with
    | N,  {|0    ; c2   |} => (W,  {|0    ; c2   |}) (* _ , _  *)
    | SE, {|c1   ; c2.+1|} => (W,  {|c1.+1; c2   |}) (* +1, -1 *)
    | N,  {|c1.+1; c2   |} => (N,  {|c1   ; c2   |}) (* -1, _  *)
    | W,  {|c1   ; c2   |} => (SE, {|c1   ; c2.+1|}) (* _ , +1 *)
    | SE, {|c1   ; 0    |} => (SE, {|c1.+1; 0    |}) (* +1, _  *)
  end.

Arguments tB2A c s : simpl never.

Definition sB2A nn s := snd (tB2A nn s).

Definition cB2A (cf ci : state) : step :=
  let: {|ci1; ci2|} := ci in
  let: {|cf1; cf2|} := cf in
  if [&& ci1 == 0, cf1 == 0 & (ci2 == cf2)] then N
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then SE
  else if (ci1 == cf1.+1) && (ci2 == cf2) then N
  else if (ci1 == cf1) && (cf2 == ci2.+1) then W
  else SE.


Definition A2Bstates (c : state) (ls : seq step) : seq state :=
  scanl sA2B c ls.

Definition A2B_from (c : state) (ls : seq step) : seq step :=
  pairmap cB2A c (A2Bstates c ls).

Definition A2B := A2B_from {|0; 0|}.

Eval compute in A2B [:: N; W; SE]. (* [:: N; SE; W] *)
Eval compute in A2B [:: N; SE; W]. (* [:: N; SE; N] *)
Eval compute in A2B [:: W; N; SE]. (* [:: N; N; SE] *)


Definition B2Astates  (c : state) (ls : seq step) : seq state :=
  scanl sB2A c ls.

Definition B2A_from (c : state) (ls : seq step) : seq step :=
  pairmap cA2B c (B2Astates c ls).

Definition B2A (ls : seq step) := rev (B2A_from {|0; 0|} (rev ls)).

Eval compute in B2A [:: N; SE; W]. (* [:: N; W; SE] *)
Eval compute in B2A [:: N; SE; N]. (* [:: N; SE; W] *)
Eval compute in B2A [:: N; N; SE]. (* [:: W; N; SE] *)

Definition noex  (s : step) (c : state) :=
  [|| (c.1 != 0%N), (c.2 != 0%N) | (s != SE)].


(* Begin: This should go to the MathComp library... *)
Section Scan.

Variables (T1 : Type) (x1 : T1) (T2 : Type) (x2 : T2).
Variables (f : T1 -> T1 -> T2) (g : T1 -> T2 -> T1).

Lemma last_scanl s : last x1 (scanl g x1 s) = foldl g x1 s.
Proof.
case: s => [| a s] //=.
rewrite (last_nth (g x1 a)) size_scanl -/(scanl g x1 (a :: s)) nth_scanl //.
by rewrite -[_.+1]/(size (a :: s)) take_size.
Qed.

Lemma foldl_rcons s t :
  foldl g x1 (rcons s t) = g (foldl g x1 s) t.
Proof. by rewrite -cats1 foldl_cat. Qed.

Lemma scanl_rcons s t :
  scanl g x1 (rcons s t) = rcons (scanl g x1 s) (foldl g x1 (rcons s t)).
Proof. by rewrite -cats1 scanl_cat /= foldl_cat cats1. Qed.


End Scan.

(* End: This should go to the MathComp library... *)

Lemma sB2A_round c h : sB2A (sA2B c h) (cB2A c (sA2B c h)) = c.
Proof.
by case: c => [] [] [|?] [|?]; case: h => //=; rewrite ?eqxx ?andbF //= ltn_eqF.
Qed.

Lemma cA2B_round d h : noex h d ->
  cA2B (sA2B d h) (sB2A (sA2B d h) (cB2A d (sA2B d h))) = h.
Proof.
case: d => [] [] [|c1] [|c2]; case: h => //= _;
  rewrite ?eqxx /sA2B /tA2B /= ?eqxx ?andbF
                /sB2A /tB2A /= ?eqxx ?andbF // ltn_eqF //=.
- by rewrite eq_sym ltn_eqF // andbF.
- by rewrite andbF ltn_eqF //= if_same.
- by rewrite ltn_eqF // andbF /= !eqxx.
- by rewrite ltn_eqF //= if_same.
Qed.

Section FirstStep.

(* We leave as (temporary) hypotheses the facts that requires introducing
   ghost variables: *)

Hypothesis preA_noex : forall l h c,
   rcons l h \in preAword -> noex h (foldl sA2B c l).

Lemma revA2B_fromK l c : l \in preAword ->
    rev (B2A_from (foldl sA2B c l) (rev (A2B_from c l))) = l.
Proof.
elim/last_ind: l c => [| l h ihl c pAlh] //=.
set cf := foldl _ _ _.
rewrite /A2B_from /A2Bstates scanl_rcons -cats1 pairmap_cat rev_cat /=.
set s := cB2A _ _.
rewrite -/(A2B_from c l) /B2A_from /= rev_cons; congr rcons.
  suff {ihl} -> : sB2A cf s = foldl sA2B c l by apply/ihl/(preA_rcons h).
  rewrite {}/cf {}/s last_scanl foldl_rcons; exact: sB2A_round.
rewrite {}/cf {}/s foldl_rcons last_scanl; apply: cA2B_round; exact: preA_noex.
Qed.

Hypothesis A_final_state : forall l,
  l \in Aword -> foldl sA2B {|0; 0|} l = {|0; 0|}.

Lemma A2BK_ : {in Aword, cancel A2B B2A}.
Proof.
move=> l /= Al; rewrite /B2A -(A_final_state Al); apply: revA2B_fromK.
exact: ApreAword.
Qed.

End FirstStep.

(* Now we prove the two remaining facts about words in A, plus the important
  missing property of A2B : that its image is included in Bword *)


Record ghost_state :=
  GState {ct1: nat; ct2: nat; dy1 : nat; dy2 : nat; free : nat}.

Definition GState_alt (c : state) (d1 d2 f : nat) : ghost_state :=
  GState c.1 c.2 d1 d2 f.

Definition state_of_ghost (g : ghost_state) :=
  let: GState c1 c2 _ _ _ := g in State (c1, c2).

(* Last case is junk *)
Definition tA2B_ghost_ (g : ghost_state)  (s : step) : step * ghost_state :=
match s, g with
  |W,  GState 0     c2    d1 d2 f  =>  (N,  GState 0     c2     d1    d2    f.+1)
  |W,  GState c1.+1 c2    d1 d2 f  =>  (SE, GState c1    c2.+1  d1    d2    f   )
  |N,  GState c1    c2    d1 d2 f  =>  (N,  GState c1.+1 c2     d1    d2    f   )
  |SE, GState c1    c2.+1 d1 d2 f  =>  (W,  GState c1    c2     d1.+1 d2    f   )
  |SE, GState c1.+1 0     d1 d2 f  =>  (SE, GState c1     0     d1    d2.+1 f   )
  |SE, GState 0     0     d1 d2 f  =>  (N,  GState  0     0     d1    d2    f   )
end.

Definition tA2B_ghost := nosimpl tA2B_ghost_.

Definition sA2B_ghost nn s := snd (tA2B_ghost nn s).

Definition cB2A_ghost gf gi :=
  let: {|ci1; ci2|} := state_of_ghost gi in
  let: {|cf1; cf2|} := state_of_ghost gf in
  if [&& ci1 == 0, cf1 == 0 & (ci2 == cf2)] then N
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then SE
  else if (ci1 == cf1.+1) && (ci2 == cf2) then N
  else if (ci1 == cf1) && (cf2 == ci2.+1) then W
  else SE.

Definition A2Bstates_ghost (g : ghost_state) (ls : seq step) : seq ghost_state :=
  scanl sA2B_ghost g ls.

Definition A2B_ghost_from (g : ghost_state) (ls : seq step) : seq step :=
  pairmap cB2A_ghost g (A2Bstates_ghost g ls).

(* Complete invariant. By brute force case analysis excepy for the only *)
(* interesting case of the (tail) induction on l is, i.e. when it ends with SE: *)
(* in this case the hypothesis (preAword l) forbids ct1 c = ct2 c = 0. We *)
(* need to kind of reproduce this proof outside this one to ensure we never hit *)
(* this  exceptional case... Can we do better? *)

Lemma preA_sA2B_ghost_inv l gi (g := foldl sA2B_ghost gi l) :
  preAword l ->
  [/\  #N l  + dy1 gi + dy2 gi + ct1 gi + ct2 gi = dy1 g + dy2 g + ct1 g + ct2 g,
       #SE l + dy1 gi + dy2 gi = dy1 g + dy2 g &
       #W l  + dy1 gi + ct2 gi + free gi = dy1 g + ct2 g + free g].
Proof.
rewrite {}/g; elim/last_ind: l => [| l h ihl] /= preAlh=> //.
rewrite !foldl_rcons.
have {ihl} /ihl := preA_rcons _ preAlh.
move: (foldl sA2B_ghost gi l) => c [eN eSE eW].
case: h preAlh => /preAwordP preAlh; rewrite !count_mem_rcons !eqxx /=.
- rewrite !addSn {}eW {}eN {}eSE {preAlh}.
  by case: c => c1 c2 d1 d2 f /=; rewrite !addnS !addSn.
- rewrite !addSn {}eW {}eN {}eSE {preAlh}.
  by case: c => [] [|c1] c2 d1 d2 f /=; rewrite !addnS ?addSn.
- have {preAlh} lt_SE_N : (#SE l < #N l).
    by move: (preAlh (size (rcons l SE))); rewrite take_size !count_mem_rcons.
  have : ct1 c + ct2 c != 0.
    apply: contraL lt_SE_N; rewrite addn_eq0; case/andP=> /eqP e1 /eqP e2.
    have e : #SE l + dy1 gi + dy2 gi = #N l + dy1 gi + dy2 gi + ct1 gi + ct2 gi.
      by rewrite eN e1 e2 !addn0.
    rewrite -leqNgt -(leq_add2r (dy1 gi + dy2 gi)) !addnA e -[X in _ <= X]addnA.
    exact:leq_addr.
  rewrite !addSn {}eW {}eN {}eSE.
  by case: c => [] [|c1] [|c2] d1 d2 f /=; rewrite ?addnS ?addSn.
Qed.

(* We prove that d1 d2 and f are really ghost variables: they do not *)
(*    affect the computation of the data and of c1 and c2, as witnessed by *)
(*    the fact the these coincide with the values of the (ghost-free) *)
(*    function (spipe sA2B) *)

Lemma ghost_sA2B_ghost gi l (g := foldl sA2B_ghost gi l) :
  state_of_ghost g = foldl sA2B (state_of_ghost gi) l.
Proof.
rewrite {}/g; elim: l gi => [|h l ihl] //= gi; rewrite {}ihl; congr foldl.
by case: gi=> c1 c2* {l} /=; case: h => //=; case: c1 => * //; case: c2 => *.
Qed.

(* First fact, still to much bureaucracy *)
Lemma preA_noex l h c : rcons l h \in preAword -> noex h (foldl sA2B c l).
Proof.
rewrite /noex; case: h; rewrite ?orbT // orbF => pAlSE.
have : (#SE l < #N l).
  move/preAwordP/(_ (size (rcons l SE))): pAlSE.
  by rewrite take_size !count_mem_rcons.
pose gi := GState_alt c 0 0 0.
have -> : c = state_of_ghost gi by rewrite {}/gi; case: c=> [] [].
rewrite -ghost_sA2B_ghost.
have {pAlSE}  /(preA_sA2B_ghost_inv gi) := preA_rcons _ pAlSE.
move: (foldl _ _ _) => g.
have <- /= : (ct1 g, ct2 g) = state_of_ghost g by case: g.
rewrite !addn0; move: (dy1 _) => d1; move: (dy2 _) => d2; move: (free _) => f.
case=> eN eSE _; rewrite -negb_and; apply: contraL; case/andP=> /eqP e1 /eqP e2.
have {eN eSE} -> : #SE l = #N l + c.1 + c.2 by rewrite eN e1 e2 !addn0.
by rewrite -leqNgt -addnA leq_addr.
Qed.

Lemma A_final_state l : l \in Aword -> foldl sA2B {|0; 0|} l = {|0; 0|}.
Proof.
move=> Al; pose gi := GState 0 0 0 0 0.
rewrite -{1}[{|0; 0|}]/(state_of_ghost gi) -ghost_sA2B_ghost.
case/AwordP: Al => /(preA_sA2B_ghost_inv gi) /=.
rewrite !addn0; move: (foldl _ _ _) => [] c1 c2 d1 d2 f {gi} /= [-> -> ->] /eqP.
by rewrite -{2}[d1 + _]addn0 -addnA eqn_add2l addn_eq0; case/andP=> /eqP-> /eqP->.
Qed.

Lemma A2BK : {in Aword, cancel A2B B2A}.
Proof. apply: A2BK_; [exact: preA_noex | exact: A_final_state]. Qed.
