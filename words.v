Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice tuple fintype (* finfun finset *).

Require Import extra_seq.


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

(* We consider a family A of words on alphabet step. A word w is in A iff:
   - for any prefix p of w, #SE p <= #N p
   - #N w = #SE w = #W w
   Intuitively (we do not verify this formally), words in A can be generated
   by taking:
   - a Dyck word d on (N, SE) of lenght 2*k;
   - with k letters W randomly inserted in d.
 *)

Definition pAword (w : seq step) : bool :=
  [forall n : 'I_(size w).+1, #SE (take n w) <= #N (take n w)].

Lemma pAwordP w :
  reflect (forall n : nat, #SE (take n w) <= #N (take n w)) (w \in pAword).
Proof.
apply: (iffP forallP) => h n //; case: (ltnP n (size w).+1) => [ltnsl | /ltnW ?].
  by have := h (Ordinal ltnsl).
by have := h (ord_max); rewrite take_size take_oversize.
Qed.

Lemma pA_rcons a w : (rcons w a) \in pAword  -> w \in pAword.
Proof.
move/pAwordP=> pAwordla; apply/forallP=> [] [n hn] /=.
by move: (pAwordla n); rewrite -cats1 takel_cat.
Qed.

Arguments pA_rcons a {w} _.

Definition Aword (w : seq step) : bool :=
  [&& (pAword w), #N w == #SE w & #SE w == #W w].

Lemma AwordP w :
  reflect [/\ (pAword w), #N w = #SE w & #SE w = #W w] (w \in Aword).
Proof. by apply: (iffP and3P); case=> pAw /eqP-> /eqP->. Qed.

Lemma ApAword l : l \in Aword -> l \in pAword. Proof. by case/and3P. Qed.


(* We consider a family B of words on alphabet step. A word w is in B iff:
   - for any prefix p of w, #W p <= #SE p <= #N p
   - #SE w - #W w = #N w - #SE w
  Intuitively (we do not verify this formally), words in B can be generated
  by taking:
   - a Dyck word d1 on (N, SEW) of lenght 3*k1 (the closing parenthesis is the
   concatenation of letters SE and W);
   - shuffled with a Dyck word d2 on (N, SE) of length 2*k2
   - with k2 letters N randomly inserted in the resulting entanglement of d1
  and d2.
*)

Definition pBword (w : seq step) : bool :=
  [forall n : 'I_(size w).+1, #W (take n w) <= #SE (take n w) <= #N (take n w)].

Lemma pBwordP w :
  reflect (forall n : nat, #W (take n w) <= #SE (take n w) <= #N (take n w))
          (pBword w).
Proof.
apply: (iffP forallP) => h n //; case: (ltnP n (size w).+1) => [ltnsl | /ltnW ?].
  by have := h (Ordinal ltnsl).
by have := h (ord_max);  rewrite take_size take_oversize.
Qed.

Lemma pBword_rcons l a : (rcons l a) \in pBword  -> pBword l.
Proof.
move/pBwordP=> pBwordla; apply/forallP=> [] [n hn] /=.
by move: (pBwordla n); rewrite -cats1 takel_cat.
Qed.

Definition Bword (w : seq step) : bool :=
  [&& (w \in pBword) & #SE w - #W w == #N w - #SE w].

Lemma BwordP (w : seq step) :
  reflect (w \in pBword /\ #SE w - #W w = #N w - #SE w) (w \in Bword).
Proof.
Proof. by apply: (iffP andP); case=> pAw /eqP->. Qed.

Lemma BpBword l : l \in Bword -> l \in pBword. Proof. by case/andP. Qed.

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


Definition A2Bstates (c : state) (ls : seq step) : seq state := scanl sA2B c ls.

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



(* End: This should go to the MathComp library... *)

Lemma sB2A_round c h : sB2A (sA2B c h) (cB2A c (sA2B c h)) = c.
Proof.
by case: c => [] [] [|?] [|?]; case: h => //=; rewrite ?eqxx ?andbF //= ltn_eqF.
Qed.

Lemma sA2B_round c h : sA2B (sB2A c h) (cA2B c (sB2A c h)) = c.
Proof.
case: c => [] [] [|?] [|?]; case: h => //=; rewrite ?eqxx ?andbF //=.
- by rewrite eq_sym ltn_eqF.
- by rewrite ltn_eqF.
- by rewrite ltn_eqF.
- by rewrite ltn_eqF //= eq_sym ltn_eqF.
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

Lemma cB2A_round d h :
  cB2A (sB2A d h) (sA2B (sB2A d h) (cA2B d (sB2A d h))) = h.
Proof.
case: d => [] [] [|c1] [|c2]; case: h => //=;
  rewrite ?eqxx /sA2B /tA2B /= ?eqxx ?andbF
                /sB2A /tB2A /= ?eqxx ?andbF //.
- by rewrite eq_sym ltn_eqF //= ltn_eqF // eqxx.
- by rewrite ltn_eqF //= !eqxx !ltn_eqF.
- by rewrite ltn_eqF //= !eqxx /= !ltn_eqF.
- by rewrite ltn_eqF //= if_same /= !eqxx !ltn_eqF.
Qed.

Section FirstStep.

(* We leave as (temporary) hypotheses the facts that requires introducing
   ghost variables: *)


Hypothesis pA_noex : forall l h c,
   rcons l h \in pAword -> noex h (foldl sA2B c l).

Lemma revA2B_fromK l c : l \in pAword ->
    rev (B2A_from (foldl sA2B c l) (rev (A2B_from c l))) = l.
Proof.
elim/last_ind: l c => [| l h ihl c pAlh] //=.
set cf := foldl _ _ _.
rewrite /A2B_from /A2Bstates scanl_rcons -cats1 pairmap_cat rev_cat /=.
set s := cB2A _ _.
rewrite -/(A2B_from c l) /B2A_from /= rev_cons; congr rcons.
  suff {ihl} -> : sB2A cf s = foldl sA2B c l by apply/ihl/(pA_rcons h).
  rewrite {}/cf {}/s last_scanl foldl_rcons; exact: sB2A_round.
rewrite {}/cf {}/s foldl_rcons last_scanl; apply: cA2B_round; exact: pA_noex.
Qed.

Lemma revB2A_fromK l c :
    A2B_from (foldl sB2A c l) (rev (B2A_from c l)) = rev l.
Proof.
elim/last_ind: l c => [| l h ihl c] //=.
set cf := foldl _ _ _.
rewrite /B2A_from /B2Astates scanl_rcons -cats1 pairmap_cat rev_cat /=.
set s := cA2B (last _ _)  _.
rewrite -/(B2A_from c l) /A2B_from /= rev_rcons; congr cons; last first.
  suff {ihl} -> : sA2B cf s = foldl sB2A c l by apply/ihl.
  rewrite {}/cf {}/s last_scanl foldl_rcons; exact: sA2B_round.
by rewrite {}/cf {}/s foldl_rcons last_scanl; apply: cB2A_round.
Qed.

Hypothesis A_final_state : forall l,
  l \in Aword -> foldl sA2B {|0; 0|} l = {|0; 0|}.

Lemma A2BK_ : {in Aword, cancel A2B B2A}.
Proof.
move=> l /= Al; rewrite /B2A -(A_final_state Al); apply: revA2B_fromK.
exact: ApAword.
Qed.

Hypothesis B_final_state : forall l,
  l \in Bword -> foldl sB2A {|0; 0|} (rev l) = {|0; 0|}.

Lemma B2AK_ : {in Bword, cancel B2A A2B}.
Proof.
by move=> l /= Bl; rewrite /A2B -(B_final_state Bl) /B2A revB2A_fromK ?revK.
Qed.

End FirstStep.


(* Now we prove the two remaining facts about words in A, plus the important
  missing property of A2B : that its image is included in Bword *)


Record ghost_state :=
  GState {ct1: nat; ct2: nat; dy1 : nat; dy2 : nat; free : nat}.

Definition GState_alt (c : state) (d1 d2 f : nat) : ghost_state :=
  GState c.1 c.2 d1 d2 f.

Let g0 := GState 0 0 0 0 0.

Definition state_of_ghost (g : ghost_state) :=
  let: GState c1 c2 _ _ _ := g in State (c1, c2).

(* Last case is junk *)
Definition tA2B_ghost_ (g : ghost_state)  (s : step) : step * ghost_state :=
match s, g with
  |W,  GState 0     c2    d1 d2 f  =>  (N,  GState 0     c2     d1    d2    f.+1)
  |W,  GState c1.+1 c2    d1 d2 f  =>  (SE, GState c1    c2.+1  d1    d2    f   )
  |N,  GState c1    c2    d1 d2 f  =>  (N,  GState c1.+1 c2     d1    d2    f   )
  |SE, GState c1    c2.+1 d1 d2 f  =>  (W,  GState c1    c2     d1.+1 d2    f   )
  |SE, GState c1.+1 0     d1 d2 f  =>  (SE, GState c1    0      d1    d2.+1 f   )
  |SE, GState 0     0     d1 d2 f  =>  (N,  GState 0     0      d1    d2    f   )
end.

Definition tA2B_ghost := nosimpl tA2B_ghost_.

Definition sA2B_ghost nn s := snd (tA2B_ghost nn s).

Definition cB2A_ghost gf gi :=
  let: (GState ci1 ci2 _ _ _) := gi in
  let: (GState cf1 cf2 _ _ _) := gf in
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
(* interesting case of the (tail) induction on l is, i.e. when it ends with SE:*)
(* in this case the hypothesis (pAword l) forbids ct1 c = ct2 c = 0. We *)
(* need to kind of reproduce this proof outside this one to ensure we never hit*)
(* this  exceptional case... Can we do better? *)

Lemma pA_rconsSE l : rcons l SE \in pAword ->  #SE l < #N l.
Proof.
by move/pAwordP/(_ (size (rcons l SE))); rewrite take_size !count_mem_rcons eqxx.
Qed.

Lemma pA_sA2B_ghost_inv l gi (g := foldl sA2B_ghost gi l) :
  l \in pAword ->
  [/\  #N l  + dy1 gi + dy2 gi + ct1 gi + ct2 gi = dy1 g + dy2 g + ct1 g + ct2 g,
       #SE l + dy1 gi + dy2 gi = dy1 g + dy2 g &
       #W l  + dy1 gi + ct2 gi + free gi = dy1 g + ct2 g + free g].
Proof.
rewrite {}/g; elim/last_ind: l => [| l h ihl] /= pAlh=> //; rewrite !foldl_rcons.
have {ihl} /ihl := pA_rcons _ pAlh.
move: (foldl sA2B_ghost gi l) => c [eN eSE eW].
case: h pAlh => pAlh; rewrite !count_mem_rcons !eqxx /=.
- by rewrite !addSn {}eW {}eN {}eSE; case: c => * /=; split; ring.
- by rewrite !addSn {}eW {}eN {}eSE; case: c => [] [|c1] * /=; split; ring.
- suff {eW} : ct1 c + ct2 c != 0.
    rewrite !addSn {}eW {}eN {}eSE; case: c => [] [|?] [|?] * //=; split; ring.
  have {pAlh} /contraL : #SE l < #N l := pA_rconsSE pAlh.
  apply; rewrite addn_eq0; case/andP=> /eqP e1 /eqP e2.
  suff /eqP-> : #SE l == #N l + (ct1 gi + ct2 gi) by rewrite -leqNgt leq_addr.
  by rewrite -(eqn_add2r (dy1 gi + dy2 gi)) addnAC !addnA eN eSE e1 e2 !addn0.
Qed.

(* We prove that d1 d2 and f are really ghost variables: they do not *)
(*    affect the computation of the data and of c1 and c2, as witnessed by *)
(*    the fact these coincide with the values of the (ghost-free) *)
(*    function (spipe sA2B) *)

Lemma ghost_foldsA2B_ghost c d1 d2 f l (gi := GState_alt c d1 d2 f) :
  state_of_ghost (foldl sA2B_ghost gi l) = foldl sA2B c l.
Proof.
have -> : c = state_of_ghost gi by rewrite {}/gi; case: c=> [] [].
elim: l gi => [|h l ihl] //= gi; rewrite {}ihl; congr foldl.
by case: gi=> c1 c2* {l} /=; case: h => //=; case: c1 => * //; case: c2 => *.
Qed.

Lemma pA_noex l h c : rcons l h \in pAword -> noex h (foldl sA2B c l).
Proof.
rewrite /noex; case: h; rewrite ?orbT // orbF -negb_and => pA.
rewrite -(ghost_foldsA2B_ghost _ 0 0 0); set gi := GState_alt _ _ _ _.
have /(pA_sA2B_ghost_inv gi) := pA_rcons _ pA.
move: (foldl _ _ _) => [] c1 c2 d1 d2 f /=; rewrite !addn0; case=> /eqP eN eSE _.
apply: contraL eN => /andP [/eqP-> /eqP->]; rewrite !addn0 -{}eSE.
by apply: contraL (pA_rconsSE pA); move/eqP<-; rewrite -leqNgt -addnA leq_addr.
Qed.

Lemma A_final_state l : l \in Aword -> foldl sA2B {|0; 0|} l = {|0; 0|}.
Proof.
case/AwordP=> /(pA_sA2B_ghost_inv g0); rewrite -(ghost_foldsA2B_ghost _ 0 0 0) /=.
rewrite !addn0; move: (foldl _ _ _) => [] c1 c2 d1 d2 f /= [-> -> ->].
rewrite -addnA addnC; move/(canRL (addnK _)); rewrite subnn.
by case: c1 => [|?] //; case: c2.
Qed.

Theorem A2BK : {in Aword, cancel A2B B2A}.
Proof. apply: A2BK_; [exact: pA_noex | exact: A_final_state]. Qed.

Lemma cB2A_sA2B d s : cB2A d (sA2B d s) = fst (tA2B d s).
Proof.
by case: d => [] [] [|?] [|?]; case: s; rewrite /= ?eqxx ?andbF //= ?ltn_eqF.
Qed.

Lemma cB2A_sA2B_ghost d s : cB2A_ghost d (sA2B_ghost d s) = fst (tA2B_ghost d s).
Proof.
by case: d => [] [] [|?] [|?] *; case: s; rewrite /= ?eqxx ?andbF /= ?ltn_eqF.
Qed.


Lemma ghost_sA2B_ghost g s :
  sA2B (state_of_ghost g) s = state_of_ghost (sA2B_ghost g s).
Proof.
rewrite /sA2B /sA2B_ghost /state_of_ghost.
case: g => [] c1 c2 d1 d2 f; case: s => //.
- by case: c1.
- by case: c1=> *; case: c2.
Qed.

Lemma ghost_cB2A_ghost g1 g2 :
  cB2A_ghost g1 g2 = cB2A (state_of_ghost g1) (state_of_ghost g2).
Proof.
rewrite /cB2A /cB2A_ghost /state_of_ghost.
by case: g1 => [] c11 c12 d11 d12 f1; case: g2 => [] c21 c22 d21 d22 f2.
Qed.

Lemma ghost_A2B_ghost l c d1 d2 f (gi := GState_alt c d1 d2 f) :
  A2B_ghost_from gi l = A2B_from c l.
Proof.
have -> : c = state_of_ghost gi by rewrite {}/gi; case: c=> [] [].
elim: l gi => [|h sl ihl] //= gi {d1 d2 f c}.
rewrite /A2B_ghost_from /= -/(A2B_ghost_from _ _).
by rewrite /A2B_from /= -/(A2B_from _ _) ghost_sA2B_ghost ihl ghost_cB2A_ghost.
Qed.

Lemma A2B_rcons l h : A2B (rcons l h) =
  A2B l ++ [:: cB2A (foldl sA2B {|0; 0|} l) (foldl sA2B {|0; 0|} (rcons l h))].
Proof.
rewrite /A2B /A2B_from /A2Bstates scanl_rcons -cats1 pairmap_cat.
by rewrite -[pairmap cB2A {|0; 0|} _]/(A2B l) last_scanl /= cats1.
Qed.

Lemma A2B_ghost_rcons g l h : A2B_ghost_from g (rcons l h) =
  A2B_ghost_from g l ++
  [:: cB2A_ghost (foldl sA2B_ghost g l) (foldl sA2B_ghost g (rcons l h))].
Proof.
rewrite /A2B_ghost_from /A2Bstates_ghost scanl_rcons -cats1 pairmap_cat.
by rewrite -[pairmap cB2A_ghost g _]/(A2B_ghost_from g l) last_scanl /= cats1.
Qed.

Lemma pA_noex_ghost l h g : rcons l h \in pAword ->
  noex h (state_of_ghost (foldl sA2B_ghost g l)).
Proof. Print GState.
have -> : g = GState_alt {|ct1 g; ct2 g|} (dy1 g) (dy2 g) (free g) by case: g.
rewrite ghost_foldsA2B_ghost; exact: pA_noex.
Qed.

Lemma pA_A2B_ghost_inv l gi (g := foldl sA2B_ghost gi l) :
  l \in pAword ->
  [/\  #N (A2B_ghost_from gi l) + dy1 gi + dy2 gi + ct1 gi + ct2 gi + free gi =
         dy1 g + dy2 g + ct1 g + ct2 g + free g,
       #SE (A2B_ghost_from gi l) + dy1 gi + dy2 gi + ct2 gi =
         dy1 g + dy2 g + ct2 g &
       #W (A2B_ghost_from gi l)  + dy1 gi = dy1 g].
Proof.
rewrite {}/g; elim/last_ind: l => [| l h ihl] /= pAlh=> //.
rewrite A2B_ghost_rcons !foldl_rcons.
have {ihl} /ihl := pA_rcons _ pAlh.
set lr := A2B_ghost_from gi l.
have := pA_noex_ghost gi pAlh.
move: (foldl sA2B_ghost gi l) => g noex [eN eSE eW].
rewrite cB2A_sA2B_ghost.
case: h noex pAlh => [_ | _ | nx] /pAwordP pAlh; rewrite !count_cat /= addn0.
- have -> : (tA2B_ghost g N).1 = N by case: g {eN eSE eW} => [] [] [|?] [|?].
  have-> /=: sA2B_ghost g N = GState (ct1 g).+1 (ct2 g) (dy1 g) (dy2 g) (free g).
    by case: g {eN eSE eW}.
  by rewrite !addn0 addn1 addnS !addSn eN eSE eW.
- case: g eN eSE eW => [] [|c1] c2 d1 d2 f /=; rewrite !addn0 addn1 => eN eSE eW.
  + by rewrite addnS !addSn eN eW eSE.
  + by rewrite eN eW !addnS !addSn eSE.
- case: g eN eSE eW nx => [] [|c1] [|c2] ? ? ? //; rewrite !addn0 => eN eSE eW _.
  + by rewrite addn1 !addSn eN eSE eW addnS !addSn.
  + by rewrite addn1 addnS !addSn eN eSE eW addnS !addSn.
  + by rewrite addn1 addnS !addSn eN eSE eW !addnS !addSn.
Qed.

Lemma take_A2B n l : A2B (take n l) = take n (A2B l).
Proof. by rewrite /A2B /A2B_from /A2Bstates -take_scanl -take_pairmap. Qed.

Lemma pB_A2B_pA l : l \in pAword -> A2B l \in pBword.
Proof.
move/pAwordP=> pAl; apply/pBwordP=> n.
have : take n l \in pAword by apply/pAwordP=> m; rewrite take_take.
pose gi := GState 0 0 0 0 0; move/(pA_A2B_ghost_inv gi) => /=.
rewrite !addn0 -[X in A2B_ghost_from X _]/(GState_alt {|0; 0|} 0 0 0).
rewrite ghost_A2B_ghost -/A2B take_A2B; case=> -> -> ->.
rewrite -addnA leq_addr /= addnA. set d := dy1 _ + dy2 _.
by rewrite -[d + _ + _]addnAC -addnA leq_addr.
Qed.

Theorem B_A2B_A l : l \in Aword -> A2B l \in Bword.
case/AwordP => pAl eNSE eSEW.
rewrite -topredE /= /Bword pB_A2B_pA //=.
pose gi := GState 0 0 0 0 0; pose rl := foldl sA2B_ghost gi l.
have /and3P [/eqP ec1 /eqP ec2 /eqP edf]:
  [&& ct1 rl == 0, ct2 rl == 0 & dy2 rl == free rl].
  move/(pA_sA2B_ghost_inv gi): (pAl); rewrite /= !addn0 -/rl; case=> eN eSE eW.
  move: eNSE; rewrite eN -addnA eSE; move/(canRL (addKn _)); rewrite subnn.
  move/eqP; rewrite addn_eq0; case/andP=> -> ct20; rewrite (eqP ct20) /=.
  by move/eqP: eSEW; rewrite eW (eqP ct20) addn0 eSE eqn_add2l.
move/(pA_A2B_ghost_inv gi): pAl => /=; rewrite -/rl ec1 ec2 edf !addn0.
rewrite -[X in A2B_ghost_from X _]/(GState_alt {|0; 0|} 0 0 0) ghost_A2B_ghost.
by case=> -> -> ->; rewrite addKn -{2}[dy1 _ + _]addn0 subnDl subn0.
Qed.

Lemma sizeA2B w : size (A2B w) = size w.
Proof. by rewrite /A2B /A2B_from /A2Bstates size_pairmap size_scanl. Qed.

Lemma sizeB2A w : size (B2A w) = size w.
Proof.
by rewrite /B2A /B2A_from /B2Astates size_rev size_pairmap size_scanl size_rev.
Qed.

Section CardinalsEquality.

Variable n : nat.

Definition Atuple : pred (n.-tuple step) := [pred w : n.-tuple step | Aword w].

Definition Btuple : pred (n.-tuple step) := [pred w : n.-tuple step | Bword w].

Corollary AB_eq_card : #|Atuple| = #|Btuple|.
Proof.
have sizeA2Bt (w : n.-tuple step) : size (A2B w) == n by rewrite sizeA2B size_tuple.
have sizeB2At (w : n.-tuple step) : size (B2A w) == n by rewrite sizeB2A size_tuple.
pose A2Bt (w : n.-tuple step) : n.-tuple step := Tuple (sizeA2Bt w).
pose B2At (w : n.-tuple step) : n.-tuple step := Tuple (sizeB2At w).
have imB2A w : Btuple w -> Atuple (B2At w). admit.
have /can_in_inj /image_injP : {in Atuple, cancel A2Bt B2At}. admit.
have /can_in_inj /image_injP : {in Atuple, cancel A2Bt B2At}. admit.
(* we still need to prove this one! *)
Admitted.

End CardinalsEquality.