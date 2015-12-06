Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice tuple fintype (* finfun finset *).

Require Import extra_seq.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Type step is the three-letter alphabet of the words we want to count.
   The names of the letters reminds how they will be interpreted as
   (the direction of) small step moves on a grid.*)

Inductive step : Type := N | W | Se.

(* Starting boilerplate code: *)

(* Type step has a canonical decidable equality test, is a countable, even finite
   type, thus equipped with a choice function. We obtain these properties, and
   the associated generic notations and theory by expliciting a bijection
   bewteen type step and the finite type 'I_3 of natural numbers {0,1,2}:
   - North (N) is coded by 0
   - West (W) is coded by 1
   - SouthEast (SW) is coded by 2
 *)

Definition ord_of_step (s : step) : 'I_3 :=
  match s with
    |N  => @Ordinal 3 0 (refl_equal true)
    |W  => @Ordinal 3 1 (refl_equal true)
    |Se => @Ordinal 3 2 (refl_equal true)
  end.

Definition step_of_ord (o : 'I_3) : step :=
  match nat_of_ord o with
      |0 => N
      |1 => W
      |_ => Se
  end.

Lemma ord_of_stepK : cancel ord_of_step step_of_ord.
Proof. by case. Qed.

(* Installing (canonical) structures of equality, countable, choice, finite type
   type step, deduced from the bijection. *)

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
Notation "#Se" := (count_mem Se).

(* Sanity check, that we do not use in the sequel. *)
Lemma count_steps_size (w : seq step) : (#N w) + (#W w) + (#Se w) = size w.
Proof.
elim: w => // [[]] l /= <-. rewrite !add0n.
- by rewrite -[RHS]add1n !addnA.
- by rewrite [_ + (1 + _)]addnCA -!addnA add1n.
- by rewrite [_ + (1 + _)]addnCA add1n.
Qed.

(* We consider a family Aword of words on alphabet step. A word w verifies Aword
   iff:
   - for any prefix p of w, #Se p <= #N p
   - #N w = #Se w = #W w

   We also introduce the auxiliary family pAword of words w such that for any
   prefix p of w,  #Se p <= #N p. pAword is stable by prefix.
   By definition, w is in Aword iff:
   - w is in pAword
   - #N w = #Se w = #W w *)


(* In order to define pA as a boolean predicate on words, we quantify over
   prefixes of length smaller that the size of the list. *)
Definition pAword (w : seq step) : bool :=
  [forall n : 'I_(size w).+1, #Se (take n w) <= #N (take n w)].

(* But this quantification is purely technical in fact. *)
Lemma pAwordP w :
  reflect (forall n : nat, #Se (take n w) <= #N (take n w)) (w \in pAword).
Proof.
apply: (iffP forallP) => [/(_ (Ordinal _)) h| ?] n //.
case: (ltnP n (size w).+1) => [| /ltnW/take_oversize->]; first exact: h.
by rewrite -(take_size w); apply: h.
Qed.

Lemma pA_rcons a w : (rcons w a) \in pAword  -> w \in pAword.
Proof.
move/pAwordP=> pAla; apply/forallP=> [] [n ?].
by move: (pAla n); rewrite -cats1 takel_cat.
Qed.

Arguments pA_rcons a {w} _.

Definition Aword (w : seq step) : bool :=
  [&& (pAword w), #N w == #Se w & #Se w == #W w].

Lemma AwordP w :
  reflect [/\ (pAword w), #N w = #Se w & #Se w = #W w] (w \in Aword).
Proof. by apply: (iffP and3P); case=> pAw /eqP-> /eqP->. Qed.

Lemma ApAword l : l \in Aword -> l \in pAword. Proof. by case/and3P. Qed.


(* We consider a family B of words on alphabet step. A word w is in B iff:
   - for any prefix p of w, #W p <= #Se p <= #N p
   - #Se w - #W w = #N w - #Se w

  We also introduce the auxiliary family pBword of words w such that for any
  prefix p of w,  #W p <= #Se p <= #N p. pBword is stable by prefix.
  By definition, w is in Bword iff:
   - w is in pBword
   - #N w = #Se w = #W w

*)

Definition pBword (w : seq step) : bool :=
  [forall n : 'I_(size w).+1, #W (take n w) <= #Se (take n w) <= #N (take n w)].

Lemma pBwordP w :
  reflect (forall n : nat, #W (take n w) <= #Se (take n w) <= #N (take n w))
          (pBword w).
Proof.
apply: (iffP forallP) => [/(_ (Ordinal _)) h| ?] n //.
case: (ltnP n (size w).+1) => [| /ltnW/take_oversize->]; first exact: h.
by rewrite -(take_size w); apply: h.
Qed.

Lemma pBword_rcons l a : (rcons l a) \in pBword  -> pBword l.
Proof.
move/pBwordP=> pBwordla; apply/forallP=> [] [n hn] /=.
by move: (pBwordla n); rewrite -cats1 takel_cat.
Qed.

Definition Bword (w : seq step) : bool :=
  [&& (w \in pBword) & #Se w - #W w == #N w - #Se w].

Lemma BwordP (w : seq step) :
  reflect (w \in pBword /\ #Se w - #W w = #N w - #Se w) (w \in Bword).
Proof.
Proof. by apply: (iffP andP); case=> pAw /eqP->. Qed.

Lemma BpBword l : l \in Bword -> l \in pBword. Proof. by case/andP. Qed.

(* We want to show that for a given n, the number of words of size n that are
   in Aword is the same as the number of words of size n that are in Bword.
   For this purpose, we construct a size-preserving bijection between the
   collection of words in Aword and the collection of words in Bword.

   Intuitively (but we do not verify this formally), words in A (of length 3*k)
   can be generated by taking:
   - a Dyck word d on (N, Se) of lenght 2*k;
   - with k letters W randomly inserted in d.

   Similarly, words in B (or length 3*(k1 + k2) can be generated by taking:
   - a Dyck word d1 on (NSe, W) of lenght 3*k1 (the closing parenthesis is the
   concatenation of letters Se and W);
   - shuffled with a Dyck word d2 on (N, Se) of length 2*k2 (letters can be
   inserted between the adjacent N and Se of d1);
   - with k2 letters N randomly inserted in the resulting entanglement of d1
   and d2.

   An other way to generate words in A is by taking:
   - a Dyck word d1' on (NW, Se) of length 3*k1;
   - shuffled with a Dyck word d2' on (N, Se) of length 2*k2 (letters can be
   inserted between the adjacent N and Se of d1);
   - with k2 letters W randomly inserted in the resulting entanglement of d1
   and d2.

   We construct a function A2B : seq step -> seq step such that if w is an
   Aword, then (A2B w) sends its d1' on a d1, its d2' on a d2 and its remaining
   Ws on Ns. Conversely, we construct a function B2A : seq step -> seq step such
   that if w is a Bword, then (B2A w) sends its d1 on a d1', its d2 on a d2' and
   its remaining Ns on Ws. We show that on Awords, B2A o A2B = id, that on
   Bwords, A2B o B2A = id and that A2B sends Awords on Bwords. Moreover, since
   A2B and B2A preserve the size of their arguments, this shows that Awords of
   size n are in bijection with Bwords of size n, which is enough to conclude.

   Functions A2B and B2A are each defined using an (infinite) automaton, with
   transitions labelled with letters. States are
   labelled with pairs of (natural) numbers, which allows to implement
   the recognition of the prioritized Dyck words. A transition
   function t : state * step -> step * state takes a letter and a
   state as argument, and computes the next state and the letter
   produced. The initial and final state is (0, 0). Given a word w,
   (A2B w) (resp. (B2A w)) is the word produced by the transducer tA2B
   (resp. tB2A) when reading w.
*)

(* Data structure for states of the transducers: a tagged version of nat * nat.*)
Inductive state := State of nat * nat.

Notation "'{|' c1 ; c2 '|}'" := (State (c1, c2)).

(* We coerce type state to nat * nat *)

Coercion nat2_of_state s : (nat * nat) := let: State c := s in c.

(* Boilerplate code to recover the canonical properties of nat * nat :
   decidable equality, choice function, countability. *)

Canonical state_subType := [newType for nat2_of_state].

Definition state_eqMixin := Eval hnf in [eqMixin of state by <:].
Canonical state_eqType := Eval hnf in EqType state state_eqMixin.
Definition state_choiceMixin := [choiceMixin of state by <:].
Canonical state_choiceType :=
  Eval hnf in ChoiceType state state_choiceMixin.
Definition state_countMixin := [countMixin of state by <:].
Canonical state_countType := Eval hnf in CountType state state_countMixin.
Canonical state_subCountType := [subCountType of state].

(* End of the boilerplate code *)

(* Transition function of the transducer tA2B *)
Definition tA2B (c : state) (s : step) : state :=
  match s, c with
    |  W,  {|0    ; c2   |} => {|0    ; c2   |} (* (N,  {|0    ; c2   |}) *) (* _ , _  *)
    |  W,  {|c1.+1; c2   |} => {|c1   ; c2.+1|} (* (Se, {|c1   ; c2.+1|}) *) (* -1, +1 *)
    |  N,  {|c1   ; c2   |} => {|c1.+1; c2   |} (* (N,  {|c1.+1; c2   |}) *) (* +1, _  *)
    |  Se, {|c1   ; c2.+1|} => {|c1   ; c2   |} (* (W,  {|c1   ; c2   |}) *) (* _ , -1 *)
    |  Se, {|c1.+1; 0    |} => {|c1   ; 0    |} (* (Se, {|c1   ; 0    |}) *) (* -1, _  *)
    |  Se, {|0    ; 0    |} => {|0    ; 0    |} (* (N,  {|0    ; 0    |}) *) (* junk *)
  end.

Arguments tA2B c s : simpl never.

(* Transition function of the transducer tB2A *)
Definition tB2A (c : state) (s : step) : state :=
  match s, c with
    | N,  {|0    ; c2   |} => {|0    ; c2   |} (* (W,  {|0    ; c2   |}) *) (* _ , _  *)
    | Se, {|c1   ; c2.+1|} => {|c1.+1; c2   |} (* (W,  {|c1.+1; c2   |}) *) (* +1, -1 *)
    | N,  {|c1.+1; c2   |} => {|c1   ; c2   |} (* (N,  {|c1   ; c2   |}) *) (* -1, _  *)
    | W,  {|c1   ; c2   |} => {|c1   ; c2.+1|} (* (Se, {|c1   ; c2.+1|}) *) (* _ , +1 *)
    | Se, {|c1   ; 0    |} => {|c1.+1; 0    |} (* (Se, {|c1.+1; 0    |}) *) (* +1, _  *)
  end.

Arguments tB2A c s : simpl never.

(* By definition, tA2B is the "converse" of tB2A in the following sense, i.e.
   tA2B reverses both the arrows of tB2A and the status of inputs and outputs *)
(* Lemma tA2BK s1 s2 c1 c2 : tB2A c1 s1 = (s2, c2) -> tA2B c2 s2 = (s1, c1). *)
(* Proof. by case: c1 => [[[|c11] [|c12]]]; case: s1=> /= [] [] <- <-. Qed. *)

(* But there is one degenerated case, which prevents the expected converse
   identity to hold *)
Definition noex  (s : step) (c : state) :=
   [|| (c.1 != 0%N), (c.2 != 0%N) | (s != Se)].

(* Lemma tB2AK s1 s2 c1 c2 : noex s1 c1 -> *)
(*   tA2B c1 s1 = (s2, c2) -> tB2A c2 s2 = (s1, c1). *)
(* Proof. by case: c1 => [[[|c11] [|c12]]]; case: s1 => //= _ [] [] <- <-. Qed. *)


(* A2B (resp.) is defined from tA2B as follows:
   - from a word w and an intial state c, we produce the sequence
     (A2Bstates c w) (resp.  (A2Bstates c w)) of states scanned when it is read
     by tA2B (resp. tB2A);
   - crucially, given two states cf and ci, there is a unique possible letter
     (cB2A ci cf) (resp. cA2B) read by a transition tB2A (resp. tA2B) from
      ci to cf, except if ci = cf = (0, 0), in which case we we consider that
     the input letter wasn't Se)
   - we then produce the sequence of corresponding letters, using cA2B
     (resp. cB2A).
   - A2B takes (0, 0) as initial state.
*)


Definition sA2B c s := tA2B c s.

Definition A2Bstates (c : state) (ls : seq step) : seq state := scanl sA2B c ls.

Definition cB2A (ci cf : state) : step :=
  let: {|cf1; cf2|} := cf in
  let: {|ci1; ci2|} := ci in
  if [&& cf1 == 0, ci1 == 0 & (cf2 == ci2)] then N
  else if (ci1 == cf1.+1) && (cf2 == ci2.+1) then Se
  else if (cf1 == ci1.+1) && (cf2 == ci2) then N
  else if (cf1 == ci1) && (ci2 == cf2.+1) then W
  else Se.

Definition A2B_from (c : state) (ls : seq step) : seq step :=
  pairmap cB2A c (A2Bstates c ls).

Definition A2B := A2B_from {|0; 0|}.

(* B2A is defined in a similar manner as A2B (with no degenerated case). *)

Definition sB2A nn s := tB2A nn s.

Definition B2Astates  (c : state) (ls : seq step) : seq state :=
  scanl sB2A c ls.

Definition cA2B (ci cf : state) : step :=
  let: {|cf1; cf2|} := cf in
  let: {|ci1; ci2|} := ci in
  if [&& cf1 == 0, ci1 == 0 & (cf2 == ci2)] then W
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then W
  else if (ci1 == cf1.+1) && (cf2 == ci2) then N
  else if (cf2 == ci2.+1) && (cf2 == ci2) then Se
  else if (cf1 == ci1.+1) && (cf2 == 0) && (ci2 == 0) then Se
  else Se (* junk *).


Definition B2A_from (c : state) (ls : seq step) : seq step :=
  pairmap cA2B c (B2Astates c ls).

Definition B2A (ls : seq step) := rev (B2A_from {|0; 0|} (rev ls)).

(* A few computations to see the translation at work: *)

Eval compute in A2B [:: N; W; Se]. (* [:: N; Se; W] *)
Eval compute in A2B [:: N; Se; W]. (* [:: N; Se; N] *)
Eval compute in A2B [:: W; N; Se]. (* [:: N; N; Se] *)


Eval compute in B2A [:: N; Se; W]. (* [:: N; W; Se] *)
Eval compute in B2A [:: N; Se; N]. (* [:: N; Se; W] *)
Eval compute in B2A [:: N; N; Se]. (* [:: W; N; Se] *)


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
  |W,  GState c1.+1 c2    d1 d2 f  =>  (Se, GState c1    c2.+1  d1    d2    f   )
  |N,  GState c1    c2    d1 d2 f  =>  (N,  GState c1.+1 c2     d1    d2    f   )
  |Se, GState c1    c2.+1 d1 d2 f  =>  (W,  GState c1    c2     d1.+1 d2    f   )
  |Se, GState c1.+1 0     d1 d2 f  =>  (Se, GState c1    0      d1    d2.+1 f   )
  |Se, GState 0     0     d1 d2 f  =>  (N,  GState 0     0      d1    d2    f   )
end.

Definition tA2B_ghost := nosimpl tA2B_ghost_.

Definition sA2B_ghost nn s := snd (tA2B_ghost nn s).

Definition cB2A_ghost gf gi :=
  let: (GState ci1 ci2 _ _ _) := gi in
  let: (GState cf1 cf2 _ _ _) := gf in
  if [&& ci1 == 0, cf1 == 0 & (ci2 == cf2)] then N
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then Se
  else if (ci1 == cf1.+1) && (ci2 == cf2) then N
  else if (ci1 == cf1) && (cf2 == ci2.+1) then W
  else Se.

Definition A2Bstates_ghost (g : ghost_state) (ls : seq step) : seq ghost_state :=
  scanl sA2B_ghost g ls.

Definition A2B_ghost_from (g : ghost_state) (ls : seq step) : seq step :=
  pairmap cB2A_ghost g (A2Bstates_ghost g ls).

(* Complete invariant. By brute force case analysis excepy for the only *)
(* interesting case of the (tail) induction on l is, i.e. when it ends with Se:*)
(* in this case the hypothesis (pAword l) forbids ct1 c = ct2 c = 0. We *)
(* need to kind of reproduce this proof outside this one to ensure we never hit*)
(* this  exceptional case... Can we do better? *)

Lemma pA_sA2B_ghost_inv l gi (g := foldl sA2B_ghost gi l) :
  l \in pAword ->
  [/\  #N l  + dy1 gi + dy2 gi + ct1 gi + ct2 gi = dy1 g + dy2 g + ct1 g + ct2 g,
       #Se l + dy1 gi + dy2 gi = dy1 g + dy2 g &
       #W l  + dy1 gi + ct2 gi + free gi = dy1 g + ct2 g + free g].
Proof.
rewrite {}/g; elim/last_ind: l => [| l h ihl] /= pAlh=> //; rewrite !foldl_rcons.
have {ihl} /ihl := pA_rcons _ pAlh.
move: (foldl sA2B_ghost gi l) => c [eN eSe eW].
case: h pAlh => pAlh; rewrite !count_mem_rcons !eqxx /=.
- by rewrite !addSn {}eW {}eN {}eSe; case: c => * /=; split; ring.
- by rewrite !addSn {}eW {}eN {}eSe; case: c => [] [|c1] * /=; split; ring.
- suff {eW} : ct1 c + ct2 c != 0.
    rewrite !addSn {}eW {}eN {}eSe; case: c => [] [|?] [|?] * //=; split; ring.
  (* have {pAlh} /contraL : #Se l < #N l := pA_rconsSe pAlh. *)
  (* apply; rewrite addn_eq0; case/andP=> /eqP e1 /eqP e2. *)
  (* suff /eqP-> : #Se l == #N l + (ct1 gi + ct2 gi) by rewrite -leqNgt leq_addr. *)
  (* by rewrite -(eqn_add2r (dy1 gi + dy2 gi)) addnAC !addnA eN eSe e1 e2 !addn0. *)
admit.
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
move: (foldl _ _ _) => [] c1 c2 d1 d2 f /=; rewrite !addn0; case=> /eqP eN eSe _.
apply: contraL eN => /andP [/eqP-> /eqP->]; rewrite !addn0 -{}eSe.
(* by apply: contraL (pA_rconsSe pA); move/eqP<-; rewrite -leqNgt -addnA leq_addr.*)
admit.
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
       #Se (A2B_ghost_from gi l) + dy1 gi + dy2 gi + ct2 gi =
         dy1 g + dy2 g + ct2 g &
       #W (A2B_ghost_from gi l)  + dy1 gi = dy1 g].
Proof.
rewrite {}/g; elim/last_ind: l => [| l h ihl] /= pAlh=> //.
rewrite A2B_ghost_rcons !foldl_rcons.
have {ihl} /ihl := pA_rcons _ pAlh.
set lr := A2B_ghost_from gi l.
have := pA_noex_ghost gi pAlh.
move: (foldl sA2B_ghost gi l) => g noex [eN eSe eW].
rewrite cB2A_sA2B_ghost.
case: h noex pAlh => [_ | _ | nx] /pAwordP pAlh; rewrite !count_cat /= addn0.
- have -> : (tA2B_ghost g N).1 = N by case: g {eN eSe eW} => [] [] [|?] [|?].
  have-> /=: sA2B_ghost g N = GState (ct1 g).+1 (ct2 g) (dy1 g) (dy2 g) (free g).
    by case: g {eN eSe eW}.
  by rewrite !addn0 addn1 addnS !addSn eN eSe eW.
- case: g eN eSe eW => [] [|c1] c2 d1 d2 f /=; rewrite !addn0 addn1 => eN eSe eW.
  + by rewrite addnS !addSn eN eW eSe.
  + by rewrite eN eW !addnS !addSn eSe.
- case: g eN eSe eW nx => [] [|c1] [|c2] ? ? ? //; rewrite !addn0 => eN eSe eW _.
  + by rewrite addn1 !addSn eN eSe eW addnS !addSn.
  + by rewrite addn1 addnS !addSn eN eSe eW addnS !addSn.
  + by rewrite addn1 addnS !addSn eN eSe eW !addnS !addSn.
Qed.

Lemma take_A2B n l : A2B (take n l) = take n (A2B l).
Proof. by rewrite /A2B /A2B_from /A2Bstates -take_scanl -take_pairmap. Qed.

Lemma pB_A2B_pA l : l \in pAword -> A2B l \in pBword.
Proof.
move/pAwordP=> pAl; apply/pBwordP=> n.
have : take n l \in pAword by apply/pAwordP=> m; rewrite take_take.
pose gi := g0; move/(pA_A2B_ghost_inv gi) => /=.
rewrite !addn0 -[X in A2B_ghost_from X _]/(GState_alt {|0; 0|} 0 0 0).
rewrite ghost_A2B_ghost -/A2B take_A2B; case=> -> -> ->.
rewrite -addnA leq_addr /= addnA. set d := dy1 _ + dy2 _.
by rewrite -[d + _ + _]addnAC -addnA leq_addr.
Qed.

Theorem B_A2B_A l : l \in Aword -> A2B l \in Bword.
case/AwordP => pAl eNSe eSeW.
rewrite -topredE /= /Bword pB_A2B_pA //=.
pose gi := g0; pose rl := foldl sA2B_ghost gi l.
have /and3P [/eqP ec1 /eqP ec2 /eqP edf]:
  [&& ct1 rl == 0, ct2 rl == 0 & dy2 rl == free rl].
  move/(pA_sA2B_ghost_inv gi): (pAl); rewrite /= !addn0 -/rl; case=> eN eSe eW.
  move: eNSe; rewrite eN -addnA eSe; move/(canRL (addKn _)); rewrite subnn.
  move/eqP; rewrite addn_eq0; case/andP=> -> ct20; rewrite (eqP ct20) /=.
  by move/eqP: eSeW; rewrite eW (eqP ct20) addn0 eSe eqn_add2l.
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
apply/eqP; rewrite eqn_leq.
have -> : #|Btuple| <= #|Atuple|.
  apply: (@leq_trans #|[seq (B2At w) | w in Atuple]|); last exact: leq_image_card.
  have imB2A w : Btuple w -> Atuple (B2At w). admit.
  admit.
have /can_in_inj /image_injP /eqP : {in Atuple, cancel A2Bt B2At}. admit.
have /can_in_inj /image_injP : {in Btuple, cancel B2At A2Bt}. admit.

Search _ (#|_| <= #|_|).
leq_image_card
   forall (T T' : finType) (f : T -> T') (A : pred T),
   #|[seq f x | x in A]| <= #|A|

Search _ card.
(* we still need to prove this one! *)
Admitted.

End CardinalsEquality.