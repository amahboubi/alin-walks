Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice tuple fintype (* finfun finset *).

Require Import extra_seq.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Type letter is the three-letter alphabet of the words we want to count.
   The names of the letters reminds how they will be interpreted as
   (the direction of) small letter moves on a grid.*)

Inductive letter : Type := N | W | Se.

(* Starting boilerplate code: *)

(* Type letter has a canonical decidable equality test, is a countable, even finite
   type, thus equipped with a choice function. We obtain these properties, and
   the associated generic notations and theory by expliciting a bijection
   bewteen type letter and the finite type 'I_3 of natural numbers {0,1,2}:
   - North (N) is coded by 0
   - West (W) is coded by 1
   - SouthEast (SW) is coded by 2
 *)

Definition ord_of_letter (l : letter) : 'I_3 :=
  match l with
    |N  => @Ordinal 3 0 (refl_equal true)
    |W  => @Ordinal 3 1 (refl_equal true)
    |Se => @Ordinal 3 2 (refl_equal true)
  end.

Definition letter_of_ord (o : 'I_3) : letter :=
  match nat_of_ord o with
      |0 => N
      |1 => W
      |_ => Se
  end.

Lemma ord_of_letterK : cancel ord_of_letter letter_of_ord.
Proof. by case. Qed.

(* Installing (canonical) structures of equality, countable, choice, finite type
   type letter, deduced from the bijection. *)

Definition letter_eqMixin := CanEqMixin ord_of_letterK.
Canonical  letter_eqType  := EqType letter letter_eqMixin.

Definition letter_choiceMixin := CanChoiceMixin ord_of_letterK.
Canonical  letter_choiceType  := ChoiceType letter letter_choiceMixin.


Definition letter_countMixin := CanCountMixin ord_of_letterK.
Canonical  letter_countType  := CountType letter letter_countMixin.

Definition letter_finMixin   := CanFinMixin ord_of_letterK.
Canonical  letter_finType    := FinType letter letter_finMixin.

(* End of boilerplate code *)


(* Boolean predicates characterizing each nature of letter *)
(* (#N w) is the number of occurrences of N in word w, etc. *)

Notation "#N" := (count_mem N).
Notation "#W" := (count_mem W).
Notation "#Se" := (count_mem Se).

(* Sanity check, that we do not use in the sequel. *)
Lemma count_letters_size (w : seq letter) : (#N w) + (#W w) + (#Se w) = size w.
Proof.
elim: w => // [[]] l /= <-. rewrite !add0n.
- by rewrite -[RHS]add1n !addnA.
- by rewrite [_ + (1 + _)]addnCA -!addnA add1n.
- by rewrite [_ + (1 + _)]addnCA add1n.
Qed.

(* We consider a family Aword of words on alphabet letter. A word w verifies Aword
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
Definition pAword (w : seq letter) : bool :=
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

Lemma pA_rconsSe w :  rcons w Se \in pAword -> #Se w < #N w.
Proof.
move/pAwordP/(_ (size w).+1); rewrite -(size_rcons w Se) take_size.
by rewrite !count_mem_rcons eqxx.
Qed.

Arguments pA_rcons a {w} _.

Definition Aword (w : seq letter) : bool :=
  [&& (pAword w), #N w == #Se w & #Se w == #W w].

Lemma AwordP w :
  reflect [/\ (pAword w), #N w = #Se w & #Se w = #W w] (w \in Aword).
Proof. by apply: (iffP and3P); case=> pAw /eqP-> /eqP->. Qed.

Lemma ApAword l : l \in Aword -> l \in pAword. Proof. by case/and3P. Qed.


(* We consider a family B of words on alphabet letter. A word w is in B iff:
   - for any prefix p of w, #W p <= #Se p <= #N p
   - #Se w - #W w = #N w - #Se w

  We also introduce the auxiliary family pBword of words w such that for any
  prefix p of w,  #W p <= #Se p <= #N p. pBword is stable by prefix.
  By definition, w is in Bword iff:
   - w is in pBword
   - #N w = #Se w = #W w

*)

Definition pBword (w : seq letter) : bool :=
  [forall n : 'I_(size w).+1, #W (take n w) <= #Se (take n w) <= #N (take n w)].

Lemma pBwordP w :
  reflect (forall n : nat, #W (take n w) <= #Se (take n w) <= #N (take n w))
          (w \in pBword).
Proof.
apply: (iffP forallP) => [/(_ (Ordinal _)) h| ?] n //.
case: (ltnP n (size w).+1) => [| /ltnW/take_oversize->]; first exact: h.
by rewrite -(take_size w); apply: h.
Qed.

Lemma pB_rcons l a : (rcons l a) \in pBword  -> pBword l.
Proof.
move/pBwordP=> pBwordla; apply/forallP=> [] [n hn] /=.
by move: (pBwordla n); rewrite -cats1 takel_cat.
Qed.

Definition Bword (w : seq letter) : bool :=
  [&& (w \in pBword) & #Se w - #W w == #N w - #Se w].

Lemma BwordP (w : seq letter) :
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
   - with k letters W arbitrarily inserted in d.

   Similarly, words in B (or length 3*(k1 + k2) can be generated by taking:
   - a Dyck word d1 on (NSe, W) of lenght 3*k1 (the closing parenthesis is the
   concatenation of letters Se and W);
   - shuffled with a Dyck word d2 on (N, Se) of length 2*k2 (letters can be
   inserted between the adjacent N and Se of d1);
   - with k2 letters N arbitrarily inserted in the resulting entanglement of d1
   and d2.

   An other way to generate words in A is by taking:
   - a Dyck word d1' on (NW, Se) of length 3*k1;
   - shuffled with a Dyck word d2' on (N, Se) of length 2*k2 (letters can be
   inserted between the adjacent N and Se of d1);
   - with k2 letters W arbitrarily inserted in the resulting entanglement of d1
   and d2.

   We construct a function A2B : seq letter -> seq letter such that if w is an
   Aword, then (A2B w) sends its d1' on a d1, its d2' on a d2 and its remaining
   Ws on Ns. Conversely, we construct a function B2A : seq letter -> seq letter such
   that if w is a Bword, then (B2A w) sends its d1 on a d1', its d2 on a d2' and
   its remaining Ns on Ws. We show that on Awords, B2A o A2B = id, that on
   Bwords, A2B o B2A = id and that A2B sends Awords on Bwords. Moreover, since
   A2B and B2A preserve the size of their arguments, this shows that Awords of
   size n are in bijection with Bwords of size n, which is enough to conclude.

   Functions A2B and B2A are each defined using an (infinite) automaton, with
   transitions labelled with letters. States are
   labelled with pairs of (natural) numbers, which allows to implement
   the recognition of the prioritized Dyck words. A transition
   function t : state * letter -> letter * state takes a letter and a
   state as argument, and computes the next state and the letter
   produced. The initial and final state is (0, 0). Given a word w,
   (A2B w) (resp. (B2A w)) is the word produced by the transducer tA2B
   (resp. tB2A) when reading w.
*)

(* Data structure for states of the transducers: a tagged copy of nat * nat.*)
Inductive state := State of nat * nat.

Notation "'{|' c1 ; c2 '|}'" := (State (c1, c2)).

(* We coerce type state to nat * nat *)

Coercion nat2_of_state s : (nat * nat) := let: State c := s in c.

(* Transition function of the transducer tA2B *)
Definition tA2B (c : state) (l : letter) : state :=
  match l, c with
    |  W,  {|0    ; c2   |} =>
           {|0    ; c2   |} (* (N,  {|0    ; c2   |}) *) (* _ , _  *)
    |  W,  {|c1.+1; c2   |} =>
           {|c1   ; c2.+1|} (* (Se, {|c1   ; c2.+1|}) *) (* -1, +1 *)
    |  N,  {|c1   ; c2   |} =>
           {|c1.+1; c2   |} (* (N,  {|c1.+1; c2   |}) *) (* +1, _  *)
    |  Se, {|c1   ; c2.+1|} =>
           {|c1   ; c2   |} (* (W,  {|c1   ; c2   |}) *) (* _ , -1 *)
    |  Se, {|c1.+1; 0    |} =>
           {|c1   ; 0    |} (* (Se, {|c1   ; 0    |}) *) (* -1, _  *)
    |  Se, {|0    ; 0    |} =>
           {|0    ; 0    |} (* (N,  {|0    ; 0    |}) *) (* junk *)
  end.

Arguments tA2B c l : simpl never.

(* Transition function of the transducer tB2A *)
Definition tB2A (c : state) (l : letter) : state :=
  match l, c with
    | N,  {|0    ; c2   |} =>
          {|0    ; c2   |} (* (W,  {|0    ; c2   |}) *) (* _ , _  *)
    | Se, {|c1   ; c2.+1|} =>
          {|c1.+1; c2   |} (* (W,  {|c1.+1; c2   |}) *) (* +1, -1 *)
    | N,  {|c1.+1; c2   |} =>
          {|c1   ; c2   |} (* (N,  {|c1   ; c2   |}) *) (* -1, _  *)
    | W,  {|c1   ; c2   |} =>
          {|c1   ; c2.+1|} (* (Se, {|c1   ; c2.+1|}) *) (* _ , +1 *)
    | Se, {|c1   ; 0    |} =>
          {|c1.+1; 0    |} (* (Se, {|c1.+1; 0    |}) *) (* +1, _  *)
  end.

Arguments tB2A c l : simpl never.

(* By definition, tA2B is the "converse" of tB2A in the following sense, i.e.
   tA2B reverses both the arrows of tB2A and the status of inputs and outputs.
 *)



(* A2B (resp.) is defined from tA2B as follows:
   - from a word w and an intial state c, we produce the sequence
     (A2Bstates c w) (resp.  (A2Bstates c w)) of states scanned when it is read
     by tA2B (resp. tB2A);
   - crucially, given two states cf and ci, there is a unique possible letter
     (A2Bout ci cf) (resp. B2Aout) read by a transition tB2A (resp. tA2B)
     from ci to cf, except if ci = cf = (0, 0), in which case we we consider
     that the input letter wasn't Se)
   - we then produce the sequence of corresponding letters, using B2Aout
     (resp. A2Bout).
   - A2B takes (0, 0) as initial state.
*)


Definition A2Bstates (c : state) (w : seq letter) : seq state :=
  scanl tA2B c w.

Arguments A2Bstates / c w.

Definition A2Bout (ci cf : state) : letter :=
  let: {|cf1; cf2|} := cf in
  let: {|ci1; ci2|} := ci in
  if [&& cf1 == 0, ci1 == 0 & (cf2 == ci2)] then N
  else if (ci1 == cf1.+1) && (cf2 == ci2.+1) then Se
  else if (cf1 == ci1.+1) && (cf2 == ci2) then N
  else if (cf1 == ci1) && (ci2 == cf2.+1) then W
  else Se.


Definition A2B_from (c : state) (w : seq letter) : seq letter :=
  pairmap A2Bout c (A2Bstates c w).

Arguments A2B_from / c w.

Definition A2B := A2B_from {|0; 0|}.

Arguments A2B /.


(* B2A is defined in a similar manner as A2B (with no degenerated case). *)

Definition B2Astates  (c : state) (w : seq letter) : seq state :=
  scanl tB2A c w.

Arguments B2Astates / c w.

Definition B2Aout (ci cf : state) : letter :=
  let: {|cf1; cf2|} := cf in
  let: {|ci1; ci2|} := ci in
  if [&& cf1 == 0, ci1 == 0 & (ci2 == cf2)] then W
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then W
  else if (ci1 == cf1.+1) && (cf2 == ci2) then N
  (* else if (cf2 == ci2.+1) && (cf2 == ci2) then Se *)
  (* else if (cf1 == ci1.+1) && (cf2 == 0) && (ci2 == 0) then Se *)
  else Se (* junk *).

Definition B2A_from (c : state) (w : seq letter) : seq letter :=
  pairmap B2Aout c (B2Astates c w).

Arguments B2A_from / c w.

Definition B2A (w : seq letter) := rev (B2A_from {|0; 0|} (rev w)).

Arguments B2A / w.

(* A few computations to see the translation at work: *)

Eval compute in A2B [:: N; W; Se]. (* [:: N; Se; W] *)
Eval compute in A2B [:: N; Se; W]. (* [:: N; Se; N] *)
Eval compute in A2B [:: W; N; Se]. (* [:: N; N; Se] *)


Eval compute in B2A [:: N; Se; W]. (* [:: N; W; Se] *)
Eval compute in B2A [:: N; Se; N]. (* [:: N; Se; W] *)
Eval compute in B2A [:: N; N; Se]. (* [:: W; N; Se] *)


(* A2B and B2A preserve size *)

Lemma sizeA2B w : size (A2B w) = size w.
Proof. by rewrite /= size_pairmap size_scanl. Qed.

Lemma sizeB2A w : size (B2A w) = size w.
Proof. by rewrite /= size_rev size_pairmap size_scanl size_rev. Qed.

Section CardinalsEquality.

Hypothesis A2BK : {in Bword, cancel B2A A2B}.

Hypothesis B2AK : {in Aword, cancel A2B B2A}.

Hypothesis BB2A : forall w, w \in Aword -> A2B w \in Bword.
Hypothesis AA2B : forall w, w \in Bword -> B2A w \in Aword.

Variable n : nat.

Definition Atuple : pred (n.-tuple letter) :=
 [pred w : n.-tuple letter | Aword w].

Definition Btuple : pred (n.-tuple letter) :=
 [pred w : n.-tuple letter | Bword w].

Lemma AB_eq_card_under_hyps : #|Atuple| = #|Btuple|.
Proof.
have sizeA2Bt (w : n.-tuple letter) : size (A2B w) == n.
  by rewrite sizeA2B size_tuple.
have sizeB2At (w : n.-tuple letter) : size (B2A w) == n.
  by rewrite sizeB2A size_tuple.
pose A2Bt (w : n.-tuple letter) : n.-tuple letter := Tuple (sizeA2Bt w).
pose B2At (w : n.-tuple letter) : n.-tuple letter := Tuple (sizeB2At w).
have BB2At : [seq A2Bt x | x in Atuple] \subset Btuple.
  by apply/subsetP=> w /imageP [w' Aw' ->]; apply: BB2A.
have AA2Bt : [seq B2At x | x in Btuple] \subset Atuple.
  by apply/subsetP=> w /imageP [w' Bw' ->]; apply: AA2B.
apply/eqP; rewrite eqn_leq.
have /card_in_image {1}<- : {in Atuple &, injective A2Bt}.
  case=> [s sizes] [t sizet] /B2AK /= As /B2AK /= At [] est; apply/val_inj.
  by rewrite /= -As -At est.
suff /card_in_image {2}<- : {in Btuple &, injective B2At}.
  by rewrite !subset_leq_card.
case=> [s sizes] [t sizet] /A2BK /= Bs /A2BK /= Bt [] est; apply/val_inj.
by rewrite /= -Bs -Bt est.
Qed.

End CardinalsEquality.

Lemma A2Bout_tB2A s2 lo : A2Bout (tB2A s2 lo) s2 = lo.
Proof.
by case: lo; case: s2 => [] [[|c1][|c2]] //=; rewrite ?eqxx ?andbF //= ltn_eqF.
Qed.

Lemma A2Bout_from_tB2A s1 s2 lo : s1 = tB2A s2 lo -> lo = A2Bout s1 s2.
Proof. by move->; rewrite A2Bout_tB2A. Qed.


(* But there is one degenerated case, which prevents the expected converse
   identities to hold everywhere *)
Definition noex  (l : letter) (c : state) :=
   [|| (c.1 != 0%N), (c.2 != 0%N) | (l != Se)].

Lemma B2Aout_tA2B s1 li : noex li s1 -> B2Aout (tA2B s1 li) s1 = li.
Proof.
by case: li; case: s1 => [] [[|c1][|c2]] //= _; rewrite ?eqxx ?andbF //= ltn_eqF.
Qed.

Lemma B2Aout_from_tA2B s1 s2 li : noex li s1 ->
  s2 = tA2B s1 li -> B2Aout s2 s1 = li.
Proof. move=> nx ->; exact: B2Aout_tA2B. Qed.

(* tB2A s2 lo = s1 -> li = B2Aout s2 s1 -> tA2B s1 li = s2. *)
Lemma tA2B_round s2 lo (s1 := tB2A s2 lo) : tA2B s1 (B2Aout s2 s1) = s2.
Proof.
rewrite {}/s1. (* the s1 abbreviation is really for the sake of readability *)
by case: s2 => [] [[|?] [|?]]; case: lo => //=; rewrite ?eqxx ?andbF 1?ltn_eqF.
Qed.

(* tA2B s1 li = s2 -> lo = A2Bout s1 s2 -> tB2A s2 lo = s1. *)
Lemma tB2A_round s1 lo (s2 := tA2B s1 lo) : tB2A s2 (A2Bout s1 s2) = s1.
Proof.
rewrite {}/s2. (* the s2 abbreviation is really for the sake of readability *)
by case: s1 => [] [] [|?] [|?]; case: lo => //=; rewrite ?eqxx ?andbF // ltn_eqF.
Qed.

(* Let s1 be such that s2  --     l         --> s1 in automaton B2A
   Then s1 -- l --> (tA2B s1 (B2Aout s2 s1)) in automaton A2B. *)
Lemma A2Bout_round s2 l (s1 := tB2A s2 l) : A2Bout s1 (tA2B s1 (B2Aout s2 s1)) = l.
Proof. by rewrite tA2B_round /s1 A2Bout_tB2A. Qed.

(* Let  s2 be such that s1  --     l         --> s2 in automaton A2B.
   Then s2 -- l --> (tB2A s2 (A2Bout s1 s2)) in automaton B2A *)
Lemma B2Aout_round s1 l (s2 := tA2B s1 l) : noex l s1 ->
  B2Aout s2 (tB2A s2 (A2Bout s1 s2)) = l.
Proof. by move=> nx; rewrite tB2A_round B2Aout_tA2B. Qed.

(* Let cf be the state reached when starting from state ci and reading word wi
   with automaton B2A. Let wf := (B2A_from ci wi) be the word output. Then
   reading (rev wf) from cf with automaton A2B produces word wi *)
Lemma revB2A_fromK wi ci (cf := foldl tB2A ci wi) (wf := B2A_from ci wi) :
    A2B_from cf (rev wf) = rev wi.
Proof.
rewrite {}/cf {}/wf; elim/last_ind: wi ci => [| w l ihw c] //=.
set cf := foldl _ _ _.
rewrite /= scanl_rcons -cats1 pairmap_cat rev_cat /=.
set s := B2Aout (last _ _)  _.
rewrite -/(B2A_from c w) /= rev_rcons; congr cons; last first.
  suff {ihw} -> : tA2B cf s = foldl tB2A c w by apply/ihw.
  rewrite {}/cf {}/s last_scanl foldl_rcons; exact: tA2B_round.
by rewrite {}/cf {}/s foldl_rcons last_scanl; apply: A2Bout_round.
Qed.


Section SufficientConditionsForCancel.

(* We leave as (temporary) hypotheses the facts that requires introducing
   ghost variables: *)

Hypothesis pA_noex : forall l h c,
   rcons l h \in pAword -> noex h (foldl tA2B c l).

Lemma revA2B_fromK l c : l \in pAword ->
    rev (B2A_from (foldl tA2B c l) (rev (A2B_from c l))) = l.
Proof.
elim/last_ind: l c => [| l h ihl c pAlh] //=.
set cf := foldl _ _ _.
rewrite /= scanl_rcons -cats1 pairmap_cat rev_cat /=.
set s := A2Bout _ _.
rewrite -/(A2B_from c l) /= rev_cons; congr rcons.
  suff {ihl} -> : tB2A cf s = foldl tA2B c l by apply/ihl/(pA_rcons h).
  rewrite {}/cf {}/s last_scanl foldl_rcons; exact: tB2A_round.
rewrite {}/cf {}/s foldl_rcons last_scanl; apply: B2Aout_round; exact: pA_noex.
Qed.

Hypothesis A_final_state : forall l,
  l \in Aword -> foldl tA2B {|0; 0|} l = {|0; 0|}.

Lemma A2BK_ : {in Aword, cancel A2B B2A}.
Proof.
move=> l Al; rewrite /B2A -(A_final_state Al); apply: revA2B_fromK.
exact: ApAword.
Qed.

Hypothesis B_final_state : forall l,
  l \in Bword -> foldl tB2A {|0; 0|} (rev l) = {|0; 0|}.

Lemma B2AK_ : {in Bword, cancel B2A A2B}.
Proof.
by move=> l Bl; rewrite /A2B -(B_final_state Bl) /B2A revB2A_fromK ?revK.
Qed.

End SufficientConditionsForCancel.

Lemma take_A2B n l : A2B (take n l) = take n (A2B l).
Proof. by rewrite /A2B /A2B_from /A2Bstates -take_scanl -take_pairmap. Qed.

Lemma A2B_from_cons c l w :
  A2B_from c (l :: w) = A2Bout c (tA2B c l) :: A2B_from (tA2B c l) w.
Proof. by []. Qed.

Lemma B2A_from_cons c l w :
  B2A_from c (l :: w) = B2Aout c (tB2A c l) :: B2A_from (tB2A c l) w.
Proof. by []. Qed.

Lemma A2B_from_rcons s w l : A2B_from s (rcons w l) =
  rcons (A2B_from s w) (A2Bout (foldl tA2B s w) (tA2B (foldl tA2B s w) l)).
Proof.
by rewrite /= scanl_rcons -cats1 pairmap_cat /= last_scanl foldl_rcons cats1.
Qed.

Lemma A2B_rcons  w l (s := foldl tA2B {|0; 0|} w) :
  A2B (rcons w l) = rcons (A2B w) (A2Bout s (tA2B s l)).
Proof. by rewrite /A2B A2B_from_rcons. Qed.

Lemma B2A_from_rcons s w l : B2A_from s (rcons w l) =
  rcons (B2A_from s w) (B2Aout (foldl tB2A s w) (tB2A (foldl tB2A s w) l)).
Proof.
by rewrite /= scanl_rcons -cats1 pairmap_cat /= last_scanl foldl_rcons cats1.
Qed.

Lemma B2A_cons w l (s := foldl tB2A {|0; 0|} (rev w)) :
  B2A (l :: w) = (B2Aout s (tB2A s l)) :: (B2A w).
Proof. by rewrite /B2A rev_cons B2A_from_rcons rev_rcons. Qed.

(* Now we prove the two remaining facts about words in A, plus the important
  missing property of A2B : that its image is included in Bword *)

Record gstate :=
  GState {ct1: nat; ct2: nat; dy1 : nat; dy2 : nat; free : nat}.

Definition mkGState (c : state) (d1 d2 f : nat) : gstate :=
  GState c.1 c.2 d1 d2 f.

Let g0 := GState 0 0 0 0 0.

Definition state_of_gstate (g : gstate) :=
  let: GState c1 c2 _ _ _ := g in State (c1, c2).

(* Last case is junk *)
Definition gtA2B_ (g : gstate)  (l : letter) : gstate :=
match l, g with
  |W,  GState 0     c2    d1 d2 f  =>  GState 0     c2     d1    d2    f.+1
  |W,  GState c1.+1 c2    d1 d2 f  =>  GState c1    c2.+1  d1    d2    f
  |N,  GState c1    c2    d1 d2 f  =>  GState c1.+1 c2     d1    d2    f
  |Se, GState c1    c2.+1 d1 d2 f  =>  GState c1    c2     d1.+1 d2    f
  |Se, GState c1.+1 0     d1 d2 f  =>  GState c1    0      d1    d2.+1 f
  |Se, GState 0     0     d1 d2 f  =>  GState 0     0      d1    d2    f
end.

Definition gtA2B := nosimpl gtA2B_.

(* Invariant for gtA2B. By brute force case analysis excepy for the only *)
(* interesting case of the (tail) induction on l is, i.e. when it ends with Se:*)
(* in this case the hypothesis (pAword l) forbids ct1 c = ct2 c = 0. We *)
(* need to kind of reproduce this proof outside this one to ensure we never hit*)
(* this  exceptional case... Can we do better? *)

Lemma pA_gtA2B_inv w gi (g := foldl gtA2B gi w) :
  w \in pAword ->
  [/\
#N  w + dy1 gi + dy2 gi + ct1 gi + ct2 gi =
        dy1 g  + dy2 g  + ct1 g  + ct2 g   ,
#Se w + dy1 gi + dy2 gi                   =
        dy1 g  + dy2 g                      &
#W  w + dy1 gi + ct2 gi + free gi         =
        dy1 g  + ct2 g  + free g
].
Proof.
rewrite {}/g; elim/last_ind: w => [| w l ihw] /= pAwl=> //; rewrite !foldl_rcons.
have {ihw} /ihw := pA_rcons _ pAwl.
move: (foldl gtA2B gi w) => c [eN eSe eW].
case: l pAwl => pAwl; rewrite !count_mem_rcons !eqxx /=.
- by rewrite !addSn {}eW {}eN {}eSe; case: c => * /=; split; ring.
- by rewrite !addSn {}eW {}eN {}eSe; case: c => [] [|c1] * /=; split; ring.
- suff {eW} : ct1 c + ct2 c != 0.
    rewrite !addSn {}eW {}eN {}eSe; case: c => [] [|?] [|?] * //=; split; ring.
  have {pAwl} : #Se w < #N w := pA_rconsSe pAwl.
  apply: contraL; rewrite addn_eq0; case/andP=> /eqP e1 /eqP e2.
  suff /eqP-> : #Se w == #N w + (ct1 gi + ct2 gi) by rewrite -leqNgt leq_addr.
  by rewrite -(eqn_add2r (dy1 gi + dy2 gi)) addnAC !addnA eN eSe e1 e2 !addn0.
Qed.

Definition gnoex (l : letter) (g : gstate) :=
   [|| ct1 g != 0, ct2 g != 0 | l != Se].

Lemma gnoex_noex l g : gnoex l g = noex l (state_of_gstate g).
Proof. by case: g. Qed.

Lemma pA_gnoex w l g : rcons w l \in pAword -> gnoex l (foldl gtA2B g w).
Proof.
rewrite /gnoex; case: l; rewrite ?orbT // orbF -negb_and => pA.
have /(pA_gtA2B_inv g) := pA_rcons _ pA.
move: (foldl _ _ _) => [] c1 c2 d1 d2 f /= [] eN eSe _.
apply: contraL (pA_rconsSe pA); case/andP => /eqP e1 /eqP e2.
suff /eqP-> : #Se w == #N w + (ct1 g + ct2 g) by rewrite -leqNgt leq_addr.
by rewrite -(eqn_add2r (dy1 g + dy2 g)) addnAC !addnA eN eSe e1 e2 !addn0.
Qed.

Lemma state_of_foldl_gtA2B s d1 d2 f w (g := mkGState s d1 d2 f) :
  state_of_gstate (foldl gtA2B g w) = foldl tA2B s w.
Proof.
have -> : s = state_of_gstate g by rewrite {}/g; case: s => [] [].
elim: w g => [|h w ihw] //= g; rewrite {}ihw; congr foldl.
by case: g=> c1 c2* {w} /=; case: h => //=; case: c1 => * //; case: c2 => *.
Qed.

Lemma pA_noex  w l s : rcons w l \in pAword -> noex l (foldl tA2B s w).
Proof.
move=> ?; rewrite -(state_of_foldl_gtA2B _ 0 0 0) -gnoex_noex; exact: pA_gnoex.
Qed.

Lemma A_final_state l : l \in Aword -> foldl tA2B {|0; 0|} l = {|0; 0|}.
Proof.
case/AwordP=> /(pA_gtA2B_inv g0); rewrite -(state_of_foldl_gtA2B _ 0 0 0) /=.
rewrite !addn0; move: (foldl _ _ _) => [] c1 c2 d1 d2 f /= [-> -> ->].
rewrite -addnA addnC; move/(canRL (addnK _)); rewrite subnn.
by case: c1 => [|?] //; case: c2.
Qed.

Theorem A2BK : {in Aword, cancel A2B B2A}.
Proof. apply: A2BK_; [exact: pA_noex | exact: A_final_state]. Qed.

Definition gA2Bout gf gi :=
  let: (GState ci1 ci2 _ _ _) := gi in
  let: (GState cf1 cf2 _ _ _) := gf in
  if [&& ci1 == 0, cf1 == 0 & (ci2 == cf2)] then N
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then Se
  else if (ci1 == cf1.+1) && (ci2 == cf2) then N
  else if (ci1 == cf1) && (cf2 == ci2.+1) then W
  else Se.

Definition gA2Bstates (g : gstate) (w : seq letter) : seq gstate :=
  scanl gtA2B g w.

Arguments gA2Bstates / g w.

Definition gA2B_from (g : gstate) (w : seq letter) : seq letter :=
  pairmap gA2Bout g (gA2Bstates g w).

Arguments gA2B_from / g w.

(* In order to prove that reading a word in A produces a word in B, we
   need another invariant. *)

Lemma gA2B_from_rcons g w l : gA2B_from g (rcons w l) =
  rcons (gA2B_from g w) (gA2Bout (foldl gtA2B g w) (gtA2B (foldl gtA2B g w) l)).
Proof.
by rewrite /= scanl_rcons -cats1 pairmap_cat /= last_scanl foldl_rcons cats1.
Qed.

Lemma gA2B_out_state_of g1 g2 :
  gA2Bout g1 g2 = A2Bout (state_of_gstate g1) (state_of_gstate g2).
Proof. by case: g1 => c11 c12 *; case: g2 => c21 c22. Qed.

Lemma gA2B_A2B_from s d1 d2 f w :
  A2B_from s w = gA2B_from (mkGState s d1 d2 f) w.
Proof.
elim/last_ind: w => [| w l ihw] //; rewrite gA2B_from_rcons -ihw.
by rewrite A2B_from_rcons gA2B_out_state_of -!foldl_rcons !state_of_foldl_gtA2B.
Qed.


Lemma pA_noex_ghost l h g : rcons l h \in pAword ->
  noex h (state_of_gstate (foldl gtA2B g l)).
Proof.
have -> : g = mkGState {|ct1 g; ct2 g|} (dy1 g) (dy2 g) (free g) by case: g.
rewrite state_of_foldl_gtA2B; exact: pA_noex.
Qed.

Lemma pA_gA2B_inv wi gi (g := foldl gtA2B gi wi) (wo := gA2B_from gi wi) :
  wi \in pAword ->
  [/\
#N  wo + dy1 gi + dy2 gi + ct1 gi + ct2 gi + free gi =
         dy1 g  + dy2 g  + ct1 g  + ct2 g  + free g    ,
#Se wo + dy1 gi + dy2 gi + ct2 gi =
         dy1 g + dy2 g + ct2 g                         &
#W  wo + dy1 gi = dy1 g].
Proof.
rewrite {}/g {}/wo; elim/last_ind: wi => [| w l ihw] pAwl=> //.
have {ihw} /ihw := pA_rcons _ pAwl.
have := pA_noex_ghost gi pAwl.
rewrite gA2B_from_rcons !foldl_rcons.
set wo := gA2B_from gi w.
move: (foldl gtA2B gi w) => g noex [eN eSe eW].
case: l noex pAwl => [_ | _ | nx] /pAwordP pAwl; rewrite !count_mem_rcons /=.
- have -> : gA2Bout g (gtA2B g N) = N. (* push this outside *)
    case: g {eN eSe eW} => [] [] [|?] [|?] *; rewrite //= ?eqxx //= ?andbF //.
    by rewrite ltn_eqF.
  have-> /=: gtA2B g N = GState (ct1 g).+1 (ct2 g) (dy1 g) (dy2 g) (free g).
     by case: g {eN eSe eW}.
  by rewrite addnS !addSn eN eSe eW.
- case: g eN eSe eW => [] [|c1] c2 d1 d2 f /=; rewrite ?addn0 !eqxx => eN eSe eW.
  + by rewrite addnS !addSn eN eW eSe.
  + by rewrite andbF /= !addSn eN eW eSe !addnS !addSn.
- case: g eN eSe eW nx => [] [|c1] [|c2] d1 d2 f //=;
    rewrite ?addn0 => eN eSe eW _ /=.
  + by rewrite ltn_eqF // !eqxx eN eSe /= !addnS !addSn eW.
  + by rewrite !andbF ltn_eqF //= eN eW /= !addSn eSe !addnS !addSn.
  + by rewrite ltn_eqF //= !eqxx /= eN eSe /= !addnS !addSn eW.
Qed.


Lemma ghost_gtA2B g s :
  tA2B (state_of_gstate g) s = state_of_gstate (gtA2B g s).
Proof. by case: g => [] c1 c2; case: s => //; case: c1 => //; case: c2. Qed.

Lemma ghost_gA2Bout g1 g2 :
  gA2Bout g1 g2 = A2Bout (state_of_gstate g1) (state_of_gstate g2).
Proof. by case: g1 => [] *; case: g2. Qed.

Lemma pB_A2B_pA l : l \in pAword -> A2B l \in pBword.
Proof.
move/pAwordP=> pAl; apply/pBwordP=> n.
have /(pA_gA2B_inv (mkGState {|0; 0|} 0 0 0)) : take n l \in pAword.
  by apply/pAwordP=> m; rewrite take_take.
rewrite !addn0 -gA2B_A2B_from -/A2B take_A2B; case=> -> -> ->.
move: (foldl _ _ _) => g; rewrite -addnA leq_addr /= addnA.
by set d := dy1 _ + dy2 _; rewrite -[d + _ + _]addnAC -addnA leq_addr.
Qed.

Theorem B_A2B_A l : l \in Aword -> A2B l \in Bword.
case/AwordP => pAl eNSe eSeW.
rewrite -topredE /= /Bword pB_A2B_pA //=.
pose rl := foldl gtA2B g0 l.
have /and3P [/eqP ec1 /eqP ec2 /eqP edf]:
  [&& ct1 rl == 0, ct2 rl == 0 & dy2 rl == free rl].
  move/(pA_gtA2B_inv g0): (pAl); rewrite /= !addn0 -/rl; case=> eN eSe eW.
  move: eNSe; rewrite eN -addnA eSe; move/(canRL (addKn _)); rewrite subnn.
  move/eqP; rewrite addn_eq0; case/andP=> -> ct20; rewrite (eqP ct20) /=.
  by move/eqP: eSeW; rewrite eW (eqP ct20) addn0 eSe eqn_add2l.
move/(pA_gA2B_inv g0): pAl; rewrite -/rl ec1 ec2 edf !addn0.
rewrite -(gA2B_A2B_from {|0; 0|} 0 0 0);  case=> -> -> ->.
by rewrite addKn -{2}[dy1 _ + _]addn0 subnDl subn0.
Qed.

Section ExtraSeq.

Variables (letter state : Type).
Variables (f : state -> letter -> state) (t : state -> state -> letter).

Lemma rev_pairmap ci cf sc :
  rev (pairmap t ci (rcons sc cf)) =
  pairmap (fun x y => t y x) cf (rcons (rev sc) ci).
Proof.
elim/last_ind: sc ci cf => [| sc c ihsc] //= ci cf.
by rewrite pairmap_rcons rev_rcons last_rcons rev_rcons rcons_cons /= ihsc.
Qed.


(* drop_nth imposes a default element ... *)
Lemma drop_add (d : letter) (w : seq letter) (n1 n2 : nat) :
   drop (n1 + n2) w = drop n1 (drop n2 w).
Proof.
elim: n1 n2 w => [| n1 ihn1] //= n2 w; first by rewrite add0n drop0.
rewrite addSn -addnS ihn1 -(addn1 n1) ihn1.
case: (ltnP n2 (size w)) => hn2; first by rewrite (drop_nth d hn2) /= drop0.
by rewrite ![drop _ w]drop_oversize //=; apply: leq_trans hn2 _.
Qed.

End ExtraSeq.

Lemma statesB2AK c w (wo := B2A_from c w) :
  c :: scanl tB2A c w =
  rcons (rev (scanl tA2B (foldl tB2A c w) (rev wo))) (foldl tB2A c w).
Proof.
rewrite {}/wo; elim/last_ind: w => [| l w ihw] //.
rewrite scanl_rcons -rcons_cons; congr rcons; rewrite {}ihw.
rewrite B2A_from_rcons rev_rcons foldl_rcons; set co := foldl _ _ _.
by rewrite [scanl _ _ (_ :: _)]/= tA2B_round rev_cons.
Qed.

Lemma statesA2BK c w (wo := A2B_from c w) :
  c :: scanl tA2B c w =
  rcons (rev (scanl tB2A (foldl tA2B c w) (rev wo))) (foldl tA2B c w).
Proof.
rewrite {}/wo; elim/last_ind: w => [| l w ihw] //.
rewrite scanl_rcons -rcons_cons; congr rcons; rewrite {}ihw.
rewrite A2B_from_rcons rev_rcons foldl_rcons; set co := foldl _ _ _.
by rewrite [scanl _ _ (_ :: _)]/= tB2A_round rev_cons.
Qed.



Lemma ct2_foldl_tB2A gi w (g := foldl tB2A gi w) :
  (forall n, #W (drop n w) <= #Se (drop n w)) -> g.2 <= gi.2.
Proof.
rewrite {}/g.
move: {2}(size w) (leqnn (size w)) => n; elim: n w gi => [| n ihn] w gi.
  by rewrite leqn0 size_eq0 => /eqP ->.
rewrite leq_eqVlt; case/orP; last by apply: ihn.
case/lastP: w => [| w l] //; rewrite size_rcons eqSS => /eqP ssn.
case: l => leWSe; rewrite foldl_rcons.
- have -> : (tB2A (foldl tB2A gi w) N).2 = (foldl tB2A gi w).2.
    by case: (foldl _ _ _) => [] [] [].
  apply: ihn => [| k]; first by rewrite ssn.
  have := leWSe k; case: (leqP k (size w)) => hkss.
    by rewrite drop_rcons // !count_mem_rcons /=.
  rewrite !drop_oversize ?size_rcons //; exact: ltnW.
- by move: (leWSe (size w)); rewrite -cats1 drop_cat ltnn subnn drop0.
- case hyp : [forall x : 'I_(size w).+1, (#W (drop x w) <= #Se (drop x w))].
  + have h : (tB2A (foldl tB2A gi w) Se).2 <= (foldl tB2A gi w).2.
      by case: (foldl _ _ _) => [] [] c1 [|c2] /=.
    apply: leq_trans h _; apply: ihn=> [|k]; rewrite ?ssn //.
    case: (leqP k (size w)) => hk; last by rewrite drop_oversize //; exact: ltnW.
    by rewrite -ltnS in hk; have /= := (forallP hyp) (Ordinal hk).
  + move/negbT: hyp; rewrite negb_forall; case/existsP=> j; rewrite -ltnNge => Pj.
    have [// | k Pk /= max_k {j Pj}] := @arg_maxP _ j
      (fun i : 'I_(size w).+1 => #Se (drop i w) < #W (drop i w)) (fun x => val x).
    have {max_k} max_k j : j < (size w).+1 -> k < j ->
         #W (drop j w) <= #Se (drop j w).
      move=> oj; rewrite ltnNge; apply: contraR; rewrite -ltnNge.
      exact: max_k (Ordinal oj).
    pose w1 := take k w. pose w2 := drop k.+1 w.
    have eWw2 : drop k w = W :: w2.
      rewrite {}/w2; case: k Pk max_k {w1} => [] k //=.
      rewrite ltnS => leks /=  Pk max_k.
      move: leks; rewrite leq_eqVlt; case/orP => [/eqP ek | ltksw].
        by move: Pk; rewrite ek drop_oversize.
      have : #Se (drop k.+1 w) >= #W (drop k.+1 w) by exact: max_k.
      move: Pk; rewrite (drop_nth W) //; case: (nth _ _) => //=.
       + by rewrite !add0n [#W(_) <= _]leqNgt; move->.
       + rewrite add0n add1n => h1 h2. have := leq_trans h1 h2.
         by rewrite ltnNge leqnSn.
   have ew12 : w = w1 ++ W :: w2 by rewrite -eWw2 cat_take_drop.
   have hw2 i : #W (drop i w2) <= #Se (drop i w2).
     rewrite /w2 -(drop_add W) addnS.
     case: (ltnP (i + k).+1 (size w)) => hik; last by rewrite drop_oversize.
     apply: max_k; first exact: ltnW.
     by rewrite /= ltnS leq_addl.
   have WSew2 : #W w2 = #Se w2.
     apply/eqP; rewrite eqn_leq; move: (hw2 0); rewrite drop0=> -> /=.
     by move: Pk; rewrite /w2 eWw2 /= add0n add1n ltnS /w2.
   have hw1 i : #W (drop i w1) <= #Se (drop i w1).
     case: (ltnP i (size w1)) => hi; last by rewrite drop_oversize.
     have := (leWSe i).
     rewrite ew12 rcons_cat !drop_cat hi !count_cat !count_mem_rcons /=.
     by rewrite !add1n !add0n WSew2 leq_add2r.
  rewrite ew12 foldl_cat /= {Pk max_k leWSe}.
  set g := foldl _ _ w1.
  have hg : g.2 <= gi.2.
    by apply: ihn => //; rewrite /w1 size_take -ssn; case: ifP => //; move/ltnW.
  apply: leq_trans hg; case: g => [] [c1 c2] /=.
  have -> : tB2A {|c1; c2|} W = {|c1; c2.+1|} by [].
  set g := foldl _ _ _.
  suff : g.2 <= c2.+1 by case: g => [] [g1 [|g2]].
  by apply: ihn => //; rewrite /w2 size_drop -ssn leq_subr.
Qed.


Lemma ct1_foldl_tB2A gi w (g := foldl tB2A gi w) :
  (forall n, #Se (drop n w) <= #N (drop n w)) -> g.1 <= gi.1.
Proof.
rewrite {}/g.
move: {2}(size w) (leqnn (size w)) => n; elim: n w gi => [| n ihn] w gi.
  by rewrite leqn0 size_eq0 => /eqP ->.
rewrite leq_eqVlt; case/orP; last by apply: ihn.
case/lastP: w => [| w l] //; rewrite size_rcons eqSS => /eqP ssn.
case: l => leWSe; rewrite foldl_rcons.
- (* aie *)
case hyp : [forall x : 'I_(size w).+1, (#Se (drop x w) <= #N (drop x w))].
  + have h : (tB2A (foldl tB2A gi w) N).1 <= (foldl tB2A gi w).1.
      by case: (foldl _ _ _) => [] [] [|c1] c2 /=.
    apply: leq_trans h _; apply: ihn=> [|k]; rewrite ?ssn //.
    case: (leqP k (size w)) => hk; last by rewrite drop_oversize //; exact: ltnW.
    by rewrite -ltnS in hk; have /= := (forallP hyp) (Ordinal hk).
  + move/negbT: hyp; rewrite negb_forall; case/existsP=> j; rewrite -ltnNge => Pj.
    have [// | k Pk /= max_k {j Pj}] := @arg_maxP _ j
      (fun i : 'I_(size w).+1 => #N (drop i w) < #Se (drop i w)) (fun x => val x).
    have {max_k} max_k j : j < (size w).+1 -> k < j ->
         #Se (drop j w) <= #N (drop j w).
      move=> oj; rewrite ltnNge; apply: contraR; rewrite -ltnNge.
      exact: max_k (Ordinal oj).
    pose w1 := take k w. pose w2 := drop k.+1 w.
    have eWw2 : drop k w = Se :: w2.
      rewrite {}/w2; case: k Pk max_k {w1} => [] k //=.
      rewrite ltnS => leks /=  Pk max_k.
      move: leks; rewrite leq_eqVlt; case/orP => [/eqP ek | ltksw].
        by move: Pk; rewrite ek drop_oversize.
      have : #N (drop k.+1 w) >= #Se (drop k.+1 w) by exact: max_k.
      move: Pk; rewrite (drop_nth Se) //; case: (nth _ _) => //=.
       + rewrite add0n add1n => h1 h2. have := leq_trans h1 h2.
         by rewrite ltnNge leqnSn.
       + by rewrite !add0n [#Se(_) <= _]leqNgt; move->.
   have ew12 : w = w1 ++ Se :: w2 by rewrite -eWw2 cat_take_drop.
   have hw2 i : #Se (drop i w2) <= #N (drop i w2).
     rewrite /w2 -(drop_add Se) addnS.
     case: (ltnP (i + k).+1 (size w)) => hik; last by rewrite drop_oversize.
     apply: max_k; first exact: ltnW.
     by rewrite /= ltnS leq_addl.
   have WSew2 : #Se w2 = #N w2.
     apply/eqP; rewrite eqn_leq; move: (hw2 0); rewrite drop0=> -> /=.
     by move: Pk; rewrite /w2 eWw2 /= add0n add1n ltnS /w2.
   have hw1 i : #Se (drop i w1) <= #N (drop i w1).
     case: (ltnP i (size w1)) => hi; last by rewrite drop_oversize.
     have := (leWSe i).
     rewrite ew12 rcons_cat !drop_cat hi !count_cat !count_mem_rcons /=.
     by rewrite !add1n !add0n WSew2 leq_add2r.
  rewrite ew12 foldl_cat /= {Pk max_k leWSe}.
  set g := foldl _ _ w1.
  have hg : g.1 <= gi.1.
    by apply: ihn => //; rewrite /w1 size_take -ssn; case: ifP => //; move/ltnW.
  apply: leq_trans hg; case: g => [] [] c1 [|c2].
   + have -> /= : tB2A {|c1; 0|} Se = {|c1.+1; 0|} by [].
     set g := foldl _ _ _.
     suff : g.1 <= c1.+1 by case: g => [] [[|g1] g2] /=.
     by apply: ihn => //; rewrite /w2 size_drop -ssn leq_subr.
   + have -> /= : tB2A {|c1; c2.+1|} Se = {|c1.+1; c2|} by [].
     set g := foldl _ _ _.
     suff : g.1 <= c1.+1 by case: g => [] [[|g1] g2] /=.
     by apply: ihn => //; rewrite /w2 size_drop -ssn leq_subr.
- have -> : (tB2A (foldl tB2A gi w) W).1 = (foldl tB2A gi w).1.
    by case: (foldl _ _ _) => [] [] [].
  apply: ihn => [| k]; first by rewrite ssn.
  have := leWSe k; case: (leqP k (size w)) => hkss.
    by rewrite drop_rcons // !count_mem_rcons /=.
  rewrite !drop_oversize ?size_rcons //; exact: ltnW.
- by move: (leWSe (size w)); rewrite -cats1 drop_cat ltnn subnn drop0.
Qed.

Lemma B_final_state w : w \in pBword -> foldl tB2A {|0; 0|} (rev w) = {|0; 0|}.
Proof.
move/pBwordP=> Bw.
have : (foldl tB2A {|0; 0|} (rev w)).1 = 0.
  apply/eqP; rewrite -leqn0; apply: ct1_foldl_tB2A => n.
  case: (ltnP (size w) n) => hn.
    by rewrite drop_oversize // size_rev; exact: ltnW.
  rewrite -[w](cat_take_drop (size w - n)) rev_cat.
  rewrite drop_size_cat; last by rewrite size_rev size_drop // subKn.
  by rewrite !count_rev; case/andP: (Bw (size w - n)).
have : (foldl tB2A {|0; 0|} (rev w)).2 = 0.
  apply/eqP; rewrite -leqn0; apply: ct2_foldl_tB2A => n.
  case: (ltnP (size w) n) => hn.
    by rewrite drop_oversize // size_rev; exact: ltnW.
  rewrite -[w](cat_take_drop (size w - n)) rev_cat.
  rewrite drop_size_cat; last by rewrite size_rev size_drop // subKn.
  by rewrite !count_rev; case/andP: (Bw (size w - n)).
by case: (foldl _ _ _) => [] [c1 c2] /= -> ->.
Qed.

(*

Record gbstate :=
  Gbstate {ctb1: nat; ctb2: nat; dyb1 : nat; dyb2 : nat; freeb : nat; ob : nat}.

Definition mkGbstate (c : state) (d1 d2 f o : nat) : gbstate :=
  Gbstate c.1 c.2 d1 d2 f o.

Let gb0 := Gbstate 0 0 0 0 0 0.

Definition state_of_gbstate (g : gbstate) :=
  let: Gbstate c1 c2 _ _ _ _ := g in State (c1, c2).


Definition gtB2A_ (g : gbstate)  (l : letter) : gbstate :=
match l, g with
  |W,  Gbstate c1     c2    d1 d2 f  o    =>  Gbstate c1     c2.+1  d1    d2    f    o     (* Se *)
  |Se, Gbstate c1     c2.+1 d1 d2 f  o    =>  Gbstate c1.+1  c2     d1    d2    f    o.+1  (* W *)
  |Se, Gbstate c1     0     d1 d2 f  o    =>  Gbstate c1.+1  0      d1    d2    f    o     (* Se *)
  |N,  Gbstate c1.+1  c2    d1 d2 f  o.+1 =>  Gbstate c1     c2     d1.+1 d2    f    o     (* N *)
  |N,  Gbstate c1.+1  c2    d1 d2 f  0    =>  Gbstate c1     c2     d1    d2.+1 f    0     (* N *)
  |N,  Gbstate 0      c2    d1 d2 f  o    =>  Gbstate 0      c2     d1    d2    f.+1 o     (* W *)
end.
Definition gtB2A := nosimpl gtB2A_.

Lemma gtB2A_inv w gi (g := foldl gtB2A gi w) :
  [/\
#N  w + dyb1 gi + dyb2 gi + freeb gi =
        dyb1 g  + dyb2 g  + freeb g   ,
#Se w + dyb1 gi + dyb2 gi + ctb1 gi  =
        dyb1 g  + dyb2 g  + ctb1 g                       &
#W  w + dyb1 gi + ob gi   + ctb2 gi          =
        dyb1 g  + ob g    + ctb2 g
].
Proof.
rewrite {}/g; elim/last_ind: w => [| w l] /= => //.
rewrite foldl_rcons /=; move: (foldl gtB2A gi w) => gf [eN eSe eW].
case: l; rewrite !count_mem_rcons !eqxx /=.
- rewrite !addSn {}eN {}eSe {}eW.
  by case: gf => [] [|c1] [|c2] d1 d2 f [|o] /=; rewrite ?addn0 ?addnS ?addSn.
- rewrite !addSn {}eN {}eSe {}eW.
  by case: gf => [] [|c1] [|c2] d1 d2 [|o] f /=; rewrite ?addn0 ?addnS ?addSn ?addn0.
- rewrite !addSn {}eN {}eSe {}eW.
  by case: gf => [] [|c1] [|c2] d1 d2 [|o] f /=; rewrite !addnS.
Qed.



Lemma state_of_foldl_gtB2A s d1 d2 f o w (g := mkGbstate s d1 d2 f o) :
  state_of_gbstate (foldl gtB2A g w) = foldl tB2A s w.
Proof.
have -> : s = state_of_gbstate g by rewrite {}/g; case: s => [] [].
elim: w g => [|h w ihw] //= g; rewrite {}ihw; congr foldl.
by case: g=> c1 c2 ? ? ? [|og] {w} /=; case: h; case: c1 => *; case: c2 => *.
Qed.

Lemma again_and_again w : w \in Bword ->
  state_of_gbstate (foldl gtB2A gb0 (rev w)) = {|0; 0|}.
Proof.
move=> Bw.
have hw1 : #W w <= #Se w by admit.
have hw2 : #Se w <= #N w by admit.
have hw3 : #N w - #Se w = #Se w - #W w by admit.
have /= := gtB2A_inv (rev w) gb0.
case: (foldl _ _ _) => c1 c2 d1 d2 f o /=.
rewrite !addn0 !count_rev; case=> eN eSe eW.
move: hw3.
  rewrite eN eSe subnDl.


Definition gB2Aout (gi gf : gbstate) : letter :=
  let: (Gbstate ci1 ci2 _ _ _ _) := gi in
  let: (Gbstate cf1 cf2 _ _ _ _) := gf in
  if [&& cf1 == 0, ci1 == 0 & (ci2 == cf2)] then W
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then W
  else if (ci1 == cf1.+1) && (cf2 == ci2) then N
  (* else if (cf2 == ci2.+1) && (cf2 == ci2) then Se *)
  (* else if (cf1 == ci1.+1) && (cf2 == 0) && (ci2 == 0) then Se *)
  else Se (* junk *).

Definition gB2Astates (g : gbstate) (w : seq letter) : seq gbstate :=
  scanl gtB2A g w.

Arguments gB2Astates / g w.

Definition gB2A_from (g : gbstate) (w : seq letter) : seq letter :=
  pairmap gB2Aout g (gB2Astates g w).

Arguments gB2A_from / g w.

(* In order to prove that reading a word in A produces a word in B, we
   need another invariant. *)

Lemma gB2A_from_rcons g w l : gB2A_from g (rcons w l) =
  rcons (gB2A_from g w) (gB2Aout (foldl gtB2A g w) (gtB2A (foldl gtB2A g w) l)).
Proof.
by rewrite /= scanl_rcons -cats1 pairmap_cat /= last_scanl foldl_rcons cats1.
Qed.

Lemma gB2A_from_inv wi gi (g := foldl gtB2A gi wi) (wo := gB2A_from gi wi) :
  [/\
#N  wo + dyb1 gi + dyb2 gi =
         dyb1 g  + dyb2 g    ,
#Se wo + dyb1 gi + dyb2 gi + ctb2 gi + ctb1 gi =
         dyb1 g  + dyb2 g  + ctb2 g  + ctb1 g                         &
#W  wo + dyb1 gi + ob gi + freeb gi =
         dyb1 g  + ob g  + freeb g].
Proof.
rewrite {}/g {}/wo; elim/last_ind: wi => [| w l] //.
rewrite gB2A_from_rcons !foldl_rcons; set wo := gB2A_from gi w.
move: (foldl gtB2A gi w) => g [eN eSe eW]; rewrite !count_mem_rcons /=.
case: l.
- case: g eN eSe eW => [] [|c1] c2 d1 d2 f [|o]; rewrite /= ?eqxx ?addSn ?addnS.
  + by move=> -> -> ->.
  + by move=> -> -> ->.
  + by rewrite andbF ltn_eqF //=; rewrite !addSn !addn0; move=> -> -> ->.
  + by rewrite ?eqxx ?andbF ltn_eqF //=; rewrite !addSn; move=> -> -> ->.
- case: g eN eSe eW => [] [|c1] c2 d1 d2 f [|o]; rewrite /= ?eqxx ?addSn ?addnS.
  + by rewrite ltn_eqF //= !addn0 !addSn ?addnS; move=> -> <- ->.
  + by rewrite ltn_eqF //= !addn0 !addSn ?addnS; move=> -> -> ->.
  + by rewrite ltn_eqF //= !addn0 !addSn ?addnS; move=> -> -> ->.
  + by rewrite ltn_eqF //= !addSn ?addnS; move=> -> -> ->.
- case: g eN eSe eW => [] c1 [|c2] d1 d2 f [|o]; rewrite /= ?eqxx ?addSn ?addnS.
  + by rewrite /= ltn_eqF //= !addn0 !addSn ?addnS; move=> -> <- ->.
  + by rewrite /= ltn_eqF //= !addn0 !addSn ?addnS; move=> -> -> ->.
  + by rewrite !addn0 !addSn ?addnS; move=> -> -> ->.
  + by rewrite !addSn ?addnS; move=> -> -> ->.
Qed.

Definition gB2A (w : seq letter) := rev (gB2A_from gb0 (rev w)).

Lemma gB2A_inv wi (wo := gB2A wi) :
wi \in Bword ->
  [/\
#N  wo = 0,
#Se wo = 0                         &
#W  wo = 0].
Proof.
have /= := gtB2A_inv (rev wi) gb0; rewrite !addn0 !count_rev.
have /= := gB2A_from_inv (rev wi) gb0.
set g := foldl _ _ _; rewrite -/(gB2A_from _ _) !addn0.
rewrite -[#N(_ )]count_rev -[#Se(_ )]count_rev -[#W(_ )]count_rev.
rewrite -/(gB2A wi).
case=> eN eSe eW.


Lemma gB2A_out_state_of g1 g2 :

  gB2Aout g1 g2 = B2Aout (state_of_gbstate g1) (state_of_gbstate g2).
Proof. by case: g1 => c11 c12 *; case: g2 => c21 c22. Qed.

Lemma gB2A_A2B_from s d1 d2 f o w :
  B2A_from s w = gB2A_from (mkGbstate s d1 d2 f o) w.
Proof.
elim/last_ind: w => [| w l ihw] //; rewrite gB2A_from_rcons -ihw.
by rewrite B2A_from_rcons gB2A_out_state_of -!foldl_rcons !state_of_foldl_gtB2A.
Qed.


(* Lemma ghost_gtA2B g s : *)
(*   tA2B (state_of_gstate g) s = state_of_gstate (gtA2B g s). *)
(* Proof. by case: g => [] c1 c2; case: s => //; case: c1 => //; case: c2. Qed. *)

(* Lemma ghost_gB2Aout g1 g2 : *)
(*   gB2Aout g1 g2 = A2Bout (state_of_gstate g1) (state_of_gstate g2). *)
(* Proof. by case: g1 => [] *; case: g2. Qed. *)

(* Lemma pB_A2B_pA l : l \in pAword -> A2B l \in pBword. *)
(* Proof. *)
(* move/pAwordP=> pAl; apply/pBwordP=> n. *)
(* have /(pA_gB2A_inv (mkGState {|0; 0|} 0 0 0)) : take n l \in pAword. *)
(*   by apply/pAwordP=> m; rewrite take_take. *)
(* rewrite !addn0 -gB2A_A2B_from -/A2B take_A2B; case=> -> -> ->. *)
(* move: (foldl _ _ _) => g; rewrite -addnA leq_addr /= addnA. *)
(* by set d := dy1 _ + dy2 _; rewrite -[d + _ + _]addnAC -addnA leq_addr. *)
(* Qed. *)

(* Theorem B_A2B_A l : l \in Aword -> A2B l \in Bword. *)
(* case/AwordP => pAl eNSe eSeW. *)
(* rewrite -topredE /= /Bword pB_A2B_pA //=. *)
(* pose rl := foldl gtA2B g0 l. *)
(* have /and3P [/eqP ec1 /eqP ec2 /eqP edf]: *)
(*   [&& ct1 rl == 0, ct2 rl == 0 & dy2 rl == free rl]. *)
(*   move/(pA_gtA2B_inv g0): (pAl); rewrite /= !addn0 -/rl; case=> eN eSe eW. *)
(*   move: eNSe; rewrite eN -addnA eSe; move/(canRL (addKn _)); rewrite subnn. *)
(*   move/eqP; rewrite addn_eq0; case/andP=> -> ct20; rewrite (eqP ct20) /=. *)
(*   by move/eqP: eSeW; rewrite eW (eqP ct20) addn0 eSe eqn_add2l. *)
(* move/(pA_gB2A_inv g0): pAl; rewrite -/rl ec1 ec2 edf !addn0. *)
(* rewrite -(gB2A_A2B_from {|0; 0|} 0 0 0);  case=> -> -> ->. *)
(* by rewrite addKn -{2}[dy1 _ + _]addn0 subnDl subn0. *)
(* Qed. *)


Lemma statesB2AK c w (wo := B2A_from c w) :
  c :: scanl tB2A c w =
  rcons (rev (scanl tA2B (foldl tB2A c w) (rev wo))) (foldl tB2A c w).
Proof.
rewrite {}/wo; elim/last_ind: w => [| l w ihw] //.
rewrite scanl_rcons -rcons_cons; congr rcons; rewrite {}ihw.
rewrite B2A_from_rcons rev_rcons foldl_rcons; set co := foldl _ _ _.
by rewrite [scanl _ _ (_ :: _)]/= tA2B_round rev_cons.
Qed.

Lemma statesA2BK c w (wo := A2B_from c w) :
  c :: scanl tA2B c w =
  rcons (rev (scanl tB2A (foldl tA2B c w) (rev wo))) (foldl tA2B c w).
Proof.
rewrite {}/wo; elim/last_ind: w => [| l w ihw] //.
rewrite scanl_rcons -rcons_cons; congr rcons; rewrite {}ihw.
rewrite A2B_from_rcons rev_rcons foldl_rcons; set co := foldl _ _ _.
by rewrite [scanl _ _ (_ :: _)]/= tB2A_round rev_cons.
Qed.

Lemma foo s2 : cancel (tB2A s2) (fun x => A2Bout x s2).
Proof. move=> y /=. exact: A2Bout_tB2A. Qed.

Lemma bar s2 : cancel (scanl tB2A s2) (pairmap (fun y x => A2Bout x y) s2).
Proof. apply: scanlK; exact: foo. Qed.

Lemma B_final_state : forall l,
  (rev l) \in Bword -> foldl tB2A {|0; 0|} l = {|0; 0|}.
Proof.
move=> w; case/BwordP => /pBwordP.
rewrite !count_rev.
Search _ take rev.



Lemma pA_gtA2B_inv w gi (g := foldl gtA2B gi w) :
  w \in pAword ->
  [/\
#N  w + dy1 gi + dy2 gi + ct1 gi + ct2 gi =
        dy1 g  + dy2 g  + ct1 g  + ct2 g   ,
#Se w + dy1 gi + dy2 gi                   =
        dy1 g  + dy2 g                      &
#W  w + dy1 gi + ct2 gi + free gi         =
        dy1 g  + ct2 g  + free g
].



Search _ scanl.
Lemma pA_B2A_inv wi si (s := foldl tB2A si wi) (wo := B2A_from si wi) :
  wi \in pBword -> exists d2 : nat, exists f : nat,
(#N  wo + si.1 + si.2 = #W wo + s.1 + s.2 + d2 + f) /\
(#Se wo + si.1 = #W wo + s.1 + d2).
Proof.
rewrite {}/s {}/wo; elim/last_ind: wi => [| w l ihw].
  by move=> _; exists 0; exists 0; rewrite /= !add0n !addn0.
move=> pBwl.
have /ihw [dw2 [fw]]: w \in pBword := pBword_rcons pBwl.
rewrite B2A_from_rcons !count_mem_rcons !foldl_rcons.
set wo := B2A_from si w; move: (foldl tB2A si w) => s [eN eSe].
case: l pBwl => /pBwordP h.
- case: s eN eSe=> [] [] [|c1] c2 /=.
  + rewrite eqxx /= !addn0 => eN eSe.
    by exists dw2.+1; exists fw; rewrite addSn -eN -eSe !addnS.
  + rewrite !andbF !eqxx /= !ltn_eqF //= !addnS !addSn => eN eSe.



Lemma B_final_state w : w \in Bword -> foldl tB2A {|0; 0|} (rev w) = {|0; 0|}.
Proof.
move=> Bw.
case/lastP: w Bw => [| w l] // Bw.
rewrite rev_rcons /=.

Goal forall s1 : state, forall w : seq letter, True.
move=> s1 w; have /= := bar s1 w.
Lemma A2Bout_tB2A s2 lo : A2Bout (tB2A s2 lo) s2 = lo.
Proof.
by case: lo; case: s2 => [] [[|c1][|c2]] //=; rewrite ?eqxx ?andbF //= ltn_eqF.
Qed.


Lemma rev_pairmap T (f : letter -> letter -> T) w li lf :
  rev (pairmap f li (rcons w lf)) =
  pairmap (fun x => f^~ x) lf (rcons (rev w) li).
Proof.
Search _ pairmap.
elim: w li lf => [|l w ihw] li lf //.
rewrite rcons_cons /= rev_cons {}ihw.
rewrite [in RHS]rev_cons.
 !rev_cons ihw.

Lemma foo w : B2A w = B2A w.
rewrite /=.

Lemma pA_gtA2B_inv w gi (g := foldl gtA2B gi w) :
  w \in pAword ->
  [/\
#N  w + dy1 gi + dy2 gi + ct1 gi + ct2 gi =
        dy1 g  + dy2 g  + ct1 g  + ct2 g   ,
#Se w + dy1 gi + dy2 gi                   =
        dy1 g  + dy2 g                      &
#W  w + dy1 gi + ct2 gi + free gi         =
        dy1 g  + ct2 g  + free g
].


Lemma pA_B2A_inv w1 w1 (s1 := foldl tB2A {|0; 0|} w1) (wo := B2A_from s1 w2) :
  w1 ++ w2 \in pBword -> exists d2 : nat, exists f : nat,
(#N  wo + si.1 + si.2 + d2 + f = #W wo + s.1 + s.2) /\
(#Se wo + si.1 + d2 = #W wo + s.1).
Proof.
rewrite {}/s {}/wo; elim/last_ind: wi => [| w l ihw].
  by move=> _; exists 0; exists 0; rewrite /= !add0n !addn0.
move=> pBwl.
have /ihw [dw2 [fw]]: w \in pBword := pBword_rcons pBwl.
rewrite B2A_from_rcons !count_mem_rcons !foldl_rcons.
set wo := B2A_from si w; move: (foldl tB2A si w) => s [eN eSe].
case: l pBwl => /pBwordP h.
- case: s eN eSe=> [] [] [|c1] c2 /=.
  + rewrite eqxx /= !addn0 => eN eSe.
    by exists dw2.+1; exists fw; rewrite addSn -eN -eSe !addnS.
  + rewrite !andbF !eqxx /= !ltn_eqF //= !addnS !addSn => eN eSe.



Lemma pA_B2A_inv wi si (s := foldl tB2A si wi) (wo := B2A_from si wi) :
  wi \in pBword -> exists d2 : nat, exists f : nat,
(#N  wo + si.1 + si.2 + d2 + f = #W wo + s.1 + s.2) /\
(#Se wo + si.1 + d2 = #W wo + s.1).
Proof.
rewrite {}/s {}/wo; elim/last_ind: wi => [| w l ihw].
  by move=> _; exists 0; exists 0; rewrite /= !add0n !addn0.
move=> pBwl.
have /ihw [dw2 [fw]]: w \in pBword := pBword_rcons pBwl.
rewrite B2A_from_rcons !count_mem_rcons !foldl_rcons.
set wo := B2A_from si w; move: (foldl tB2A si w) => s [eN eSe].
case: l pBwl => /pBwordP h.
- case: s eN eSe=> [] [] [|c1] c2 /=.
  + rewrite eqxx /= !addn0 => eN eSe.
    by exists dw2.+1; exists fw; rewrite addSn -eN -eSe !addnS.
  + rewrite !andbF !eqxx /= !ltn_eqF //= !addnS !addSn => eN eSe.


Lemma pA_B2A_inv wi si (s := foldl tB2A si wi) (wo := B2A_from si wi) :
  wi \in pBword -> exists d2 : nat, exists f : nat,
(#N  wo + si.1 + si.2 = #W wo + d2 + f + s.1 + s.2) /\
(#Se wo + si.1 = #W wo + d2 + s.1).
Proof.
rewrite {}/s {}/wo; elim/last_ind: wi => [| w l ihw].
  by move=> _; exists 0; exists 0; rewrite !add0n.
move=> pBwl.
have /ihw [dw2 [fw]]: w \in pBword := pBword_rcons pBwl.
rewrite B2A_from_rcons !count_mem_rcons !foldl_rcons.
set wo := B2A_from si w; move: (foldl tB2A si w) => s [eN eSe].
case: l pBwl => /pBwordP h.
- case: s eN eSe=> [] [] [|c1] c2 /=.
  + rewrite eqxx /= !addn0 => -> ->.



Definition tB2A (c : state) (l : letter) : state :=
  match l, c with
    | N,  {|0    ; c2   |} =>
          {|0    ; c2   |} (* (W,  {|0    ; c2   |}) *) (* _ , _  *)
    | Se, {|c1   ; c2.+1|} =>
          {|c1.+1; c2   |} (* (W,  {|c1.+1; c2   |}) *) (* +1, -1 *)
    | N,  {|c1.+1; c2   |} =>
          {|c1   ; c2   |} (* (N,  {|c1   ; c2   |}) *) (* -1, _  *)
    | W,  {|c1   ; c2   |} =>
          {|c1   ; c2.+1|} (* (Se, {|c1   ; c2.+1|}) *) (* _ , +1 *)
    | Se, {|c1   ; 0    |} =>
          {|c1.+1; 0    |} (* (Se, {|c1.+1; 0    |}) *) (* +1, _  *)
  end.

Definition B2Aout (ci cf : state) : letter :=
  let: {|cf1; cf2|} := cf in
  let: {|ci1; ci2|} := ci in
  if [&& cf1 == 0, ci1 == 0 & (ci2 == cf2)] then W
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then W
  else if (ci1 == cf1.+1) && (cf2 == ci2) then N
  (* else if (cf2 == ci2.+1) && (cf2 == ci2) then Se *)
  (* else if (cf1 == ci1.+1) && (cf2 == 0) && (ci2 == 0) then Se *)
  else Se (* junk *).




Definition gtB2A (g : gstate) (l : letter) : state :=
  match l, g with
    | N,  GState 0     c2    d1 d2 f =>
          GState 0     c2    d1 d2 f (* (W,  GState 0     c2   |}) *) (* _ , _  *)
    | Se, GState c1    c2.+1 d1 d2 f =>
          GState c1.+1 c2    d1 d2 f (* (W,  GState c1.+1 c2    d1 d2 f) *) (* +1, -1 *)
    | N,  GState c1.+1 c2    d1 d2 f =>
          GState c1    c2    d1 d2 f (* (N,  GState c1    c2   |}) *) (* -1, _  *)
    | W,  GState c1    c2    d1 d2 f =>
          GState c1    c2.+1 d1 d2 f (* (Se, GState c1    c2.+1|}) *) (* _ , +1 *)
    | Se, GState c1    0     d1 d2 f =>
          GState c1.+1 0     d1 d2 f (* (Se, {|c1.+1; 0    |}) *) (* +1, _  *)
  end.

   (* Similarly, words in B (or length 3*(k1 + k2) can be generated by taking: *)
   (* - a Dyck word d1 on (NSe, W) of lenght 3*k1 (the closing parenthesis is the *)
   (* concatenation of letters Se and W); *)
   (* - shuffled with a Dyck word d2 on (N, Se) of length 2*k2 (letters can be *)
   (* inserted between the adjacent N and Se of d1); *)
   (* - with k2 letters N arbitrarily inserted in the resulting entanglement of d1 *)
   (* and d2. *)

   (* An other way to generate words in A is by taking: *)
   (* - a Dyck word d1' on (NW, Se) of length 3*k1; *)
   (* - shuffled with a Dyck word d2' on (N, Se) of length 2*k2 (letters can be *)
   (* inserted between the adjacent N and Se of d1); *)
   (* - with k2 letters W arbitrarily inserted in the resulting entanglement of d1 *)
   (* and d2. *)



Definition AfromB  w :=
  pairmap A2Bout {|0; 0|}
          (rev (scanl tB2A {|0; 0|} (rev w))).

(* Definition AfromB l w := *)
(*   pairmap A2Bout (foldl tB2A {|0; 0|} (rcons (rev w) l)) *)
(*           (rev ({|0; 0|} :: (scanl tB2A {|0; 0|} (rev w)))). *)

Eval compute in AfromB [:: W; N; Se].
(* A few computations to see the translation at work: *)

Eval compute in A2B [:: N; W; Se]. (* [:: N; Se; W] *)
Eval compute in A2B [:: N; Se; W]. (* [:: N; Se; N] *)
Eval compute in A2B [:: W; N; Se]. (* [:: N; N; Se] *)


Eval compute in B2A [:: N; Se; W]. (* [:: N; W; Se] *)
Eval compute in B2A [:: N; Se; N]. (* [:: N; Se; W] *)
Eval compute in B2A [:: N; N; Se]. (* [:: W; N; Se] *)


Lemma foo :


(* ****)



Lemma B_final_state w : w \in Bword -> foldl tB2A {|0; 0|} (rev w) = {|0; 0|}.
Proof.
case: w => [| l w] // Blw.
rewrite rev_cons foldl_rcons.
move: (pB_gtB2A_inv (rev w) gb0); rewrite /= -(state_of_foldl_gtB2A _ 0 0 0 0) /=.
rewrite !count_rev !addn0.
move: (foldl _ _ _) => [] c1 c2 d1 d2 f o /= [eN eSe eW].
case/BwordP: Blw => _.
case: l => /=; rewrite !add0n !add1n eN eSe eW.
rewrite -![d1 + _ + _]addnA subnDl !addnA.
rewrite subSn; last admit.
rewrite subnDl.


case/lastP: w => [|w l] //.
case/BwordP=> pBwl eWl.
have pBw := pB_rcons pBwl.
rewrite rev_rcons /=.
have {pBwl} : #W (rcons w l) <= #Se (rcons w l) <= #N (rcons w l). admit.
move: eWl; rewrite !count_mem_rcons.
case: l => /= => e le.
  rewrite-[tB2A {|0; 0|} N]/({|0; 0|}).
  move: (pB_gtB2A_inv (rev w) g0); rewrite /= -(state_of_foldl_gtB2A _ 0 0 0) /= !addn0.
rewrite !count_rev. move: (foldl _ _ _) => [] c1 c2 d1 d2 f /= [eN eSe eW].
rewrite subnDl in e.
rewrite leq_add2l in le2.
move/(leq_sub2r c1): le2; rewrite subnn.



(* ok below *)
Definition gtB2A_ (g : gstate)  (l : letter) : gstate :=
match l, g with
  |W,  GState c1     c2    d o f  =>  GState c1     c2.+1     d    o    f
  |Se, GState c1     c2.+1 d o f  =>  GState c1.+1  c2        d    o.+1 f
  |Se, GState c1     0     d o f  =>  GState c1.+1  0         d    o    f
  |N,  GState c1.+1  c2    d o f  =>  GState c1     c2        d.+1 o    f
  |N,  GState 0      c2    d o f  =>  GState 0      c2        d    o    f.+1
end.

Definition gtB2A := nosimpl gtB2A_.

Lemma pB_gtB2A_inv w gi (g := foldl gtB2A gi w) :
  [/\
#N  w + dy1 gi + free gi =
        dy1 g  + free g   ,
#Se w + dy1 gi + ct1 gi  =
        dy1 g  + ct1 g                       &
#W  w + dy2 gi + ct2 gi =
        dy2 g  + ct2 g
].
Proof.
rewrite {}/g; elim/last_ind: w => [| w l] /= => //.
rewrite foldl_rcons /=; move: (foldl gtB2A gi w) => gf [eN eSe eW].
case: l; rewrite !count_mem_rcons !eqxx /=.
- rewrite !addSn {}eN {}eSe {}eW.
  by case: gf => [] [|c1] [|c2] d o f /=; rewrite !addnS.
- rewrite !addSn {}eN {}eSe {}eW.
  by case: gf => [] [|c1] [|c2] d o f /=; rewrite !addnS.
- rewrite !addSn {}eN {}eSe {}eW.
  by case: gf => [] [|c1] [|c2] d o f /=; rewrite !addnS.
Qed.

(* Lemma pB_gtB2A_inv w gi (g := foldl gtB2A gi (rev w)) : *)
(*   [/\ *)
(* #N  w + dy1 gi + free gi = *)
(*         dy1 g  + free g   , *)
(* #Se w + dy1 gi + ct1 gi  = *)
(*         dy1 g  + ct1 g                       & *)
(* #W  w + dy2 gi + ct2 gi = *)
(*         dy2 g  + ct2 g *)
(* ]. *)
(* Proof. *)
(* rewrite {}/g; elim/last_ind: w gi => [| w l ihw] /= gi => //. *)
(* rewrite rev_rcons /=. have {ihw} [<- <- <- ] := (ihw (gtB2A gi l)). *)
(* case: l; rewrite !count_mem_rcons !eqxx /=. *)
(* - by case: gi => [] [|c1] [|c2] d o f /=; rewrite !addnS !addSn ?addn0. *)
(* - by case: gi => [] [|c1] [|c2] d o f /=; rewrite !addnS !addSn ?addn0. *)
(* - by case: gi => [] [|c1] [|c2] d o f /=; rewrite !addnS !addSn ?addn0. *)
(* Qed. *)

Lemma state_of_foldl_gtB2A s d1 d2 f w (g := mkGState s d1 d2 f) :
  state_of_gstate (foldl gtB2A g w) = foldl tB2A s w.
Proof.
have -> : s = state_of_gstate g by rewrite {}/g; case: s => [] [].
elim: w g => [|h w ihw] //= g; rewrite {}ihw; congr foldl.
by case: g=> c1 c2* {w} /=; case: h => //=; case: c1 => * //; case: c2 => *.
Qed.

Lemma B_final_state w : w \in Bword -> foldl tB2A {|0; 0|} (rev w) = {|0; 0|}.
Proof.
case/BwordP=> pBw.
have /andP : #W w <= #Se w <= #N w.
  by move/pBwordP/(_ (size w)): pBw; rewrite take_size.
move: (pB_gtB2A_inv (rev w) g0); rewrite /= -(state_of_foldl_gtB2A _ 0 0 0) /= !addn0.
rewrite !count_rev; move: (foldl _ _ _) => [] c1 c2 d1 d2 f /= [-> -> ->] [le1 le2] /eqP e.
rewrite subnDl in e.

rewrite leq_add2l in le2.
move/(leq_sub2r c1): le2; rewrite subnn.



suff : (c1 == 0) && (c2 == 0) by case/andP=> /eqP-> /eqP->.
rewrite subnDl in e.
rewrite leq_add2l in le2.
move/(leq_sub2r c1): le2.
rewrite subnn.
rewrite leq_eqVlt.
case/orP=> h.
  rewrite -(eqP h) subn_eq0 in e. admit.
move: h. rewrite -(eqP e) subn_gt0.
Search _ (_ - _ > 0).

apply: contraLR e.
rewrite -addnA addnC; move/(canRL (addnK _)); rewrite subnn.
by case: c1 => [|?] //; case: c2.
Qed.

Theorem A2BK : {in Aword, cancel A2B B2A}.
Proof. apply: A2BK_; [exact: pA_noex | exact: A_final_state]. Qed.
 *)