From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice tuple fintype (* finfun finset *).

Require Import extra_seq.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*-- 3 Letter alphabet --*)

(* Type letter is the three-letter alphabet of the words we want to count.
   The names of the letters reminds how they will be interpreted as
   (the direction of) small letter moves on a grid.*)

Inductive letter : Type := N | W | Se.

(* Starting boilerplate code: *)

(* Type letter has a canonical decidable equality test, is a countable (finite)
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

(*-- Two families of words --*)

(* By definition, a word w is a pre_Motzkin word on alphabet 'letter' iff:
   - for any prefix p of w, #Se p <= #N p

   By definition, a word w is a Motzkin word on alphabet 'letter' iff:
   - it is a pre_Motzkin word and moreover:
   - #N w = #Se w = #W w
 *)


(* In order to define pre_Motzkin as a boolean predicate on words,
  we use a bounded quantification, over prefixes of length smaller
  that the size of the list. *)

Definition pre_Motzkin (w : seq letter) : bool :=
  [forall n : 'I_(size w).+1, #Se (take n w) <= #N (take n w)].

(* But this quantification is in fact a technical device, and we
   prove the equivalence with the usual quantification*)
Lemma pre_MotzkinP w :
  reflect (forall n : nat, #Se (take n w) <= #N (take n w)) (w \in pre_Motzkin).
Proof.
apply: (iffP forallP) => [/(_ (Ordinal _)) h| ?] n //.
case: (ltnP n (size w).+1) => [| /ltnW/take_oversize->]; first exact: h.
by rewrite -(take_size w); apply: h.
Qed.

(* The empty word is a pre_Motzkin *)
Lemma pre_Motzkin_nil : [::] \in pre_Motzkin.
Proof. by apply/pre_MotzkinP=> n. Qed.

(* A prefix of a pre_Motzkin is itself a pre_Motzkin *)
Lemma pre_Motzkin_rcons a w : rcons w a \in pre_Motzkin  -> w \in pre_Motzkin.
Proof.
move/pre_MotzkinP=> pAla; apply/forallP=> [] [n ?].
by move: (pAla n); rewrite -cats1 takel_cat.
Qed.

Arguments pre_Motzkin_rcons a {w} _.


Lemma pre_Motzkin_rcons_Se w : rcons w Se \in pre_Motzkin  -> #Se w < #N w.
Proof.
move/pre_MotzkinP/(_ (size w).+1); rewrite -(size_rcons w Se) take_size.
by rewrite !count_mem_rcons eqxx.
Qed.

Lemma pre_Motzkin_take n w : w \in pre_Motzkin  -> take n w \in pre_Motzkin.
Proof. exact: (rcons_2_taken pre_Motzkin_nil pre_Motzkin_rcons). Qed.

Definition Motzkin (w : seq letter) : bool :=
  [&& (pre_Motzkin w), #N w == #Se w & #Se w == #W w].

Lemma MotzkinP w :
  reflect [/\ w \in pre_Motzkin, #N w = #Se w & #Se w = #W w] (w \in Motzkin).
Proof. by apply: (iffP and3P); case=> pAw /eqP-> /eqP->. Qed.

Lemma pre_Motzkin_Motzkin l : l \in Motzkin -> l \in pre_Motzkin.
Proof. by case/and3P. Qed.


(* By definition, a word w on alphabet 'letter' is a Yamanouchi word if
  any of its prefixes has less occurrences of W than occurrences of Se,
  and less occurrences of Se than occurrences of N.

  Such a word is a balanced Yamanouchi word if it is a Yamanouchi word
  w such that
   - #Se w - #W w = #N w - #Se w
*)

(* In order to define Yamanouchi as a boolean predicate on words,
  we use a bounded quantification, over prefixes of length smaller
  that the size of the list. *)

Definition Yamanouchi (w : seq letter) : bool :=
  [forall n : 'I_(size w).+1, #W (take n w) <= #Se (take n w) <= #N (take n w)].

(* But this quantification is in fact a technical device, and we
   prove the equivalence with the usual quantification*)
Lemma YamanouchiP w :
  reflect (forall n : nat, #W (take n w) <= #Se (take n w) <= #N (take n w))
          (w \in Yamanouchi).
Proof.
apply: (iffP forallP) => [/(_ (Ordinal _)) h| ?] n //.
case: (ltnP n (size w).+1) => [| /ltnW/take_oversize->]; first exact: h.
by rewrite -(take_size w); apply: h.
Qed.

Lemma Yamanouchi_nil : [::] \in Yamanouchi.
Proof. by apply/YamanouchiP=> n. Qed.

Lemma Yamanouchi_rcons l w : rcons w l \in Yamanouchi  -> Yamanouchi w.
Proof.
move/YamanouchiP=> Yam_wl; apply/forallP=> [] [n hn] /=.
by move: (Yam_wl n); rewrite -cats1 takel_cat.
Qed.

Arguments Yamanouchi_rcons l {w} _.

Lemma Yamanouchi_take n w : w \in Yamanouchi  -> take n w \in Yamanouchi.
Proof. exact: (rcons_2_taken Yamanouchi_nil Yamanouchi_rcons). Qed.

Definition balanced_Yam (w : seq letter) : bool :=
  [&& (w \in Yamanouchi) & #Se w - #W w == #N w - #Se w].

Lemma balanced_YamP (w : seq letter) :
  reflect (w \in Yamanouchi /\ #Se w - #W w = #N w - #Se w) (w \in balanced_Yam).
Proof.
Proof. by apply: (iffP andP); case=> pAw /eqP->. Qed.

Lemma Yam_balanced_Yam w : w \in balanced_Yam -> w \in Yamanouchi.
Proof. by case/andP. Qed.



(* (Motzkin_tuple n) (resp. (balanced_Yam n)) is the type of Motzkin
   (resp. balanced Yamanouchi) words on alphabet letter. *)
Definition Motzkin_tuple n : pred (n.-tuple letter) :=
 [pred w : n.-tuple letter | Motzkin w].

Arguments Motzkin_tuple n _ : clear implicits.

Definition balanced_Yam_tuple n : pred (n.-tuple letter) :=
 [pred w : n.-tuple letter | balanced_Yam w].

Arguments balanced_Yam_tuple n _ : clear implicits.

(* We want to prove that for any n, there is the same number of Motzkin words
   of size n than of balanced Yamanouchi words of size n. We proceed by
   showing that:
   - for a Motzkin word, M2bY (bY2M w) = w
   - for a Motzkin word, (bY2M w) is a balanced Yamanouchi word
   - for a balanced Yamanouchi word, bY2M (M2bY w) = w
   - for a balanced Yamanouchi word, (M2bY w) is a Motzkin word
*)

Section CardinalsEquality.

Variables bY2M_ M2bY_ : seq letter -> seq letter.

Hypothesis size_M2bY_ : forall w : seq letter, size (M2bY_ w) = size w.
Hypothesis size_bY2M_ : forall w : seq letter, size (bY2M_ w) = size w.

(* Suppose that for a balanced Yamanouchi word, bY2M (M2bY w) = w *)
Hypothesis M2bYK : {in balanced_Yam, cancel bY2M_ M2bY_}.

(* Suppose that  for a Motzkin word, M2bY (bY2M w) = w *)
Hypothesis bY2MK : {in Motzkin, cancel M2bY_ bY2M_}.

(* Suppose that for a Motzkin word, (bY2M w) is a balanced Yamanouchi word *)
Hypothesis bYam_M2bY : forall w, w \in Motzkin -> M2bY_ w \in balanced_Yam.

(* for a balanced Yamanouchi word, (M2bY w) is a Motzkin word *)
Hypothesis Motz_bY2M : forall w, w \in balanced_Yam -> bY2M_ w \in Motzkin.

(* Let n be an arbitrary size *)
Variable n : nat.

(* Then we get the desired equality *)
Lemma eq_card_Motzkin_bYam_suff : #|Motzkin_tuple n| = #|balanced_Yam_tuple n|.
Proof.
have size_M2bYt (w : n.-tuple letter) : size (M2bY_ w) == n.
  by rewrite size_M2bY_ size_tuple.
have size_bY2Mt (w : n.-tuple letter) : size (bY2M_ w) == n.
  by rewrite size_bY2M_ size_tuple.
pose M2bYt (w : n.-tuple letter) : n.-tuple letter := Tuple (size_M2bYt w).
pose bY2Mt (w : n.-tuple letter) : n.-tuple letter := Tuple (size_bY2Mt w).
have sub_bY : [seq M2bYt x | x in Motzkin_tuple n] \subset balanced_Yam_tuple n.
  by apply/subsetP=> w /imageP [? ? ->]; apply: bYam_M2bY.
have sub_M : [seq bY2Mt x | x in balanced_Yam_tuple n] \subset Motzkin_tuple n.
  by apply/subsetP=> w /imageP [? ? ->]; apply: Motz_bY2M.
apply/eqP; rewrite eqn_leq.
have /card_in_image {1}<- : {in Motzkin_tuple n &, injective M2bYt}.
  case=> [s sizes] [t sizet] /bY2MK /= Ms /bY2MK /= Mt [] est; apply/val_inj.
  by rewrite /= -Ms -Mt est.
suff /card_in_image {2}<- : {in balanced_Yam_tuple n &, injective bY2Mt}.
  by rewrite !subset_leq_card.
case=> [s sizes] [t sizet] /M2bYK /= bYs /M2bYK /= bYt [] est; apply/val_inj.
by rewrite /= -bYs -bYt est.
Qed.

End CardinalsEquality.

(* We want to show that for a given n, the number of Motzkin words of size n
   is the same as the number of balanced Yamanouchi words of size n.
   For this purpose, we construct a size-preserving bijection between the
   collection of words in Motzkin and the collection of words in balanced_Yam.

   Intuitively (this is not proved formally), Motzkin words (of length 3*k)
   can be generated by taking:
   - a Dyck word d on (N, Se) of length 2*k;
   - with k letters W arbitrarily inserted in d.

   Similarly, balanced Yamanouchi words (of length 3*(k1 + k2)
   can be generated by taking:
   - a (pseudo-)Dyck word d1 on (NSe, W) of length 3*k1, whose opening
   parenthesis is the concatenation of letters N and Se;
   - shuffled with a Dyck word d2 on (N, Se) of length 2*k2 (letters can be
   inserted between the adjacent N and Se of the left parenthesis of d1);
   - with k2 letters N arbitrarily inserted in the resulting entanglement of d1
   and d2.

   An other way to generate Motzkin words is by taking:
   - a (pseudo)Dyck word d1' on (NW, Se) of length 3*k1, whose opening
   parenthesis is the concatenation of letters N and W;
   - shuffled with a Dyck word d2' on (N, Se) of length 2*k2 (letters can be
   inserted between the adjacent N and Se of d1);
   - with k2 letters W arbitrarily inserted in the resulting entanglement of d1
   and d2.

   But unfortunately these generating processes do not provide unique
   factorizations.

   We construct a function M2bY : seq letter -> seq letter such that if w is in
   Motzkin, then there is a factorization of w as a pseudo-Dyck word d1
   on (NW, Se) and a Dyck word d2 on (N, Se) such that d1 is transformed into
   a pseudo-Dyck word d1' on (NSe, W), d2 stays unchanged, and the k remaining
   occurrences of W are changed to Ns. We also define a candidate converse
   function bY2M : seq letter -> seq letter and show that:
   - M2bY and bY2M preserve the size of their arguments;
   - for a Motzkin word, M2bY (bY2M w) = w
   - for a Motzkin word, (bY2M w) is a balanced Yamanouchi word
   - for a balanced Yamanouchi word, bY2M (M2bY w) = w
   - for a balanced Yamanouchi word, (M2bY w) is a Motzkin word
   This is enough to conclude that M2bY and bY2M realize a (family of)
   bijection(s) between Motzkin words (of size n) and balanced Yamanouchi words
   (of size n).

   Each of the functions M2bY and bY2M is defined by the mean of an (infinite)
   automaton, with transitions labeled with pairs letters. The states
   of the automata are labeled with pairs of (natural) numbers, with
   initial state (0, 0). This counters are useful to implement the
   prioritized recognition of (pseudo)Dyck words. The pair of letters
   labeling a transition are seen as the pair of an input letter and
   an output letter, and each automaton is a transducer: we are in
   fact not much interested by the state reached after reading an
   input word from the initial state, although we show that Motzkin
   (resp. Yamanouchi) words are recognized by the automaton, which has
   (0, 0) as final state. Indeed, the output word is in fact the value
   of the function M2bY (resp. bY2M) on the input word.

  The transducer which is used to implement bY2M is obtained from the
  transducer which is used to implement M2bY, by both reversing the arrows and
  the order in the pairs of letters labeling the transitions.

  In the sequel, we use the name M2bY and bY2M to refer both to the transducers
  and to the corresponding functions.
*)


(*--- Transducers and bijection(s) ---*)

(* Data structure for states of the transducers: a tagged copy of nat * nat.*)
Inductive state := State of nat * nat.

Notation "'{|' c1 ; c2 '|}'" := (State (c1, c2)).

(* We coerce type state to nat * nat *)

Coercion nat2_of_state s : (nat * nat) := let: State c := s in c.

(* The transition function of the transducer t_M2bY:
   t_M2bY c l is the state reached when reading l from c (and here we do not
   explicit the letter output when this transition is performed). *)
Definition t_M2bY (c : state) (l : letter) : state :=
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

Arguments t_M2bY c l : simpl never.

(* Similarly, the transition function of the transducer t_bY2M *)
Definition t_bY2M (c : state) (l : letter) : state :=
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

Arguments t_bY2M c l : simpl never.

(* (M2bY_state c w) (resp. (bY2M_state c w) is the state
 reached when reading w from c in the transducer M2bY (resp. bY2M)*)
Definition M2bY_state (c : state) (w : seq letter) : state :=
  foldl t_M2bY c w.

Definition bY2M_state (c : state) (w : seq letter) : state :=
  foldl t_bY2M c w.

(* Properties of M2bY_state (resp. bY2M_state) inherited from those of foldl *)

(*The state reached from c after reading  (rcons w l) is the one reached from
  "the state reached from c after reading w" after reading l *)
Lemma M2bY_state_rcons (c : state) (w : seq letter) (l : letter) :
  M2bY_state c (rcons w l) = t_M2bY (M2bY_state c w) l.
Proof. exact: foldl_rcons. Qed.

Lemma bY2M_state_rcons (c : state) (w : seq letter) (l : letter) :
  bY2M_state c (rcons w l) = t_bY2M (bY2M_state c w) l.
Proof. exact: foldl_rcons. Qed.

(*The state reached from c after reading  (w1 ++ w2) is the one reached from
  "the state reached from c after reading w1" after reading w2 *)

Lemma M2bY_state_cat (c : state) (w1 w2 : seq letter) :
  M2bY_state c (w1 ++ w2) = M2bY_state (M2bY_state c w1) w2.
Proof. exact: foldl_cat. Qed.

Lemma bY2M_state_cat (c : state) (w1 w2 : seq letter) :
  bY2M_state c (w1 ++ w2) = bY2M_state (bY2M_state c w1) w2.
Proof. exact: foldl_cat. Qed.

(* *_state functions in terms of foldr. Don know yet if is usefull. *)
Lemma M2bY_state_rev (c : state) (w : seq letter) :
  M2bY_state c (rev w) = foldr (fun x => t_M2bY^~ x) c w.
Proof. exact: foldl_rev. Qed.

Lemma bY2M_state_rev (c : state) (w : seq letter) :
  bY2M_state c (rev w) = foldr (fun x => t_bY2M^~ x) c w.
Proof. exact: foldl_rev. Qed.


(* (M2bY_states_seq c w) (resp. (bY2M_states c w) is the sequence of states
 followed when reading w from c in the transducer M2bY (resp. bY2M)*)
Definition M2bY_states_seq (c : state) (w : seq letter) : seq state :=
  scanl t_M2bY c w.

(* Arguments M2bY_states_seq / c w. *)

Definition bY2M_states_seq  (c : state) (w : seq letter) : seq state :=
  scanl t_bY2M c w.

(* Arguments bY2M_states_seq / c w. *)


(* Properties of M2bY_states_seq (resp. bY2M_states_seq) obtained from those of
  scanl. *)
Lemma last_M2bY_states_seq (c : state) (w : seq letter) :
  last c (M2bY_states_seq c w) = M2bY_state c w.
Proof. exact: last_scanl. Qed.

Lemma M2bY_states_seq_rcons (c : state) (w : seq letter) (l : letter) :
  M2bY_states_seq c (rcons w l) =
  rcons (M2bY_states_seq c w) (M2bY_state c (rcons w l)).
Proof. exact: scanl_rcons. Qed.

Lemma take_M2bY_states_seq (c : state) (w : seq letter) (n : nat) :
take n (M2bY_states_seq c w) = M2bY_states_seq c (take n w).
Proof. exact: take_scanl. Qed.

Lemma size_M2bY_states_seq c w : size (M2bY_states_seq c w) = size w.
Proof. by rewrite  size_scanl. Qed.

Lemma M2bY_states_seq_cat c w1 w2 :
  M2bY_states_seq c (w1 ++ w2) =
  M2bY_states_seq c w1 ++ M2bY_states_seq (M2bY_state c w1) w2.
Proof. exact: scanl_cat. Qed.

Lemma last_bY2M_states_seq (c : state) (w : seq letter) :
  last c (bY2M_states_seq c w) = bY2M_state c w.
Proof. exact: last_scanl. Qed.

Lemma bY2M_states_seq_rcons (c : state) (w : seq letter) (l : letter) :
  bY2M_states_seq c (rcons w l) =
  rcons (bY2M_states_seq c w) (bY2M_state c (rcons w l)).
Proof. exact: scanl_rcons. Qed.

Lemma take_bY2M_states_seq (c : state) (w : seq letter) (n : nat) :
take n (bY2M_states_seq c w) = bY2M_states_seq c (take n w).
Proof. exact: take_scanl. Qed.

Lemma size_bY2M_states_seq c w : size (bY2M_states_seq c w) = size w.
Proof. by rewrite  size_scanl. Qed.

Lemma bY2M_states_seq_cat c w1 w2 :
  bY2M_states_seq c (w1 ++ w2) =
  bY2M_states_seq c w1 ++ bY2M_states_seq (bY2M_state c w1) w2.
Proof. exact: scanl_cat. Qed.

(* Crucially, for any two states cf and ci, there is a transition in
   transducer M2bY (resp. bY2M) from state ci to state cf, and the output
   letter is unique. We call this letter (M2bY_out ci cf)
   (resp. (bY2Mout ci cf)). There is one exception, in transducer M2bY,
   when ci = cf = (0, 0), in which case we we consider that the input letter
   wasn't Se. *)

Definition M2bY_out (ci cf : state) : letter :=
  let: {|cf1; cf2|} := cf in
  let: {|ci1; ci2|} := ci in
  if [&& cf1 == 0, ci1 == 0 & (cf2 == ci2)] then N
  else if (ci1 == cf1.+1) && (cf2 == ci2.+1) then Se
  else if (cf1 == ci1.+1) && (cf2 == ci2) then N
  else if (cf1 == ci1) && (ci2 == cf2.+1) then W
  else Se.

Definition bY2M_out (ci cf : state) : letter :=
  let: {|cf1; cf2|} := cf in
  let: {|ci1; ci2|} := ci in
  if [&& cf1 == 0, ci1 == 0 & (ci2 == cf2)] then W
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then W
  else if (ci1 == cf1.+1) && (cf2 == ci2) then N
  else Se (* junk *).

(* It may be useful to name the analogues of these, just swapping arguments,
   in order to describe the reverse path in the automaton. *)
Definition M2bY_outV ci cf := M2bY_out cf ci.

Definition bY2M_outV cf ci := bY2M_out ci cf.

(* M2bY (resp. bY2M) is defined from t_M2bY and M2bY_out
  (resp. t_bY2M and bY2M_out) as follows:
   - from a word w and an intial state c, produce the sequence of states
     (M2bY_states_seq c w) (resp.  (bY2M_states_seq c w));
   - from sequence (M2bY_states_seq c w) (resp.  (bY2M_states_seq c w)), produce
    the sequence of corresponding output letters, using bY2M_out
    (resp. M2bY_out).
M2bY and bY2M take (0, 0) as initial state c.
*)

Definition M2bY_from (c : state) (w : seq letter) : seq letter :=
  pairmap M2bY_out c (M2bY_states_seq c w).

Arguments M2bY_from / c w : simpl never.

Definition M2bY := M2bY_from {|0; 0|}.

Arguments M2bY / : simpl never.

Definition bY2M_from (c : state) (w : seq letter) : seq letter :=
  pairmap bY2M_out c (bY2M_states_seq c w).

Arguments bY2M_from / c w : simpl never.

Definition bY2M (w : seq letter) := rev (bY2M_from {|0; 0|} (rev w)).

Arguments bY2M / w : simpl never.

(* A few computations to see the translation at work: *)

Eval compute in M2bY [:: N; W; Se]. (* [:: N; Se; W] *)
Eval compute in M2bY [:: N; Se; W]. (* [:: N; Se; N] *)
Eval compute in M2bY [:: W; N; Se]. (* [:: N; N; Se] *)


Eval compute in bY2M [:: N; Se; W]. (* [:: N; W; Se] *)
Eval compute in bY2M [:: N; Se; N]. (* [:: N; Se; W] *)
Eval compute in bY2M [:: N; N; Se]. (* [:: W; N; Se] *)


(* Properties of M2bY_from and M2bY (resp. bY2M_from, bY2M) obtained from those
 of pairmap (resp. pairmap and rev) *)

Lemma size_M2bY_from c w : size (M2bY_from c w) = size w.
Proof. by rewrite /M2bY_from size_pairmap size_M2bY_states_seq. Qed.

Lemma size_M2bY w : size (M2bY w) = size w.
Proof. by exact: size_M2bY_from. Qed.

Lemma M2bY_from_cat c w1 w2 :
  M2bY_from c (w1 ++ w2) = M2bY_from c w1 ++ M2bY_from (M2bY_state c w1) w2.
Proof.
by rewrite [LHS]/M2bY_from M2bY_states_seq_cat pairmap_cat last_M2bY_states_seq.
Qed.

Lemma M2bY_from_rcons c w l :
  M2bY_from c (rcons w l) =
  rcons (M2bY_from c w) (M2bY_out (M2bY_state c w) (t_M2bY (M2bY_state c w) l)).
Proof. by rewrite -cats1 M2bY_from_cat cats1. Qed.

Lemma take_M2bY_from c w n : take n (M2bY_from c w) = M2bY_from c (take n w).
Proof. by rewrite take_pairmap take_M2bY_states_seq. Qed.

Lemma take_M2bY w n : take n (M2bY w) = M2bY (take n w).
Proof. exact: take_M2bY_from. Qed.

Lemma rev_M2bY_from c w l :
  rev (M2bY_from c (rcons w l)) =
  pairmap M2bY_outV (t_M2bY (M2bY_state c w) l)
  (rcons (rev (M2bY_states_seq c w)) c).
Proof.
by rewrite /M2bY_from M2bY_states_seq_rcons rev_pairmap M2bY_state_rcons.
Qed.

Lemma M2bY_from_cons c w l :
  M2bY_from c (l :: w) = M2bY_out c (t_M2bY c l) :: M2bY_from (t_M2bY c l) w.
Proof. by []. Qed.

Lemma M2bY_rcons  w l (c := M2bY_state {|0; 0|} w) :
  M2bY (rcons w l) = rcons (M2bY w) (M2bY_out c (t_M2bY c l)).
Proof. by rewrite /M2bY M2bY_from_rcons. Qed.

Lemma size_bY2M_from c w : size (bY2M_from c w) = size w.
Proof. by rewrite /bY2M_from size_pairmap size_bY2M_states_seq. Qed.

Lemma size_bY2M w : size (bY2M w) = size w.
Proof. by rewrite size_rev size_bY2M_from size_rev. Qed.

Lemma bY2M_from_cat c w1 w2 :
  bY2M_from c (w1 ++ w2) = bY2M_from c w1 ++ bY2M_from (bY2M_state c w1) w2.
Proof.
by rewrite [LHS]/bY2M_from bY2M_states_seq_cat pairmap_cat last_bY2M_states_seq.
Qed.

Lemma bY2M_from_rcons c w l :
  bY2M_from c (rcons w l) =
  rcons (bY2M_from c w) (bY2M_out (bY2M_state c w) (t_bY2M (bY2M_state c w) l)).
Proof. by rewrite -cats1 bY2M_from_cat cats1. Qed.

Lemma take_bY2M_from c w n : take n (bY2M_from c w) = bY2M_from c (take n w).
Proof. by rewrite take_pairmap take_bY2M_states_seq. Qed.

Lemma take_bY2M w n :
  take n (bY2M w) =
  rev (bY2M_from (bY2M_state {|0; 0|} (rev (drop n w))) (rev (take n w))).
Proof.
case: (ltnP n (size w)) => [ltns | lesn]; last first.
  by rewrite [in RHS]take_oversize // drop_oversize //= take_oversize ?size_bY2M.
rewrite -[in LHS](cat_take_drop n w) /bY2M rev_cat bY2M_from_cat rev_cat.
by rewrite take_size_cat // size_rev size_bY2M_from size_rev size_take ltns.
Qed.

Lemma rev_bY2M_from c w l :
  rev (bY2M_from c (rcons w l)) =
  pairmap bY2M_outV (t_bY2M (bY2M_state c w) l)
  (rcons (rev (bY2M_states_seq c w)) c).
Proof.
by rewrite /bY2M_from bY2M_states_seq_rcons rev_pairmap bY2M_state_rcons.
Qed.

Lemma bY2M_from_cons c w l (cf := bY2M_state c (rev w)) :
  bY2M_from c (l :: w) =  bY2M_out c (t_bY2M c l) :: bY2M_from (t_bY2M c l) w.
Proof. by []. Qed.

Lemma bY2M_cons w l (c := bY2M_state {|0; 0|} (rev w)) :
  bY2M (l :: w) = (bY2M_out c (t_bY2M c l)) :: (bY2M w).
Proof. by rewrite /bY2M rev_cons bY2M_from_rcons rev_rcons. Qed.


(* Now we start studying the various transition functions that we defined per se.
   In particular, we prove various forms of cancellation properties that will
   hopefully get lifted as properties of the input/output words of the
   transducers. *)

Lemma M2bY_out_t_bY2M c lo : M2bY_out (t_bY2M c lo) c = lo.
Proof.
by case: lo; case: c => [] [[|c1][|c2]] //=; rewrite ?eqxx ?andbF //= ltn_eqF.
Qed.

Lemma  t_bY2MK s2 : cancel (t_bY2M s2) (M2bY_outV s2).
Proof. exact: M2bY_out_t_bY2M. Qed.

Lemma bY2M_states_seqKV c w : pairmap M2bY_outV c (bY2M_states_seq c w) = w.
Proof. by rewrite (scanlK t_bY2MK). Qed.

(* But there is one degenerated case, which prevents the expected converse
   identities to hold everywhere *)
Definition noex  (l : letter) (c : state) :=
   [|| (c.1 != 0%N), (c.2 != 0%N) | (l != Se)].

Lemma bY2M_out_t_M2bY c l : noex l c -> bY2M_out (t_M2bY c l) c = l.
Proof.
by case: l; case: c => [] [[|c1][|c2]] //= _; rewrite ?eqxx ?andbF //= ltn_eqF.
Qed.

(* t_bY2M c2 lo = c1 -> l = bY2M_out c2 c1 -> t_M2bY c1 l = c2. *)
Lemma t_M2bY_round c2 l (c1 := t_bY2M c2 l) : t_M2bY c1 (bY2M_out c2 c1) = c2.
Proof.
rewrite {}/c1. (* the c1 abbreviation is really for the sake of readability *)
by case: c2 => [] [[|?] [|?]]; case: l => //=; rewrite ?eqxx ?andbF 1?ltn_eqF.
Qed.

(* t_M2bY c1 li = c2 -> lo = M2bY_out c1 c2 -> t_bY2M c2 lo = c1. *)
Lemma t_bY2M_round c1 l (c2 := t_M2bY c1 l) : t_bY2M c2 (M2bY_out c1 c2) = c1.
Proof.
rewrite {}/c2. (* the c2 abbreviation is really for the sake of readability *)
by case: c1 => [] [] [|?] [|?]; case: l => //=; rewrite ?eqxx ?andbF // ltn_eqF.
Qed.

(* Let c1 be such that (c2)  -- l --> (c1) in automaton bY2M
   Then (c1) -- l --> (t_M2bY c1 (bY2M_out c2 c1)) in automaton M2bY. *)
Lemma M2bY_out_round c2 l (c1 := t_bY2M c2 l) :
  M2bY_out c1 (t_M2bY c1 (bY2M_out c2 c1)) = l.
Proof. by rewrite t_M2bY_round {}/c1 M2bY_out_t_bY2M. Qed.

(* Let  c2 be such that (c1)  -- l --> (c2) in automaton M2bY.
   Then (c2) -- l --> (t_bY2M s2 (M2bY_out c1 c2)) in automaton bY2M *)
Lemma bY2M_out_round c1 l (c2 := t_M2bY c1 l) : noex l c1 ->
  bY2M_out c2 (t_bY2M c2 (M2bY_out c1 c2)) = l.
Proof. by move=> nx; rewrite t_bY2M_round bY2M_out_t_M2bY. Qed.

(* Let cf be the state reached when starting from state ci and reading word wi
   with automaton bY2M. Let wf := (bY2M_from ci wi) be the word output. Then
   reading (rev wf) from cf with automaton M2bY produces word wi *)

Lemma revbY2M_fromK wi ci (cf := bY2M_state ci wi) (wf := bY2M_from ci wi) :
    M2bY_from cf (rev wf) = rev wi.
Proof.
rewrite {}/cf {}/wf; elim/last_ind: wi ci => [| w l ihw c] //=.
rewrite bY2M_state_rcons bY2M_from_rcons !rev_rcons /= M2bY_from_cons.
by rewrite M2bY_out_round t_M2bY_round ihw.
Qed.


(*--- Reduction: we prove that the conditions on M2bY, bY2M can be reduced to
  assumptions on the states of the transducer(s), whose proofs require
  introducing ghost variables to state and establish suitable invariants. ---*)


Section SufficientConditionsForCancel.

(* We leave as (temporary) hypotheses the facts that requires introducing
   ghost variables: *)

Hypothesis pre_Motzkin_noex : forall l w c,
   rcons l w \in pre_Motzkin -> noex w (M2bY_state c l).

Lemma revM2bY_fromK l c : l \in pre_Motzkin ->
    rev (bY2M_from (M2bY_state c l) (rev (M2bY_from c l))) = l.
Proof.
elim/last_ind: l c => [| w l ihw c pMwl] //=.
rewrite M2bY_state_rcons M2bY_from_rcons !rev_rcons.
rewrite bY2M_from_cons bY2M_out_round; last exact: pre_Motzkin_noex.
rewrite t_bY2M_round rev_cons ihw //; exact: (pre_Motzkin_rcons l).
Qed.

Hypothesis Motzkin_final_state : forall w,
  w \in Motzkin -> M2bY_state {|0; 0|} w = {|0; 0|}.

Lemma M2bYK_ : {in Motzkin, cancel M2bY bY2M}.
Proof.
move=> w Mw; rewrite /bY2M -(Motzkin_final_state Mw); apply: revM2bY_fromK.
exact: pre_Motzkin_Motzkin.
Qed.

Hypothesis bYam_final_state : forall w,
  w \in balanced_Yam -> bY2M_state {|0; 0|} (rev w) = {|0; 0|}.

Lemma bY2MK_ : {in balanced_Yam, cancel bY2M M2bY}.
Proof.
by move=> l Bl; rewrite /M2bY -(bYam_final_state Bl) /bY2M revbY2M_fromK ?revK.
Qed.

End SufficientConditionsForCancel.

(*--- Invariant of the M2bY transducer, by decoration with ghost variables. This
      proves the two remaining facts about (pre)Motzkin words, plus the important
      missing property of M2bY : that a Motzkin word is mapped to a  balanced
      Yamanouchi ---*)

(* The states of the automaton are augmented with 3 more natural numbers, that
   count respectively: the number of Dyck words (N, Se) processed so far (d1);
   the number of pseudo-Dyck words (NSe, W) in progress so
   far (d2); the number of "free" occurrences of W processed so far (f). These
   numbers are here to retain an information which is otherwise lost during
   computation, but they do not interfere with the computation nor its result.
   Hence we coin these extra data "ghost variables", as in the vocabulary of
   program verification. *)

Record gstate :=
  GState {ct1: nat; ct2: nat; dy1 : nat; dy2 : nat; free : nat}.

Definition mkGState (c : state) (d1 d2 f : nat) : gstate :=
  GState c.1 c.2 d1 d2 f.

Let g0 := GState 0 0 0 0 0.

Definition state_of_gstate (g : gstate) : state :=
  let: GState c1 c2 _ _ _ := g in State (c1, c2).

(* Last case is junk *)
Definition gt_M2bY_ (g : gstate)  (l : letter) : gstate :=
match l, g with
  |W,  GState 0     c2    d1 d2 f  =>  GState 0     c2     d1    d2    f.+1
  |W,  GState c1.+1 c2    d1 d2 f  =>  GState c1    c2.+1  d1    d2    f
  |N,  GState c1    c2    d1 d2 f  =>  GState c1.+1 c2     d1    d2    f
  |Se, GState c1    c2.+1 d1 d2 f  =>  GState c1    c2     d1.+1 d2    f
  |Se, GState c1.+1 0     d1 d2 f  =>  GState c1    0      d1    d2.+1 f
  |Se, GState 0     0     d1 d2 f  =>  GState 0     0      d1    d2    f
end.

Definition gt_M2bY := nosimpl gt_M2bY_.

Definition M2bY_gstate := foldl gt_M2bY.

Lemma M2bY_gstate_rcons (g : gstate) (w : seq letter) (l : letter) :
  M2bY_gstate g (rcons w l) = gt_M2bY (M2bY_gstate g w) l.
Proof. exact: foldl_rcons. Qed.
(* Forgeting the ghost information in a list of reached states *)

Lemma state_of_gt_M2bY g l :
  state_of_gstate (gt_M2bY g l) = t_M2bY (state_of_gstate g) l.
Proof. by case: g => [[| ?] [|?]] /=; case: l. Qed.

Lemma state_of_M2bY_gstate c d1 d2 f w (g := mkGState c d1 d2 f) :
  state_of_gstate (M2bY_gstate g w) = M2bY_state c w.
Proof.
have -> : c = state_of_gstate g by rewrite {}/g; case: c => [] [].
by elim: w g => [|h w ihw] //= g; rewrite {}ihw state_of_gt_M2bY.
Qed.

(* First invariant for gt_M2bY: it provides equations relating the number of
   occurrences of each letter in the *input* word with the values of the state
   reached after reading this word.

   Proof is by brute force case analysis excepy for the only
   interesting case of the (tail) induction on w is, i.e. when it ends with Se:
   in this case the hypothesis (pre_Motzkin (rcons l Se)) forbids
   ct1 c = ct2 c = 0.
   We need to kind of reproduce this proof outside this one to ensure we never hit
   this  exceptional case... Can we do better? *)

Lemma pM_M2bY_gstateP w gi (g := M2bY_gstate gi w) :
  w \in pre_Motzkin ->
  [/\
#N  w + dy1 gi + dy2 gi + ct1 gi + ct2 gi =
        dy1 g  + dy2 g  + ct1 g  + ct2 g   ,
#Se w + dy1 gi + dy2 gi                   =
        dy1 g  + dy2 g                     &
#W  w + dy1 gi + ct2 gi + free gi         =
        dy1 g  + ct2 g  + free g
].
Proof.
rewrite {}/g; elim/last_ind: w => [| w l ihw] /= pMwl=> //.
rewrite !M2bY_gstate_rcons.
have {ihw} /ihw := pre_Motzkin_rcons _ pMwl.
move: (M2bY_gstate gi w) => g [eN eSe eW].
case: l pMwl => pMwl; rewrite !count_mem_rcons !eqxx /=.
- rewrite !addSn {}eW {}eN {}eSe; case: g => * /=; split; ring.
- by rewrite !addSn {}eW {}eN {}eSe; case: g => [] [|c1] * /=; split; ring.
- suff {eW} : ct1 g + ct2 g != 0.
    rewrite !addSn {}eW {}eN {}eSe. case: g => [] [|?] [|?] * //=; split; ring.
  have {pMwl} : #Se w < #N w := pre_Motzkin_rcons_Se pMwl.
  apply: contraL; rewrite addn_eq0; case/andP=> /eqP e1 /eqP e2.
  suff /eqP-> : #Se w == #N w + (ct1 gi + ct2 gi) by rewrite -leqNgt leq_addr.
  by rewrite -(eqn_add2r (dy1 gi + dy2 gi)) addnAC !addnA eN eSe e1 e2 !addn0.
Qed.

(* Specialization to the g0 initial case. *)
Lemma pM_M2bY_gstate0P w (g := M2bY_gstate g0 w) :
  w \in pre_Motzkin ->
  [/\
#N  w = dy1 g  + dy2 g  + ct1 g  + ct2 g   ,
#Se w = dy1 g  + dy2 g                     &
#W  w = dy1 g  +                   ct2 g  + free g
].
Proof. by case/(pM_M2bY_gstateP g0); rewrite !addn0. Qed.

(* Reading a Motzkin word with automaton M2bY reaches state (0,0). *)
Corollary Motzkin_final l : l \in Motzkin -> M2bY_state {|0; 0|} l = {|0; 0|}.
Proof.
case/MotzkinP=> /pM_M2bY_gstate0P; rewrite -(state_of_M2bY_gstate _ 0 0 0).
move: (M2bY_gstate _ _) => [] c1 c2 d1 d2 f /= [-> -> ->] /eqP.
by rewrite -{2}[d1 + _]addn0 -!addnA !eqn_add2l addn_eq0=> /andP [] /eqP-> /eqP->.
Qed.

Corollary pre_Motzkin_noex  w l c :
  rcons w l \in pre_Motzkin -> noex l (M2bY_state c w).
Proof.
rewrite /noex; case: l; rewrite ?orbT // orbF => pMwl.
pose g := M2bY_gstate (mkGState c 0 0 0) w.
suff : (ct1 g != 0) || (ct2 g != 0).
  by rewrite -(state_of_M2bY_gstate _ 0 0 0) // /g; case: (M2bY_gstate _ _).
suff : ct1 g + ct2 g != 0 by rewrite addn_eq0 negb_and.
have := pM_M2bY_gstateP (mkGState c 0 0 0) (pre_Motzkin_rcons _ pMwl).
rewrite !addn0 -/g; case: g => c1 c2 d1 d2 f /= [eN eSe _].
have {pMwl} : #Se w < #N w := pre_Motzkin_rcons_Se pMwl.
apply: contraL; rewrite addn_eq0; case/andP=> /eqP e1 /eqP e2.
by rewrite e1 e2 -eSe !addn0 in eN; rewrite -eN -leqNgt -addnA leq_addr.
Qed.

(* Hence bY2M is a right inverse for M2bY on Motzkin words. *)
Theorem M2bYK : {in Motzkin, cancel M2bY bY2M}.
Proof. apply: M2bYK_; [exact: pre_Motzkin_noex | exact: Motzkin_final]. Qed.

Definition gM2bY_out (gf gi : gstate) : letter :=
  M2bY_out (state_of_gstate gf) (state_of_gstate gi).

Arguments gM2bY_out / gf gi.

Definition gM2bY_states_seq (g : gstate) (w : seq letter) : seq gstate :=
  scanl gt_M2bY g w.

Arguments gM2bY_states_seq / g w.

Lemma gM2bY_states_seq_state_of g w :
  M2bY_states_seq (state_of_gstate g) w =
  map state_of_gstate (gM2bY_states_seq g w).
Proof. by elim: w g => [| l w ihw] g //=; rewrite -state_of_gt_M2bY ihw. Qed.

Definition gM2bY_from (g : gstate) (w : seq letter) : seq letter :=
  pairmap gM2bY_out g (gM2bY_states_seq g w).

Arguments gM2bY_from / g w.

Lemma M2bY_from_state_of g w : gM2bY_from g w = M2bY_from (state_of_gstate g) w.
Proof.
by elim: w g => [| l w ihw] g //; rewrite M2bY_from_cons -state_of_gt_M2bY -ihw.
Qed.

(* In order to prove that reading a word in A produces a word in B, we
   need another invariant. *)

Lemma gM2bY_from_rcons g w l :
  gM2bY_from g (rcons w l) =
  rcons (gM2bY_from g w)
        (gM2bY_out (M2bY_gstate g w) (gt_M2bY (M2bY_gstate g w) l)).
Proof.
by rewrite /= scanl_rcons -cats1 pairmap_cat /= last_scanl foldl_rcons cats1.
Qed.

Lemma gM2bY_M2bY_from c d1 d2 f w :
  M2bY_from c w = gM2bY_from (mkGState c d1 d2 f) w.
Proof.
elim/last_ind: w => [| w l ihw] //; rewrite gM2bY_from_rcons -ihw.
by rewrite M2bY_from_rcons /gM2bY_out !state_of_gt_M2bY !state_of_M2bY_gstate.
Qed.

Lemma pre_Motzkin_noex_ghost l h g : rcons l h \in pre_Motzkin ->
  noex h (state_of_gstate (M2bY_gstate g l)).
Proof.
have -> : g = mkGState {|ct1 g; ct2 g|} (dy1 g) (dy2 g) (free g) by case: g.
rewrite state_of_M2bY_gstate; exact: pre_Motzkin_noex.
Qed.

(* Reading an N always produces an N *)
Lemma gM2bY_out_N g :  gM2bY_out g (gt_M2bY g N) = N.
Proof.
by case: g => [] [] [|?] [|?] *; rewrite //= ?eqxx //= ?andbF // ltn_eqF.
Qed.

(* Second invariant  for gt_M2bY: it provides equations relating the number of
   occurrences of each letter in the *output* word with the values of the state
   reached after reading this word. By brute force case analysis, some branches
   being eliminated by the previously established noex property. *)
Lemma pM_gM2bY_fromP wi gi (g := M2bY_gstate gi wi) (wo := gM2bY_from gi wi) :
  wi \in pre_Motzkin ->
  [/\
#N  wo + dy1 gi + dy2 gi + ct1 gi + ct2 gi + free gi =
         dy1 g  + dy2 g  + ct1 g  + ct2 g  + free g    ,
#Se wo + dy1 gi + dy2 gi + ct2 gi =
         dy1 g  + dy2 g  + ct2 g                         &
#W  wo + dy1 gi = dy1 g].
Proof.
rewrite {}/g {}/wo; elim/last_ind: wi => [| w l ihw] pMwl=> //.
have {ihw} /ihw := pre_Motzkin_rcons _ pMwl.
have := pre_Motzkin_noex_ghost gi pMwl.
rewrite gM2bY_from_rcons M2bY_gstate_rcons.
set wo := gM2bY_from gi w.
move: (M2bY_gstate gi w) => g noex [eN eSe eW].
case: l noex pMwl => [_ | _ | nx] /pre_MotzkinP pMwl; rewrite !count_mem_rcons.
- rewrite gM2bY_out_N.
  have -> /= : gt_M2bY g N = GState (ct1 g).+1 (ct2 g) (dy1 g) (dy2 g) (free g).
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

Corollary Y_M2bY_pM w : w \in pre_Motzkin -> M2bY w \in Yamanouchi.
Proof.
move=> w_in_pM; move/pre_MotzkinP: (w_in_pM) => pMw; apply/YamanouchiP=> n.
have /(pM_gM2bY_fromP g0) : take n w \in pre_Motzkin by exact: pre_Motzkin_take.
rewrite !addn0 M2bY_from_state_of -/M2bY take_M2bY; move: (M2bY_gstate _ _) => g.
by case=> -> -> ->; rewrite -!addnA leq_addr /= !leq_add2l addnCA leq_addr.
Qed.

Theorem B_M2bY_A w : w \in Motzkin -> M2bY w \in balanced_Yam.
case/MotzkinP => pMl eNSe eSeW.
rewrite -topredE /= /balanced_Yam Y_M2bY_pM //=.
pose gf := M2bY_gstate g0 w.
have /and3P [/eqP ec1 /eqP ec2 /eqP edf]:
  [&& ct1 gf == 0, ct2 gf == 0 & dy2 gf == free gf].
  move/(pM_M2bY_gstateP g0): (pMl); rewrite /= !addn0 -/gf; case=> eN eSe eW.
  move: eNSe; rewrite eN -addnA eSe; move/(canRL (addKn _)); rewrite subnn.
  move/eqP; rewrite addn_eq0; case/andP=> -> ct20; rewrite (eqP ct20) /=.
  by move/eqP: eSeW; rewrite eW (eqP ct20) addn0 eSe eqn_add2l.
move/(pM_gM2bY_fromP g0): pMl; rewrite -/gf ec1 ec2 edf !addn0.
rewrite -(gM2bY_M2bY_from {|0; 0|} 0 0 0);  case=> -> -> ->.
by rewrite addKn -{2}[dy1 _ + _]addn0 subnDl subn0.
Qed.

(* Lemma statesbY2MK c w (wo := bY2M_from c w) : *)
(*   c :: scanl t_bY2M c w = *)
(*   rcons (rev (scanl t_M2bY (bY2M_state c w) (rev wo))) (bY2M_state c w). *)
(* Proof. *)
(* rewrite {}/wo; elim/last_ind: w => [| l w ihw] //. *)
(* rewrite scanl_rcons -rcons_cons; congr rcons; rewrite {}ihw. *)
(* rewrite bY2M_from_rcons rev_rcons bY2M_state_rcons. *)
(* by rewrite [scanl _ _ (_ :: _)]/= t_M2bY_round rev_cons. *)
(* Qed. *)

(* Lemma statesM2bYK c w (wo := M2bY_from c w) : *)
(*   c :: scanl t_M2bY c w = *)
(*   rcons (rev (scanl t_bY2M (M2bY_state c w) (rev wo))) (M2bY_state c w). *)
(* Proof. *)
(* rewrite {}/wo; elim/last_ind: w => [| l w ihw] //. *)
(* rewrite scanl_rcons -rcons_cons; congr rcons; rewrite {}ihw. *)
(* rewrite M2bY_from_rcons rev_rcons M2bY_state_rcons. *)
(* by rewrite [scanl _ _ (_ :: _)]/= t_bY2M_round rev_cons. *)
(* Qed. *)

Lemma ct2_foldl_t_bY2M gi w (g := bY2M_state gi w) :
  (forall n, #W (drop n w) <= #Se (drop n w)) -> g.2 <= gi.2.
Proof.
rewrite {}/g.
move: {2}(size w) (leqnn (size w)) => n; elim: n w gi => [| n ihn] w gi.
  by rewrite leqn0 size_eq0 => /eqP ->.
rewrite leq_eqVlt; case/orP; last by apply: ihn.
case/lastP: w => [| w l] //; rewrite size_rcons eqSS => /eqP ssn.
case: l => leWSe; rewrite bY2M_state_rcons.
- have -> : (t_bY2M (bY2M_state gi w) N).2 = (bY2M_state gi w).2.
    by case: (bY2M_state _ _) => [] [] [].
  apply: ihn => [| k]; first by rewrite ssn.
  have := leWSe k; case: (leqP k (size w)) => hkss.
    by rewrite drop_rcons // !count_mem_rcons /=.
  rewrite !drop_oversize ?size_rcons //; exact: ltnW.
- by move: (leWSe (size w)); rewrite -cats1 drop_cat ltnn subnn drop0.
- case hyp : [forall x : 'I_(size w).+1, (#W (drop x w) <= #Se (drop x w))].
  + have h : (t_bY2M (bY2M_state gi w) Se).2 <= (bY2M_state gi w).2.
      by case: (bY2M_state  _ _) => [] [] c1 [|c2] /=.
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
  rewrite ew12 bY2M_state_cat /= {Pk max_k leWSe}.
  set g := bY2M_state _ w1.
  have hg : g.2 <= gi.2.
    by apply: ihn => //; rewrite /w1 size_take -ssn; case: ifP => //; move/ltnW.
  apply: leq_trans hg; case: g => [] [c1 c2] /=.
  have -> : t_bY2M {|c1; c2|} W = {|c1; c2.+1|} by [].
  set g := bY2M_state _ _.
  suff : g.2 <= c2.+1 by case: g => [] [g1 [|g2]].
  by apply: ihn => //; rewrite /w2 size_drop -ssn leq_subr.
Qed.

Lemma ct1_foldl_t_bY2M gi w (g := bY2M_state gi w) :
  (forall n, #Se (drop n w) <= #N (drop n w)) -> g.1 <= gi.1.
Proof.
rewrite {}/g.
move: {2}(size w) (leqnn (size w)) => n; elim: n w gi => [| n ihn] w gi.
  by rewrite leqn0 size_eq0 => /eqP ->.
rewrite leq_eqVlt; case/orP; last by apply: ihn.
case/lastP: w => [| w l] //; rewrite size_rcons eqSS => /eqP ssn.
case: l => leWSe; rewrite bY2M_state_rcons.
- (* aie *)
case hyp : [forall x : 'I_(size w).+1, (#Se (drop x w) <= #N (drop x w))].
  + have h : (t_bY2M (bY2M_state gi w) N).1 <= (bY2M_state gi w).1.
      by case: (bY2M_state _  _) => [] [] [|c1] c2 /=.
    apply: leq_trans h _; apply: ihn=> [|k]; rewrite ?ssn //.
    case: (leqP k (size w)) => hk; last by rewrite drop_oversize //; exact: ltnW.
    by rewrite -ltnS in hk; have /= := (forallP hyp) (Ordinal hk).
  + move/negbT: hyp; rewrite negb_forall; case/existsP=> j.
    rewrite -ltnNge => Pj.
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
  rewrite ew12 bY2M_state_cat /= {Pk max_k leWSe}.
  set g := bY2M_state _ w1.
  have hg : g.1 <= gi.1.
    by apply: ihn => //; rewrite /w1 size_take -ssn; case: ifP => //; move/ltnW.
  apply: leq_trans hg; case: g => [] [] c1 [|c2].
   + have -> /= : t_bY2M {|c1; 0|} Se = {|c1.+1; 0|} by [].
     set g := bY2M_state _ _.
     suff : g.1 <= c1.+1 by case: g => [] [[|g1] g2] /=.
     by apply: ihn => //; rewrite /w2 size_drop -ssn leq_subr.
   + have -> /= : t_bY2M {|c1; c2.+1|} Se = {|c1.+1; c2|} by [].
     set g :=  bY2M_state _ _.
     suff : g.1 <= c1.+1 by case: g => [] [[|g1] g2] /=.
     by apply: ihn => //; rewrite /w2 size_drop -ssn leq_subr.
- have -> : (t_bY2M (bY2M_state gi w) W).1 = (bY2M_state gi w).1.
    by case: ( bY2M_state _ _) => [] [] [].
  apply: ihn => [| k]; first by rewrite ssn.
  have := leWSe k; case: (leqP k (size w)) => hkss.
    by rewrite drop_rcons // !count_mem_rcons /=.
  rewrite !drop_oversize ?size_rcons //; exact: ltnW.
- by move: (leWSe (size w)); rewrite -cats1 drop_cat ltnn subnn drop0.
Qed.


Lemma B_final_state w : w \in Yamanouchi ->
                              bY2M_state {|0; 0|} (rev w) = {|0; 0|}.
Proof.
move/YamanouchiP=> Bw.
have : (bY2M_state {|0; 0|} (rev w)).1 = 0.
  apply/eqP; rewrite -leqn0; apply: ct1_foldl_t_bY2M => n.
  case: (ltnP (size w) n) => hn.
    by rewrite drop_oversize // size_rev; exact: ltnW.
  rewrite -[w](cat_take_drop (size w - n)) rev_cat.
  rewrite drop_size_cat; last by rewrite size_rev size_drop // subKn.
  by rewrite !count_rev; case/andP: (Bw (size w - n)).
have : (bY2M_state {|0; 0|} (rev w)).2 = 0.
  apply/eqP; rewrite -leqn0; apply: ct2_foldl_t_bY2M => n.
  case: (ltnP (size w) n) => hn.
    by rewrite drop_oversize // size_rev; exact: ltnW.
  rewrite -[w](cat_take_drop (size w - n)) rev_cat.
  rewrite drop_size_cat; last by rewrite size_rev size_drop // subKn.
  by rewrite !count_rev; case/andP: (Bw (size w - n)).
by case: (bY2M_state _ _) => [] [c1 c2] /= -> ->.
Qed.

Theorem bY2MK : {in balanced_Yam, cancel bY2M M2bY}.
Proof.
by apply: bY2MK_ => w hw; apply: B_final_state; apply: Yam_balanced_Yam.
Qed.


Record gbstate :=
  Gbstate {ctb1: nat; ctb2: nat; dyb1 : nat; dyb2 : nat; freeb : nat; ob : nat}.

Definition mkGbstate (c : state) (d1 d2 f o : nat) : gbstate :=
  Gbstate c.1 c.2 d1 d2 f o.

Let gb0 := Gbstate 0 0 0 0 0 0.

Definition state_of_gbstate (g : gbstate) :=
  let: Gbstate c1 c2 _ _ _ _ := g in State (c1, c2).


Definition gt_bY2M_ (g : gbstate)  (l : letter) : gbstate :=
match l, g with
 |W,  Gbstate c1     c2    d1 d2 f  o    => Gbstate c1    c2.+1  d1    d2    f    o     (* Se *)
 |Se, Gbstate c1     c2.+1 d1 d2 f  o    => Gbstate c1.+1 c2     d1    d2    f    o.+1  (* W *)
 |Se, Gbstate c1     0     d1 d2 f  o    => Gbstate c1.+1 0      d1    d2    f    o     (* Se *)
 |N,  Gbstate c1.+1  c2    d1 d2 f  o.+1 => Gbstate c1    c2     d1.+1 d2    f    o     (* N *)
 |N,  Gbstate c1.+1  c2    d1 d2 f  0    => Gbstate c1    c2     d1    d2.+1 f    0     (* N *)
 |N,  Gbstate 0      c2    d1 d2 f  o    => Gbstate 0     c2     d1    d2    f.+1 o     (* W *)
end.


Definition gt_bY2M := nosimpl gt_bY2M_.

Lemma gt_bY2M_bY2M g c l : state_of_gbstate g = c ->
  state_of_gbstate (gt_bY2M g l) = t_bY2M c l.
Proof.
by case: g=> c1 c2 d1 d2 f o /= <-; case: l; case: c2; case: c1; case: o.
Qed.

Lemma gt_bY2M_inv w gi (g := foldl gt_bY2M gi w) :
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
rewrite foldl_rcons /=; move: (foldl gt_bY2M gi w) => gf [eN eSe eW].
case: l; rewrite !count_mem_rcons !eqxx /=.
- rewrite !addSn {}eN {}eSe {}eW.
  by case: gf => [] [|c1] [|c2] d1 d2 f [|o] /=; rewrite ?addn0 ?addnS ?addSn.
- rewrite !addSn {}eN {}eSe {}eW.
  by case: gf => [] [|c1] [|c2] d1 d2 [|o] f /=; rewrite ?addnS ?addSn ?addn0.
- rewrite !addSn {}eN {}eSe {}eW.
  by case: gf => [] [|c1] [|c2] d1 d2 [|o] f /=; rewrite !addnS.
Qed.

Lemma state_of_foldl_gt_bY2M c g w : state_of_gbstate g = c ->
  state_of_gbstate (foldl gt_bY2M g w) = bY2M_state c w.
Proof.
move<-.
elim: w g => [|h w ihw] //= g; rewrite {}ihw; congr foldl.
case: g=> c1 c2 ? ? ? o {w} /=.
by case: h => //=; case: c1 => * //; case: c2 => *; case: o.
Qed.

Definition gbY2M_out (gi gf : gbstate) : letter :=
  let: (Gbstate ci1 ci2 _ _ _ _) := gi in
  let: (Gbstate cf1 cf2 _ _ _ _) := gf in
  if [&& cf1 == 0, ci1 == 0 & (ci2 == cf2)] then W
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then W
  else if (ci1 == cf1.+1) && (cf2 == ci2) then N
  (* else if (cf2 == ci2.+1) && (cf2 == ci2) then Se *)
  (* else if (cf1 == ci1.+1) && (cf2 == 0) && (ci2 == 0) then Se *)
  else Se (* junk *).

Lemma gbY2M_out_gbY2M gi gf ci cf :
  state_of_gbstate gi = ci -> state_of_gbstate gf = cf ->
  gbY2M_out gi gf = bY2M_out ci cf.
Proof. by case: gi=> ? ? ? ? ? ?/= <-; case: gf => ? ? ? ? ? ? /= <-. Qed.


Definition gbY2M_states_seq (g : gbstate) (w : seq letter) : seq gbstate :=
  scanl gt_bY2M g w.

Arguments gbY2M_states_seq / g w.

Definition gbY2M_from (g : gbstate) (w : seq letter) : seq letter :=
  pairmap gbY2M_out g (gbY2M_states_seq g w).

Arguments gbY2M_from / g w.

Lemma gbY2M_from_bY2M g c w : state_of_gbstate g = c ->
  gbY2M_from g w = bY2M_from c w.
Proof.
elim: w c g => [|l w ihw] //= c g hgc.
rewrite -/(bY2M_from (t_bY2M c l) w) -/(gbY2M_from (gt_bY2M g l) w).
have h : state_of_gbstate (gt_bY2M g l) = t_bY2M c l by exact: gt_bY2M_bY2M.
by rewrite (ihw (t_bY2M c l)) //; congr (_ :: _); apply: (gbY2M_out_gbY2M hgc).
Qed.

(* In order to prove that reading a word in A produces a word in B, we
   need another invariant. *)

Lemma gbY2M_from_rcons g w l : gbY2M_from g (rcons w l) =
  rcons (gbY2M_from g w)
        (gbY2M_out (foldl gt_bY2M g w) (gt_bY2M (foldl gt_bY2M g w) l)).
Proof.
by rewrite /= scanl_rcons -cats1 pairmap_cat /= last_scanl foldl_rcons cats1.
Qed.

Lemma gbY2M_from_inv wi gi (g := foldl gt_bY2M gi wi) (wo := gbY2M_from gi wi) :
  [/\
#N  wo + dyb1 gi + dyb2 gi =
         dyb1 g  + dyb2 g    ,
#Se wo + dyb1 gi + dyb2 gi + ctb2 gi + ctb1 gi =
         dyb1 g  + dyb2 g  + ctb2 g  + ctb1 g                         &
#W  wo + dyb1 gi + ob gi + freeb gi =
         dyb1 g  + ob g  + freeb g].
Proof.
rewrite {}/g {}/wo; elim/last_ind: wi => [| w l] //.
rewrite gbY2M_from_rcons !foldl_rcons; set wo := gbY2M_from gi w.
move: (foldl gt_bY2M gi w) => g [eN eSe eW]; rewrite !count_mem_rcons /=.
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


Lemma gbY2MP wi gi (g := foldl gt_bY2M gi wi) (wo := gbY2M_from gi wi) :
[/\
#N  wi + freeb gi = #N  wo + freeb g,
#Se wi + ctb2 g = #Se wo + ctb2 gi &
#W  wi + ctb2 gi  + freeb g = #W  wo + freeb gi  + ctb2 g
].
Proof.
have [eN1 eSe1 eW1] := gt_bY2M_inv wi gi; have := gbY2M_from_inv wi gi.
rewrite /g0 -/wo; case=> [eN2 eSe2 eW2].
split => [{eSe1 eSe2 eW1 eW2}|{eN1 eN2 eW1 eW2} | {eSe1 eSe2 eN1 eN2}].
- apply/eqP; rewrite -(eqn_add2r (dyb1 gi + dyb2 gi)) addnAC addnA eN1 -eN2.
  by apply/eqP; rewrite [RHS]addnAC addnA.
- apply/eqP; move: eSe2; rewrite [_ +  ctb1 g]addnAC -eSe1.
  rewrite [_ +  ctb1 gi]addnAC [_  + ctb2 gi]addnC  [X in _ = X]addnC !addnA.
  by move/eqP; rewrite !eqn_add2r addnC [X in _ == X]addnC eq_sym.
- apply/eqP; rewrite -(eqn_add2r (dyb1 gi + ob gi)).
  rewrite addnAC [_ + _ + (_ + _)]addnAC addnA eW1 [X in _ == X]addnAC.
  by rewrite [_ + _ + (_ + _)]addnAC addnA eW2 -!addnA !eqn_add2l addnC.
Qed.

Lemma gB_final_state w : w \in Yamanouchi ->
  state_of_gbstate (foldl gt_bY2M gb0 (rev w)) = {|0; 0|}.
Proof. rewrite (@state_of_foldl_gt_bY2M {|0; 0|}) //; exact: B_final_state. Qed.

Lemma pM_bY2M_Y w : w \in Yamanouchi -> bY2M w \in pre_Motzkin.
Proof.
move=> hl; apply/pre_MotzkinP => n.
rewrite take_bY2M !count_rev.
set c := bY2M_state  _ _; set w1 := take _ w.
pose gc := foldl gt_bY2M gb0 (rev (drop n w)).
have [] := gbY2M_from_inv (rev w1) gc.
set gf := foldl _ _ _.
have [-> ->] : (ctb1 gf = 0) /\ (ctb2 gf = 0).
  suff : state_of_gbstate gf = {|0; 0|} by case: gf => c1 c2 ? ? ? ? /= [-> ->].
  suff -> : gf = foldl gt_bY2M gb0 (rev w) by exact: gB_final_state.
  by rewrite /gf /gc -foldl_cat -rev_cat cat_take_drop.
rewrite !addn0.
have -> : (gbY2M_from gc (rev w1)) = (bY2M_from c (rev w1)).
  apply: gbY2M_from_bY2M; rewrite /c /gc; exact: state_of_foldl_gt_bY2M.
set N := #N _; set S := #Se _.
move=> eN eS _; move/eqP: eS.
rewrite -eN -addnA addnAC eqn_add2r addnAC eqn_add2r; move/eqP<-.
by rewrite leq_addr.
Qed.

Theorem A_bY2M_B w : w \in balanced_Yam -> bY2M w \in Motzkin.
Proof.
case/balanced_YamP=> Yw e; apply/MotzkinP.
rewrite pM_bY2M_Y //.
have := gbY2MP (rev w) gb0.
have := gbY2M_from_inv (rev w) gb0.
rewrite !count_rev /=; set g := foldl _ _ _; set wo := gbY2M_from gb0 (rev w).
have [-> ->] : ctb1 g = 0 /\ ctb2 g = 0.
  suff : state_of_gbstate g = {|0; 0|} by case: g => c1 c2 ? ? ? ? /= [-> ->].
  exact: gB_final_state.
rewrite !addn0 -/(bY2M_from _ (rev w)) -(@gbY2M_from_bY2M gb0) //.
rewrite -[pairmap _ _ _]/wo -/wo.
case=> eN1 eS1 eW1 [eN2 eS2 eW2]; split=> //; first by rewrite eN1 eS1.
have {e} e : #N w + #W w = #Se w + #Se w.
  have /andP[hWSe hSeN] : #W w <= #Se w <= #N w.
    by move/YamanouchiP/(_ (size w)):Yw; rewrite take_size.
  apply/eqP; rewrite -(subnK hSeN) addnAC eqn_add2r -{2}(subnK hWSe) eqn_add2r.
  by apply/eqP.
by apply/eqP; rewrite -eW2 -(eqn_add2l (#N w)) addnA e eN2 eN1 -eS1 -eS2 addnAC.
Qed.

Theorem AB_eq_card n : #|Motzkin_tuple n| = #|balanced_Yam_tuple n|.
Proof.
apply: (@eq_card_Motzkin_bYam_suff bY2M M2bY).
- apply: size_M2bY.
- apply: size_bY2M.
- apply: bY2MK.
- apply: M2bYK.
- apply: B_M2bY_A.
- apply: A_bY2M_B.
Qed.