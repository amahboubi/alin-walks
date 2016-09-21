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

(* (M2bY_states c w) (resp. (bY2M_states c w) is the sequence of states
 followed when reading w from c in the transducer M2bY (resp. bY2M)*)
Definition M2bY_states (c : state) (w : seq letter) : seq state :=
  scanl t_M2bY c w.

Arguments M2bY_states / c w.

Definition bY2M_states  (c : state) (w : seq letter) : seq state :=
  scanl t_bY2M c w.

Arguments bY2M_states / c w.

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


(* M2bY (resp. bY2M) is defined from t_M2bY and M2bY_out
  (resp. t_bY2M and bY2M_out) as follows:
   - from a word w and an intial state c, produce the sequence of states
     (M2bY_states c w) (resp.  (bY2M_states c w));
   - from sequence (M2bY_states c w) (resp.  (bY2M_states c w)), produce
    the sequence of corresponding output letters, using bY2M_out
    (resp. M2bY_out).
M2bY and bY2M take (0, 0) as initial state c.
*)

Definition M2bY_from (c : state) (w : seq letter) : seq letter :=
  pairmap M2bY_out c (M2bY_states c w).

Arguments M2bY_from / c w.

Definition M2bY := M2bY_from {|0; 0|}.

Arguments M2bY /.

Definition bY2M_from (c : state) (w : seq letter) : seq letter :=
  pairmap bY2M_out c (bY2M_states c w).

Arguments bY2M_from / c w.

Definition bY2M (w : seq letter) := rev (bY2M_from {|0; 0|} (rev w)).

Arguments bY2M / w.

(* A few computations to see the translation at work: *)

Eval compute in M2bY [:: N; W; Se]. (* [:: N; Se; W] *)
Eval compute in M2bY [:: N; Se; W]. (* [:: N; Se; N] *)
Eval compute in M2bY [:: W; N; Se]. (* [:: N; N; Se] *)


Eval compute in bY2M [:: N; Se; W]. (* [:: N; W; Se] *)
Eval compute in bY2M [:: N; Se; N]. (* [:: N; Se; W] *)
Eval compute in bY2M [:: N; N; Se]. (* [:: W; N; Se] *)


(* Operations reserving the size of sequences *)

Lemma size_M2bY_states c w : size (M2bY_states c w) = size w.
Proof. by rewrite  size_scanl. Qed.

Lemma size_bY2M_states c w : size (bY2M_states c w) = size w.
Proof. by rewrite  size_scanl. Qed.

Lemma size_M2bY_from c w : size (M2bY_from c w) = size w.
Proof. by rewrite /M2bY_from size_pairmap size_M2bY_states. Qed.

Lemma size_bY2M_from c w : size (bY2M_from c w) = size w.
Proof. by rewrite /= size_pairmap size_bY2M_states. Qed.

Lemma size_M2bY w : size (M2bY w) = size w.
Proof. by exact: size_M2bY_from. Qed.

Lemma size_bY2M w : size (bY2M w) = size w.
Proof. by rewrite /= size_rev size_bY2M_from size_rev. Qed.


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

(* Suppose that for a balanced Yamanouchi word, bY2M (M2bY w) = w *)
Hypothesis M2bYK : {in balanced_Yam, cancel bY2M M2bY}.

(* Suppose that  for a Motzkin word, M2bY (bY2M w) = w *)
Hypothesis bY2MK : {in Motzkin, cancel M2bY bY2M}.

(* Suppose that for a Motzkin word, (bY2M w) is a balanced Yamanouchi word *)
Hypothesis bYam_M2bY : forall w, w \in Motzkin -> M2bY w \in balanced_Yam.

(* for a balanced Yamanouchi word, (M2bY w) is a Motzkin word *)
Hypothesis Motz_bY2M : forall w, w \in balanced_Yam -> bY2M w \in Motzkin.

(* Let n be an arbitrary size *)
Variable n : nat.

(* Then we get the desired equality *)
Lemma eq_card_Motzkin_bYam_suff : #|Motzkin_tuple n| = #|balanced_Yam_tuple n|.
Proof.
have size_M2bYt (w : n.-tuple letter) : size (M2bY w) == n.
  by rewrite size_M2bY size_tuple.
have size_bY2Mt (w : n.-tuple letter) : size (bY2M w) == n.
  by rewrite size_bY2M size_tuple.
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


(*--- Reduction: we prove that the conditions on M2bY, bY2M can be reduced to
  assumptions on the states of the transducer(s), whose proofs require
  introducing ghost variables to state and establish suitable invariants. ---*)

Lemma M2bY_out_t_bY2M s2 lo : M2bY_out (t_bY2M s2 lo) s2 = lo.
Proof.
by case: lo; case: s2 => [] [[|c1][|c2]] //=; rewrite ?eqxx ?andbF //= ltn_eqF.
Qed.

Lemma M2bY_out_from_t_bY2M s1 s2 lo : s1 = t_bY2M s2 lo -> lo = M2bY_out s1 s2.
Proof. by move->; rewrite M2bY_out_t_bY2M. Qed.


(* But there is one degenerated case, which prevents the expected converse
   identities to hold everywhere *)
Definition noex  (l : letter) (c : state) :=
   [|| (c.1 != 0%N), (c.2 != 0%N) | (l != Se)].

Lemma bY2M_out_t_M2bY s1 li : noex li s1 -> bY2M_out (t_M2bY s1 li) s1 = li.
Proof.
by case: li; case: s1 => [] [[|c1][|c2]] //= _; rewrite ?eqxx ?andbF //= ltn_eqF.
Qed.

Lemma bY2M_out_from_t_M2bY s1 s2 li : noex li s1 ->
  s2 = t_M2bY s1 li -> bY2M_out s2 s1 = li.
Proof. move=> nx ->; exact: bY2M_out_t_M2bY. Qed.

(* t_bY2M s2 lo = s1 -> li = bY2M_out s2 s1 -> t_M2bY s1 li = s2. *)
Lemma t_M2bY_round s2 lo (s1 := t_bY2M s2 lo) : t_M2bY s1 (bY2M_out s2 s1) = s2.
Proof.
rewrite {}/s1. (* the s1 abbreviation is really for the sake of readability *)
by case: s2 => [] [[|?] [|?]]; case: lo => //=; rewrite ?eqxx ?andbF 1?ltn_eqF.
Qed.

(* t_M2bY s1 li = s2 -> lo = M2bY_out s1 s2 -> t_bY2M s2 lo = s1. *)
Lemma t_bY2M_round s1 lo (s2 := t_M2bY s1 lo) : t_bY2M s2 (M2bY_out s1 s2) = s1.
Proof.
rewrite {}/s2. (* the s2 abbreviation is really for the sake of readability *)
by case: s1 => [] [] [|?] [|?]; case: lo => //=; rewrite ?eqxx ?andbF // ltn_eqF.
Qed.

(* Let s1 be such that s2  --     l         --> s1 in automaton bY2M
   Then s1 -- l --> (t_M2bY s1 (bY2M_out s2 s1)) in automaton M2bY. *)
Lemma M2bY_out_round s2 l (s1 := t_bY2M s2 l) :
  M2bY_out s1 (t_M2bY s1 (bY2M_out s2 s1)) = l.
Proof. by rewrite t_M2bY_round /s1 M2bY_out_t_bY2M. Qed.

(* Let  s2 be such that s1  --     l         --> s2 in automaton M2bY.
   Then s2 -- l --> (t_bY2M s2 (M2bY_out s1 s2)) in automaton bY2M *)
Lemma bY2M_out_round s1 l (s2 := t_M2bY s1 l) : noex l s1 ->
  bY2M_out s2 (t_bY2M s2 (M2bY_out s1 s2)) = l.
Proof. by move=> nx; rewrite t_bY2M_round bY2M_out_t_M2bY. Qed.

(* Let cf be the state reached when starting from state ci and reading word wi
   with automaton bY2M. Let wf := (bY2M_from ci wi) be the word output. Then
   reading (rev wf) from cf with automaton M2bY produces word wi *)
Lemma revbY2M_fromK wi ci (cf := foldl t_bY2M ci wi) (wf := bY2M_from ci wi) :
    M2bY_from cf (rev wf) = rev wi.
Proof.
rewrite {}/cf {}/wf; elim/last_ind: wi ci => [| w l ihw c] //=.
set cf := foldl _ _ _.
rewrite /= scanl_rcons -cats1 pairmap_cat rev_cat /=.
set s := bY2M_out (last _ _)  _.
rewrite -/(bY2M_from c w) /= rev_rcons; congr cons; last first.
  suff {ihw} -> : t_M2bY cf s = foldl t_bY2M c w by apply/ihw.
  rewrite {}/cf {}/s last_scanl foldl_rcons; exact: t_M2bY_round.
by rewrite {}/cf {}/s foldl_rcons last_scanl; apply: M2bY_out_round.
Qed.


Section SufficientConditionsForCancel.

(* We leave as (temporary) hypotheses the facts that requires introducing
   ghost variables: *)

Hypothesis pA_noex : forall l h c,
   rcons l h \in pre_Motzkin -> noex h (foldl t_M2bY c l).

Lemma revM2bY_fromK l c : l \in pre_Motzkin ->
    rev (bY2M_from (foldl t_M2bY c l) (rev (M2bY_from c l))) = l.
Proof.
elim/last_ind: l c => [| l h ihl c pAlh] //=.
set cf := foldl _ _ _.
rewrite /= scanl_rcons -cats1 pairmap_cat rev_cat /=.
set s := M2bY_out _ _.
rewrite -/(M2bY_from c l) /= rev_cons; congr rcons; last first.
  rewrite /cf /s foldl_rcons last_scanl; apply: bY2M_out_round; exact: pA_noex.
suff -> : t_bY2M cf s = foldl t_M2bY c l by apply/ihl/(pre_Motzkin_rcons h).
  rewrite {}/cf {}/s last_scanl foldl_rcons; exact: t_bY2M_round.
Qed.

Hypothesis A_final_state : forall l,
  l \in Motzkin -> foldl t_M2bY {|0; 0|} l = {|0; 0|}.

Lemma M2bYK_ : {in Motzkin, cancel M2bY bY2M}.
Proof.
move=> l Al; rewrite /bY2M -(A_final_state Al); apply: revM2bY_fromK.
exact: pre_Motzkin_Motzkin.
Qed.

Hypothesis B_final_state : forall l,
  l \in balanced_Yam -> foldl t_bY2M {|0; 0|} (rev l) = {|0; 0|}.

Lemma bY2MK_ : {in balanced_Yam, cancel bY2M M2bY}.
Proof.
by move=> l Bl; rewrite /M2bY -(B_final_state Bl) /bY2M revbY2M_fromK ?revK.
Qed.

End SufficientConditionsForCancel.


(*--- A few useful technical surgery lemmas about M2bY and bY2M ---*)

Lemma take_M2bY n l : M2bY (take n l) = take n (M2bY l).
Proof. by rewrite /M2bY /M2bY_from /M2bY_states -take_scanl -take_pairmap. Qed.

Lemma M2bY_from_cons c l w :
  M2bY_from c (l :: w) = M2bY_out c (t_M2bY c l) :: M2bY_from (t_M2bY c l) w.
Proof. by []. Qed.

Lemma bY2M_from_cons c l w :
  bY2M_from c (l :: w) = bY2M_out c (t_bY2M c l) :: bY2M_from (t_bY2M c l) w.
Proof. by []. Qed.

Lemma M2bY_from_rcons s w l : M2bY_from s (rcons w l) =
  rcons (M2bY_from s w)
        (M2bY_out (foldl t_M2bY s w) (t_M2bY (foldl t_M2bY s w) l)).
Proof.
by rewrite /= scanl_rcons -cats1 pairmap_cat /= last_scanl foldl_rcons cats1.
Qed.

Lemma M2bY_rcons  w l (s := foldl t_M2bY {|0; 0|} w) :
  M2bY (rcons w l) = rcons (M2bY w) (M2bY_out s (t_M2bY s l)).
Proof. by rewrite /M2bY M2bY_from_rcons. Qed.

Lemma bY2M_from_rcons s w l : bY2M_from s (rcons w l) =
  rcons (bY2M_from s w)
        (bY2M_out (foldl t_bY2M s w) (t_bY2M (foldl t_bY2M s w) l)).
Proof.
by rewrite /= scanl_rcons -cats1 pairmap_cat /= last_scanl foldl_rcons cats1.
Qed.

Lemma bY2M_cons w l (s := foldl t_bY2M {|0; 0|} (rev w)) :
  bY2M (l :: w) = (bY2M_out s (t_bY2M s l)) :: (bY2M w).
Proof. by rewrite /bY2M rev_cons bY2M_from_rcons rev_rcons. Qed.

(*--- Invariant of the M2bY transducer, by decoration with ghost variables. This
      proves the two remaining facts about words in A, plus the important
      missing property of M2bY : that its image is included in balanced_Yam ---*)

(* The states of the automaton are augmented with 3 more natural numbers, that
   count respectively: the number of Dyck words (N, Se) processed so far (d1);
   the number of pseudo-Dyck words (NSe, W) in progress so
   far (d2); the number of "free" occurrences of W processed so far (f) *)

Record gstate :=
  GState {ct1: nat; ct2: nat; dy1 : nat; dy2 : nat; free : nat}.

Definition mkGState (c : state) (d1 d2 f : nat) : gstate :=
  GState c.1 c.2 d1 d2 f.

Let g0 := GState 0 0 0 0 0.

Definition state_of_gstate (g : gstate) :=
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

(* Forgeting the ghost information in a list of reached states *)


Lemma state_of_foldl_gt_M2bY s d1 d2 f w (g := mkGState s d1 d2 f) :
  state_of_gstate (foldl gt_M2bY g w) = foldl t_M2bY s w.
Proof.
have -> : s = state_of_gstate g by rewrite {}/g; case: s => [] [].
elim: w g => [|h w ihw] //= g; rewrite {}ihw; congr foldl.
by case: g=> c1 c2* {w} /=; case: h => //=; case: c1 => * //; case: c2 => *.
Qed.


(* Invariant for gt_M2bY. By brute force case analysis excepy for the only *)
(* interesting case of the (tail) induction on w is, i.e. when it ends with Se:*)
(* in this case the hypothesis (pre_Motzkin l) forbids ct1 c = ct2 c = 0. We *)
(* need to kind of reproduce this proof outside this one to ensure we never hit*)
(* this  exceptional case... Can we do better? *)

Lemma pA_gt_M2bY_inv w gi (g := foldl gt_M2bY gi w) :
  w \in pre_Motzkin ->
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
have {ihw} /ihw := pre_Motzkin_rcons _ pAwl.
move: (foldl gt_M2bY gi w) => c [eN eSe eW].
case: l pAwl => pAwl; rewrite !count_mem_rcons !eqxx /=.
- by rewrite !addSn {}eW {}eN {}eSe; case: c => * /=; split; ring.
- by rewrite !addSn {}eW {}eN {}eSe; case: c => [] [|c1] * /=; split; ring.
- suff {eW} : ct1 c + ct2 c != 0.
    rewrite !addSn {}eW {}eN {}eSe; case: c => [] [|?] [|?] * //=; split; ring.
  have {pAwl} : #Se w < #N w := pre_Motzkin_rcons_Se pAwl.
  apply: contraL; rewrite addn_eq0; case/andP=> /eqP e1 /eqP e2.
  suff /eqP-> : #Se w == #N w + (ct1 gi + ct2 gi) by rewrite -leqNgt leq_addr.
  by rewrite -(eqn_add2r (dy1 gi + dy2 gi)) addnAC !addnA eN eSe e1 e2 !addn0.
Qed.

(* Lifting the exceptional case to states with ghosts *)
Definition gnoex (l : letter) (g : gstate) :=
   [|| ct1 g != 0, ct2 g != 0 | l != Se].

Lemma gnoex_noex l g : gnoex l g = noex l (state_of_gstate g).
Proof. by case: g. Qed.

Lemma pA_gnoex w l g : rcons w l \in pre_Motzkin -> gnoex l (foldl gt_M2bY g w).
Proof.
rewrite /gnoex; case: l; rewrite ?orbT // orbF -negb_and => pA.
have /(pA_gt_M2bY_inv g) := pre_Motzkin_rcons _ pA.
move: (foldl _ _ _) => [] c1 c2 d1 d2 f /= [] eN eSe _.
apply: contraL (pre_Motzkin_rcons_Se pA); case/andP => /eqP e1 /eqP e2.
suff /eqP-> : #Se w == #N w + (ct1 g + ct2 g) by rewrite -leqNgt leq_addr.
by rewrite -(eqn_add2r (dy1 g + dy2 g)) addnAC !addnA eN eSe e1 e2 !addn0.
Qed.

Lemma pA_noex  w l s : rcons w l \in pre_Motzkin -> noex l (foldl t_M2bY s w).
Proof.
move=> ?; rewrite -(state_of_foldl_gt_M2bY _ 0 0 0) -gnoex_noex; exact: pA_gnoex.
Qed.

Lemma A_final_state l : l \in Motzkin -> foldl t_M2bY {|0; 0|} l = {|0; 0|}.
Proof.
case/MotzkinP=> /(pA_gt_M2bY_inv g0); rewrite -(state_of_foldl_gt_M2bY _ 0 0 0).
rewrite /= !addn0; move: (foldl _ _ _) => [] c1 c2 d1 d2 f /= [-> -> ->].
rewrite -addnA addnC; move/(canRL (addnK _)); rewrite subnn.
by case: c1 => [|?] //; case: c2.
Qed.

Theorem M2bYK : {in Motzkin, cancel M2bY bY2M}.
Proof. apply: M2bYK_; [exact: pA_noex | exact: A_final_state]. Qed.

Definition gM2bY_out gf gi :=
  let: (GState ci1 ci2 _ _ _) := gi in
  let: (GState cf1 cf2 _ _ _) := gf in
  if [&& ci1 == 0, cf1 == 0 & (ci2 == cf2)] then N
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then Se
  else if (ci1 == cf1.+1) && (ci2 == cf2) then N
  else if (ci1 == cf1) && (cf2 == ci2.+1) then W
  else Se.

Definition gM2bY_states (g : gstate) (w : seq letter) : seq gstate :=
  scanl gt_M2bY g w.

Arguments gM2bY_states / g w.

Definition gM2bY_from (g : gstate) (w : seq letter) : seq letter :=
  pairmap gM2bY_out g (gM2bY_states g w).

Arguments gM2bY_from / g w.

(* In order to prove that reading a word in A produces a word in B, we
   need another invariant. *)

Lemma gM2bY_from_rcons g w l : gM2bY_from g (rcons w l) =
  rcons (gM2bY_from g w) (gM2bY_out (foldl gt_M2bY g w) (gt_M2bY (foldl gt_M2bY g w) l)).
Proof.
by rewrite /= scanl_rcons -cats1 pairmap_cat /= last_scanl foldl_rcons cats1.
Qed.

Lemma gM2bY_out_state_of g1 g2 :
  gM2bY_out g1 g2 = M2bY_out (state_of_gstate g1) (state_of_gstate g2).
Proof. by case: g1 => c11 c12 *; case: g2 => c21 c22. Qed.

Lemma gM2bY_M2bY_from s d1 d2 f w :
  M2bY_from s w = gM2bY_from (mkGState s d1 d2 f) w.
Proof.
elim/last_ind: w => [| w l ihw] //; rewrite gM2bY_from_rcons -ihw.
by rewrite M2bY_from_rcons gM2bY_out_state_of -!foldl_rcons !state_of_foldl_gt_M2bY.
Qed.

Lemma pA_noex_ghost l h g : rcons l h \in pre_Motzkin ->
  noex h (state_of_gstate (foldl gt_M2bY g l)).
Proof.
have -> : g = mkGState {|ct1 g; ct2 g|} (dy1 g) (dy2 g) (free g) by case: g.
rewrite state_of_foldl_gt_M2bY; exact: pA_noex.
Qed.


(* Second invariant *)
Lemma pA_gM2bY_inv wi gi (g := foldl gt_M2bY gi wi) (wo := gM2bY_from gi wi) :
  wi \in pre_Motzkin ->
  [/\
#N  wo + dy1 gi + dy2 gi + ct1 gi + ct2 gi + free gi =
         dy1 g  + dy2 g  + ct1 g  + ct2 g  + free g    ,
#Se wo + dy1 gi + dy2 gi + ct2 gi =
         dy1 g + dy2 g + ct2 g                         &
#W  wo + dy1 gi = dy1 g].
Proof.
rewrite {}/g {}/wo; elim/last_ind: wi => [| w l ihw] pAwl=> //.
have {ihw} /ihw := pre_Motzkin_rcons _ pAwl.
have := pA_noex_ghost gi pAwl.
rewrite gM2bY_from_rcons !foldl_rcons.
set wo := gM2bY_from gi w.
move: (foldl gt_M2bY gi w) => g noex [eN eSe eW].
case: l noex pAwl => [_ | _ | nx] /pre_MotzkinP pAwl; rewrite !count_mem_rcons /=.
- have -> : gM2bY_out g (gt_M2bY g N) = N. (* push this outside *)
    case: g {eN eSe eW} => [] [] [|?] [|?] *; rewrite //= ?eqxx //= ?andbF //.
    by rewrite ltn_eqF.
  have-> /=: gt_M2bY g N = GState (ct1 g).+1 (ct2 g) (dy1 g) (dy2 g) (free g).
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


Lemma ghost_gt_M2bY g s :
  t_M2bY (state_of_gstate g) s = state_of_gstate (gt_M2bY g s).
Proof. by case: g => [] c1 c2; case: s => //; case: c1 => //; case: c2. Qed.

Lemma ghost_gM2bY_out g1 g2 :
  gM2bY_out g1 g2 = M2bY_out (state_of_gstate g1) (state_of_gstate g2).
Proof. by case: g1 => [] *; case: g2. Qed.

Lemma pB_M2bY_pA l : l \in pre_Motzkin -> M2bY l \in Yamanouchi.
Proof.
move/pre_MotzkinP=> pAl; apply/YamanouchiP=> n.
have /(pA_gM2bY_inv (mkGState {|0; 0|} 0 0 0)) : take n l \in pre_Motzkin.
  by apply/pre_MotzkinP=> m; rewrite take_take.
rewrite !addn0 -gM2bY_M2bY_from -/M2bY take_M2bY; case=> -> -> ->.
move: (foldl _ _ _) => g; rewrite -addnA leq_addr /= addnA.
by set d := dy1 _ + dy2 _; rewrite -[d + _ + _]addnAC -addnA leq_addr.
Qed.

Theorem B_M2bY_A l : l \in Motzkin -> M2bY l \in balanced_Yam.
case/MotzkinP => pAl eNSe eSeW.
rewrite -topredE /= /balanced_Yam pB_M2bY_pA //=.
pose rl := foldl gt_M2bY g0 l.
have /and3P [/eqP ec1 /eqP ec2 /eqP edf]:
  [&& ct1 rl == 0, ct2 rl == 0 & dy2 rl == free rl].
  move/(pA_gt_M2bY_inv g0): (pAl); rewrite /= !addn0 -/rl; case=> eN eSe eW.
  move: eNSe; rewrite eN -addnA eSe; move/(canRL (addKn _)); rewrite subnn.
  move/eqP; rewrite addn_eq0; case/andP=> -> ct20; rewrite (eqP ct20) /=.
  by move/eqP: eSeW; rewrite eW (eqP ct20) addn0 eSe eqn_add2l.
move/(pA_gM2bY_inv g0): pAl; rewrite -/rl ec1 ec2 edf !addn0.
rewrite -(gM2bY_M2bY_from {|0; 0|} 0 0 0);  case=> -> -> ->.
by rewrite addKn -{2}[dy1 _ + _]addn0 subnDl subn0.
Qed.

Lemma statesbY2MK c w (wo := bY2M_from c w) :
  c :: scanl t_bY2M c w =
  rcons (rev (scanl t_M2bY (foldl t_bY2M c w) (rev wo))) (foldl t_bY2M c w).
Proof.
rewrite {}/wo; elim/last_ind: w => [| l w ihw] //.
rewrite scanl_rcons -rcons_cons; congr rcons; rewrite {}ihw.
rewrite bY2M_from_rcons rev_rcons foldl_rcons; set co := foldl _ _ _.
by rewrite [scanl _ _ (_ :: _)]/= t_M2bY_round rev_cons.
Qed.

Lemma statesM2bYK c w (wo := M2bY_from c w) :
  c :: scanl t_M2bY c w =
  rcons (rev (scanl t_bY2M (foldl t_M2bY c w) (rev wo))) (foldl t_M2bY c w).
Proof.
rewrite {}/wo; elim/last_ind: w => [| l w ihw] //.
rewrite scanl_rcons -rcons_cons; congr rcons; rewrite {}ihw.
rewrite M2bY_from_rcons rev_rcons foldl_rcons; set co := foldl _ _ _.
by rewrite [scanl _ _ (_ :: _)]/= t_bY2M_round rev_cons.
Qed.



Lemma ct2_foldl_t_bY2M gi w (g := foldl t_bY2M gi w) :
  (forall n, #W (drop n w) <= #Se (drop n w)) -> g.2 <= gi.2.
Proof.
rewrite {}/g.
move: {2}(size w) (leqnn (size w)) => n; elim: n w gi => [| n ihn] w gi.
  by rewrite leqn0 size_eq0 => /eqP ->.
rewrite leq_eqVlt; case/orP; last by apply: ihn.
case/lastP: w => [| w l] //; rewrite size_rcons eqSS => /eqP ssn.
case: l => leWSe; rewrite foldl_rcons.
- have -> : (t_bY2M (foldl t_bY2M gi w) N).2 = (foldl t_bY2M gi w).2.
    by case: (foldl _ _ _) => [] [] [].
  apply: ihn => [| k]; first by rewrite ssn.
  have := leWSe k; case: (leqP k (size w)) => hkss.
    by rewrite drop_rcons // !count_mem_rcons /=.
  rewrite !drop_oversize ?size_rcons //; exact: ltnW.
- by move: (leWSe (size w)); rewrite -cats1 drop_cat ltnn subnn drop0.
- case hyp : [forall x : 'I_(size w).+1, (#W (drop x w) <= #Se (drop x w))].
  + have h : (t_bY2M (foldl t_bY2M gi w) Se).2 <= (foldl t_bY2M gi w).2.
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
  have -> : t_bY2M {|c1; c2|} W = {|c1; c2.+1|} by [].
  set g := foldl _ _ _.
  suff : g.2 <= c2.+1 by case: g => [] [g1 [|g2]].
  by apply: ihn => //; rewrite /w2 size_drop -ssn leq_subr.
Qed.


Lemma ct1_foldl_t_bY2M gi w (g := foldl t_bY2M gi w) :
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
  + have h : (t_bY2M (foldl t_bY2M gi w) N).1 <= (foldl t_bY2M gi w).1.
      by case: (foldl _ _ _) => [] [] [|c1] c2 /=.
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
  rewrite ew12 foldl_cat /= {Pk max_k leWSe}.
  set g := foldl _ _ w1.
  have hg : g.1 <= gi.1.
    by apply: ihn => //; rewrite /w1 size_take -ssn; case: ifP => //; move/ltnW.
  apply: leq_trans hg; case: g => [] [] c1 [|c2].
   + have -> /= : t_bY2M {|c1; 0|} Se = {|c1.+1; 0|} by [].
     set g := foldl _ _ _.
     suff : g.1 <= c1.+1 by case: g => [] [[|g1] g2] /=.
     by apply: ihn => //; rewrite /w2 size_drop -ssn leq_subr.
   + have -> /= : t_bY2M {|c1; c2.+1|} Se = {|c1.+1; c2|} by [].
     set g := foldl _ _ _.
     suff : g.1 <= c1.+1 by case: g => [] [[|g1] g2] /=.
     by apply: ihn => //; rewrite /w2 size_drop -ssn leq_subr.
- have -> : (t_bY2M (foldl t_bY2M gi w) W).1 = (foldl t_bY2M gi w).1.
    by case: (foldl _ _ _) => [] [] [].
  apply: ihn => [| k]; first by rewrite ssn.
  have := leWSe k; case: (leqP k (size w)) => hkss.
    by rewrite drop_rcons // !count_mem_rcons /=.
  rewrite !drop_oversize ?size_rcons //; exact: ltnW.
- by move: (leWSe (size w)); rewrite -cats1 drop_cat ltnn subnn drop0.
Qed.

Lemma B_final_state w : w \in Yamanouchi ->
                              foldl t_bY2M {|0; 0|} (rev w) = {|0; 0|}.
Proof.
move/YamanouchiP=> Bw.
have : (foldl t_bY2M {|0; 0|} (rev w)).1 = 0.
  apply/eqP; rewrite -leqn0; apply: ct1_foldl_t_bY2M => n.
  case: (ltnP (size w) n) => hn.
    by rewrite drop_oversize // size_rev; exact: ltnW.
  rewrite -[w](cat_take_drop (size w - n)) rev_cat.
  rewrite drop_size_cat; last by rewrite size_rev size_drop // subKn.
  by rewrite !count_rev; case/andP: (Bw (size w - n)).
have : (foldl t_bY2M {|0; 0|} (rev w)).2 = 0.
  apply/eqP; rewrite -leqn0; apply: ct2_foldl_t_bY2M => n.
  case: (ltnP (size w) n) => hn.
    by rewrite drop_oversize // size_rev; exact: ltnW.
  rewrite -[w](cat_take_drop (size w - n)) rev_cat.
  rewrite drop_size_cat; last by rewrite size_rev size_drop // subKn.
  by rewrite !count_rev; case/andP: (Bw (size w - n)).
by case: (foldl _ _ _) => [] [c1 c2] /= -> ->.
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
  state_of_gbstate (foldl gt_bY2M g w) = foldl t_bY2M c w.
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


Definition gbY2M_states (g : gbstate) (w : seq letter) : seq gbstate :=
  scanl gt_bY2M g w.

Arguments gbY2M_states / g w.

Definition gbY2M_from (g : gbstate) (w : seq letter) : seq letter :=
  pairmap gbY2M_out g (gbY2M_states g w).

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

Lemma take_bY2M n w (w2 := drop n w) (c := foldl t_bY2M {|0; 0|} (rev w2)) :
  take n (bY2M w) = rev (bY2M_from c (rev (take n w))).
Proof.
rewrite /bY2M -[w](cat_take_drop n) rev_cat /bY2M_from /bY2M_states.
rewrite scanl_cat pairmap_cat rev_cat last_scanl.
set w1 := take _ w.
rewrite -/(bY2M_from c (rev w1)) -/(bY2M_from {|0; 0|} (rev w2)).
case: (ltnP n (size w)) => hn.
  rewrite take_size_cat; first by rewrite take_size_cat // size_take hn.
  by rewrite size_rev size_bY2M_from size_rev size_take hn.
have -> : w1 = w by rewrite /w1 take_oversize.
have -> : w2 = [::] by rewrite /w2 drop_oversize.
rewrite take_cat ltnNge size_rev size_bY2M_from size_rev hn /=.
by rewrite take_cat ltnNge hn /= drop_oversize //= !cats0.
Qed.

Lemma gB_final_state w : w \in Yamanouchi ->
  state_of_gbstate (foldl gt_bY2M gb0 (rev w)) = {|0; 0|}.
Proof. rewrite (@state_of_foldl_gt_bY2M {|0; 0|}) //; exact: B_final_state. Qed.

Lemma pA_bY2M_pB w : w \in Yamanouchi -> bY2M w \in pre_Motzkin.
Proof.
move=> hl; apply/pre_MotzkinP => n.
rewrite take_bY2M !count_rev.
set c := foldl _ _ _; set w1 := take _ w.
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
case/balanced_YamP=> pBw e; apply/MotzkinP.
rewrite pA_bY2M_pB //.
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
    by move/YamanouchiP/(_ (size w)):pBw; rewrite take_size.
  apply/eqP; rewrite -(subnK hSeN) addnAC eqn_add2r -{2}(subnK hWSe) eqn_add2r.
  by apply/eqP.
by apply/eqP; rewrite -eW2 -(eqn_add2l (#N w)) addnA e eN2 eN1 -eS1 -eS2 addnAC.
Qed.

Theorem AB_eq_card n : #|Motzkin_tuple n| = #|balanced_Yam_tuple n|.
Proof.
apply: eq_card_Motzkin_bYam_suff.
- apply: bY2MK.
- apply: M2bYK.
- apply: B_M2bY_A.
- apply: A_bY2M_B.
Qed.