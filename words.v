Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice tuple fintype finfun finset.
Require Import bigop ssralg ssrnum poly ssrint.

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

Lemma preA_rcons w a : preAword (rcons w a) -> preAword w.
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

Definition sA2B (c : state) (s : step) : step * state :=
  match s, c with
    |  W,  {|0    ; c2   |} => (N,  {|0    ; c2   |})
    |  W,  {|c1.+1; c2   |} => (SE, {|c1   ; c2.+1|})
    |  N,  {|c1   ; c2   |} => (N,  {|c1.+1; c2   |})
    |  SE, {|c1   ; c2.+1|} => (W,  {|c1   ; c2   |})
    |  SE, {|c1.+1; 0    |} => (SE, {|c1   ; 0    |})
    |  SE, {|0    ; 0    |} => (N,  {|0    ; 0    |}) (* junk *)
  end.

Arguments sA2B c s : simpl never.

(* Inverse transformation. *)
Definition sB2A (c : state) (s : step) :=
  match s, c with
    | N,  {|0    ; c2   |} => (W,  {|0    ; c2   |})
    | SE, {|c1   ; c2.+1|} => (W,  {|c1.+1; c2   |})
    | N,  {|c1.+1; c2   |} => (N,  {|c1   ; c2   |})
    | W,  {|c1   ; c2   |} => (SE, {|c1   ; c2.+1|})
    | SE, {|c1   ; 0    |} => (SE, {|c1.+1; 0    |}) (* junk *)
  end.

Arguments sB2A c s : simpl never.


Definition cA2B (ci cf : state) : step :=
  let: {|ci1; ci2|} := ci in
  let: {|cf1; cf2|} := cf in
  if (ci == cf) then W
  else if (ci1 == cf1.+1) && (cf2 == ci2.+1) then W
  else if (cf1 == ci1.+1) then N
  else if (ci2 == cf2.+1) || (ci1 == cf1.+1) then SE
  else SE (* junk *).

Definition cB2A (ci cf : state) : step :=
  let: {|ci1; ci2|} := ci in
  let: {|cf1; cf2|} := cf in
  if (ci == cf) then N
  else if (cf1 == ci1.+1) && (ci2 == cf2.+1) then SE
  else if (ci1 == cf1.+1) then N
  else if (cf2 == ci2.+1) then W
  else SE (* junk *).

Definition noex  (s : step) (c : state) :=
  [|| (c.1 != 0%N), (c.2 != 0%N) | (s != SE)].

Lemma sA2BK (c : state) (s : step) : noex s c ->
  cA2B c (sA2B c s).2 = s.
rewrite /cA2B /sA2B /noex.
case: s; case: c => [] [] [| c1] [| c2] _ //=; rewrite ?eqxx ?if_same //=.
- by rewrite eqE /= eqE /= ltn_eqF //= ltn_eqF.
- by rewrite eqE /= eqE ltn_eqF //= ltn_eqF.
- by rewrite eqE /= eqE /= gtn_eqF.
- by rewrite !ifF // ?ltn_eqF // eqE /= eqE /= gtn_eqF.
- by rewrite !ifF // ?ltn_eqF // eqE /= eqE /= eqxx gtn_eqF.
Qed.

Definition A2Bstates (c : state) (ls : seq step) : seq state :=
  scanl (fun nn s => snd (sA2B nn s)) c ls.

Definition A2B_from (c : state) (ls : seq step) : seq step :=
  pairmap cB2A c (A2Bstates c ls).

Definition A2B : seq step -> seq step := A2B_from {|0; 0|}.

Definition B2Astates (c : state) (ls : seq step) : seq state :=
  scanl (fun nn s => snd (sB2A nn s)) c ls.

Definition B2A_from (c : state) (ls : seq step) : seq step :=
  pairmap cA2B c (B2Astates c ls).

Definition B2A : seq step -> seq step := B2A_from {|0; 0|}.

Theorem B2AK : {in preAword, cancel A2B B2A}.
Proof.
Admitted.


(* Section Scan. *)

(* Variables (T1 : Type) (x1 : T1) (T2 : Type) (x2 : T2). *)
(* Variables (f : T1 -> T1 -> T2) (g : T1 -> T2 -> T1). *)
(* Variables (D : pred T1). *)

(* Lemma in_scanlK : *)
(*   (forall x, x \in D -> cancel (g x) (f x)) -> *)
(*   forall x, x \in D -> cancel (scanl g x) (pairmap f x). *)
(* Proof. *)
(* move=> Hfg x Dx s; elim: s x Dx => //= y s IHs x Dx. *)
(* rewrite Hfg // IHs //. Qed. *)

(* Lemma in_scanlK : *)
(*   (forall x, cancel (g x) (f x)) -> forall x, cancel (scanl g x) (pairmap f x). *)
(* Proof. by move=> Hfg x s; elim: s x => //= y s IHs x; rewrite Hfg IHs. Qed. *)

(* Lemma in_pairmapK : *)
(*   (forall x, cancel (f x) (g x)) -> forall x, cancel (pairmap f x) (scanl g x). *)
(* Proof. by move=> Hgf x s; elim: s x => //= y s IHs x; rewrite Hgf IHs. Qed. *)

(* End Scan. *)


(* Intuition behind the bijection:
  - Remember a word w in A is a Dyck word on (N, SE) with W letters freely
inserted;
  - Hence for each pair of parentheses (N, SE) in the Dyck word in w,
either they enclose a letter W, or not.
  - Otherwise said a word in A is a Dyck word w1 on (NW, SE) shuffled with a
Dyck word w2 on (N, SE), and possibly with some remaining free occurrences
of letter W.
The bijection looks for a word w1 of maximal length and transforms it into
a Dyck word on (NSE, W), leaves w2 unchanged and turns the free occurrences
of letter W into N. These transformations are implemented using two counters
which repsectively detect the two natures of Dyck words, with the suitable
priority. *)






(* We implement the bijection using a "monadic" style: we first describe
   a transition system on pairs of a letter and a (double) counter.
   Then we fold this transformation on a sequence of letters, and an initial
   value of the counter. This fold computes the tranformation of the input
   word, and propagates the resulting value of the counter. *)

(* Record store (A : Type) : Type := Store {data : A; hidden : nat * nat}. *)

(* Definition mkStore {A} (a : A) (n1 n2 : nat) : store A := Store a (n1, n2). *)


(* (* Step by step transformation of an A-word into a B-word. The two counters are *)
(*    used to discriminate interleaved Dyck-words: *)
(*    - c2 checks for Dyck words on the alphabet (N-W, SE), where N-W is the *)
(*      concatenation of the two letters N and W, used as a single opening *)
(*      parenthesis. Each pair of such parentheses found by c2 is translated into *)
(*      (N-SE, W). *)
(*    - c1 checks for Dyck words on the alphabet (N, SE). Each pair of such *)
(*      parentheses *)
(*      found by c1 is translated into (N, SE). *)
(*    - remaining occurrences of letter W are translated to N *)
(*    - the last case of the match (SE, (0, 0)) is never reached when scanning an *)
(*      A-word. *) *)

(* Definition sA2B (c : nat * nat) (s : step) : store step := *)
(*   match s, c with *)
(*     |  W,  (0, c2)     => mkStore N 0 c2 *)
(*     |  W,  (c1.+1, c2) => mkStore SE c1 c2.+1 *)
(*     |  N,  (c1, c2)    => mkStore N c1.+1 c2 *)
(*     |  SE, (c1, c2.+1) => mkStore W c1 c2 *)
(*     |  SE, (c1.+1, 0)  => mkStore SE c1 0 *)
(*     |  SE, (0, 0)      => mkStore N 0 0 (* junk *) *)
(*   end. *)

(* Arguments sA2B c s : simpl never. *)

(* (* Inverse transformation. *) *)
(* Definition sB2A (c : nat * nat) (s : step) := *)
(*   match s, c with *)
(*     | N,  (0, c2)     => mkStore W 0 c2 *)
(*     | SE, (c1, c2.+1) => mkStore W c1.+1 c2 *)
(*     | N,  (c1.+1, c2) => mkStore N c1 c2 *)
(*     | W,  (c1, c2)    => mkStore SE c1 c2.+1 *)
(*     | SE, (c1, 0)     => mkStore SE c1.+1 0 *)
(*   end. *)

(* Arguments sB2A c s : simpl never. *)

(* (* Folding sA2B on a word from a value of the counter. *) *)





(* (* Folding sB2A on a word from a value of the counter. *) *)
(* Definition readB2A : seq step -> state cmpt2 (seq step) := spipe sB2A. *)

(* (* A pair of a letter s and and a counter c is non-exceptional (noex) if *)
(*    one of the numbers of c is non-zero or else s is not SE. We will see that *)
(*    starting with a zero counter, we never reach a store (s, c) if we process *)
(*    a word in preA. *) *)
(* Definition noex  (s : step) (c : cmpt2) := *)
(*   [|| (c.1 != 0%N), (c.2 != 0%N) | (s != SE)]. *)

(* (* sA2B and sB2A cancel on non exceptional states. *) *)

(* Lemma sA2BK (s : step) (c : cmpt2) : noex s c -> *)
(*   (sdo x <- (sB2A s); sA2B x) c = sreturn s c. *)
(* Proof. by case: s; case: c => [] [| ?] [| ?]. Qed. *)

(* Lemma sB2AK  (s : step) (c : cmpt2) :  noex s c -> *)
(*   (sdo x <- (sA2B s); sB2A x) c = sreturn s c. *)
(* Proof. by case: s; case: c => [] [| ?] [| ?]. Qed. *)

(* (* Datas in an element of sA2B_ghost_data are ghost variables, *)
(*    computed by the program, but not exposed in the code. *)
(*    They are however crucial for stating the appropriate invariant: *)
(*    d1 is the number of Dyck words on (NW, SE) aready processed *)
(*    d2 is the number of Dyck words on (N, SE) aready processed *)
(*    fw is the number of "free" occurrences (i.e. which did not contribute to *)
(*    d1) already processed. We do not prove this property about sub-Dyck *)
(*    words, but only their consequences on the respective numbers of occurrences *)
(*    of each letter in step. *) *)

(* Record ghost_data := *)
(*   GData {ct1: nat; ct2: nat; dy1 : nat; dy2 : nat; free : nat}. *)

(* Definition mkGStore A (a : A) (c1 c2 d1 d2 f : nat) : store ghost_data A := *)
(*   Store a (GData c1 c2 d1 d2 f). *)

(* Definition GData_alt (c : cmpt2) (d1 d2 f : nat) : ghost_data := *)
(*   GData c.1 c.2 d1 d2 f. *)

(* (* Last case is junk *) *)
(* Definition sA2B_ghost_ (s : step) : state ghost_data step := fun g => *)
(* match s, g with *)
(*   |W,  GData 0     c2    d1 d2 f  =>  mkGStore  N  0    c2     d1    d2    f.+1 *)
(*   |W,  GData c1.+1 c2    d1 d2 f  =>  mkGStore SE c1    c2.+1  d1    d2    f *)
(*   |N,  GData c1    c2    d1 d2 f  =>  mkGStore  N c1.+1 c2     d1    d2    f *)
(*   |SE, GData c1    c2.+1 d1 d2 f  =>  mkGStore  W c1    c2     d1.+1 d2    f *)
(*   |SE, GData c1.+1 0     d1 d2 f  =>  mkGStore SE c1     0     d1    d2.+1 f *)
(*   |SE, GData 0     0     d1 d2 f  =>  mkGStore  N  0     0     d1    d2    f *)
(* end. *)

(* Definition sA2B_ghost := nosimpl sA2B_ghost_. *)

(* (* We prove that d1 d2 and f are really ghost variables: they do not *)
(*    affect the computation of the data and of c1 and c2, as witnessed by *)
(*    the fact the these coincide with the values of the (ghost-free) *)
(*    function (spipe sA2B) *) *)
(* Lemma ghost_readA2B_ghost l ci d1i d2i fi *)
(*       (gi := GData_alt ci d1i d2i fi) (sg := spipe sA2B_ghost l gi) *)
(*       (s := spipe sA2B l ci) : *)
(*       [/\ (hidden s).1 = ct1 (hidden sg), (hidden s).2 = ct2 (hidden sg) & *)
(*                                          data s = data sg]. *)
(* Proof. *)
(* rewrite {}/sg {}/s; elim/last_ind: l => [| l h ihl] //=. *)
(* rewrite !hidden_spipe_rcons !data_spipe_rcons -/readA2B. *)
(* case: (hidden (readA2B l ci)) ihl => c1 c2 /=. *)
(* set g := spipe sA2B_ghost _ _; set s := spipe sA2B _ _. *)
(* case: (hidden g) => cg1 cg2 dg1 dg2 gf /=; case=> -> -> -> {c1 c2}. *)
(* by case: h => //=; case: cg1 => [| cg1] //; case: cg2 => [| cg2]. *)
(* Qed. *)

(* (* Complete invariant. By brute force case analysis excepy for the only *)
(*    interesting case of the (tail) induction on l is, i.e. when it ends with SE: *)
(*    in this case the hypothesis (preAword l) forbids ct1 c = ct2 c = 0. We need to *)
(*    kind of reproduce this proof outside this one to ensure we never hit this *)
(*    exceptional case... Can we do better? *) *)

(* Lemma preA_rA2B_ghost_inv l gi (g := hidden (spipe sA2B_ghost l gi)) : *)
(*   preAword l -> *)
(*   [/\  #N l + dy1 gi + dy2 gi + ct1 gi + ct2 gi = dy1 g + dy2 g + ct1 g + ct2 g, *)
(*        #SE l + dy1 gi + dy2 gi = dy1 g + dy2 g & *)
(*        #W l + dy1 gi + ct2 gi + free gi = dy1 g + ct2 g + free g]. *)
(* Proof. *)
(* rewrite {}/g; elim/last_ind: l => [| l h ihl] /= preAlh=> //. *)
(* rewrite !hidden_spipe_rcons -/readA2B. *)
(* have {ihl} /ihl := preA_rcons preAlh. *)
(* move: (hidden (spipe sA2B_ghost l gi)) => c [eN eSE eW]. *)
(* case: h preAlh => /preAwordP preAlh; rewrite !count_mem_rcons !eqxx /=. *)
(* - rewrite !addSn {}eW {}eN {}eSE {preAlh}. *)
(*   by case: c => c1 c2 d1 d2 f /=; rewrite !addnS !addSn. *)
(* - rewrite !addSn {}eW {}eN {}eSE {preAlh}. *)
(*   by case: c => [] [|c1] c2 d1 d2 f /=; rewrite !addnS ?addSn. *)
(* - have {preAlh} lt_SE_N : (#SE l < #N l). *)
(*     by move: (preAlh (size (rcons l SE))); rewrite take_size !count_mem_rcons. *)
(*   have : ct1 c + ct2 c != 0. *)
(*     apply: contraL lt_SE_N; rewrite addn_eq0; case/andP=> /eqP e1 /eqP e2. *)
(*     have e : #SE l + dy1 gi + dy2 gi = #N l + dy1 gi + dy2 gi + ct1 gi + ct2 gi. *)
(*       by rewrite eN e1 e2 !addn0. *)
(*     rewrite -leqNgt -(leq_add2r (dy1 gi + dy2 gi)) !addnA e -[X in _ <= X]addnA. *)
(*     exact:leq_addr. *)
(*   rewrite !addSn {}eW {}eN {}eSE. *)
(*   by case: c => [] [|c1] [|c2] d1 d2 f /=; rewrite ?addnS ?addSn. *)
(* Qed. *)


(* (* Transfer of the invariant on the ghost-free version of the code, taking *)
(*    initial values d1 = d2 = f = 0. Still we do not hide the values of the *)
(*    witness behind existential quantifiers. *) *)
(* Lemma preA_rA2B_inv l ci d1i d2i fi *)
(*       (gi := GData_alt ci d1i d2i fi) *)
(*       (sg := spipe sA2B_ghost l gi) *)
(*       (s := spipe sA2B l ci) : *)
(*   preAword l -> *)
(*   [/\ #N l  + d1i + d2i + ci.1 + ci.2 = *)
(*       dy1 (hidden sg) + dy2 (hidden sg) + (hidden s).1 + (hidden s).2, *)
(*       #SE l + d1i + d2i = dy1 (hidden sg) + dy2 (hidden sg) & *)
(*       #W l  + d1i + ci.2 + free gi = *)
(*       dy1 (hidden sg) + (hidden s).2 + free (hidden sg)]. *)
(* Proof. *)
(* move/(preA_rA2B_ghost_inv gi) => /=. *)
(* by have /= [<- <- _]:= ghost_readA2B_ghost l ci d1i d2i fi. *)
(* Qed. *)

(* (* Now we can prove that the exceptional state is never reached. *) *)
(* Lemma preA_rA2B_noex l a ci (c := hidden (readA2B l ci)) : *)
(*   preAword (rcons l a) -> [|| (c.1 != 0), (c.2 != 0) | (a != SE)]. *)
(* Proof. *)
(* case: a; rewrite ?orbF ?orbT // -negb_and => AlSE. *)
(* have: (#SE l < #N l). *)
(*   move/preAwordP/(_ (size (rcons l SE))): AlSE. *)
(*   by rewrite take_size !count_mem_rcons. *)
(* apply: contraL; case/andP=> /eqP e1 /eqP e2. *)
(* have {AlSE} /(preA_rA2B_inv ci 0 0 0) := preA_rcons AlSE. *)
(* rewrite !addn0; move: (dy1 _) => d1; move: (dy2 _) => d2; move: (free _) => f. *)
(* case=> eN eSE _. *)
(* have {eN eSE} -> : #SE l = #N l + ci.1 + ci.2 by rewrite eN e1 e2 !addn0. *)
(* by rewrite -leqNgt -addnA leq_addr. *)
(* Qed. *)

(* (* And finally that the two functions (spipe sA2B) and (spipe sB2A) cancel. *) *)

(* Lemma readA2BK l : preAword l -> *)
(*                (sdo x <- spipe sA2B l; spipe sB2A (rev x)) =1 sreturn (rev l). *)
(* Proof. *)
(* elim/last_ind: l => [| l a ihl] // preAla ci. *)
(* rewrite (sbind_extl (spipe_rcons _ _ _)) sbind_comp. *)
(* have /sbind_extr -> a0 : *)
(*      (sdo b <- (sdo s1 <- (sA2B a); sreturn (rcons a0 s1)); spipe sB2A (rev b)) *)
(*   =1 (sdo s1 <- (sA2B a); (sdo b <- sreturn (rcons a0 s1); spipe sB2A (rev b))). *)
(*   by move=> c; rewrite sbind_comp. *)
(* have /sbind_extr -> x : *)
(*     (sdo s1 <- (sA2B a); (sdo b <- (sreturn (rcons x s1)); spipe sB2A (rev b))) *)
(*   =1 (sdo s1 <- (sA2B a); spipe sB2A (rev (rcons x s1))). *)
(*   by apply: sbind_extr=> s; rewrite sbind_return. *)
(* have /sbind_extr -> x : *)
(*     (sdo s1 <- (sA2B a); spipe sB2A (rev (rcons x s1))) *)
(*  =1 (sdo s1 <- (sA2B a); spipe sB2A (s1 :: (rev x))). *)
(*   by apply: sbind_extr=> s; rewrite rev_rcons. *)
(* have -> : *)
(*   (sdo x <- (spipe sA2B l); (sdo s1 <- (sA2B a); spipe sB2A (s1 :: rev x))) ci = *)
(*   (sdo x <- (spipe sA2B l); sdo s1 <- sreturn a; sdo l1 <- spipe sB2A (rev x); *)
(*                              sreturn (s1 :: l1)) ci. *)
(*   apply: sbind_eqr. *)
(*   have /sbind_extr -> s1 : *)
(*   spipe sB2A (s1 :: rev (data (spipe sA2B l ci))) =1 *)
(*   sdo s2 <- sB2A s1; sdo l1 <- spipe sB2A (rev (data (spipe sA2B l ci))); *)
(*   sreturn (s2 :: l1). *)
(*     by move=> c; rewrite spipe_cons. *)
(*   by rewrite -sbind_comp; apply: sbind_eql; apply: sB2AK; exact: preA_rA2B_noex. *)
(* rewrite -sbind_comp. *)
(* have /ihl  {ihl} /sbind_extl -> : preAword l by exact: (preA_rcons preAla). *)
(* by rewrite sbind_return rev_rcons. *)
(* Qed. *)
