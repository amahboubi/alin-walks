Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice tuple finfun fintype finset.
Require Import finfun bigop ssralg ssrnum poly ssrint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* Three natures of (small) steps are allowed:
   - North (coded by 0)
   - West (coded by 1)
   - SouthEast (coded by 2)
Hence we represent steps as (a wrapper around) type 'I_3, which has exactly
three elements. *)

Inductive step : Type := N | W | SE.


(* Installing  structures of equality, countable, choice,
   finite type on type step, plus a coercion from step to finite ordinals. We proceed
   by showing that ord_of_step : step -> 'I_3 has a left inverse, where I_3 is the
   enumerated type type with elements 0, 1, 2. *)

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

Definition step_eqMixin := CanEqMixin ord_of_stepK.
Canonical  step_eqType  := EqType step step_eqMixin.

Definition step_choiceMixin := CanChoiceMixin ord_of_stepK.
Canonical  step_choiceType  := ChoiceType step step_choiceMixin.

Definition step_countMixin := CanCountMixin ord_of_stepK.
Canonical  step_countType  := CountType step step_countMixin.

Definition step_finMixin   := CanFinMixin ord_of_stepK.
Canonical  step_finType    := FinType step step_finMixin.

(* Boolean predicates characterizing each nature of step *)
Definition is_N (s : step) := s == N.
Definition is_W (s : step)  := s == W.
Definition is_SE (s : step) := s == SE.


Definition count_N : seq step -> nat := count is_N.
Definition count_W : seq step -> nat := count is_W.
Definition count_SE : seq step -> nat := count is_SE.

Lemma count_steps_size (w : seq step) :
  count_N w + count_W w + count_SE w = size w.
Proof.
elim: w => // [[]] l /= <-; rewrite !add0n.
- by rewrite -[RHS]add1n !addnA.
- by rewrite [_ + (1 + _)]addnCA -!addnA add1n.
- by rewrite [_ + (1 + _)]addnCA add1n.
Qed.

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
Notation abs  := (fun g : grid => g.1).
Notation ord  := (fun g : grid => g.2).

(* Several predicates describing zones of interest in the grid *)
Definition diag (g : grid) : bool := abs g == ord g.

(* North (closed) half plane *)
Definition nhalf (g : grid) : bool := ord g >= 0.

(* South (closed) half plane *)
Definition shalf (g : grid) : bool := ord g <= 0.

(* East (closed) half plane *)
Definition ehalf (g : grid) : bool := abs g >= 0.

(* West (closed) half plane *)
Definition whalf (g : grid) : bool := abs g <= 0.

(* Quandrant I *)
Definition Iquadrant (g : grid) : bool := nhalf g && ehalf g.

(* (* Quandrant II *) *)
(* Definition IIquadrant (g : grid) : bool := nhalf g && whalf g. *)

(* (* Quandrant III *) *)
(* Definition IIIquadrant (g : grid) : bool := shalf g && whalf g. *)

(* (* Quandrant IV *) *)
(* Definition IVquadrant (g : grid) : bool := shalf g && ehalf g. *)


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


(* We call 'trajectory' the sequence of positions prescribed by a sequence of
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

(* Several predicates on the final position of a trajectory *)

Definition to_diag_traj (g : grid) (w : seq step) : bool :=
  diag (final_pos g w).

(* Not sure this is the usefull form... *)
Lemma to_diag_trajP (g : grid) (w : seq step) :
  reflect (abs g + (count_SE w)%:Z -  (count_W w)%:Z =
           ord g + (count_N w)%:Z - (count_SE w)%:Z)
          (to_diag_traj g w).
Proof. by apply: (iffP eqP); rewrite /to_diag_traj abs_final ord_final. Qed.

Definition loop_traj (g : grid) (w : seq step) : bool := final_pos g w == g.

Lemma loop_trajP (g : grid) (w : seq step) :
  reflect (count_N w = count_SE w /\ count_SE w = count_W w) (loop_traj g w).
Proof.
apply: (iffP andP); rewrite ord_final abs_final; case; last first.
  by move=> -> ->; rewrite !addrK.
rewrite -addrA (can2_eq (addKr g.1) (addNKr g.1)) addNr subr_eq0; move/eqP=> e1.
rewrite -addrA (can2_eq (addKr g.2) (addNKr g.2)) addNr subr_eq0; move/eqP=> e2.
by case: e1 => <-; case: e2.
Qed.

Definition Iquadrant_traj (g : grid) (w : seq step) : bool :=
  all Iquadrant (trajectory g w).

Definition nhalf_traj (g : grid) (w : seq step) : bool :=
  all nhalf (trajectory g w).

(* If g is in the north half plane and the trajectory along w from g stays in
   the north half-plane, then for every prefix of w, the number of SE is smaller
   than the number of N *)
Lemma nhalf_traj_leSEN g w2 w1 : nhalf g -> nhalf_traj g (w1 ++ w2) ->
  (count_SE w1)%:Z <= (count_N w1)%:Z.
Proof. Admitted.

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


(* A sequence is a B-seqeunce if its trajectory from the origin stays in
   quadrant I and ends somewhere on the diagonal: *)
Definition Bseq (w : seq step) :=
  Iquadrant_traj origin w && to_diag_traj origin w.



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

(*  OBSOLETE Some code, to test programming. *)
(* Fixpoint naiveA2B (w : seq step) : seq step := *)
(*   match w with *)
(*     |[::] => [::] *)
(*     |s :: w' => if (is_W s) && (count_W w' < count_ w')%N *)
(*                  then s :: (naiveA2B w') *)
(*                  else north :: (naiveA2B w') *)
(*   end. *)


(* Fixpoint naiveB2A (w : seq step) : seq step := *)
(*   match w with *)
(*     |[::] => [::] *)
(*     |s :: w' => if (is_north s) && ((count_north w) > (count_west w))%N *)
(*                 then west :: (naiveB2A w') *)
(*                 else s :: (naiveB2A w') *)
(*   end. *)

(* Lemma test : {in Bseq, cancel naiveB2A naiveA2B}. *)
(* Proof. Admitted. *)