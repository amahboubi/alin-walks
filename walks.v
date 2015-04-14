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

Inductive step := Step of 'I_3.

(* Boilerplate code to install the structures of equality, countable, choice,
   finite type on type step, plus a coercion from step to finite ordinals *)

Coercion ord_of_step (p : step) := let: Step n := p in n.

Canonical step_subType := Eval hnf in [newType for ord_of_step].

Definition step_eqMixin := [eqMixin of step by <:].
Canonical  step_eqType  := EqType step step_eqMixin.

Definition step_choiceMixin := [choiceMixin of step by <:].
Canonical  step_choiceType  := ChoiceType step step_choiceMixin.

Definition step_countMixin   := [countMixin of step by <:].
Canonical  step_countType    := CountType step step_countMixin.
Canonical  step_subCountType := Eval hnf in [subCountType of step].

Definition step_finMixin   := [finMixin of step by <:].
Canonical  step_finType    := FinType step step_finMixin.
Canonical  step_subFinType := Eval hnf in [subFinType of step].
(* End boilerplate code *)

Definition north : step := Step (@Ordinal 3 0 (refl_equal true)).
Definition west  : step := Step (@Ordinal 3 1 (refl_equal true)).
Definition seast : step := Step (@Ordinal 3 2 (refl_equal true)).


(* Boolean predicates characterizing each nature of step *)
Definition is_north (s : step) := s == north.
Definition is_west (s : step)  := s == west.
Definition is_seast (s : step) := s == seast.

(* Case analysis on a step *)
Inductive NxWxSE (s : step) : bool -> bool -> bool -> Type :=
  |North : (is_north s) -> NxWxSE s true false false
  |West : (is_west s) -> NxWxSE s false true false
  |SEast : (is_seast s) -> NxWxSE s false false true.

Lemma stepP (s : step) : NxWxSE s (is_north s) (is_west s) (is_seast s).
Proof.
case: s; case; case => [| m] /=; first by move=> *; exact: North.
case: m => [| m];  first by move=> *; exact: West.
case: m => [| m] //; move=> *; exact: SEast.
Qed.

Definition count_north (w : seq step) := count is_north w.

Definition count_west (w : seq step) := count is_west w.

Definition count_seast (w : seq step) := count is_seast w.

Lemma count_steps_size (w : seq step) :
  count_north w + count_west w + count_seast w = size w.
Proof.
elim: w => // s l ihl /=; case: stepP=> ds /=; rewrite !add0n -ihl.
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
Definition abs (g : grid) := g.1.
Definition ord (g : grid) := g.2.

(* Several predicates describing zones of interest in the grid *)
Definition diag (g : grid) : bool := g.1 == g.2.

(* North (closed) half plane *)
Definition nhalf (g : grid) : bool := g.2 >= 0.

(* South (closed) half plane *)
Definition shalf (g : grid) : bool := g.2 <= 0.

(* East (closed) half plane *)
Definition ehalf (g : grid) : bool := g.1 >= 0.

(* West (closed) half plane *)
Definition whalf (g : grid) : bool := g.1 <= 0.

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
  match nat_of_ord s with
    |0 => Grid (g1, g2 +1)
    |1 => Grid (g1 - 1, g2)
    |_ => Grid (g1 - 1, g2 + 1)
  end.

Arguments move_of_step : simpl never.

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

(* Several predicates on the final position of a final_pos *)

Definition to_diag_traj (g : grid) (w : seq step) : bool :=
  diag (final_pos g w).

Definition to_origin_traj (g : grid) (w : seq step) : bool :=
  final_pos g w == origin.

Definition Iquadrant_traj (g : grid) (w : seq step) : bool :=
  all Iquadrant (trajectory g w).

Definition nhalf_traj (g : grid) (w : seq step) : bool :=
  all nhalf (trajectory g w).

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


(* A walk of length n is an 'A-walk' if its trajectory from the origin stays in
   the upper (north) half-plane and ends at the origin: *)
Definition Awalk (n : nat) (w : walk n) :=
  nhalf_traj origin w && to_origin_traj origin w.

(* A walk of length n is a 'B-walk' if its trajectory from the origin stays in
   quadrant I and ends somewhere on the diagonal: *)
Definition Bwalk (n : nat) (w : walk n) :=
  Iquadrant_traj origin w && to_diag_traj origin w.

(* And the conjecture is the following: *)
(*  Conjecture card_Awalks_Bwalks : forall n : nat, #|@Awalk n| = #|@Bwalk n|. *)

Fixpoint naiveA2B (w : seq step) : seq step :=
  match w with
    | [::] => [::]
    | s :: w' => if (is_west s) && (count_west w' < count_seast w')%N
                 then s :: (naiveA2B w')
                 else north :: (naiveA2B w')
  end.
