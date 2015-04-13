Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice tuple finfun fintype finset.
Require Import finfun bigop ssralg ssrnum poly ssrint.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.


(* Three natures of (small) steps are allowed:
   - North (coded by 0)
   - West (coded by 1)
   - SouthWest (coded by 2)
*)

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

(* A walk is a sequence of steps *)
Inductive walk := Walk of seq step.


(* Boilerplate code to install the structures of equality, countable, choice
   type on type step, plus a coercion from walk to sequences. *)

Coercion seq_of_walk (p : walk) := let: Walk n := p in n.

Canonical walk_subType := Eval hnf in [newType for seq_of_walk].

Definition walk_eqMixin := [eqMixin of walk by <:].
Canonical  walk_eqType  := EqType walk walk_eqMixin.

Definition walk_choiceMixin := [choiceMixin of walk by <:].
Canonical  walk_choiceType  := ChoiceType walk walk_choiceMixin.

Definition walk_countMixin   := [countMixin of walk by <:].
Canonical  walk_countType    := CountType walk walk_countMixin.
Canonical  walk_subCountType := Eval hnf in [subCountType of walk].
(* End boilerplate code *)


(* A two-dimentional grid. *)

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

(* We interpret each step as a function : grid -> grid, with the following
   semantic:
   - North (coded by 0) means increasing ordinate of 1, leaving abscissia unchanged
   - West (coded by 1) means decreasing abscissia of 1, leaving ordinate unchanged
   - SouthWest (coded by 2) means decreading both ordinate and abscissia. *)

Definition move_of_step (s : step) (g : grid) : grid :=
  let: Grid (g1, g2) := g in
  match nat_of_ord s with
    |0 => Grid (g1, g2 +1)
    |1 => Grid (g1 - 1, g2)
    |_ => Grid (g1 -1, g2 + 1)
  end.

(* We interpret a sequence of steps as successive moves on the grid, starting
   from the origin *)

Fixpoint position (w : seq step) : grid :=
  match w with
    |[::]    => origin
    |s :: w' => move_of_step s (position w')
  end.