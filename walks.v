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

Notation "#SE" := count_SE.
Notation "#N" := count_N.
Notation "#W" := count_W.


Lemma count_steps_size (w : seq step) :
  (#N w) + (#W w) + (#SE w) = size w.
Proof.
elim: w => // [[]] l /= <-. rewrite !add0n.
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
Definition abs  := (fun g : grid => g.1).
Definition ord  := (fun g : grid => g.2).

Lemma grid_eq g1 g2 : (g1 == g2) = (abs g1 == abs g2) && (ord g1 == ord g2).
Proof. by []. Qed.

(* Several predicates describing zones of interest in the grid *)
Definition diag (g : grid) : bool := abs g == ord g.

(* North (closed) half plane *)
Definition nhalf (g : grid) : bool := 0 <= ord g.

(* South (closed) half plane *)
Definition shalf (g : grid) : bool := ord g <= 0.

(* East (closed) half plane *)
Definition ehalf (g : grid) : bool := 0 <= abs g.

(* West (closed) half plane *)
Definition whalf (g : grid) : bool := abs g <= 0.

(* Quadrant I *)
Definition Iquadrant := predI nhalf ehalf.

Arguments Iquadrant : simpl never.

(* (* Quadrant II *) *)
(* Definition IIquadrant : bool := predI nhalf whalf. *)

(* (* Quadrant III *) *)
(* Definition IIIquadrant : bool := predI shalf whalf. *)

(* (* Quadrant IV *) *)
(* Definition IVquadrant : bool := predI shalf ehalf. *)


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


(* We call (trajectory g w) the sequence of positions prescribed by a sequence of
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

Lemma size_trajectory g w : size (trajectory g w) = size w.
Proof. by rewrite /trajectory size_scanl. Qed.

Lemma nth_trajectory g1 g2 w n : (n < size w)%N ->
   nth g1 (trajectory g2 w) n = final_pos g2 (take n.+1 w).
Proof. by move=> ltnsw; rewrite nth_scanl. Qed.

Lemma final_pos_take g w n :
  final_pos g (take n.+1 w) = nth (final_pos g w) (trajectory g w) n.
Proof.
case: (ltnP n (size  w)) => hnsw; first by rewrite nth_scanl.
rewrite take_oversize; last by apply: leq_trans hnsw _.
by rewrite nth_default // size_trajectory.
Qed.

Lemma abs_nth_trajectory g1 g2 w n : (n < size w)%N ->
  abs (nth g1 (trajectory g2 w) n) =
  abs g2 + (count_SE (take n.+1 w))%:Z - (count_W (take n.+1 w))%:Z.
Proof. by move=> ?; rewrite nth_trajectory // abs_final. Qed.

Lemma ord_nth_trajectory g1 g2 w n : (n < size w)%N ->
  ord (nth g1 (trajectory g2 w) n) =
  ord g2 + (count_N (take n.+1 w))%:Z - (count_SE (take n.+1 w))%:Z.
Proof. by move=> ?; rewrite nth_trajectory // ord_final. Qed.

Lemma trajectory_final g w : final_pos g w \in g :: trajectory g w.
Proof.
case: w => [|s w]; first by rewrite /= mem_seq1.
rewrite -[X in final_pos g X \in _]take_size [size _]/= -(nth_trajectory g) //.
by rewrite in_cons mem_nth ?orbT // size_trajectory.
Qed.

Lemma trajectory_final_cons g s w :
  final_pos g (s :: w) \in trajectory g (s :: w).
Proof. by rewrite /=; exact: trajectory_final. Qed.

(* Several predicates on the final position of a trajectory *)

Definition to_diag_traj (g : grid) (w : seq step) : bool :=
  diag (final_pos g w).

(* Not sure this is the usefull form... *)
Lemma to_diag_trajP g w :
 reflect (abs g + (count_SE w)%:Z -  (count_W w)%:Z =
          ord g + (count_N w)%:Z - (count_SE w)%:Z)
         (to_diag_traj g w).
Proof. by apply: (iffP eqP); rewrite /to_diag_traj abs_final ord_final. Qed.

Lemma oto_diag_trajP w :
 reflect ((count_SE w)%:Z - (count_W w)%:Z = (count_N w)%:Z - (count_SE w)%:Z)
         (to_diag_traj origin w).
Proof.
rewrite -[LHS]add0r -[RHS]add0r !addrA; exact: (to_diag_trajP origin).
Qed.

Definition loop_traj (g : grid) (w : seq step) : bool := final_pos g w == g.

Lemma loop_trajP (g : grid) (w : seq step) :
  reflect (count_N w = count_SE w /\ count_SE w = count_W w) (loop_traj g w).
Proof.
rewrite /loop_traj grid_eq.
apply: (iffP andP); rewrite ord_final abs_final; case; last first.
  by move=> -> ->; rewrite !addrK.
rewrite -!addrA ![_ + (_ - _) == _](can2_eq (addKr _) (addNKr _)) !addNr !subr_eq0.
by move=> /eqP [] <- /eqP [] ->.
Qed.


(* Properties of trajectories that start and stay in the north half plane *)
Definition nhalf_traj (g : grid) (w : seq step) : bool :=
  all nhalf (g :: (trajectory g w)).

Lemma nhalf_trajE g w : nhalf_traj g w = nhalf g && all nhalf (trajectory g w).
Proof. by []. Qed.

Lemma nhalf_traj_cat  g w1 w2 :
  nhalf_traj g (w1 ++ w2) =
  nhalf_traj g w1 && nhalf_traj (final_pos g w1) w2.
Proof.
rewrite [in LHS]/nhalf_traj trajectory_cat -cat_cons all_cat.
apply: andb_id2l; rewrite nhalf_trajE; move/allP/(_ _ (trajectory_final _ _))->.
done.
Qed.

(* If the trajectory along w from the origin stays in the north half-plane,
  then the number of SE in w is smaller than the number of N *)
Lemma nhalf_otraj_le w : nhalf_traj origin w ->
  (count_SE w <= count_N w)%N.
Proof.
move/allP/(_ _ (trajectory_final _ _)); rewrite /nhalf ord_final add0r subr_ge0.
done.
Qed.

(* If  the trajectory along w from the origin stays in the north half-plane,
  then for every of its prefixes w' the number of SE in w' is smaller than
  the number of N *)


Lemma nhalf_otraj_pre w1 w2 : nhalf_traj origin (w1 ++ w2) ->
  (count_SE w1 <= count_N w1)%N.
Proof. by rewrite nhalf_traj_cat; case/andP=> /nhalf_otraj_le. Qed.

(* This is in fact characterizing trajectories from the origin that stay in
   the north plane *)
Lemma nhalf_otrajP w :
  reflect (forall n, count_SE (take n w) <= count_N (take n w))%N
          (nhalf_traj origin w).
Proof.
apply: (iffP idP) => [ntw n| countle].
  by move: ntw; rewrite -{1}[w](cat_take_drop n); move/nhalf_otraj_pre.
rewrite nhalf_trajE /=; apply/(all_nthP origin) => i ltisw.
rewrite /nhalf ord_nth_trajectory -?(size_trajectory origin) // subr_ge0.
exact: countle.
Qed.

(* The analogue theory for trajectories staying in the east half plane.
   Copy-paste mutatis mutandis. *)

Definition ehalf_traj (g : grid) (w : seq step) : bool :=
  all ehalf (g :: (trajectory g w)).

Lemma ehalf_trajE g w :
  ehalf_traj g w = ehalf g && all ehalf (trajectory g w).
Proof. by []. Qed.

Lemma ehalf_traj_cat  g w1 w2 :
  ehalf_traj g (w1 ++ w2) =
  ehalf_traj g w1 && ehalf_traj (final_pos g w1) w2.
Proof.
rewrite [in LHS]/ehalf_traj trajectory_cat -cat_cons all_cat.
apply: andb_id2l; rewrite ehalf_trajE; move/allP/(_ _ (trajectory_final _ _))->.
done.
Qed.

(* If  the trajectory along w from the origin stays in the east half-plane,
  then the number of W in w is smaller than the number of SE *)
Lemma ehalf_otraj_le w : ehalf_traj origin w -> (count_W w <= count_SE w)%N.
Proof.
move/allP/(_ _ (trajectory_final _ _)); rewrite /ehalf abs_final add0r subr_ge0.
done.
Qed.

(* If  the trajectory along w from the origin stays in the north half-plane,
  then for every of its prefixes w' the number of W in w' is smaller than
  the number of SE *)

Lemma ehalf_otraj_pre w1 w2 : ehalf_traj origin (w1 ++ w2) ->
  (count_W w1 <= count_SE w1)%N.
Proof. by rewrite ehalf_traj_cat; case/andP=> /ehalf_otraj_le. Qed.

(* This is in fact characterizing trajectories from the origin that stay in
   the east plane *)
Lemma ehalf_otrajP w :
  reflect (forall n, count_W (take n w) <= count_SE (take n w))%N
          (ehalf_traj origin w).
Proof.
apply: (iffP idP) => [ntw n| countle].
  by move: ntw; rewrite -{1}[w](cat_take_drop n); move/ehalf_otraj_pre.
rewrite ehalf_trajE /=; apply/(all_nthP origin) => i ltisw.
rewrite /ehalf abs_nth_trajectory -?(size_trajectory origin) // subr_ge0.
exact: countle.
Qed.

Definition Iquadrant_traj (g : grid) (w : seq step) : bool :=
  all Iquadrant (g :: (trajectory g w)).

Lemma Iquadrant_trajE g w :
  Iquadrant_traj g w = Iquadrant g && all Iquadrant (trajectory g w).
Proof. by []. Qed.

Lemma Iquadrant_nhalf_traj g w : Iquadrant_traj g w -> nhalf_traj g w.
Proof. by rewrite [Iquadrant_traj _ _]all_predI; case/andP. Qed.

Lemma Iquadrant_ehalf_traj g w : Iquadrant_traj g w -> ehalf_traj g w.
Proof. by rewrite [Iquadrant_traj _ _]all_predI; case/andP. Qed.

Lemma Iquadrant_nehalf_traj g w :
  Iquadrant_traj g w = (nhalf_traj g w) && (ehalf_traj g w).
Proof. by rewrite /Iquadrant_traj /Iquadrant all_predI. Qed.

Lemma Iquadrant_traj_cat  g w1 w2 :
  Iquadrant_traj g (w1 ++ w2) =
  Iquadrant_traj g w1 && Iquadrant_traj (final_pos g w1) w2.
Proof.
rewrite [in LHS]/Iquadrant_traj trajectory_cat -cat_cons all_cat.
apply: andb_id2l => /allP/(_ _ (trajectory_final _ _)).
by rewrite Iquadrant_trajE; move->.
Qed.

Lemma Iquadrant_otraj_le w : Iquadrant_traj origin w ->
  (count_W w <= count_SE w <= count_N w)%N.
Proof.
move=> itow; rewrite ehalf_otraj_le; last exact: Iquadrant_ehalf_traj.
rewrite nhalf_otraj_le //; exact: Iquadrant_nhalf_traj.
Qed.

Lemma Iquadrant_otraj_pre w1 w2 : Iquadrant_traj origin (w1 ++ w2) ->
  (count_W w1 <= count_SE w1 <= count_N w1)%N.
Proof.
by rewrite Iquadrant_traj_cat; case/andP=> itow1 _; apply: Iquadrant_otraj_le.
Qed.

Lemma Iquadrant_otrajP w :
  reflect (forall n, count_W (take n w) <= count_SE (take n w)
                                       <= count_N (take n w))%N
          (Iquadrant_traj origin w).
Proof.
apply: (iffP idP) => [ntw n| countle].
  move/Iquadrant_nhalf_traj: (ntw) => /nhalf_otrajP ->.
  by move/Iquadrant_ehalf_traj: (ntw) => /ehalf_otrajP ->.
rewrite Iquadrant_nehalf_traj.
have /nhalf_otrajP -> :
  forall n, (count_SE (take n w))%:Z <= (count_N (take n w))%:Z.
  by move=> n; case/andP: (countle n).
by apply/ehalf_otrajP=> n; case/andP: (countle n).
Qed.


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

(* Any prefix of an Aseq has more N than SE: *)
Lemma Aseq_pre w1 w2 : w1 ++ w2 \in Aseq ->
  (count_SE w1)%:Z <= (count_N w1)%:Z.
Proof. by move/Aseq_nhalf/nhalf_otraj_pre. Qed.

Lemma AseqP w : reflect
                [/\ forall n, (count_SE (take n w))%:Z <= (count_N (take n w))%:Z,
                    count_N w = count_SE w & count_SE w = count_W w]
                (Aseq w).
Proof.
apply: (iffP idP).
  by rewrite /Aseq; case/andP => /nhalf_otrajP=> ? /loop_trajP; case.
by rewrite /Aseq; case=> /nhalf_otrajP => -> /= he1 he2; apply/loop_trajP.
Qed.

(* A sequence is a B-sequence if its trajectory from the origin stays in
   quadrant I and ends somewhere on the diagonal: *)
Definition Bseq (w : seq step) :=
  Iquadrant_traj origin w && to_diag_traj origin w.

Lemma Bseq_Iquadrant w : w \in Bseq -> Iquadrant_traj origin w.
Proof. by case/andP. Qed.

Lemma Bseq_oto_diag w : w \in Bseq -> to_diag_traj origin w.
Proof. by case/andP. Qed.

(* A Bseq necessarily has less W than SE than N *)
Lemma Bseq_count_le w : w \in Bseq ->
   (count_W w)%:Z <= (count_SE w)%:Z <= (count_N w)%:Z.
Proof. by move/Bseq_Iquadrant/Iquadrant_otraj_le. Qed.

Lemma Bseq_pre w1 w2 : w1 ++ w2 \in Bseq ->
   (count_W w1)%:Z <= (count_SE w1)%:Z <= (count_N w1)%:Z.
Proof. by move/Bseq_Iquadrant/Iquadrant_otraj_pre. Qed.

(* Again we inherit from the tentative statement of
   to_diagP, probably not in its most convenient form. *)
Lemma Bseq_count w : w \in Bseq ->
  (count_SE w)%:Z - (count_W w)%:Z = (count_N w)%:Z - (count_SE w)%:Z.
Proof. by move/Bseq_oto_diag/oto_diag_trajP. Qed.

Lemma BseqP w : reflect
                  ((forall n, (count_W (take n w))%:Z <= (count_SE (take n w))%:Z
                                                      <= (count_N (take n w))%:Z)
                  /\
                    (count_SE w)%:Z - (count_W w)%:Z =
                    (count_N w)%:Z - (count_SE w)%:Z)
                  (Bseq w).
Proof.
apply: (iffP idP).
  by rewrite /Bseq; case/andP => /Iquadrant_otrajP=> ? /oto_diag_trajP.
by case=> /Iquadrant_otrajP iw /oto_diag_trajP odw; rewrite /Bseq iw.
Qed.

(* A state monad for datas of type A equipped with two counters *)

Definition cmpt2 := (nat * nat)%type.

(* The intuition is to represent the word transformations using automatons,
   with steps labelled with pairs of natural numbers and transitions labelled
   with 'step' letters. *)


Section StateMonadDefs.

Context {A B C : Type}.

Record store (A : Type) : Type := Store {data : A; ct : cmpt2}.

Definition mkStore {A} a n1 n2 : store A := Store a (n1, n2).

Definition state (A : Type) :=  cmpt2 -> store A.

Definition sreturn {A} (a : A) : state A := fun c => Store a c.

Definition sbind {A B} (sa : state A) (f : A -> state B) : state B :=
  fun x => let: Store a c := sa x in f a c.


(* A convenient notation for programming in monadic style, borrowed to Cyril :) *)
Notation "'sdo' x <- y ; z" :=
  (sbind y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' 'sdo'  x  <-  y ;  '/' z ']'").

Lemma sbind_return (a : A) (f : A -> state B) :
  (sdo x <- (sreturn a); f x) = f a.
Proof. by []. Qed.

Lemma sreturn_bind (sa : state A) : (sdo x <- sa; sreturn x) =1 sa.
Proof. by move=> c; rewrite /sbind; case: (sa c). Qed.

Lemma sbind_comp (f : A -> state B) (g : B -> state C) (sa : state A) :
(sdo b <- (sdo a <- sa; f a); g b) =1 (sdo a <- sa; sdo b <- (f a); g b).
Proof. by move=> c; rewrite /sbind; case: (sa c). Qed.

Definition srev (sl : state (seq A)) := sdo l <- sl; sreturn (rev l).

Lemma data_srev sl c : data (srev sl c) = rev (data (sl c)).
Proof. by rewrite /srev /= /sbind; case: (sl c). Qed.

Lemma ct_srev sl c : ct (srev sl c) = ct (sl c).
Proof. by rewrite /srev /= /sbind; case: (sl c). Qed.


Fixpoint spipe (f : A -> state B) (l : seq A) : state (seq B) :=
  if l is a :: l then
    sdo s1 <- f a;
    sdo l1 <- spipe f l;
    sreturn (s1 :: l1)
 else sreturn [::].

Lemma data_spipe_nil f c : data (spipe f [::] c) = [::].
Proof. by []. Qed.

Lemma data_spipe_cons f s l c :
  data (spipe f (s :: l) c) =
  data (f s c) :: data (spipe f l (ct (f s c))).
Proof.
by rewrite /sbind /= /sbind; case: (f s c) => d1 c1 /=; case: (spipe f l c1).
Qed.

(* Remark: If we exchange the two sdo in the code of spipe, we would
    obtain a piping which
   follows the above specification (which would suit an interpretation of
    words as trajectories where the last letter codes the first move).
Lemma data_spipe_cons f s l c :
  data (spipe f (s :: l) c) =
  data (f s (ct (spipe f l c))) :: data (spipe f l c).
Proof.
by rewrite /sbind /= /sbind; case:  (spipe f l c) => d1 c1; case: (f s c1).
Qed.
 *)

Lemma ct_spipe_nil f c : ct (spipe f [::] c) = c.
Proof. by []. Qed.

Lemma ct_spipe_cons f s l c :
  ct (spipe f (s :: l) c) = ct (spipe f l (ct (f s c))).
Proof.
by rewrite /sbind /= /sbind; case: (f s c) => d1 c1 /=; case: (spipe f l c1).
Qed.

Lemma data_spipe_cat f l1 l2 c :
  data (spipe f (cat l1 l2) c) =
  (data (spipe f l1 c)) ++ (data (spipe f l2 (ct (spipe f l1 c)))).
Proof.
elim: l1 l2 c => [| s l1 ihl1 l2 c] //; rewrite cat_cons [LHS]data_spipe_cons.
by rewrite ihl1 data_spipe_cons ct_spipe_cons cat_cons.
Qed.

Lemma data_spipe_rcons f s l c :
  data (spipe f (rcons l s) c) =
  rcons (data (spipe f l c)) (data (f s (ct (spipe f l c)))).
Proof. by rewrite -cats1 data_spipe_cat -cats1 data_spipe_cons. Qed.

Lemma ct_spipe_cat f l1 l2 c :
  ct (spipe f (l1 ++ l2) c) = ct (spipe f l2 (ct (spipe f l1 c))).
Proof.
elim: l1 l2 c => [| s l1 ihl1 l2 c] //; rewrite cat_cons [LHS]ct_spipe_cons.
by rewrite ihl1 ct_spipe_cons.
Qed.

Lemma ct_spipe_rcons f s l c :
  ct (spipe f (rcons l s) c) = ct (f s (ct (spipe f l c))).
Proof. by rewrite -cats1 ct_spipe_cat ct_spipe_cons. Qed.

End StateMonadDefs.

Notation "'sdo' x <- y ; z" :=
  (sbind y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' 'sdo'  x  <-  y ;  '/' z ']'").

(* Step by step transformation of an A-word into a B-word. The two counters are
   used to discriminate interleaved Dyck-words:
   - c2 checks for Dyck words on the alphabet (N-W, SE), where N-W is the
     concatenation of the two letters N and W, used as a single opening
     parenthesis. Each pair of such parentheses found by c2 is translated into
     (N-SE, W).
   - c1 checks for Dyck words on the alphabet (N, SE). Each pair of such parentheses
     found by c1 is translated into (N, SE).
   - remaining occurrences of letter W are translated to N
   - the last case of the match (SE, (0, 0)) is never reached when scanning an A-word. *)

Definition sA2B (s : step) : state step := fun c =>
  match s, c with
    |  W, (0, c2)      =>  mkStore N 0 c2
    |  W, (c1.+1, c2)  =>  mkStore SE c1 c2.+1
    |  N, (c1, c2)     =>  mkStore N c1.+1 c2
    |  SE, (c1, c2.+1) =>  mkStore W c1 c2
    |  SE, (c1.+1, 0)  =>  mkStore SE c1 0
    |  SE, (0, 0)      =>  mkStore N 0 0 (* junk *)
  end.

Arguments sA2B s c : simpl never.

(* Inverse transformation. *)
Definition sB2A (s : step) : state step := fun c =>
  match s, c with
    | N, (0, c2)      => mkStore W 0 c2
    | SE, (c1, c2.+1) => mkStore W c1.+1 c2
    | N, (c1.+1, c2)  => mkStore N c1 c2
    | W, (c1, c2)     => mkStore SE c1 c2.+1
    | SE, (c1, 0)     => mkStore SE c1.+1 0
  end.

Arguments sB2A s c : simpl never.

(* For any state x, if the counter statisfies the premisse, performing one step
   transformation after the other keeps x unchanged. Note that an A-word
   cannot start with SE hence in particular, this premisse condition is
   verified initially. *)

Lemma sA2BK (s : step) (c : cmpt2) :
  [|| (c.1 != 0%N), (c.2 != 0%N) | (s != SE)] ->
  (sdo x <- (sB2A s); sA2B x) c = sreturn s c.
Proof. by case: s; case: c => [] [| n1] [|n2]. Qed.

Lemma sB2AK  (s : step) (c : cmpt2) :
  [|| (c.1 != 0%N), (c.2 != 0%N) | (s != SE)] ->
  (sdo x <- (sA2B s); sB2A x) c = sreturn s c.
Proof. by case: s; case: c => [] [| n1] [|n2]. Qed.

Definition readA2B : seq step -> state (seq step) := spipe sA2B.
Definition readB2A : seq step -> state (seq step) := spipe sB2A.

Definition csum (c : cmpt2) : nat := (c.1 + c.2)%N.

Lemma csum0 c : csum c = 0%N -> c = (0%N, 0%N).
Proof. by case: c => [[| c1]] [| c2]. Qed.

Lemma csum0l c : csum (0%N, c) = c. by []. Qed.

Lemma csum0r c : csum (c, 0%N) = c. by rewrite /csum addn0. Qed.

Lemma csum_A2B_N c : csum (ct (sA2B N c)) = (csum c).+1.
Proof. by rewrite /csum; case: c => [[| c1]] [| c2]. Qed.


Lemma csum_A2B_W c : csum (ct (sA2B W c)) = csum c.
Proof.
by rewrite /csum; case: c => [[| c1]] [| c2]; rewrite ?addn0 ?addn1 ?addnS.
Qed.

(* This one is a bit clumsy. *)
Lemma csum_A2B_SE c : csum c = (csum (ct (sA2B SE c)) + (csum c != 0))%N.
Proof.
by rewrite /csum; case: c => [[| c1]] [| c2]; rewrite ?addn0 ?addn1 ?addnS.
Qed.

Definition preA l :=   (forall n, (#SE (take n l) <= #N (take n l)))%N.

Lemma preA_rcons l a : preA (rcons l a) -> preA l.
Proof.
rewrite /preA => preAla n; case: (ltnP n (size l)) => [ltnsl |].
  by move: (preAla n); rewrite -cats1 take_cat ltnsl.
by move/take_oversize->; move: (preAla (size l)); rewrite -cats1 take_size_cat.
Qed.

Lemma count_mem_rcons {T : eqType} l (a b : T) :
  count_mem a (rcons l b) = ((count_mem a l) + (b == a))%N.
Proof. by rewrite -cats1 count_cat /= addn0. Qed.

(* d1 is the number of Dyck words on (NW, SE) aready processed
   d2 is the number of Dyck words on (N, SE) aready processed
   fw is the number of "free" occurrences (i.e. which did not contribute to
   d1) already processed. *)
Record sA2B_invariant_data := InvData {d1 : nat; d2 : nat; fw : nat}.

Lemma preA_sA2B_invariant l ci (c := ct (readA2B l ci)) :
  preA l ->
  exists i : sA2B_invariant_data,
    [/\ (csum ci + #N l = (d1 i) + (d2 i) + csum c)%N,
        (#SE l = (d1 i) + (d2 i))%N &
        (ci.2 + #W l = (d1 i) + c.2 + (fw i))%N].
Proof.
rewrite {}/c; elim/last_ind: l => [| l h ihl] /= preAlh.
   by exists (InvData 0%N 0%N 0%N); rewrite /= addn0.
rewrite !ct_spipe_rcons -/readA2B.
have {ihl} /ihl [[dl1 dl2 fwl /=]] : preA l by exact: preA_rcons.
move: (ct (readA2B l ci)) => c [eN eSE eW].
case: h preAlh => preAlh.
- have -> : #N (rcons l N) = (#N l).+1 by rewrite /count_N count_mem_rcons addn1.
  have -> : #W (rcons l N) = #W l by rewrite /count_W count_mem_rcons addn0.
  have -> : #SE (rcons l N) = #SE l by rewrite -cats1 /count_SE count_cat addn0.
  rewrite !csum_A2B_N !addnS eN; exists (InvData dl1 dl2 fwl); split => //=.
  suff {eN eW} -> : (ct (sA2B N c)).2 = c.2 by [].
  by case: c.
- have -> : #N (rcons l W) = #N l by rewrite /count_N count_mem_rcons addn0.
  have -> : #W (rcons l W) = (#W l).+1 by rewrite /count_W count_mem_rcons addn1.
  have -> : #SE (rcons l W) = #SE l by rewrite -cats1 /count_SE count_cat addn0.
  rewrite !csum_A2B_W !addnS {}eW {}eN {}eSE {preAlh}; case: c => [[| c1]] c2 /=.
    by rewrite csum0l /=; exists (InvData dl1 dl2 fwl.+1) => /=.
  by exists (InvData dl1 dl2 fwl); split => //=; rewrite addnS addSn.
- have nN : #N (rcons l SE) = #N l by rewrite /count_N count_mem_rcons addn0.
  have nW : #W (rcons l SE) = #W l by rewrite /count_W count_mem_rcons addn0.
  have nSE : #SE (rcons l SE) = (#SE l).+1.
    by rewrite /count_SE count_mem_rcons addn1.
  have {preAlh} lt_SE_N : (#SE l < #N l)%N.
    by move: (preAlh (size (rcons l SE))); rewrite take_size nSE nN.
  have {lt_SE_N} : csum c != 0%N.
    apply: contraL lt_SE_N => /eqP sumc0.
    by rewrite -leqNgt -[#SE l]addn0 eSE -sumc0 -eN leq_addl.
  rewrite {}nN {}nW {}nSE {}eN {}eSE {}eW.
  case: c => [[|c1]] [| c2] // _; rewrite ?csum0r ?csum0l /=.
  - by exists (InvData dl1.+1 dl2 fwl); rewrite ?addnS ?addSn.
  - by exists (InvData dl1 dl2.+1 fwl); rewrite /= addn0 !addnS !addSn.
  - by exists (InvData dl1.+1 dl2 fwl); rewrite /csum /= addnS !addSn !addnS.
Qed.


(*
Lemma whatWeWant l : l \in Aseq ->
  (sdo x <- (srev (readA2B l)); readB2A x) (0, 0)%N = sreturn (rev l) (0, 0)%N.
Proof.
elim: l => [|t l ihl] //= htl.
rewrite /srev.
rewrite sbind_comp /=.
Admitted.


Definition stateA2B : seq step -> state (seq step) := srev \o (spipe sA2B).

Lemma data_stateA2B_cons s l c :
 data (stateA2B (s :: l) c) =
 rcons (data (stateA2B l (ct (sA2B s c)))) (data (sA2B s c)).
Proof.
by rewrite /stateA2B data_srev data_spipe_cons rev_cons data_srev.
Qed.

Lemma data_stateA2B_rcons s l c :
 data (stateA2B (rcons l s) c) =
 (data (sA2B s (ct (stateA2B l c)))) :: data (stateA2B l c).
Proof.
by rewrite /stateA2B data_srev data_spipe_rcons rev_rcons data_srev ct_srev.
Qed.

Lemma ct_stateA2B_cons s l c :
 ct (stateA2B (s :: l) c) = ct (stateA2B l (ct (sA2B s c))).
Proof. by rewrite /stateA2B ct_srev ct_spipe_cons ct_srev. Qed.

Lemma ct_stateA2B_rcons s l c :
 ct (stateA2B (rcons l s) c) = ct (sA2B s (ct (spipe sA2B l c))).
Proof. by rewrite /stateA2B !ct_srev ct_spipe_rcons. Qed.

Definition seqA2B l := data (stateA2B l (0, 0)%N).

Lemma seqA2BP l : l \in Aseq -> seqA2B l \in Bseq.
Admitted.

Search _ card in fintype.
Search _ injective cancel.


Definition readB2A : seq step -> state (seq step) := spipe sB2A.
Definition readA2B : seq step -> state (seq step) := spipe sA2B.

Lemma whatWeWant l : l \in Aseq ->
  (sdo x <- (srev (readA2B l)); readB2A x) (0, 0)%N = sreturn (rev l) (0, 0)%N.
Admitted.




(* Dyck words, as sequences of booleans, where false is the opening parenthesis
   and true is the closing one *)

Fixpoint dyck_c (l : seq bool) (c : nat) : bool :=
  match l with
    | [::] => c == 0%N
    | s :: l' => if (~~ s) then dyck_c l' c.+1
                else if c is c'.+1 then dyck_c l' c' else false
  end.

Definition dyck l := dyck_c l 0%N.

Lemma dyck_cP c l : reflect
 ((forall n, (count_mem true (take n l) <= c + count_mem false (take n l))%N) /\
 (c + count_mem false l = count_mem true l)%N) (dyck_c l c).
Proof.
apply: (iffP idP).
  elim: l c => [|b l ihl] c //; first by move/eqP->.
  case: b; last first.
  - by move/ihl => [? hl]; split => [[|n] //|]; rewrite /= add0n addnA addn1 ?hl.
  - case: c => [|c] // /ihl => [] [hl1 hl2]; split => [[|n]|] //=; rewrite add0n.
    + rewrite !addSn add0n ltnS; exact: leq_trans (hl1 _) _.
    + by rewrite !addSn add0n hl2.
elim: l c => [ /= |b l ihl] c; first by rewrite addn0; case => _ ->.
case: b; last first.
  case=> h1 h2; apply: ihl; split; last by rewrite -[RHS]h2 /= addnA addn1.
  case=> [|n] /=; first by rewrite take0 /= addn0.
  by apply: leq_trans (h1 n.+2) _; rewrite /= addnA addn1.
case: c => [|c] [h1 h2] /=; first by move: (h1 1%N); rewrite /= take0 !addn0.
apply: ihl; split; last by move: h2; rewrite /= add0n add1n addSn; case.
by move=> n; move: (h1 n.+1); rewrite /= add0n add1n addSn.
Qed.

Lemma dyckP l : reflect
 ((forall n, (count_mem true (take n l) <= count_mem false (take n l))%N) /\
 (count_mem false l = count_mem true l)) (dyck l).
Proof. by apply: (iffP (dyck_cP _ _)). Qed.

Lemma dyck_trueN l : dyck (true :: l) = false.
Proof.
by apply/negP; move/dyckP; case; move/(_ 1%N); rewrite /= take0 /= !addn0.
Qed.

(* Entangling words wt and wf, following the pattern provided by m:
   - filter is_true m becomes a prefix of wt (padded with adflt if necessary)
   - filter is_false m becomes a prefix of wf (padded with adflt if necessary)
*)
Definition bitseqN (m : bitseq) := map negb m.

Lemma count_bipartition {T} (p : pred T) (m : bitseq) (s : seq T) :
   count p (take (size m) s) =
  (count p (mask m s) + count p (mask (bitseqN m) s))%N.
elim: m s => [|bm m ihm] s; first by rewrite /= take0.
by case: s => [|hs s] //=; case: bm; rewrite /= ihm addnA // addnCA addnA.
Qed.

Lemma count_nseq  {T} (p : pred T) (t : T) (n : nat) :
  count p (nseq n t) = ((p t) * n)%N.
Proof.
case hpt: (p t); last first.
  by rewrite mul0n; apply/eqP; rewrite eqn0Ngt -has_count has_nseq hpt andbF.
rewrite mul1n -[RHS](size_nseq n t); apply/eqP; rewrite -all_count all_nseq hpt.
by rewrite orbT.
Qed.

Lemma count_sub {T : eqType} (p : pred T) (s1 s2 : seq T) :
  subseq s1 s2 -> (count p s1 <= count p s2)%N.
Proof.
elim: s2 s1 => [|t2 s2 ihs2] s1 //; first by move/eqP->.
case: s1 => [|t1 s1] //=; case: ifP=> ht12 hs12.
- rewrite (eqP ht12) leq_add2l; exact: ihs2.
- move/ihs2: hs12=> /= h; apply: leq_trans h _; exact: leq_addl.
Qed.

Lemma take_subseq {T : eqType} (s : seq T) n : subseq (take n s) s.
Proof.
elim: n s => [|n] s; first by rewrite take0 sub0seq.
by case=> [| t u] //; rewrite /= eqxx.
Qed.

Lemma count_take {T : eqType} (p : pred T) (s1 : seq T) n:
  (count p (take n s1) <= count p s1)%N.
Proof. apply: count_sub;  exact: take_subseq. Qed.

Section Shuffle.

Variables (A : Type) (adflt : A).

Fixpoint shuffle (m : bitseq) (wt wf : seq A) : seq A :=
  match m with
    |[::] => [::]
    |true :: m'  => if wt is hwt :: wt' then hwt :: shuffle m' wt' wf
                    else adflt :: shuffle m' wt wf
    |false :: m' => if wf is hwf :: wf' then hwf :: shuffle m' wt wf'
                    else adflt :: shuffle m' wt wf
  end.

Lemma shuffle_consT m wt wf :
  shuffle (true :: m) wt wf = if wt is hwt :: wt' then hwt :: shuffle m wt' wf
                              else adflt :: shuffle m wt wf.
Proof. by []. Qed.

Lemma shuffle_consF m wt wf :
  shuffle (false :: m) wt wf = if wf is hwf :: wf' then hwf :: shuffle m wt wf'
                               else adflt :: shuffle m wt wf.
Proof. by []. Qed.

Lemma size_shuffle m wt wf : size (shuffle m wt wf) = size m.
Proof.
elim: m wt wf => [|[] m ihm] //; first by case=> [|hwt wt] wf /=; rewrite ihm.
by move=> wt; case=> [|hwf wf] /=; rewrite ihm.
Qed.

Lemma mask_shuffleT m wt wf :
  mask m (shuffle m wt wf) =
  (take (count_mem true m) wt) ++ nseq ((count_mem true m) - size wt)%N adflt.
Proof.
elim: m wt wf => [|[] m ihm] wt wf; first by rewrite take0.
- by rewrite shuffle_consT; case: wt => [|hwt wt] /=; rewrite ihm //= subn0.
- by rewrite shuffle_consF; case: wf => [|hwf wf] /=; rewrite ihm //= subn0.
Qed.

Lemma mask_shuffleF m wt wf :
  mask (bitseqN m) (shuffle m wt wf) =
  (take (count_mem false m) wf) ++ nseq ((count_mem false m) - size wf)%N adflt.
Proof.
elim: m wt wf => [|[] m ihm] wt wf; first by rewrite take0.
- by rewrite shuffle_consT; case: wt => [|hwt wt]; rewrite [mask _ _]/= ihm.
- by rewrite shuffle_consF; case: wf => [|hwf wf] /=; rewrite ihm //= subn0.
Qed.

Lemma count_shuffle m wt wf p :
  count p (shuffle m wt wf) =
  (count p (take (count_mem true m) wt) + count p (take (count_mem false m) wf) +
  (p adflt) * ((count_mem true) m - size wt + ((count_mem false) m - size wf)))%N.
Proof.
have -> : shuffle m wt wf = take (size m) (shuffle m wt wf).
  by rewrite take_oversize // size_shuffle.
rewrite count_bipartition mask_shuffleT mask_shuffleF !count_cat !count_nseq.
rewrite -!addnA; congr (_ + _)%N; rewrite addnCA; congr (_ + _)%N.
by rewrite -mulnDr.
Qed.

Lemma count_shuffle_exact m wt wf p :
  size wt = count_mem true m -> size wf = count_mem false m ->
  count p (shuffle m wt wf) = (count p wt + count p wf)%N.
Proof.
move=> swt swf; rewrite count_shuffle -swf -swt !take_oversize // !subnn muln0.
by [].
Qed.

Lemma take_shuffle m wt wf n :
  take n (shuffle m wt wf) = shuffle (take n m) wt wf.
Proof.
elim: n m wt wf => [|n ihn] [| [] m] wt wf; rewrite ?take0 //.
- by case: wt ihn => [|bwt wt] ihn //=; rewrite ihn.
- by case: wf ihn => [|bwf wf] ihn //=; rewrite ihn.
Qed.

Lemma count_take_shuffle_exact m wt wf p1 p2 n :
  size wt = count_mem true m -> size wf = count_mem false m ->
  (forall n, count p1 (take n wt) <= count p2 (take n wt))%N ->
  (forall n, count p1 (take n wf) <= count p2 (take n wf))%N ->
  (count p1 (take n (shuffle m wt wf)) <= count p2 (take n (shuffle m wt wf)))%N.
Proof.
move=> swt swf hpt hpf; rewrite take_shuffle !count_shuffle.
apply: leq_add; first exact: leq_add.
have -> : ((count_mem true) (take n m) - size wt = 0)%N.
  apply/eqP; rewrite subn_eq0 swt; exact: count_take.
have -> : ((count_mem false) (take n m) - size wf = 0)%N.
  apply/eqP; rewrite subn_eq0 swf; exact: count_take.
by rewrite addn0 muln0.
Qed.

End Shuffle.

Definition dyck_N_SE (m : bitseq) : seq step :=
  map (fun b => if b then SE else N) m.

(* Definition dyck_NSE_W1 (m : bitseq) := *)
(*   flatten (map (fun b => if b then [:: W] else [:: N; SE]) m). *)

Definition dyck_NSE_W (m : bitseq) :=
  foldr (fun b l => (if b then W :: l else N :: SE :: l)) [::] m.

Lemma dyck_NSE_W_cons b m :
 dyck_NSE_W (b :: m) = if b then W :: dyck_NSE_W m
                        else N :: SE :: dyck_NSE_W m.
Proof. by []. Qed.

(* Lemma dyck_NSE_W1_cons b m : *)
(*  dyck_NSE_W1 (b :: m) = if b then W :: dyck_NSE_W1 m *)
(*                         else N :: SE :: dyck_NSE_W1 m. *)
(* Proof. by case: b. Qed. *)

(* Lemma dyck_NSE_W12 : dyck_NSE_W1 =1 dyck_NSE_W. *)
(* Proof. by elim=> [| b m ihm] //=; rewrite -ihm dyck_NSE_W1_cons. Qed. *)

Lemma countSE_dyck_N_SE m : count_SE (dyck_N_SE m) = count_mem true m.
Proof.
rewrite /count_SE /count_N /dyck_N_SE !count_map.
suff /eq_count -> :
  (preim (fun b : bool => if b then SE else N) is_SE) =1 pred1 true by [].
by case.
Qed.

Lemma countN_dyck_N_SE m : count_N (dyck_N_SE m) = count_mem false m.
Proof.
rewrite /count_SE /count_N /dyck_N_SE !count_map.
suff /eq_count -> :
  (preim (fun b : bool => if b then SE else N) is_N) =1 pred1 false by [].
by case.
Qed.

Lemma dyck_N_SE_count_le m n : dyck m ->
  (count_SE (dyck_N_SE (take n m)) <= count_N (dyck_N_SE (take n m)))%N.
Proof. by case/dyckP=> cm _; rewrite countN_dyck_N_SE countSE_dyck_N_SE. Qed.

Lemma dyck_N_SE_count m : dyck m ->
  (count_SE (dyck_N_SE m) = count_N (dyck_N_SE m))%N.
Proof. by case/dyckP=> _ cm; rewrite countN_dyck_N_SE countSE_dyck_N_SE. Qed.

Lemma countW_dyck_NSE_W m : count_W (dyck_NSE_W m) = count_mem true m.
Proof.
by elim: m => [|b m ihm] //=; rewrite -ihm; case: b; rewrite ?addSn add0n.
Qed.

Lemma countN_dyck_NSE_W m : count_N (dyck_NSE_W m) = count_mem false m.
Proof.
by elim: m => [|b m ihm] //=; rewrite -ihm; case: b; rewrite ?addSn add0n.
Qed.

Lemma countSE_dyck_NSE_W m : count_SE (dyck_NSE_W m) = count_mem false m.
Proof.
by elim: m => [|b m ihm] //=; rewrite -ihm; case: b; rewrite ?addSn add0n.
Qed.

Lemma dyck_NSE_W_count_le m n : dyck m ->
  (count_W (dyck_NSE_W (take n m)) <=
   count_SE (dyck_NSE_W (take n m)) <= count_N (dyck_NSE_W (take n m)))%N.
Proof.
case/dyckP=> cm _.
by rewrite countW_dyck_NSE_W countN_dyck_NSE_W countSE_dyck_NSE_W cm /=.
Qed.

Lemma dyck_NSE_W_count m : dyck m ->
  count_N (dyck_NSE_W m) = count_SE (dyck_NSE_W m) /\
  count_SE (dyck_NSE_W m) = count_W (dyck_NSE_W m).
Proof.
case/dyckP=> _ cm.
by rewrite countW_dyck_NSE_W countN_dyck_NSE_W countSE_dyck_NSE_W cm.
Qed.

Section Target.

Variable n : nat.

(* Common target of bijections with Aseqs and Bseqs respectively *)
Record target : Type := Target {
  o_val : 'I_n;
  d_val : 'I_n;
  dom1_val : (3 * o_val + 2 * d_val).-tuple bool;
  dom2_val : n.-tuple bool;
  m1_val   : (2 * o_val)%N.-tuple bool;
  m2_val   : (2 * d_val)%N.-tuple bool;
  dom1_supportT : (count_mem true dom1_val = 3 * o_val)%N;
  dom2_supportT : (count_mem true dom2_val = 3 * o_val + 2 * d_val)%N;
  dyck_m1 : dyck m1_val;
  dyck_m2 : dyck m2_val;
  dom12P : all (pred1 false) (map (fun i => i.1 && i.2) (zip dom1_val dom2_val));
  od_valP : (3 * o_val + 3 * d_val = n)%N
}.

Section ElementaryThings.

Variable t : target.

Local Notation o := (o_val t).
Local Notation d := (d_val t).
Local Notation dom1 := (dom1_val t).
Local Notation dom2 := (dom2_val t).
Local Notation m1 := (m1_val t).
Local Notation m2 := (m2_val t).


Lemma dom1_supportF : (count_mem false dom1 = 2 * d)%N.
Proof.
apply/eqP; rewrite -(eqn_add2l (count_mem true dom1)); apply/eqP.
rewrite [in RHS]dom1_supportT /= -[RHS](size_tuple dom1).
rewrite -(count_predC (pred1 true)).
suff /eq_count -> : pred1 false =1 predC (pred1 true) by [].
by case.
Qed.

Lemma dom2_supportF : (count_mem false dom2 = d)%N.
Proof.
apply/eqP; rewrite -(eqn_add2l (count_mem true dom2)); apply/eqP.
rewrite [in RHS]dom2_supportT /= -addnA -mulSnr od_valP.
rewrite -[RHS](size_tuple dom2) -(count_predC (pred1 true)).
suff /eq_count -> : pred1 false =1 predC (pred1 true) by [].
by case.
Qed.


Definition target2B :=
  shuffle N dom2 (shuffle N dom1 (dyck_NSE_W m1) (dyck_N_SE m2)) (nseq d N).

Definition target2A :=
  shuffle N dom2 (shuffle N dom1 (dyck_NSE_W m1) (dyck_N_SE m2)) (nseq d W).

Lemma target2BP : Bseq target2B.
Proof.
apply/BseqP; split; last first.
  rewrite /count_SE count_shuffle_exact; last 2 first.
  - by rewrite size_shuffle size_tuple dom2_supportT.
  - by rewrite size_nseq dom2_supportF.
  rewrite count_shuffle_exact; last 2 first.
  - admit. (* prove size (dyck_NSE_W m1) *)
  - by rewrite size_map size_tuple dom1_supportF.
  have -> :  count is_SE (nseq d N) = 0%N. admit.
  (*changle count_W for count_mem *)
  rewrite /count_W count_shuffle_exact; last 2 first.
  - by rewrite size_shuffle size_tuple dom2_supportT.
  - by rewrite size_nseq dom2_supportF.
  rewrite count_shuffle_exact; last 2 first.
  - admit.  (* prove size (dyck_NSE_W m1) *)
  - by rewrite size_map size_tuple dom1_supportF.
  rewrite /count_N count_shuffle_exact; last 2 first.
  - by rewrite size_shuffle size_tuple dom2_supportT.
  - by rewrite size_nseq dom2_supportF.
  rewrite count_shuffle_exact; last 2 first.
  - admit.  (* prove size (dyck_NSE_W m1) *)
  - by rewrite size_map size_tuple dom1_supportF.
  rewrite addn0; case: (dyck_NSE_W_count (dyck_m1 t)).
  move: (dyck_N_SE_count (dyck_m2 t)).
  rewrite /count_SE /count_N /count_W => -> -> ->.
  rewrite -/count_SE -/count_N -/count_W.
  have -> : count_W (dyck_N_SE m2) = 0%N. admit.
  have -> : count_W (nseq d N) = 0%N. admit.
  rewrite !addn0 !PoszD -!addrA; do 2! congr (_ + _).
  rewrite countW_dyck_NSE_W countN_dyck_N_SE.
  admit.
move=> k; apply/andP; split.
rewrite /count_W. apply: count_take_shuffle_exact; last 1 first.
- admit. (* trivial *)
- by rewrite size_shuffle dom2_supportT size_tuple.
- by rewrite size_nseq dom2_supportF.
move=> {k} k; apply: count_take_shuffle_exact.
- admit. (* prove size (dyck_NSE_W m1) *)
- by rewrite size_map dom1_supportF size_tuple.
- move=> {k} k; case/andP: (dyck_NSE_W_count_le k (dyck_m1 t)).
  rewrite -/count_SE -/count_N -/count_W.
 admit. (* take commutes withe the interpretations *)
- move=> {k} k.
  have := (dyck_N_SE_count_le k (dyck_m2 t)).
 admit. (* take commutes withe the interpretations *)
apply: count_take_shuffle_exact.
Admitted.


End ElementaryThings.

Definition target2B t :=
  let: Target o d dom1 dom2 m1 m2 _ _ _ _ _ _ := t in
  shuffle N dom2 (shuffle N dom1 (dyck_NSE_W m1) (dyck_N_SE m2)) (nseq d N).

Definition target2A t :=
  let: Target o d dom1 dom2 m1 m2 _ _ _ _ _ _ := t in
  shuffle N dom2 (shuffle N dom1 (dyck_NSE_W m1) (dyck_N_SE m2)) (nseq d W).

Lemma target2BP t : Bseq (target2B t).
Proof.
case: t => o d dom1 dom2 m1 m2 supd1 supd2 dyckm1 dyckm2 dom12 eod /=.
apply/BseqP; split; last first.
  rewrite /count_SE count_shuffle_exact; last first.
  rewrite size_nseq dom2_supportF.
Admitted.

End Target.






*)




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

(* Rmk : I would like n to be implicit in definitions Aseq and Bseq, but
   I do not manage to overrid the flag set by my global options, even
   with the Argument command. Is it possible? *)
