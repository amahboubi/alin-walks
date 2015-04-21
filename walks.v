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

Record store (A : Type) : Type := Store {res : A; c : cmpt2}.

Definition mkStore {A} a n1 n2 : store A := Store a (n1, n2).

Definition state (A : Type) :=  cmpt2 -> store A.

Definition sreturn {A} (a : A) : state A := fun c => Store a c.

Definition sbind {A B} (sa : state A) (f : A -> state B) : state B :=
  fun x => let: Store a c := sa x in f a c.

Lemma sbind_return {A B} (x : A) (f : A -> state B) : sbind (sreturn x) f = f x.
Proof. by []. Qed.

Lemma sreturn_bind {A} (x : state A) : sbind x sreturn =1 x.
Proof. by move=> c; rewrite /sbind; case: (x c). Qed.

Lemma sbind_comp {A B C} (f : A -> state B) (g : B -> state C) (x : state A) :
    sbind (sbind x f) g =1 sbind x (fun x => (sbind (f x) g)).
Proof. by move=> c; rewrite /sbind; case: (x c). Qed.


(* A convenient notation for programming in monadic style, borrowed to Cyril :) *)

Notation "'sdo' x <- y ; z" :=
  (sbind y (fun x => z)) (at level 99, x at level 0, y at level 0,
    format "'[hv' 'sdo'  x  <-  y ;  '/' z ']'").

(* A monadic version of scanl, properties to be proved *)
Fixpoint sscanl {A B} (f : A -> state B) (wl : seq A) : state (seq B) :=
  if wl is sa :: l then
    sdo l1 <- sscanl f l;
    sdo s1 <- f sa;
    sreturn (s1 :: l1)
 else sreturn [::].


(* State transformation from game A to game B *)
Definition sA2B (s : step) : state step := fun c =>
  match s, c with
    |  W, (0, c2)      =>  mkStore N 0 c2
    |  W, (c1.+1, c2)  =>  mkStore SE c1 c2.+1
    |  N, (c1, c2)     =>  mkStore N c1.+1 c2
    |  SE, (c1, c2.+1) =>  mkStore W c1 c2
    |  SE, (c1.+1, 0)  =>  mkStore SE c1 0
    |  SE, (0, 0)      =>  mkStore N 0 0
  end.

Arguments sA2B s c : simpl never.

(* State transformation from game B to game A *)

Definition sB2A (s : step) : state step := fun c =>
  match s, c with
    | N, (0, c2)      => mkStore W 0 c2
    | SE, (c1, c2.+1) => mkStore W c1.+1 c2
    | N, (c1.+1, c2)  => mkStore N c1 c2
    | W, (c1, c2)     => mkStore SE c1 c2.+1
    | SE, (c1, 0)     => mkStore SE c1.+1 0
  end.

Arguments sB2A s c : simpl never.

Lemma readA2BK (s : step) (c : cmpt2) :
  [|| (c.1 != 0%N), (c.2 != 0%N) | (s != SE)] ->
  sbind (sB2A s) sA2B c = Store s c.
Proof. by case: s; case: c => [] [| n1] [|n2]. Qed.

(* Now we can implement both transformations *)
Definition readA2B (l : seq step) : state (seq step) := sscanl sA2B l.

Definition readB2A (l : seq step) : state (seq step) := sscanl sB2A l.


(* Definition counters_at_0 (s : store step) := (cnse s == 0%N) && (cnsew s == 0%N). *)

(* Definition Nstore (s : store step) := res s == N. *)

(* Definition SEstore (s : store step) := res s == SE. *)

(* Definition Wstore (s : store step) := res s == W. *)

(* Definition valid_Astart := predU (predC counters_at_0) (predC SEstore). *)

(* Lemma mem_validAstart s : *)
(*   s \in valid_Astart = [|| (cnse s != 0%N), (cnsew s != 0%N) | (res s != SE)]. *)
(* Proof. by rewrite inE /= /counters_at_0 negb_and !orbA. Qed. *)

(* Lemma sA2BK : {in valid_Astart, cancel (sA2B (sB2A s)}. *)
(* Proof. by case=> [[]] [|c1] [|c2]; rewrite mem_validAstart; case/or3P. Qed. *)


(* Definition stepA2B (s : state step) : state step := *)
(*   match s with *)
(*     | State W 0 c2      => State N 0 c2 *)
(*     | State W c1.+1 c2  => State SE c1 c2.+1 *)
(*     | State N c1 c2     => State N c1.+1 c2 *)
(*     | State SE c1 c2.+1 => State W c1 c2 *)
(*     | State SE c1.+1 0  => State SE c1 0 *)
(*     | State SE 0 0      => State N 0 0 *)
(*   end. *)

(* Arguments stepA2B s : simpl never. *)

(* Definition stepB2A (s : state step) : state step := *)
(*   match s with *)
(*     | State N 0 c2         => State W 0 c2 *)
(*     | State SE c1 c2.+1    => State W c1.+1 c2 *)
(*     | State N c1.+1 c2    => State N c1 c2 *)
(*     | State W c1 c2      => State SE c1 c2.+1 *)
(*     | State SE c1 0        => State SE c1.+1 0 *)
(*   end. *)

(* Arguments stepB2A s : simpl never. *)

(* Definition counters_at_0 (s : state step) := (cnse s == 0%N) && (cnsew s == 0%N). *)

(* Definition Nstate (s : state step) := res s == N. *)

(* Definition SEstate (s : state step) := res s == SE. *)

(* Definition Wstate (s : state step) := res s == W. *)

(* Definition valid_Astart := predU (predC counters_at_0) (predC SEstate). *)

(* Lemma mem_validAstart s : *)
(*   s \in valid_Astart = [|| (cnse s != 0%N), (cnsew s != 0%N) | (res s != SE)]. *)
(* Proof. by rewrite inE /= /counters_at_0 negb_and !orbA. Qed. *)

(* Lemma stepA2BK : {in valid_Astart, cancel stepA2B stepB2A}. *)
(* Proof. by case=> [[]] [|c1] [|c2]; rewrite mem_validAstart; case/or3P. Qed. *)














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
