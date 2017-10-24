From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice tuple fintype finfun finset.
From mathcomp Require Import bigop ssralg ssrnum poly ssrint.

Require Import words.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(* Characterization via trajectories.*)

(* A two-dimentional grid, as (a  warper around) pairs of  integers *)

Import GRing.Theory Num.Theory.
Open Scope ring_scope.

Inductive gridpoint := Gridpoint of int * int.

(* Boilerplate code to install the structures of equality, countable, choice
   type on type step, plus a coercion from grid to paris of integers. *)

Coercion int_pair_of_gridpoint (p : gridpoint) := let: Gridpoint xy := p in xy.

Canonical gridpoint_subType := Eval hnf in [newType for int_pair_of_gridpoint].

Definition gridpoint_eqMixin := [eqMixin of gridpoint by <:].
Canonical  gridpoint_eqType  := EqType gridpoint gridpoint_eqMixin.

Definition gridpoint_choiceMixin := [choiceMixin of gridpoint by <:].
Canonical  gridpoint_choiceType  := ChoiceType gridpoint gridpoint_choiceMixin.

Definition gridpoint_countMixin   := [countMixin of gridpoint by <:].
Canonical  gridpoint_countType    := CountType gridpoint gridpoint_countMixin.
Canonical  gridpoint_subCountType := Eval hnf in [subCountType of gridpoint].
(* End boilerplate code *)

(* Origin of the gridpoint *)
Definition origin := Gridpoint (0, 0).

(* Abscissia and ordinate of a point of the gridpoint *)
Definition abs  := (fun g : gridpoint => g.1).
Definition ord  := (fun g : gridpoint => g.2).

Lemma gridpoint_eq g1 g2 : (g1 == g2) = (abs g1 == abs g2) && (ord g1 == ord g2).
Proof. by []. Qed.

(* Several predicates describing zones of interest in the grid *)
Definition diag (g : gridpoint) : bool := abs g == ord g.

(* North (closed) half plane *)
Definition nhalf (g : gridpoint) : bool := 0 <= ord g.

(* South (closed) half plane *)
Definition shalf (g : gridpoint) : bool := ord g <= 0.

(* East (closed) half plane *)
Definition ehalf (g : gridpoint) : bool := 0 <= abs g.

(* West (closed) half plane *)
Definition whalf (g : gridpoint) : bool := abs g <= 0.

(* Quadrant I *)
Definition Iquadrant := predI nhalf ehalf.

Arguments Iquadrant : simpl never.

(* (* Quadrant II *) *)
(* Definition IIquadrant : bool := predI nhalf whalf. *)

(* (* Quadrant III *) *)
(* Definition IIIquadrant : bool := predI shalf whalf. *)

(* (* Quadrant IV *) *)
(* Definition IVquadrant : bool := predI shalf ehalf. *)


(* We interpret each step as a function : gridpoint -> gridpoint,
   with the following semantic:
   - North means increasing ordinate of 1, leaving abscissia unchanged
   - West means decreasing abscissia of 1, leaving ordinate unchanged
   - SouthEast (coded by 2) means decreading both ordinate and abscissia. *)


Definition move_of_letter (g : gridpoint) (s : letter) : gridpoint :=
  let: Gridpoint (g1, g2) := g in
  match s with
    |N  => Gridpoint (g1, g2 + 1)
    |W  => Gridpoint (g1 - 1, g2)
    |Se => Gridpoint (g1 + 1, g2 - 1)
  end.

Arguments move_of_letter : simpl never.

Lemma move_of_N g : move_of_letter g N = Gridpoint (abs g, ord g + 1).
Proof. by case: g; case=> g1 g2. Qed.

Lemma move_of_W g : move_of_letter g W = Gridpoint (abs g - 1, ord g).
Proof.  by case: g; case=> g1 g2. Qed.

Lemma move_of_Se g : move_of_letter g Se = Gridpoint (abs g + 1, ord g - 1).
Proof.  by case: g; case=> g1 g2. Qed.

Lemma abs_move_N g : abs (move_of_letter g N) = abs g.
Proof. by rewrite move_of_N. Qed.

Lemma abs_move_W g : abs (move_of_letter g W) = abs g - 1.
Proof. by rewrite move_of_W. Qed.

Lemma abs_move_Se g : abs (move_of_letter g Se) = abs g + 1.
Proof. by rewrite move_of_Se. Qed.

Lemma ord_move_of_N g : ord (move_of_letter g N) = ord g + 1.
Proof. by rewrite move_of_N. Qed.

Lemma ord_move_of_W g : ord (move_of_letter g W) = ord g.
Proof. by rewrite move_of_W. Qed.

Lemma ord_move_of_Se g : ord (move_of_letter g Se) = ord g - 1.
Proof. by rewrite move_of_Se. Qed.


(* We call (trajectory g w) the sequence of positions prescribed by a sequence of
   letters w , from a starting point g of the grid. If the list of letters is
   of the form s :: w, the move coded by s is executed first. The grid point
   (final_pos g w) is the final position on the grid reached at the end of the
   trajectory.*)

Definition final_pos := foldl move_of_letter.

Lemma final_pos_nil g : final_pos g [::] = g. Proof. by []. Qed.

Lemma final_pos_cons g s w :
  final_pos g (s :: w) = final_pos (move_of_letter g s) w.
Proof. by []. Qed.

Lemma final_pos_cat g w1 w2 :
  final_pos g (w1 ++ w2) = final_pos (final_pos g w1) w2.
Proof. by rewrite /final_pos foldl_cat. Qed.

Lemma abs_final g w :
  abs (final_pos g w) = abs g + (#Se w)%:Z - (#W w)%:Z.
Proof.
elim: w g => [| s w ihw] /= g; first by rewrite addrK.
rewrite ihw; case: s => /=; rewrite !add0n ?add1n; first by rewrite abs_move_N.
- by rewrite abs_move_W intS opprD addrACA addrA.
- by rewrite abs_move_Se intS addrA.
Qed.

Lemma ord_final g w :
  ord (final_pos g w) = ord g + (#N w)%:Z - (#Se w)%:Z.
Proof.
elim: w g => [| s w ihw] /= g; first by rewrite addrK.
rewrite ihw; case: s => /=; rewrite !add0n ?add1n ?intS.
- by rewrite ord_move_of_N addrA.
- by rewrite ord_move_of_W.
- by rewrite ord_move_of_Se opprD addrACA addrA.
Qed.

Definition trajectory := scanl move_of_letter.

Lemma trajectory_nil g : trajectory g [::] = [::]. by []. Qed.

Lemma trajectory_cons g s w :
  trajectory g (s :: w) =
  (move_of_letter g s) :: trajectory (move_of_letter g s) w.
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
  abs g2 + (#Se (take n.+1 w))%:Z - (#W (take n.+1 w))%:Z.
Proof. by move=> ?; rewrite nth_trajectory // abs_final. Qed.

Lemma ord_nth_trajectory g1 g2 w n : (n < size w)%N ->
  ord (nth g1 (trajectory g2 w) n) =
  ord g2 + (#N (take n.+1 w))%:Z - (#Se (take n.+1 w))%:Z.
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

Definition to_diag_traj (g : gridpoint) (w : seq letter) : bool :=
  diag (final_pos g w).

(* Not sure this is the usefull form... *)
Lemma to_diag_trajP g w :
 reflect (abs g + (#Se w)%:Z -  (#W w)%:Z =
          ord g + (#N w)%:Z - (#Se w)%:Z)
         (to_diag_traj g w).
Proof. by apply: (iffP eqP); rewrite /to_diag_traj abs_final ord_final. Qed.

Lemma oto_diag_trajP w :
 reflect ((#Se w)%:Z - (#W w)%:Z = (#N w)%:Z - (#Se w)%:Z)
         (to_diag_traj origin w).
Proof.
rewrite -[LHS]add0r -[RHS]add0r !addrA; exact: (to_diag_trajP origin).
Qed.

Definition loop_traj (g : gridpoint) (w : seq letter) : bool :=
  final_pos g w == g.

Lemma loop_trajP (g : gridpoint) (w : seq letter) :
  reflect (#N w = #Se w /\ #Se w = #W w) (loop_traj g w).
Proof.
rewrite /loop_traj gridpoint_eq.
apply: (iffP andP); rewrite ord_final abs_final; case; last first.
  by move=> -> ->; rewrite !addrK.
  rewrite -!addrA ![_ + (_ - _) == _](can2_eq (addKr _) (addNKr _)) !addNr.
by rewrite  !subr_eq0; move=> /eqP [] <- /eqP [] ->.
Qed.


(* Properties of trajectories that start and stay in the north half plane *)
Definition nhalf_traj (g : gridpoint) (w : seq letter) : bool :=
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
  then the number of Se in w is smaller than the number of N *)
Lemma nhalf_otraj_le w : nhalf_traj origin w ->
  (#Se w <= #N w)%N.
Proof.
move/allP/(_ _ (trajectory_final _ _)); rewrite /nhalf ord_final add0r subr_ge0.
done.
Qed.

(* If  the trajectory along w from the origin stays in the north half-plane,
  then for every of its prefixes w' the number of Se in w' is smaller than
  the number of N *)


Lemma nhalf_otraj_pre w1 w2 : nhalf_traj origin (w1 ++ w2) ->
  (#Se w1 <= #N w1)%N.
Proof. by rewrite nhalf_traj_cat; case/andP=> /nhalf_otraj_le. Qed.

(* This is in fact characterizing trajectories from the origin that stay in
   the north plane *)
Lemma nhalf_otrajP w :
  reflect (forall n, #Se (take n w) <= #N (take n w))%N
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

Definition ehalf_traj (g : gridpoint) (w : seq letter) : bool :=
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
  then the number of W in w is smaller than the number of Se *)
Lemma ehalf_otraj_le w : ehalf_traj origin w -> (#W w <= #Se w)%N.
Proof.
move/allP/(_ _ (trajectory_final _ _)); rewrite /ehalf abs_final add0r subr_ge0.
done.
Qed.

(* If  the trajectory along w from the origin stays in the north half-plane,
  then for every of its prefixes w' the number of W in w' is smaller than
  the number of Se *)

Lemma ehalf_otraj_pre w1 w2 : ehalf_traj origin (w1 ++ w2) ->
  (#W w1 <= #Se w1)%N.
Proof. by rewrite ehalf_traj_cat; case/andP=> /ehalf_otraj_le. Qed.

(* This is in fact characterizing trajectories from the origin that stay in
   the east plane *)
Lemma ehalf_otrajP w :
  reflect (forall n, #W (take n w) <= #Se (take n w))%N
          (ehalf_traj origin w).
Proof.
apply: (iffP idP) => [ntw n| countle].
  by move: ntw; rewrite -{1}[w](cat_take_drop n); move/ehalf_otraj_pre.
rewrite ehalf_trajE /=; apply/(all_nthP origin) => i ltisw.
rewrite /ehalf abs_nth_trajectory -?(size_trajectory origin) // subr_ge0.
exact: countle.
Qed.

Definition Iquadrant_traj (g : gridpoint) (w : seq letter) : bool :=
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
  (#W w <= #Se w <= #N w)%N.
Proof.
move=> itow; rewrite ehalf_otraj_le; last exact: Iquadrant_ehalf_traj.
rewrite nhalf_otraj_le //; exact: Iquadrant_nhalf_traj.
Qed.

Lemma Iquadrant_otraj_pre w1 w2 : Iquadrant_traj origin (w1 ++ w2) ->
  (#W w1 <= #Se w1 <= #N w1)%N.
Proof.
by rewrite Iquadrant_traj_cat; case/andP=> itow1 _; apply: Iquadrant_otraj_le.
Qed.

Lemma Iquadrant_otrajP w :
  reflect (forall n, #W (take n w) <= #Se (take n w)
                                       <= #N (take n w))%N
          (Iquadrant_traj origin w).
Proof.
apply: (iffP idP) => [ntw n| countle].
  move/Iquadrant_nhalf_traj: (ntw) => /nhalf_otrajP ->.
  by move/Iquadrant_ehalf_traj: (ntw) => /ehalf_otrajP ->.
rewrite Iquadrant_nehalf_traj.
have /nhalf_otrajP -> :
  forall n, (#Se (take n w))%:Z <= (#N (take n w))%:Z.
  by move=> n; case/andP: (countle n).
by apply/ehalf_otrajP=> n; case/andP: (countle n).
Qed.


(* A sequence is an Asequence if its associated trajectory from the origin stays
   in the upper (north) half-plane and ends at the origin: *)

Definition Aseq (w : seq letter) := nhalf_traj origin w && loop_traj origin w.

Lemma Aseq_nhalf w : w \in Aseq -> nhalf_traj origin w.
Proof. by case/andP. Qed.

Lemma Aseq_oloop w : w \in Aseq -> loop_traj origin w.
Proof. by case/andP. Qed.

(* An Aseq necessarily has an equal number of N, W and Se *)
Lemma Aseq_count_NW : {in Aseq, #N =1 #W}.
Proof. by move=> w /Aseq_oloop /loop_trajP; case=> ->. Qed.

Lemma Aseq_count_SeW : {in Aseq, #Se =1 #W}.
Proof. by move=> w /Aseq_oloop /loop_trajP; case=> _ ->. Qed.

Lemma Aseq_count_NSe : {in Aseq, #N =1 #Se}.
Proof. by move=> w Aw; rewrite /= Aseq_count_NW // Aseq_count_SeW. Qed.

(* Any prefix of an Aseq has more N than Se: *)
Lemma Aseq_pre w1 w2 : w1 ++ w2 \in Aseq ->
  (#Se w1)%:Z <= (#N w1)%:Z.
Proof. by move/Aseq_nhalf/nhalf_otraj_pre. Qed.

Lemma AseqP w : reflect
                [/\ forall n, (#Se (take n w))%:Z <= (#N (take n w))%:Z,
                    #N w = #Se w & #Se w = #W w]
                (Aseq w).
Proof.
apply: (iffP idP).
  by rewrite /Aseq; case/andP => /nhalf_otrajP=> ? /loop_trajP; case.
by rewrite /Aseq; case=> /nhalf_otrajP => -> /= he1 he2; apply/loop_trajP.
Qed.

(* A sequence is a B-sequence if its trajectory from the origin stays in
   quadrant I and ends somewhere on the diagonal: *)
Definition Bseq (w : seq letter) :=
  Iquadrant_traj origin w && to_diag_traj origin w.

Lemma Bseq_Iquadrant w : w \in Bseq -> Iquadrant_traj origin w.
Proof. by case/andP. Qed.

Lemma Bseq_oto_diag w : w \in Bseq -> to_diag_traj origin w.
Proof. by case/andP. Qed.

(* A Bseq necessarily has less W than Se than N *)
Lemma Bseq_count_le w : w \in Bseq ->
   (#W w)%:Z <= (#Se w)%:Z <= (#N w)%:Z.
Proof. by move/Bseq_Iquadrant/Iquadrant_otraj_le. Qed.

Lemma Bseq_pre w1 w2 : w1 ++ w2 \in Bseq ->
   (#W w1)%:Z <= (#Se w1)%:Z <= (#N w1)%:Z.
Proof. by move/Bseq_Iquadrant/Iquadrant_otraj_pre. Qed.

(* Again we inherit from the tentative statement of
   to_diagP, probably not in its most convenient form. *)
Lemma Bseq_count w : w \in Bseq ->
  (#Se w)%:Z - (#W w)%:Z = (#N w)%:Z - (#Se w)%:Z.
Proof. by move/Bseq_oto_diag/oto_diag_trajP. Qed.

Lemma BseqP w : reflect
                  ((forall n, (#W (take n w))%:Z <= (#Se (take n w))%:Z
                                                      <= (#N (take n w))%:Z)
                  /\
                    (#Se w)%:Z - (#W w)%:Z =
                    (#N w)%:Z - (#Se w)%:Z)
                  (Bseq w).
Proof.
apply: (iffP idP).
  by rewrite /Bseq; case/andP => /Iquadrant_otrajP=> ? /oto_diag_trajP.
by case=> /Iquadrant_otrajP iw /oto_diag_trajP odw; rewrite /Bseq iw.
Qed.

(* A state monad for datas of type A equipped with two counters *)

(* Now we have all the necessary vocabulary to describe the families of walks
   the exercise is about *)


(* A (walk n) is (a wrapper around) a sequence of size n  *)

Inductive walk (n : nat) := Walk of n.-tuple letter.


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

(* Rmk : I would like n to be explicit in definitions Aseq and Bseq, but
   I do not manage to overrid the flag set by my global options, even
   with the Argument command. Is it possible? *)
