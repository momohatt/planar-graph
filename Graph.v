Require Import Coq.Reals.Reals.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.omega.Omega.
Require Export LibTactics.

Inductive point : Type := Point (x y : R).

Definition region : Type := point -> Prop.

Definition map : Type := point -> region.

Inductive interval : Type := Interval (x y : R).

Inductive rectangle : Type := Rectangle (hspan vspan : interval).

Definition in_interval (s : interval) : R -> Prop :=
  fun t => let ' Interval x y := s in (x < t)%R /\ (t < y)%R.

Definition in_rectangle rr : region :=
  fun z => let ' Rectangle hspan vspan := rr in let ' Point x y := z in
  in_interval hspan x /\ in_interval vspan y.

(* Elementary set theory for the plane. *)

Definition union (r1 r2 : region) : region := fun z => r1 z \/ r2 z.

Definition intersect (r1 r2 : region) : region := fun z => r1 z /\ r2 z.

Definition nonempty (r : region) : Prop := exists z : point, r z.

Definition subregion (r1 r2 : region) : Prop := forall z : point, r1 z -> r2 z.

Lemma intersect_symm (r1 r2 : region) (z : point) :
  intersect r1 r2 z <-> intersect r2 r1 z.
Proof. split; intros [? ?]; split; auto. Qed.

Lemma subregion_refl (r : region) :
  subregion r r.
Proof. red. auto. Qed.

Lemma subregion_trans (r1 r2 r3 : region) :
  subregion r1 r2 -> subregion r2 r3 -> subregion r1 r3.
Proof.
  unfold subregion. intros. auto. Qed.

Definition meet (r1 r2 : region) : Prop := nonempty (intersect r1 r2).

Lemma meet_symm (r1 r2 : region) :
  meet r1 r2 -> meet r2 r1.
Proof. intros [? [? ?]]. exists x; split; auto. Qed.

Lemma meet_subregion (u1 u2 r : region) :
  meet u1 r -> subregion u1 u2 -> meet u2 r.
Proof.
  unfold meet, nonempty, intersect. intros [? [? ?]] ?.
  exists x. split; auto.
Qed.

Hint Resolve subregion_refl subregion_trans meet_subregion.

(* Maps are represented as relations; proper map are partial equivalence  *)
(* relations (PERs).                                                      *)

Record plain_map (m : map) : Prop := PlainMap {
  map_symm z1 z2 : m z1 z2 -> m z2 z1;
  map_trans z1 z2 z3 : m z1 z2 -> m z2 z3 -> m z1 z3
}.

(*
Axiom plain_map_unique_point :
  forall (m : map) (z1 z2 : point), plain_map m -> m z1 z2 -> z1 = z2.
*)

Lemma map_symm_trans_ll (m : map) (z1 z2 z3 : point) :
  plain_map m -> m z1 z2 -> m z1 z3 -> m z2 z3.
Proof. intros. apply map_trans with z1; auto. apply map_symm; auto. Qed.

Lemma map_symm_trans_rr (m : map) (z1 z2 z3 : point) :
  plain_map m -> m z1 z2 -> m z3 z2 -> m z1 z3.
Proof. intros. apply map_trans with z2; auto. apply map_symm; auto. Qed.

Lemma map_covered_left (m : map) (z1 z2 : point) :
  plain_map m -> m z1 z2 -> m z1 z1.
Proof.
  intros. assert (m z2 z1) by (apply map_symm; auto).
  apply map_trans with z2; auto. Qed.

Lemma map_covered_right (m : map) (z1 z2 : point) :
  plain_map m -> m z1 z2 -> m z2 z2.
Proof.
  intros. assert (m z2 z1) by (apply map_symm; auto).
  apply map_trans with z1; auto. Qed.

(* sum of all the regions in map (set of all the points defined on map) *)
Definition cover (m : map) : region := fun z => m z z.

Definition submap (m1 m2 : map) : Prop := forall z, subregion (m1 z) (m2 z).

Lemma submap_refl (m : map) :
  submap m m.
Proof. unfold submap. auto. Qed.

Lemma submap_trans (m1 m2 m3 : map) :
  submap m1 m2 -> submap m2 m3 -> submap m1 m3.
Proof.
  unfold submap. intros.
  eapply subregion_trans; auto.
Qed.

(* There are at most n regions in m. *)
Definition at_most_regions (n : nat) (m : map) :=
  exists f, forall z, cover m z -> exists2 i : nat, Peano.lt i n & m (f i) z.

(* Elementary topology. *)

Definition open (r : region) : Prop :=
  forall z, r z -> exists2 u, in_rectangle u z & subregion (in_rectangle u) r.

Definition closure (r : region) : region :=
  fun z => forall u, open u -> u z -> meet r u.

Lemma closure_preserves_subregion (r1 r2 : region) :
  subregion r1 r2 -> subregion (closure r1) (closure r2).
Proof with auto.
  unfold subregion, closure. intros. destruct (H0 u) as [x [? ?]]...
  exists x. split...
Qed.

Definition connected (r : region) : Prop :=
  forall u v, open u -> open v -> subregion r (union u v) ->
  meet u r -> meet v r -> meet u v.

Record simple_map (m : map) : Prop := SimpleMap {
  simple_map_plain : plain_map m;
  simple_map_open z : open (m z);
  simple_map_connected z : connected (m z)
}.

Record finite_simple_map (m : map) : Prop := FiniteSimpleMap {
  finite_simple_map_simple : simple_map m;
  finite_simple_map_finite : exists n, at_most_regions n m
}.

Hint Resolve simple_map_plain.

Lemma closure_map (m : map) (z z' : point) :
  simple_map m -> closure (m z) z' -> m z z' \/ ~ m z' z'.
Proof.
  intros. repeat red in H0. destruct H.
  assert (m z' z' -> exists z0 : point, intersect (m z) (m z') z0) by auto.
  apply imply_to_or in H.
  destruct H; auto.
  left. inversion H; inversion H1.
  apply map_trans with x; auto.
  apply map_symm; auto.
Qed.

Lemma closure_map_trans (m : map) (z1 z2 z : point) :
  plain_map m -> m z1 z2 -> closure (m z1) z -> closure (m z2) z.
Proof with auto.
  unfold closure, meet. intros.
  assert (nonempty (intersect (m z1) u)) by auto.
  destruct H4. destruct H4. exists x. split; auto.
  apply map_trans with z1... apply map_symm...
Qed.

(* Borders, corners, adjacency and coloring. *)

Definition border (m : map) (z1 z2 : point) : region :=
  intersect (closure (m z1)) (closure (m z2)).

Definition corner_map (m : map) (z : point) : map :=
  fun z1 z2 => open (m z1) /\ m z1 z2 /\ closure (m z1) z.

(* a point is not a corner of a map iff it doesn't belong to the closure of
*  more than 2 regions. *)
Definition not_corner (m : map) : region :=
  fun z => at_most_regions 2 (corner_map m z).

Lemma not_corner_correct (m : map) (z1 z2 z3 z : point) :
  simple_map m -> not_corner m z ->
  m z1 z1 /\ closure (m z1) z ->
  m z2 z2 /\ closure (m z2) z ->
  m z3 z3 /\ closure (m z3) z ->
  m z1 z2 \/ m z2 z3 \/ m z3 z1.
Proof with auto.
  intros. repeat red in H0. destruct H0 as [f ?].
  assert (open (m z1) /\ m z1 z1 /\ closure (m z1) z) by (split; auto; apply simple_map_open; auto).
  assert (open (m z2) /\ m z2 z2 /\ closure (m z2) z) by (split; auto; apply simple_map_open; auto).
  assert (open (m z3) /\ m z3 z3 /\ closure (m z3) z) by (split; auto; apply simple_map_open; auto).
  clear H1 H2 H3; rename H4 into H1; rename H5 into H2; rename H6 into H3.
  apply (H0 z1) in H1. destruct H1 as [i ?]. destruct H4 as [? [? ?]].
  apply (H0 z2) in H2. destruct H2 as [j ?]. destruct H7 as [? [? ?]].
  apply (H0 z3) in H3. destruct H3 as [k ?]. destruct H10 as [? [? ?]].
  assert (i = 0 \/ i = 1) by omega.
  assert (j = 0 \/ j = 1) by omega.
  assert (k = 0 \/ k = 1) by omega.
  clear H1 H2 H3.
  destruct H13; subst.
  - destruct H14; subst.
    + left. apply map_trans with (f 0)... apply map_symm...
    + right. destruct H15; subst.
      { right. apply map_symm_trans_ll with (f 0)... }
      { left. apply map_symm_trans_ll with (f 1)... }
  - destruct H14; subst.
    + right. destruct H15; subst.
      { left. apply map_symm_trans_ll with (f 0)... }
      { right. apply map_symm_trans_ll with (f 1)... }
    + left. apply map_symm_trans_ll with (f 1)...
Qed.

Definition adjacent (m : map) (z1 z2 : point) : Prop :=
  m z1 z1 /\ m z2 z2 /\ ~ m z1 z2 /\ meet (not_corner m) (border m z1 z2).

Definition inter_region (m : map) (z1 z2 : point) : region :=
  fun z => ~ m z1 z2 /\ intersect (not_corner m) (border m z1 z2) z.

Lemma border_symm (m : map) (z1 z2 z : point) :
  border m z1 z2 z <-> border m z2 z1 z.
Proof. split; unfold border; apply intersect_symm. Qed.

Lemma inter_region_symm (m : map) (z1 z2 z : point) :
  simple_map m ->
  inter_region m z1 z2 z <-> inter_region m z2 z1 z.
Proof with auto.
  split; unfold inter_region; intros [? [? ?]]; split.
  - intros F; apply H0; apply map_symm...
  - split... apply border_symm...
  - intros F; apply H0; apply map_symm...
  - split... apply border_symm...
Qed.

Hint Resolve border_symm inter_region_symm.

Lemma border_not_covered (m : map) (z1 z2 z : point) :
  simple_map m -> ~ m z1 z2 -> border m z1 z2 z -> ~ m z z.
Proof with auto.
  intros ? ? [? ?] ?.
  apply H0. apply map_trans with z.
  - inversion H...
  - destruct (closure_map _ _ _ H H1)...
    apply H4 in H3. inversion H3.
  - destruct (closure_map _ _ _ H H2).
    + apply map_symm...
    + apply H4 in H3. inversion H3.
Qed.

Lemma inter_region_deterministic (m : map) (z z1 z2 z3 z4 : point) :
  simple_map m ->
  m z1 z1 -> m z2 z2 -> m z3 z3 -> m z4 z4 ->
  inter_region m z1 z2 z -> inter_region m z3 z4 z ->
  (m z1 z3 /\ m z2 z4) \/ (m z1 z4 /\ m z2 z3).
Proof with auto.
  unfold inter_region. intros ? ? ? ? ? [? [? [? ?]]] [? [_ [? ?]]].
  assert (m z1 z2 \/ m z2 z3 \/ m z3 z1) by (apply not_corner_correct with z; auto).
  destruct H11.
  - contradiction.
  - destruct H11.
    + right; split...
      assert (m z1 z3 \/ m z3 z4 \/ m z4 z1) by (apply not_corner_correct with z; auto).
      destruct H12.
      { exfalso. apply H4; apply map_symm_trans_rr with z3... }
      { destruct H12. contradiction. apply map_symm... }
    + left. split; apply map_symm...
      assert (m z2 z3 \/ m z3 z4 \/ m z4 z2) by (apply not_corner_correct with z; auto).
      destruct H12.
      { exfalso. apply H4; apply map_trans with z3; auto; apply map_symm... }
      { destruct H12. contradiction. auto. }
Qed.

Definition outerface (m : map) (z1 : point) : Prop :=
  exists2 z2 : point, adjacent m z1 z2 & ~ (cover m z2).

Record outerplane_map (m : map) : Prop := OuterplaneMap {
  outerplane_map_finsimple : finite_simple_map m;
  outerplane_map_outer z : outerface m z
}.
