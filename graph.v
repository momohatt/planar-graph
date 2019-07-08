Require Import Coq.Reals.Reals.
Require Import Coq.Logic.Classical_Prop.

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
  map_trans z1 z2 : m z1 z2 -> subregion (m z2) (m z1)
}.

Hint Resolve map_trans.

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

(*
(* edgeがregionとして存在する *)
Record edged_map (m : map) : Prop := EdgeMap {
  edged_map_plain : plain_map m;
  edged_map_connected z : connected (m z)
}.
*)

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

(* Borders, corners, adjacency and coloring. *)

Definition border (m : map) (z1 z2 : point) : region :=
  intersect (closure (m z1)) (closure (m z2)).

Definition corner_map (m : map) (z : point) : map :=
  fun z1 z2 => m z1 z2 /\ closure (m z1) z.

(* a point is not a corner of a map iff it doesn't belong to the closure of
*  more than 2 regions. *)
Definition not_corner (m : map) : region :=
  fun z => at_most_regions 2 (corner_map m z).

Definition adjacent (m : map) (z1 z2 : point) : Prop :=
  ~ m z1 z2 /\ meet (not_corner m) (border m z1 z2).

Lemma border_not_covered (m : map) (z1 z2 z :point) :
  simple_map m -> ~ m z1 z2 -> border m z1 z2 z -> ~ m z z.
Proof.
  intros ? ? [? ?] ?.
  apply H0. apply map_trans with z.
  - inversion H; auto.
  - destruct (closure_map _ _ _ H H1); auto.
    apply H4 in H3. inversion H3.
  - destruct (closure_map _ _ _ H H2).
    + apply map_symm; auto. apply simple_map_plain; auto.
    + apply H4 in H3. inversion H3.
Qed.

Definition outerface (m : map) (z1 : point) : Prop :=
  exists2 z2 : point, adjacent m z1 z2 & ~ (cover m z2).

Record outerplane_map (m : map) : Prop := OuterplaneMap {
  outerplane_map_finsimple : finite_simple_map m;
  outerplane_map_outer z : outerface m z
}.

Record coloring (m k : map) : Prop := Coloring {
  coloring_plain : plain_map k;
  coloring_cover : subregion (cover m) (cover k);
  coloring_consistent : submap m k;
  coloring_adjacent z1 z2 : adjacent m z1 z2 -> ~ k z1 z2
}.

(* TODO: add a restriction so that each region of m should be convex *)
Definition totalize (m : map) : map :=
  fun z z' =>
    (* もともとm上の点である *)
    m z z' \/
    (* z1, z2を含むregionの間にある点 *)
    (exists z1 z2 : point,
      closure (m z1) z /\ closure (m z2) z /\ ~ m z1 z2 /\
      intersect (border m z1 z2) (not_corner m) z').

Lemma totalize_symm (m : map) (z1 z2 : point) :
  simple_map m -> totalize m z1 z2 -> totalize m z2 z1.
Proof.
  unfold totalize. intros. destruct H0.
  - left. apply map_symm; auto.
  - destruct H0 as [z3 [z4 [? [? [? ?]]]]]. right.
  (* TODO *)
Admitted.

Lemma totalize_trans (m : map) (z1 z2 : point) :
  totalize m z1 z2 -> subregion (totalize m z2) (totalize m z1).
Proof.
  (* TODO *)
Admitted.

Lemma totalize_subregion (m : map) (z : point) :
  subregion (m z) (totalize m z).
Proof.
  red; intros; left; auto. Qed.

Lemma totalize_plain_map (m : map) :
  simple_map m -> plain_map (totalize m).
Proof.
  intros. inversion H. split; intros.
  - apply totalize_symm; auto.
  - apply totalize_trans; auto.
Qed.

Lemma plain_map_totalize (m : map) (z z' : point) :
  simple_map m -> m z z' -> totalize m z z'.
Proof.
  intros. red. auto.
Qed.

Lemma totalize_cover_subregion (m : map) :
  simple_map m -> subregion (cover m) (cover (totalize m)).
Proof.
  unfold subregion, cover. intros. apply plain_map_totalize; auto.
Qed.

Record tcoloring (m k : map) : Prop := TColoring {
  tcoloring_coloring : coloring (totalize m) k;
  tcoloring_adjacent z :
    forall z1 z2 : point,
    adjacent (totalize m) z z1 -> adjacent (totalize m) z z2 -> ~ k z1 z2
}.

Definition colorable_with (n : nat) (m : map) : Prop :=
  exists2 k, coloring m k & at_most_regions n k.

Definition tcolorable_with (n : nat) (m : map) : Prop :=
  exists2 k, tcoloring m k & at_most_regions n k.

Lemma tcoloring_is_coloring :
  forall m k : map, simple_map m -> tcoloring m k -> coloring m k.
Proof.
  intros.
  destruct H0.
  destruct tcoloring_coloring0.
  split; auto.
  - apply subregion_trans with (cover (totalize m)); auto.
    apply totalize_cover_subregion; auto.
  - apply submap_trans with (totalize m); auto.
    repeat red. auto.
  - (* any adjacent two faces in m are colored differently *)
    intros.
    destruct H0 as [? [? [? ?]]].
    assert (~ m x x) by apply (border_not_covered _ _ _ _ H H0 H2).
    apply tcoloring_adjacent0 with x.
    + (* adjacent (totalize m) x z1 *)
      red. split.
      { (* ~ totalize m x z1 *)
        unfold totalize. intros F. destruct F.
        - (* m x z1 を仮定する場合 *)
          apply H3. assert (m z1 x) by (apply map_symm; auto).
          apply map_trans with z1; auto.
        - (* z1が境界上にあることを仮定する場合 *)
          destruct H4 as [z3 [z4 [? [? [? [? ?]]]]]].
          apply border_not_covered in H7; auto.
          apply H7.
          admit. }
      { (* meet (not_corner (totalize m)) (border (totalize m) x z1) *)
        admit. }
    + red. split.
Admitted.

Lemma coloring_leq_tcoloring :
  forall m : map, forall n : nat,
  simple_map m -> tcolorable_with n m -> colorable_with n m.
Proof with auto.
  unfold colorable_with, tcolorable_with.
  intros m n H [k H0 H1].
  exists k...
  apply tcoloring_is_coloring...
Qed.
