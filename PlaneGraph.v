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

Lemma closure_supregion (m : map) (z : point) :
  m z z -> closure (m z) z.
Proof with auto.
  red. intros. exists z... split...
Qed.

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

Record adjacent (m : map) (z1 z2 : point) : Prop := Adjacent {
  adjacent_cover_left : m z1 z1;
  adjacent_cover_right : m z2 z2;
  adjacent_not_same_face : ~ m z1 z2;
  adjacent_meet : meet (not_corner m) (border m z1 z2)
}.

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

Record coloring (m k : map) : Prop := Coloring {
  coloring_plain : plain_map k;
  coloring_cover : subregion (cover m) (cover k);
  coloring_consistent : submap m k;
  coloring_adjacent z1 z2 : adjacent m z1 z2 -> ~ k z1 z2
}.

Definition colorable_with (n : nat) (m : map) : Prop :=
  exists2 k, coloring m k & at_most_regions n k.

(* TODO: add a restriction so that each region of m should be convex *)
Definition totalize (m : map) : map :=
  fun z z' =>
    (* もともとm上の点である *)
    m z z' \/
    (* z1, z2を含むregionの間にある点 *)
    (exists z1 z2 : point,
      m z1 z1 /\ m z2 z2 /\ ~ m z1 z2 /\
      intersect (border m z1 z2) (not_corner m) z /\
      intersect (border m z1 z2) (not_corner m) z').

Lemma totalize_symm (m : map) (z1 z2 : point) :
  simple_map m -> totalize m z1 z2 -> totalize m z2 z1.
Proof.
  unfold totalize. intros. destruct H0.
  - left. apply map_symm; auto.
  - destruct H0 as [z3 [z4 [? [? [? [[? ?] [? ?]]]]]]].
    right. exists z3, z4.
    repeat (split; auto).
Qed.

Lemma totalize_trans (m : map) (z1 z2 z3 : point) :
  simple_map m -> totalize m z1 z2 -> totalize m z2 z3 -> totalize m z1 z3.
Proof with auto.
  intros. destruct H0.
  - destruct H1.
    + left. apply map_trans with z2...
    + destruct H1 as [z4 [z5 [? [? [? [[? ?] [? ?]]]]]]].
      apply border_not_covered in H4...
      apply map_covered_right in H0... contradiction.
  - destruct H0 as [z4 [z5 [? [? [? [[? ?] [? ?]]]]]]].
    destruct H1.
    + apply border_not_covered in H6...
      apply map_covered_left in H1... contradiction.
    + destruct H1 as [z6 [z7 [? [? [? [[? ?] [? ?]]]]]]].
      assert (m z4 z6 /\ m z5 z7 \/ m z4 z7 /\ m z5 z6).
      { apply inter_region_deterministic with z2; auto; split; auto; split; auto. }
      destruct H14; destruct H14.
      { right. exists z4, z5. destruct H12. repeat (split; auto).
        - apply closure_map_trans with z6... apply map_symm...
        - apply closure_map_trans with z7... apply map_symm... }
      { right. exists z4, z5. destruct H12. repeat (split; auto).
        - apply closure_map_trans with z7... apply map_symm...
        - apply closure_map_trans with z6... apply map_symm... }
Qed.

Lemma totalize_subregion (m : map) (z : point) :
  subregion (m z) (totalize m z).
Proof.
  red; intros; left; auto. Qed.

Lemma totalize_plain_map (m : map) :
  simple_map m -> plain_map (totalize m).
Proof with auto.
  intros. inversion H. split; intros.
  - apply totalize_symm...
  - red. intros. apply totalize_trans with z3...
    apply totalize_trans with z2... apply totalize_trans with z2...
    apply totalize_symm...
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

Lemma totalize_open (m : map) (z1 z2 : point) :
  simple_map m ->
  totalize m z1 z2 -> open (totalize m z1) -> m z1 z2.
Proof with auto.
  intros. inversion H0...
  exfalso.
  destruct H2 as [z3 [z4 [? [? [? [[? ?] [? ?]]]]]]].
  destruct (H1 z2) as [u ?]...
  assert (totalize m z1 z3).
  { destruct H7.
    assert (meet (m z3) (in_rectangle u)).
    { apply H7... red. intros. exists u... }
    destruct H12 as [z5 [? ?]].
    assert (totalize m z1 z5)...
    apply totalize_trans with z5... left. apply map_symm... }
  assert (totalize m z1 z4).
  { destruct H7.
    assert (meet (m z4) (in_rectangle u)).
    { apply H12... red. intros. exists u... }
    destruct H13 as [z5 [? ?]].
    assert (totalize m z1 z5)...
    apply totalize_trans with z5... left; apply map_symm... }
  assert (totalize m z3 z4).
  { apply totalize_trans with z1... apply totalize_symm... }
  destruct H13.
  - contradiction.
  - destruct H13 as [z5 [z6 [? [? [? [[? ?] _]]]]]].
    apply border_not_covered in H16...
Qed.

Lemma totalize_preserves_corner_map (m : map) (x z1 z2 : point) :
  simple_map m -> corner_map m x z1 z2 <-> corner_map (totalize m) x z1 z2.
Proof with auto.
  split; unfold corner_map; intros [? [? ?]].
  - splits.
    + red. intros. destruct H3.
      { destruct (H0 z)... exists x0...
        apply subregion_trans with (m z1)...
        apply totalize_subregion. }
      { exfalso.
        destruct H3 as [z3 [z4 [_ [_ [? [? ?]]]]]].
        destruct H4.
        apply border_not_covered in H4...
        apply H4. apply map_covered_left in H1... }
    + left...
    + repeat red. intros.
      repeat red in H2. destruct (H2 u) as [z ?]...
      exists z. destruct H5. split... left...
  - splits.
    + red. intros. unfold open in H0. destruct (H0 z) as [u ?]... left...
      exists u... unfold subregion in H5.
      red; intros.
      destruct (H5 z0)...
      exfalso. destruct H7 as [z3 [z4 [_ [_ [? [[? ?] _]]]]]].
      apply border_not_covered in H8...
      apply H8. apply map_covered_left in H3...
    + apply totalize_open...
    + repeat red. intros.
      destruct (H2 u) as [z ?]... exists z... destruct H5. split...
      apply totalize_open...
Qed.

Lemma totalize_preserves_not_corner (m : map) (x : point) :
  simple_map m -> not_corner m x -> not_corner (totalize m) x.
Proof.
  unfold not_corner, at_most_regions. intros.
  destruct H0 as [f ?]. exists f. intros.
  assert (exists2 i : nat, i < 2 & corner_map m x (f i) z).
  { apply H0. apply totalize_preserves_corner_map; auto. }
  destruct H2 as [i ?].
  exists i; auto. rewrite <- totalize_preserves_corner_map; auto.
Qed.

Record tcoloring (m k : map) : Prop := TColoring {
  tcoloring_coloring : coloring (totalize m) k;
  tcoloring_adjacent z :
    forall z1 z2 : point,
    adjacent (totalize m) z z1 -> adjacent (totalize m) z z2 -> ~ k z1 z2
}.

Definition tcolorable_with (n : nat) (m : map) : Prop :=
  exists2 k, tcoloring m k & at_most_regions n k.

Lemma tcoloring_is_coloring :
  forall m k : map, simple_map m -> tcoloring m k -> coloring m k.
Proof with auto.
  intros. destruct H0. destruct tcoloring_coloring0.
  split...
  - apply subregion_trans with (cover (totalize m))...
    apply totalize_cover_subregion...
  - apply submap_trans with (totalize m)...
    repeat red...
  - (* any adjacent two faces in m are colored differently *)
    intros z1 z2 [? ? ? [? [? ?]]].
    assert (~ m x x). { apply border_not_covered with z1 z2... }
    apply tcoloring_adjacent0 with x.
    + (* adjacent (totalize m) x z1 *)
      split.
      { right. exists z1, z2. repeat (split; auto). }
      { left... }
      { (* ~ totalize m x z1 *)
        intros F. destruct F.
        - (* m x z1 を仮定する場合 *)
          apply map_covered_left in H3...
        - (* z1が境界上にあることを仮定する場合 *)
          destruct H3 as [z3 [z4 [? [? [? [? ?]]]]]].
          destruct H7. apply border_not_covered in H7... }
      { (* meet (not_corner (totalize m)) (border (totalize m) x z1) *)
        exists x. split.
        - apply totalize_preserves_not_corner...
        - split.
          + apply closure_supregion... right.
            exists z1, z2... destruct H1. repeat split...
          + destruct H1.
            cut (subregion (closure (m z1)) (closure (totalize m z1)))...
            apply closure_preserves_subregion. apply totalize_subregion. }
    + (* same as previous one! *)
      split.
      { right. exists z1, z2. repeat (split; auto). }
      { left... } { unfold totalize. intros F. destruct F.
        - apply map_covered_left in H3...
        - destruct H3 as [z3 [z4 [? [? [? [? ?]]]]]].
          destruct H7. apply border_not_covered in H7... }
      { exists x. split.
        - apply totalize_preserves_not_corner...
        - split.
          + apply closure_supregion... right.
            exists z1, z2... destruct H1. repeat split...
          + destruct H1.
            cut (subregion (closure (m z2)) (closure (totalize m z2)))...
            apply closure_preserves_subregion. apply totalize_subregion. }
Qed.

Theorem coloring_leq_tcoloring (m : map) (n : nat) :
  simple_map m -> tcolorable_with n m -> colorable_with n m.
Proof with auto.
  intros H [k H0 H1]. exists k... apply tcoloring_is_coloring...
Qed.

Record incident (m : map) (z1 z2 : point) : Prop := Incident {
  incident_not_same_edge : ~ totalize m z1 z2;
  incident_common_adjacent : exists z, adjacent (totalize m) z z1 /\ adjacent (totalize m) z z2
}.

Definition edge (m : map) : map :=
  fun z z' =>
    (* z1, z2を含むregionの間にある点 *)
    (exists z1 z2 : point,
      m z1 z1 /\ m z2 z2 /\ ~ m z1 z2 /\
      intersect (border m z1 z2) (not_corner m) z /\
      intersect (border m z1 z2) (not_corner m) z').

Record ecoloring (m k : map) : Prop := EColoring {
  ecoloring_plain : plain_map k;
  ecoloring_cover : subregion (cover (edge m)) (cover k);
  ecoloring_consistent : submap (edge m) k;
  ecoloring_incident z1 z2 :
    incident m z1 z2 -> ~ k z1 z2
}.

Definition ecolorable_with (n : nat) (m : map) : Prop :=
  exists2 k, ecoloring m k & at_most_regions n k.

Theorem tcoloring_is_ecoloring (m k : map) :
  simple_map m -> tcoloring m k -> ecoloring m k.
Proof with auto.
  intros. inversion H0. split.
  - apply coloring_plain with m... apply tcoloring_is_coloring...
  - destruct tcoloring_coloring0. apply subregion_trans with (cover (totalize m))...
    red. intros. repeat red. right...
  - destruct tcoloring_coloring0. apply submap_trans with (totalize m)...
    repeat red. intros. right...
  - intros. destruct H1. destruct incident_common_adjacent0 as [z [? ?]].
    eapply tcoloring_adjacent0 with z...
Qed.

Theorem ecoloring_leq_tcoloring (m : map) (n : nat) :
  simple_map m -> tcolorable_with n m -> ecolorable_with n m.
Proof with auto.
  intros ? [k ? ?]. exists k... apply tcoloring_is_ecoloring...
Qed.

Theorem tcoloring_leq_coloring_and_ecoloring (m : map) (n n' : nat) :
  colorable_with n m -> ecolorable_with n' m ->
  tcolorable_with (n + n') m.
Proof.
  intros [k ?] [k' ?].
  red.
Admitted.

Definition num_of_regions (n : nat) (m : map) : Prop :=
  ~ (at_most_regions (n - 1) m) /\ at_most_regions n m.

(* alias *)
Definition num_of_vertices := num_of_regions.

Definition num_of_edges (n : nat) (m : map) : Prop :=
  ~ (at_most_regions (n - 1) (edge m)) /\ at_most_regions n (edge m).

(*
Definition num_of_faces (n : nat) (m : map) : Prop :=
  ~ (at_most_regions (n - 1) (corner_map m)) /\ at_most_regions n (corner_map m).
*)
