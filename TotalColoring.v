Require Import Coloring.
Require Import PlaneGraph.

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
    intros. destruct H0. destruct adjacent_meet as [? [? ?]].
    assert (~ m x x) by apply (border_not_covered _ _ _ _ H adjacent_not_same_face H1).
    apply tcoloring_adjacent0 with x.
    + (* adjacent (totalize m) x z1 *)
      split.
      { right. exists z1, z2. repeat (split; auto). }
      { left... }
      { (* ~ totalize m x z1 *)
        unfold totalize. intros F. destruct F.
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

Theorem coloring_leq_tcoloring :
  forall m : map, forall n : nat,
  simple_map m -> tcolorable_with n m -> colorable_with n m.
Proof with auto.
  unfold colorable_with, tcolorable_with.
  intros m n H [k H0 H1].
  exists k...
  apply tcoloring_is_coloring...
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
