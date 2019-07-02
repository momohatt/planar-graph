Require Import Coq.Reals.Reals.

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

Definition meet (r1 r2 : region) : Prop := nonempty (intersect r1 r2).

(* Maps are represented as relations; proper map are partial equivalence  *)
(* relations (PERs).                                                      *)

Record plain_map (m : map) : Prop := PlainMap {
  map_sym z1 z2 : m z1 z2 -> m z2 z1;
  map_trans z1 z2 : m z1 z2 -> subregion (m z2) (m z1)
}.

(* sum of all the regions in map (set of all the points defined on map) *)
Definition cover (m : map) : region := fun z => m z z.

Definition submap (m1 m2 : map) : Prop := forall z, subregion (m1 z) (m2 z).

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

Definition totalize (m : map) : map :=
  fun z z' =>
    (exists z1 z2 : point,
      closure (m z1) z /\ closure (m z2) z /\ adjacent m z1 z2 /\
      intersect (border m z1 z2) (not_corner m) z') \/
    (forall z1 z2 : point,
      ~ (closure (m z1) z /\ closure (m z2) z /\ adjacent m z1 z2) /\
      m z z').

Lemma plain_map_totalize :
  forall (m : map) (z z' : point),
  simple_map m -> m z z' -> totalize m z z'.
Proof.
Admitted.

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
  destruct H.
  destruct H0.
  destruct tcoloring_coloring0.
  split; auto.
  - red. red. intros.
    apply coloring_consistent0.
    unfold totalize.
    intros.

    right; split; auto.
    intros.
    intros z1 z2 [[F1 F2] _].
    unfold closure in F1.
    inversion simple_map_plain0.
    apply map_sym0 in H.
    assert (meet (m z1) (m z0)). { apply F1; auto. }

Admitted.

Lemma coloring_leq_tcoloring :
  forall m : map, forall n : nat,
  tcolorable_with n m -> colorable_with n m.
Proof with auto.
  unfold colorable_with, tcolorable_with.
  intros m n [k H0 H1].
  exists k...
  apply tcoloring_is_coloring...
Qed.
