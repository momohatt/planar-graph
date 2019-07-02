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
  (* if z2 belongs to the region containing z1,
   * then either z1 belongs to the region containing z2 *)
  map_sym z1 z2 : m z1 z2 -> m z2 z1;
  (* or the region of z2 is a subregion of that of z1 *)
  map_trans z1 z2 : m z1 z2 -> subregion (m z2) (m z1)
}.

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

Record coloring (m k : map) : Prop := Coloring {
  coloring_plain : plain_map k;
  coloring_cover : subregion (cover k) (cover m);
  coloring_consistent : submap m k;
  coloring_adjacent z1 z2 : adjacent m z1 z2 -> ~ k z1 z2
}.

Definition colorable_with (n : nat) (m : map) : Prop :=
  exists2 k, coloring m k & at_most_regions n k.
