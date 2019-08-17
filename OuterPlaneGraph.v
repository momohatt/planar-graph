Require Import PlaneGraph.

Definition outerface (m : map) (z1 : point) : Prop :=
  exists2 z2 : point, adjacent m z1 z2 & ~ (cover m z2).

Record outerplane_map (m : map) : Prop := OuterplaneMap {
  outerplane_map_finsimple : finite_simple_map m;
  outerplane_map_outer z : outerface m z
}.
