Require Import Database.
From Trocq Require Import map4 umap.
From Trocq Require Import coverage.
Unset Uniform Inductive Parameters.

Elpi derive False.
Check False_map4 : IsUMap False_R.

Elpi derive Unit.
Check Unit_map4 : IsUMap Unit_R.

Elpi derive Bool.
Check Bool_map4 : IsUMap Bool_R.

Elpi derive Wrap.
Check Wrap_map4 : IsUMap Wrap_R.

Elpi derive WrapMore.
Check WrapMore_map4 : IsUMap WrapMore_R.

Elpi derive Nat.
Check Nat_map4 : IsUMap Nat_R.

Elpi derive Box.
Check Box_map4 : forall A1 A2 AR UR, IsUMap (Box_R A1 A2 AR).

Elpi derive Option.
Check Option_map4 : forall A1 A2 AR UR, IsUMap (Option_R A1 A2 AR).

Elpi derive Prod.
Check Prod_map4 : forall A1 A2 AR UR B1 B2 BR BUR, IsUMap (Prod_R A1 A2 AR B1 B2 BR).

Elpi derive ThreeTypes.
Check ThreeTypes_map4 : forall A1 A2 AR UR B1 B2 BR BUR C1 C2 CR CUR, IsUMap (ThreeTypes_R A1 A2 AR B1 B2 BR C1 C2 CR).

Elpi derive List.
Check List_map4 : forall A1 A2 AR UR, IsUMap (List_R A1 A2 AR).