From Trocq Require Import coverage.
From elpi Require Import elpi.
From elpi.apps.derive Require Import param2.
From Trocq Require Import Rm mymap.
From Trocq Require Import Hierarchy.
Unset Uniform Inductive Parameters.

Elpi derive.param2 False.
Elpi derive.param2 Unit.
Elpi derive.param2 Bool.
Elpi derive.param2 Nat.
Elpi derive.param2 Wrap.
Elpi derive.param2 WrapMore.
Elpi derive.param2 Box.
Elpi derive.param2 Option.
Elpi derive.param2 Prod.
Elpi derive.param2 ThreeTypes.
Elpi derive.param2 List.
Elpi derive.param2 Vector.
Elpi derive.param2 Issue.


Elpi derive.mymap False.
Elpi derive.mymap Unit.
Elpi derive.mymap Bool.
Elpi derive.mymap Nat.
Elpi derive.mymap Wrap.
Elpi derive.mymap WrapMore.
Elpi derive.mymap Box.
Elpi derive.mymap Option.
Elpi derive.mymap Prod.
Elpi derive.mymap ThreeTypes.
Elpi derive.mymap List.
Elpi derive.Rm Nat.
Elpi derive.mymap Vector.

(* Notes:

  - things should be uniform/regular, each container should go from A -> C A,
    this is important for the deductive database. Then you can on a single instance
    generate a non uniform version.

  - TODO: in mymap.elpi we hack the mymap-db loading a mymap-db h for an h that
    has a different type. Fixing the previous point clarified this one. See
    the mk-clause code.

  - If a parameter is of type "Type" then we need a relation and a Map1.Has on it,
    If an index is of type "Type" then we need a relation and a Map2b.Has on it,
    while if a parameter/index is of a known type we have already derived param
    and Map1.Has on it and we don't need any extra argument

    Eg
 Check Vector_mymap : 
  forall (i j : Type)  (r : i -> j -> Type), Map1.Has r ->
  forall (i0 j0 : Nat) (r0 : Nat_R i0 j0)  -> Map1.Has (Vector_R i j r i0 j0 r0).
  
 *)

Elpi derive.mymap Issue.

Check Issue_mymap : forall i j : Nat, Nat_R i j -> Issue i -> Issue j.

Elpi Print derive.mymap "Trocq/a". (* you can see the rule for vector in not uniform in the rec call *)

Inductive Test : Prop := KKK :  Vector Nat O' -> Test.

Elpi derive.param2 Test.
Fail Elpi derive.mymap Test. (* bug uniformity *)




