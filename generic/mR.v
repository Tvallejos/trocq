From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "param2.elpi" as param2.
From Trocq Extra Dependency "mR.elpi" as mR.
From Trocq Require Import Hierarchy mymap.

From elpi Require Import elpi.
From elpi.apps Require Import derive.param2.
(* From elpi.apps Require Import derive derive.param2. *)

Elpi Db derive.mR.db lp:{{
  % [mR-db T D] links a type T to its corresponding map in R.
  pred mR-db i:inductive, o:term.

  % [mR-done T] mean T was already derived
  pred mR-done o:inductive.
}}.

Elpi Command derive.mR.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate File param2.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate File mR.
Elpi Accumulate Db derive.mR.db.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.mR.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.mR <object name>".
}}. 

Elpi derive list.
(* Print list_R. *)
Goal forall (A B : Type) (R : Param10.Rel A B), A -> B.
intros A B R. Fail exact R. exact (map R). Abort.


Elpi derive "unit".
Print unit_R.
Elpi derive.mymap unit.
Elpi derive.mR unit.

Elpi derive.param2 nat.
Elpi derive.mymap nat.
Elpi derive.mR nat.

Elpi Trace Browser.
Elpi derive.param2 option.
Elpi derive.mymap option.
Elpi derive.mR option.

(* Elpi derive.param2 list. *)
Elpi derive.mymap list.
Elpi derive.mR list.

Elpi derive.param2 prod.
Elpi derive.mymap prod.
Elpi derive.mR prod.

Print option_R.
Elpi Query lp:{{
  std.findall (param {{ option }} {{ option }} T ) Rules,
  %std.findall (param {{ list }} {{ list }} T ) Rules,
  %std.findall (mymap-db {{ option nat }} {{ option nat }} C ) Rules,
  %coq.typecheck T Ty _,
  coq.say Rules.

}}. 

Print list_R.

Elpi derive.mR list.
Elpi derive list.

