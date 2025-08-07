From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq Extra Dependency "Rm.elpi" as Rm.

From elpi Require Import elpi.
From elpi.apps Require Import derive.param2.
From Trocq Require Import mymap.

Elpi Db derive.Rm.db lp:{{
  % [ar-db A1 A2 AR] returns the relation between a type A1 and A2.
  pred ar-db i:term, i:term, o:term. 

  % [Rm-db T D] links a type T to its corresponding R in map.
  pred Rm-db i:term, o:term.

  % [Rm-done T] mean T was already derived
  pred Rm-done o:term.
}}.

Elpi Command derive.Rm.
Elpi Accumulate File derive_hook.
Elpi Accumulate File Rm.
Elpi Accumulate Db derive.Rm.db.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I GR,
    coq.gref->id GR Tname,
    Prefix is Tname ^ "_",
    derive.Rm.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.myder <object name>".
}}. 

Inductive False : Prop :=.
Elpi derive.param2 False.
Elpi derive.mymap False.
Fail Elpi derive.Rm False.
Fail Print False_Rm.

Elpi derive.param2 unit.
Elpi derive.mymap unit.
Fail Elpi derive.Rm unit.
Fail Print unit_Rm.

Elpi derive.param2 bool.
Elpi derive.mymap bool.
Fail Elpi derive.Rm bool.
Fail Print bool_Rm.

Inductive Wrap : Type :=
| KWrap1 : unit -> Wrap.

Elpi derive.param2 Wrap.
Elpi derive.mymap Wrap.
Fail Elpi derive.Rm Wrap.
Fail Print Wrap_Rm.

Inductive WrapMore : Type :=
| KWrap : unit -> bool -> WrapMore
| KWrapWrap : Wrap -> WrapMore
| F : unit -> unit -> unit -> WrapMore.

Elpi derive.param2 WrapMore.
Elpi derive.mymap WrapMore.
Fail Elpi derive.Rm WrapMore.
Fail Print WrapMore_Rm.

Elpi derive.param2 nat.
Elpi derive.mymap nat.
Fail Elpi derive.Rm nat.
Fail Print nat_Rm.

Inductive Box (A : Type) :=
| B : A -> Box A.

Elpi derive.param2 Box.
Elpi derive.mymap Box.
Fail Elpi derive.Rm Box.
Fail Print Box_Rm.

Elpi derive.param2 option.
Elpi derive.mymap option.
Fail Elpi derive.Rm option.
Fail Print option_Rm.

Elpi derive.param2 prod.
Elpi derive.mymap prod.
Fail Elpi derive.Rm prod.
Fail Print prod_Rm.


Fail Elpi derive.param2 list.
Elpi derive.mymap list.
Fail Elpi derive.Rm list.
Fail Print list_Rm.
