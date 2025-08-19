From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Algo Extra Dependency "Rm.elpi" as Rm.
From Trocq.Algo Extra Dependency "common_algo.elpi" as common.

From elpi Require Import elpi.
From elpi.apps Require Import derive.param2.
From elpi.apps Require Import derive.bcongr. (* for eq_f register *) 
From Trocq.Algo Require Import mymap.
From elpi.apps Require Import derive.induction.
From Trocq Require Import HoTT_additions Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.Rm.db lp:{{
  % [ar-db A1 A2 AR] returns the relation between a type A1 and A2.
  pred ar-db i:term, i:term, o:term. 

  % [Rm-db T D] links a type T to its corresponding R in map.
  pred rm-db i:term, o:term.

  % [Rm-done T] mean T was already derived
  pred rm-done o:term.
}}.

Elpi Command derive.Rm.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate File common.
Elpi Accumulate Db derive.Rm.db.
Elpi Accumulate File Rm.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.Rm.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.Rm <object name>".
}}. 


Elpi derive.param2 unit.
Elpi derive.mymap unit.

Elpi derive.Rm unit.
Print unit_Rm.

Elpi derive.param2 bool.
Elpi derive.mymap bool.
Elpi derive.Rm bool.
Print bool_Rm.

Inductive Wrap : Type :=
| KWrap1 : unit -> Wrap.

Elpi derive.param2 Wrap.
Elpi derive.mymap Wrap.
Elpi derive.Rm Wrap.
Print Wrap_Rm.

Inductive WrapMore : Type :=
| KWrap : unit -> bool -> WrapMore
| KWrapWrap : Wrap -> WrapMore
| F : unit -> unit -> unit -> WrapMore.

Elpi derive.param2 WrapMore.
Elpi derive.mymap WrapMore.
Elpi derive.Rm WrapMore.
Print WrapMore_Rm.

Elpi derive.param2 nat.
Elpi derive.mymap nat.
Elpi derive.Rm nat.
Print nat_Rm.

Inductive DoubleRec : Type :=
| Base
| Double : DoubleRec -> DoubleRec -> DoubleRec.
Elpi derive.param2 DoubleRec.
Elpi derive.mymap DoubleRec.
Elpi derive.Rm DoubleRec.
Print DoubleRec_Rm.

Inductive Box (A : Type) :=
| B : A -> Box A.

Elpi derive.param2 Box.
Elpi derive.mymap Box.
Set Printing All.
About R_in_map.
Print B_R.
Print Box_R_ind.
Elpi derive.Rm Box.
Print Box_Rm.

Elpi derive.param2 option.
Elpi derive.mymap option.
Elpi derive.Rm option.
Print option_Rm.

Elpi derive.param2 prod.
Elpi derive.mymap prod.
Elpi derive.Rm prod.
Print prod_Rm.


Elpi derive.param2 list.
Elpi derive.mymap list.
Elpi derive.Rm list.
Print list_Rm.
