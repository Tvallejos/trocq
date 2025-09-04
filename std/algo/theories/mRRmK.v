From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq Extra Dependency "algo/elpi/mRRmK.elpi" as mRRmK.
From Trocq Require Import injK mR Rm.
From Trocq Extra Dependency "algo/elpi/common_algo.elpi" as common.
From Trocq Extra Dependency "algo/elpi/utils.elpi" as algo_utils.

From elpi Require Import elpi.
From elpi.apps Require Import derive.param2.
(* From elpi.apps Require Import derive.bcongr. for eq_f register  *)
(* From Trocq.Algo Require Import mymap. *)
(* From elpi.apps Require Import derive.induction. *)
From Trocq Require Import Hierarchy.
(* From Trocq Require Import HoTT_additions Hierarchy. *)
Unset Uniform Inductive Parameters. 

Elpi Db derive.mRRmK.db lp:{{
  % [ar-db A1 A2 AR] returns the relation between a type A1 and A2.
  pred ar-db i:term, i:term, o:term. 

  % [mRRm-db T D] links a type T to its corresponding R in map.
  pred mRRm-db i:term, o:term.

  % [mRRm-done T] mean T was already derived
  pred rm-done o:term.
}}.

Elpi Command derive.mRRmK.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate File common.
Elpi Accumulate File algo_utils.
Elpi Accumulate Db Header derive.injectionsK.db.
Elpi Accumulate Db derive.injectionsK.db.
Elpi Accumulate Db Header derive.mR.db.
Elpi Accumulate Db derive.mR.db.
Elpi Accumulate Db Header derive.Rm.db.
Elpi Accumulate Db derive.Rm.db.

Elpi Accumulate Db derive.mRRmK.db.
Elpi Accumulate File mRRmK.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.mRRmK.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.mRRmK <object name>".
}}. 

(* From Trocq Require Import coverage.
Elpi derive.param2 Unit.
Elpi derive.mymap Unit.
Elpi derive.projK Unit.
Elpi derive.injections Unit.
Elpi derive.isK Unit.
Elpi derive.mR Unit.
Elpi derive.Rm Unit.
Elpi derive.injK Unit.
Elpi derive.mRRmK Unit.

Elpi derive.param2 Bool.
Elpi derive.mymap Bool.
Elpi derive.projK Bool.
Elpi derive.injections Bool.
Elpi derive.isK Bool.
Elpi derive.mR Bool.
Elpi derive.Rm Bool.
Elpi derive.injK Bool.
Elpi derive.mRRmK Bool.

Elpi derive.param2 Wrap.
Elpi derive.mymap Wrap.
Elpi derive.projK Wrap.
Elpi derive.injections Wrap.
Elpi derive.isK Wrap.
Elpi derive.mR Wrap.
Elpi derive.Rm Wrap.
Elpi derive.injK Wrap.
Elpi Trace Browser.
Elpi derive.mRRmK Wrap.

Elpi derive.param2 WrapMore.
Elpi derive.mymap WrapMore.
Elpi derive.projK WrapMore.
Elpi derive.injections WrapMore.
Elpi derive.isK WrapMore.
Elpi derive.mR WrapMore.
Elpi derive.Rm WrapMore.
Elpi derive.injK WrapMore.
Elpi derive.mRRmK WrapMore. *)
