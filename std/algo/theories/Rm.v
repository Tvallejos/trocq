From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq Extra Dependency "algo/elpi/Rm.elpi" as Rm.
From Trocq Extra Dependency "algo/elpi/common_algo.elpi" as common.
From Trocq Extra Dependency "algo/elpi/utils.elpi" as algo_utils.

From elpi Require Import elpi.
From Trocq Require Export Hierarchy.

From elpi.apps Require Export derive.param2.
From elpi.apps Require Export derive.bcongr. (* for eq_f register *) 
(* From Trocq Require Export mymap. *)
(* todo: the real dependency is mymap *)
From Trocq Require Import mR. 
From Trocq Require Export mymap.
Unset Uniform Inductive Parameters. 

Elpi Command derive.Rm.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate File common.
Elpi Accumulate File algo_utils.
Elpi Accumulate Db Header derive.Rm.db.
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

(* hook into derive *)
Elpi Accumulate derive Db Header derive.Rm.db.
Elpi Accumulate derive Db Header derive.param2.db.
Elpi Accumulate derive Db derive.Rm.db.
Elpi Accumulate derive File common.
Elpi Accumulate derive File algo_utils.
Elpi Accumulate derive File Rm.

Elpi Accumulate derive lp:{{
dep1 "Rm" "mymap".
dep1 "Rm" "param2".
derivation (indt T) Prefix ff (derive "Rm" (derive.Rm.main T Prefix) (rm-done T)).

}}.


Elpi derive.param2 nat.
Elpi derive.mymap nat.
Elpi derive.Rm nat.
Inductive issue : nat -> Type := 
| K : forall n, issue n -> issue (S (S n))
| K2 : forall n, issue n.

Elpi derive.param2 issue. 
Elpi derive.mymap issue. 

Check issue_mymap :
  forall n1 n2 (r : nat_R n1 n2), issue n1 -> issue n2.

Elpi derive.param2 option.
Elpi derive.mymap option. 

Check option_mymap :
  forall A B (r : A -> B -> Type), Map1.Has r -> option A -> option B.

