From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.
(* From Trocq Extra Dependency "algo/elpi/utils.elpi" as algo_utils. *)
From Trocq Extra Dependency "algo/elpi/common_algo.elpi" as common.
From Trocq Extra Dependency "algo/elpi/utils.elpi" as utils.
From Trocq Extra Dependency "algo/elpi/swap.elpi" as swap.

From elpi.apps Require Import derive.legacy derive.param2.
(* From elpi.apps Require Export derive.bcongr. (* for eq_f register  *) *)
(* From elpi.apps Require Export derive.projK.  *)

From Trocq Require Export Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.swap.db lp:{{

  % [swap I S] links I inductive type, 
  %  with the function showing symmetry 
  pred swap-db i:term, o:term.

  % [swap-done T K] means T K was already derived
  pred swap-done o:inductive. 
}}.

Elpi Command derive.swap.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate File common.
Elpi Accumulate File utils.
Elpi Accumulate Db Header derive.swap.db.
Elpi Accumulate Db derive.swap.db.
Elpi Accumulate File swap.
Elpi Accumulate lp:{{
  
  main [str I] :- !, 
    coq.locate I (indt GR),
    % Ind is (indt GR)
    coq.gref->id (indt GR) Tname,
    Suffix is Tname ^ "_",
    derive.swap.main GR Suffix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.swap <object name>".
}}. 

(* hook into derive *)



Elpi Accumulate derive Db Header derive.swap.db.
Elpi Accumulate derive Db derive.swap.db.
Elpi Accumulate derive File common.
Elpi Accumulate derive File utils. 
Elpi Accumulate derive File swap.

Elpi Accumulate derive lp:{{

dep1 "swap" "param2".
derivation (indt T) Prefix ff (derive "swap" (derive.swap.main T Prefix) (swap-done T)).

}}.
