
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From Trocq.Algo Extra Dependency "injK.elpi" as injK.

From elpi Require Import elpi.
From elpi.apps Require Import derive.bcongr. (* for eq_f register *) 

From Trocq Require Import HoTT_additions Hierarchy.
Unset Uniform Inductive Parameters. 

Elpi Db derive.injectionsK.db lp:{{

  % [injectionsK-db I K ILs] links I, 
  %  constructor inductive type, 
  %  and K, 
  %  a natural number > 0 (representing the constructor number)
  %  with the list of injectionK lemmas for that constructor
  pred injectionsK-db i:term, i:int, o:term.

  % [injectionsK-done T K] means T K was already derived
  pred injectionsK-done o:term. 
}}.

Elpi Command derive.injectionsK.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db derive.injectionsK.db.
Elpi Accumulate File injK.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I (indt GR),
    coq.gref->id (indt GR) Tname,
    Prefix is Tname ^ "_",
    derive.injK.main GR Prefix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.Rm <object name>".
}}. 
