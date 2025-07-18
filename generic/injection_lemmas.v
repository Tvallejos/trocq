From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.
From Trocq Extra Dependency "injection_lemmas.elpi" as injections.

From elpi Require Import elpi.
From elpi.apps Require Import derive.legacy.
From elpi.apps Require Import projK.

Elpi Db derive.injections.db lp:{{

  % [injections I K ILs] links I, 
  %  an inductive type, 
  %  and K, 
  %  a natural number > 0 (representing the constructor number)
  %  with the list of injection lemmas for that constructor
  pred injections i:gref, i:int, o:gref.

  % [injections-done T K] means T K was already derived
  pred injections-done o:gref o:int.
}}.

Elpi Command derive.injections.
Elpi Accumulate File derive_hook.
(* Elpi Accumulate Db Header derive.projK.db. *)
Elpi Accumulate Db derive.projK.db.
Elpi Accumulate File injections.
Elpi Accumulate Db derive.injections.db.
Elpi Accumulate lp:{{
  
  main [str I] :- !, 
    coq.locate I (indt GR),
    % Ind is (indt GR)
    coq.gref->id (indt GR) Tname,
    Suffix is Tname ^ "_",
    derive.injections.main GR Suffix _.
  main _ :- usage.

  pred usage.
  usage :- coq.error "Usage: derive.injections <object name>".
}}. 

Elpi Trace Browser.
Elpi derive.projK list.
Elpi derive.injections list.

Elpi Query lp:{{

  projK-db _ B _, 
  coq.say "Constructor " B ""

}}.
Elpi derive.projK nat.
Elpi derive.injections nat.
