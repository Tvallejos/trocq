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

Elpi Program test lp:{{ 
  kind  term  type.
  type  app   term -> term -> term.
  type  fun   (term -> term) -> term.

  kind  ty   type.           % the data type of types
  type  arr  ty -> ty -> ty. % our type constructor

  pred of i:term, o:ty. % the type checking algorithm
  of (app X Y) B :- 
    of X (arr A B), 
    of Y A.
  of (fun Bo) (arr A B) :-
  pi x\
    of x A ==>
    of (Bo x) B.

}}.
(* Elpi Query lp:{{
  coq.locate "list" (indt GR),
  coq.locate "nat" (indt GR2),

  coq.mk-apps (global (indt GR)) [global (indt GR2)] ListNat,

  coq.say "list nat:" ListNat
}}. *)

(* Elpi Query lp:{{
  coq.locate "list" (indt GR),
  coq.locate "nat" (indt GR2),
  L is (global (indt GR)),
  N is (global (indt GR2)),
  coq.mk-app L [N] ListNat,
  %coq.say EQ,
  coq.say ListNat.

}}. *)

Elpi Query lp:{{

  coq.locate "list" (indt GR),
  coq.locate "nat" (indt GR2),
  %
  coq.say R.
  %F1 = {{ fun (A : Type) => lp:{{global (indt GR)}} A }},
  %coq.typecheck F1 _ ok.

}}.

(* Elpi Query lp:{{ 
  
  F = fun `A` {{ Type }} x\ {coq.mk-app (global (indt GR)) [x]},
  %F = fun `A` {{ Type }} x\ {{ lp:(global (indt GR)) lp:(x) }}, 
  coq.typecheck F _ ok.
 
  (* coq.say F. *)
}}. *)

Elpi Command derive.injections.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.projK.db.
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

Elpi derive.projK nat.
Elpi derive.injections nat.
Print nat_injections21.

Elpi derive.projK list.
Print projcons1.
Fail Elpi derive.injections list.

Elpi Query lp:{{

  projK-db _ B _, 
  coq.say "Constructor " B ""

}}.
