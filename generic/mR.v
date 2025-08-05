From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "param2.elpi" as param2.
From elpi.apps.derive.elpi Extra Dependency "discriminate.elpi" as discr.
From Trocq Extra Dependency "mR.elpi" as mR.
From Trocq Require Import Hierarchy mymap.

From elpi Require Import elpi.
From elpi.apps Require Import derive.param2 derive.isK.
From elpi.apps Require Import derive.bcongr (* for eq_f register *) 
                              derive.eqK (*for bool_discr *)
                              derive.isK. (* for isK db required by discriminate *)

Elpi Db derive.mR.db lp:{{
  % [mR-db T D] links a type T to its corresponding map in R.
  pred mR-db i:term, o:term.

  % [mR-done T] mean T was already derived
  pred mR-done o:term.
}}.

Elpi Command derive.mR.
Elpi Accumulate File derive_hook.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate File param2.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate Db derive.mymap.db.
Elpi Accumulate File discr.
Elpi Accumulate Db derive.isK.db.
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
Print unit_mR.

Elpi derive "bool".
Print bool_R.
Search "R" bool.
Elpi derive.mymap bool.
Fail Elpi derive.param2 bool.
Elpi Trace Browser.
Elpi derive.isK bool.
Elpi derive.mR bool.
Print bool_mR.

Elpi derive.param2 nat.
Elpi derive.mymap nat.
Elpi derive.isK nat.
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

Elpi derive.isK nat.
Elpi derive.isK option.
Print option_is_Some.
Print option_is_None.
Elpi derive.isK list.

Print option_R.

Definition m (h : 0 = 1 ) P : P 0 -> P 1 :=
  match h as e in eq _ x return P 0 -> P x
  with eq_refl => fun (p : P 0) => p end.

Elpi Query lp:{{

coq.locate "m" (const C),
coq.env.const C (some (fun _ _ h\ fun _ _ p\ match _ (RT h p) _)) _,
coq.say "The return type of m is:" RT

}}.

(* Inductive tricky :=
| K1 : tricky 
| K2 : tricky
| K3 : tricky -> tricky
| K4 : tricky -> tricky.
Elpi derive tricky.
Print tricky_isk_K1.
Print tricky_isk_K3. *)


(* % Build the following function : {{ fun (A : Type) (l : list A) => match l with nil => unit | cons a l => Prop end }}. *)
Elpi Program test lp:{{
  coq.locate "list"
}}.

Elpi Query lp:{{
  F = {{ fun (A : Type) (l : list A) => match l with nil => unit | cons a l => Prop end }}.
  %coq.elaborate-skeleton F Ty FE ok,
  coq.typecheck F Ty ok.
  coq.say F.
  %F = {{ fun b : bool => match b with true => unit | false => Prop end }}.
  %std.findall (param {{ option }} {{ option }} T ) Rules,
  %std.findall (param {{ list }} {{ list }} T ) Rules,
  %std.findall (mymap-db {{ option nat }} {{ option nat }} C ) Rules,
  %coq.typecheck T Ty _,
  coq.say Rules.

}}. 

Print list_R.

Elpi derive.mR list.
Elpi derive list.

