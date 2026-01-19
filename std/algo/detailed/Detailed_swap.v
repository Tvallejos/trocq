From Coq Require Import ssreflect.
From elpi.apps.derive Require Import derive derive.param2.
Require Import Hierarchy.
From Trocq Require Import coverage.
(* Require Import HoTT_additions Hierarchy. *)
Unset Uniform Inductive Parameters.
(* Unset Universe Polymorphism. *)
Unset Universe Minimization ToSet.

(* Definition Unit := unit. *)

Elpi derive.param2 Unit.
Definition UnitR := Unit_R.
Definition unit_Pred := fun (s1 s2: Unit) (RR : Unit_R s1 s2)=> Unit_R s2 s1.

Definition unitR_sym : forall u1 u2, UnitR u1 u2 -> UnitR u2 u1.
Proof.
move=> u1 u2 uR.
refine (Unit_R_rect unit_Pred _ u1 u2 uR).
- exact TT_R.
Defined.

Definition unitR_symKPred := fun u1 u2 (uR : UnitR u1 u2)=> unitR_sym _ _ (unitR_sym _ _ uR) = uR.
Definition unitR_symK : forall u1 u2 (uR : UnitR u1 u2), unitR_sym _ _ (unitR_sym _ _ uR) = uR.
Proof.
move=> u1 u2 uR.
refine (Unit_R_ind unitR_symKPred _ u1 u2 uR).
exact: eq_refl.
Defined.

Elpi derive.param2 Bool.
Definition BoolR := Bool_R.

Notation BoolR_symPred := (fun b1 b2 (bR : Bool_R b1 b2)=> Bool_R b2 b1).
Definition boolR_sym : forall b1 b2 (bR : Bool_R b1 b2), Bool_R b2 b1.
Proof.
refine (fun b1 b2 bR=> Bool_R_rect BoolR_symPred _ _ b1 b2 bR).
- exact: Falseb_R.
- exact: Trueb_R.
Defined.

Notation BoolR_symKPred := (fun b1 b2 (bR : Bool_R b1 b2)=> boolR_sym _ _ (boolR_sym _ _ bR) = bR).
Definition boolR_symK : forall b1 b2 (bR : Bool_R b1 b2), boolR_sym _ _ (boolR_sym _ _ bR) = bR.
Proof.
refine (fun b1 b2 bR=> Bool_R_ind BoolR_symKPred _ _ b1 b2 bR).
- exact: eq_refl.
- exact: eq_refl.
Defined.
Elpi derive.param2 Wrap.
Definition WrapR := Wrap_R.

Notation wrapR_symPred := (fun w1 w2 (wR : Wrap_R w1 w2) => Wrap_R w2 w1).
Definition wrapR_sym : forall w1 w2, Wrap_R w1 w2 -> Wrap_R w2 w1.
Proof.
refine (fun w1 w2 wR=> Wrap_R_rect wrapR_symPred _ w1 w2 wR).
refine (fun u1 u2 uR=> _).
exact: (KWrap1_R u2 u1 (unitR_sym u1 u2 uR)).
Defined.

Notation wrapR_symKPred := (fun w1 w2 (wR : Wrap_R w1 w2) => wrapR_sym _ _ (wrapR_sym _ _ wR) = wR).
Definition WrapR_symK : forall w1 w2 (wR : Wrap_R w1 w2), wrapR_sym _ _ (wrapR_sym _ _ wR) = wR.
Proof.
refine (fun w1 w2 wR=> Wrap_R_ind wrapR_symKPred _ w1 w2 wR).
refine (fun u1 u2 uR=> _).
unfold wrapR_sym.
unfold Wrap_R_rect.
rewrite unitR_symK.
exact: eq_refl.
Defined.

Elpi derive.param2 WrapMore.
Notation wrapMoreR_symPred := (fun w1 w2 (wR : WrapMore_R w1 w2) => WrapMore_R w2 w1).
Definition wrapMoreR_sym : forall w1 w2, WrapMore_R w1 w2 -> WrapMore_R w2 w1.
Proof.
refine (fun w1 w2 wR=> WrapMore_R_rect wrapMoreR_symPred _ _ _ w1 w2 wR).
- refine (fun u1 u2 uR=> _).
  refine (fun b1 b2 bR=> _).
  exact: (KWrap_R u2 u1 (unitR_sym u1 u2 uR) b2 b1 (boolR_sym b1 b2 bR)).
- refine (fun w1 w2 wR=> _).
  exact: (KWrapWrap_R w2 w1 (wrapR_sym w1 w2 wR)).
- refine (fun u1 u2 uR=> _).
  refine (fun u3 u4 uR2=> _). 
  refine (fun u5 u6 uR3=> _). 
  exact: (F_R u2 u1 (unitR_sym u1 u2 uR) u4 u3 (unitR_sym u3 u4 uR2) u6 u5 (unitR_sym u5 u6 uR3)).
Defined.

Notation wrapMoreR_symKPred := (fun w1 w2 (wR : WrapMore_R w1 w2) => wrapMoreR_sym _ _ (wrapMoreR_sym _ _ wR) = wR).
Definition WrapMoreR_symK : forall w1 w2 (wR : WrapMore_R w1 w2), wrapMoreR_sym _ _ (wrapMoreR_sym _ _ wR) = wR.
Proof.
refine (fun w1 w2 wR=> WrapMore_R_ind wrapMoreR_symKPred _ _ _ w1 w2 wR).
- refine (fun u1 u2 uR=> _).
  refine (fun b1 b2 bR=> _).
  cbn delta beta iota.
  rewrite unitR_symK boolR_symK.
  exact: eq_refl.
- refine (fun w1 w2 wR=> _).
  cbn delta beta iota.
  rewrite WrapR_symK.
  exact: eq_refl.
- refine (fun u1 u2 uR=> _).
  refine (fun u3 u4 uR2 => _).
  refine (fun u5 u6 uR3 => _).
  cbn delta beta iota.
  rewrite !unitR_symK. 
  exact: eq_refl.
Defined.

Definition Nat := nat.
Elpi derive.param2 nat.
Definition NatR := nat_R.

Notation nat_symPred := (fun w1 w2 (wR : nat_R w1 w2) => nat_R w2 w1).
Fixpoint nat_sym : forall w1 w2, nat_R w1 w2 -> nat_R w2 w1.
Proof.
refine (fun w1 w2 wR=> nat_R_rect nat_symPred _ _ w1 w2 wR).
exact: O_R.
refine (fun n1 n2 nR IH => _).
apply (S_R _ _ (nat_sym _ _ nR)).
Defined.

Notation nat_symKPred := (fun w1 w2 (wR : nat_R w1 w2) => nat_sym _ _ (nat_sym _ _ wR) = wR).
Definition nat_symK : forall w1 w2 (wR : nat_R w1 w2), nat_sym _ _ (nat_sym _ _ wR) = wR.
Proof.
refine (fun w1 w2 wR=> nat_R_ind nat_symKPred _ _ w1 w2 wR).
exact: eq_refl.
refine (fun n1 n2 nR IH => _).
cbn delta beta iota.
rewrite IH.
exact: eq_refl.
Defined.

Inductive Box (A : Type) : Type := B : A -> Box A.
Elpi derive.param2 Box.

Check @sym_rel.
Notation boxR_symPred := (fun A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : Box_R A1 A2 AR b1 b2) => Box_R A2 A1 (sym_rel AR) b2 b1).
Definition boxR_sym : forall A1 A2 (AR: A1 -> A2 -> Type) b1 b2, Box_R A1 A2 AR b1 b2 -> Box_R A2 A1 (sym_rel AR) b2 b1.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (Box_R_rect A1 A2 AR (boxR_symPred A1 A2 AR) _ _ _ bR).
move=> a1 a2 ar.
refine (B_R A2 A1 (sym_rel AR) a2 a1 _).
exact: ( (fun x y r => r) a1 a2 ar).
Defined.

Notation boxR_symKPred := (fun A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : Box_R A1 A2 AR b1 b2) => boxR_sym A2 A1 (sym_rel AR) b2 b1 (boxR_sym A1 A2 AR b1 b2 bR) = bR).
Definition boxR_symK :
  forall A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : Box_R A1 A2 AR b1 b2), boxR_sym A2 A1 (sym_rel AR) b2 b1 (boxR_sym A1 A2 AR b1 b2 bR) = bR.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (Box_R_ind A1 A2 AR (boxR_symKPred A1 A2 AR) _ b1 b2 bR).
move=> a1 a2 ar.
cbn delta beta iota.
exact: eq_refl.
Defined.

Definition Option (A : Type) : Type := option A.

Elpi derive.param2 option.

Notation option_symPred := (fun A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : option_R A1 A2 AR b1 b2) => option_R A2 A1 (sym_rel AR) b2 b1).
Definition option_sym : forall A1 A2 (AR: A1 -> A2 -> Type) b1 b2, option_R A1 A2 AR b1 b2 -> option_R A2 A1 (sym_rel AR) b2 b1.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (option_R_rect A1 A2 AR (option_symPred A1 A2 AR) _ _ _ _ bR).
- move=> a1 a2 ar. exact: (Some_R A2 A1 (sym_rel AR) a2 a1 ar).
- exact: (None_R A2 A1 (sym_rel AR)).
Defined.

Notation optionR_symKPred := (fun A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : option_R A1 A2 AR b1 b2) => option_sym A2 A1 (sym_rel AR) b2 b1 (option_sym A1 A2 AR b1 b2 bR) = bR).
Definition option_symK :
  forall A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : option_R A1 A2 AR b1 b2), option_sym A2 A1 (sym_rel AR) b2 b1 (option_sym A1 A2 AR b1 b2 bR) = bR.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (option_R_ind A1 A2 AR (optionR_symKPred A1 A2 AR) _ _ b1 b2 bR).
move=> a1 a2 ar.
cbn delta beta iota.
exact: eq_refl.
- exact: eq_refl.
Defined.

Definition List (A : Type) := list A.
Elpi derive.param2 list.

Notation list_symPred := (fun A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : list_R A1 A2 AR b1 b2) => list_R A2 A1 (sym_rel AR) b2 b1).
Fixpoint list_sym : forall A1 A2 (AR: A1 -> A2 -> Type) b1 b2, list_R A1 A2 AR b1 b2 -> list_R A2 A1 (sym_rel AR) b2 b1.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (list_R_rect A1 A2 AR (list_symPred A1 A2 AR) _ _ _ _ bR).
- exact: (nil_R A2 A1 (sym_rel AR)).
- move=> a1 a2 ar l1 l2 lr IH. 
exact: (cons_R A2 A1 (sym_rel AR) a2 a1 ar l2 l1 (list_sym A1 A2 AR _ _ lr)).
Defined.

Notation list_symKPred := (fun A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : list_R A1 A2 AR b1 b2) => list_sym A2 A1 (sym_rel AR) b2 b1 (list_sym A1 A2 AR b1 b2 bR) = bR).
Definition list_symK :
  forall A1 A2 (AR: A1 -> A2 -> Type) b1 b2 (bR : list_R A1 A2 AR b1 b2), list_sym A2 A1 (sym_rel AR) b2 b1 (list_sym A1 A2 AR b1 b2 bR) = bR.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun b1 b2 bR=> _).
refine (list_R_ind A1 A2 AR (list_symKPred A1 A2 AR) _ _ b1 b2 bR).
- exact: eq_refl.
- move=> a1 a2 ar l1 l2 lr IH.
  cbn delta beta iota.
  rewrite IH.
  exact: eq_refl.
Defined.

Definition Prod (A B : Type) := prod A B.
Elpi derive.param2 prod.

Notation prod_symPred := (fun A1 A2 (AR: A1 -> A2 -> Type) B1 B2 (BR : B1 -> B2 -> Type) b1 b2 (bR : prod_R A1 A2 AR B1 B2 BR b1 b2) => prod_R A2 A1 (sym_rel AR) B2 B1 (sym_rel BR) b2 b1).
Definition prod_sym : forall A1 A2 (AR: A1 -> A2 -> Type) B1 B2 (BR: B1 -> B2 -> Type) b1 b2, prod_R A1 A2 AR B1 B2 BR b1 b2 -> prod_R A2 A1 (sym_rel AR) B2 B1 (sym_rel BR) b2 b1.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun B1 B2 BR=> _).
refine (fun b1 b2 bR=> _).
refine (prod_R_rect A1 A2 AR B1 B2 BR (prod_symPred A1 A2 AR B1 B2 BR) _ _ _ bR).
- move=> a1 a2 ar b b' br. exact: (pair_R A2 A1 (sym_rel AR) B2 B1 (sym_rel BR) a2 a1 ar b' b br).
Defined.

Notation prod_symKPred := (fun A1 A2 (AR: A1 -> A2 -> Type) B1 B2 BR b1 b2 (bR : prod_R A1 A2 AR B1 B2 BR b1 b2) => prod_sym A2 A1 (sym_rel AR) B2 B1 (sym_rel BR) b2 b1 (prod_sym A1 A2 AR B1 B2 BR b1 b2 bR) = bR).
Definition prod_symK :
  forall A1 A2 (AR: A1 -> A2 -> Type) B1 B2 (BR : B1 -> B2 -> Type) b1 b2 (bR : prod_R A1 A2 AR B1 B2 BR b1 b2), prod_sym A2 A1 (sym_rel AR) B2 B1 (sym_rel BR) b2 b1 (prod_sym A1 A2 AR B1 B2 BR b1 b2 bR) = bR.
Proof.
refine (fun A1 A2 AR=> _).
refine (fun B1 B2 BR=> _).
refine (fun b1 b2 bR=> _).
refine (prod_R_ind A1 A2 AR B1 B2 BR (prod_symKPred A1 A2 AR B1 B2 BR) _ b1 b2 bR).
- move=> a1 a2 ar b b' br.
exact: eq_refl.
Defined.

