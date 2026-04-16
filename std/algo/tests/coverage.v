(* Inductive False : Set :=. *)

Inductive Unit : Set := 
| TT : Unit.

Inductive Bool : Set := 
| Falseb 
| Trueb.

Inductive Wrap : Set :=
| KWrap1 : Unit -> Wrap.

Inductive WrapMore : Set :=
| KWrap : Unit -> Bool -> WrapMore
| KWrapWrap : Wrap -> WrapMore
| F : Unit -> Unit -> Unit -> WrapMore.

Inductive Nat : Set :=
| O' 
| S' : Nat -> Nat.

Inductive Box (A : Type) : Type :=
| B : A -> Box A.

Inductive Option (A : Type) : Type :=
| None' : Option A 
| Some' : A -> Option A.

Inductive Prod (A B : Type) : Type :=
| PR : A -> B -> Prod A B. 

Inductive ThreeTypes (A B C : Type) :=
| C1 : A -> ThreeTypes A B C
| C2 : B -> ThreeTypes A B C
| C3 : C -> ThreeTypes A B C.

Inductive List (A : Type) : Type :=
| Nil : List A 
| Cons : A -> List A -> List A.

Inductive issue : nat -> Type := 
| K : forall n, issue n -> issue (S (S n))
| K2 : forall n, issue n.

Inductive natR : nat -> nat -> Type :=
| OR : natR O O
| SR : forall n1 n2 (nr : natR n1 n2), natR (S n1) (S n2).

Inductive I (n : nat) : nat -> Type :=
| natrefl : I n n.

From elpi Require Import elpi.
(* From elpi.apps Require Import derive.std.

Inductive funny (A : Type) : A -> Type := Kf (a : A) : funny a.

Elpi derive.map funny.
 *)

From Trocq Require Import Database Rel44.
Require Import ssreflect.
Unset Universe Minimization ToSet.

Elpi derive nat.
Elpi derive.param2 issue.

Definition m : forall n1 n2 (r : nat_R n1 n2), issue n1 -> issue n2.
  refine (fun n1 n2 r =>
    match nat_Rm n1 n2 r with
    | eq_refl => _
    end).
  refine ((fix rec n1 (x : issue n1) {struct x} : issue (nat_mymap n1) :=
        match x with
        | K n rn => K (nat_mymap n) (rec n rn)
        | K2 n => K2 (nat_mymap n)
        end) n1).
Defined. 

(* Definition m : forall n1 n2 (r : nat_R n1 n2), issue n1 -> issue n2.
  refine ((fix rec n1 n2 (r : nat_R n1 n2) (x : issue n1) {struct x} : issue n2 :=
        match x in issue i return i = n1 -> _ with
        | K n rn => _
        | K2 n => _
        end (eq_refl n1))).
    refine match nat_Rm n1 n2 r with
    | eq_refl => _
    end.
    refine (fun idxE => match idxE with eq_refl _ => _ end).
    have := K (nat_mymap n).

          refine (fun n1 n2 r =>
    match nat_Rm n1 n2 r with
    | eq_refl => _
    end).

Defined. *)

From Trocq Require Import Param_lemmas Stdlib.
Check ind_mapP.
Check ind_map.

(* Definition nat_injections21red n1 n2 : S n1 = S n2 -> n1 = n2 *)
  (* := nat_injections21 n1 n2. *)
Check nat_injK21.
About nat_injK21.
Print nat_injK21.
Check nat_injections21.
Require Import HoTTNotations.

Definition predn n := if n is S n then n else 0.

Definition inj k m n (e : m = n) :
  nat_getk_S1 k m
=
  nat_getk_S1 k n.
refine 
  (match m, n return m = n -> _ with
  | S m, S n => fun e : S m = S n => _
  | O, O => fun e => _
  | _, _ => _
  end e).
  all: try by [].
  by apply: nat_injections21.
Defined.


Definition pnk {k n m} : S n = m -> S (nat_getk_S1 k m) = m.
by move<-.
Defined.

Lemma apSproj2 : forall k pn1 n1 n2 (e : n1 = n2) 
  (dn1 : S pn1 = n1) ,
  (* ap S (ap (nat_getK_S1 n1 n2 e)) = e. *)
  ap S (inj k _ _ e) = (pnk dn1 @ e @ (pnk (dn1 @ e))^).
move=> k n1 n2 pn1 e.
case: _ / e => /=. case: _ /. simpl.
by [].
Defined.

Lemma injE k m n (e : S m = S n) :
  inj k _ _ e = nat_injections21 _ _ e.
reflexivity.
Defined. 

Lemma tr_concat {T : Type} {x y z : T} (p : x = y) (q : y = z) : transport _ q p = p @ q.
Proof. 
(* by destruct q.
Defined. *)
move: q.
refine (match p as p0 in _ = t return forall (q : t = z), transport _ q p0 = p0 @ q with eq_refl => _ end).
exact (fun q => match q with eq_refl => 1 end).
Defined.


Lemma tr_concat2 {T : Type} {x y z : T} (p : y = x) (q : y = z) : transport (fun x => @eq _ x z) p q = p^ @ q.
Proof.
case: _ / p.
by rewrite concat_1p.
Defined.

Lemma pred1 : forall {n1 n2 k} (e1 e2 : S n1 = n2), @pnk k _ _ e1 = @pnk k _ _ e2.
Proof.
rewrite /pnk/eq_ind/=.
move=> n1 n2 k.
case: _ /.
Abort.

Elpi derive nat.
Check nat_mR.

(* Lemma apSproj : forall n1 n2 (e : S n1 = S n2), 
  (* ap S (ap (nat_getK_S1 n1 n2 e)) = e. *)
  ap S (nat_injections21 _ _ e) = e. *)
(*
move=> n1.
have -> : n1 = nat_mymap n1. by admit.
move=> n2 e.
have e2 : (nat_mymap (S n1)) = (S n2). by rewrite -e.
have := nat_mR _ _ e2.
move=> n2.
move=> e. 
have := (nat_mR _ _ e). 
have -> : S n1 = nat_mymap (S n1).
move=> n1 n2 e.
rewrite -injE.
(* Set Printing All.
Check apSproj2. *)
rewrite (apSproj2 n1 n1).
rewrite concat_1p.
Search inverse.
apply moveR_pM.
rewrite inv_V.
(* rewrite /pnk/eq_ind.  *)
rewrite -tr_concat.
Check (pnk e).
move: e.
move: (S n2).
Abort. *)
(* Admitted. *)

(* Lemma apSproj3 : forall k pn1 n1 n2 (e e2 : n1 = n2) 
  (dn1 : S pn1 = n1) ,
  (* ap S (ap (nat_getK_S1 n1 n2 e)) = e. *)
  ap S (inj k _ _ e) = (pnk dn1 @ e @ (pnk (dn1 @ e2))^).
move=> k n1 n2 pn1 e e2.
case: _ / e2 => /=. case: _ /. simpl.
by [].
Defined. *)

Print nat_injections21.
Print nat_getk_S1.

Definition RmmRK {A A' : Type} (AR : Param40.Rel A A'): 
  forall a b (e : map AR a = b), R_in_map AR _ _ (map_in_R AR _ _ e) = e.
Admitted.

Definition nat_RmmRK : 
  forall a b (e : nat_mymap a = b), nat_Rm _ _ (nat_mR _ _ e) = e.
Admitted.

Lemma maps_id {U : Type} {R : U -> U -> Type} (AR : Map4.Has R) (r0 : forall a, R a a):
  forall a, Map4.map R AR a = a.
Proof.
move=> a.
apply (Map4.R_in_map R AR _ _ (r0 a)).
Defined.

Lemma maps_idp {U : Type} (AR : Param40.Rel U U) (r0 : forall a, (Param40.R _ _ AR) a a):
  forall a, map AR a = a.
Proof.
move=> a.
by apply (R_in_map AR _ _ (r0 a)).
Defined.

Definition nat_R' : nat -> nat -> Prop.
refine (fun n1 n2 => 
match n1 with 
| O => match n2 with O => True 
        | S _ => False end 
| S x => match n2 with O => False | S y => x = y end end). 
Defined.

Fixpoint nat_refl : forall n, nat_R n n.
Proof.
case => [|n'].
constructor.
exact: S_R _ _ (nat_refl n').
Defined.

Lemma nat_mymapP n : nat_mymap n = n.
Proof.
apply nat_Rm.
apply nat_refl.
Defined.

Definition good_mR : forall n1 n2, n1 = n2 -> nat_R n1 n2.
- move=> a b /= e. apply nat_mR. 
refine (transport _ e _). apply nat_mymapP.
Show Proof.
Defined.

Definition good_Rm : forall n1 n2, nat_R n1 n2 -> n1 = n2.
Proof.
- move=> a b r.
  rewrite /=.
  refine ( (nat_mymapP a)^ @ _).
  (* have H := nat_Rm _ _ r.
  refine (transport (fun x => ) (nat_mymapP a)^ (nat_Rm _ _ r)). *)
  by apply nat_Rm.
Defined.

Lemma good_rel : Param40.Rel nat nat.
unshelve econstructor.
+ apply nat_R.
+ unshelve econstructor.
- exact: (fun x => x).
- move=> a b /= e. apply nat_mR. 
refine (transport _ e _). apply nat_mymapP.
- move=> a b r.
  rewrite /=.
  refine (transport (fun x => x = b) (nat_mymapP a) _).
  by apply nat_Rm.
- move=> a b r.
  rewrite /=. 
  rewrite tr_concat.
  rewrite tr_concat2.
  rewrite -concat_pp_p.
  rewrite concat_pV.
  rewrite /=.
  rewrite concat_1p.
  apply nat_mRRmK.
+ constructor. 
Defined.

Lemma no_conf {U A' : Type} (AR : Param40.Rel U A') a a'
  (P : map AR a = a' -> Type) 
  (PH : forall ar, P (R_in_map AR _ _ ar))
  :
  forall e, P e .
Proof.
move=> e.
rewrite -(RmmRK AR _ _ e).
apply PH.
Defined.

Definition f : forall n1 n2, nat_R n1 n2 -> nat_R' n1 n2.
move=> n1 n2; case=> [//| x y xr] /=.
by apply good_Rm.
(* rewrite -(nat_mymapP x).
by apply nat_Rm.  *)
Defined.

Definition g : forall n1 n2, nat_R' n1 n2 -> nat_R n1 n2.
move=> n1 n2.
case: n1 n2=> [|n'] [|n2] //=.
- move=> r; exact: O_R.
- move=> /(ap S). apply good_mR. 
(* rewrite -[X in X = S n2](nat_mymapP). apply nat_mR. *)
Defined.

Search nat_injections21.


Lemma apeqf : forall A B (f : A -> B) x y (p: x = y),
  bcongr.eq_f A B f x y p = ap f p.
Proof.
  move=> A B f x y p.
  by case: _ / p.
Defined.

(* Elpi derive list.
Search list_injections21.
Check list_injK21. *)
Lemma natRR : forall n1 n2, nat_R n1 n2 <->> nat_R' n1 n2.
Proof.
unshelve eexists.
exact: f.
unshelve eexists.
exact: g.
move=> r.
elim: r=> [//|n' m' r' IHn] /=.
rewrite /good_mR/good_Rm.
rewrite tr_concat.
rewrite /=.
apply ap.
rewrite -/(nat_mymap).
rewrite /nat_mymapP/=.
rewrite apeqf/=.
rewrite -/(nat_mymap).
set P := nat_Rm _ _ _.
Search ap concat.
rewrite ap_pp.
rewrite -concat_pp_p.
rewrite -ap_pp.
rewrite concat_pV.
Search nat_injections21.
rewrite /=.
rewrite concat_1p.
rewrite -[(ap S _)]concat_p1.
rewrite nat_injK21.
rewrite nat_mRRmK.
done.
Defined.
Search (_ <->> _).

Lemma fogK :
forall n1 n2,
forall x : nat_R' n1 n2, f n1 n2 (g n1 n2 x) = x.
Proof.
elim => [|n1' IHn'] [|n2] //.
- by case.
- move=> e. 
  rewrite /f/nat_R_ind. 
  rewrite /g. 
  move: e=> /= e. 
  case: _ / e.
  simpl.
  (* done.
  nat_R_ind. *)
  (* rewrite /good_mR/good_Rm. *)
  (* rewrite tr_concat. *)
  rewrite /=.
  rewrite -/(nat_mymap).
  rewrite /good_Rm.
  rewrite nat_RmmRK.
  rewrite /transport/eq_rect_r/=.
  rewrite /nat_mymapP/=.
  rewrite apeqf/=.
  rewrite nat_injK21.
  by rewrite concat_Vp.
Defined.

Lemma natRR' : forall n1 n2, nat_R' n1 n2 <->> nat_R n1 n2.
Proof.
unshelve eexists.
exact: g.
unshelve eexists.
exact: f.
exact: fogK.
Defined.

Lemma very_good_rel : Param40.Rel nat nat.
unshelve econstructor.
+ apply nat_R'.
+ apply (eq_Map4 natRR'). apply nat_map4.
+ constructor.
Defined.

Lemma very_good_ref : Param40.Rel nat nat.
unshelve econstructor.
+ apply nat_R'.
+ unshelve econstructor.
- exact: id.
- move=> a b e. 
  by have /f @H := good_mR a b e.
- by move=> a b /g e; apply good_Rm. 
- move=> a b r /=. 
  rewrite /good_mR /good_Rm /nat_mymapP/=.
  rewrite tr_concat /id.
  rewrite -concat_pp_p.
  rewrite concat_pV concat_1p.
  rewrite nat_mRRmK.
  by rewrite fogK.
+ constructor.
Defined.

(* Lemma maps_idrm {U : Type} (AR : Param40.Rel U U) (r0 : forall a, (Param40.R _ _ AR) a a):
  forall a b, map AR a = a.
Proof.
move=> a.
by apply (R_in_map AR _ _ (r0 a)).
Defined.

Check @transport. *)
(* Lemma no_confid {U : Type} (AR : Param40.Rel U U) a a' (r0 : forall a2, (Param40.R _ _ AR) a2 a2)
  (P : a = a' -> Type) 
  (PH : forall (ar: AR a a'), P (@transport _ (fun b => b = a') _ _  (maps_idp AR r0 a) (R_in_map AR _ _ ar)))
  :
  forall e, P e .
Proof.
have := (maps_idp AR r0 a).
move=> e.
move: PH.
move: (maps_idp AR r0 a).
move=> e2.
case : _ / e2 P. PH.
move=>P PH e.
apply no_conf.
move=> ar.
move: PH.
move: (maps_idp _ _ _).
move=> /(_ ar).
rewrite /=.
rewrite -(RmmRK AR _ _ e).
have := PH.
apply PH.
Defined. *)

Lemma no_conf_nat n1 n2
  (P : nat_mymap n1 = n2 -> Type) 
  (PH : forall ar, P (nat_Rm _ _ ar))
  :
  forall e, P e .
Proof.
move=> e.
rewrite -(nat_RmmRK _ _ e).
apply PH.
Defined.

Lemma nat_good_RmmRK: forall a b (e : a = b), good_Rm _ _ (good_mR _ _ e) = e.
Admitted.

Lemma good_no_conf_nat n1 n2
  (P : n1 = n2 -> Type) 
  (PH : forall ar, P (good_Rm _ _ ar))
  :
  forall e, P e .
Proof.
move=> e.
rewrite -(nat_good_RmmRK _ _ e).
apply PH.
Defined.


Lemma injectS (x y : nat) (P : forall y, (S x) = S y -> Type)
(prf : P x eq_refl) : (forall (e : (S x) = S y), P y e).
Proof.
move=> e.
apply (no_conf very_good_ref).
rewrite /=.
move=> e2.
case: _ / e2.
rewrite /=.
rewrite /R_in_map/=/id.
by rewrite nat_good_RmmRK.
Defined.


 Lemma ap_eq : forall (T U : Type) (f g: T -> U) (H : forall t, f t = g t),
 forall x y,
 forall (p : x = y), (transport (fun x => x = g y) (H x) (transport (fun y => f x = y) (H y) (ap f p))) =  ap g p.
 Proof.
move=> T U f g H x y p.
case: _ / p.
rewrite /=.
rewrite tr_concat.
rewrite tr_concat2.
rewrite concat_1p.
by rewrite concat_Vp.
Defined.

Definition is_Sb n : bool :=
match n with 
| O => false 
| S _ => true end.
 
Lemma ap_eqin {T U : Type} {f g: T -> U} {h : T -> bool} {x y} (H : forall a, is_true (h a) -> f a = g a)
  (p : x = y): 
  forall (H2 : is_true (h x)), (transport (fun x => x = g y) (H x H2) (transport (fun y => f x = y) (H y (transport (fun x => is_true (h x)) p H2)) (ap f p))) =  ap g p.
 Proof.
move=> H1.
rewrite tr_concat.
rewrite tr_concat2.
case: _ / p H1.
move=> /= H1.
rewrite concat_1p /=.
rewrite transport_1.
by rewrite concat_Vp.
Defined.
  
Lemma ap_id {U : Type} {x y : U}  (p : x = y): ap idmap p = p. 
Proof. by case: _ /p. Defined.
  

Lemma tr_tt {U : Type} (P : U -> Type) (x y : U) (p : x = y) (u : unit) :
  transport _ p u = tt. 
Proof. by case: _ / p; case: u. Defined.

Lemma apSproj''' : forall n1 n2 (e : (S n1) = S n2), 
  ap S (nat_injections21 _ _ e) = e.
Proof.
move=> n1 n2 e.
rewrite /nat_injections21 -ap_compose -[RHS]ap_id.
have @H2 : forall t1, is_true (is_Sb t1) -> (fun x => (S (nat_getk_S1 n1 x))) t1 = idmap t1. 
  by move=> [//| t1'] //.
have h : is_true (is_Sb (S n1)) by [].
by rewrite -[RHS](ap_eqin H2 e h).
Defined.

Lemma apSproj : forall n1 n2 (e : (S n1) = S n2), 
  ap S (nat_injections21 _ _ e) = e.
move=> n1 n2.
by refine (injectS n1 n2 (fun (n2 : nat) (e : S n1 = S n2)=> ap S (nat_injections21 n1 n2 e) = e) _).
Defined.

(* Fixpoint mR 
  n1 n2 (r : nat_R n1 n2) (a : issue n1) (b : issue n2) {struct n1}: m n1 n2 r a = b -> issue_R n1 n2 r a b.
  move: r.
(* move: n1 n2 r a b. *)

  refine ( 
  match a as a0 in issue n1' return n1 = n1' -> forall (r : nat_R n1' n2), m n1' n2 r a0 = b -> issue_R n1' n2 r a0 b with
  | K n rn => _
  | K2 n => _
  end eq_refl).
  (* move=> e. *)
  simpl.
  (* move: (S (S (nat_mymap n))). *)

  
  refine (
  match b as bx in issue w
  return 
    forall e1 : n2 = w,
    forall e : n1 = S (S n),
    forall (r : nat_R (S (S n)) w),
    m (S (S n)) w r _ = transport _ e1^ bx ->
    (*K (nat_mymap n) (m n rn) = (match e in _ = ttt return issue ttt with eq_refl => bx end) ->*)
    issue_R (S (S n)) w r (K n rn) (transport _ (eq_sym e1) bx)
  with
  | K m' rm => _
  | K2 m' => _
  end (eq_refl _)).
  move=> e1 e2 r H.
  eapply transport .
  2: apply K_R. _ _ _.

  move=> e1 e2.
  (* apply transport (fun t => issue_R _ _ _ (K n rn) (K m rm))  *)
  apply K_R.
  (* move=> e. *)
  have <- : ap S (ap S (nat_injections21 _ _ (nat_injections21 _ _ e))) = e.  
    by rewrite 2!apSproj /=.
  
  move: (nat_injections21 _ _ _) => /= e' {e}.
  case: _ / e' in rm * => /=.
   
  hnf.
  rewrite /transport/eq_rect_r/=.
  move=> e.
  (* case: _ / => /=. *)
  apply K_R.
  apply mR.
  rewrite /coverage.m.
  have [] := e.
  move=> [].
  move=> [].
  case: _ /.
  (* move=> e1 e2. *)
  apply K_R.
  all: try by []. *)

Fixpoint mR 
  n1 n2 (r : nat_R n1 n2) (a : issue n1) (b : issue n2) {struct n1}: m n1 n2 r a = b -> issue_R n1 n2 r a b.
move: n1 n2 r a b.

(* move => n1 n2 r.
have r' := r.
move : r.
elim (nat_Rm _ _ r')=> {r' n2}. *)
  refine (fun n1 n2 r =>
    (* let r' := nat_mR n1 (nat_mymap n1) (eq_refl _) in *)
    match nat_Rm n1 n2 r in _ = w return 
      forall (r : nat_R n1 w) (a : issue n1) (b : issue w),
        m n1 w r a = b -> issue_R n1 w r a b
    with
    | eq_refl => fun rx => _
    end r).
rewrite /m.

(* elim/(ind_map nat_rel40): (nat_Rm) _ /_.  *)

have :=(ind_map nat_rel40 n1 _ _ _ rx). 
rewrite [in R_in_map _]/nat_rel40/nat_map4/R_in_map /=.
move: (nat_Rm n1 (nat_mymap n1) rx) => it.

move=> H.
apply H. clear H.
move=> {it}.
rewrite -[map nat_rel40]/(nat_mymap).
rewrite -[map_in_R nat_rel40]/(nat_mR).
set m := fix rec n (x : issue n) {struct x} := _.

  refine (fun a=> 
  match a with
  | K n rn => _
  | K2 n => _
  end).
  simpl.
  (* move: (S (S (nat_mymap n))). *)

  
  refine (fun b => 
  match b as bx in issue w
  return 
    forall e : S (S (nat_mymap n)) = w,
    K (nat_mymap n) (m n rn) = transport _ (eq_sym e) bx ->
    (*K (nat_mymap n) (m n rn) = (match e in _ = ttt return issue ttt with eq_refl => bx end) ->*)
    issue_R (S (S n)) (S (S (nat_mymap n))) (S_R (S n) (S (nat_mymap n)) (S_R n (nat_mymap n) (nat_mR n (nat_mymap n) eq_refl))) (K n rn) (transport _ (eq_sym e) bx)
  with
  | K m rm => _
  | K2 m => _
  end (eq_refl _)).
  move=> e H.
  (* apply transport (fun t => issue_R _ _ _ (K n rn) (K m rm))  *)
  (* apply K_R. *)
  (* move=> e. *)
  have <- : ap S (ap S (nat_injections21 _ _ (nat_injections21 _ _ e))) = e.  
    by rewrite 2!apSproj /=.
  move: (nat_injections21 _ _ _) => /= e' {e H}.
  case: _ / e' in rm * => /=.
  hnf.
  rewrite /transport/eq_rect_r/=.
  apply K_R.
  apply mR.
  rewrite /coverage.m.
  rewrite nat_RmmRK /=.
  (* this id has to be recovered from IH *)
Abort.




(*
Plan #1:

- modify standard derive.map to map indexes as well 


  refine ((fix rec n1 (x : issue n1) {struct x} : issue (nat_mymap n1) :=
        match x with
        | K n rn => K (nat_mymap n) (rec n rn)
        | K2 n => K2 (nat_mymap n)
        end)).

- new derivation to unify related indexes

  forall n1 n2 (r : nat_R n1 n2), P n1 n2 -> P n1 (nat_map n1)

  refine (fun n1 n2 r =>
    match nat_Rm n1 n2 r with
    | eq_refl => _
    end).


*)

Definition issue_mymap : forall n1 n2 (r : nat_R n1 n2), issue n1 -> issue n2.
  refine (
  fix rec n1 n2 (r : nat_R n1 n2) (x : issue n1) {struct x} : issue n2 :=
    match nat_Rm n1 n2 r with
    | eq_refl =>
        match x with
        | K n rn => K (nat_mymap n) _
        | K2 n => K2 (nat_mymap n)
        end
    end).
  refine (rec n _ _ rn).
  apply nat_mR.
  refine eq_refl.
Defined.

Fail Elpi derive.mymap issue.
Print issue_mymap.

Definition Rm : forall n1 n2, natR n1 n2 -> nat_mymap n1 = n2. Admitted.
Definition mR : forall n1 n2,  nat_mymap n1 = n2 -> natR n1 n2. Admitted.
Definition mRRmK : forall n1 n2 (r : natR n1 n2), mR _ _ (Rm _ _ r) = r. Admitted.

Definition issuemap : forall n1 n2 (nr : natR n1 n2), issue n1 -> issue n2.
Fail refine (fun n1 n2 nR x => match x in issue w return w = n1 -> _  with K n => fun e => _ | K2 n => fun _ => K2 n2 end (eq_refl n1)).

Abort.