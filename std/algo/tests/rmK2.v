Require Import ssreflect.
From Trocq Require Import Trocq.

Require Import HoTTNotations.

Section Trocqlib.
  (* Lemma MereM4 `{Funext} (A B : Type) (R : A -> B -> Type) (map : A -> B) :
  {f : forall x : A, R x (map x) &
    forall (x : A) (y : B) (r : R x y), {e : map x = y & transport (R x) e (f x) = r}} <~>
    {f : forall x : A, R x (map x) & forall (x : A) (y : B) (r : R x y),
(map x; f x) = (y; r)}. *)
End Trocqlib.

Section Preliminary.

  Definition tr {T : Type}{x y : T} (P : T -> Type) (p : x = y) : P x -> P y.
  refine (match p with eq_refl => fun P => P end).
  Defined.

  Definition apd {T : Type}{P : T -> Type} (f : forall x, P x) {x y : T} (p : x = y) : 
    tr _ p (f x) = f y.
  Proof. 
  refine (match p with eq_refl => eq_refl end).
  Defined.

  Lemma tr_concat {T : Type} {x y z : T} (p : x = y) (q : y = z) : tr _ q p = p @ q.
  Proof. 
  move: q.
  refine (match p as p0 in _ = t return forall (q : t = z), tr _ q p0 = p0 @ q with eq_refl => _ end).
  exact (fun q => match q with eq_refl => 1 end).
  Defined.

End Preliminary.

(*Lemma 2.9.6 in the HoTT BooK weakened *)
Lemma L : forall {T : Type}{P Q : T -> Type} {x y : T} (p : x = y) (f : P x -> Q x) (g : P y -> Q y) 
    ,tr (fun x => P x -> Q x) p f = g -> forall x, tr _ p (f x) = g (tr _ p x).
Proof.
move=> T P Q x y p.
case: _ / p.
move=> f g /= -> //. 
Defined.

Section Genthm722.

  Variable A B : Type.
  Variable R : A -> B -> Type.
  (* Variable MR : Map4.Has R. *)
  (* Variable m : A -> B.
  Variable mR : forall x y, m x = y -> R x y. (* 2a *)
  Variable Rm : forall x y, R x y -> m x = y. *)
  Axiom MR : Map4.Has R.
  Definition AR : Param40.Rel A B.
  econstructor.
  apply MR.
  constructor.
  Defined.
  Variable MereR : forall x y (r1 r2 : R x y), r1 = r2.

  Definition F {x : A} {y : B}  (p : map AR x = y) := apd (R_in_map AR x) p.

  Definition inverses_concat_tr : forall x y,
  forall p : map AR x = y,
  R_in_map AR x (map AR x) (map_in_R AR x (map AR x) 1) @ p 
  = R_in_map AR x y (tr _ p (map_in_R AR x (map AR x) 1)).
  Proof. move=> x y p.
  rewrite -tr_concat.
  apply L.
  exact: F.
  Defined.

  (* Definition path_shape : forall x,
  forall p : map AR x = map AR x,
  p = (Rm x (map AR m) (mR x (map AR m) 1))^ @ Rm x (map AR m) (@tr _ _ _ _ p (mR x (map AR m) 1)).
  Proof. *)

  Definition path_shape {x y} : 
  forall p : map AR x = y,
  p = (R_in_map AR x (map AR x) (map_in_R AR x (map AR x) 1))^ @ R_in_map AR x y (tr _ p (map_in_R AR x (map AR x) 1)).
  Proof.
  move=> p.
  rewrite -[LHS](concat_1p p).
  rewrite -[X in X @ p](concat_Vp (R_in_map AR x (map AR x) (map_in_R AR x (map AR x) 1))).
  rewrite concat_pp_p.
  apply ap.
  apply inverses_concat_tr.
  Defined.

  Lemma tr_id : forall (x : A) y (p : map AR x = y), 
    tr (fun y=> R x y) p (map_in_R AR _ _ 1) = (map_in_R AR _ _ p).
  move=> x y p.
  by case : _ / p.
  Defined.

  Require Import Param_lemmas.

  Lemma foo : 
  forall
  a 
b b1 
(e : map AR a = b)
(e1 : b = b1),
R_in_map AR a b1 (map_in_R AR a b1 (e @ e1)) =
R_in_map AR a b (map_in_R AR a b e) @ e1.
Proof.
  move=> a b1 b2 e e1.
  by case: _ / e1.
Defined.
  
(* Lemma foo2 : 
  forall
  a 
b b1 
(e : map AR a = b)
(e1 : b = b1),
R_in_map AR a b (map_in_R AR a b e) =
(R_in_map AR a b (map_in_R AR a b e))^.
Proof.
  move=> a b1 b2 e e1.
  by case: _ / e1.
Defined. *)

(* Search inverse concat.
  Definition distr_inv_concat :
    forall {x y : A} (p : x = y) {z : A} (q : y = z) →
    (p @ q)^ = q^ @ p^
  distributive-inv-concat refl refl = refl *)

  Definition left_transpose_eq_concat : forall
    {x y : A} (p : x = y) {z : A} (q : y = z) (r : x = z),
    p @ q = r -> q = p^ @ r.
  Proof.
  move=> x y p.
  case : _ / p => /= z q r.
  by rewrite !concat_1p. 
  Defined.

  Definition RmmRK : forall a b (e : map AR a = b), R_in_map AR _ _ (map_in_R AR _ _ e) = e.
  Proof.
  move=> a b.
  move=> e.
  rewrite [RHS](path_shape e).
  rewrite tr_id.
  rewrite /R_in_map /map_in_R /=.
  set p := R_in_map AR a b _.
  set q := R_in_map AR _ _ _.
  apply left_transpose_eq_concat.
  rewrite -[X in _ @ X](inv_V).
  rewrite -eq_trans_sym_distr.
  Search concat inverse.

  case: _ / e.
  set q1 := R_in_map AR _ _ _.
  move: q1=> q1.
  case : _ / q1.
  set q2 := R_in_map AR _ _ _.
  set q3 := R_in_map AR _ _ _.
  Check (moveL_1V ((R_in_map PR a b (map_in_R PR a b e))^ @ 1) (R_in_map PR a b (map_in_R PR a b e)) _).



rewrite (
            inverse2
              ((concat_p1 (R_in_map AR x x' xR)^)^ @
                (moveL_1V ((R_in_map AR x x' xR)^ @ 1) (R_in_map AR x x' yR) H))).
rewrite ((inv_V (R_in_map AR x x' yR))).
rewrite ((R_in_mapK AR x x' yR)).

  rewrite tr_concat.
  eapply (map_ind PR a).
  eapply (ind_map PR a _ (map_in_R PR _ _ e)).
  2: apply map_in_R. 2: exact: eq_refl.
  case: _ / e.
  move: 1.
  move=> e.
  Search inverse.
  rewrite -{3}(inv_V (Rm a (m a) (mR a (m a) 1))).
  rewrite -eq_trans_sym_distr.
  Search inverse concat.
  Search "move".
  rewrite moveR_pM.
  rewrite -inverses_concat_tr /= concat_1p //.
  Search concat 1.
  rewrite concat_1p //.
  elim.
  Lemma tr_id : forall (x : A) (p : m x = m x), tr (fun y=> R x y) p (mR x (m x) 1) = (mR x (m x) 1).
  Proof. move=> x p; apply MereR. Qed.

  Definition UIP_MA {x y : A} (p q : m x = m y): p = q.
  Proof.
  move: q.
  refine (match p as p0 return forall q, p0 = q with eq_refl => _ end).
  move=> q.
  rewrite (path_shape x 1) /=.
  rewrite (path_shape x q).
  (* rewrite -uniqr. *)
  by rewrite tr_id.
  Defined.

  Section inj.
    Definition injective {A B : Type} (f : A -> B) := forall x y, f x = f y -> x = y.
    Hypothesis m_inj : injective m. 
    
    Lemma ap_inj {C D : Type} (f : C -> D) (inj_f : injective f) : forall x y, injective (@f_equal _ _ f x y).
    Proof.
    move=> x y p1 p2.
    dependent destruction p1.
    dependent destruction p2.
    move=> _ ; exact: eq_refl.
    Defined.
    Print JMeq_refl.

    Definition UIP_A {x y : A} (p q : x = y) : p = q.
    Proof. 
      set mp := @f_equal _ _ m _ _ p.
      set mq := @f_equal _ _ m _ _ q.
      have : mp = mq. by apply UIP_MA.
      by apply: ap_inj.
    Defined.

  End inj.

  Section surj.

    Definition fiber {C D : Type} (f : C -> D) (d : D) := { c & f c = d}.
    Definition isContr (A : Type) := { t & forall t1 : A, t = t1}.
    Definition isProp (A : Type) := forall (x y : A), isContr(x = y).
    Definition surjection {C D : Type} (f : C -> D) := forall y, isProp (fiber f y).
    Hypothesis m_surj : surjection m.

    Lemma UIP_B : forall (x y : B) (p q : x = y), p = q.
    Proof.
    move=> x y.
    have := m_surj x.
    Abort.

  End surj.
  Section surj2.

    Hypothesis comap : B -> A.
    Hypothesis corefl : forall b, R (comap b) b.
    
    Lemma UIP_B : forall (x y : B) (p q : x = y), p = q.
    Proof.
    move=> x y.
    have := (Rm _ _ (corefl x)).
    have := (Rm _ _ (corefl y)).
    elim.
    elim.
    apply UIP_MA.
    Qed.

  End surj2.

End Genthm722.

Section thm722.

    Variable A : Type.
    Variable R : A -> A -> Type.
    Variable rrefl : forall x, R x x. (* 2a *)
    Variable imp : forall x y, R x y -> x = y.  (* 2b *)
    Variable mereR : forall x y (r1 r2 : R x y), r1 = r2.
    Variable M4 : forall x (r1 r2 : {y & R x y} ), r1 = r2.

    Lemma uip_a (x y : A) (p q : x = y) : p = q.
    Proof. 
    apply (UIP_MA A A R (@id A) rrefl imp). 
    by move=> e ?; apply mereR.
    Qed.

End thm722.

