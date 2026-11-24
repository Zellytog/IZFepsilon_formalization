(** * The Sεt-tripos (Definition 29, Proposition 30)

    The definition of tripos we follow is Pitts' ("Tripos theory in
    retrospect", Def. 4.3): a functor to Heyting pre-algebras on a
    category with finite products, with a left adjoint to reindexing along
    diagonals, adjoints on both sides along projections (with the
    Beck–Chevalley condition) and weak power objects.

    For Sεt, the fibre over x consists of the compatible predicates
    p : V → Φ, preordered by p ⊑ q ≜ ∃e. ∀α. e ⊩ ⟦α ε x⟧ ∧ p(α) ⩽ q(α). *)

From Stdlib Require Import Setoid Morphisms.
From IZFe Require Import Frame VE Set_eps Cartesian.

(** ** Heyting pre-algebras *)

Record preheyting := {
  hcar :> Type;
  hle : hcar -> hcar -> Prop;
  hle_refl : forall p, hle p p;
  hle_trans : forall p q r, hle p q -> hle q r -> hle p r;
  htop : hcar; hbot : hcar;
  hand : hcar -> hcar -> hcar; hor : hcar -> hcar -> hcar; himp : hcar -> hcar -> hcar;
  htop_spec : forall p, hle p htop;
  hbot_spec : forall p, hle hbot p;
  hand_spec : forall r p q, hle r (hand p q) <-> hle r p /\ hle r q;
  hor_spec : forall p q r, hle (hor p q) r <-> hle p r /\ hle q r;
  himp_spec : forall r p q, hle (hand r p) q <-> hle r (himp p q)
}.

Arguments hle {p} _ _ : rename.
Arguments htop {p} : rename. Arguments hbot {p} : rename.
Arguments hand {p} _ _ : rename. Arguments hor {p} _ _ : rename. Arguments himp {p} _ _ : rename.

Definition hiso {H : preheyting} (a b : H) : Prop := hle a b /\ hle b a.

(** ** Triposes over a cartesian category *)

Section TriposDef.

Context (C : category) (K : cartesian C).

Local Notation "g ∘ f" := (ccomp g f) (at level 40, left associativity).
Local Notation pr1 := (pr1 C K).
Local Notation pr2 := (pr2 C K).
Local Notation pairing := (pairing C K _ _ _).
Local Notation prod := (prod C K).

Definition diag (x : ob C) : hom C x (prod x x) := pairing (cid x) (cid x).
Definition fxid {G' G X : ob C} (f : hom C G' G) : hom C (prod G' X) (prod G X) := pairing (f ∘ pr1 G' X) (pr2 G' X).
Definition idxf {X Y P : ob C} (f : hom C Y P) : hom C (prod X Y) (prod X P) := pairing (pr1 X Y) (f ∘ pr2 X Y).

Record tripos := {
  fib : ob C -> preheyting;
  reidx : forall {x y}, hom C x y -> fib y -> fib x;
  reidx_mono : forall x y (f : hom C x y) p q, hle p q -> hle (reidx f p) (reidx f q);
  reidx_top : forall x y (f : hom C x y), hiso (reidx f htop) htop;
  reidx_bot : forall x y (f : hom C x y), hiso (reidx f hbot) hbot;
  reidx_and : forall x y (f : hom C x y) p q, hiso (reidx f (hand p q)) (hand (reidx f p) (reidx f q));
  reidx_or : forall x y (f : hom C x y) p q, hiso (reidx f (hor p q)) (hor (reidx f p) (reidx f q));
  reidx_imp : forall x y (f : hom C x y) p q, hiso (reidx f (himp p q)) (himp (reidx f p) (reidx f q));
  reidx_proper : forall x y (f g : hom C x y) p, heq f g -> hiso (reidx f p) (reidx g p);
  reidx_id : forall x p, hiso (reidx (cid x) p) p;
  reidx_comp : forall x y z (f : hom C x y) (g : hom C y z) p, hiso (reidx (g ∘ f) p) (reidx f (reidx g p));
  teqd : forall x, fib x -> fib (prod x x);
  teqd_adj : forall x (p : fib x) r, hle (teqd x p) r <-> hle p (reidx (diag x) r);
  tex : forall G X, fib (prod G X) -> fib G;
  tall : forall G X, fib (prod G X) -> fib G;
  tex_adj : forall G X (r : fib (prod G X)) p, hle (tex G X r) p <-> hle r (reidx (pr1 G X) p);
  tall_adj : forall G X (r : fib (prod G X)) p, hle p (tall G X r) <-> hle (reidx (pr1 G X) p) r;
  bc_ex : forall G' G X (f : hom C G' G) r, hiso (reidx f (tex G X r)) (tex G' X (reidx (fxid f) r));
  bc_all : forall G' G X (f : hom C G' G) r, hiso (reidx f (tall G X r)) (tall G' X (reidx (fxid f) r));
  tpow : ob C -> ob C;
  tmem : forall X, fib (prod X (tpow X));
  tpow_spec : forall X Y (φ : fib (prod X Y)), exists f : hom C Y (tpow X), hiso φ (reidx (idxf f) (tmem X))
}.

End TriposDef.

(** ** The fibres of Sεt *)

Section Fibres.

Context (F : frame).

Local Notation V := (@V F).

#[local] Instance teq_equiv3 : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.

Record tpred := { tp :> V -> pcar F; tp_proper : Pproper F tp }.

Definition tle (x : V) (p q : tpred) : Prop := exists e, forall α, fand (eps α x) (p α) —[e]→ q α.

Lemma tle_refl x p : tle x p p.
Proof. exists e_snd. intros; apply f_snd. Qed.

Lemma tle_trans x p q r : tle x p q -> tle x q r -> tle x p r.
Proof.
  intros [e1 H1] [e2 H2]. exists (e_comp (e_pair e_fst e1) e2). intros α.
  eapply f_comp; [apply n_pair; [apply f_fst|apply H1]|apply H2].
Qed.

Definition cst (φ : pcar F) : tpred := {| tp := fun _ => φ; tp_proper := fun _ _ _ => peq_refl φ |}.

Program Definition tand (p q : tpred) : tpred := {| tp := fun α => fand (p α) (q α) |}.
Next Obligation. intros α α' E. apply fand_proper; apply tp_proper, E. Qed.
Program Definition tor (p q : tpred) : tpred := {| tp := fun α => for_ (p α) (q α) |}.
Next Obligation. intros α α' E. apply for_proper; apply tp_proper, E. Qed.
Program Definition timp (p q : tpred) : tpred := {| tp := fun α => fimp (p α) (q α) |}.
Next Obligation. intros α α' E. apply fimp_proper; apply tp_proper, E. Qed.

Definition fibre (x : V) : preheyting.
Proof.
  refine {| hcar := tpred; hle := tle x; hle_refl := tle_refl x; hle_trans := tle_trans x;
            htop := cst ftop; hbot := cst fbot; hand := tand; hor := tor; himp := timp |}.
  - intros p. exists e_top. intros; apply f_top.
  - intros p. exists (e_comp e_snd e_incl). intros α. eapply f_comp; [apply f_snd|apply f_bot].
  - intros r p q. split.
    + intros [e H]. split; [exists (e_comp e e_fst)|exists (e_comp e e_snd)]; intros α; [eapply n_fst|eapply n_snd]; apply H.
    + intros [[e1 H1] [e2 H2]]. exists (e_pair e1 e2). intros α. apply n_pair; [apply H1|apply H2].
  - intros p q r. split.
    + intros [e H]. split; [exists (e_comp (e_pair e_fst (e_kl e_snd)) e)|exists (e_comp (e_pair e_fst (e_kr e_snd)) e)];
        intros α; (eapply f_comp; [|apply H]); cbn; apply n_pair; [apply f_fst| |apply f_fst|];
        [apply n_orI1, f_snd|apply n_orI2, f_snd].
    + intros [[e1 H1] [e2 H2]]. eexists. intros α. cbn.
      apply (n_orE _ (p α) (q α)); [apply f_snd| |].
      * eapply f_comp; [|apply H1]. apply n_pair; [eapply n_fst, n_wk, f_id|apply n_hyp0].
      * eapply f_comp; [|apply H2]. apply n_pair; [eapply n_fst, n_wk, f_id|apply n_hyp0].
  - intros r p q. split.
    + intros [e H]. eexists. intros α. cbn. apply n_lam. eapply f_comp; [|apply H]. cbn.
      apply n_pair; [eapply n_fst, n_fst, f_id|apply n_pair; [eapply n_snd, n_fst, f_id|apply f_snd]].
    + intros [e H]. eexists. intros α. cbn. eapply n_app; [eapply f_comp; [|apply H]|].
      * apply n_pair; [apply f_fst|eapply n_fst, f_snd].
      * eapply n_snd, f_snd.
Defined.

End Fibres.

(** ** Reindexing: f*(q)(α) ≜ ⋃_β f(α, β) ∧ q(β) *)

Section Reidx.

Context (F : frame).

Local Notation V := (@V F).
Local Notation tpred := (tpred F).
Local Notation tle := (tle F).

#[local] Instance teq_equiv4 : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.
#[local] Existing Instance sheq_equiv.

Program Definition treidx {x y} (f : shom F x y) (q : tpred) : tpred :=
  {| tp := fun α => fex (fun β => fand (f α β) (q β)) |}.
Next Obligation.
  intros α α' E. apply fex_proper. intros β. apply fand_proper; [|reflexivity]. apply (hr_proper F _ _ f); [exact E|reflexivity].
Qed.

Definition tiso x (p q : tpred) := tle x p q /\ tle x q p.

Lemma treidx_mono x y (f : shom F x y) p q : tle y p q -> tle x (treidx f p) (treidx f q).
Proof.
  intros [e H]. destruct (strict_r F f) as [e1 H1]. eexists. intros α. cbn.
  apply (n_exE (fun β => fand (f α β) (p β))); [apply f_snd|]. intros β.
  apply (n_exI (fun β => fand (f α β) (q β)) β). apply n_pair; [eapply n_fst, n_hyp0|].
  eapply f_comp; [|apply H]. apply n_pair; [eapply f_comp; [eapply n_fst, n_hyp0|apply H1]|eapply n_snd, n_hyp0].
Qed.

Lemma treidx_top x y (f : shom F x y) : tiso x (treidx f (cst F ftop)) (cst F ftop).
Proof.
  destruct (total_e F f) as [e1 H1]. split; [exists e_top; intros; apply f_top|].
  eexists. intros α. cbn. apply (n_exE (fun β => f α β)); [eapply f_comp; [apply f_fst|apply H1]|]. intros β.
  apply (n_exI (fun β => fand (f α β) ftop) β). apply n_pair; [apply n_hyp0|apply f_top].
Qed.

Lemma treidx_bot x y (f : shom F x y) : tiso x (treidx f (cst F fbot)) (cst F fbot).
Proof.
  split.
  - eexists. intros α. cbn. apply (n_exE (fun β => fand (f α β) fbot)); [apply f_snd|]. intros β. eapply n_snd, n_hyp0.
  - exists (e_comp e_snd e_incl). intros α. eapply f_comp; [apply f_snd|apply f_bot].
Qed.

Lemma treidx_and x y (f : shom F x y) p q :
  tiso x (treidx f (tand F p q)) (tand F (treidx f p) (treidx f q)).
Proof.
  destruct (func_e F f) as [e1 H1]. split.
  - eexists. intros α. cbn. apply (n_exE (fun β => fand (f α β) (fand (p β) (q β)))); [apply f_snd|]. intros β.
    apply n_pair.
    + apply (n_exI (fun β => fand (f α β) (p β)) β). apply n_pair; [eapply n_fst, n_hyp0|eapply n_fst, n_snd, n_hyp0].
    + apply (n_exI (fun β => fand (f α β) (q β)) β). apply n_pair; [eapply n_fst, n_hyp0|eapply n_snd, n_snd, n_hyp0].
  - eexists. intros α. cbn.
    apply (n_exE (fun β => fand (f α β) (p β))); [eapply n_fst, f_snd|]. intros β.
    apply (n_exE (fun β => fand (f α β) (q β))); [eapply n_snd, n_wk, f_snd|]. intros β'.
    apply (n_exI (fun β => fand (f α β) (fand (p β) (q β))) β). apply n_pair; [eapply n_fst, n_wk, n_hyp0|].
    apply n_pair; [eapply n_snd, n_wk, n_hyp0|].
    apply (n_tr F q (tp_proper F q) β' β); [|eapply n_snd, n_hyp0].
    eapply f_comp; [|apply (H1 α β' β)]. apply n_pair; [eapply n_fst, n_hyp0|eapply n_fst, n_wk, n_hyp0].
Qed.

Lemma treidx_or x y (f : shom F x y) p q :
  tiso x (treidx f (tor F p q)) (tor F (treidx f p) (treidx f q)).
Proof.
  split.
  - eexists. intros α. cbn. apply (n_exE (fun β => fand (f α β) (for_ (p β) (q β)))); [apply f_snd|]. intros β.
    apply (n_orE _ (p β) (q β)); [eapply n_snd, n_hyp0| |].
    + apply n_orI1. apply (n_exI (fun β => fand (f α β) (p β)) β). apply n_pair; [eapply n_fst, n_wk, n_hyp0|apply n_hyp0].
    + apply n_orI2. apply (n_exI (fun β => fand (f α β) (q β)) β). apply n_pair; [eapply n_fst, n_wk, n_hyp0|apply n_hyp0].
  - eexists. intros α. cbn.
    apply (n_orE _ (treidx f p α) (treidx f q α)); [apply f_snd| |].
    + apply (n_exE (fun β => fand (f α β) (p β))); [apply n_hyp0|]. intros β.
      apply (n_exI (fun β => fand (f α β) (for_ (p β) (q β))) β). apply n_pair; [eapply n_fst, n_hyp0|].
      apply n_orI1. eapply n_snd, n_hyp0.
    + apply (n_exE (fun β => fand (f α β) (q β))); [apply n_hyp0|]. intros β.
      apply (n_exI (fun β => fand (f α β) (for_ (p β) (q β))) β). apply n_pair; [eapply n_fst, n_hyp0|].
      apply n_orI2. eapply n_snd, n_hyp0.
Qed.

Lemma treidx_imp x y (f : shom F x y) p q :
  tiso x (treidx f (timp F p q)) (timp F (treidx f p) (treidx f q)).
Proof.
  destruct (func_e F f) as [e1 H1], (total_e F f) as [e2 H2]. split.
  - eexists. intros α. cbn. apply n_lam.
    apply (n_exE (fun β => fand (f α β) (fimp (p β) (q β)))); [eapply n_snd, n_fst, f_id|]. intros β.
    apply (n_exE (fun β => fand (f α β) (p β))); [eapply n_snd, n_wk, f_id|]. intros β'.
    apply (n_exI (fun β => fand (f α β) (q β)) β). apply n_pair; [eapply n_fst, n_wk, n_hyp0|].
    eapply n_app; [eapply n_snd, n_wk, n_hyp0|].
    apply (n_tr F p (tp_proper F p) β' β); [|eapply n_snd, n_hyp0].
    eapply f_comp; [|apply (H1 α β' β)]. apply n_pair; [eapply n_fst, n_hyp0|eapply n_fst, n_wk, n_hyp0].
  - eexists. intros α. cbn.
    apply (n_exE (fun β => f α β)); [eapply f_comp; [apply f_fst|apply H2]|]. intros β.
    apply (n_exI (fun β => fand (f α β) (fimp (p β) (q β))) β). apply n_pair; [apply n_hyp0|].
    apply n_lam.
    apply (n_exE (fun β => fand (f α β) (q β))).
    { eapply n_app; [eapply n_snd, n_wk, n_wk, f_id|].
      apply (n_exI (fun β => fand (f α β) (p β)) β). apply n_pair; [apply n_wk, n_hyp0|apply n_hyp0]. }
    intros β'.
    apply (n_tr F q (tp_proper F q) β' β); [|eapply n_snd, n_hyp0].
    eapply f_comp; [|apply (H1 α β' β)]. apply n_pair; [eapply n_fst, n_hyp0|apply n_wk, n_wk, n_hyp0].
Qed.

Lemma treidx_proper x y (f g : shom F x y) p : sheq F f g -> tiso x (treidx f p) (treidx g p).
Proof.
  assert (M : forall f g : shom F x y, sheq F f g -> tle x (treidx f p) (treidx g p)).
  { intros f0 g0 [[e H] _]. eexists. intros α. cbn.
    apply (n_exE (fun β => fand (f0 α β) (p β))); [apply f_snd|]. intros β.
    apply (n_exI (fun β => fand (g0 α β) (p β)) β). apply n_pair; [|eapply n_snd, n_hyp0].
    eapply f_comp; [eapply n_fst, n_hyp0|apply (H (α, β))]. }
  intros E. split; apply M; [exact E|symmetry; exact E].
Qed.

Lemma treidx_id x p : tiso x (treidx (sid F x) p) p.
Proof.
  split.
  - eexists. intros α. cbn. apply (n_exE (fun β => fand (id_rel F x α β) (p β))); [apply f_snd|]. intros β.
    apply (n_tr F p (tp_proper F p) β α); [apply n_sym; eapply n_snd, n_fst, n_hyp0|eapply n_snd, n_hyp0].
  - eexists. intros α. cbn. apply (n_exI (fun β => fand (id_rel F x α β) (p β)) α).
    apply n_pair; [apply n_pair; [apply f_fst|apply n_refl]|apply f_snd].
Qed.

Lemma treidx_comp x y z (f : shom F x y) (g : shom F y z) p :
  tiso x (treidx (scomp F g f) p) (treidx f (treidx g p)).
Proof.
  split.
  - eexists. intros α. cbn. apply (n_exE (fun γ => fand (comp_rel F g f α γ) (p γ))); [apply f_snd|]. intros γ.
    apply (n_exE (fun β => fand (f α β) (g β γ))); [eapply n_fst, n_hyp0|]. intros β.
    apply (n_exI (fun β => fand (f α β) (treidx g p β)) β). apply n_pair; [eapply n_fst, n_hyp0|].
    apply (n_exI (fun γ => fand (g β γ) (p γ)) γ). apply n_pair; [eapply n_snd, n_hyp0|eapply n_snd, n_wk, n_hyp0].
  - eexists. intros α. cbn. apply (n_exE (fun β => fand (f α β) (treidx g p β))); [apply f_snd|]. intros β.
    apply (n_exE (fun γ => fand (g β γ) (p γ))); [eapply n_snd, n_hyp0|]. intros γ.
    apply (n_exI (fun γ => fand (comp_rel F g f α γ) (p γ)) γ). apply n_pair; [|eapply n_snd, n_hyp0].
    apply (n_exI (fun β => fand (f α β) (g β γ)) β). apply n_pair; [eapply n_fst, n_wk, n_hyp0|eapply n_fst, n_hyp0].
Qed.

End Reidx.

(** ** Projections and pairs: tools *)

Section ProdTools.

Context (F : frame).
Local Notation V := (@V F).
Local Notation tpred := (tpred F).

#[local] Instance teq_equiv5 : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.

Local Notation P1 x y := (prj_rel F x y (fun α β => α)).
Local Notation P2 x y := (prj_rel F x y (fun α β => β)).

Lemma P1_intro x y : exists e, forall z a b, fand (eps z (vprod F x y)) (veq z (kp F a b)) —[e]→ P1 x y z a.
Proof.
  eexists. intros z a b. apply n_pair; [apply f_fst|].
  apply (n_ex2I F _ (fun α β => fand (veq z (kp F α β)) (veq α a)) a b). apply n_pair; [apply f_snd|apply n_refl].
Qed.

Lemma P2_intro x y : exists e, forall z a b, fand (eps z (vprod F x y)) (veq z (kp F a b)) —[e]→ P2 x y z b.
Proof.
  eexists. intros z a b. apply n_pair; [apply f_fst|].
  apply (n_ex2I F _ (fun α β => fand (veq z (kp F α β)) (veq β b)) a b). apply n_pair; [apply f_snd|apply n_refl].
Qed.

Lemma P1_veq x y : exists e, forall z a b u, fand (veq z (kp F a b)) (P1 x y z u) —[e]→ veq a u.
Proof.
  destruct (inj_fst F) as [ei Hi]. eexists. intros z a b u.
  apply (n_ex2E F _ _ (fun α β => fand (veq z (kp F α β)) (veq α u))); [eapply n_snd, f_snd|]. intros a' b'.
  eapply n_trans; [|eapply n_snd, n_hyp0]. eapply f_comp; [|apply (Hi a b a' b')].
  eapply n_trans; [apply n_sym; eapply n_fst, n_wk, n_wk, f_id|eapply n_fst, n_hyp0].
Qed.

Lemma P2_veq x y : exists e, forall z a b u, fand (veq z (kp F a b)) (P2 x y z u) —[e]→ veq b u.
Proof.
  destruct (inj_snd F) as [ei Hi]. eexists. intros z a b u.
  apply (n_ex2E F _ _ (fun α β => fand (veq z (kp F α β)) (veq β u))); [eapply n_snd, f_snd|]. intros a' b'.
  eapply n_trans; [|eapply n_snd, n_hyp0]. eapply f_comp; [|apply (Hi a b a' b')].
  eapply n_trans; [apply n_sym; eapply n_fst, n_wk, n_wk, f_id|eapply n_fst, n_hyp0].
Qed.

Lemma kp_veq_l : exists e, forall a a' b, veq a a' —[e]→ veq (kp F a b) (kp F a' b).
Proof.
  destruct (veq_kp F) as [e He]. eexists. intros a a' b. eapply f_comp; [|apply He]. apply n_pair; [apply f_id|apply n_refl].
Qed.

Lemma kp_veq_r : exists e, forall a b b', veq b b' —[e]→ veq (kp F a b) (kp F a b').
Proof.
  destruct (veq_kp F) as [e He]. eexists. intros a b b'. eapply f_comp; [|apply He]. apply n_pair; [apply n_refl|apply f_id].
Qed.

Lemma kp_intro x y : exists e, forall a b, fand (eps a x) (eps b y) —[e]→ eps (kp F a b) (vprod F x y).
Proof.
  destruct (prod_from F) as [e He]. eexists. intros a b. eapply f_comp; [|apply He].
  apply (n_ex2I F _ (ProdEf F x y (kp F a b)) a b). apply n_pair; [apply n_refl|apply f_id].
Qed.

End ProdTools.

(** ** Quantifiers along projections

    ∃_π(r)(γ) ≜ ⟦γ ε Γ⟧ ∧ ⋃_α (⟦α ε X⟧ ∧ r(⟨γ, α⟩)),
    ∀_π(r)(γ) ≜ ⟦γ ε Γ⟧ ∧ ⋂_α (⟦α ε X⟧ ⊃ r(⟨γ, α⟩)). *)

Section Quant.

Context (F : frame).
Local Notation V := (@V F).
Local Notation tpred := (tpred F).
Local Notation tle := (tle F).

#[local] Instance teq_equiv6 : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.

Local Notation P1 x y := (prj_rel F x y (fun α β => α)).
Local Notation P2 x y := (prj_rel F x y (fun α β => β)).

Lemma kpr_proper (r : tpred) γ : Pproper F (fun α => r (kp F γ α)).
Proof. intros α α' E. apply tp_proper, kp_proper; [reflexivity|exact E]. Qed.

Program Definition texq (G X : V) (r : tpred) : tpred :=
  {| tp := fun γ => fand (eps γ G) (fex (fun α => fand (eps α X) (r (kp F γ α)))) |}.
Next Obligation.
  intros γ γ' E. apply fand_proper; [apply eps_proper; [exact E|reflexivity]|].
  apply fex_proper. intros α. apply fand_proper; [reflexivity|]. apply tp_proper, kp_proper; [exact E|reflexivity].
Qed.

Program Definition tallq (G X : V) (r : tpred) : tpred :=
  {| tp := fun γ => fand (eps γ G) (fall (fun α => fimp (eps α X) (r (kp F γ α)))) |}.
Next Obligation.
  intros γ γ' E. apply fand_proper; [apply eps_proper; [exact E|reflexivity]|].
  apply fall_proper. intros α. apply fimp_proper; [reflexivity|]. apply tp_proper, kp_proper; [exact E|reflexivity].
Qed.

Lemma texq_adj G X (r p : tpred) :
  tle G (texq G X r) p <-> tle (vprod F G X) r (treidx F (spr1 F G X) p).
Proof.
  destruct (prod_to F) as [e1 H1], (P1_intro F G X) as [e2 H2], (P1_veq F G X) as [e3 H3], (kp_intro F G X) as [e4 H4].
  split.
  - intros [e H]. eexists. intros z. cbn.
    apply (n_ex2E F _ _ (ProdEf F G X z)); [eapply f_comp; [apply f_fst|apply H1]|]. intros γ α.
    apply (n_exI (fun u => fand (P1 G X z u) (p u)) γ). apply n_pair.
    + eapply f_comp; [|apply (H2 z γ α)]. apply n_pair; [eapply n_fst, n_wk, n_wk, f_id|eapply n_fst, n_hyp0].
    + eapply f_comp; [|apply H]. cbn. apply n_pair; [eapply n_fst, n_snd, n_hyp0|]. apply n_pair; [eapply n_fst, n_snd, n_hyp0|].
      apply (n_exI (fun α0 => fand (eps α0 X) (r (kp F γ α0))) α). apply n_pair; [eapply n_snd, n_snd, n_hyp0|].
      apply (n_tr F r (tp_proper F r) z (kp F γ α)); [eapply n_fst, n_hyp0|eapply n_snd, n_wk, n_wk, f_id].
  - intros [e K]. eexists. intros γ. cbn.
    apply (n_exE (fun α => fand (eps α X) (r (kp F γ α)))); [eapply n_snd, f_snd|]. intros α.
    apply (n_exE (fun u => fand (P1 G X (kp F γ α) u) (p u))).
    { eapply f_comp; [|apply (K (kp F γ α))]. apply n_pair; [|eapply n_snd, n_hyp0].
      eapply f_comp; [|apply H4]. apply n_pair; [eapply n_fst, n_wk, f_id|eapply n_fst, n_hyp0]. }
    intros u. apply (n_tr F p (tp_proper F p) u γ); [|eapply n_snd, n_hyp0].
    apply n_sym. eapply f_comp; [|apply (H3 (kp F γ α) γ α u)]. apply n_pair; [apply n_refl|eapply n_fst, n_hyp0].
Qed.

Lemma tallq_adj G X (r p : tpred) :
  tle G p (tallq G X r) <-> tle (vprod F G X) (treidx F (spr1 F G X) p) r.
Proof.
  destruct (prod_to F) as [e1 H1], (P1_intro F G X) as [e2 H2], (P1_veq F G X) as [e3 H3], (kp_intro F G X) as [e4 H4],
    (kp_veq_l F) as [e5 H5].
  split.
  - intros [e H]. eexists. intros z. cbn.
    apply (n_exE (fun u => fand (P1 G X z u) (p u))); [apply f_snd|]. intros u.
    apply (n_ex2E F _ _ (ProdEf F G X z)); [eapply f_comp; [eapply n_fst, n_wk, f_id|apply H1]|]. intros γ α.
    apply (n_tr F r (tp_proper F r) (kp F u α) z).
    + apply n_sym. eapply n_trans; [eapply n_fst, n_hyp0|]. eapply f_comp; [|apply H5]. (eapply f_comp; [|apply (H3 z γ α u)]; apply n_pair; [eapply n_fst, n_hyp0|eapply n_fst, n_snd, n_wk, n_wk, f_id]).
    + eapply n_app; [apply (n_inst (fun α0 => fimp (eps α0 X) (r (kp F u α0))) α)|eapply n_snd, n_snd, n_hyp0].
      eapply n_snd. eapply f_comp; [|apply H]. apply n_pair; [|eapply n_snd, n_snd, n_wk, n_wk, f_id].
      apply (n_tr F (fun w => eps w G) (eps_l_proper F G) γ u); [(eapply f_comp; [|apply (H3 z γ α u)]; apply n_pair; [eapply n_fst, n_hyp0|eapply n_fst, n_snd, n_wk, n_wk, f_id])|eapply n_fst, n_snd, n_hyp0].
  - intros [e K]. eexists. intros γ. cbn. apply n_pair; [apply f_fst|]. apply n_gen. intros α. apply n_lam.
    eapply f_comp; [|apply (K (kp F γ α))]. cbn. apply n_pair.
    + eapply f_comp; [|apply H4]. apply n_pair; [eapply n_fst, n_fst, f_id|apply f_snd].
    + apply (n_exI (fun u => fand (P1 G X (kp F γ α) u) (p u)) γ). apply n_pair; [|eapply n_snd, n_fst, f_id].
      eapply f_comp; [|apply (H2 (kp F γ α) γ α)]. apply n_pair; [|apply n_refl].
      eapply f_comp; [|apply H4]. apply n_pair; [eapply n_fst, n_fst, f_id|apply f_snd].
Qed.

End Quant.

(** ** Equality and the Beck–Chevalley condition *)

Section EqBC.

Context (F : frame).
Local Notation V := (@V F).
Local Notation tpred := (tpred F).
Local Notation tle := (tle F).

#[local] Instance teq_equiv7 : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.

Local Notation P1 x y := (prj_rel F x y (fun α β => α)).
Local Notation P2 x y := (prj_rel F x y (fun α β => β)).

(** ∃_Δ(p)(⟨α, α'⟩) ≜ ⟦α ε x⟧ ∧ ⟦α = α'⟧ ∧ p(α). *)
Definition teqdS_f (x : V) (p : tpred) (z : V) (α α' : V) : pcar F :=
  fand (veq z (kp F α α')) (fand (eps α x) (fand (veq α α') (p α))).

Program Definition teqdS (x : V) (p : tpred) : tpred := {| tp := fun z => fex2 F (teqdS_f x p z) |}.
Next Obligation.
  intros z z' E. apply fex2_proper. intros α α'. apply fand_proper; [apply veq_proper; [exact E|reflexivity]|reflexivity].
Qed.

Definition sdiag (x : V) : shom F x (vprod F x x) := spair F (sid F x) (sid F x).

Lemma teqdS_adj x (p r : tpred) : tle (vprod F x x) (teqdS x p) r <-> tle x p (treidx F (sdiag x) r).
Proof.
  destruct (kp_intro F x x) as [e1 H1], (veq_kp F) as [e2 H2].
  split.
  - intros [e H]. eexists. intros α. cbn.
    apply (n_exI (fun w => fand (pair_rel F (sid F x) (sid F x) α w) (r w)) (kp F α α)). apply n_pair.
    + apply (n_ex2I F _ (fun β γ => fand (fand (id_rel F x α β) (id_rel F x α γ)) (veq (kp F α α) (kp F β γ))) α α).
      apply n_pair; [apply n_pair; apply n_pair; [apply f_fst|apply n_refl|apply f_fst|apply n_refl]|apply n_refl].
    + eapply f_comp; [|apply H]. cbn. apply n_pair; [eapply f_comp; [apply n_pair; apply f_fst|apply H1]|].
      apply (n_ex2I F _ (teqdS_f x p (kp F α α)) α α). apply n_pair; [apply n_refl|].
      apply n_pair; [apply f_fst|]. apply n_pair; [apply n_refl|apply f_snd].
  - intros [e K]. eexists. intros z. cbn.
    apply (n_ex2E F _ _ (teqdS_f x p z)); [apply f_snd|]. intros α α'.
    apply (n_exE (fun w => fand (pair_rel F (sid F x) (sid F x) α w) (r w))).
    { eapply f_comp; [|apply K]. apply n_pair; [eapply n_fst, n_snd, n_hyp0|eapply n_snd, n_snd, n_snd, n_hyp0]. }
    intros w.
    apply (n_ex2E F _ _ (fun β γ => fand (fand (id_rel F x α β) (id_rel F x α γ)) (veq w (kp F β γ)))); [eapply n_fst, n_hyp0|]. intros β γ.
    apply (n_tr F r (tp_proper F r) w z); [|eapply n_snd, n_wk, n_wk, n_hyp0].
    eapply n_trans; [eapply n_snd, n_hyp0|]. eapply n_trans; [|apply n_sym; eapply n_fst, n_wk, n_wk, n_wk, n_hyp0].
    eapply f_comp; [|apply H2]. apply n_pair.
    + apply n_sym. eapply n_snd, n_fst, n_fst, n_hyp0.
    + eapply n_trans; [apply n_sym; eapply n_snd, n_snd, n_fst, n_hyp0|]. eapply n_fst, n_snd, n_snd, n_wk, n_wk, n_wk, n_hyp0.
Qed.

(** f × id ≜ ⟨f ∘ π₁, π₂⟩: on pairs, (f × id)(⟨γ', α⟩, w) ⇔ ∃γ. f(γ', γ) ∧ w = ⟨γ, α⟩. *)
Section FxId.

Context (G' G X : V) (f : shom F G' G).

Definition sfx : shom F (vprod F G' X) (vprod F G X) := spair F (scomp F f (spr1 F G' X)) (spr2 F G' X).

Lemma fx_intro : exists e, forall γ' γ α, fand (fand (eps γ' G') (eps α X)) (f γ' γ) —[e]→ sfx (kp F γ' α) (kp F γ α).
Proof.
  destruct (P1_intro F G' X) as [e1 H1], (P2_intro F G' X) as [e2 H2], (kp_intro F G' X) as [e3 H3].
  eexists. intros γ' γ α. cbn.
  apply (n_ex2I F _ (fun β δ => fand (fand (comp_rel F f (spr1 F G' X) (kp F γ' α) β) (P2 G' X (kp F γ' α) δ))
                                      (veq (kp F γ α) (kp F β δ))) γ α).
  apply n_pair; [apply n_pair|apply n_refl].
  - apply (n_exI (fun u => fand (P1 G' X (kp F γ' α) u) (f u γ)) γ'). apply n_pair; [|apply f_snd].
    eapply f_comp; [|apply (H1 (kp F γ' α) γ' α)]. apply n_pair; [eapply f_comp; [apply f_fst|apply H3]|apply n_refl].
  - eapply f_comp; [|apply (H2 (kp F γ' α) γ' α)]. apply n_pair; [eapply f_comp; [apply f_fst|apply H3]|apply n_refl].
Qed.

Lemma fx_elim : exists e, forall γ' α w, sfx (kp F γ' α) w —[e]→ fex (fun β => fand (f γ' β) (veq w (kp F β α))).
Proof.
  destruct (P1_veq F G' X) as [e1 H1], (P2_veq F G' X) as [e2 H2], (kp_veq_r F) as [e3 H3].
  eexists. intros γ' α w. cbn.
  apply (n_ex2E F _ _ (fun β δ => fand (fand (comp_rel F f (spr1 F G' X) (kp F γ' α) β) (P2 G' X (kp F γ' α) δ))
                                      (veq w (kp F β δ)))); [apply f_id|]. intros β δ.
  apply (n_exE (fun u => fand (P1 G' X (kp F γ' α) u) (f u β))); [eapply n_fst, n_fst, n_hyp0|]. intros u.
  apply (n_exI (fun β => fand (f γ' β) (veq w (kp F β α))) β). apply n_pair.
  - apply (n_tr F (fun v => f v β) (hr_l_proper F f β) u γ'); [|eapply n_snd, n_hyp0].
    apply n_sym. eapply f_comp; [|apply (H1 (kp F γ' α) γ' α u)]. apply n_pair; [apply n_refl|eapply n_fst, n_hyp0].
  - eapply n_trans; [eapply n_snd, n_wk, n_hyp0|]. eapply f_comp; [|apply H3]. apply n_sym.
    eapply f_comp; [|apply (H2 (kp F γ' α) γ' α δ)]. apply n_pair; [apply n_refl|eapply n_snd, n_fst, n_wk, n_hyp0].
Qed.

Lemma bc_ex_eq (r : tpred) : tiso F G' (treidx F f (texq F G X r)) (texq F G' X (treidx F sfx r)).
Proof.
  destruct fx_intro as [e1 H1], fx_elim as [e2 H2], (strict_r F f) as [e3 H3].
  split.
  - eexists. intros γ'. cbn.
    apply (n_exE (fun γ => fand (f γ' γ) (texq F G X r γ))); [apply f_snd|]. intros γ.
    apply (n_exE (fun α => fand (eps α X) (r (kp F γ α)))); [eapply n_snd, n_snd, n_hyp0|]. intros α.
    apply n_pair; [eapply n_fst, n_wk, n_wk, f_id|].
    apply (n_exI (fun α => fand (eps α X) (treidx F sfx r (kp F γ' α))) α). apply n_pair; [eapply n_fst, n_hyp0|]. cbn.
    apply (n_exI (fun w => fand (sfx (kp F γ' α) w) (r w)) (kp F γ α)). apply n_pair; [|eapply n_snd, n_hyp0].
    eapply f_comp; [|apply H1]. apply n_pair; [apply n_pair; [eapply n_fst, n_wk, n_wk, f_id|eapply n_fst, n_hyp0]|].
    eapply n_fst, n_wk, n_hyp0.
  - eexists. intros γ'. cbn.
    apply (n_exE (fun α => fand (eps α X) (treidx F sfx r (kp F γ' α)))); [eapply n_snd, f_snd|]. intros α.
    apply (n_exE (fun w => fand (sfx (kp F γ' α) w) (r w))); [eapply n_snd, n_hyp0|]. intros w.
    apply (n_exE (fun β => fand (f γ' β) (veq w (kp F β α)))); [eapply f_comp; [eapply n_fst, n_hyp0|apply H2]|]. intros β.
    apply (n_exI (fun γ => fand (f γ' γ) (texq F G X r γ)) β). apply n_pair; [eapply n_fst, n_hyp0|]. cbn.
    apply n_pair; [eapply f_comp; [eapply n_fst, n_hyp0|apply H3]|].
    apply (n_exI (fun α0 => fand (eps α0 X) (r (kp F β α0))) α). apply n_pair; [eapply n_fst, n_wk, n_wk, n_hyp0|].
    apply (n_tr F r (tp_proper F r) w (kp F β α)); [eapply n_snd, n_hyp0|eapply n_snd, n_wk, n_hyp0].
Qed.

Lemma bc_all_eq (r : tpred) : tiso F G' (treidx F f (tallq F G X r)) (tallq F G' X (treidx F sfx r)).
Proof.
  destruct fx_intro as [e1 H1], fx_elim as [e2 H2], (strict_r F f) as [e3 H3], (total_e F f) as [e4 H4],
    (func_e F f) as [e5 H5], (kp_veq_l F) as [e6 H6].
  split.
  - eexists. intros γ'. cbn.
    apply (n_exE (fun γ => fand (f γ' γ) (tallq F G X r γ))); [apply f_snd|]. intros γ.
    apply n_pair; [eapply n_fst, n_wk, f_id|]. apply n_gen. intros α. apply n_lam.
    apply (n_exI (fun w => fand (sfx (kp F γ' α) w) (r w)) (kp F γ α)). apply n_pair.
    + eapply f_comp; [|apply H1]. apply n_pair; [apply n_pair; [eapply n_fst, n_wk, n_wk, f_id|apply n_hyp0]|].
      eapply n_fst, n_wk, n_hyp0.
    + eapply n_app; [|apply n_hyp0]. apply (n_inst (fun α0 => fimp (eps α0 X) (r (kp F γ α0))) α).
      eapply n_snd, n_snd, n_wk, n_hyp0.
  - eexists. intros γ'. cbn.
    apply (n_exE (fun γ => f γ' γ)); [eapply f_comp; [apply f_fst|apply H4]|]. intros γ.
    apply (n_exI (fun γ => fand (f γ' γ) (tallq F G X r γ)) γ). apply n_pair; [apply n_hyp0|]. cbn.
    apply n_pair; [eapply f_comp; [apply n_hyp0|apply H3]|]. apply n_gen. intros α. apply n_lam.
    apply (n_exE (fun w => fand (sfx (kp F γ' α) w) (r w))).
    { eapply n_app; [|apply n_hyp0]. apply (n_inst (fun α0 => fimp (eps α0 X) (treidx F sfx r (kp F γ' α0))) α).
      eapply n_snd, n_snd, n_wk, n_wk, f_id. }
    intros w.
    apply (n_exE (fun β => fand (f γ' β) (veq w (kp F β α)))); [eapply f_comp; [eapply n_fst, n_hyp0|apply H2]|]. intros β.
    apply (n_tr F r (tp_proper F r) w (kp F γ α)); [|eapply n_snd, n_wk, n_hyp0].
    eapply n_trans; [eapply n_snd, n_hyp0|]. eapply f_comp; [|apply H6].
    eapply f_comp; [|apply (H5 γ' β γ)]. apply n_pair; [eapply n_fst, n_hyp0|apply n_wk, n_wk, n_wk, n_hyp0].
Qed.

End FxId.

End EqBC.

(** ** Weak power objects: 𝒫X ≜ ⟦𝒫(X)⟧, ∈_X(⟨α, b⟩) ≜ ⟦α ε b⟧ *)

Section Pow.

Context (F : frame).
Context (Φ0 : Type) (enc : pcar F -> Φ0) (dec : Φ0 -> pcar F).
Context (dec_enc : forall φ, dec (enc φ) ≡ φ).

Local Notation V := (@V F).
Local Notation tpred := (tpred F).
Local Notation tle := (tle F).
Local Notation vpower := (vpower F Φ0 dec).
Local Notation bsub := (bsub F Φ0 dec).

#[local] Instance teq_equiv8 : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.

Local Notation P1 x y := (prj_rel F x y (fun α β => α)).
Local Notation P2 x y := (prj_rel F x y (fun α β => β)).

Definition tmemf (z α A : V) : pcar F := fand (veq z (kp F α A)) (eps α A).

Program Definition tmemS (X : V) : tpred := {| tp := fun z => fex2 F (tmemf z) |}.
Next Obligation. intros z z' E. apply fex2_proper. intros α A. apply fand_proper; [apply veq_proper; [exact E|reflexivity]|reflexivity]. Qed.

Lemma bsub_br (X : V) g t : teq (sub (bsub X g) t) (sub X t) /\ lbl (bsub X g) t = fand (dec (g t)) (lbl X t).
Proof. destruct X as [[T k] l]. split; reflexivity. Qed.

Lemma bsub_proper (X : V) g g' : (forall t, dec (g t) ≡ dec (g' t)) -> teq (bsub X g) (bsub X g').
Proof. intros H. exists eq_refl. cbn. apply rel_proper; [apply leq_refl|exact H]. Qed.

Section Spec.

Context (X Y : V) (φ : tpred).

Definition chi (β : V) : V := bsub X (fun t => enc (φ (kp F (sub X t) β))).

Lemma chi_proper β β' : teq β β' -> teq (chi β) (chi β').
Proof.
  intros E. apply bsub_proper. intros t. rewrite !dec_enc. apply tp_proper, kp_proper; [reflexivity|exact E].
Qed.

Definition fpow_rel (β b : V) : pcar F := fand (eps β Y) (veq b (chi β)).

Lemma fpow_proper : Rproper F fpow_rel.
Proof.
  intros β β' b b' E1 E2. apply fand_proper; [apply eps_proper; [exact E1|reflexivity]|].
  apply veq_proper; [exact E2|apply chi_proper, E1].
Qed.

Lemma chi_in β : ftop —[e_comp e_top e_exI]→ eps (chi β) (vpower X).
Proof. eapply (n_eps_in F _ _ (vpower X) (fun t => enc (φ (kp F (sub X t) β)))); [reflexivity|apply f_top]. Qed.

Definition fpow : shom F Y (vpower X).
Proof.
  refine {| hr := fpow_rel; hr_proper := fpow_proper |}.
  - eexists. intros [β b]. cbn. apply n_pair; [apply f_fst|].
    apply (n_tr F (fun w => eps w (vpower X)) (eps_l_proper F _) (chi β) b); [apply n_sym, f_snd|].
    eapply f_comp; [apply f_top|apply chi_in].
  - eexists. intros β. apply (n_exI (fun b => fpow_rel β b) (chi β)). apply n_pair; [apply f_id|apply n_refl].
  - eexists. intros [[β b] b']. cbn. eapply n_trans; [eapply n_snd, f_fst|]. apply n_sym. eapply n_snd, f_snd.
Defined.

Definition sidxf : shom F (vprod F X Y) (vprod F X (vpower X)) := spair F (spr1 F X Y) (scomp F fpow (spr2 F X Y)).

Lemma pow_spec_eq : tiso F (vprod F X Y) φ (treidx F sidxf (tmemS X)).
Proof.
  destruct (prod_to F) as [e1 H1], (P1_intro F X Y) as [e2 H2], (P2_intro F X Y) as [e3 H3],
    (P1_veq F X Y) as [e4 H4], (P2_veq F X Y) as [e5 H5], (kp_inj_sem F) as [e6 H6], (veq_kp F) as [e7 H7].
  split.
  - eexists. intros z. cbn.
    apply (n_ex2E F _ _ (ProdEf F X Y z)); [eapply f_comp; [apply f_fst|apply H1]|]. intros α β.
    apply (n_exI (fun w => fand (pair_rel F (spr1 F X Y) (scomp F fpow (spr2 F X Y)) z w) (tmemS X w)) (kp F α (chi β))).
    apply n_pair.
    + apply (n_ex2I F _ (fun β0 γ0 => fand (fand (P1 X Y z β0) (comp_rel F fpow (spr2 F X Y) z γ0)) (veq (kp F α (chi β)) (kp F β0 γ0))) α (chi β)).
      apply n_pair; [apply n_pair|apply n_refl].
      * eapply f_comp; [|apply (H2 z α β)]. apply n_pair; [eapply n_fst, n_wk, n_wk, f_id|eapply n_fst, n_hyp0].
      * apply (n_exI (fun u => fand (P2 X Y z u) (fpow_rel u (chi β))) β). apply n_pair.
        -- eapply f_comp; [|apply (H3 z α β)]. apply n_pair; [eapply n_fst, n_wk, n_wk, f_id|eapply n_fst, n_hyp0].
        -- apply n_pair; [eapply n_snd, n_snd, n_hyp0|apply n_refl].
    + cbn. apply (n_ex2I F _ (tmemf (kp F α (chi β))) α (chi β)). apply n_pair; [apply n_refl|].
      eapply (n_eps_el F _ _ _ _ α X); [eapply n_fst, n_snd, n_hyp0|]. intros t Ht.
      eapply (n_eps_in F _ _ (chi β) t); [etransitivity; [unfold chi; apply (proj1 (bsub_br _ _ t))|exact Ht]|].
      unfold chi; rewrite (proj2 (bsub_br _ _ t)). apply n_pair; [|apply n_hyp0].
      eapply n_eq; [symmetry; apply dec_enc|].
      eapply n_eq; [apply tp_proper, kp_proper; [symmetry; exact Ht|reflexivity]|].
      apply (n_tr F φ (tp_proper F φ) z (kp F α β)); [eapply n_fst, n_wk, n_hyp0|eapply n_snd, n_wk, n_wk, n_wk, f_id].
  - eexists. intros z. cbn.
    apply (n_exE (fun w => fand (pair_rel F (spr1 F X Y) (scomp F fpow (spr2 F X Y)) z w) (tmemS X w))); [apply f_snd|]. intros w.
    apply (n_ex2E F _ _ (fun β0 γ0 => fand (fand (P1 X Y z β0) (comp_rel F fpow (spr2 F X Y) z γ0)) (veq w (kp F β0 γ0))));
      [eapply n_fst, n_hyp0|]. intros β1 γ1.
    apply (n_exE (fun u => fand (P2 X Y z u) (fpow_rel u γ1))); [eapply n_snd, n_fst, n_hyp0|]. intros u.
    apply (n_ex2E F _ _ (tmemf w)); [eapply n_snd, n_wk, n_wk, n_wk, n_hyp0|]. intros α A.
    apply (n_ex2E F _ _ (ProdEf F X Y z)); [eapply f_comp; [eapply n_fst, n_wk, n_wk, n_wk, n_wk, n_wk, n_wk, f_id|apply H1]|]. intros α0 β0.
    (* Γ: …, w, β1, γ1, u, α, A, α0, β0; hypotheses (most recent first):
       H0 = ProdEf z α0 β0; H1' = tmemf w α A; H2' = P2 z u ∧ fpow u γ1; H3' = data of the pair *)
    eapply (n_eps_el F _ _ _ _ α (chi u)).
    { apply (n_tr F (fun B => eps α B) (fun B B' E => eps_proper F _ _ _ _ (teq_refl F _) E) A (chi u)).
      - eapply n_trans; [apply n_sym; eapply n_snd; eapply f_comp; [|apply (H6 β1 γ1 α A)];
                         eapply n_trans; [apply n_sym; eapply n_snd, n_wk, n_wk, n_wk, n_wk, n_wk, n_hyp0|eapply n_fst, n_wk, n_wk, n_hyp0]|].
        eapply n_snd, n_snd, n_wk, n_wk, n_wk, n_wk, n_hyp0.
      - eapply n_snd, n_wk, n_wk, n_hyp0. }
    intros t Ht. unfold chi in *; rewrite (proj2 (bsub_br _ _ t)).
    apply (n_tr F φ (tp_proper F φ) (kp F α u) z).
    + apply n_sym. eapply n_trans; [eapply n_fst, n_wk, n_hyp0|]. eapply f_comp; [|apply H7]. apply n_pair.
      * (* α0 = α *)
        eapply n_trans; [eapply f_comp; [|apply (H4 z α0 β0 β1)]; apply n_pair; [eapply n_fst, n_wk, n_hyp0|eapply n_fst, n_fst, n_wk, n_wk, n_wk, n_wk, n_wk, n_wk, n_hyp0]|].
        eapply n_fst. eapply f_comp; [|apply (H6 β1 γ1 α A)].
        eapply n_trans; [apply n_sym; eapply n_snd, n_wk, n_wk, n_wk, n_wk, n_wk, n_wk, n_hyp0|eapply n_fst, n_wk, n_wk, n_wk, n_hyp0].
      * (* β0 = u *)
        eapply f_comp; [|apply (H5 z α0 β0 u)]. apply n_pair; [eapply n_fst, n_wk, n_hyp0|eapply n_fst, n_wk, n_wk, n_wk, n_wk, n_wk, n_hyp0].
    + eapply n_eq; [apply tp_proper, kp_proper; [etransitivity; [symmetry; apply (proj1 (bsub_br _ _ t))|exact Ht]|reflexivity]|].
      eapply n_eq; [apply dec_enc|]. eapply n_fst, n_hyp0.
Qed.

End Spec.

End Pow.

(** ** Proposition 30: x ↦ T(x) is an Sεt-tripos *)

Section SepsTripos.

Context (F : frame).
Context (Φ0 : Type) (enc : pcar F -> Φ0) (dec : Φ0 -> pcar F).
Context (dec_enc : forall φ, dec (enc φ) ≡ φ).

Theorem Seps_tripos : tripos (Seps F) (Seps_cart F).
Proof.
  refine (Build_tripos (Seps F) (Seps_cart F) (fibre F) (@treidx F)
            (treidx_mono F) (treidx_top F) (treidx_bot F) (treidx_and F) (treidx_or F) (treidx_imp F)
            (treidx_proper F) (treidx_id F) (treidx_comp F)
            (teqdS F) (teqdS_adj F) (texq F) (tallq F) (texq_adj F) (tallq_adj F) _ _
            (vpower F Φ0 dec) (tmemS F) _).
  - intros G' G X f r. apply (bc_ex_eq F G' G X f r).
  - intros G' G X f r. apply (bc_all_eq F G' G X f r).
  - intros X Y φ. exists (fpow F Φ0 enc dec dec_enc X Y φ). apply (pow_spec_eq F Φ0 enc dec dec_enc X Y φ).
Defined.

End SepsTripos.
