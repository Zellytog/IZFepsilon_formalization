(** * Sεt is cartesian (Proposition 28)

    x × y ≜ {(φ ∧ ψ, ⟨α, β⟩) | (φ, α) ∈ x, (ψ, β) ∈ y}, with Kuratowski
    pairs built in V(E). Their injectivity for Leibniz equality is the
    derivation of [Pairs.v], transported into V(E) through the soundness
    of deduction: tree equality is never decided. *)

From Stdlib Require Import List Setoid Morphisms.
Import ListNotations.
From IZFe Require Import Syntax Deriv Theories Frame VE Model Realize Pairs Set_eps.

Record cartesian (C : category) := {
  one : ob C;
  bang : forall x, hom C x one;
  bang_uniq : forall x (f : hom C x one), heq f (bang x);
  prod : ob C -> ob C -> ob C;
  pr1 : forall x y, hom C (prod x y) x;
  pr2 : forall x y, hom C (prod x y) y;
  pairing : forall a x y, hom C a x -> hom C a y -> hom C a (prod x y);
  pr1_pair : forall a x y (f : hom C a x) (g : hom C a y), heq (ccomp (pr1 x y) (pairing a x y f g)) f;
  pr2_pair : forall a x y (f : hom C a x) (g : hom C a y), heq (ccomp (pr2 x y) (pairing a x y f g)) g;
  pair_uniq : forall a x y (f : hom C a x) (g : hom C a y) (h : hom C a (prod x y)),
    heq (ccomp (pr1 x y) h) f -> heq (ccomp (pr2 x y) h) g -> heq h (pairing a x y f g)
}.

Section Cart.

Context (F : frame).

Local Notation V := (@V F).

#[local] Instance teq_equiv2 : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.
#[local] Existing Instance sheq_equiv.

(** ** Pairs *)

Definition kp (a b : V) : V := vpair F (vpair F a a) (vpair F a b).

Lemma kp_proper a a' b b' : teq a a' -> teq b b' -> teq (kp a b) (kp a' b').
Proof. intros Ha Hb. unfold kp. apply vpair_proper; apply vpair_proper; assumption. Qed.

(** Any interpretation of the missing symbols will do. *)
Definition dcoll (T : Type) (xs : T -> V) (ψ : V -> V -> pcar F) : V := vempty F.
Lemma dcoll_proper : forall T (xs xs' : T -> V) (ψ ψ' : V -> V -> pcar F),
  Rproper F ψ -> (forall t, teq (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) -> teq (dcoll T xs ψ) (dcoll T xs' ψ').
Proof. intros; apply teq_refl. Qed.

Lemma PairT_realized φ : PairT φ -> urealized F unit (fun _ => ftop) dcoll φ.
Proof.
  intros (x & y & z & ->). destruct (R_pair F) as [e He]. exists e. intros ρ. apply He.
Qed.

Lemma kp_inj_sem : exists e, forall a b a' b', veq (kp a b) (kp a' b') —[e]→ fand (veq a a') (veq b b').
Proof.
  destruct (soundness F unit (fun _ => ftop) dcoll dcoll_proper PairT PairT_realized [] _ kp_inj) as [e He].
  exists (e_app (e_comp e_top e) e_id). intros a b a' b'.
  eapply n_app; [apply n_const, (He (a .: b .: a' .: b' .: fun _ => vempty F))|apply f_id].
Qed.

Lemma n_kp_inj1 (φ : F) e a b a' b' : φ —[e]→ veq (kp a b) (kp a' b') -> exists e', φ —[e']→ veq a a'.
Proof. intros H. destruct kp_inj_sem as [e0 H0]. eexists. eapply n_fst. eapply f_comp; [exact H|apply H0]. Qed.

(** veq is a congruence for kp. *)
Lemma veq_kp : exists e, forall a b a' b', fand (veq a a') (veq b b') —[e]→ veq (kp a b) (kp a' b').
Proof.
  eexists. intros a b a' b'.
  apply (n_tr F (fun z => veq (kp a b) (kp a' z)) (fun z z' E => veq_proper F _ _ _ _ (teq_refl F _) (kp_proper _ _ _ _ (teq_refl F _) E)) b b').
  - eapply n_snd, f_id.
  - apply (n_tr F (fun z => veq (kp a b) (kp z b)) (fun z z' E => veq_proper F _ _ _ _ (teq_refl F _) (kp_proper _ _ _ _ E (teq_refl F _))) a a').
    + eapply n_fst, f_id.
    + apply n_refl.
Qed.

(** ** The product *)

Definition vprod (x y : V) : V :=
  mk (idx x * idx y) (fun p => (fand (lbl x (fst p)) (lbl y (snd p)), kp (sub x (fst p)) (sub y (snd p)))).

Definition fex2 (f : V -> V -> pcar F) : pcar F := fex (fun α : V => fex (fun β : V => f α β)).

Lemma fex2_proper f g : (forall α β, f α β ≡ g α β) -> fex2 f ≡ fex2 g.
Proof. intros H. apply fex_proper; intros α; apply fex_proper; intros β; apply H. Qed.

Lemma n_ex2I (φ : F) (f : V -> V -> pcar F) α β e : φ —[e]→ f α β -> φ —[e_comp (e_comp e e_exI) e_exI]→ fex2 f.
Proof. intros H. apply (n_exI (fun α => fex (fun β => f α β)) α). apply (n_exI (fun β => f α β) β). exact H. Qed.

Lemma n_ex2E (φ χ : F) (f : V -> V -> pcar F) e0 e :
  φ —[e0]→ fex2 f -> (forall α β, fand (fand φ (fex (fun β => f α β))) (f α β) —[e]→ χ) ->
  φ —[e_exE_ctx e0 (e_exE_ctx e_snd e)]→ χ.
Proof.
  intros H0 H. apply (n_exE (fun α => fex (fun β => f α β))); [exact H0|]. intros α.
  apply (n_exE (fun β => f α β)); [apply n_hyp0|]. intros β. apply H.
Qed.

(** The elements of x × y: p ε x × y ⇔ ∃α β. p = ⟨α, β⟩ ∧ α ε x ∧ β ε y. *)
Definition ProdEf (x y p : V) (α β : V) : pcar F := fand (veq p (kp α β)) (fand (eps α x) (eps β y)).
Definition ProdE (x y p : V) : pcar F := fex2 (ProdEf x y p).

Lemma prod_to : exists e, forall x y p, eps p (vprod x y) —[e]→ ProdE x y p.
Proof.
  eexists. intros x y p. eapply (n_eps_el F _ _ _ _ p (vprod x y)); [apply f_id|]. intros [t u] Ht.
  apply (n_ex2I _ _ (sub x t) (sub y u)). apply n_pair.
  - apply n_veq_of_teq. apply (teq_trans F p (sub (vprod x y) (t, u))); [apply teq_sym, Ht|unfold vprod; apply (sub_mk F)].
  - apply n_pair.
    + eapply (n_eps_in F _ _ x t); [reflexivity|]. eapply n_fst, n_hyp0.
    + eapply (n_eps_in F _ _ y u); [reflexivity|]. eapply n_snd, n_hyp0.
Qed.

Lemma prod_from : exists e, forall x y p, ProdE x y p —[e]→ eps p (vprod x y).
Proof.
  eexists. intros x y p. apply (n_ex2E _ _ (ProdEf x y p)); [apply f_id|]. intros α β.
  eapply (n_eps_el F _ _ _ _ α x); [eapply n_fst, n_snd, n_hyp0|]. intros t Ht.
  eapply (n_eps_el F _ _ _ _ β y); [eapply n_snd, n_snd, n_wk, n_hyp0|]. intros u Hu.
  apply (n_tr F (fun z => eps z (vprod x y)) (eps_l_proper F _) (kp α β) p).
  - apply n_sym. eapply n_fst, n_wk, n_wk, n_hyp0.
  - eapply (n_eps_in F _ _ (vprod x y) (t, u)).
    + etransitivity; [unfold vprod; apply (sub_mk F)|]. apply kp_proper; assumption.
    + apply n_pair; [apply n_wk, n_hyp0|apply n_hyp0].
Qed.


Lemma prod_to_e : exists e, forall x y p (φ : F) e0, φ —[e0]→ eps p (vprod x y) -> φ —[e_comp e0 e]→ ProdE x y p.
Proof. destruct prod_to as [e He]. exists e. intros. eapply f_comp; [eassumption|apply He]. Qed.

(** ** The projections, generically: s(α, β) selects a component *)

Section Proj.

Context (x y z : V) (s : V -> V -> V).
Context (s_proper : forall α α' β β', teq α α' -> teq β β' -> teq (s α β) (s α' β')).
Context (s_inj : exists e, forall α β α' β', veq (kp α β) (kp α' β') —[e]→ veq (s α β) (s α' β')).
Context (s_mem : exists e, forall α β, fand (eps α x) (eps β y) —[e]→ eps (s α β) z).

Definition prj_rel (p γ : V) : pcar F :=
  fand (eps p (vprod x y)) (fex2 (fun α β => fand (veq p (kp α β)) (veq (s α β) γ))).

Lemma prj_proper : Rproper F prj_rel.
Proof.
  intros p p' γ γ' Ep Eγ. apply fand_proper; [apply eps_proper; [exact Ep|reflexivity]|].
  apply fex2_proper. intros α β. apply fand_proper; apply veq_proper; (assumption || reflexivity).
Qed.

Definition sprj : shom F (vprod x y) z.
Proof.
  refine {| hr := prj_rel; hr_proper := prj_proper |}.
  - destruct prod_to_e as [e1 H1], s_inj as [e2 H2], s_mem as [e3 H3].
    eexists. intros [p γ]. cbn. apply n_pair; [eapply n_fst, f_id|].
    apply (n_ex2E _ _ (ProdEf x y p)); [apply (H1 x y p); eapply n_fst, f_id|]. intros α' β'.
    apply (n_ex2E _ _ (fun α β => fand (veq p (kp α β)) (veq (s α β) γ))); [eapply n_snd, n_wk, n_wk, f_id|]. intros α β.
    apply (n_tr F (fun w => eps w z) (eps_l_proper F z) (s α' β') γ).
    + eapply n_trans; [|eapply n_snd, n_hyp0].
      eapply f_comp; [|apply H2].
      eapply n_trans; [apply n_sym; eapply n_fst, n_wk, n_wk, n_hyp0|eapply n_fst, n_hyp0].
    + eapply f_comp; [|apply H3]. eapply n_snd, n_wk, n_wk, n_hyp0.
  - destruct prod_to_e as [e1 H1].
    eexists. intros p. apply (n_ex2E _ _ (ProdEf x y p)); [apply (H1 x y p), f_id|]. intros α β.
    apply (n_exI (fun γ => prj_rel p γ) (s α β)). apply n_pair; [eapply n_wk, n_wk, f_id|].
    apply (n_ex2I _ _ α β). apply n_pair; [eapply n_fst, n_hyp0|apply n_refl].
  - destruct s_inj as [e2 H2].
    eexists. intros [[p γ] γ']. cbn.
    apply (n_ex2E _ _ (fun α β => fand (veq p (kp α β)) (veq (s α β) γ))); [eapply n_snd, n_fst, f_id|]. intros α β.
    apply (n_ex2E _ _ (fun α β => fand (veq p (kp α β)) (veq (s α β) γ'))); [eapply n_snd, n_snd, n_wk, n_wk, f_id|]. intros α' β'.
    eapply n_trans; [apply n_sym; eapply n_snd, n_wk, n_wk, n_hyp0|].
    eapply n_trans; [|eapply n_snd, n_hyp0].
    eapply f_comp; [|apply H2].
    eapply n_trans; [apply n_sym; eapply n_fst, n_wk, n_wk, n_hyp0|eapply n_fst, n_hyp0].
Defined.

End Proj.

Lemma inj_fst : exists e, forall α β α' β', veq (kp α β) (kp α' β') —[e]→ veq α α'.
Proof. destruct kp_inj_sem as [e He]. exists (e_comp e e_fst). intros. eapply n_fst, He. Qed.
Lemma inj_snd : exists e, forall α β α' β', veq (kp α β) (kp α' β') —[e]→ veq β β'.
Proof. destruct kp_inj_sem as [e He]. exists (e_comp e e_snd). intros. eapply n_snd, He. Qed.
Lemma mem_fst (x y : V) : exists e, forall α β, fand (eps α x) (eps β y) —[e]→ eps α x.
Proof. exists e_fst. intros; apply f_fst. Qed.
Lemma mem_snd (x y : V) : exists e, forall α β, fand (eps α x) (eps β y) —[e]→ eps β y.
Proof. exists e_snd. intros; apply f_snd. Qed.

Definition spr1 x y : shom F (vprod x y) x :=
  sprj x y x (fun α β => α) inj_fst (mem_fst x y).
Definition spr2 x y : shom F (vprod x y) y :=
  sprj x y y (fun α β => β) inj_snd (mem_snd x y).

(** ** Pairing: ⟨f, g⟩(c, p) ≜ ⋃_{β, γ} f(c, β) ∧ g(c, γ) ∧ ⟦p = ⟨β, γ⟩⟧ *)

Definition pair_rel {a x y} (f : shom F a x) (g : shom F a y) (c p : V) : pcar F :=
  fex2 (fun β γ => fand (fand (f c β) (g c γ)) (veq p (kp β γ))).

Lemma pair_rel_proper {a x y} (f : shom F a x) (g : shom F a y) : Rproper F (pair_rel f g).
Proof.
  intros c c' p p' Ec Ep. apply fex2_proper. intros β γ.
  apply fand_proper; [apply fand_proper|apply veq_proper; [exact Ep|reflexivity]].
  - apply (hr_proper F _ _ f); [exact Ec|reflexivity].
  - apply (hr_proper F _ _ g); [exact Ec|reflexivity].
Qed.

Definition spair {a x y} (f : shom F a x) (g : shom F a y) : shom F a (vprod x y).
Proof.
  refine {| hr := pair_rel f g; hr_proper := pair_rel_proper f g |}.
  - destruct (strict_l F f) as [e1 H1], (strict_r F f) as [e2 H2], (strict_r F g) as [e3 H3], prod_from as [e4 H4].
    eexists. intros [c p]. cbn. apply (n_ex2E _ _ (fun β γ => fand (fand (f c β) (g c γ)) (veq p (kp β γ)))); [apply f_id|]. intros β γ.
    apply n_pair; [eapply f_comp; [eapply n_fst, n_fst, n_hyp0|apply H1]|].
    eapply f_comp; [|apply H4]. apply (n_ex2I _ _ β γ). apply n_pair; [eapply n_snd, n_hyp0|].
    apply n_pair; [eapply f_comp; [eapply n_fst, n_fst, n_hyp0|apply H2]|eapply f_comp; [eapply n_snd, n_fst, n_hyp0|apply H3]].
  - destruct (total_e F f) as [e1 H1], (total_e F g) as [e2 H2].
    eexists. intros c. apply (n_exE (fun β => f c β)); [apply H1|]. intros β.
    apply (n_exE (fun γ => g c γ)); [eapply f_comp; [apply n_wk, f_id|apply H2]|]. intros γ.
    apply (n_exI (fun p => pair_rel f g c p) (kp β γ)). apply (n_ex2I _ _ β γ).
    apply n_pair; [apply n_pair; [apply n_wk, n_hyp0|apply n_hyp0]|apply n_refl].
  - destruct (func_e F f) as [e1 H1], (func_e F g) as [e2 H2], veq_kp as [e3 H3].
    eexists. intros [[c p] p']. cbn.
    apply (n_ex2E _ _ (fun β γ => fand (fand (f c β) (g c γ)) (veq p (kp β γ)))); [eapply n_fst, f_id|]. intros β γ.
    apply (n_ex2E _ _ (fun β γ => fand (fand (f c β) (g c γ)) (veq p' (kp β γ)))); [eapply n_snd, n_wk, n_wk, f_id|]. intros β' γ'.
    eapply n_trans; [eapply n_snd, n_wk, n_wk, n_hyp0|].
    eapply n_trans; [|apply n_sym; eapply n_snd, n_hyp0].
    eapply f_comp; [|apply H3]. apply n_pair.
    + eapply f_comp; [|apply (H1 c)]. apply n_pair; [eapply n_fst, n_fst, n_wk, n_wk, n_hyp0|eapply n_fst, n_fst, n_hyp0].
    + eapply f_comp; [|apply (H2 c)]. apply n_pair; [eapply n_snd, n_fst, n_wk, n_wk, n_hyp0|eapply n_snd, n_fst, n_hyp0].
Defined.


(** ** The universal property *)

Local Notation P1 x y := (prj_rel x y (fun α β => α)).
Local Notation P2 x y := (prj_rel x y (fun α β => β)).

Lemma pr1_pair_eq a x y (f : shom F a x) (g : shom F a y) : sheq F (scomp F (spr1 x y) (spair f g)) f.
Proof.
  destruct inj_fst as [ei Hi], (strict_l F f) as [e1 H1], (strict_r F f) as [e2 H2], (strict_r F g) as [e3 H3],
    (total_e F g) as [e4 H4], prod_from as [e5 H5].
  split.
  - eexists. intros [c δ]. cbn.
    apply (n_exE (fun p => fand (pair_rel f g c p) (P1 x y p δ))); [apply f_id|]. intros p.
    apply (n_ex2E _ _ (fun β γ => fand (fand (f c β) (g c γ)) (veq p (kp β γ)))); [eapply n_fst, n_hyp0|]. intros β γ.
    apply (n_ex2E _ _ (fun α β' => fand (veq p (kp α β')) (veq α δ))); [eapply n_snd, n_snd, n_wk, n_wk, n_hyp0|]. intros α β'.
    apply (n_tr F (fun b => f c b) (hr_r_proper F f c) β δ).
    + eapply n_trans; [|eapply n_snd, n_hyp0]. eapply f_comp; [|apply (Hi β γ α β')].
      eapply n_trans; [apply n_sym; eapply n_snd, n_wk, n_wk, n_hyp0|eapply n_fst, n_hyp0].
    + eapply n_fst, n_fst, n_wk, n_wk, n_hyp0.
  - eexists. intros [c δ]. cbn.
    apply (n_exE (fun γ => g c γ)); [eapply f_comp; [apply H1|apply H4]|]. intros γ.
    apply (n_exI (fun p => fand (pair_rel f g c p) (P1 x y p δ)) (kp δ γ)). apply n_pair.
    + apply (n_ex2I _ (fun β γ0 => fand (fand (f c β) (g c γ0)) (veq (kp δ γ) (kp β γ0))) δ γ).
      apply n_pair; [apply n_pair; [apply n_wk, f_id|apply n_hyp0]|apply n_refl].
    + apply n_pair.
      * eapply f_comp; [|apply H5]. apply (n_ex2I _ (ProdEf x y (kp δ γ)) δ γ).
        apply n_pair; [apply n_refl|]. apply n_pair; [eapply f_comp; [apply n_wk, f_id|apply H2]|eapply f_comp; [apply n_hyp0|apply H3]].
      * apply (n_ex2I _ (fun α β => fand (veq (kp δ γ) (kp α β)) (veq α δ)) δ γ). apply n_pair; apply n_refl.
Qed.

Lemma pr2_pair_eq a x y (f : shom F a x) (g : shom F a y) : sheq F (scomp F (spr2 x y) (spair f g)) g.
Proof.
  destruct inj_snd as [ei Hi], (strict_l F g) as [e1 H1], (strict_r F f) as [e2 H2], (strict_r F g) as [e3 H3],
    (total_e F f) as [e4 H4], prod_from as [e5 H5].
  split.
  - eexists. intros [c δ]. cbn.
    apply (n_exE (fun p => fand (pair_rel f g c p) (P2 x y p δ))); [apply f_id|]. intros p.
    apply (n_ex2E _ _ (fun β γ => fand (fand (f c β) (g c γ)) (veq p (kp β γ)))); [eapply n_fst, n_hyp0|]. intros β γ.
    apply (n_ex2E _ _ (fun α β' => fand (veq p (kp α β')) (veq β' δ))); [eapply n_snd, n_snd, n_wk, n_wk, n_hyp0|]. intros α β'.
    apply (n_tr F (fun b => g c b) (hr_r_proper F g c) γ δ).
    + eapply n_trans; [|eapply n_snd, n_hyp0]. eapply f_comp; [|apply (Hi β γ α β')].
      eapply n_trans; [apply n_sym; eapply n_snd, n_wk, n_wk, n_hyp0|eapply n_fst, n_hyp0].
    + eapply n_snd, n_fst, n_wk, n_wk, n_hyp0.
  - eexists. intros [c δ]. cbn.
    apply (n_exE (fun β => f c β)); [eapply f_comp; [apply H1|apply H4]|]. intros β.
    apply (n_exI (fun p => fand (pair_rel f g c p) (P2 x y p δ)) (kp β δ)). apply n_pair.
    + apply (n_ex2I _ (fun β0 γ0 => fand (fand (f c β0) (g c γ0)) (veq (kp β δ) (kp β0 γ0))) β δ).
      apply n_pair; [apply n_pair; [apply n_hyp0|apply n_wk, f_id]|apply n_refl].
    + apply n_pair.
      * eapply f_comp; [|apply H5]. apply (n_ex2I _ (ProdEf x y (kp β δ)) β δ).
        apply n_pair; [apply n_refl|]. apply n_pair; [eapply f_comp; [apply n_hyp0|apply H2]|eapply f_comp; [apply n_wk, f_id|apply H3]].
      * apply (n_ex2I _ (fun α β0 => fand (veq (kp β δ) (kp α β0)) (veq β0 δ)) β δ). apply n_pair; apply n_refl.
Qed.

Lemma pair_uniq_eq a x y (f : shom F a x) (g : shom F a y) (h : shom F a (vprod x y)) :
  sheq F (scomp F (spr1 x y) h) f -> sheq F (scomp F (spr2 x y) h) g -> sheq F h (spair f g).
Proof.
  intros [[k1 K1] _] [[k2 K2] _].
  destruct (strict_r F h) as [e1 H1], prod_to as [e2 H2], (strict_l F f) as [e3 H3], (total_e F h) as [e4 H4],
    (func_e F f) as [e5 H5], (func_e F g) as [e6 H6], veq_kp as [e7 H7].
  split.
  - eexists. intros [c p]. cbn.
    apply (n_ex2E _ _ (ProdEf x y p)); [eapply f_comp; [apply H1|apply H2]|]. intros α β.
    apply (n_ex2I _ (fun β0 γ0 => fand (fand (f c β0) (g c γ0)) (veq p (kp β0 γ0))) α β).
    apply n_pair; [apply n_pair|eapply n_fst, n_hyp0].
    + eapply f_comp; [|apply (K1 (c, α))]. cbn.
      apply (n_exI (fun p0 => fand (h c p0) (P1 x y p0 α)) p). apply n_pair; [apply n_wk, n_wk, f_id|].
      apply n_pair; [eapply f_comp; [apply n_wk, n_wk, f_id|apply H1]|].
      apply (n_ex2I _ (fun α0 β0 => fand (veq p (kp α0 β0)) (veq α0 α)) α β). apply n_pair; [eapply n_fst, n_hyp0|apply n_refl].
    + eapply f_comp; [|apply (K2 (c, β))]. cbn.
      apply (n_exI (fun p0 => fand (h c p0) (P2 x y p0 β)) p). apply n_pair; [apply n_wk, n_wk, f_id|].
      apply n_pair; [eapply f_comp; [apply n_wk, n_wk, f_id|apply H1]|].
      apply (n_ex2I _ (fun α0 β0 => fand (veq p (kp α0 β0)) (veq β0 β)) α β). apply n_pair; [eapply n_fst, n_hyp0|apply n_refl].
  - eexists. intros [c p]. cbn.
    apply (n_ex2E _ _ (fun β γ => fand (fand (f c β) (g c γ)) (veq p (kp β γ)))); [apply f_id|]. intros β γ.
    apply (n_exE (fun p' => h c p')); [eapply f_comp; [eapply n_fst, n_fst, n_hyp0|]; eapply f_comp; [apply H3|apply H4]|]. intros p'.
    apply (n_ex2E _ _ (ProdEf x y p')); [eapply f_comp; [apply n_hyp0|]; eapply f_comp; [apply H1|apply H2]|]. intros α' β'.
    (* context: ((((φ ∧ _) ∧ (fβ ∧ gγ ∧ p = ⟨β,γ⟩)) ∧ h c p') ∧ _) ∧ (p' = ⟨α',β'⟩ ∧ …) *)
    apply (n_tr F (fun q => h c q) (hr_r_proper F h c) p' p).
    + eapply n_trans; [eapply n_fst, n_hyp0|]. apply n_sym.
      eapply n_trans; [eapply n_snd, n_wk, n_wk, n_wk, n_hyp0|].
      eapply f_comp; [|apply H7]. apply n_pair.
      * eapply f_comp; [|apply (H5 c)]. apply n_pair; [eapply n_fst, n_fst, n_wk, n_wk, n_wk, n_hyp0|].
        eapply f_comp; [|apply (K1 (c, α'))]. cbn.
        apply (n_exI (fun p0 => fand (h c p0) (P1 x y p0 α')) p'). apply n_pair; [apply n_wk, n_wk, n_hyp0|].
        apply n_pair; [eapply f_comp; [apply n_wk, n_wk, n_hyp0|apply H1]|].
        apply (n_ex2I _ (fun α0 β0 => fand (veq p' (kp α0 β0)) (veq α0 α')) α' β'). apply n_pair; [eapply n_fst, n_hyp0|apply n_refl].
      * eapply f_comp; [|apply (H6 c)]. apply n_pair; [eapply n_snd, n_fst, n_wk, n_wk, n_wk, n_hyp0|].
        eapply f_comp; [|apply (K2 (c, β'))]. cbn.
        apply (n_exI (fun p0 => fand (h c p0) (P2 x y p0 β')) p'). apply n_pair; [apply n_wk, n_wk, n_hyp0|].
        apply n_pair; [eapply f_comp; [apply n_wk, n_wk, n_hyp0|apply H1]|].
        apply (n_ex2I _ (fun α0 β0 => fand (veq p' (kp α0 β0)) (veq β0 β')) α' β'). apply n_pair; [eapply n_fst, n_hyp0|apply n_refl].
    + apply n_wk, n_wk, n_hyp0.
Qed.

(** ** The terminal object 1 ≜ {(⊤, ∅)} *)

Definition vone : V := mk unit (fun _ => (ftop, vempty F)).

Lemma one_el (β β' : V) (t t' : idx vone) : teq (sub vone t) β -> teq (sub vone t') β' -> teq β β'.
Proof.
  intros H H'. rewrite <- H, <- H'. etransitivity; [apply (sub_mk F)|]. symmetry. apply (sub_mk F).
Qed.

Definition bang_rel (x : V) (α β : V) : pcar F := fand (eps α x) (eps β vone).

Lemma bang_proper x : Rproper F (bang_rel x).
Proof. intros ? ? ? ? E1 E2. apply fand_proper; apply eps_proper; (assumption || reflexivity). Qed.

Definition sbang (x : V) : shom F x vone.
Proof.
  refine {| hr := bang_rel x; hr_proper := bang_proper x |}.
  - exists e_id. intros [α β]. apply f_id.
  - eexists. intros α. apply (n_exI (fun β => bang_rel x α β) (vempty F)). apply n_pair; [apply f_id|].
    eapply (n_eps_in F _ _ vone tt); [apply (sub_mk F)|apply f_top].
  - eexists. intros [[α β] β']. cbn.
    eapply (n_eps_el F _ _ _ _ β vone); [eapply n_snd, n_fst, f_id|]. intros t Ht.
    eapply (n_eps_el F _ _ _ _ β' vone); [eapply n_snd, n_snd, n_wk, f_id|]. intros t' Ht'.
    apply n_veq_of_teq. eapply one_el; eassumption.
Defined.

Lemma bang_uniq_eq x (f : shom F x vone) : sheq F f (sbang x).
Proof.
  destruct (h_strict F _ _ f) as [e0 H0], (total_e F f) as [e1 H1], (strict_r F f) as [e2 H2].
  split.
  - exists e0. intros [α β]. apply (H0 (α, β)).
  - eexists. intros [α β]. cbn.
    apply (n_exE (fun β' => f α β')); [eapply f_comp; [apply f_fst|apply H1]|]. intros β'.
    eapply (n_eps_el F _ _ _ _ β vone); [eapply n_snd, n_wk, f_id|]. intros t Ht.
    eapply (n_eps_el F _ _ _ _ β' vone); [eapply f_comp; [apply n_wk, n_hyp0|apply H2]|]. intros t' Ht'.
    eapply n_eq; [apply (hr_proper F _ _ f); [reflexivity|eapply one_el; [exact Ht'|exact Ht]]|].
    apply n_wk, n_wk, n_hyp0.
Qed.

Definition Seps_cart : cartesian (Seps F) :=
  Build_cartesian (Seps F) vone sbang bang_uniq_eq vprod spr1 spr2 (@spair)
    pr1_pair_eq pr2_pair_eq pair_uniq_eq.

End Cart.
