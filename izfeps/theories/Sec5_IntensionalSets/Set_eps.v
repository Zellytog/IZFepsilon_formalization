(** * The category Sεt of intensional sets (Section 5.1)

    Objects: the elements of V(E). Morphisms x → y (Definition 27): the
    relations F : V × V → Φ, compatible with tree equality, whose
    strictness, totality and functionality (for Leibniz equality) are
    realized; two relations are identified if they are uniformly
    equivalent.

    The paper indexes relations by dom(x) × dom(y); here they are defined
    on V × V, strictness restricting them to the elements of x and y: the
    quantifications ⋂_{α ∈ dom(x)} become ⋂_{α ∈ V} guarded by
    ⟦α ε x⟧, which is uniformly equivalent. *)

From Stdlib Require Import Setoid Morphisms.
From IZFe Require Import Frame VE.

(** ** Categories with setoid homs *)

Record category := {
  ob : Type;
  hom : ob -> ob -> Type;
  heq : forall {x y}, hom x y -> hom x y -> Prop;
  heq_equiv : forall x y, Equivalence (@heq x y);
  cid : forall x, hom x x;
  ccomp : forall {x y z}, hom y z -> hom x y -> hom x z;
  ccomp_proper : forall x y z (g g' : hom y z) (f f' : hom x y), heq g g' -> heq f f' -> heq (ccomp g f) (ccomp g' f');
  cid_l : forall x y (f : hom x y), heq (ccomp (cid y) f) f;
  cid_r : forall x y (f : hom x y), heq (ccomp f (cid x)) f;
  cassoc : forall x y z w (f : hom x y) (g : hom y z) (h : hom z w), heq (ccomp h (ccomp g f)) (ccomp (ccomp h g) f)
}.

Arguments heq {c x y} f g.
Arguments cid {c} x.
Arguments ccomp {c x y z} g f.

Section Seps.

Context (F : frame).

Local Abbreviation V := (@V F).

#[local] Instance teq_equiv : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.

(** ** Tools *)

Definition uent {I : Type} (P Q : I -> pcar F) : Prop := exists e, forall i, P i —[e]→ Q i.

Lemma n_eps_in (φ : F) e (y : V) t x : teq (sub y t) x -> φ —[e]→ lbl y t -> φ —[e_comp e e_exI]→ eps x y.
Proof.
  intros Ht H. eapply f_comp; [exact H|].
  exact (f_exI _ (fun u : { u : idx y | teq (sub y u) x } => lbl y (proj1_sig u)) (exist _ t Ht)).
Qed.

Lemma n_eps_el (φ χ : F) e0 e (x y : V) :
  φ —[e0]→ eps x y -> (forall t, teq (sub y t) x -> fand φ (lbl y t) —[e]→ χ) -> φ —[e_exE_ctx e0 e]→ χ.
Proof.
  intros H0 H. apply (n_exE (fun u : { u : idx y | teq (sub y u) x } => lbl y (proj1_sig u))); [exact H0|].
  intros [t Ht]. apply H, Ht.
Qed.

Lemma n_veq_of_teq (φ : F) (x y : V) : teq x y -> φ —[e_refl]→ veq x y.
Proof. intros H. eapply n_eq; [apply veq_proper; [reflexivity|exact H]|apply n_refl]. Qed.

Definition Pm (P : V -> pcar F) (HP : Pproper F P) : pmor (Vset F) F := Build_pmor (Vset F) F P HP.

(** Transport along Leibniz equality, for a compatible predicate. *)
Lemma n_tr (P : V -> pcar F) (HP : Pproper F P) (a b : V) (φ : F) e1 e2 :
  φ —[e1]→ veq a b -> φ —[e2]→ P a -> φ —[e_app (e_comp e1 e_incl) e2]→ P b.
Proof. intros H1 H2. exact (n_leib (Pm P HP) a b φ e1 e2 H1 H2). Qed.

Lemma eps_l_proper y : Pproper F (fun z => eps z y).
Proof. intros z z' E. apply eps_proper; [exact E|reflexivity]. Qed.

(** ** Morphisms *)

Record shom (x y : V) := {
  hr :> V -> V -> pcar F;
  hr_proper : Rproper F hr;
  h_strict : uent (fun p : V * V => hr (fst p) (snd p)) (fun p => fand (eps (fst p) x) (eps (snd p) y));
  h_total : uent (fun α => eps α x) (fun α => fex (fun β : V => hr α β));
  h_func : uent (fun p : V * V * V => fand (hr (fst (fst p)) (snd (fst p))) (hr (fst (fst p)) (snd p)))
                (fun p => veq (snd (fst p)) (snd p))
}.

Arguments hr {x y} _ _ _.
Arguments hr_proper {x y} _.

Definition sheq {x y} (f g : shom x y) : Prop :=
  uent (fun p : V * V => f (fst p) (snd p)) (fun p => g (fst p) (snd p)) /\
  uent (fun p : V * V => g (fst p) (snd p)) (fun p => f (fst p) (snd p)).

Lemma sheq_equiv x y : Equivalence (@sheq x y).
Proof.
  split.
  - intros f. split; exists e_id; intros p; apply f_id.
  - intros f g [H1 H2]. split; assumption.
  - intros f g h [[e1 H1] [e1' H1']] [[e2 H2] [e2' H2']]. split.
    + exists (e_comp e1 e2). intros p. eapply f_comp; [apply H1|apply H2].
    + exists (e_comp e2' e1'). intros p. eapply f_comp; [apply H2'|apply H1'].
Qed.

#[local] Existing Instance sheq_equiv.

(** Access to the evidences of the three conditions. *)
Lemma strict_l {x y} (f : shom x y) : exists e, forall α β, f α β —[e]→ eps α x.
Proof. destruct (h_strict x y f) as [e He]. exists (e_comp e e_fst). intros α β. eapply n_fst, (He (α, β)). Qed.

Lemma strict_r {x y} (f : shom x y) : exists e, forall α β, f α β —[e]→ eps β y.
Proof. destruct (h_strict x y f) as [e He]. exists (e_comp e e_snd). intros α β. eapply n_snd, (He (α, β)). Qed.

Lemma func_e {x y} (f : shom x y) : exists e, forall α β β', fand (f α β) (f α β') —[e]→ veq β β'.
Proof. destruct (h_func x y f) as [e He]. exists e. intros α β β'. apply (He (α, β, β')). Qed.

Lemma total_e {x y} (f : shom x y) : exists e, forall α, eps α x —[e]→ fex (fun β : V => f α β).
Proof. exact (h_total x y f). Qed.

(** ** The identity: id_x(α, β) ≜ ⟦α ε x⟧ ∧ ⟦α = β⟧ *)

Definition id_rel (x : V) (α β : V) : pcar F := fand (eps α x) (veq α β).

Lemma id_proper x : Rproper F (id_rel x).
Proof. intros ? ? ? ? E1 E2. apply fand_proper; [apply eps_proper; [exact E1|reflexivity]|apply veq_proper; assumption]. Qed.

Definition sid (x : V) : shom x x.
Proof.
  refine {| hr := id_rel x; hr_proper := id_proper x |}.
  - eexists. intros [α β]. cbn. apply n_pair; [eapply n_fst, f_id|].
    apply (n_tr (fun z => eps z x) (eps_l_proper x) α β); [eapply n_snd, f_id|eapply n_fst, f_id].
  - eexists. intros α. apply (n_exI (fun β => id_rel x α β) α). apply n_pair; [apply f_id|apply n_refl].
  - eexists. intros [[α β] β']. cbn. apply n_trans with (b := α).
    + apply n_sym. eapply n_snd, n_fst, f_id.
    + eapply n_snd, n_snd, f_id.
Defined.

(** ** Composition: (g ∘ f)(α, γ) ≜ ⋃_β f(α, β) ∧ g(β, γ) *)

Definition comp_rel {x y z} (g : shom y z) (f : shom x y) (α γ : V) : pcar F :=
  fex (fun β : V => fand (f α β) (g β γ)).

Lemma comp_proper {x y z} (g : shom y z) (f : shom x y) : Rproper F (comp_rel g f).
Proof.
  intros α α' γ γ' E1 E2. apply fex_proper. intros β. apply fand_proper.
  - apply (hr_proper f); [exact E1|reflexivity].
  - apply (hr_proper g); [reflexivity|exact E2].
Qed.

Lemma hr_l_proper {x y} (f : shom x y) β : Pproper F (fun α => f α β).
Proof. intros α α' E. apply (hr_proper f); [exact E|reflexivity]. Qed.

Lemma hr_r_proper {x y} (f : shom x y) α : Pproper F (fun β => f α β).
Proof. intros β β' E. apply (hr_proper f); [reflexivity|exact E]. Qed.

Definition scomp {x y z} (g : shom y z) (f : shom x y) : shom x z.
Proof.
  refine {| hr := comp_rel g f; hr_proper := comp_proper g f |}.
  - destruct (strict_l f) as [e1 H1], (strict_r g) as [e2 H2].
    eexists. intros [α γ]. cbn. apply (n_exE (fun β => fand (f α β) (g β γ))); [apply f_id|]. intros β.
    apply n_pair; [eapply f_comp; [eapply n_fst, n_hyp0|apply H1]|eapply f_comp; [eapply n_snd, n_hyp0|apply H2]].
  - destruct (total_e f) as [e1 H1], (total_e g) as [e2 H2], (strict_r f) as [e3 H3].
    eexists. intros α. apply (n_exE (fun β => f α β)); [apply H1|]. intros β.
    apply (n_exE (fun γ => g β γ)); [eapply f_comp; [eapply f_comp; [apply n_hyp0|apply H3]|apply H2]|]. intros γ.
    apply (n_exI (fun γ => comp_rel g f α γ) γ). apply (n_exI (fun β => fand (f α β) (g β γ)) β).
    apply n_pair; [apply n_wk, n_hyp0|apply n_hyp0].
  - destruct (func_e f) as [e1 H1], (func_e g) as [e2 H2].
    eexists. intros [[α γ] γ']. cbn.
    apply (n_exE (fun β => fand (f α β) (g β γ))); [eapply n_fst, f_id|]. intros β.
    apply (n_exE (fun β => fand (f α β) (g β γ'))); [eapply n_snd, n_wk, f_id|]. intros β'.
    eapply f_comp; [|apply (H2 β)]. apply n_pair; [eapply n_snd, n_wk, n_hyp0|].
    apply (n_tr (fun b => g b γ') (hr_l_proper g γ') β' β).
    + apply n_sym. eapply f_comp; [|apply (H1 α β β')]. apply n_pair; [eapply n_fst, n_wk, n_hyp0|eapply n_fst, n_hyp0].
    + eapply n_snd, n_hyp0.
Defined.


(** ** The category laws, up to equivalence *)

Lemma scomp_proper x y z (g g' : shom y z) (f f' : shom x y) : sheq g g' -> sheq f f' -> sheq (scomp g f) (scomp g' f').
Proof.
  assert (M : forall (g g' : shom y z) (f f' : shom x y), sheq g g' -> sheq f f' ->
            uent (fun p : V * V => scomp g f (fst p) (snd p)) (fun p => scomp g' f' (fst p) (snd p))).
  { intros g0 g0' f0 f0' [[e1 H1] _] [[e2 H2] _]. eexists. intros [α γ]. cbn.
    apply (n_exE (fun β => fand (f0 α β) (g0 β γ))); [apply f_id|]. intros β.
    apply (n_exI (fun β => fand (f0' α β) (g0' β γ)) β).
    apply n_pair; [eapply f_comp; [eapply n_fst, n_hyp0|apply (H2 (α, β))]|eapply f_comp; [eapply n_snd, n_hyp0|apply (H1 (β, γ))]]. }
  intros Hg Hf. split; apply M; auto; symmetry; auto.
Qed.

Lemma scid_l x y (f : shom x y) : sheq (scomp (sid y) f) f.
Proof.
  destruct (strict_r f) as [e0 H0]. split.
  - eexists. intros [α γ]. cbn. apply (n_exE (fun β => fand (f α β) (id_rel y β γ))); [apply f_id|]. intros β.
    apply (n_tr (fun b => f α b) (hr_r_proper f α) β γ); [eapply n_snd, n_snd, n_hyp0|eapply n_fst, n_hyp0].
  - eexists. intros [α γ]. cbn. apply (n_exI (fun β => fand (f α β) (id_rel y β γ)) γ).
    apply n_pair; [apply f_id|]. apply n_pair; [apply H0|apply n_refl].
Qed.

Lemma scid_r x y (f : shom x y) : sheq (scomp f (sid x)) f.
Proof.
  destruct (strict_l f) as [e0 H0]. split.
  - eexists. intros [α γ]. cbn. apply (n_exE (fun β => fand (id_rel x α β) (f β γ))); [apply f_id|]. intros β.
    apply (n_tr (fun b => f b γ) (hr_l_proper f γ) β α); [apply n_sym; eapply n_snd, n_fst, n_hyp0|eapply n_snd, n_hyp0].
  - eexists. intros [α γ]. cbn. apply (n_exI (fun β => fand (id_rel x α β) (f β γ)) α).
    apply n_pair; [|apply f_id]. apply n_pair; [apply H0|apply n_refl].
Qed.

Lemma sassoc x y z w (f : shom x y) (g : shom y z) (h : shom z w) :
  sheq (scomp h (scomp g f)) (scomp (scomp h g) f).
Proof.
  split.
  - eexists. intros [α δ]. cbn.
    apply (n_exE (fun β => fand (comp_rel g f α β) (h β δ))); [apply f_id|]. intros γ.
    apply (n_exE (fun β => fand (f α β) (g β γ))); [eapply n_fst, n_hyp0|]. intros β.
    apply (n_exI (fun β => fand (f α β) (comp_rel h g β δ)) β). apply n_pair; [eapply n_fst, n_hyp0|].
    apply (n_exI (fun γ => fand (g β γ) (h γ δ)) γ). apply n_pair; [eapply n_snd, n_hyp0|eapply n_snd, n_wk, n_hyp0].
  - eexists. intros [α δ]. cbn.
    apply (n_exE (fun β => fand (f α β) (comp_rel h g β δ))); [apply f_id|]. intros β.
    apply (n_exE (fun γ => fand (g β γ) (h γ δ))); [eapply n_snd, n_hyp0|]. intros γ.
    apply (n_exI (fun γ => fand (comp_rel g f α γ) (h γ δ)) γ). apply n_pair; [|eapply n_snd, n_hyp0].
    apply (n_exI (fun β => fand (f α β) (g β γ)) β). apply n_pair; [eapply n_fst, n_wk, n_hyp0|eapply n_fst, n_hyp0].
Qed.

Definition Seps : category := {|
  ob := V; hom := shom; heq := @sheq; heq_equiv := sheq_equiv;
  cid := sid; ccomp := @scomp; ccomp_proper := scomp_proper;
  cid_l := scid_l; cid_r := scid_r; cassoc := sassoc
|}.

End Seps.
