(** * Interpretation of IZFε in V(E), and soundness of deduction

    Terms are interpreted in V(E), formulas in Φ (Definition 25); the
    interpretation of a binder ({x ε a | φ}, {ψ(α) | α ε a}) uses the
    interpretation of its formula, as a function from V(E) to Φ. Free
    variables are interpreted by a valuation ρ.

    A formula is realized when a single evidence realizes it for all
    valuations (free variables are universal). Deduction preserves
    realization, uniformly: this is the "standard interpretation of
    formula constructors" invoked at the end of the proof of
    Theorem 26. *)

From Stdlib Require Import List Setoid Morphisms.
Import ListNotations.
From IZFe Require Import Syntax Deriv Frame VE.

Section Model.

Context (F : frame).
Context (Φ0 : Type) (enc : pcar F -> Φ0) (dec : Φ0 -> pcar F).
Context (dec_enc : forall φ, dec (enc φ) ≡ φ).
Local Abbreviation V := (@V F).

Context (coll : forall T : Type, (T -> V) -> (V -> V -> pcar F) -> V).
Context (coll_proper : forall T (xs xs' : T -> V) (ψ ψ' : V -> V -> pcar F),
  Rproper F ψ -> (forall t, teq (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
  teq (coll T xs ψ) (coll T xs' ψ')).

#[local] Instance teq_equiv : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.

Fixpoint evt (ρ : nat -> V) (t : term) : V :=
  match t with
  | tvar n => ρ n
  | tempty => vempty F
  | tomega => vomega F
  | tpair a b => vpair F (evt ρ a) (evt ρ b)
  | tunion a => vunion F (evt ρ a)
  | tpow a => vpower F Φ0 dec (evt ρ a)
  | tsep a φ => vsep F (evt ρ a) (fun z => evf (z .: ρ) φ)
  | trepl a ψ => vrepl F coll (evt ρ a) (fun α β => evf (β .: α .: ρ) ψ)
  end
with evf (ρ : nat -> V) (φ : form) : pcar F :=
  match φ with
  | fTop => ftop
  | fBot => fbot
  | fAnd φ ψ => fand (evf ρ φ) (evf ρ ψ)
  | fOr φ ψ => for_ (evf ρ φ) (evf ρ ψ)
  | fImp φ ψ => fimp (evf ρ φ) (evf ρ ψ)
  | fAll φ => fall (fun z : V => evf (z .: ρ) φ)
  | fEx φ => fex (fun z : V => evf (z .: ρ) φ)
  | fEps a b => eps (evt ρ a) (evt ρ b)
  | fMem a b => vmem (evt ρ a) (evt ρ b)
  | fSub a b => vsub (evt ρ a) (evt ρ b)
  | fEqv a b => veqv (evt ρ a) (evt ρ b)
  | fEq a b => veq (evt ρ a) (evt ρ b)
  end.

Definition venv (ρ ρ' : nat -> V) := forall n, teq (ρ n) (ρ' n).

Lemma venv_cons ρ ρ' z z' : venv ρ ρ' -> teq z z' -> venv (z .: ρ) (z' .: ρ').
Proof. intros H Hz [|n]; cbn; auto. Qed.

(** ** Compatibility of the interpretation with equality *)

Lemma ev_proper :
  (forall t ρ ρ', venv ρ ρ' -> teq (evt ρ t) (evt ρ' t)) /\
  (forall φ ρ ρ', venv ρ ρ' -> evf ρ φ ≡ evf ρ' φ).
Proof.
  apply syn_ind; intros; cbn.
  all: try reflexivity.
  all: try (apply H).
  all: try (apply vpair_proper; auto).
  all: try (apply vunion_proper; auto).
  all: try (apply vpower_proper; auto).
  all: try (apply fand_proper; auto).
  all: try (apply for_proper; auto).
  all: try (apply fimp_proper; auto).
  all: try (apply fall_proper; intros; apply H; apply venv_cons; [auto|reflexivity]).
  all: try (apply fex_proper; intros; apply H; apply venv_cons; [auto|reflexivity]).
  all: try (apply eps_proper; auto).
  all: try (apply vmem_proper; auto).
  all: try (apply vsub_proper; auto).
  all: try (apply veqv_proper; auto).
  all: try (apply veq_proper; auto).
  - apply vsep_proper; [| |intros z; apply H0, venv_cons; [auto|reflexivity]].
    + intros z z' E. apply H0, venv_cons; [intros n; reflexivity|exact E].
    + apply H, H1.
  - apply vrepl_proper; [exact coll_proper| | |].
    + intros α α' β β' Eα Eβ. apply H0. apply venv_cons; [apply venv_cons; [intros n; reflexivity|]|]; assumption.
    + apply H, H1.
    + intros α β. apply H0. apply venv_cons; [apply venv_cons|]; [auto|reflexivity|reflexivity].
Qed.

Lemma evt_proper t ρ ρ' : venv ρ ρ' -> teq (evt ρ t) (evt ρ' t).
Proof. apply ev_proper. Qed.
Lemma evf_proper φ ρ ρ' : venv ρ ρ' -> evf ρ φ ≡ evf ρ' φ.
Proof. apply ev_proper. Qed.

(** The formula φ, seen as a predicate compatible in its variable 0. *)
Definition pred (ρ : nat -> V) (φ : form) : pmor (Vset F) F :=
  Build_pmor (Vset F) F (fun z => evf (z .: ρ) φ)
    (fun z z' E => evf_proper φ _ _ (venv_cons ρ ρ z z' (fun n => teq_refl F (ρ n)) E)).

(** ** Renaming and substitution *)

Lemma ev_ren :
  (forall t ξ ρ ρ', (forall n, teq (ρ (ξ n)) (ρ' n)) -> teq (evt ρ (rent ξ t)) (evt ρ' t)) /\
  (forall φ ξ ρ ρ', (forall n, teq (ρ (ξ n)) (ρ' n)) -> evf ρ (renf ξ φ) ≡ evf ρ' φ).
Proof.
  assert (U : forall ξ (ρ ρ' : nat -> V) z, (forall n, teq (ρ (ξ n)) (ρ' n)) ->
                forall n, teq ((z .: ρ) (upr ξ n)) ((z .: ρ') n)).
  { intros ξ ρ ρ' z H [|n]; cbn; [reflexivity|apply H]. }
  apply syn_ind; intros; cbn.
  all: try reflexivity.
  all: try (apply H).
  all: try (apply vpair_proper; auto).
  all: try (apply vunion_proper; auto).
  all: try (apply vpower_proper; auto).
  all: try (apply fand_proper; auto).
  all: try (apply for_proper; auto).
  all: try (apply fimp_proper; auto).
  all: try (apply fall_proper; intros; apply H; apply U; auto).
  all: try (apply fex_proper; intros; apply H; apply U; auto).
  all: try (apply eps_proper; auto).
  all: try (apply vmem_proper; auto).
  all: try (apply vsub_proper; auto).
  all: try (apply veqv_proper; auto).
  all: try (apply veq_proper; auto).
  - apply vsep_proper; [| |intros z; apply H0, U; auto].
    + intros z z' E. apply evf_proper, venv_cons; [intros n; reflexivity|exact E].
    + apply H, H1.
  - apply vrepl_proper; [exact coll_proper| | |].
    + intros α α' β β' Eα Eβ. apply evf_proper. apply venv_cons; [apply venv_cons; [intros n; reflexivity|]|]; assumption.
    + apply H, H1.
    + intros α β. apply H0. apply U, U, H1.
Qed.

Lemma ev_subst :
  (forall t σ ρ ρ', (forall n, teq (evt ρ (σ n)) (ρ' n)) -> teq (evt ρ (subt σ t)) (evt ρ' t)) /\
  (forall φ σ ρ ρ', (forall n, teq (evt ρ (σ n)) (ρ' n)) -> evf ρ (subf σ φ) ≡ evf ρ' φ).
Proof.
  assert (U : forall σ (ρ ρ' : nat -> V) z, (forall n, teq (evt ρ (σ n)) (ρ' n)) ->
                forall n, teq (evt (z .: ρ) (ups σ n)) ((z .: ρ') n)).
  { intros σ ρ ρ' z H [|n]; cbn; [reflexivity|].
    rewrite <- (H n). apply (proj1 ev_ren). intros k; reflexivity. }
  apply syn_ind; intros; cbn.
  all: try reflexivity.
  all: try (apply H).
  all: try (apply vpair_proper; auto).
  all: try (apply vunion_proper; auto).
  all: try (apply vpower_proper; auto).
  all: try (apply fand_proper; auto).
  all: try (apply for_proper; auto).
  all: try (apply fimp_proper; auto).
  all: try (apply fall_proper; intros; apply H; apply U; auto).
  all: try (apply fex_proper; intros; apply H; apply U; auto).
  all: try (apply eps_proper; auto).
  all: try (apply vmem_proper; auto).
  all: try (apply vsub_proper; auto).
  all: try (apply veqv_proper; auto).
  all: try (apply veq_proper; auto).
  - apply vsep_proper; [| |intros z; apply H0, U; auto].
    + intros z z' E. apply evf_proper, venv_cons; [intros n; reflexivity|exact E].
    + apply H, H1.
  - apply vrepl_proper; [exact coll_proper| | |].
    + intros α α' β β' Eα Eβ. apply evf_proper. apply venv_cons; [apply venv_cons; [intros n; reflexivity|]|]; assumption.
    + apply H, H1.
    + intros α β. apply H0. apply U, U, H1.
Qed.

Lemma evf_inst ρ φ t : evf ρ (inst φ t) ≡ evf (evt ρ t .: ρ) φ.
Proof. apply ev_subst. intros [|n]; reflexivity. Qed.

Lemma evf_shf ρ z φ : evf (z .: ρ) (shf φ) ≡ evf ρ φ.
Proof. apply ev_ren. intros n; reflexivity. Qed.

Lemma evt_sht ρ z t : teq (evt (z .: ρ) (sht t)) (evt ρ t).
Proof. apply ev_ren. intros n; reflexivity. Qed.

(** ** Soundness of deduction *)

Fixpoint ctx (ρ : nat -> V) (Γ : list form) : pcar F :=
  match Γ with [] => ftop | A :: Γ => fand (ctx ρ Γ) (evf ρ A) end.

Lemma ctx_shift ρ z Γ : ctx (z .: ρ) (map shf Γ) ≡ ctx ρ Γ.
Proof. induction Γ as [|A Γ IH]; cbn; [reflexivity|]. rewrite IH, evf_shf. reflexivity. Qed.

Lemma ctx_In Γ φ : In φ Γ -> exists e, forall ρ, ctx ρ Γ —[e]→ evf ρ φ.
Proof.
  induction Γ as [|A Γ IH]; [intros []|]. intros [<-|H].
  - exists e_snd. intros ρ. apply f_snd.
  - destruct (IH H) as [e He]. exists (e_comp e_fst e). intros ρ. apply n_wk, He.
Qed.

Definition urealized (φ : form) : Prop := exists e, forall ρ, ftop —[e]→ evf ρ φ.

Theorem soundness (T : form -> Prop) (HT : forall φ, T φ -> urealized φ) Γ φ :
  prv T Γ φ -> exists e, forall ρ, ctx ρ Γ —[e]→ evf ρ φ.
Proof.
  induction 1.
  - apply ctx_In, H.
  - destruct (HT _ H) as [e He]. exists (e_const e). intros ρ. apply n_const, He.
  - exists e_top. intros ρ. apply f_top.
  - destruct IHprv as [e He]. exists (e_comp e e_incl). intros ρ. eapply f_comp; [apply He|apply f_bot].
  - destruct IHprv1 as [e1 K1], IHprv2 as [e2 K2]. exists (e_pair e1 e2). intros ρ. apply n_pair; [apply K1|apply K2].
  - destruct IHprv as [e He]. exists (e_comp e e_fst). intros ρ. eapply n_fst, He.
  - destruct IHprv as [e He]. exists (e_comp e e_snd). intros ρ. eapply n_snd, He.
  - destruct IHprv as [e He]. exists (e_kl e). intros ρ. apply n_orI1, He.
  - destruct IHprv as [e He]. exists (e_kr e). intros ρ. apply n_orI2, He.
  - destruct IHprv1 as [e0 K0], IHprv2 as [e1 K1], IHprv3 as [e2 K2].
    exists (e_case e0 e1 e2). intros ρ. apply (n_orE _ (evf ρ φ) (evf ρ ψ)); [apply K0|apply K1|apply K2].
  - destruct IHprv as [e He]. exists (e_lam e). intros ρ. apply n_lam, He.
  - destruct IHprv1 as [e1 K1], IHprv2 as [e2 K2]. exists (e_app e1 e2). intros ρ. eapply n_app; [apply K1|apply K2].
  - destruct IHprv as [e He]. exists (e_gen e). intros ρ. cbn. apply n_gen. intros z.
    rewrite <- (ctx_shift ρ z Γ). apply He.
  - destruct IHprv as [e He]. exists (e_comp e e_incl). intros ρ. rewrite evf_inst.
    apply (n_inst (fun z => evf (z .: ρ) φ)), He.
  - destruct IHprv as [e He]. exists (e_comp e e_exI). intros ρ.
    apply (n_exI (fun z => evf (z .: ρ) φ) (evt ρ t)). rewrite <- evf_inst. apply He.
  - destruct IHprv1 as [e1 K1], IHprv2 as [e2 K2]. exists (e_exE_ctx e1 e2). intros ρ.
    apply (n_exE (fun z => evf (z .: ρ) φ)); [apply K1|]. intros z.
    rewrite <- (evf_shf ρ z ψ), <- (ctx_shift ρ z Γ). apply (K2 (z .: ρ)).
  - exists e_refl. intros ρ. apply n_refl.
  - destruct IHprv1 as [e1 K1], IHprv2 as [e2 K2]. exists (e_app (e_comp e1 e_incl) e2). intros ρ.
    rewrite evf_inst. change (evf (evt ρ t .: ρ) φ) with (pred ρ φ (evt ρ t)).
    apply n_leib with (a := evt ρ s); [apply K1|]. cbn. rewrite <- evf_inst. apply K2.
Qed.

Corollary soundness_closed (T : form -> Prop) (HT : forall φ, T φ -> urealized φ) φ :
  prv T [] φ -> urealized φ.
Proof. intros H. apply (soundness T HT [] φ H). Qed.

End Model.
