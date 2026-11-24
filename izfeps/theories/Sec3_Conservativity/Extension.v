(** * IZF⁻ε extends IZF (Section 3.1: Lemma 11 and Theorem 12)

    The translation φ ↦ φ^ε reads ∈ and ⊆ as themselves and = as ≃. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax Deriv ISyntax Theories Basic.

Fixpoint tr (φ : iform) : form :=
  match φ with
  | iTop => fTop | iBot => fBot
  | iAnd φ ψ => fAnd (tr φ) (tr ψ)
  | iOr φ ψ => fOr (tr φ) (tr ψ)
  | iImp φ ψ => fImp (tr φ) (tr ψ)
  | iAll φ => fAll (tr φ)
  | iEx φ => fEx (tr φ)
  | iMem x y => fMem (tvar x) (tvar y)
  | iSub x y => fSub (tvar x) (tvar y)
  | iEq x y => fEqv (tvar x) (tvar y)
  end.

Lemma tr_ren φ : forall ξ, tr (iren ξ φ) = renf ξ (tr φ).
Proof. induction φ; intros; cbn; f_equal; auto. Qed.

Lemma tr_inst φ n : tr (iinst φ n) = inst (tr φ) (tvar n).
Proof. unfold iinst, inst. rewrite tr_ren. apply ren_subst. intros [|k]; reflexivity. Qed.

Lemma tr_ish φ : tr (ish φ) = shf (tr φ).
Proof. apply tr_ren. Qed.

Lemma prv_shift T (HC : closed_sub T) Γ φ : prv T Γ φ -> prv T (map shf Γ) (shf φ).
Proof.
  intros H. pose proof (prv_subst T HC _ _ H (fun n => tvar (S n))) as K.
  rewrite renf_as_subf. replace (map shf Γ) with (map (subf (fun n => tvar (S n))) Γ); [exact K|].
  apply map_ext. intros; symmetry; apply renf_as_subf.
Qed.

Lemma inst_up_shf φ : inst (renf (upr S) φ) x0 = φ.
Proof.
  unfold inst. rewrite subf_renf. apply subst_id. intros [|n]; reflexivity.
Qed.

(** ** Lemma 11 *)

Section L11.

Local Notation "Γ ⊢m φ" := (prv IZFm Γ φ) (at level 70).

Lemma ups_eqv Γ σ τ : (forall n, Γ ⊢m fEqv (σ n) (τ n)) -> forall n, map shf Γ ⊢m fEqv (ups σ n) (ups τ n).
Proof.
  intros H [|n]; cbn; [apply eqv_refl_t|]. apply (prv_shift _ IZFm_closed _ _ (H n)).
Qed.

Lemma lemma11_imp φ : forall Γ σ τ, (forall n, Γ ⊢m fEqv (σ n) (τ n)) ->
  Γ ⊢m fImp (subf σ (tr φ)) (subf τ (tr φ)).
Proof.
  induction φ; intros Γ σ τ H; cbn.
  - apply p_impI, p_topI.
  - apply p_impI. hyp.
  - apply p_impI. apply p_andI.
    + eapply p_impE; [apply IHφ1; intros; apply p_wk, H|]. eapply p_andE1. hyp.
    + eapply p_impE; [apply IHφ2; intros; apply p_wk, H|]. eapply p_andE2. hyp.
  - apply p_impI. eapply p_orE; [hyp| |].
    + apply p_orI1. eapply p_impE; [apply IHφ1; intros; apply p_wk, p_wk, H|]. hyp.
    + apply p_orI2. eapply p_impE; [apply IHφ2; intros; apply p_wk, p_wk, H|]. hyp.
  - apply p_impI, p_impI.
    eapply p_impE; [apply IHφ2; intros; apply p_wk, p_wk, H|].
    eapply p_impE; [apply p_ax; right; left; reflexivity|].
    eapply p_impE; [apply IHφ1; intros; apply eqv_sym_t, p_wk, p_wk, H|]. hyp.
  - apply p_impI, p_allI.
    eapply p_impE; [apply IHφ; apply (ups_eqv (fAll (subf (ups σ) (tr φ)) :: Γ)); intros; apply p_wk, H|].
    apply (p_allE' _ _ (renf (upr S) (subf (ups σ) (tr φ))) x0); [symmetry; apply inst_up_shf|].
    apply p_ax. left. reflexivity.
  - apply p_impI. eapply p_exE; [hyp|]. cbn.
    apply (p_exI _ _ _ x0). rewrite inst_up_shf.
    eapply p_impE; [apply IHφ; intros n; apply p_wk; apply (ups_eqv (fEx (subf (ups σ) (tr φ)) :: Γ)); intros; apply p_wk, H|]. hyp.
  - apply p_impI. lem mem_cong (sl [σ x; τ x; σ y; τ y]); try apply p_wk, H. hyp.
  - apply p_impI. lem sub_cong (sl [σ x; τ x; σ y; τ y]); try apply p_wk, H. hyp.
  - apply p_impI. lem eqv_cong (sl [σ x; τ x; σ y; τ y]); try apply p_wk, H. hyp.
Qed.

(** The statement of the paper: if x⃗ ≃ y⃗, then φ(x⃗) ⇔ φ(y⃗). *)
Theorem lemma11 φ Γ σ τ : (forall n, Γ ⊢m fEqv (σ n) (τ n)) ->
  Γ ⊢m fIff (subf σ (tr φ)) (subf τ (tr φ)).
Proof.
  intros H. apply p_andI; apply lemma11_imp; [exact H|]. intros n; apply eqv_sym_t, H.
Qed.

(** Usable form: transport a translated formula along ≃. *)
Lemma l11_conv Γ φ σ τ G : (forall n, Γ ⊢m fEqv (σ n) (τ n)) -> G = subf τ (tr φ) ->
  Γ ⊢m subf σ (tr φ) -> Γ ⊢m G.
Proof. intros H -> K. eapply p_impE; [apply lemma11_imp, H|exact K]. Qed.

End L11.
