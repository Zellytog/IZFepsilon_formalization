(** * Intuitionistic natural deduction for IZFε

    [prv T Γ φ]: φ is derivable from the hypotheses Γ and the axioms T.
    Free variables are implicitly universal: an axiom with free variables
    holds for all their values (theories are closed under substitution,
    [closed_sub]). Equality is Leibniz equality: reflexivity and transport
    along an arbitrary formula. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax.

Section Prv.

Context (T : form -> Prop).

Inductive prv : list form -> form -> Prop :=
| p_ax Γ φ : In φ Γ -> prv Γ φ
| p_th Γ φ : T φ -> prv Γ φ
| p_topI Γ : prv Γ fTop
| p_botE Γ φ : prv Γ fBot -> prv Γ φ
| p_andI Γ φ ψ : prv Γ φ -> prv Γ ψ -> prv Γ (fAnd φ ψ)
| p_andE1 Γ φ ψ : prv Γ (fAnd φ ψ) -> prv Γ φ
| p_andE2 Γ φ ψ : prv Γ (fAnd φ ψ) -> prv Γ ψ
| p_orI1 Γ φ ψ : prv Γ φ -> prv Γ (fOr φ ψ)
| p_orI2 Γ φ ψ : prv Γ ψ -> prv Γ (fOr φ ψ)
| p_orE Γ φ ψ χ : prv Γ (fOr φ ψ) -> prv (φ :: Γ) χ -> prv (ψ :: Γ) χ -> prv Γ χ
| p_impI Γ φ ψ : prv (φ :: Γ) ψ -> prv Γ (fImp φ ψ)
| p_impE Γ φ ψ : prv Γ (fImp φ ψ) -> prv Γ φ -> prv Γ ψ
| p_allI Γ φ : prv (map shf Γ) φ -> prv Γ (fAll φ)
| p_allE Γ φ t : prv Γ (fAll φ) -> prv Γ (inst φ t)
| p_exI Γ φ t : prv Γ (inst φ t) -> prv Γ (fEx φ)
| p_exE Γ φ ψ : prv Γ (fEx φ) -> prv (φ :: map shf Γ) (shf ψ) -> prv Γ ψ
| p_refl Γ t : prv Γ (fEq t t)
| p_leib Γ φ s t : prv Γ (fEq s t) -> prv Γ (inst φ s) -> prv Γ (inst φ t).

(** ** Weakening *)

Lemma prv_weak Γ φ : prv Γ φ -> forall Γ', incl Γ Γ' -> prv Γ' φ.
Proof.
  induction 1; intros Γ' Hi; try (econstructor; eauto; fail).
  - eapply p_orE; [eauto|apply IHprv2|apply IHprv3]; apply incl_cons; auto using in_eq, incl_tl.
  - apply p_impI, IHprv. apply incl_cons; auto using in_eq, incl_tl.
  - apply p_allI, IHprv. apply incl_map, Hi.
  - eapply p_exE; [eauto|]. apply IHprv2. apply incl_cons; [apply in_eq|]. apply incl_tl, incl_map, Hi.
Qed.

(** ** Substitution *)

Definition closed_sub := forall φ σ, T φ -> T (subf σ φ).

Lemma map_shf_subf σ Γ : map (subf (ups σ)) (map shf Γ) = map shf (map (subf σ) Γ).
Proof. rewrite !map_map. apply map_ext. intros φ. symmetry. apply shf_subf. Qed.

Lemma prv_subst (HT : closed_sub) Γ φ : prv Γ φ -> forall σ, prv (map (subf σ) Γ) (subf σ φ).
Proof.
  induction 1; intros σ; cbn.
  all: try solve [econstructor; eauto].
  all: try solve [apply p_ax, in_map; assumption].
  all: try solve [apply p_th, HT; assumption].
  all: try solve [apply p_allI; rewrite <- map_shf_subf; auto].
  all: try solve [rewrite inst_subf; apply p_allE; auto].
  all: try solve [eapply p_exI; rewrite <- inst_subf; eauto].
  all: try solve [rewrite inst_subf; eapply p_leib; [eauto|rewrite <- inst_subf; eauto]].
  eapply p_exE; [apply IHprv1|]. specialize (IHprv2 (ups σ)). cbn in IHprv2.
  rewrite map_shf_subf, <- shf_subf in IHprv2. exact IHprv2.
Qed.

(** ** Derived rules, for the proof mode *)

Lemma p_cut Γ A B : prv Γ A -> prv (A :: Γ) B -> prv Γ B.
Proof. intros H1 H2. eapply p_impE; [apply p_impI, H2|exact H1]. Qed.

Lemma p_nth Γ n φ : nth_error Γ n = Some φ -> prv Γ φ.
Proof. intros H. apply p_ax. eapply nth_error_In, H. Qed.

Lemma p_wk Γ A φ : prv Γ φ -> prv (A :: Γ) φ.
Proof. intros H. eapply prv_weak; [exact H|]. apply incl_tl, incl_refl. Qed.

Lemma p_spec Γ n t φ ψ : nth_error Γ n = Some (fAll φ) -> prv (inst φ t :: Γ) ψ -> prv Γ ψ.
Proof. intros H K. eapply p_cut; [|exact K]. apply p_allE, (p_nth _ _ _ H). Qed.

Lemma p_app Γ n A B : nth_error Γ n = Some (fImp A B) -> prv Γ A -> prv Γ B.
Proof. intros H K. eapply p_impE; [apply (p_nth _ _ _ H)|exact K]. Qed.

Lemma p_mp Γ n A B ψ : nth_error Γ n = Some (fImp A B) -> prv Γ A -> prv (B :: Γ) ψ -> prv Γ ψ.
Proof. intros H K L. eapply p_cut; [|exact L]. eapply p_app; eauto. Qed.

Lemma p_dand Γ n A B ψ : nth_error Γ n = Some (fAnd A B) -> prv (A :: B :: Γ) ψ -> prv Γ ψ.
Proof.
  intros H K. pose proof (p_nth _ _ _ H) as Hn.
  eapply p_cut; [apply (p_andE2 _ _ _ Hn)|]. eapply p_cut; [apply p_wk, (p_andE1 _ _ _ Hn)|].
  eapply prv_weak; [exact K|]. intros x [<-|[<-|Hx]]; [left|right; left|right; right]; auto.
Qed.

Lemma p_dor Γ n A B ψ : nth_error Γ n = Some (fOr A B) -> prv (A :: Γ) ψ -> prv (B :: Γ) ψ -> prv Γ ψ.
Proof. intros H K L. eapply p_orE; [apply (p_nth _ _ _ H)|exact K|exact L]. Qed.

Lemma p_dex Γ n φ ψ : nth_error Γ n = Some (fEx φ) -> prv (φ :: map shf Γ) (shf ψ) -> prv Γ ψ.
Proof. intros H K. eapply p_exE; [apply (p_nth _ _ _ H)|exact K]. Qed.

Lemma p_iff1 Γ A B : prv Γ (fIff A B) -> prv Γ A -> prv Γ B.
Proof. intros H K. eapply p_impE; [eapply p_andE1, H|exact K]. Qed.

Lemma p_iff2 Γ A B : prv Γ (fIff A B) -> prv Γ B -> prv Γ A.
Proof. intros H K. eapply p_impE; [eapply p_andE2, H|exact K]. Qed.

Lemma p_iffI Γ A B : prv (A :: Γ) B -> prv (B :: Γ) A -> prv Γ (fIff A B).
Proof. intros; apply p_andI; apply p_impI; assumption. Qed.

Lemma p_exI' Γ φ t ψ : ψ = inst φ t -> prv Γ ψ -> prv Γ (fEx φ).
Proof. intros -> H. eapply p_exI, H. Qed.

Lemma p_allE' Γ φ t ψ : ψ = inst φ t -> prv Γ (fAll φ) -> prv Γ ψ.
Proof. intros -> H. apply p_allE, H. Qed.


Lemma p_cuts Γ Δ φ : prv Δ φ -> (forall χ, In χ Δ -> prv Γ χ) -> prv Γ φ.
Proof.
  revert φ. induction Δ as [|A Δ IH]; intros φ H K.
  - eapply prv_weak; [exact H|]. intros x [].
  - assert (H' : prv Δ (fImp A φ)) by (apply p_impI, H).
    eapply p_impE; [apply IH; [exact H'|]|apply K, in_eq]. intros χ Hχ. apply K, in_cons, Hχ.
Qed.

(** Using an open lemma: its free variables are instantiated by σ. *)
Lemma p_use (HT : closed_sub) Δ φ σ Γ : prv Δ φ -> (forall χ, In χ Δ -> prv Γ (subf σ χ)) -> prv Γ (subf σ φ).
Proof.
  intros H K. eapply p_cuts; [exact (prv_subst HT _ _ H σ)|].
  intros χ Hχ. apply in_map_iff in Hχ as (χ0 & <- & Hχ0). apply K, Hχ0.
Qed.

Lemma p_have (HT : closed_sub) φ σ Γ ψ : prv [] φ -> prv (subf σ φ :: Γ) ψ -> prv Γ ψ.
Proof. intros H K. eapply p_cut; [|exact K]. apply (p_use HT [] φ σ); [exact H|intros _ []]. Qed.

End Prv.

(** A substitution given by a finite list of terms. *)
Definition sl (l : list term) : nat -> term := fun n => nth n l (tvar (n - length l)).

(** Monotonicity in the theory. *)
Lemma prv_mono (T T' : form -> Prop) Γ φ : (forall ψ, T ψ -> T' ψ) -> prv T Γ φ -> prv T' Γ φ.
Proof. intros HT H. induction H; solve [econstructor; eauto]. Qed.

(** ** The proof mode

    Hypotheses are referred to by their rank in Γ (0 = the most recent
    one). The tactics compute substitutions with [cbn]. *)

Ltac hyp := apply p_ax; cbn; solve [repeat (first [left; reflexivity | right])].
Tactic Notation "ass" constr(n) := apply (p_nth _ _ n); reflexivity.
Tactic Notation "spec" constr(n) constr(t) := eapply (p_spec _ _ n t); [reflexivity|cbn].
Tactic Notation "app" constr(n) := eapply (p_app _ _ n ); [reflexivity|cbn].
Tactic Notation "mp" constr(n) := eapply (p_mp _ _ n ); [reflexivity|cbn|cbn].
Tactic Notation "dand" constr(n) := eapply (p_dand _ _ n ); [reflexivity|cbn].
Tactic Notation "dor" constr(n) := eapply (p_dor _ _ n ); [reflexivity|cbn|cbn].
Tactic Notation "dex" constr(n) := eapply (p_dex _ _ n ); [reflexivity|cbn].
Ltac intro_all := apply p_allI; cbn.
Ltac intro_imp := apply p_impI.
Ltac intros_imp := repeat apply p_impI.
Ltac split_and := apply p_andI.
Ltac split_iff := apply p_iffI.
Tactic Notation "exists_" constr(t) := refine (p_exI' _ _ _ t _ _ _); [cbn; reflexivity|].
Tactic Notation "cut_" constr(A) := refine (p_cut _ _ A _ _ _).
