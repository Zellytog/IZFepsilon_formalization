(** * IZF in its own language L_IZF = {∈, ⊆} (with =)

    The terms of L_IZF are just variables: a formula is a tree whose atoms
    carry de Bruijn indices, and the only substitution needed is
    renaming.

    Presentation choices (Section 3 of the paper): weak power set and weak
    collection; ⊆ is a symbol defined by its axiom; infinity is stated
    relationally (∅ ∈ w and x ∈ w ⇒ x ∪ {x} ∈ w). *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax.

Inductive iform : Type :=
| iTop | iBot
| iAnd (φ ψ : iform) | iOr (φ ψ : iform) | iImp (φ ψ : iform)
| iAll (φ : iform) | iEx (φ : iform)
| iMem (x y : nat) | iSub (x y : nat) | iEq (x y : nat).

Notation iIff φ ψ := (iAnd (iImp φ ψ) (iImp ψ φ)).
Notation iNot φ := (iImp φ iBot).

Fixpoint iren (ξ : nat -> nat) (φ : iform) : iform :=
  match φ with
  | iTop => iTop | iBot => iBot
  | iAnd φ ψ => iAnd (iren ξ φ) (iren ξ ψ)
  | iOr φ ψ => iOr (iren ξ φ) (iren ξ ψ)
  | iImp φ ψ => iImp (iren ξ φ) (iren ξ ψ)
  | iAll φ => iAll (iren (upr ξ) φ)
  | iEx φ => iEx (iren (upr ξ) φ)
  | iMem x y => iMem (ξ x) (ξ y)
  | iSub x y => iSub (ξ x) (ξ y)
  | iEq x y => iEq (ξ x) (ξ y)
  end.

Notation ish := (iren S).

Definition iinst (φ : iform) (n : nat) : iform := iren (n .: fun k => k) φ.

Lemma iren_ext φ : forall ξ ξ', (forall n, ξ n = ξ' n) -> iren ξ φ = iren ξ' φ.
Proof. induction φ; intros; cbn; f_equal; eauto using upr_ext. Qed.

Lemma iren_comp φ : forall ξ ζ θ, (forall n, θ n = ξ (ζ n)) -> iren ξ (iren ζ φ) = iren θ φ.
Proof.
  induction φ; intros; cbn; f_equal; try rewrite H; auto; try (apply IHφ || apply IHφ1 || apply IHφ2); auto.
  all: intros [|n]; cbn; [reflexivity|rewrite H; reflexivity].
Qed.

Lemma iren_id φ : forall ξ, (forall n, ξ n = n) -> iren ξ φ = φ.
Proof. induction φ; intros; cbn; f_equal; rewrite ?H; auto; apply IHφ; intros [|n]; cbn; congruence. Qed.

Lemma iinst_ish φ n : iinst (ish φ) n = φ.
Proof. unfold iinst. rewrite (iren_comp _ _ _ (fun k => k)) by reflexivity. apply iren_id; reflexivity. Qed.

Lemma iinst_iren ξ φ n : iren ξ (iinst φ n) = iinst (iren (upr ξ) φ) (ξ n).
Proof.
  unfold iinst. rewrite (iren_comp _ _ _ (ξ n .: ξ)) by (intros [|k]; reflexivity).
  rewrite (iren_comp _ _ _ (ξ n .: ξ)) by (intros [|k]; reflexivity). reflexivity.
Qed.

Lemma ish_iren ξ φ : ish (iren ξ φ) = iren (upr ξ) (ish φ).
Proof.
  rewrite (iren_comp _ _ _ (fun k => S (ξ k))) by reflexivity.
  rewrite (iren_comp _ _ _ (fun k => S (ξ k))) by reflexivity. reflexivity.
Qed.

(** ** Natural deduction *)

Section IPrv.

Context (T : iform -> Prop).

Inductive iprv : list iform -> iform -> Prop :=
| i_ax Γ φ : In φ Γ -> iprv Γ φ
| i_th Γ φ : T φ -> iprv Γ φ
| i_topI Γ : iprv Γ iTop
| i_botE Γ φ : iprv Γ iBot -> iprv Γ φ
| i_andI Γ φ ψ : iprv Γ φ -> iprv Γ ψ -> iprv Γ (iAnd φ ψ)
| i_andE1 Γ φ ψ : iprv Γ (iAnd φ ψ) -> iprv Γ φ
| i_andE2 Γ φ ψ : iprv Γ (iAnd φ ψ) -> iprv Γ ψ
| i_orI1 Γ φ ψ : iprv Γ φ -> iprv Γ (iOr φ ψ)
| i_orI2 Γ φ ψ : iprv Γ ψ -> iprv Γ (iOr φ ψ)
| i_orE Γ φ ψ χ : iprv Γ (iOr φ ψ) -> iprv (φ :: Γ) χ -> iprv (ψ :: Γ) χ -> iprv Γ χ
| i_impI Γ φ ψ : iprv (φ :: Γ) ψ -> iprv Γ (iImp φ ψ)
| i_impE Γ φ ψ : iprv Γ (iImp φ ψ) -> iprv Γ φ -> iprv Γ ψ
| i_allI Γ φ : iprv (map ish Γ) φ -> iprv Γ (iAll φ)
| i_allE Γ φ n : iprv Γ (iAll φ) -> iprv Γ (iinst φ n)
| i_exI Γ φ n : iprv Γ (iinst φ n) -> iprv Γ (iEx φ)
| i_exE Γ φ ψ : iprv Γ (iEx φ) -> iprv (φ :: map ish Γ) (ish ψ) -> iprv Γ ψ
| i_refl Γ n : iprv Γ (iEq n n)
| i_leib Γ φ m n : iprv Γ (iEq m n) -> iprv Γ (iinst φ m) -> iprv Γ (iinst φ n).

Lemma iprv_weak Γ φ : iprv Γ φ -> forall Γ', incl Γ Γ' -> iprv Γ' φ.
Proof.
  induction 1; intros Γ' Hi; try (econstructor; eauto; fail).
  - eapply i_orE; [eauto|apply IHiprv2|apply IHiprv3]; apply incl_cons; auto using in_eq, incl_tl.
  - apply i_impI, IHiprv. apply incl_cons; auto using in_eq, incl_tl.
  - apply i_allI, IHiprv. apply incl_map, Hi.
  - eapply i_exE; [eauto|]. apply IHiprv2. apply incl_cons; [apply in_eq|]. apply incl_tl, incl_map, Hi.
Qed.

Definition iclosed := forall φ ξ, T φ -> T (iren ξ φ).

Lemma iprv_ren (HT : iclosed) Γ φ : iprv Γ φ -> forall ξ, iprv (map (iren ξ) Γ) (iren ξ φ).
Proof.
  assert (M : forall ξ Γ, map (iren (upr ξ)) (map ish Γ) = map ish (map (iren ξ) Γ)).
  { intros ξ Δ. rewrite !map_map. apply map_ext. intros; symmetry; apply ish_iren. }
  induction 1; intros ξ; cbn.
  all: try solve [econstructor; eauto].
  all: try solve [apply i_ax, in_map; assumption].
  all: try solve [apply i_th, HT; assumption].
  all: try solve [apply i_allI; rewrite <- M; auto].
  all: try solve [rewrite iinst_iren; apply i_allE; auto].
  all: try solve [eapply i_exI; rewrite <- iinst_iren; eauto].
  all: try solve [rewrite iinst_iren; eapply i_leib; [eauto|rewrite <- iinst_iren; eauto]].
  eapply i_exE; [apply IHiprv1|]. specialize (IHiprv2 (upr ξ)). cbn in IHiprv2.
  rewrite M, <- ish_iren in IHiprv2. exact IHiprv2.
Qed.

Lemma i_cut Γ A B : iprv Γ A -> iprv (A :: Γ) B -> iprv Γ B.
Proof. intros H1 H2. eapply i_impE; [apply i_impI, H2|exact H1]. Qed.

Lemma i_nth Γ n φ : nth_error Γ n = Some φ -> iprv Γ φ.
Proof. intros H. apply i_ax. eapply nth_error_In, H. Qed.

Lemma i_wk Γ A φ : iprv Γ φ -> iprv (A :: Γ) φ.
Proof. intros H. eapply iprv_weak; [exact H|]. apply incl_tl, incl_refl. Qed.

Lemma i_spec Γ n t φ ψ : nth_error Γ n = Some (iAll φ) -> iprv (iinst φ t :: Γ) ψ -> iprv Γ ψ.
Proof. intros H K. eapply i_cut; [|exact K]. apply i_allE, (i_nth _ _ _ H). Qed.

Lemma i_app Γ n A B : nth_error Γ n = Some (iImp A B) -> iprv Γ A -> iprv Γ B.
Proof. intros H K. eapply i_impE; [apply (i_nth _ _ _ H)|exact K]. Qed.

Lemma i_mp Γ n A B ψ : nth_error Γ n = Some (iImp A B) -> iprv Γ A -> iprv (B :: Γ) ψ -> iprv Γ ψ.
Proof. intros H K L. eapply i_cut; [|exact L]. eapply i_app; eauto. Qed.

Lemma i_dand Γ n A B ψ : nth_error Γ n = Some (iAnd A B) -> iprv (A :: B :: Γ) ψ -> iprv Γ ψ.
Proof.
  intros H K. pose proof (i_nth _ _ _ H) as Hn.
  eapply i_cut; [apply (i_andE2 _ _ _ Hn)|]. eapply i_cut; [apply i_wk, (i_andE1 _ _ _ Hn)|].
  eapply iprv_weak; [exact K|]. intros x [<-|[<-|Hx]]; [left|right; left|right; right]; auto.
Qed.

Lemma i_dor Γ n A B ψ : nth_error Γ n = Some (iOr A B) -> iprv (A :: Γ) ψ -> iprv (B :: Γ) ψ -> iprv Γ ψ.
Proof. intros H K L. eapply i_orE; [apply (i_nth _ _ _ H)|exact K|exact L]. Qed.

Lemma i_dex Γ n φ ψ : nth_error Γ n = Some (iEx φ) -> iprv (φ :: map ish Γ) (ish ψ) -> iprv Γ ψ.
Proof. intros H K. eapply i_exE; [apply (i_nth _ _ _ H)|exact K]. Qed.

Lemma i_iffI Γ A B : iprv (A :: Γ) B -> iprv (B :: Γ) A -> iprv Γ (iIff A B).
Proof. intros; apply i_andI; apply i_impI; assumption. Qed.

Lemma i_exI' Γ φ t ψ : ψ = iinst φ t -> iprv Γ ψ -> iprv Γ (iEx φ).
Proof. intros -> H. eapply i_exI, H. Qed.

Lemma i_cuts Γ Δ φ : iprv Δ φ -> (forall χ, In χ Δ -> iprv Γ χ) -> iprv Γ φ.
Proof.
  revert φ. induction Δ as [|A Δ IH]; intros φ H K.
  - eapply iprv_weak; [exact H|]. intros x [].
  - assert (H' : iprv Δ (iImp A φ)) by (apply i_impI, H).
    eapply i_impE; [apply IH; [exact H'|]|apply K, in_eq]. intros χ Hχ. apply K, in_cons, Hχ.
Qed.

Lemma i_use (HT : iclosed) Δ φ ξ Γ : iprv Δ φ -> (forall χ, In χ Δ -> iprv Γ (iren ξ χ)) -> iprv Γ (iren ξ φ).
Proof.
  intros H K. eapply i_cuts; [exact (iprv_ren HT _ _ H ξ)|].
  intros χ Hχ. apply in_map_iff in Hχ as (χ0 & <- & Hχ0). apply K, Hχ0.
Qed.

Lemma i_have (HT : iclosed) φ ξ Γ ψ : iprv [] φ -> iprv (iren ξ φ :: Γ) ψ -> iprv Γ ψ.
Proof. intros H K. eapply i_cut; [|exact K]. apply (i_use HT [] φ ξ); [exact H|intros _ []]. Qed.

End IPrv.

Definition il (l : list nat) : nat -> nat := fun n => nth n l (n - length l).

Ltac ihyp := apply i_ax; cbn; solve [repeat (first [left; reflexivity | right])].
Tactic Notation "iass" constr(n) := apply (i_nth _ _ n); reflexivity.
Tactic Notation "ispec" constr(n) constr(t) := eapply (i_spec _ _ n t); [reflexivity|cbn].
Tactic Notation "iapp" constr(n) := eapply (i_app _ _ n ); [reflexivity|cbn].
Tactic Notation "imp" constr(n) := eapply (i_mp _ _ n ); [reflexivity|cbn|cbn].
Tactic Notation "idand" constr(n) := eapply (i_dand _ _ n ); [reflexivity|cbn].
Tactic Notation "idor" constr(n) := eapply (i_dor _ _ n ); [reflexivity|cbn|cbn].
Tactic Notation "idex" constr(n) := eapply (i_dex _ _ n ); [reflexivity|cbn].
Ltac iintro_all := apply i_allI; cbn.
Tactic Notation "iexists" constr(t) := refine (i_exI' _ _ _ t _ _ _); [cbn; reflexivity|].
Tactic Notation "icut" constr(A) := refine (i_cut _ _ A _ _ _).

(** ** The axioms of IZF

    The free variables of an axiom are implicitly universal; schemes range
    over an arbitrary formula, whose free variables (other than the bound
    one) are the parameters. *)

Inductive IZF : iform -> Prop :=
| I_sub x y : IZF (iIff (iSub x y) (iAll (iImp (iMem 0 (S x)) (iMem 0 (S y)))))
| I_ext x y : IZF (iImp (iSub x y) (iImp (iSub y x) (iEq x y)))
| I_empty : IZF (iEx (iAll (iNot (iMem 0 1))))
| I_pair x y : IZF (iEx (iAll (iIff (iMem 0 1) (iOr (iEq 0 (S (S x))) (iEq 0 (S (S y)))))))
| I_union x : IZF (iEx (iAll (iIff (iMem 0 1) (iEx (iAnd (iMem 0 (S (S (S x)))) (iMem 1 0))))))
| I_inf : IZF (iEx (iAnd (iEx (iAnd (iMem 0 1) (iAll (iNot (iMem 0 1)))))
                         (iAll (iImp (iMem 0 1) (iEx (iAnd (iMem 0 2)
                            (iAll (iIff (iMem 0 1) (iOr (iMem 0 2) (iEq 0 2))))))))))
| I_wpow x : IZF (iEx (iAll (iEx (iAnd (iMem 0 2)
                    (iAll (iIff (iMem 0 1) (iAnd (iMem 0 (S (S (S (S x))))) (iMem 0 2))))))))
| I_sep φ y : IZF (iEx (iAll (iIff (iMem 0 1) (iAnd (iMem 0 (S (S y))) (iren (upr S) φ)))))
| I_coll ψ a : IZF (iImp (iAll (iImp (iMem 0 (S a)) (iEx ψ)))
                         (iEx (iAll (iImp (iMem 0 (S (S a))) (iEx (iAnd (iMem 0 2) (iren (upr (upr S)) ψ)))))))
| I_ind φ : IZF (iImp (iAll (iImp (iAll (iImp (iMem 0 1) (iren (upr S) φ))) φ)) (iAll φ)).

Lemma iren_swap φ ξ ζ ξ' ζ' : (forall n, ξ (ζ n) = ξ' (ζ' n)) -> iren ξ (iren ζ φ) = iren ξ' (iren ζ' φ).
Proof.
  intros H. rewrite (iren_comp φ ξ ζ (fun n => ξ (ζ n))) by reflexivity.
  rewrite (iren_comp φ ξ' ζ' (fun n => ξ (ζ n))) by (intros; apply H). reflexivity.
Qed.

(** IZF is closed under renaming. *)
Lemma IZF_closed : iclosed IZF.
Proof.
  intros φ ξ H. destruct H; cbn; try constructor.
  - rewrite (iren_swap φ _ (upr S) (upr S) (upr ξ)) by (intros [|n]; reflexivity). apply I_sep.
  - rewrite (iren_swap ψ _ (upr (upr S)) (upr (upr S)) (upr (upr ξ))) by (intros [|[|n]]; reflexivity). apply I_coll.
  - rewrite (iren_swap φ _ (upr S) (upr S) (upr ξ)) by (intros [|n]; reflexivity). apply I_ind.
Qed.
