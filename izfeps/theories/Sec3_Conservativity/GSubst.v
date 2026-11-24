(** * The translation commutes with substitution (up to equivalence in IZF)

    D(t, ρ, v) ≜ ∀z. G(t, ρ, z) ⇔ z = v: "v is the value of t". If each
    σ(n) has value y(n), then φ[σ] translated with ρ is equivalent to φ
    translated with y. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax ISyntax ILogic Graph.

Definition D (t : term) (ρ : nat -> nat) (v : nat) : iform := iAll (iIff (G t (sh 1 ρ) 0) (iEq 0 (S v))).

Definition Hyp (Γ : list iform) (σ : nat -> term) (ρ y : nat -> nat) : Prop := forall n, Γ ⊢i D (σ n) ρ (y n).

Lemma D_ren ξ t ρ v : iren ξ (D t ρ v) = D t (fun k => ξ (ρ k)) (ξ v).
Proof.
  unfold D. cbn. rewrite (proj1 GT_iren t (upr ξ) (sh 1 ρ) (sh 1 (fun k => ξ (ρ k))) 0) by (intros; reflexivity).
  reflexivity.
Qed.

Lemma D_use Γ t ρ v z : Γ ⊢i D t ρ v -> Γ ⊢i iIff (G t ρ z) (iEq z v).
Proof.
  intros H. apply (i_conv _ (iinst (iIff (G t (sh 1 ρ) 0) (iEq 0 (S v))) z)); [|apply i_allE, H].
  unfold iinst. cbn. rewrite (proj1 GT_iren t _ (sh 1 ρ) ρ 0) by (intros; reflexivity). reflexivity.
Qed.

Lemma Hyp_sh Γ σ ρ y : Hyp Γ σ ρ y -> Hyp (map ish Γ) σ (sh 1 ρ) (sh 1 y).
Proof. intros H n. change (D (σ n) (sh 1 ρ) (sh 1 y n)) with (D (σ n) (fun k => S (ρ k)) (S (y n))). rewrite <- D_ren. apply iprv_sh, H. Qed.

Lemma Hyp_shk k : forall Γ σ ρ y, Hyp Γ σ ρ y -> Hyp (Nat.iter k (map ish) Γ) σ (sh k ρ) (sh k y).
Proof.
  induction k as [|k IH]; intros Γ σ ρ y H n; [exact (H n)|].
  apply (Hyp_sh _ _ (sh k ρ) (sh k y)), IH, H.
Qed.

Lemma Hyp_up Γ σ ρ y j : Hyp Γ σ ρ y -> Hyp Γ (ups σ) (j .: ρ) (j .: y).
Proof.
  intros H [|n]; cbn.
  - unfold D. cbn. iintro_all. apply ii_refl.
  - unfold D. cbn. rewrite (proj1 GT_ren (σ n) S (sh 1 (j .: ρ)) (sh 1 ρ)) by (intros; reflexivity). apply H.
Qed.

Ltac iicong := repeat (first [apply ii_refl | apply ii_and | apply ii_or | apply ii_imp | apply ii_all | apply ii_ex]).
Ltac solve_hyp := repeat (first [apply Hyp_up | apply (Hyp_shk 1) | apply (Hyp_shk 2) | apply (Hyp_shk 3)
                                  | apply (Hyp_shk 4) | apply (Hyp_shk 5)]);
  match goal with HH : Hyp _ _ _ _ |- _ => exact HH end.

Lemma GT_subst :
  (forall t σ ρ y Γ, Hyp Γ σ ρ y -> forall z, Γ ⊢i iIff (G (subt σ t) ρ z) (G t y z)) /\
  (forall φ σ ρ y Γ, Hyp Γ σ ρ y -> Γ ⊢i iIff (T (subf σ φ) ρ) (T φ y)).
Proof.
  apply (syn_ind (fun t => forall σ ρ y Γ, Hyp Γ σ ρ y -> forall z, Γ ⊢i iIff (G (subt σ t) ρ z) (G t y z))
                 (fun φ => forall σ ρ y Γ, Hyp Γ σ ρ y -> Γ ⊢i iIff (T (subf σ φ) ρ) (T φ y)));
    intros; cbn; unfold atom; iicong.
  1: apply D_use, H.
  all: match goal with IH : _ |- _ => solve [apply IH; solve_hyp] end.
Qed.

