(** * Theorem 17: IZF⁺ε is a conservative extension of IZF

    The translation T (Graph.v) sends every derivation of IZF⁺ε to a
    derivation of IZF ([sound17]): terms have unique values ([HED],
    Repl.v), the translated axioms are theorems of IZF ([HAX], Ax17.v),
    and the rules are preserved. On formulas of L_IZF (embedded by [tr],
    Extension.v), T is the identity up to equivalence ([T_tr]). *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax Deriv Theories ISyntax ILogic Graph GSubst ED Repl Ax17 Extension Thm12.

Theorem sound17 Γ φ : prv IZFp Γ φ -> forall ρ, map (fun A => T A ρ) Γ ⊢i T φ ρ.
Proof.
  induction 1; intros ρ.
  - apply i_ax. apply (in_map (fun A => T A ρ)). exact H.
  - apply HAX, H.
  - apply i_topI.
  - apply i_botE, IHprv.
  - apply i_andI; auto.
  - eapply i_andE1; apply IHprv.
  - eapply i_andE2; apply IHprv.
  - apply i_orI1; auto.
  - apply i_orI2; auto.
  - eapply i_orE; [apply IHprv1|apply IHprv2|apply IHprv3].
  - apply i_impI, IHprv.
  - eapply i_impE; [apply IHprv1|apply IHprv2].
  - apply i_allI. rewrite <- Tmap_shf. apply IHprv.
  - apply (with_val _ t ρ). rewrite Tiren.
    eapply ii_r; [apply inst_T; apply i_ax; left; reflexivity|].
    rewrite <- T_inst_v. apply i_allE.
    apply (i_conv _ (ish (T (fAll φ) ρ))); [cbn; rewrite Tiren; f_equal; apply (proj2 GT_ext); pwsolve|].
    apply i_wk, iprv_sh, IHprv.
  - apply (with_val _ t ρ). cbn [iren]. apply (i_exI _ _ _ 0). rewrite ii_inst.
    eapply ii_l; [apply inst_T; apply i_ax; left; reflexivity|].
    apply (i_conv _ (iren S (T (inst φ t) ρ))); [rewrite Tiren; reflexivity|]. apply i_wk, iprv_sh, IHprv.
  - apply (i_exE _ _ (T φ (0 .: sh 1 ρ))); [apply IHprv1|]. rewrite Tiren.
    apply (i_conv _ (T (shf ψ) (0 .: sh 1 ρ))); [apply (proj2 GT_ren); intros; reflexivity|].
    rewrite <- Tmap_shf. apply (IHprv2 (0 .: sh 1 ρ)).
  - apply (with_val _ t ρ). apply (i_conv _ (T (fEq t t) (sh 1 ρ))); [rewrite Tiren; reflexivity|].
    eapply ii_r; [apply (atom_char _ iEq); [reflexivity|apply i_ax; left; reflexivity|apply i_ax; left; reflexivity]|apply i_refl].
  - apply (with_val _ s ρ). apply (i_conv _ (T (inst φ t) (sh 1 ρ))); [rewrite Tiren; reflexivity|].
    apply (with_val _ t (sh 1 ρ)). apply (i_conv _ (T (inst φ t) (sh 2 ρ))); [rewrite Tiren; reflexivity|].
    assert (Ds : D t (sh 1 (sh 1 ρ)) 0 :: map ish (D s (sh 1 ρ) 0 :: map ish (map (fun A => T A ρ) Γ)) ⊢i D s (sh 2 ρ) 1).
    { apply i_wk. apply (i_conv _ (iren S (D s (sh 1 ρ) 0))); [rewrite Diren; reflexivity|]. apply i_ax; left; reflexivity. }
    assert (Dt : D t (sh 1 (sh 1 ρ)) 0 :: map ish (D s (sh 1 ρ) 0 :: map ish (map (fun A => T A ρ) Γ)) ⊢i D t (sh 2 ρ) 0)
      by (apply i_ax; left; reflexivity).
    assert (Sh : forall A, map (fun A => T A ρ) Γ ⊢i T A ρ ->
               D t (sh 1 (sh 1 ρ)) 0 :: map ish (D s (sh 1 ρ) 0 :: map ish (map (fun A => T A ρ) Γ)) ⊢i T A (sh 2 ρ)).
    { intros A HA. apply i_wk. apply (i_conv _ (iren S (iren S (T A ρ)))); [rewrite !Tiren; reflexivity|].
      apply iprv_sh, i_wk, iprv_sh, HA. }
    eapply ii_r; [apply inst_T, Dt|].
    apply (i_conv _ (iren (0 .: fun k => k) (T φ (0 .: sh 3 ρ)))); [rewrite Tiren; apply (proj2 GT_ext); pwsolve|].
    apply (i_tr _ _ 1 0).
    + eapply ii_l; [apply (atom_char _ iEq); [reflexivity|exact Ds|exact Dt]|]. exact (Sh (fEq s t) (IHprv1 ρ)).
    + apply (i_conv _ (T φ (1 .: sh 2 ρ))); [rewrite Tiren; apply (proj2 GT_ext); pwsolve|].
      eapply ii_l; [apply inst_T, Ds|]. exact (Sh (inst φ s) (IHprv2 ρ)).
Qed.


(** ** Round trip on the formulas of L_IZF *)

Lemma T_tr φ : forall Γ ρ, Γ ⊢i iIff (T (tr φ) ρ) (iren ρ φ).
Proof.
  induction φ; intros Γ ρ; cbn [tr T iren].
  - apply ii_refl.
  - apply ii_refl.
  - apply ii_and; auto.
  - apply ii_or; auto.
  - apply ii_imp; auto.
  - apply ii_all. rewrite (iren_ext φ (upr ρ) (0 .: sh 1 ρ)) by (intros [|n]; reflexivity). apply IHφ.
  - apply ii_ex. rewrite (iren_ext φ (upr ρ) (0 .: sh 1 ρ)) by (intros [|n]; reflexivity). apply IHφ.
  - apply atom_char; [reflexivity|exact (D_var' _ x ρ)|exact (D_var' _ y ρ)].
  - apply atom_char; [reflexivity|exact (D_var' _ x ρ)|exact (D_var' _ y ρ)].
  - apply atom_char; [reflexivity|exact (D_var' _ x ρ)|exact (D_var' _ y ρ)].
Qed.

Lemma T_tr_id Γ φ : Γ ⊢i iIff (T (tr φ) (fun k => k)) φ.
Proof. eapply i_conv; [|apply (T_tr φ Γ (fun k => k))]. rewrite iren_id by reflexivity. reflexivity. Qed.

(** ** The theorem *)

Theorem thm17 Γ φ : prv IZFp (map tr Γ) (tr φ) -> iprv IZF Γ φ.
Proof.
  intros H. pose proof (sound17 _ _ H (fun k => k)) as K.
  eapply ii_l; [apply T_tr_id|]. eapply i_cuts; [exact K|].
  intros χ Hχ. rewrite map_map in Hχ. apply in_map_iff in Hχ as (A & <- & HA).
  eapply ii_r; [apply T_tr_id|]. apply i_ax, HA.
Qed.

Corollary thm17_closed φ : prv IZFp [] (tr φ) -> iprv IZF [] φ.
Proof. apply (thm17 []). Qed.

(** Hence IZFε and IZF⁻ε are also conservative over IZF and, with
    Theorem 12, prove exactly the same formulas of L_IZF. *)
Corollary conservative_IZFe Γ φ : prv IZFe (map tr Γ) (tr φ) -> iprv IZF Γ φ.
Proof. intros H. apply thm17. eapply prv_mono; [exact P_base|exact H]. Qed.

Corollary conservative_IZFm Γ φ : prv IZFm (map tr Γ) (tr φ) -> iprv IZF Γ φ.
Proof. intros H. apply thm17. eapply prv_mono; [exact ext_mp|exact H]. Qed.

Corollary IZFm_iff Γ φ : iprv IZF Γ φ <-> prv IZFm (map tr Γ) (tr φ).
Proof. split; [apply thm12|apply conservative_IZFm]. Qed.

Corollary IZFe_iff Γ φ : iprv IZF Γ φ <-> prv IZFe (map tr Γ) (tr φ).
Proof.
  split; [|apply conservative_IZFe]. intros H. eapply prv_mono; [exact E_base|apply thm12, H].
Qed.

Corollary IZFp_iff Γ φ : iprv IZF Γ φ <-> prv IZFp (map tr Γ) (tr φ).
Proof.
  split; [|apply thm17]. intros H. eapply prv_mono; [exact ext_mp|apply thm12, H].
Qed.
