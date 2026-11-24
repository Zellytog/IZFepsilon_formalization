(** * Theorem 12: IZF⁻ε ⊢ IZF^ε

    Each axiom of IZF, once translated, is a theorem of IZF⁻ε; hence the
    translation sends derivations of IZF to derivations of IZF⁻ε (the
    Leibniz rule for ≃ is Lemma 11). *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax Deriv ISyntax Theories Basic Extension.

Local Notation "Γ ⊢m φ" := (prv IZFm Γ φ) (at level 70).

(** ** Lemmas on the constructions *)

Lemma empty_mem : [fMem x0 tempty] ⊢m fBot.
Proof.
  axm (M_mem x0 tempty). iffm 0; [hyp|]. dex 0. dand 0.
  axm (M_empty x0). app 0. hyp.
Qed.

(** z ∈ {x, y} ⇔ z ≃ x ∨ z ≃ y   (z = 0, x = 1, y = 2) *)
Lemma pair_mem : [] ⊢m fIff (fMem x0 (tpair x1 x2)) (fOr (fEqv x0 x1) (fEqv x0 x2)).
Proof.
  split_iff.
  - axm (M_mem x0 (tpair x1 x2)). iffm 0; [hyp|]. dex 0. dand 0.
    (* z' = 0, z = 1, x = 2, y = 3 *)
    axm (M_pair x2 x3 x0). iffm 0; [hyp|]. dor 0.
    + apply p_orI1. rew (fEqv x2 x0) x0 x2; hyp.
    + apply p_orI2. rew (fEqv x2 x0) x0 x3; hyp.
  - axm (M_mem x0 (tpair x1 x2)). iffr 0. dor 1.
    + exists_ x1. split_and; [hyp|]. axm (M_pair x1 x2 x1). iffr 0. apply p_orI1, p_refl.
    + exists_ x2. split_and; [hyp|]. axm (M_pair x1 x2 x2). iffr 0. apply p_orI2, p_refl.
Qed.

(** z ∈ ⋃x ⇔ ∃y. y ∈ x ∧ z ∈ y   (z = 0, x = 1) *)
Lemma union_mem : [] ⊢m fIff (fMem x0 (tunion x1)) (fEx (fAnd (fMem x0 x2) (fMem x1 x0))).
Proof.
  split_iff.
  - axm (M_mem x0 (tunion x1)). iffm 0; [hyp|]. dex 0. dand 0.
    (* z' = 0, z = 1, x = 2 *)
    axm (M_union x2 x0). iffm 0; [hyp|]. dex 0. dand 0.
    (* a = 0, z' = 1, z = 2, x = 3 *)
    exists_ x0. split_and; [apply eps_mem_t; hyp|].
    axm (M_mem x2 x0). iffr 0. exists_ x1. split_and; hyp.
  - dex 0. dand 0.
    (* y = 0, z = 1, x = 2 *)
    axm (M_mem x0 x2). iffm 0; [hyp|]. dex 0. dand 0.
    (* y' = 0, y = 1, z = 2, x = 3 *)
    cut_ (fMem x2 x0); [lem mem_sub (sl [x2; x1; x0]); [hyp|lem eqv_l (sl [x1; x0]); hyp]|].
    axm (M_mem x2 x0). iffm 0; [hyp|]. dex 0. dand 0.
    (* z'' = 0, y' = 1, y = 2, z = 3, x = 4 *)
    axm (M_mem x3 (tunion x4)). iffr 0. exists_ x0. split_and; [hyp|].
    axm (M_union x4 x0). iffr 0. exists_ x1. split_and; hyp.
Qed.

(** z ∈ S(x) ⇔ z ∈ x ∨ z ≃ x   (z = 0, x = 1) *)
Lemma suc_mem : [] ⊢m fIff (fMem x0 (tsuc x1)) (fOr (fMem x0 x1) (fEqv x0 x1)).
Proof.
  unfold tsuc. haveL union_mem (sl [x0; tpair x1 (tpair x1 x1)]). split_iff.
  - iffm 1; [hyp|]. dex 0. dand 0.
    (* y = 0, z = 1, x = 2 *)
    haveL pair_mem (sl [x0; x2; tpair x2 x2]). iffm 0; [hyp|]. dor 0.
    + apply p_orI1. lem mem_cong (sl [x1; x1; x0; x2]); [lem eqv_refl (sl [x1])|hyp|hyp].
    + apply p_orI2.
      cut_ (fMem x1 (tpair x2 x2)); [lem mem_cong (sl [x1; x1; x0; tpair x2 x2]); [lem eqv_refl (sl [x1])|hyp|hyp]|].
      haveL pair_mem (sl [x1; x2; x2]). iffm 0; [hyp|]. dor 0; hyp.
  - iffr 1. dor 0.
    + exists_ x1. split_and; [|hyp].
      haveL pair_mem (sl [x1; x1; tpair x1 x1]). iffr 0. apply p_orI1. lem eqv_refl (sl [x1]).
    + exists_ (tpair x1 x1). split_and.
      * haveL pair_mem (sl [tpair x1 x1; x1; tpair x1 x1]). iffr 0. apply p_orI2. lem eqv_refl (sl [tpair x1 x1]).
      * haveL pair_mem (sl [x0; x1; x1]). iffr 0. apply p_orI1. hyp.
Qed.

(** The weak power set (a = 0, x = 1):
    ∃b. b ∈ 𝒫(x) ∧ ∀z. z ∈ b ⇔ z ∈ x ∧ z ∈ a. *)
Lemma wpow_core : [] ⊢m fEx (fAnd (fMem x0 (tpow x2)) (fAll (fIff (fMem x0 x1) (fAnd (fMem x0 x3) (fMem x0 x2))))).
Proof.
  axm (M_wpow x1 (tsep x1 (fMem x0 x1))). dex 0. dand 0.
  (* b = 0, a = 1, x = 2 *)
  exists_ x0. split_and; [apply eps_mem_t; hyp|]. intro_all.
  (* z = 0, b = 1, a = 2, x = 3 *)
  split_iff.
  - axm (M_mem x0 x1). iffm 0; [hyp|]. dex 0. dand 0.
    (* z' = 0, z = 1, b = 2, a = 3, x = 4 *)
    spec 7 x0. iffm 0; [hyp|]. dand 0.
    axm (M_sep (fMem x0 x4) x4 x0). iffm 0; [hyp|]. dand 0.
    split_and.
    + axm (M_mem x1 x4). iffr 0. exists_ x0. split_and; hyp.
    + lem mem_eqv_l (sl [x0; x1; x3]); [lem eqv_sym (sl [x1; x0]); hyp|hyp].
  - dand 0. axm (M_mem x0 x3). iffm 0; [hyp|]. dex 0. dand 0.
    (* z' = 0, z = 1, b = 2, a = 3, x = 4 *)
    cut_ (fMem x0 x3); [lem mem_eqv_l (sl [x1; x0; x3]); hyp|].
    cut_ (fEps x0 (tsep x4 (fMem x0 x4))); [axm (M_sep (fMem x0 x4) x4 x0); iffr 0; split_and; hyp|].
    spec 11 x0. axm (M_mem x1 x2). iffr 0. exists_ x0. split_and; [hyp|]. iffr 1. split_and; hyp.
Qed.

(** ** The axioms of IZF, translated, are theorems of IZF⁻ε *)

Theorem IZF_tr φ : IZF φ -> [] ⊢m tr φ.
Proof.
  intros H; destruct H; cbn; rewrite ?tr_ren.
  - (* ⊆ *) lem sub_iff (sl [tvar x; tvar y]).
  - (* extensionality *) intro_imp. intro_imp. lem eqv_intro (sl [tvar x; tvar y]); hyp.
  - (* ∅ *) exists_ tempty. intro_all. intro_imp. lem empty_mem (sl [x0]). hyp.
  - (* pairing *) exists_ (tpair (tvar x) (tvar y)). intro_all. lem pair_mem (sl [x0; tvar (S x); tvar (S y)]).
  - (* union *) exists_ (tunion (tvar x)). intro_all. lem union_mem (sl [x0; tvar (S x)]).
  - (* infinity *)
    exists_ tomega. split_and.
    + exists_ tempty. split_and.
      * apply eps_mem_t. axm (M_omega tempty). iffr 0. apply p_orI1, p_refl.
      * intro_all. intro_imp. lem empty_mem (sl [x0]). hyp.
    + intro_all. intro_imp.
      axm (M_mem x0 tomega). iffm 0; [hyp|]. dex 0. dand 0.
      (* x' = 0, x = 1 *)
      exists_ (tsuc x0). split_and.
      * apply eps_mem_t. axm (M_omega (tsuc x0)). iffr 0. apply p_orI2. exists_ x0. split_and; [hyp|apply p_refl].
      * intro_all.
        (* z = 0, x' = 1, x = 2 *)
        haveL suc_mem (sl [x0; x1]). split_iff.
        -- iffm 1; [hyp|]. dor 0.
           ++ apply p_orI1. lem mem_cong (sl [x0; x0; x1; x2]); [lem eqv_refl (sl [x0])|lem eqv_sym (sl [x2; x1]); hyp|hyp].
           ++ apply p_orI2. lem eqv_trans (sl [x0; x1; x2]); [hyp|lem eqv_sym (sl [x2; x1]); hyp].
        -- iffr 1. dor 0.
           ++ apply p_orI1. lem mem_cong (sl [x0; x0; x2; x1]); [lem eqv_refl (sl [x0])|hyp|hyp].
           ++ apply p_orI2. lem eqv_trans (sl [x0; x2; x1]); hyp.
  - (* weak power set *)
    exists_ (tpow (tvar x)). intro_all. lem wpow_core (sl [x0; tvar (S x)]).
  - (* separation *)
    exists_ (tsep (tvar y) (tr φ)). intro_all. split_iff.
    + axm (M_mem x0 (tsep (tvar (S y)) (renf (upr S) (tr φ)))). iffm 0; [hyp|]. dex 0. dand 0.
      axm (M_sep (renf (upr S) (renf (upr S) (tr φ))) (tvar (S (S y))) x0). iffm 0; [hyp|]. dand 0.
      split_and.
      * axm (M_mem x1 (tvar (S (S y)))). iffr 0. exists_ x0. split_and; hyp.
      * eapply (l11_conv _ φ (x0 .: fun k => tvar (S (S k))) (x1 .: fun k => tvar (S (S k)))).
        -- intros [|n]; cbn; [lem eqv_sym (sl [x1; x0]); hyp|apply eqv_refl_t].
        -- fnorm.
        -- apply (p_conv _ _ (inst (renf (upr S) (renf (upr S) (tr φ))) x0)); [fnorm|hyp].
    + dand 0. axm (M_mem x0 (tvar (S y))). iffm 0; [hyp|]. dex 0. dand 0.
      axm (M_mem x1 (tsep (tvar (S (S y))) (renf (upr S) (renf (upr S) (tr φ))))). iffr 0.
      exists_ x0. split_and; [hyp|].
      conv (fEps x0 (tsep (tvar (S (S y))) (renf (upr S) (renf (upr S) (tr φ))))).
      axm (M_sep (renf (upr S) (renf (upr S) (tr φ))) (tvar (S (S y))) x0). iffr 0. split_and; [hyp|].
      eapply (l11_conv _ φ (x1 .: fun k => tvar (S (S k))) (x0 .: fun k => tvar (S (S k)))).
      -- intros [|n]; cbn; [hyp|apply eqv_refl_t].
      -- fnorm.
      -- apply (p_conv _ _ (shf (subf (ups (tsep (tvar y) (tr φ) .: tvar)) (renf (upr S) (tr φ))))); [fnorm|hyp].
  - (* collection *)
    intro_imp. axm (M_coll (tr ψ) (tvar a)). mp 0.
    + intro_all. intro_imp. spec 2 x0. mp 0; [apply eps_mem_t; hyp|].
      apply (p_conv _ _ (fEx (subf (ups (x0 .: tvar)) (renf (upr (upr S)) (tr ψ))))); [fnorm|hyp].
    + dex 0.
      (* b = 0 *)
      exists_ x0. intro_all. intro_imp.
      (* α = 0, b = 1 *)
      axm (M_mem x0 (tvar (S (S a)))). iffm 0; [hyp|]. dex 0. dand 0.
      (* α' = 0, α = 1, b = 2 *)
      spec 6 x0. mp 0; [hyp|]. dex 0. dand 0.
      (* β = 0, α' = 1, α = 2, b = 3 *)
      exists_ x0. split_and; [apply eps_mem_t; hyp|].
      eapply (l11_conv _ ψ (x0 .: x1 .: fun k => tvar (S (S (S (S k))))) (x0 .: x2 .: fun k => tvar (S (S (S (S k)))))).
      -- intros [|[|n]]; cbn; [apply eqv_refl_t|lem eqv_sym (sl [x2; x1]); hyp|apply eqv_refl_t].
      -- fnorm.
      -- apply (p_conv _ _ (subf (ups (x0 .: tvar)) (renf (upr (upr S)) (renf (upr (upr S)) (renf (upr (upr S)) (tr ψ)))))); [fnorm|hyp].
  - (* ∈-induction *)
    intro_imp. axm (M_ind (tr φ)). app 0. intro_all. intro_imp.
    spec 2 x0. mp 0.
    + intro_all. intro_imp.
      (* y = 0, x = 1 *)
      axm (M_mem x0 x1). iffm 0; [hyp|]. dex 0. dand 0.
      (* y' = 0, y = 1, x = 2 *)
      spec 7 x0. mp 0; [hyp|].
      eapply (l11_conv _ φ (x0 .: fun k => tvar (S (S (S k)))) (x1 .: fun k => tvar (S (S (S k))))).
      -- intros [|n]; cbn; [lem eqv_sym (sl [x1; x0]); hyp|apply eqv_refl_t].
      -- fnorm.
      -- convh 0 (subf (x0 .: fun k => tvar (S (S (S k)))) (tr φ)). hyp.
    + convh 0 (tr φ). hyp.
Qed.

(** ** Theorem 12 *)

Theorem thm12 Γ φ : iprv IZF Γ φ -> prv IZFm (map tr Γ) (tr φ).
Proof.
  assert (M : forall Γ, map tr (map ish Γ) = map shf (map tr Γ)).
  { intros Δ. rewrite !map_map. apply map_ext. intros; apply tr_ish. }
  induction 1; cbn in *.
  - apply p_ax, in_map, H.
  - eapply prv_weak; [apply IZF_tr, H|intros ? []].
  - apply p_topI.
  - apply p_botE; auto.
  - apply p_andI; auto.
  - eapply p_andE1; eauto.
  - eapply p_andE2; eauto.
  - apply p_orI1; auto.
  - apply p_orI2; auto.
  - eapply p_orE; eauto.
  - apply p_impI; auto.
  - eapply p_impE; eauto.
  - apply p_allI. rewrite <- M. exact IHiprv.
  - rewrite tr_inst. apply p_allE; auto.
  - rewrite tr_inst in IHiprv. eapply p_exI; eauto.
  - eapply p_exE; [eauto|]. rewrite <- M, <- tr_ish. exact IHiprv2.
  - apply eqv_refl_t.
  - rewrite tr_inst in *. eapply (l11_conv _ φ (tvar m .: tvar) (tvar n .: tvar)); [|reflexivity|exact IHiprv2].
    intros [|k]; cbn; [exact IHiprv1|apply eqv_refl_t].
Qed.

(** Closed form: if IZF ⊢ φ, then IZF⁻ε ⊢ φ^ε. *)
Corollary IZFm_extends_IZF φ : iprv IZF [] φ -> prv IZFm [] (tr φ).
Proof. apply thm12. Qed.
