(** * Existence and uniqueness of the values of terms in IZF *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax ISyntax ILogic Graph GSubst.

Lemma Giren ξ t ρ y : iren ξ (G t ρ y) = G t (fun k => ξ (ρ k)) (ξ y).
Proof. apply GT_iren. intros; reflexivity. Qed.
Lemma Tiren ξ φ ρ : iren ξ (T φ ρ) = T φ (fun k => ξ (ρ k)).
Proof. apply GT_iren. intros; reflexivity. Qed.
Lemma Diren ξ t ρ v : iren ξ (D t ρ v) = D t (fun k => ξ (ρ k)) (ξ v).
Proof. apply D_ren. Qed.

Ltac gnorm := unfold iinst; rewrite ?Giren, ?Tiren, ?Diren; cbn.

(** Transport along equality. *)
Lemma i_tr Γ (χ : iform) m n : Γ ⊢i iEq m n -> Γ ⊢i iren (m .: fun k => k) χ -> Γ ⊢i iren (n .: fun k => k) χ.
Proof. intros H K. exact (i_leib _ _ χ m n H K). Qed.

Lemma G_tr Γ t ρ m n : Γ ⊢i iEq m n -> Γ ⊢i G t ρ m -> Γ ⊢i G t ρ n.
Proof.
  intros H K. pose proof (i_tr _ (G t (sh 1 ρ) 0) m n H) as L. rewrite !Giren in L. apply L, K.
Qed.

Lemma inst_sh Γ X : Γ ⊢i iAll X -> map ish Γ ⊢i X.
Proof. intros H. apply (i_conv _ (iinst (iren (upr S) X) 0)); [apply ii_inst|]. apply i_allE, (iprv_sh _ _ H). Qed.

(** Extensionality: two sets characterised by the same formula are equal. *)
Lemma ext_by Γ C p q : Γ ⊢i iAll (iIff (iMem 0 (S p)) C) -> Γ ⊢i iAll (iIff (iMem 0 (S q)) C) -> Γ ⊢i iEq p q.
Proof.
  assert (K : forall a b, Γ ⊢i iAll (iIff (iMem 0 (S a)) C) -> Γ ⊢i iAll (iIff (iMem 0 (S b)) C) -> Γ ⊢i iSub a b).
  { intros a b Ha Hb. eapply ii_r; [apply i_th, I_sub|]. apply i_allI, i_impI.
    eapply ii_r; [apply i_wk, inst_sh, Hb|]. eapply ii_l; [apply i_wk, inst_sh, Ha|ihyp]. }
  intros Hp Hq. eapply i_impE; [eapply i_impE; [apply i_th, I_ext|]|]; apply K; assumption.
Qed.

(** A value for t, if t has a total and functional graph. *)
Lemma ED_of Γ t ρ :
  Γ ⊢i iEx (G t (sh 1 ρ) 0) ->
  (forall Γ' ρ' a b, Γ' ⊢i G t ρ' a -> Γ' ⊢i G t ρ' b -> Γ' ⊢i iEq a b) ->
  Γ ⊢i iEx (D t (sh 1 ρ) 0).
Proof.
  intros E U. eapply i_exE; [exact E|]. apply i_ex0. unfold D. apply i_allI. apply i_iffI.
  - eapply U; [ihyp|]. apply (i_conv _ (iren S (G t (sh 1 ρ) 0))); [rewrite Giren; reflexivity|ihyp].
  - eapply G_tr; [apply ieq_sym_t; ihyp|]. apply (i_conv _ (iren S (G t (sh 1 ρ) 0))); [rewrite Giren; reflexivity|ihyp].
Qed.

(** A value v of t is unique, and every u such that G(t, u) is a value. *)
Lemma D_uniq Γ t ρ v a : Γ ⊢i D t ρ v -> Γ ⊢i G t ρ a -> Γ ⊢i iEq a v.
Proof. intros H K. eapply ii_l; [apply D_use, H|exact K]. Qed.

Lemma D_val Γ t ρ v : Γ ⊢i D t ρ v -> Γ ⊢i G t ρ v.
Proof. intros H. eapply ii_r; [apply D_use, H|apply i_refl]. Qed.

(** ** Characterising a unary constructor by the value of its argument *)

Lemma char1 Γ a ρ u B : Γ ⊢i D a ρ u -> Γ ⊢i iIff (iEx (iAnd (G a (sh 1 ρ) 0) B)) (iren (u .: fun k => k) B).
Proof.
  intros Hu. apply i_iffI.
  - eapply i_exE; [ihyp|]. idand 0.
    assert (E : map ish (iEx (iAnd (G a (sh 1 ρ) 0) B) :: Γ) ⊢i D a (sh 1 ρ) (S u)).
    { apply (i_conv _ (iren S (D a ρ u))); [rewrite Diren; reflexivity|]. apply iprv_sh. apply i_wk, Hu. }
    assert (K : G a (sh 1 ρ) 0 :: B :: iAnd (G a (sh 1 ρ) 0) B :: map ish (iEx (iAnd (G a (sh 1 ρ) 0) B) :: Γ) ⊢i iEq 0 (S u))
      by (eapply D_uniq; [do 3 apply i_wk; exact E|ihyp]).
    pose proof (i_tr _ (iren (upr S) B) 0 (S u) K) as L.
    rewrite (iren_swap B (S u .: fun k => k) (upr S) S (u .: fun k => k)) in L by (intros [|n]; reflexivity).
    apply L. rewrite (iren_comp B _ _ (fun k => k)) by (intros [|n]; reflexivity). rewrite iren_id by reflexivity. ihyp.
  - apply (i_exI _ _ _ u). unfold iinst. cbn [iren]. apply i_andI; [|ihyp].
    rewrite Giren. apply (i_conv _ (G a ρ u)); [apply (proj1 GT_ext); intros; reflexivity|]. apply D_val, i_wk, Hu.
Qed.

Lemma ii_T_ext Γ φ f g : (forall n, g n = f n) -> Γ ⊢i iIff (T φ f) (T φ g).
Proof. intros H. rewrite (proj2 GT_ext φ f g H). apply ii_refl. Qed.

Ltac tcong := icong; try reflexivity; apply (proj2 GT_ext); pwsolve.

(** The common scheme: a unary constructor whose elements are
    characterised by a formula C(ρ, u) about the value u of the
    argument. *)
Lemma ED_un (a t : term) (C : (nat -> nat) -> nat -> iform) :
  (forall ρ Γ, Γ ⊢i iEx (D a (sh 1 ρ) 0)) ->
  (forall Γ ρ u p, Γ ⊢i D a ρ u -> Γ ⊢i iIff (G t ρ p) (iAll (iIff (iMem 0 (S p)) (C ρ u)))) ->
  (forall Γ ρ u, Γ ⊢i iEx (iAll (iIff (iMem 0 1) (C (sh 1 ρ) (S u))))) ->
  forall ρ Γ, Γ ⊢i iEx (D t (sh 1 ρ) 0).
Proof.
  intros Ha Hc He ρ Γ. apply ED_of.
  - eapply i_exE; [apply Ha|].
    apply (i_conv _ (iEx (G t (sh 2 ρ) 0))); [cbn [iren]; rewrite Giren; reflexivity|].
    eapply ii_r; [apply ii_ex, Hc|apply He].
    apply (i_conv _ (iren S (D a (sh 1 ρ) 0))); [rewrite Diren; reflexivity|]. apply i_ax; left; reflexivity.
  - intros Γ' ρ' p q Hp Hq. eapply i_exE; [apply Ha|]. cbn [iren].
    apply (ext_by _ (C (sh 1 ρ') 0)).
    + eapply ii_l; [apply Hc; apply i_ax; left; reflexivity|].
      apply (i_conv _ (iren S (G t ρ' p))); [rewrite Giren; reflexivity|]. apply i_wk, iprv_sh; assumption.
    + eapply ii_l; [apply Hc; apply i_ax; left; reflexivity|].
      apply (i_conv _ (iren S (G t ρ' q))); [rewrite Giren; reflexivity|]. apply i_wk, iprv_sh; assumption.
Qed.

(** ** The constructors *)

Lemma ED_var n : forall ρ Γ, Γ ⊢i iEx (D (tvar n) (sh 1 ρ) 0).
Proof.
  intros ρ Γ. apply ED_of.
  - apply (i_exI _ _ _ (ρ n)). apply i_refl.
  - intros Γ' ρ' a b Ha Hb. cbn in *. eapply ieq_trans_t; [exact Ha|apply ieq_sym_t, Hb].
Qed.

Lemma empty_char Γ p : Γ ⊢i iEmpty p -> Γ ⊢i iAll (iIff (iMem 0 (S p)) iBot).
Proof.
  intros H. apply i_allI, i_iffI; [|apply i_botE; ihyp].
  eapply i_impE; [apply i_wk, inst_sh, H|ihyp].
Qed.

Lemma ED_empty : forall ρ Γ, Γ ⊢i iEx (D tempty (sh 1 ρ) 0).
Proof.
  intros ρ Γ. apply ED_of; [apply i_th, I_empty|].
  intros Γ' ρ' a b Ha Hb. apply (ext_by _ iBot); apply empty_char; assumption.
Qed.

Lemma ED_union a : (forall ρ Γ, Γ ⊢i iEx (D a (sh 1 ρ) 0)) -> forall ρ Γ, Γ ⊢i iEx (D (tunion a) (sh 1 ρ) 0).
Proof.
  intros Ha. apply (ED_un a (tunion a) (fun ρ u => iEx (iAnd (iMem 0 (S (S u))) (iMem 1 0)))); [exact Ha| |].
  - intros Γ ρ u p H. exact (char1 _ _ _ _ (iAll (iIff (iMem 0 (2 + p)) (iEx (iAnd (iMem 0 2) (iMem 1 0))))) H).
  - intros Γ ρ u. apply i_th, I_union.
Qed.

Lemma ED_sep a φ : (forall ρ Γ, Γ ⊢i iEx (D a (sh 1 ρ) 0)) -> forall ρ Γ, Γ ⊢i iEx (D (tsep a φ) (sh 1 ρ) 0).
Proof.
  intros Ha. apply (ED_un a (tsep a φ) (fun ρ u => iAnd (iMem 0 (S u)) (T φ (0 .: sh 1 ρ)))); [exact Ha| |].
  - intros Γ ρ u p H. eapply ii_trans; [apply (char1 _ _ _ _ _ H)|]. cbn [iren]. rewrite Tiren.
    iicong; apply ii_T_ext; pwsolve.
  - intros Γ ρ u. apply (i_conv _ (iEx (iAll (iIff (iMem 0 1) (iAnd (iMem 0 (S (S u))) (iren (upr S) (T φ (0 .: sh 1 ρ)))))))).
    + rewrite Tiren. tcong.
    + apply i_th, I_sep.
Qed.

Lemma G_env Γ t ρ ρ' y : (forall n, ρ' n = ρ n) -> Γ ⊢i G t ρ y -> Γ ⊢i G t ρ' y.
Proof. intros H K. rewrite <- (proj1 GT_ext t ρ ρ' y H). exact K. Qed.

Lemma char2 Γ a b ρ u v B : Γ ⊢i D a ρ u -> Γ ⊢i D b ρ v ->
  Γ ⊢i iIff (iEx (iAnd (G a (sh 1 ρ) 0) (iEx (iAnd (G b (sh 2 ρ) 0) B))))
            (iren (v .: fun k => k) (iren (upr (u .: fun k => k)) B)).
Proof.
  intros Hu Hv. eapply ii_trans; [apply (char1 _ _ _ _ _ Hu)|]. cbn [iren]. rewrite Giren.
  rewrite (proj1 GT_ext b _ (sh 1 ρ)) by pwsolve. apply (char1 _ _ _ _ _ Hv).
Qed.

Lemma atom_char Γ R a b ρ u v : (forall ξ m n, iren ξ (R m n) = R (ξ m) (ξ n)) ->
  Γ ⊢i D a ρ u -> Γ ⊢i D b ρ v -> Γ ⊢i iIff (atom R (G a (sh 1 ρ) 0) (G b (sh 2 ρ) 0)) (R u v).
Proof. intros HR Hu Hv. unfold atom. pose proof (char2 _ _ _ _ _ _ (R 1 0) Hu Hv) as K. rewrite !HR in K. exact K. Qed.

Lemma ED_pair a b : (forall ρ Γ, Γ ⊢i iEx (D a (sh 1 ρ) 0)) -> (forall ρ Γ, Γ ⊢i iEx (D b (sh 1 ρ) 0)) ->
  forall ρ Γ, Γ ⊢i iEx (D (tpair a b) (sh 1 ρ) 0).
Proof.
  intros Ha Hb.
  assert (Hc : forall Γ ρ u v p, Γ ⊢i D a ρ u -> Γ ⊢i D b ρ v ->
             Γ ⊢i iIff (G (tpair a b) ρ p) (iAll (iIff (iMem 0 (S p)) (iOr (iEq 0 (S u)) (iEq 0 (S v)))))).
  { intros Γ ρ u v p Hu Hv. exact (char2 _ _ _ _ _ _ (iAll (iIff (iMem 0 (3 + p)) (iOr (iEq 0 2) (iEq 0 1)))) Hu Hv). }
  intros ρ Γ. apply ED_of.
  - eapply i_exE; [apply Ha|]. eapply i_exE; [apply Hb|]. cbn [iren]. rewrite !Giren.
    eapply ii_r; [apply ii_ex, Hc|apply i_th, (I_pair 1 0)].
    + apply (i_conv _ (iren S (iren S (D a (sh 1 ρ) 0)))); [rewrite !Diren; reflexivity|].
      apply iprv_sh. apply i_ax; right; left; reflexivity.
    + apply (i_conv _ (iren S (D b (sh 1 (sh 1 ρ)) 0))); [rewrite !Diren; reflexivity|].
      apply iprv_sh. apply i_ax; left; reflexivity.
  - intros Γ' ρ' p q Hp Hq. eapply i_exE; [apply Ha|]. eapply i_exE; [apply Hb|]. cbn [iren].
    apply (ext_by _ (iOr (iEq 0 2) (iEq 0 1))).
    all: eapply ii_l; [apply Hc|].
    all: try (apply (i_conv _ (iren S (D a (sh 1 ρ') 0))); [rewrite !Diren; reflexivity|]; apply i_wk, iprv_sh, i_ax; left; reflexivity).
    all: try (apply i_ax; left; reflexivity).
    + apply (i_conv _ (iren S (iren S (G (tpair a b) ρ' p)))); [rewrite !Giren; reflexivity|].
      apply i_wk, iprv_sh, i_wk, iprv_sh; assumption.
    + apply (i_conv _ (iren S (iren S (G (tpair a b) ρ' q)))); [rewrite !Giren; reflexivity|].
      apply i_wk, iprv_sh, i_wk, iprv_sh; assumption.
Qed.

(** ** The power set, in IZF *)

Lemma sub_el : [iSub 1 2; iMem 0 1] ⊢i iMem 0 2.
Proof. iax (I_sub 1 2). iffm 0; [ihyp|]. ispec 0 0. iapp 0. ihyp. Qed.

Lemma pow_ex u : [] ⊢i iEx (iAll (iIff (iMem 0 1) (iSub 0 (S (S u))))).
Proof.
  iax (I_wpow u). idex 0.
  iax (I_sep (iSub 0 (S (S u))) 0). idex 0.
  (* p = 0, q = 1 *)
  iexists 0. iintro_all. apply i_iffI.
  - ispec 1 0. iffm 0; [ihyp|]. idand 0. ihyp.
  - (* b ⊆ u ⇒ b ∈ p *)
    ispec 3 0. idex 0. idand 0.
    (* b' = 0, b = 1, p = 2, q = 3 *)
    icut (iEq 0 1).
    { apply (ext_by _ (iAnd (iMem 0 (5 + u)) (iMem 0 2))); [ihyp|].
      iintro_all. apply i_iffI; [|idand 0; ihyp]. apply i_andI; [|ihyp].
      ilem sub_el (il [0; 2; 5 + u]); ihyp. }
    ispec 6 1. iffr 0. apply i_andI; [|ihyp].
    irew (iMem 0 4) 0 1; ihyp.
Qed.

Lemma ED_pow a : (forall ρ Γ, Γ ⊢i iEx (D a (sh 1 ρ) 0)) -> forall ρ Γ, Γ ⊢i iEx (D (tpow a) (sh 1 ρ) 0).
Proof.
  intros Ha. apply (ED_un a (tpow a) (fun ρ u => iSub 0 (S u))); [exact Ha| |].
  - intros Γ ρ u p H. exact (char1 _ _ _ _ (iAll (iIff (iMem 0 (2 + p)) (iSub 0 1))) H).
  - intros Γ ρ u. eapply iprv_weak; [apply pow_ex|intros ? []].
Qed.

(** ** ω: the least inductive set *)

Lemma omega_uniq : [iOmega 0; iOmega 1] ⊢i iEq 0 1.
Proof.
  unfold iOmega. idand 0. idand 3.
  iax (I_ext 0 1). iapp2 0.
  - ispec 4 1. iapp 0. ihyp.
  - ispec 2 0. iapp 0. ihyp.
Qed.

Lemma omega_ex : [] ⊢i iEx (iOmega 0).
Proof.
  iax I_inf. idex 0.
  iax (I_sep (iAll (iImp (iInd 0) (iMem 1 0))) 0). idex 0.
  (* s = 0, w = 1 *)
  iexists 0. apply i_andI; [apply i_andI|].
  - (* the empty set is in s *)
    idand 2. idex 0. idand 0.
    (* e = 0, s = 1, w = 2 *)
    iexists 0. apply i_andI; [|ihyp].
    ispec 5 0. iffr 0. apply i_andI; [ihyp|].
    iintro_all. apply i_impI. idand 0. idex 0. idand 0.
    (* e' = 0, I = 1, e = 2 *)
    icut (iEq 2 0); [apply (ext_by _ iBot); apply empty_char; ihyp|].
    irew (iMem 0 2) 0 2; [apply ieq_sym_t; ihyp|ihyp].
  - (* s is closed under successor *)
    iintro_all. apply i_impI.
    ispec 1 0. iffm 0; [ihyp|]. idand 0. idand 7. ispec 1 0. imp 0; [ihyp|]. idex 0. idand 0.
    (* t = 0, z = 1, s = 2, w = 3 *)
    iexists 0. apply i_andI; [|ihyp].
    ispec 12 0. iffr 0. apply i_andI; [ihyp|].
    iintro_all. apply i_impI.
    (* I = 0, t = 1, z = 2 *)
    ispec 10 0. imp 0; [ihyp|]. idand 2. ispec 1 2. imp 0; [ihyp|]. idex 0. idand 0.
    (* t' = 0, I = 1, t = 2, z = 3 *)
    icut (iEq 2 0); [apply (ext_by _ (iOr (iMem 0 4) (iEq 0 4))); ihyp|].
    irew (iMem 0 2) 0 2; [apply ieq_sym_t; ihyp|ihyp].
  - (* minimality *)
    iintro_all. apply i_impI. iax (I_sub 1 0). iffr 0. iintro_all. apply i_impI.
    ispec 3 0. iffm 0; [ihyp|]. idand 0. ispec 1 1. iapp 0. ihyp.
Qed.

Lemma ED_omega : forall ρ Γ, Γ ⊢i iEx (D tomega (sh 1 ρ) 0).
Proof.
  intros ρ Γ. apply ED_of; [eapply iprv_weak; [apply omega_ex|intros ? []]|].
  intros Γ' ρ' a b Ha Hb. ilem omega_uniq (il [a; b]); assumption.
Qed.
