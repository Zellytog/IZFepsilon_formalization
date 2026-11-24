(** * Theorem 17: the axioms of IZF⁺ε, translated, are theorems of IZF *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax Deriv Theories ISyntax ILogic Graph GSubst ED Repl.

(** ** Tools: values, instantiation *)

Lemma Tmap_shf ρ Γ : map (fun A => T A (0 .: sh 1 ρ)) (map shf Γ) = map ish (map (fun A => T A ρ) Γ).
Proof.
  rewrite !map_map. apply map_ext. intros A. rewrite Tiren.
  apply (proj2 GT_ren). intros; reflexivity.
Qed.

Lemma Hyp_inst Γ t ρ v : Γ ⊢i D t ρ v -> Hyp Γ (t .: tvar) ρ (v .: ρ).
Proof. intros H [|n]; [exact H|]. unfold D. cbn. apply i_allI, ii_refl. Qed.

Lemma T_inst_v φ ρ v : iinst (T φ (0 .: sh 1 ρ)) v = T φ (v .: ρ).
Proof. unfold iinst. rewrite Tiren. apply (proj2 GT_ext). intros [|n]; reflexivity. Qed.

Lemma inst_T Γ φ t ρ v : Γ ⊢i D t ρ v -> Γ ⊢i iIff (T (inst φ t) ρ) (T φ (v .: ρ)).
Proof. intros H. apply (proj2 GT_subst), Hyp_inst, H. Qed.

(** Eliminating the existence of a value. *)
Lemma with_val Γ t ρ ψ : (D t (sh 1 ρ) 0 :: map ish Γ) ⊢i ish ψ -> Γ ⊢i ψ.
Proof. intros H. eapply i_exE; [apply HED|exact H]. Qed.

Lemma D_var' Γ n ρ : Γ ⊢i D (tvar n) ρ (ρ n).
Proof. unfold D. cbn. apply i_allI, ii_refl. Qed.

Lemma D_sh Γ t ρ v : Γ ⊢i D t ρ v -> map ish Γ ⊢i D t (sh 1 ρ) (S v).
Proof. intros H. apply (i_conv _ (iren S (D t ρ v))); [rewrite Diren; reflexivity|]. apply iprv_sh, H. Qed.

Lemma D_sht Γ t ρ j v : Γ ⊢i D t ρ v -> Γ ⊢i D (sht t) (j .: ρ) v.
Proof.
  intros H. unfold D. rewrite (proj1 GT_ren t S (sh 1 (j .: ρ)) (sh 1 ρ)) by (intros; reflexivity). exact H.
Qed.

Lemma D_up Γ t ρ v : Γ ⊢i D t ρ v -> map ish Γ ⊢i D (sht t) (0 .: sh 1 ρ) (S v).
Proof. intros H. apply D_sht, D_sh, H. Qed.

(** Obtaining values for a list of terms. *)
Lemma vals ts : forall φ, (forall Γ ρ vs, Forall2 (fun t v => Γ ⊢i D t ρ v) ts vs -> Γ ⊢i T φ ρ) ->
  forall Γ ρ, Γ ⊢i T φ ρ.
Proof.
  induction ts as [|t ts IH]; intros φ K.
  - intros Γ ρ. apply (K Γ ρ []). constructor.
  - apply IH. intros Γ ρ vs H. apply (with_val _ t ρ).
    apply (i_conv _ (T φ (sh 1 ρ))); [rewrite Tiren; reflexivity|].
    apply (K _ _ (0 :: map S vs)). constructor; [apply i_ax; left; reflexivity|].
    clear K IH. induction H; constructor; [|exact IHForall2].
    apply i_wk, D_sh, H.
Qed.

Ltac fdest := repeat match goal with H : Forall2 _ (_ :: _) _ |- _ => inversion H; subst; clear H end;
  repeat match goal with H : Forall2 _ [] _ |- _ => clear H end.

(** ** Characterisation of the values of the constructors *)

Lemma C_empty Γ ρ p : Γ ⊢i D tempty ρ p -> Γ ⊢i iEmpty p.
Proof. apply D_val. Qed.

Lemma C_omega Γ ρ p : Γ ⊢i D tomega ρ p -> Γ ⊢i iOmega p.
Proof. apply D_val. Qed.

Lemma C_pair Γ a b ρ u v p : Γ ⊢i D (tpair a b) ρ p -> Γ ⊢i D a ρ u -> Γ ⊢i D b ρ v ->
  Γ ⊢i iAll (iIff (iMem 0 (S p)) (iOr (iEq 0 (S u)) (iEq 0 (S v)))).
Proof.
  intros Hp Hu Hv. eapply ii_l; [exact (char2 _ _ _ _ _ _ (iAll (iIff (iMem 0 (3 + p)) (iOr (iEq 0 2) (iEq 0 1)))) Hu Hv)|].
  exact (D_val _ _ _ _ Hp).
Qed.

Lemma C_union Γ a ρ u p : Γ ⊢i D (tunion a) ρ p -> Γ ⊢i D a ρ u ->
  Γ ⊢i iAll (iIff (iMem 0 (S p)) (iEx (iAnd (iMem 0 (S (S u))) (iMem 1 0)))).
Proof.
  intros Hp Hu. eapply ii_l; [exact (char1 _ _ _ _ (iAll (iIff (iMem 0 (2 + p)) (iEx (iAnd (iMem 0 2) (iMem 1 0))))) Hu)|].
  exact (D_val _ _ _ _ Hp).
Qed.

Lemma C_pow Γ a ρ u p : Γ ⊢i D (tpow a) ρ p -> Γ ⊢i D a ρ u ->
  Γ ⊢i iAll (iIff (iMem 0 (S p)) (iSub 0 (S u))).
Proof.
  intros Hp Hu. eapply ii_l; [exact (char1 _ _ _ _ (iAll (iIff (iMem 0 (2 + p)) (iSub 0 1))) Hu)|].
  exact (D_val _ _ _ _ Hp).
Qed.

Lemma C_sep Γ a φ ρ u p : Γ ⊢i D (tsep a φ) ρ p -> Γ ⊢i D a ρ u ->
  Γ ⊢i iAll (iIff (iMem 0 (S p)) (iAnd (iMem 0 (S u)) (T φ (0 .: sh 1 ρ)))).
Proof.
  intros Hp Hu. eapply ii_l; [|exact (D_val _ _ _ _ Hp)]. eapply ii_trans; [apply (char1 _ _ _ _ _ Hu)|].
  cbn [iren]. rewrite Tiren. iicong; apply ii_T_ext; pwsolve.
Qed.

Lemma C_repl Γ a ψ ρ u p : Γ ⊢i D (trepl a ψ) ρ p -> Γ ⊢i D a ρ u ->
  Γ ⊢i iAll (iIff (iMem 0 (S p))
    (iAnd (iAll (iImp (iMem 0 (S (S u))) (iEx (iAnd (T ψ (0 .: 1 .: sh 3 ρ)) (iAll (iImp (T ψ (0 .: 2 .: sh 4 ρ)) (iEq 0 1)))))))
          (iEx (iAnd (iMem 0 (S (S u))) (T ψ (1 .: 0 .: sh 2 ρ)))))).
Proof.
  intros Hp Hu. eapply ii_l; [|exact (D_val _ _ _ _ Hp)]. eapply ii_trans; [apply (char1 _ _ _ _ _ Hu)|].
  cbn [iren]. rewrite !Tiren. iicong; apply ii_T_ext; pwsolve.
Qed.

(** The graphs stay folded while the axioms are reduced. *)
Local Arguments G : simpl never.

Lemma ii_Tren Γ φ ξ f g : (forall n, g n = f (ξ n)) -> Γ ⊢i iIff (T (renf ξ φ) f) (T φ g).
Proof. intros H. rewrite (proj2 GT_ren φ ξ f g H). apply ii_refl. Qed.

Ltac dval := first [eassumption | match goal with |- _ ⊢i D (tvar ?n) ?r _ => exact (D_var' _ n r) end].
Ltac areduce := iicong;
  try (apply atom_char; [reflexivity|dval|dval]);
  try (apply ii_T_ext; pwsolve);
  try (apply ii_Tren; pwsolve);
  try (apply inst_T; eassumption).

Section Vals.
Context (φ : form).
Lemma vals1 a : (forall Γ ρ u, Γ ⊢i D a ρ u -> Γ ⊢i T φ ρ) -> forall Γ ρ, Γ ⊢i T φ ρ.
Proof. intros K. apply (vals [a]). intros Γ ρ vs H. fdest. eauto. Qed.
Lemma vals2 a b : (forall Γ ρ u v, Γ ⊢i D a ρ u -> Γ ⊢i D b ρ v -> Γ ⊢i T φ ρ) -> forall Γ ρ, Γ ⊢i T φ ρ.
Proof. intros K. apply (vals [a; b]). intros Γ ρ vs H. fdest. eauto. Qed.
Lemma vals3 a b c : (forall Γ ρ u v w, Γ ⊢i D a ρ u -> Γ ⊢i D b ρ v -> Γ ⊢i D c ρ w -> Γ ⊢i T φ ρ) ->
  forall Γ ρ, Γ ⊢i T φ ρ.
Proof. intros K. apply (vals [a; b; c]). intros Γ ρ vs H. fdest. eauto. Qed.
Lemma vals4 a b c d : (forall Γ ρ u v w p, Γ ⊢i D a ρ u -> Γ ⊢i D b ρ v -> Γ ⊢i D c ρ w -> Γ ⊢i D d ρ p -> Γ ⊢i T φ ρ) ->
  forall Γ ρ, Γ ⊢i T φ ρ.
Proof. intros K. apply (vals [a; b; c; d]). intros Γ ρ vs H. fdest. eauto. Qed.
End Vals.

Ltac usec C w := eapply i_conv; [|apply (i_allE _ _ _ w C)];
  unfold iinst; cbn [iren]; rewrite ?Tiren; icong; try reflexivity; apply (proj2 GT_ext); pwsolve.

(** ** The axioms of IZF⁻ε *)

Lemma ax_pair x y z Γ ρ : Γ ⊢i T (A_pair x y z) ρ.
Proof.
  revert Γ ρ. apply (vals4 _ x y z (tpair x y)). intros Γ ρ u v w p Hu Hv Hw Hp.
  pose proof (C_pair _ _ _ _ _ _ _ Hp Hu Hv) as C.
  unfold A_pair; cbn [T].
  apply (ii_r _ _ (iIff (iMem w p) (iOr (iEq w u) (iEq w v)))); [areduce|usec C w].
Qed.

Lemma ax_empty x Γ ρ : Γ ⊢i T (A_empty x) ρ.
Proof.
  revert Γ ρ. apply (vals2 _ x tempty). intros Γ ρ u e Hu He.
  pose proof (C_empty _ _ _ He) as C.
  unfold A_empty; cbn [T].
  apply (ii_r _ _ (iNot (iMem u e))); [areduce|usec C u].
Qed.

Lemma ax_union x y Γ ρ : Γ ⊢i T (A_union x y) ρ.
Proof.
  revert Γ ρ. apply (vals3 _ x y (tunion x)). intros Γ ρ u v p Hu Hv Hp.
  pose proof (C_union _ _ _ _ _ Hp Hu) as C.
  pose proof (D_up _ _ _ _ Hu). pose proof (D_up _ _ _ _ Hv).
  unfold A_union; cbn [T].
  apply (ii_r _ _ (iIff (iMem v p) (iEx (iAnd (iMem 0 (S u)) (iMem (S v) 0))))); [areduce|usec C v].
Qed.

Lemma mem_l : [] ⊢i iIff (iMem 0 1) (iEx (iAnd (iEq 1 0) (iMem 0 2))).
Proof.
  apply i_iffI.
  - iexists 0. apply i_andI; [apply i_refl|ihyp].
  - idex 0. idand 0. irew (iMem 0 3) 0 1; [apply ieq_sym_t; ihyp|ihyp].
Qed.

Lemma ax_mem x y Γ ρ : Γ ⊢i T (A_mem x y) ρ.
Proof.
  revert Γ ρ. apply (vals2 _ x y). intros Γ ρ u v Hu Hv.
  pose proof (D_up _ _ _ _ Hu). pose proof (D_up _ _ _ _ Hv).
  unfold A_mem; cbn [T].
  apply (ii_r _ _ (iIff (iMem u v) (iEx (iAnd (iEq (S u) 0) (iMem 0 (S v)))))); [areduce|].
  ilem mem_l (il [u; v]).
Qed.

Lemma ax_sub x y Γ ρ : Γ ⊢i T (A_sub x y) ρ.
Proof.
  revert Γ ρ. apply (vals2 _ x y). intros Γ ρ u v Hu Hv.
  pose proof (D_up _ _ _ _ Hu). pose proof (D_up _ _ _ _ Hv).
  unfold A_sub; cbn [T].
  apply (ii_r _ _ (iIff (iSub u v) (iAll (iImp (iMem 0 (S u)) (iMem 0 (S v)))))); [areduce|apply i_th, I_sub].
Qed.

Lemma sub_refl : [] ⊢i iSub 0 0.
Proof. iax (I_sub 0 0). iffr 0. iintro_all. apply i_impI. ihyp. Qed.

Lemma eqv_l : [] ⊢i iIff (iEq 0 1) (iAnd (iSub 0 1) (iSub 1 0)).
Proof.
  apply i_iffI.
  - ihave sub_refl (il [0]). apply i_andI.
    + irew (iSub 1 0) 0 1; [ihyp|ihyp].
    + irew (iSub 0 1) 0 1; [ihyp|ihyp].
  - idand 0. iax (I_ext 0 1). iapp2 0; ihyp.
Qed.

Lemma ax_eqv x y Γ ρ : Γ ⊢i T (A_eqv x y) ρ.
Proof.
  revert Γ ρ. apply (vals2 _ x y). intros Γ ρ u v Hu Hv.
  unfold A_eqv; cbn [T].
  apply (ii_r _ _ (iIff (iEq u v) (iAnd (iSub u v) (iSub v u)))); [areduce|].
  ilem eqv_l (il [u; v]).
Qed.

Lemma wpow_l : [iAll (iIff (iMem 0 1) (iSub 0 2))] ⊢i
  iEx (iAnd (iMem 0 1) (iAll (iIff (iMem 0 1) (iAnd (iMem 0 3) (iMem 0 4))))).
Proof.
  iax (I_sep (iMem 0 3) 1). idex 0.
  iexists 0. apply i_andI; [|ihyp].
  ispec 2 0. iffr 0. iax (I_sub 0 2). iffr 0. iintro_all. apply i_impI.
  ispec 3 0. iffm 0; [ihyp|]. idand 0. ihyp.
Qed.

Lemma ax_wpow x a Γ ρ : Γ ⊢i T (A_wpow x a) ρ.
Proof.
  revert Γ ρ. apply (vals3 _ x a (tpow x)). intros Γ ρ u w p Hu Hw Hp.
  pose proof (C_pow _ _ _ _ _ Hp Hu) as C.
  assert (map ish Γ ⊢i D (tpow (sht x)) (0 .: sh 1 ρ) (S p)) by exact (D_up _ _ _ _ Hp).
  pose proof (D_up _ _ _ _ (D_up _ _ _ _ Hu)). pose proof (D_up _ _ _ _ (D_up _ _ _ _ Hw)).
  unfold A_wpow; cbn [T].
  apply (ii_r _ _ (iEx (iAnd (iMem 0 (S p)) (iAll (iIff (iMem 0 1) (iAnd (iMem 0 (S (S u))) (iMem 0 (S (S w))))))))); [areduce|].
  ilem wpow_l (il [p; u; w]). exact C.
Qed.

Lemma ax_sep φ y z Γ ρ : Γ ⊢i T (A_sep φ y z) ρ.
Proof.
  revert Γ ρ. apply (vals3 _ y z (tsep y φ)). intros Γ ρ u w s Hu Hw Hs.
  pose proof (C_sep _ _ _ _ _ _ Hs Hu) as C.
  unfold A_sep; cbn [T].
  apply (ii_r _ _ (iIff (iMem w s) (iAnd (iMem w u) (T φ (w .: ρ))))); [areduce|usec C w].
Qed.

Lemma ax_ind φ Γ ρ : Γ ⊢i T (A_ind φ) ρ.
Proof.
  unfold A_ind; cbn [T].
  apply (ii_r _ _ (iImp (iAll (iImp (iAll (iImp (iMem 0 1) (T φ (0 .: sh 2 ρ)))) (T φ (0 .: sh 1 ρ))))
                        (iAll (T φ (0 .: sh 1 ρ))))); [areduce|].
  eapply i_conv; [|apply i_th, (I_ind (T φ (0 .: sh 1 ρ)))]. rewrite Tiren. tcong.
Qed.

Lemma ax_coll ψ a Γ ρ : Γ ⊢i T (A_coll ψ a) ρ.
Proof.
  revert Γ ρ. apply (vals1 _ a). intros Γ ρ u Hu.
  pose proof (D_up _ _ _ _ Hu). pose proof (D_up _ _ _ _ (D_up _ _ _ _ Hu)).
  unfold A_coll; cbn [T].
  apply (ii_r _ _ (iImp (iAll (iImp (iMem 0 (S u)) (iEx (T ψ (0 .: 1 .: sh 2 ρ)))))
                        (iEx (iAll (iImp (iMem 0 (S (S u))) (iEx (iAnd (iMem 0 2) (T ψ (0 .: 1 .: sh 3 ρ))))))))); [areduce|].
  eapply i_conv; [|apply i_th, (I_coll (T ψ (0 .: 1 .: sh 2 ρ)) u)]. rewrite Tiren. tcong.
Qed.

(** ** The axioms added in IZFε, and extensionality *)

Lemma ax_repl ψ a b Γ ρ : Γ ⊢i T (A_repl ψ a b) ρ.
Proof.
  revert Γ ρ. apply (vals3 _ a b (trepl a ψ)). intros Γ ρ u w r Hu Hw Hr.
  pose proof (C_repl _ _ _ _ _ _ Hr Hu) as C.
  pose proof (D_up _ _ _ _ Hu) as Hu'. pose proof (D_up _ _ _ _ Hw) as Hw'.
  unfold A_repl, fExU, repl_body; cbn [T].
  apply (ii_r _ _ (iImp (iAll (iImp (iMem 0 (S u)) (iEx (iAnd (T ψ (0 .: 1 .: sh 2 ρ)) (iAll (iImp (T ψ (0 .: 2 .: sh 3 ρ)) (iEq 0 1)))))))
                        (iIff (iMem w r) (iEx (iAnd (iMem 0 (S u)) (T ψ (S w .: 0 .: sh 1 ρ))))))).
  { areduce. all: apply (proj2 GT_subst); intros [|[|n]]; [exact Hw'|exact (D_var' _ 0 _)|exact (D_var' _ (S n) _)]. }
  icut (iIff (iMem w r) (iAnd (iAll (iImp (iMem 0 (S u)) (iEx (iAnd (T ψ (0 .: 1 .: sh 2 ρ)) (iAll (iImp (T ψ (0 .: 2 .: sh 3 ρ)) (iEq 0 1)))))))
                              (iEx (iAnd (iMem 0 (S u)) (T ψ (S w .: 0 .: sh 1 ρ)))))); [usec C w|].
  apply i_impI. apply i_iffI.
  - iffm 2; [ihyp|]. idand 0. ihyp.
  - iffr 2. apply i_andI; ihyp.
Qed.

Lemma ax_seppow φ a Γ ρ : Γ ⊢i T (A_seppow φ a) ρ.
Proof.
  revert Γ ρ. apply (vals3 _ a (tsep a φ) (tpow a)). intros Γ ρ u s p Hu Hs Hp.
  pose proof (C_pow _ _ _ _ _ Hp Hu) as Cp. pose proof (C_sep _ _ _ _ _ _ Hs Hu) as Cs.
  unfold A_seppow; cbn [T].
  apply (ii_r _ _ (iMem s p)); [areduce|].
  icut (iIff (iMem s p) (iSub s u)); [usec Cp s|]. iffr 0.
  eapply i_cut; [apply i_wk, Cs|].
  iax (I_sub s u). iffr 0. iintro_all. apply i_impI.
  ispec 2 0. iffm 0; [ihyp|]. idand 0. ihyp.
Qed.

Lemma powres_l : [iAll (iIff (iMem 0 1) (iSub 0 2))] ⊢i
  iImp (iMem 2 0) (iEx (iAll (iIff (iMem 0 4) (iAnd (iMem 0 3) (iMem 0 1))))).
Proof.
  apply i_impI. ispec 1 2. iffm 0; [ihyp|].
  iexists 2. iintro_all. apply i_iffI.
  - apply i_andI; [ilem sub_el (il [0; 3; 2]); ihyp|ihyp].
  - idand 0. ihyp.
Qed.

Lemma ax_powres x a Γ ρ : Γ ⊢i T (A_powres x a) ρ.
Proof.
  revert Γ ρ. apply (vals3 _ x a (tpow x)). intros Γ ρ u v p Hu Hv Hp.
  pose proof (C_pow _ _ _ _ _ Hp Hu) as C.
  pose proof (D_up _ _ _ _ (D_up _ _ _ _ Hu)). pose proof (D_up _ _ _ _ (D_up _ _ _ _ Hv)).
  unfold A_powres; cbn [T].
  apply (ii_r _ _ (iImp (iMem v p) (iEx (iAll (iIff (iMem 0 (S (S v))) (iAnd (iMem 0 (S (S u))) (iMem 0 1))))))); [areduce|].
  ilem powres_l (il [p; u; v]). exact C.
Qed.

Lemma ax_ext x y Γ ρ : Γ ⊢i T (A_ext x y) ρ.
Proof. unfold A_ext; cbn [T]. apply i_impI. ihyp. Qed.

(** ** ω *)

Lemma suc_l : [iAll (iIff (iMem 0 1) (iEx (iAnd (iMem 0 3) (iMem 1 0))));
               iAll (iIff (iMem 0 2) (iOr (iEq 0 4) (iEq 0 3)));
               iAll (iIff (iMem 0 3) (iOr (iEq 0 4) (iEq 0 4)))] ⊢i iSuc 3 0.
Proof.
  unfold iSuc. iintro_all. apply i_iffI.
  - ispec 1 0. iffm 0; [ihyp|]. idex 0. idand 0. ispec 7 0. iffm 0; [ihyp|]. idor 0.
    + apply i_orI1. irew (iMem 2 0) 0 5; ihyp.
    + apply i_orI2. icut (iMem 1 4); [irew (iMem 2 0) 0 4; ihyp|].
      ispec 12 1. iffm 0; [ihyp|]. idor 0; ihyp.
  - ispec 1 0. iffr 0. idor 1.
    + iexists 4. apply i_andI; [|ihyp]. ispec 4 4. iffr 0. apply i_orI1. apply i_refl.
    + iexists 3. apply i_andI.
      * ispec 4 3. iffr 0. apply i_orI2. apply i_refl.
      * ispec 5 0. iffr 0. apply i_orI1. ihyp.
Qed.

Lemma suc_char Γ ρ s : Γ ⊢i D (tsuc x0) ρ s -> Γ ⊢i iSuc (ρ 0) s.
Proof.
  intros Hs. unfold tsuc in Hs.
  eapply i_exE; [apply (HED (tpair x0 x0) ρ)|].
  eapply i_exE; [apply (HED (tpair x0 (tpair x0 x0)) (sh 1 ρ))|].
  assert (H1 : D (tpair x0 (tpair x0 x0)) (sh 1 (sh 1 ρ)) 0 :: map ish (D (tpair x0 x0) (sh 1 ρ) 0 :: map ish Γ)
               ⊢i D (tpair x0 x0) (sh 1 (sh 1 ρ)) 1) by (apply i_wk, D_sh, i_ax; left; reflexivity).
  match goal with |- ?Δ ⊢i _ =>
    assert (H3 : Δ ⊢i D (tunion (tpair x0 (tpair x0 x0))) (sh 1 (sh 1 ρ)) (S (S s))) by (apply i_wk, D_sh, i_wk, D_sh, Hs);
    assert (Hn : Δ ⊢i D x0 (sh 1 (sh 1 ρ)) (S (S (ρ 0)))) by exact (D_var' _ 0 _) end.
  pose proof (C_union _ _ _ _ _ H3 (i_ax _ _ _ (in_eq _ _))) as Cu.
  pose proof (C_pair _ _ _ _ _ _ _ (i_ax _ _ _ (in_eq _ _)) Hn H1) as C2.
  pose proof (C_pair _ _ _ _ _ _ _ H1 Hn Hn) as C1.
  ilem suc_l (il [S (S s); 0; 1; S (S (ρ 0))]); [exact Cu|exact C2|exact C1].
Qed.

Lemma sucu_l : [iSuc 1 0] ⊢i iIff (iEq 2 0) (iSuc 1 2).
Proof.
  apply i_iffI.
  - irew (iSuc 2 0) 0 2; [apply ieq_sym_t; ihyp|ihyp].
  - apply (ext_by _ (iOr (iMem 0 2) (iEq 0 2))); ihyp.
Qed.

Lemma atom_suc Γ a ρ v : Γ ⊢i D a ρ v ->
  Γ ⊢i iIff (atom iEq (G a (sh 1 ρ) 0) (G (tsuc x0) (sh 2 ρ) 0)) (iSuc (ρ 0) v).
Proof.
  intros Hv. apply (with_val _ (tsuc x0) ρ).
  apply (i_conv _ (iIff (atom iEq (G a (sh 1 (sh 1 ρ)) 0) (G (tsuc x0) (sh 2 (sh 1 ρ)) 0)) (iSuc (S (ρ 0)) (S v)))).
  { unfold atom, iSuc. cbn [iren]. rewrite !Giren. icong; try reflexivity; apply (proj1 GT_ext); pwsolve. }
  eapply ii_trans; [apply atom_char; [reflexivity|apply i_wk, D_sh, Hv|apply i_ax; left; reflexivity]|].
  assert (Hs : D (tsuc x0) (sh 1 ρ) 0 :: map ish Γ ⊢i iSuc (S (ρ 0)) 0)
    by (apply (suc_char _ (sh 1 ρ)); apply i_ax; left; reflexivity).
  ilem sucu_l (il [0; S (ρ 0); S v]). exact Hs.
Qed.

Lemma omega_l : [iOmega 0; iEmpty 1] ⊢i iIff (iMem 2 0) (iOr (iEq 2 1) (iEx (iAnd (iMem 0 1) (iSuc 0 3)))).
Proof.
  unfold iOmega. apply i_iffI.
  - idand 1.
    iax (I_sep (iOr (iEq 0 2) (iEx (iAnd (iMem 0 2) (iSuc 0 1)))) 0). idex 0.
    (* I = 0, o = 1, e = 2, u = 3 *)
    icut (iInd 0).
    { apply i_andI.
      - idand 2. idex 0. idand 0. iexists 0. apply i_andI; [|ihyp].
        ispec 5 0. iffr 0. apply i_andI; [ihyp|]. apply i_orI1.
        apply (ext_by _ iBot); apply empty_char; ihyp.
      - iintro_all. apply i_impI. ispec 1 0. iffm 0; [ihyp|]. idand 0. idand 7.
        ispec 1 0. imp 0; [ihyp|]. idex 0. idand 0. iexists 0. apply i_andI; [|ihyp].
        ispec 12 0. iffr 0. apply i_andI; [ihyp|]. apply i_orI2. iexists 1. apply i_andI; ihyp. }
    ispec 4 0. imp 0; [ihyp|].
    icut (iMem 3 0); [ilem sub_el (il [3; 1; 0]); ihyp|].
    ispec 4 3. iffm 0; [ihyp|]. idand 0. ihyp.
  - idand 1. idand 0. idor 4.
    + idex 1. idand 0.
      icut (iEq 0 2); [apply (ext_by _ iBot); apply empty_char; ihyp|].
      irew (iMem 0 2) 0 3; [eapply ieq_trans_t; [ihyp|apply ieq_sym_t; ihyp]|ihyp].
    + idex 0. idand 0. ispec 5 0. imp 0; [ihyp|]. idex 0. idand 0.
      icut (iEq 0 4); [apply (ext_by _ (iOr (iMem 0 2) (iEq 0 2))); ihyp|].
      irew (iMem 0 3) 0 4; ihyp.
Qed.

Lemma ax_omega x Γ ρ : Γ ⊢i T (A_omega x) ρ.
Proof.
  revert Γ ρ. apply (vals3 _ x tomega tempty). intros Γ ρ u o e Hu Ho He.
  pose proof (C_omega _ _ _ Ho) as Co. pose proof (C_empty _ _ _ He) as Ce.
  pose proof (D_up _ _ _ _ Hu). assert (map ish Γ ⊢i D tomega (0 .: sh 1 ρ) (S o)) by exact (D_up _ _ _ _ Ho).
  unfold A_omega; cbn [T].
  apply (ii_r _ _ (iIff (iMem u o) (iOr (iEq u e) (iEx (iAnd (iMem 0 (S o)) (iSuc 0 (S u))))))).
  { areduce. all: apply atom_suc; eassumption. }
  ilem omega_l (il [o; e; u]); [exact Co|exact Ce].
Qed.

(** ** All the axioms of IZF⁺ε *)

Theorem HAX φ : IZFp φ -> forall Γ ρ, Γ ⊢i T φ ρ.
Proof.
  intros [φ' [φ'' H| | |]|x y] Γ ρ.
  - destruct H.
    + apply ax_empty.
    + apply ax_omega.
    + apply ax_pair.
    + apply ax_union.
    + apply ax_wpow.
    + apply ax_mem.
    + apply ax_sub.
    + apply ax_eqv.
    + apply ax_sep.
    + apply ax_ind.
    + apply ax_coll.
  - apply ax_repl.
  - apply ax_seppow.
  - apply ax_powres.
  - apply ax_ext.
Qed.
