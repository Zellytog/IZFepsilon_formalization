(** * The theories IZF⁻ε, IZFε and IZF⁺ε (Definitions 3, 6 and 15)

    Each axiom is given by a function of its arguments (terms, and a
    formula for schemes); its free variables are implicitly universal
    parameters. For schemes, the formula φ has its bound variable at 0 (at
    0 and 1 for ψ(α, β): β at 0, α at 1), its other variables being the
    parameters x⃗. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax Deriv.

Abbreviation x0 := (tvar 0).
Abbreviation x1 := (tvar 1).
Abbreviation x2 := (tvar 2).
Abbreviation x3 := (tvar 3).
Abbreviation x4 := (tvar 4).
Abbreviation x5 := (tvar 5).
Abbreviation x6 := (tvar 6).
Abbreviation x7 := (tvar 7).

(** The successor S(x) ≜ ⋃{x, {x, x}}. *)
Definition tsuc (a : term) : term := tunion (tpair a (tpair a a)).

(** ∃!β. χ(β) (β at 0). *)
Definition fExU (χ : form) : form := fEx (fAnd χ (fAll (fImp (renf (upr S) χ) (fEq x0 x1)))).

(** ** The axioms of IZF⁻ε (Definition 3) *)

Definition A_empty x := fNot (fEps x tempty).
Definition A_omega x :=
  fIff (fEps x tomega) (fOr (fEq x tempty) (fEx (fAnd (fEps x0 tomega) (fEq (sht x) (tsuc x0))))).
Definition A_pair x y z := fIff (fEps z (tpair x y)) (fOr (fEq z x) (fEq z y)).
Definition A_union x y := fIff (fEps y (tunion x)) (fEx (fAnd (fEps x0 (sht x)) (fEps (sht y) x0))).
Definition A_wpow x a :=
  fEx (fAnd (fEps x0 (tpow (sht x)))
            (fAll (fIff (fEps x0 x1) (fAnd (fEps x0 (sht (sht x))) (fEps x0 (sht (sht a))))))).
Definition A_mem x y := fIff (fMem x y) (fEx (fAnd (fEqv (sht x) x0) (fEps x0 (sht y)))).
Definition A_sub x y := fIff (fSub x y) (fAll (fImp (fEps x0 (sht x)) (fMem x0 (sht y)))).
Definition A_eqv x y := fIff (fEqv x y) (fAnd (fSub x y) (fSub y x)).
Definition A_sep φ y z := fIff (fEps z (tsep y φ)) (fAnd (fEps z y) (inst φ z)).
Definition A_ind φ := fImp (fAll (fImp (fAll (fImp (fEps x0 x1) (renf (upr S) φ))) φ)) (fAll φ).
Definition A_coll ψ a :=
  fImp (fAll (fImp (fEps x0 (sht a)) (fEx ψ)))
       (fEx (fAll (fImp (fEps x0 (sht (sht a))) (fEx (fAnd (fEps x0 x2) (renf (upr (upr S)) ψ)))))).

Inductive IZFm : form -> Prop :=
| M_empty x : IZFm (A_empty x)
| M_omega x : IZFm (A_omega x)
| M_pair x y z : IZFm (A_pair x y z)
| M_union x y : IZFm (A_union x y)
| M_wpow x a : IZFm (A_wpow x a)
| M_mem x y : IZFm (A_mem x y)
| M_sub x y : IZFm (A_sub x y)
| M_eqv x y : IZFm (A_eqv x y)
| M_sep φ y z : IZFm (A_sep φ y z)
| M_ind φ : IZFm (A_ind φ)
| M_coll ψ a : IZFm (A_coll ψ a).

(** ** The axioms added in IZFε (Definition 6) *)

(** ψ(β, α) with α ↦ x0 (bound) and β ↦ b: the conclusion of replacement. *)
Definition repl_body (ψ : form) (b : term) : form := subf (sht b .: x0 .: fun k => tvar (S k)) ψ.

Definition A_repl ψ a b :=
  fImp (fAll (fImp (fEps x0 (sht a)) (fExU ψ)))
       (fIff (fEps b (trepl a ψ)) (fEx (fAnd (fEps x0 (sht a)) (repl_body ψ b)))).
Definition A_seppow φ a := fEps (tsep a φ) (tpow a).
Definition A_powres x a :=
  fImp (fEps a (tpow x)) (fEx (fAll (fIff (fEps x0 (sht (sht a))) (fAnd (fEps x0 (sht (sht x))) (fEps x0 x1))))).

Inductive IZFe : form -> Prop :=
| E_base φ : IZFm φ -> IZFe φ
| E_repl ψ a b : IZFe (A_repl ψ a b)
| E_seppow φ a : IZFe (A_seppow φ a)
| E_powres x a : IZFe (A_powres x a).

(** ** IZF⁺ε: IZFε plus extensionality (Definition 15) *)

Definition A_ext x y := fImp (fEqv x y) (fEq x y).

Inductive IZFp : form -> Prop :=
| P_base φ : IZFe φ -> IZFp φ
| P_ext x y : IZFp (A_ext x y).

Lemma IZFm_IZFe φ : IZFm φ -> IZFe φ.
Proof. apply E_base. Qed.

Lemma IZFe_IZFp φ : IZFe φ -> IZFp φ.
Proof. apply P_base. Qed.

(** ** Closure under substitution *)

Lemma sht_ups σ t : subt (ups σ) (sht t) = sht (subt σ t).
Proof. symmetry. apply sht_subt. Qed.

Lemma renf_swap φ ξ ζ ξ' ζ' : (forall n, ξ (ζ n) = ξ' (ζ' n)) -> renf ξ (renf ζ φ) = renf ξ' (renf ζ' φ).
Proof.
  intros H. rewrite (proj2 ren_comp φ ξ ζ (fun n => ξ (ζ n))) by reflexivity.
  rewrite (proj2 ren_comp φ ξ' ζ' (fun n => ξ (ζ n))) by (intros; apply H). reflexivity.
Qed.

(** Commutation of a lifted substitution with a lifted weakening. *)
Lemma subf_up_renf σ φ :
  subf (ups (ups σ)) (renf (upr S) φ) = renf (upr S) (subf (ups σ) φ).
Proof.
  rewrite (proj2 subst_ren φ _ _ (fun n => ups (ups σ) (upr S n))) by reflexivity.
  rewrite (proj2 ren_subst_comm φ _ _ (fun n => rent (upr S) (ups σ n))) by reflexivity.
  apply subf_ext. intros [|n]; cbn; [reflexivity|].
  rewrite (proj1 ren_comp (σ n) (upr S) S (fun k => S (S k))) by reflexivity.
  rewrite (proj1 ren_comp (σ n) S S (fun k => S (S k))) by reflexivity. reflexivity.
Qed.

Lemma subf_up2_renf σ φ :
  subf (ups (ups (ups σ))) (renf (upr (upr S)) φ) = renf (upr (upr S)) (subf (ups (ups σ)) φ).
Proof.
  rewrite (proj2 subst_ren φ _ _ (fun n => ups (ups (ups σ)) (upr (upr S) n))) by reflexivity.
  rewrite (proj2 ren_subst_comm φ _ _ (fun n => rent (upr (upr S)) (ups (ups σ) n))) by reflexivity.
  apply subf_ext. intros [|[|n]]; cbn; [reflexivity|reflexivity|].
  rewrite !rent_rent. apply rent_ext. reflexivity.
Qed.

Lemma subf_fExU σ χ : subf σ (fExU χ) = fExU (subf (ups σ) χ).
Proof. unfold fExU. cbn. rewrite subf_up_renf. reflexivity. Qed.

Lemma subf_repl_body σ ψ b : subf (ups σ) (repl_body ψ b) = repl_body (subf (ups (ups σ)) ψ) (subt σ b).
Proof.
  unfold repl_body.
  rewrite (proj2 subst_comp ψ _ _ (fun n => subt (ups σ) ((sht b .: x0 .: fun k => tvar (S k)) n))) by reflexivity.
  rewrite (proj2 subst_comp ψ _ _ (fun n => subt (sht (subt σ b) .: x0 .: fun k => tvar (S k)) (ups (ups σ) n))) by reflexivity.
  apply subf_ext. intros [|[|n]]; cbn.
  - rewrite sht_ups. reflexivity.
  - reflexivity.
  - rewrite !subt_sht. apply (proj1 ren_subst). intros k. reflexivity.
Qed.

Lemma IZFm_closed : closed_sub IZFm.
Proof.
  intros φ σ H. destruct H; cbn.
  - apply M_empty.
  - unfold A_omega; cbn. rewrite sht_ups. apply M_omega.
  - apply M_pair.
  - unfold A_union; cbn. rewrite !sht_ups. apply M_union.
  - unfold A_wpow; cbn. rewrite !sht_ups. apply M_wpow.
  - unfold A_mem; cbn. rewrite !sht_ups. apply M_mem.
  - unfold A_sub; cbn. rewrite !sht_ups. apply M_sub.
  - apply M_eqv.
  - unfold A_sep; cbn. rewrite inst_subf. apply M_sep.
  - unfold A_ind; cbn. rewrite subf_up_renf. apply M_ind.
  - unfold A_coll; cbn. rewrite !sht_ups, subf_up2_renf. apply M_coll.
Qed.

Lemma IZFe_closed : closed_sub IZFe.
Proof.
  intros φ σ H. destruct H; cbn.
  - apply E_base, IZFm_closed, H.
  - unfold A_repl; cbn [subf subt]. rewrite !sht_ups, subf_up_renf, subf_repl_body. apply E_repl.
  - apply E_seppow.
  - unfold A_powres; cbn. rewrite !sht_ups. apply E_powres.
Qed.

Lemma IZFp_closed : closed_sub IZFp.
Proof.
  intros φ σ H. destruct H; cbn.
  - apply P_base, IZFe_closed, H.
  - apply P_ext.
Qed.

(** ** Tactics: adding an axiom as a hypothesis *)

(** ** Theory inclusions and closure, as classes *)

Class Ext (T0 T : form -> Prop) := ext : forall φ, T0 φ -> T φ.
Class Closed (T : form -> Prop) := closedT : closed_sub T.

#[export] Instance ext_refl T : Ext T T := fun φ H => H.
#[export] Instance ext_me : Ext IZFm IZFe := E_base.
#[export] Instance ext_mp : Ext IZFm IZFp := fun φ H => P_base _ (E_base _ H).
#[export] Instance ext_ep : Ext IZFe IZFp := P_base.
#[export] Instance closed_m : Closed IZFm := IZFm_closed.
#[export] Instance closed_e : Closed IZFe := IZFe_closed.
#[export] Instance closed_p : Closed IZFp := IZFp_closed.

Lemma p_useL {T0 T} {HE : Ext T0 T} {HC : Closed T} Δ φ σ Γ G :
  prv T0 Δ φ -> subf σ φ = G -> Forall (fun χ => prv T Γ (subf σ χ)) Δ -> prv T Γ G.
Proof.
  intros H <- K. apply (p_use T HC Δ); [eapply prv_mono; [exact HE|exact H]|].
  intros χ Hχ. rewrite Forall_forall in K. apply K, Hχ.
Qed.

Lemma p_haveL {T0 T} {HE : Ext T0 T} {HC : Closed T} Δ φ σ Γ G ψ :
  prv T0 Δ φ -> subf σ φ = G -> Forall (fun χ => prv T Γ (subf σ χ)) Δ -> prv T (G :: Γ) ψ -> prv T Γ ψ.
Proof. intros H E K L. eapply p_cut; [|exact L]. eapply p_useL; eassumption. Qed.

Tactic Notation "axm" constr(H) := refine (p_cut _ _ _ _ (p_th _ _ _ (ext _ H)) _).
Ltac forall_goals := first [apply Forall_nil | apply Forall_cons; [cbn | forall_goals]].
Tactic Notation "lem" constr(L) constr(σ) := eapply (p_useL _ _ σ _ _ L); [cbn; reflexivity|forall_goals].
Tactic Notation "haveL" constr(L) constr(σ) := eapply (p_haveL _ _ σ _ _ _ L); [cbn; reflexivity|forall_goals|cbn].

Lemma p_iffl T Γ n A B : nth_error Γ n = Some (fIff A B) -> prv T Γ A -> prv T Γ B.
Proof. intros H K. eapply p_iff1; [apply (p_nth _ _ _ _ H)|exact K]. Qed.

Lemma p_iffr T Γ n A B : nth_error Γ n = Some (fIff A B) -> prv T Γ B -> prv T Γ A.
Proof. intros H K. eapply p_iff2; [apply (p_nth _ _ _ _ H)|exact K]. Qed.

Tactic Notation "iffl" constr(n) := eapply (p_iffl _ _ n ); [reflexivity|cbn].
Tactic Notation "iffr" constr(n) := eapply (p_iffr _ _ n ); [reflexivity|cbn].

Lemma p_iffm T Γ n A B ψ : nth_error Γ n = Some (fIff A B) -> prv T Γ A -> prv T (B :: Γ) ψ -> prv T Γ ψ.
Proof. intros H K L. eapply p_cut; [|exact L]. eapply p_iffl; eassumption. Qed.

Lemma p_iffm' T Γ n A B ψ : nth_error Γ n = Some (fIff A B) -> prv T Γ B -> prv T (A :: Γ) ψ -> prv T Γ ψ.
Proof. intros H K L. eapply p_cut; [|exact L]. eapply p_iffr; eassumption. Qed.

Lemma p_app2 T Γ n A B C : nth_error Γ n = Some (fImp A (fImp B C)) -> prv T Γ A -> prv T Γ B -> prv T Γ C.
Proof. intros H K L. eapply p_impE; [eapply p_impE; [apply (p_nth _ _ _ _ H)|exact K]|exact L]. Qed.

Lemma p_keep T Γ l φ : prv T (map (fun i => nth i Γ fTop) l) φ -> prv T Γ φ.
Proof.
  intros H. eapply p_cuts; [exact H|]. intros χ Hχ. apply in_map_iff in Hχ as (i & <- & _).
  destruct (Nat.lt_ge_cases i (length Γ)) as [Hi|Hi].
  - apply p_ax, nth_In, Hi.
  - rewrite nth_overflow by exact Hi. apply p_topI.
Qed.

Tactic Notation "iffm" constr(n) := eapply (p_iffm _ _ n); [reflexivity|cbn|cbn].
Tactic Notation "iffm'" constr(n) := eapply (p_iffm' _ _ n); [reflexivity|cbn|cbn].
Tactic Notation "app2" constr(n) := eapply (p_app2 _ _ n); [reflexivity|cbn|cbn].
Tactic Notation "keep" constr(l) := apply (p_keep _ _ l); cbn.

(** ** Normalisation of substitutions *)

Lemma subf_renf σ ξ φ : subf σ (renf ξ φ) = subf (fun n => σ (ξ n)) φ.
Proof. apply subst_ren; reflexivity. Qed.
Lemma renf_subf ξ σ φ : renf ξ (subf σ φ) = subf (fun n => rent ξ (σ n)) φ.
Proof. apply ren_subst_comm; reflexivity. Qed.
Lemma subf_subf τ σ φ : subf τ (subf σ φ) = subf (fun n => subt τ (σ n)) φ.
Proof. apply subst_comp; reflexivity. Qed.
Lemma renf_as_subf ξ φ : renf ξ φ = subf (fun n => tvar (ξ n)) φ.
Proof. apply ren_subst; reflexivity. Qed.


(** Conversion of a hypothesis or of the goal along a syntactic equality. *)
Lemma p_conv T Γ A B : A = B -> prv T Γ A -> prv T Γ B.
Proof. intros -> H; exact H. Qed.

Lemma p_convh T Γ n A B ψ : nth_error Γ n = Some A -> A = B -> prv T (B :: Γ) ψ -> prv T Γ ψ.
Proof. intros H -> K. eapply p_cut; [apply (p_nth _ _ _ _ H)|exact K]. Qed.

Lemma p_rew T Γ φ s t G : G = inst φ t -> prv T Γ (fEq s t) -> prv T Γ (inst φ s) -> prv T Γ G.
Proof. intros -> H K. eapply p_leib; eassumption. Qed.

Ltac fcong := lazymatch goal with
  | |- subf _ ?X = subf _ ?X =>
      apply subf_ext; let n := fresh "n" in intros n;
      do 5 (destruct n as [|n]; [reflexivity|]); reflexivity
  | |- subf _ ?X = ?X =>
      apply (proj2 subst_id X); let n := fresh "n" in intros n;
      do 5 (destruct n as [|n]; [reflexivity|]); reflexivity
  | |- ?X = subf _ ?X => symmetry; fcong
  | |- ?a = ?a => reflexivity
  | |- _ => f_equal; fcong
  end.

Ltac fnorm := unfold inst, inst2;
  repeat (rewrite ?subf_renf, ?renf_subf, ?subf_subf, ?renf_renf); rewrite ?renf_as_subf; fcong.

Tactic Notation "convh" constr(n) constr(B) := eapply (p_convh _ _ n _ B); [reflexivity|fnorm|].
Tactic Notation "conv" constr(A) := apply (p_conv _ _ A); [fnorm|].
Tactic Notation "rew" constr(φ) constr(s) constr(t) := eapply (p_rew _ _ φ s t); [cbn; reflexivity|cbn|cbn].

(** The empty theory, for purely logical lemmas. *)
Definition Empty : form -> Prop := fun _ => False.
#[export] Instance ext_empty T : Ext Empty T := fun φ (H : Empty φ) => match H with end.
#[export] Instance closed_empty : Closed Empty := fun φ σ (H : Empty φ) => match H with end.

Lemma eq_sym_l : prv Empty [fEq x0 x1] (fEq x1 x0).
Proof. rew (fEq x0 x1) x0 x1; [hyp|apply p_refl]. Qed.

Lemma eq_trans_l : prv Empty [fEq x0 x1; fEq x1 x2] (fEq x0 x2).
Proof. rew (fEq x1 x0) x1 x2; [hyp|hyp]. Qed.
