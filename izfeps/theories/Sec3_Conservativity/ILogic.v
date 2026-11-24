(** * Tools for reasoning inside IZF *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax ISyntax.

Notation "Γ ⊢i φ" := (iprv IZF Γ φ) (at level 70).

Lemma i_iffl Γ n A B : nth_error Γ n = Some (iIff A B) -> Γ ⊢i A -> Γ ⊢i B.
Proof. intros H K. eapply i_impE; [eapply i_andE1, (i_nth _ _ _ _ H)|exact K]. Qed.
Lemma i_iffr Γ n A B : nth_error Γ n = Some (iIff A B) -> Γ ⊢i B -> Γ ⊢i A.
Proof. intros H K. eapply i_impE; [eapply i_andE2, (i_nth _ _ _ _ H)|exact K]. Qed.
Lemma i_iffm Γ n A B ψ : nth_error Γ n = Some (iIff A B) -> Γ ⊢i A -> (B :: Γ) ⊢i ψ -> Γ ⊢i ψ.
Proof. intros H K L. eapply i_cut; [|exact L]. eapply i_iffl; eassumption. Qed.
Lemma i_iffm' Γ n A B ψ : nth_error Γ n = Some (iIff A B) -> Γ ⊢i B -> (A :: Γ) ⊢i ψ -> Γ ⊢i ψ.
Proof. intros H K L. eapply i_cut; [|exact L]. eapply i_iffr; eassumption. Qed.
Lemma i_app2 Γ n A B C : nth_error Γ n = Some (iImp A (iImp B C)) -> Γ ⊢i A -> Γ ⊢i B -> Γ ⊢i C.
Proof. intros H K L. eapply i_impE; [eapply i_impE; [apply (i_nth _ _ _ _ H)|exact K]|exact L]. Qed.

Lemma i_useL Δ φ ξ Γ G : iprv IZF Δ φ -> iren ξ φ = G -> Forall (fun χ => Γ ⊢i iren ξ χ) Δ -> Γ ⊢i G.
Proof.
  intros H <- K. rewrite Forall_forall in K. exact (i_use IZF IZF_closed Δ φ ξ Γ H K).
Qed.
Lemma i_haveL Δ φ ξ Γ G ψ : iprv IZF Δ φ -> iren ξ φ = G -> Forall (fun χ => Γ ⊢i iren ξ χ) Δ -> (G :: Γ) ⊢i ψ -> Γ ⊢i ψ.
Proof. intros H E K L. eapply i_cut; [|exact L]. exact (i_useL _ _ _ _ _ H E K). Qed.
Lemma i_rew Γ φ m n G : G = iinst φ n -> Γ ⊢i iEq m n -> Γ ⊢i iinst φ m -> Γ ⊢i G.
Proof. intros -> H K. eapply i_leib; eassumption. Qed.
Lemma i_keep Γ l φ : iprv IZF (map (fun i => nth i Γ iTop) l) φ -> Γ ⊢i φ.
Proof.
  intros H. eapply i_cuts; [exact H|]. intros χ Hχ. apply in_map_iff in Hχ as (i & <- & _).
  destruct (Nat.lt_ge_cases i (length Γ)) as [Hi|Hi].
  - apply i_ax, nth_In, Hi.
  - rewrite nth_overflow by exact Hi. apply i_topI.
Qed.
Lemma i_conv Γ A B : A = B -> Γ ⊢i A -> Γ ⊢i B.
Proof. intros -> H; exact H. Qed.
Lemma i_convh Γ n A B ψ : nth_error Γ n = Some A -> A = B -> (B :: Γ) ⊢i ψ -> Γ ⊢i ψ.
Proof. intros H -> K. eapply i_cut; [apply (i_nth _ _ _ _ H)|exact K]. Qed.
Lemma i_th' Γ φ : IZF φ -> Γ ⊢i φ.
Proof. intros; apply i_th; assumption. Qed.

Ltac iforall_goals := first [apply Forall_nil | apply Forall_cons; [cbn | iforall_goals]].
Tactic Notation "iffl" constr(n) := eapply (i_iffl _ n); [reflexivity|cbn].
Tactic Notation "iffr" constr(n) := eapply (i_iffr _ n); [reflexivity|cbn].
Tactic Notation "iffm" constr(n) := eapply (i_iffm _ n); [reflexivity|cbn|cbn].
Tactic Notation "iffm'" constr(n) := eapply (i_iffm' _ n); [reflexivity|cbn|cbn].
Tactic Notation "iapp2" constr(n) := eapply (i_app2 _ n); [reflexivity|cbn|cbn].
Tactic Notation "ilem" constr(L) constr(ξ) := eapply (i_useL _ _ ξ _ _ L); [cbn; reflexivity|iforall_goals].
Tactic Notation "ihave" constr(L) constr(ξ) := eapply (i_haveL _ _ ξ _ _ _ L); [cbn; reflexivity|iforall_goals|cbn].
Tactic Notation "irew" constr(φ) constr(m) constr(n) := eapply (i_rew _ φ m n); [cbn; reflexivity|cbn|cbn].
Tactic Notation "ikeep" constr(l) := apply (i_keep _ l); cbn.
Tactic Notation "iax" constr(H) := refine (i_cut _ _ _ _ (i_th' _ _ H) _).

(** ** Equality *)

Lemma ieq_sym : [iEq 0 1] ⊢i iEq 1 0.
Proof. irew (iEq 0 1) 0 1; [ihyp|apply i_refl]. Qed.
Lemma ieq_trans : [iEq 0 1; iEq 1 2] ⊢i iEq 0 2.
Proof. irew (iEq 1 0) 1 2; ihyp. Qed.
Lemma ieq_sym_t Γ m n : Γ ⊢i iEq m n -> Γ ⊢i iEq n m.
Proof. intros H. ilem ieq_sym (il [m; n]). exact H. Qed.
Lemma ieq_trans_t Γ a b c : Γ ⊢i iEq a b -> Γ ⊢i iEq b c -> Γ ⊢i iEq a c.
Proof. intros H K. ilem ieq_trans (il [a; b; c]); assumption. Qed.

(** ** Congruences for ⇔ *)

Lemma ii_refl Γ A : Γ ⊢i iIff A A.
Proof. apply i_iffI; ihyp. Qed.
Lemma ii_sym Γ A B : Γ ⊢i iIff A B -> Γ ⊢i iIff B A.
Proof. intros H. apply i_andI; [eapply i_andE2|eapply i_andE1]; exact H. Qed.
Lemma ii_trans Γ A B C : Γ ⊢i iIff A B -> Γ ⊢i iIff B C -> Γ ⊢i iIff A C.
Proof.
  intros H K. apply i_iffI.
  - eapply i_impE; [eapply i_andE1, i_wk, K|]. eapply i_impE; [eapply i_andE1, i_wk, H|ihyp].
  - eapply i_impE; [eapply i_andE2, i_wk, H|]. eapply i_impE; [eapply i_andE2, i_wk, K|ihyp].
Qed.
Lemma ii_l Γ A B : Γ ⊢i iIff A B -> Γ ⊢i A -> Γ ⊢i B.
Proof. intros H K. eapply i_impE; [eapply i_andE1, H|exact K]. Qed.
Lemma ii_r Γ A B : Γ ⊢i iIff A B -> Γ ⊢i B -> Γ ⊢i A.
Proof. intros H K. eapply i_impE; [eapply i_andE2, H|exact K]. Qed.

Lemma ii_and Γ A A' B B' : Γ ⊢i iIff A A' -> Γ ⊢i iIff B B' -> Γ ⊢i iIff (iAnd A B) (iAnd A' B').
Proof.
  intros H K. apply i_iffI; idand 0; apply i_andI.
  all: first [eapply ii_l; [apply i_wk, i_wk, i_wk; eassumption|ihyp]
             |eapply ii_r; [apply i_wk, i_wk, i_wk; eassumption|ihyp]].
Qed.
Lemma ii_or Γ A A' B B' : Γ ⊢i iIff A A' -> Γ ⊢i iIff B B' -> Γ ⊢i iIff (iOr A B) (iOr A' B').
Proof.
  intros H K. apply i_iffI; idor 0.
  - apply i_orI1. eapply ii_l; [apply i_wk, i_wk; eassumption|ihyp].
  - apply i_orI2. eapply ii_l; [apply i_wk, i_wk; eassumption|ihyp].
  - apply i_orI1. eapply ii_r; [apply i_wk, i_wk; eassumption|ihyp].
  - apply i_orI2. eapply ii_r; [apply i_wk, i_wk; eassumption|ihyp].
Qed.
Lemma ii_imp Γ A A' B B' : Γ ⊢i iIff A A' -> Γ ⊢i iIff B B' -> Γ ⊢i iIff (iImp A B) (iImp A' B').
Proof.
  intros H K. apply i_iffI; apply i_impI.
  - eapply ii_l; [apply i_wk, i_wk, K|]. eapply i_impE; [ihyp|]. eapply ii_r; [apply i_wk, i_wk, H|ihyp].
  - eapply ii_r; [apply i_wk, i_wk, K|]. eapply i_impE; [ihyp|]. eapply ii_l; [apply i_wk, i_wk, H|ihyp].
Qed.

Lemma ii_inst φ : iinst (iren (upr S) φ) 0 = φ.
Proof. unfold iinst. rewrite (iren_comp _ _ _ (fun k => k)) by (intros [|k]; reflexivity). apply iren_id; reflexivity. Qed.

Lemma i_inst0 Γ A : In (iAll (iren (upr S) A)) Γ -> Γ ⊢i A.
Proof. intros H. apply (i_conv _ (iinst (iren (upr S) A) 0)); [apply ii_inst|]. apply i_allE, i_ax, H. Qed.

Lemma i_ex0 Γ A : Γ ⊢i A -> Γ ⊢i iEx (iren (upr S) A).
Proof. intros H. apply (i_exI _ _ _ 0). rewrite ii_inst. exact H. Qed.

Lemma ii_all Γ A A' : map ish Γ ⊢i iIff A A' -> Γ ⊢i iIff (iAll A) (iAll A').
Proof.
  intros H. apply i_iffI; iintro_all.
  - eapply ii_l; [apply i_wk, H|]. apply i_inst0. left; reflexivity.
  - eapply ii_r; [apply i_wk, H|]. apply i_inst0. left; reflexivity.
Qed.

Lemma ii_ex Γ A A' : map ish Γ ⊢i iIff A A' -> Γ ⊢i iIff (iEx A) (iEx A').
Proof.
  intros H. apply i_iffI; idex 0; apply i_ex0.
  - eapply ii_l; [apply i_wk, i_wk, H|ihyp].
  - eapply ii_r; [apply i_wk, i_wk, H|ihyp].
Qed.

Lemma ii_iff Γ A A' B B' : Γ ⊢i iIff A A' -> Γ ⊢i iIff B B' -> Γ ⊢i iIff (iIff A B) (iIff A' B').
Proof. intros H K. apply ii_and; apply ii_imp; assumption. Qed.

Lemma iprv_sh Γ φ : Γ ⊢i φ -> map ish Γ ⊢i ish φ.
Proof. intros H. exact (iprv_ren IZF IZF_closed Γ φ H S). Qed.
