(** * Section 2.2: induction on ω (Theorem 7) *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax Deriv Theories Basic Extension.

Local Notation "Γ ⊢m φ" := (prv IZFm Γ φ) (at level 70).

(** y ε S(y). *)
Lemma eps_suc : [] ⊢m fEps x0 (tsuc x0).
Proof.
  unfold tsuc. axm (M_union (tpair x0 (tpair x0 x0)) x0). iffr 0. exists_ (tpair x0 x0). split_and.
  - axm (M_pair x0 (tpair x0 x0) (tpair x0 x0)). iffr 0. apply p_orI2, p_refl.
  - axm (M_pair x0 x0 x0). iffr 0. apply p_orI1, p_refl.
Qed.

(** φ(S n), for φ with bound variable 0. *)
Definition at_suc (φ : form) : form := subf (tsuc x0 .: fun k => tvar (S k)) φ.

Definition ind_omega (φ : form) : form :=
  fImp (inst φ tempty)
       (fImp (fAll (fImp (fEps x0 tomega) (fImp φ (at_suc φ))))
             (fAll (fImp (fEps x0 tomega) φ))).

(** Theorem 7: if φ(0) and ∀n ε ω, φ(n) ⇒ φ(S n), then ∀x ε ω, φ(x). *)
Theorem thm7 φ : [] ⊢m ind_omega φ.
Proof.
  unfold ind_omega, at_suc. intro_imp. intro_imp.
  axm (M_ind (fImp (fEps x0 tomega) φ)). app 0. intro_all. intro_imp. intro_imp.
  (* x = 0 ; Γ = [x ε ω; IH; …; HS; H0] *)
  axm (M_omega x0). iffm 0; [hyp|]. dor 0.
  - eapply (p_rew _ _ (renf (upr S) φ) tempty x0); [symmetry; apply inst_up_shf| |].
    + lem eq_sym_l (sl [x0; tempty]). hyp.
    + apply (p_conv _ _ (shf (inst φ tempty))); [fnorm|hyp].
  - dex 0. dand 0.
    (* x' = 0, x = 1 *)
    cut_ (fEps x0 x1).
    { rew (fEps x1 x0) (tsuc x0) x1; [lem eq_sym_l (sl [x1; tsuc x0]); hyp|lem eps_suc (sl [x0])]. }
    spec 8 x0. mp 0; [hyp|]. mp 0; [hyp|].
    spec 13 x0. mp 0; [hyp|]. mp 0; [hyp|].
    eapply (p_rew _ _ (subf (x0 .: fun k => tvar (S (S (S k)))) φ) (tsuc x0) x1); [fnorm| |].
    + lem eq_sym_l (sl [x1; tsuc x0]). hyp.
    + convh 0 (inst (subf (x0 .: fun k => tvar (S (S (S k)))) φ) (tsuc x0)). hyp.
Qed.
