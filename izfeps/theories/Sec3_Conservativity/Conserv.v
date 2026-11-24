(** * Section 3.2: IZF⁺ε (Lemma 16) *)

From Stdlib Require Import List.
Import ListNotations.
From IZFe Require Import Syntax Deriv Theories Basic.

Local Notation "Γ ⊢p φ" := (prv IZFp Γ φ) (at level 70).

(** Lemma 16: IZF⁺ε ⊢ x ε y ⇔ x ∈ y. *)
Lemma lemma16 : [] ⊢p fIff (fEps x0 x1) (fMem x0 x1).
Proof.
  split_iff.
  - lem eps_mem (sl [x0; x1]). hyp.
  - axm (M_mem x0 x1). iffm 0; [hyp|]. dex 0. dand 0.
    (* x' = 0, x = 1, y = 2 *)
    axm (P_ext x1 x0). mp 0; [hyp|].
    rew (fEps x0 x3) x0 x1; [lem eq_sym_l (sl [x1; x0]); hyp|hyp].
Qed.

(** Consequence: x ⊆ y ⇔ ∀z. z ε x ⇒ z ε y. *)
Lemma sub_eps : [] ⊢p fIff (fSub x0 x1) (fAll (fImp (fEps x0 x1) (fEps x0 x2))).
Proof.
  axm (M_sub x0 x1). split_iff.
  - iffm 1; [hyp|]. intro_all. intro_imp. spec 1 x0. mp 0; [hyp|].
    haveL lemma16 (sl [x0; x2]). iffm' 0; [hyp|]. hyp.
  - iffr 1. intro_all. intro_imp. spec 1 x0. mp 0; [hyp|].
    haveL lemma16 (sl [x0; x2]). iffm 0; [hyp|]. hyp.
Qed.
