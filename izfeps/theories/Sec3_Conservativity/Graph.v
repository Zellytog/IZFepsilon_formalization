(** * Translation of IZF⁺ε into IZF (Section 3.2)

    Each term t becomes its graph G(t, ρ, y): "y is the value of t", where
    ρ maps the variables of t to IZF variables. Formulas are translated
    homomorphically, atoms R(a, b) becoming
    ∃u v. G(a, u) ∧ G(b, v) ∧ R(u, v); ε and ∈ become ∈, ⊆ stays ⊆,
    ≃ and = become =. This is the extension by definition of Theorem 13,
    done once and for all on the tower Lₙ:
    - {x ε a | φ} ↦ {z ∈ a | φ(z)};
    - {ψ(α) | α ε a} ↦ {z | (∀α ∈ a. ∃!β. ψ(α, β)) ∧ ∃α ∈ a. ψ(α, z)},
      the total construction of the paper;
    - 𝒫(x) ↦ the power set of x;
    - ω ↦ the least inductive set. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax ISyntax.

(** z is empty, s = z ∪ {z}, w is inductive (IZF variables). *)
Definition iEmpty (z : nat) : iform := iAll (iNot (iMem 0 (S z))).
Definition iSuc (z s : nat) : iform := iAll (iIff (iMem 0 (S s)) (iOr (iMem 0 (S z)) (iEq 0 (S z)))).
Definition iInd (w : nat) : iform :=
  iAnd (iEx (iAnd (iMem 0 (S w)) (iEmpty 0)))
       (iAll (iImp (iMem 0 (S w)) (iEx (iAnd (iMem 0 (S (S w))) (iSuc 1 0))))).
(** y is the least inductive set. *)
Definition iOmega (y : nat) : iform := iAnd (iInd y) (iAll (iImp (iInd 0) (iSub (S y) 0))).

Definition atom (R : nat -> nat -> iform) (A B : iform) : iform := iEx (iAnd A (iEx (iAnd B (R 1 0)))).

Definition sh (k : nat) (ρ : nat -> nat) : nat -> nat := fun n => k + ρ n.

Fixpoint G (t : term) (ρ : nat -> nat) (y : nat) : iform :=
  match t with
  | tvar n => iEq y (ρ n)
  | tempty => iEmpty y
  | tomega => iOmega y
  | tpair a b => iEx (iAnd (G a (sh 1 ρ) 0) (iEx (iAnd (G b (sh 2 ρ) 0)
                   (iAll (iIff (iMem 0 (3 + y)) (iOr (iEq 0 2) (iEq 0 1)))))))
  | tunion a => iEx (iAnd (G a (sh 1 ρ) 0) (iAll (iIff (iMem 0 (2 + y)) (iEx (iAnd (iMem 0 2) (iMem 1 0))))))
  | tpow a => iEx (iAnd (G a (sh 1 ρ) 0) (iAll (iIff (iMem 0 (2 + y)) (iSub 0 1))))
  | tsep a φ => iEx (iAnd (G a (sh 1 ρ) 0) (iAll (iIff (iMem 0 (2 + y)) (iAnd (iMem 0 1) (T φ (0 .: sh 2 ρ))))))
  | trepl a ψ => iEx (iAnd (G a (sh 1 ρ) 0) (iAll (iIff (iMem 0 (2 + y))
                   (iAnd (iAll (iImp (iMem 0 2) (iEx (iAnd (T ψ (0 .: 1 .: sh 4 ρ))
                                                             (iAll (iImp (T ψ (0 .: 2 .: sh 5 ρ)) (iEq 0 1)))))))
                         (iEx (iAnd (iMem 0 2) (T ψ (1 .: 0 .: sh 3 ρ))))))))
  end
with T (φ : form) (ρ : nat -> nat) : iform :=
  match φ with
  | fTop => iTop
  | fBot => iBot
  | fAnd φ ψ => iAnd (T φ ρ) (T ψ ρ)
  | fOr φ ψ => iOr (T φ ρ) (T ψ ρ)
  | fImp φ ψ => iImp (T φ ρ) (T ψ ρ)
  | fAll φ => iAll (T φ (0 .: sh 1 ρ))
  | fEx φ => iEx (T φ (0 .: sh 1 ρ))
  | fEps a b => atom iMem (G a (sh 1 ρ) 0) (G b (sh 2 ρ) 0)
  | fMem a b => atom iMem (G a (sh 1 ρ) 0) (G b (sh 2 ρ) 0)
  | fSub a b => atom iSub (G a (sh 1 ρ) 0) (G b (sh 2 ρ) 0)
  | fEqv a b => atom iEq (G a (sh 1 ρ) 0) (G b (sh 2 ρ) 0)
  | fEq a b => atom iEq (G a (sh 1 ρ) 0) (G b (sh 2 ρ) 0)
  end.

(** ** Extensionality in the environment, renamings *)

Ltac icong := repeat match goal with
  | |- iEx _ = iEx _ => apply f_equal
  | |- iAll _ = iAll _ => apply f_equal
  | |- iAnd _ _ = iAnd _ _ => apply f_equal2
  | |- iOr _ _ = iOr _ _ => apply f_equal2
  | |- iImp _ _ = iImp _ _ => apply f_equal2
  | |- iMem _ _ = iMem _ _ => apply f_equal2
  | |- iEq _ _ = iEq _ _ => apply f_equal2
  | |- iSub _ _ = iSub _ _ => apply f_equal2
  | |- atom ?R _ _ = atom ?R _ _ => apply (f_equal2 (atom R))
  end.

Ltac pwsolve := let n := fresh "n" in
  intros n; destruct n as [|[|[|[|[|n]]]]]; cbn; try unfold sh; cbn; try reflexivity; repeat apply eq_S; auto.

Ltac leaf := first [reflexivity | solve [auto] |
  match goal with IH : _ |- _ => solve [eapply eq_trans; [eapply IH|reflexivity]; pwsolve] end].

Lemma GT_ext :
  (forall t ρ ρ' y, (forall n, ρ' n = ρ n) -> G t ρ y = G t ρ' y) /\
  (forall φ ρ ρ', (forall n, ρ' n = ρ n) -> T φ ρ = T φ ρ').
Proof. apply syn_ind; intros; cbn; unfold atom; icong; leaf. Qed.

(** Renaming the source variables. *)
Lemma GT_ren :
  (forall t ξ ρ ρ' y, (forall n, ρ' n = ρ (ξ n)) -> G (rent ξ t) ρ y = G t ρ' y) /\
  (forall φ ξ ρ ρ', (forall n, ρ' n = ρ (ξ n)) -> T (renf ξ φ) ρ = T φ ρ').
Proof. apply syn_ind; intros; cbn; unfold atom; icong; leaf. Qed.

(** Renaming the target variables. *)
Lemma GT_iren :
  (forall t ξ ρ ρ' y, (forall n, ρ' n = ξ (ρ n)) -> iren ξ (G t ρ y) = G t ρ' (ξ y)) /\
  (forall φ ξ ρ ρ', (forall n, ρ' n = ξ (ρ n)) -> iren ξ (T φ ρ) = T φ ρ').
Proof. apply syn_ind; intros; cbn; unfold atom; icong; leaf. Qed.
