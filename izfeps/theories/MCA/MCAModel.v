(** * The model V(E) for a monadic combinatory algebra

    The evidenced frame of any MCA, with its fixed point combinator
    (MCAFrame.v), fits into Theorem 26. Φ = A → Prop is "essentially
    small" without any encoding (Φ₀ ≜ A → Prop); only the named collection
    hypothesis remains, as for the PCA on ℕ (Examples/NatModel.v). *)

From Stdlib Require Import List.
From IZFe Require Import Syntax Deriv Theories Frame VE Model Realize MCAFrame.

Section MCAModel.

Context (A : mca).
Local Notation F := (mca_frame A).
Local Notation V := (@V F).

Context (coll : forall T : Type, (T -> V) -> (V -> V -> pcar F) -> V).
Context (coll_proper : forall T (xs xs' : T -> V) (ψ ψ' : V -> V -> pcar F),
  Rproper F ψ -> (forall t, teq (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
  teq (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> V) (ψ : V -> V -> pcar F), Rproper F ψ ->
  forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub (coll T xs ψ) s)).

Definition Φ0M : Type := mc A -> Prop.
Definition encM (φ : pcar F) : Φ0M := φ.
Definition decM (φ : Φ0M) : pcar F := φ.

Corollary mca_IZFe_realized φ : prv IZFe nil φ -> urealized F Φ0M decM coll φ.
Proof.
  exact (IZFe_realized F Φ0M encM decM (fun φ => peq_refl φ) coll coll_proper coll_spec
           (mca_fix A) (mca_fixpoint A) φ).
Qed.

End MCAModel.
