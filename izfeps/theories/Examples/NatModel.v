(** * The model V(E) for the PCA on ℕ

    The frame of the PCA of the combinators coded in ℕ, with its fixed
    point combinator, fits into Theorem 26. Φ = ℕ → Prop is "essentially
    small" without any encoding (Φ₀ ≜ ℕ → Prop); only the named collection
    hypothesis remains. *)

From Stdlib Require Import List.
From IZFe Require Import Syntax Deriv Theories Frame VE Model Realize PCA.

Section NatModel.

Local Abbreviation V := (@V nat_frame).

Context (coll : forall T : Type, (T -> V) -> (V -> V -> pcar nat_frame) -> V).
Context (coll_proper : forall T (xs xs' : T -> V) (ψ ψ' : V -> V -> pcar nat_frame),
  Rproper nat_frame ψ -> (forall t, teq (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
  teq (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> V) (ψ : V -> V -> pcar nat_frame), Rproper nat_frame ψ ->
  forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub (coll T xs ψ) s)).

Definition Φ0N : Type := nat -> Prop.
Definition encN (φ : pcar nat_frame) : Φ0N := φ.
Definition decN (φ : Φ0N) : pcar nat_frame := φ.

Corollary nat_IZFe_realized φ : prv IZFe nil φ -> urealized nat_frame Φ0N decN coll φ.
Proof.
  exact (IZFe_realized nat_frame Φ0N encN decN (fun φ => peq_refl φ) coll coll_proper coll_spec
           (pca_fix natPCA) nat_fixpoint φ).
Qed.

End NatModel.
