(** * An instance: a non-deterministic MCA with the angelic modality

    Codes are λ-codes λⁿ.e and a code flip, with flip·c returning either
    λ₁.0 or λ₁.1 (the selectors), as in the relational combinatory
    algebras of Cohen–Grunfeld–Kirst–Miquey (Example 20). The monad is the
    powerset monad M X ≜ X → Prop, application is given by a big-step
    relational semantics (a divergent computation has no result), and the
    modality is the angelic one, ♢ m Q ≜ ∃x ∈ m, Q(x).

    The frame is consistent (⊥ is not realized), and its model V(E)
    realizes IZFε under the named collection hypothesis. *)

From Stdlib Require Import List.
From IZFe Require Import Syntax Deriv Theories Frame VE Model Realize MCAFrame MCAModel.

Inductive ncode : Type := NLam (n : nat) (e : xp ncode) | Flip.

Inductive nred : ncode -> ncode -> ncode -> Prop :=
| n_lamS n e a : nred (NLam (S n) e) a (NLam n (xsub0 e a))
| n_lam0 e a r : nered (xsub0 e a) r -> nred (NLam 0 e) a r
| n_flipK a : nred Flip a (NLam 1 (xv 0))
| n_flipKI a : nred Flip a (NLam 1 (xv 1))
with nered : xp ncode -> ncode -> Prop :=
| ne_v n : nered (xv n) (NLam 0 (xv 0))
| ne_c c : nered (xc c) c
| ne_a f a cf ca r : nered f cf -> nered a ca -> nred cf ca r -> nered (xa f a) r.

Definition nret (X : Type) (x : X) : X -> Prop := fun y => y = x.
Definition nbind (X Y : Type) (m : X -> Prop) (f : X -> Y -> Prop) : Y -> Prop := fun y => exists x, m x /\ f x y.
Definition ndia (X : Type) (m : X -> Prop) (Q : X -> Prop) : Prop := exists x, m x /\ Q x.

(** The relational semantics of expressions is the call-by-value
    evaluation ν of Definition 4, in the powerset monad. *)
Lemma nered_eval e r : nered e r <-> @xeval ncode (fun X => X -> Prop) (nret ncode) (nbind ncode ncode) nred (NLam 0 (xv 0)) e r.
Proof.
  revert r. induction e as [n|c|f IHf a IHa]; intros r; cbn; unfold nret, nbind.
  - split; [intros H; inversion H; reflexivity|intros ->; constructor].
  - split; [intros H; inversion H; reflexivity|intros ->; constructor].
  - split.
    + intros H. inversion H; subst. exists cf. split; [apply IHf; assumption|]. exists ca. split; [apply IHa; assumption|assumption].
    + intros (cf & Hf & ca & Ha & Hr). econstructor; [apply IHf, Hf|apply IHa, Ha|exact Hr].
Qed.

Definition nd_mca : mca.
Proof.
  refine {| mc := ncode; M := fun X => X -> Prop; ret := nret; bind := nbind; app := nred;
            mlam := NLam; dia := ndia |}.
  - intros X x Q. unfold ndia, nret. split; [intros (y & -> & H); exact H|intros H; exists x; auto].
  - intros X Y m f Q. unfold ndia, nbind. split.
    + intros (y & (x & Hm & Hf) & HQ). exists x. split; [exact Hm|exists y; auto].
    + intros (x & Hm & y & Hf & HQ). exists y. split; [exists x; auto|exact HQ].
  - intros X m Q Q' H (x & Hm & HQ). exists x. auto.
  - intros n e c Q. unfold ndia, nret. split.
    + intros (r & Hr & HQ). inversion Hr; subst. exists (NLam n (xsub0 e c)). auto.
    + intros (r & -> & HQ). exists (NLam n (xsub0 e c)). split; [constructor|exact HQ].
  - intros e c Q. unfold ndia. split.
    + intros (r & Hr & HQ). inversion Hr; subst. exists r. split; [apply nered_eval; assumption|exact HQ].
    + intros (r & Hr & HQ). exists r. split; [constructor; apply nered_eval, Hr|exact HQ].
Defined.

Definition nd_frame : frame := mca_frame nd_mca.

(** flip is genuinely non-deterministic: it has two different results. *)
Lemma flip_nd : nred Flip Flip (NLam 1 (xv 0)) /\ nred Flip Flip (NLam 1 (xv 1)) /\ NLam 1 (xv 0) <> NLam 1 (xv 1).
Proof. split; [constructor|split; [constructor|discriminate]]. Qed.

Theorem nd_fixpoint : fixpoint_comb nd_frame (mca_fix nd_mca).
Proof. apply mca_fixpoint. Qed.

(** With the angelic modality, ♢ m (λ_. False) never holds: the frame is consistent. *)
Theorem nd_consistent : ~ exists e, @ftop nd_frame —[e]→ fbot.
Proof. apply mca_consistent. intros f a (r & _ & []). Qed.

Section NdModel.

Local Notation V := (@V nd_frame).

Context (coll : forall T : Type, (T -> V) -> (V -> V -> pcar nd_frame) -> V).
Context (coll_proper : forall T (xs xs' : T -> V) (ψ ψ' : V -> V -> pcar nd_frame),
  Rproper nd_frame ψ -> (forall t, teq (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
  teq (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> V) (ψ : V -> V -> pcar nd_frame), Rproper nd_frame ψ ->
  forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub (coll T xs ψ) s)).

Corollary nd_IZFe_realized φ : prv IZFe nil φ -> urealized nd_frame (Φ0M nd_mca) (decM nd_mca) coll φ.
Proof. exact (mca_IZFe_realized nd_mca coll coll_proper coll_spec φ). Qed.

End NdModel.
