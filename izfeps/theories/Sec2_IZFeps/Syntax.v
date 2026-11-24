(** * Syntax of IZFε

    A mutual inductive type of terms and formulas, specific to IZFε
    (Definitions 1 and 5 of the paper). Variables are de Bruijn indices,
    without intrinsic scoping: a term is an ordinary tree, and the
    substitution lemmas are those of the σ-calculus.

    Term binders are constructors:
    - [tsep a φ] is {x ε a | φ}: in φ, variable 0 is x and variable k+1
      is variable k of the context (the parameters);
    - [trepl a ψ] is {ψ(α) | α ε a}: in ψ, variable 1 is α, variable 0 is
      β, and variable k+2 is variable k of the context.

    This replaces the hierarchy Lₙ of the paper: a term whose bound
    formulas have level ≤ n is a symbol of Lₙ₊₁, and conversely ([level]
    below measures this level). *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Inductive term : Type :=
| tvar (n : nat)
| tempty
| tomega
| tpair (a b : term)
| tunion (a : term)
| tpow (a : term)
| tsep (a : term) (φ : form)
| trepl (a : term) (ψ : form)
with form : Type :=
| fTop
| fBot
| fAnd (φ ψ : form)
| fOr (φ ψ : form)
| fImp (φ ψ : form)
| fAll (φ : form)
| fEx (φ : form)
| fEps (a b : term)
| fMem (a b : term)
| fSub (a b : term)
| fEqv (a b : term)
| fEq (a b : term).

Scheme term_ind2 := Induction for term Sort Prop
with form_ind2 := Induction for form Sort Prop.
Combined Scheme syn_ind from term_ind2, form_ind2.

(** Derived connectives. *)
Notation fIff φ ψ := (fAnd (fImp φ ψ) (fImp ψ φ)).
Notation fNot φ := (fImp φ fBot).

(** ** The level of a term in the hierarchy Lₙ *)

Fixpoint tlevel (t : term) : nat :=
  match t with
  | tvar _ | tempty | tomega => 0
  | tpair a b => Nat.max (tlevel a) (tlevel b)
  | tunion a | tpow a => tlevel a
  | tsep a φ | trepl a φ => Nat.max (tlevel a) (S (flevel φ))
  end
with flevel (φ : form) : nat :=
  match φ with
  | fTop | fBot => 0
  | fAnd φ ψ | fOr φ ψ | fImp φ ψ => Nat.max (flevel φ) (flevel ψ)
  | fAll φ | fEx φ => flevel φ
  | fEps a b | fMem a b | fSub a b | fEqv a b | fEq a b => Nat.max (tlevel a) (tlevel b)
  end.

(** ** Renamings *)

Definition upr (ξ : nat -> nat) : nat -> nat :=
  fun n => match n with 0 => 0 | S n => S (ξ n) end.

Fixpoint rent (ξ : nat -> nat) (t : term) : term :=
  match t with
  | tvar n => tvar (ξ n)
  | tempty => tempty
  | tomega => tomega
  | tpair a b => tpair (rent ξ a) (rent ξ b)
  | tunion a => tunion (rent ξ a)
  | tpow a => tpow (rent ξ a)
  | tsep a φ => tsep (rent ξ a) (renf (upr ξ) φ)
  | trepl a ψ => trepl (rent ξ a) (renf (upr (upr ξ)) ψ)
  end
with renf (ξ : nat -> nat) (φ : form) : form :=
  match φ with
  | fTop => fTop
  | fBot => fBot
  | fAnd φ ψ => fAnd (renf ξ φ) (renf ξ ψ)
  | fOr φ ψ => fOr (renf ξ φ) (renf ξ ψ)
  | fImp φ ψ => fImp (renf ξ φ) (renf ξ ψ)
  | fAll φ => fAll (renf (upr ξ) φ)
  | fEx φ => fEx (renf (upr ξ) φ)
  | fEps a b => fEps (rent ξ a) (rent ξ b)
  | fMem a b => fMem (rent ξ a) (rent ξ b)
  | fSub a b => fSub (rent ξ a) (rent ξ b)
  | fEqv a b => fEqv (rent ξ a) (rent ξ b)
  | fEq a b => fEq (rent ξ a) (rent ξ b)
  end.

Notation sht := (rent S).
Notation shf := (renf S).

(** ** Simultaneous substitutions *)

Definition ups (σ : nat -> term) : nat -> term :=
  fun n => match n with 0 => tvar 0 | S n => sht (σ n) end.

Fixpoint subt (σ : nat -> term) (t : term) : term :=
  match t with
  | tvar n => σ n
  | tempty => tempty
  | tomega => tomega
  | tpair a b => tpair (subt σ a) (subt σ b)
  | tunion a => tunion (subt σ a)
  | tpow a => tpow (subt σ a)
  | tsep a φ => tsep (subt σ a) (subf (ups σ) φ)
  | trepl a ψ => trepl (subt σ a) (subf (ups (ups σ)) ψ)
  end
with subf (σ : nat -> term) (φ : form) : form :=
  match φ with
  | fTop => fTop
  | fBot => fBot
  | fAnd φ ψ => fAnd (subf σ φ) (subf σ ψ)
  | fOr φ ψ => fOr (subf σ φ) (subf σ ψ)
  | fImp φ ψ => fImp (subf σ φ) (subf σ ψ)
  | fAll φ => fAll (subf (ups σ) φ)
  | fEx φ => fEx (subf (ups σ) φ)
  | fEps a b => fEps (subt σ a) (subt σ b)
  | fMem a b => fMem (subt σ a) (subt σ b)
  | fSub a b => fSub (subt σ a) (subt σ b)
  | fEqv a b => fEqv (subt σ a) (subt σ b)
  | fEq a b => fEq (subt σ a) (subt σ b)
  end.

Definition scons {A} (a : A) (f : nat -> A) : nat -> A :=
  fun n => match n with 0 => a | S n => f n end.

Notation "a .: f" := (scons a f) (at level 55, right associativity).

(** φ[t/0]: substitute t for variable 0 (and shift the others down). *)
Definition inst (φ : form) (t : term) : form := subf (t .: tvar) φ.
(** φ[t/0, u/1] (t for variable 0, u for variable 1). *)
Definition inst2 (φ : form) (u t : term) : form := subf (t .: u .: tvar) φ.

(** ** The σ-calculus *)

Lemma upr_ext ξ ξ' : (forall n, ξ n = ξ' n) -> forall n, upr ξ n = upr ξ' n.
Proof. intros H [|n]; cbn; congruence. Qed.

Lemma ren_ext :
  (forall t ξ ξ', (forall n, ξ n = ξ' n) -> rent ξ t = rent ξ' t) /\
  (forall φ ξ ξ', (forall n, ξ n = ξ' n) -> renf ξ φ = renf ξ' φ).
Proof.
  apply syn_ind; intros; cbn; f_equal; eauto using upr_ext.
Qed.

Definition rent_ext := proj1 ren_ext.
Definition renf_ext := proj2 ren_ext.

Lemma upr_comp ξ ζ θ : (forall n, θ n = ξ (ζ n)) -> forall n, upr θ n = upr ξ (upr ζ n).
Proof. intros H [|n]; cbn; congruence. Qed.

Lemma ren_comp :
  (forall t ξ ζ θ, (forall n, θ n = ξ (ζ n)) -> rent ξ (rent ζ t) = rent θ t) /\
  (forall φ ξ ζ θ, (forall n, θ n = ξ (ζ n)) -> renf ξ (renf ζ φ) = renf θ φ).
Proof.
  apply syn_ind; intros; cbn; f_equal; eauto; try (symmetry; auto; fail).
  all: (eapply H || eapply H0); repeat (apply upr_comp); intros; symmetry; auto.
Qed.

Lemma rent_rent ξ ζ t : rent ξ (rent ζ t) = rent (fun k => ξ (ζ k)) t.
Proof. apply ren_comp; reflexivity. Qed.

Lemma renf_renf ξ ζ φ : renf ξ (renf ζ φ) = renf (fun k => ξ (ζ k)) φ.
Proof. apply ren_comp; reflexivity. Qed.

Lemma subst_ext :
  (forall t σ τ, (forall n, σ n = τ n) -> subt σ t = subt τ t) /\
  (forall φ σ τ, (forall n, σ n = τ n) -> subf σ φ = subf τ φ).
Proof.
  assert (U : forall σ τ, (forall n, σ n = τ n) -> forall n, ups σ n = ups τ n).
  { intros σ τ H [|n]; cbn; congruence. }
  apply syn_ind; intros; cbn; try solve [auto | symmetry; auto]; f_equal; solve [eauto | symmetry; eauto].
Qed.

Definition subt_ext := proj1 subst_ext.
Definition subf_ext := proj2 subst_ext.

(** A renaming is a substitution. *)
Lemma ren_subst :
  (forall t ξ σ, (forall n, σ n = tvar (ξ n)) -> rent ξ t = subt σ t) /\
  (forall φ ξ σ, (forall n, σ n = tvar (ξ n)) -> renf ξ φ = subf σ φ).
Proof.
  assert (U : forall ξ σ, (forall n, σ n = tvar (ξ n)) -> forall n, ups σ n = tvar (upr ξ n)).
  { intros ξ σ H [|n]; cbn; [reflexivity|rewrite H; reflexivity]. }
  apply syn_ind; intros; cbn; try solve [auto | symmetry; auto]; f_equal; solve [eauto | symmetry; eauto].
Qed.

(** Substitution after renaming. *)
Lemma subst_ren :
  (forall t σ ξ τ, (forall n, τ n = σ (ξ n)) -> subt σ (rent ξ t) = subt τ t) /\
  (forall φ σ ξ τ, (forall n, τ n = σ (ξ n)) -> subf σ (renf ξ φ) = subf τ φ).
Proof.
  assert (U : forall σ ξ τ, (forall n, τ n = σ (ξ n)) -> forall n, ups τ n = ups σ (upr ξ n)).
  { intros σ ξ τ H [|n]; cbn; [reflexivity|rewrite H; reflexivity]. }
  apply syn_ind; intros; cbn; try solve [auto | symmetry; auto]; f_equal; solve [eauto | symmetry; eauto].
Qed.

(** Renaming after substitution. *)
Lemma ren_subst_comm :
  (forall t ξ σ τ, (forall n, τ n = rent ξ (σ n)) -> rent ξ (subt σ t) = subt τ t) /\
  (forall φ ξ σ τ, (forall n, τ n = rent ξ (σ n)) -> renf ξ (subf σ φ) = subf τ φ).
Proof.
  assert (U : forall ξ σ τ, (forall n, τ n = rent ξ (σ n)) -> forall n, ups τ n = rent (upr ξ) (ups σ n)).
  { intros ξ σ τ H [|n]; cbn; [reflexivity|]. rewrite H.
    rewrite (proj1 ren_comp (σ n) S ξ (fun k => S (ξ k))) by reflexivity.
    rewrite (proj1 ren_comp (σ n) (upr ξ) S (fun k => S (ξ k))) by reflexivity. reflexivity. }
  apply syn_ind; intros; cbn; try solve [auto | symmetry; auto]; f_equal; solve [eauto | symmetry; eauto].
Qed.

(** Composition of substitutions. *)
Lemma subst_comp :
  (forall t σ τ θ, (forall n, θ n = subt τ (σ n)) -> subt τ (subt σ t) = subt θ t) /\
  (forall φ σ τ θ, (forall n, θ n = subt τ (σ n)) -> subf τ (subf σ φ) = subf θ φ).
Proof.
  assert (U : forall σ τ θ, (forall n, θ n = subt τ (σ n)) -> forall n, ups θ n = subt (ups τ) (ups σ n)).
  { intros σ τ θ H [|n]; cbn; [reflexivity|]. rewrite H.
    rewrite (proj1 ren_subst_comm (σ n) S τ (fun k => sht (τ k))) by reflexivity.
    rewrite (proj1 subst_ren (σ n) (ups τ) S (fun k => sht (τ k))) by reflexivity. reflexivity. }
  apply syn_ind; intros; cbn; try solve [auto | symmetry; auto]; f_equal; solve [eauto | symmetry; eauto].
Qed.

Lemma subst_id :
  (forall t σ, (forall n, σ n = tvar n) -> subt σ t = t) /\
  (forall φ σ, (forall n, σ n = tvar n) -> subf σ φ = φ).
Proof.
  assert (U : forall σ, (forall n, σ n = tvar n) -> forall n, ups σ n = tvar n).
  { intros σ H [|n]; cbn; [reflexivity|rewrite H; reflexivity]. }
  apply syn_ind; intros; cbn; try solve [auto | symmetry; auto]; f_equal; solve [eauto | symmetry; eauto].
Qed.

Lemma ren_id :
  (forall t ξ, (forall n, ξ n = n) -> rent ξ t = t) /\
  (forall φ ξ, (forall n, ξ n = n) -> renf ξ φ = φ).
Proof.
  split; intros.
  - rewrite (proj1 ren_subst t ξ tvar) by (intros; rewrite H; reflexivity). apply subst_id; reflexivity.
  - rewrite (proj2 ren_subst φ ξ tvar) by (intros; rewrite H; reflexivity). apply subst_id; reflexivity.
Qed.

(** ** Usual consequences *)

Lemma inst_shf φ t : inst (shf φ) t = φ.
Proof. unfold inst. rewrite (proj2 subst_ren φ _ S tvar) by reflexivity. apply subst_id; reflexivity. Qed.

Lemma subt_sht σ t : subt σ (sht t) = subt (fun n => σ (S n)) t.
Proof. apply subst_ren; reflexivity. Qed.

Lemma subf_shf σ φ : subf σ (shf φ) = subf (fun n => σ (S n)) φ.
Proof. apply subst_ren; reflexivity. Qed.

Lemma sht_subt σ t : sht (subt σ t) = subt (ups σ) (sht t).
Proof.
  rewrite (proj1 ren_subst_comm t S σ (fun n => sht (σ n))) by reflexivity.
  rewrite (proj1 subst_ren t (ups σ) S (fun n => sht (σ n))) by reflexivity. reflexivity.
Qed.

Lemma shf_subf σ φ : shf (subf σ φ) = subf (ups σ) (shf φ).
Proof.
  rewrite (proj2 ren_subst_comm φ S σ (fun n => sht (σ n))) by reflexivity.
  rewrite (proj2 subst_ren φ (ups σ) S (fun n => sht (σ n))) by reflexivity. reflexivity.
Qed.

Lemma inst_subf σ φ t : subf σ (inst φ t) = inst (subf (ups σ) φ) (subt σ t).
Proof.
  unfold inst. rewrite (proj2 subst_comp φ (t .: tvar) σ (subt σ t .: σ)) by (intros [|n]; reflexivity).
  rewrite (proj2 subst_comp φ (ups σ) (subt σ t .: tvar) (subt σ t .: σ)); [reflexivity|].
  intros [|n]; cbn; [reflexivity|]. rewrite subt_sht. symmetry. apply subst_id. reflexivity.
Qed.

Lemma shf_inst φ t : shf (inst φ t) = inst (renf (upr S) φ) (sht t).
Proof.
  unfold inst. rewrite (proj2 ren_subst_comm φ S (t .: tvar) (sht t .: fun n => tvar (S n))) by (intros [|n]; reflexivity).
  rewrite (proj2 subst_ren φ (sht t .: tvar) (upr S) (sht t .: fun n => tvar (S n))) by (intros [|n]; reflexivity).
  reflexivity.
Qed.

(** ** Formulas with bounded free variables *)

Fixpoint tbound (k : nat) (t : term) : Prop :=
  match t with
  | tvar n => n < k
  | tempty | tomega => True
  | tpair a b => tbound k a /\ tbound k b
  | tunion a | tpow a => tbound k a
  | tsep a φ => tbound k a /\ fbound (S k) φ
  | trepl a ψ => tbound k a /\ fbound (S (S k)) ψ
  end
with fbound (k : nat) (φ : form) : Prop :=
  match φ with
  | fTop | fBot => True
  | fAnd φ ψ | fOr φ ψ | fImp φ ψ => fbound k φ /\ fbound k ψ
  | fAll φ | fEx φ => fbound (S k) φ
  | fEps a b | fMem a b | fSub a b | fEqv a b | fEq a b => tbound k a /\ tbound k b
  end.
