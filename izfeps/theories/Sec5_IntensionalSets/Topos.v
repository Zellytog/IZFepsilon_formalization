(** * Tripos-to-topos for intensional sets (Section 5.3)

    - Sεt[T]: objects are pairs (X, ≈) where ≈ is a strict Φ-valued
      partial equivalence relation; morphisms are the strict, total,
      functional and compatible relations, identified up to uniform
      equivalence.
    - Set[E]: objects are those of V(E), morphisms are the relations of
      Sεt read through ≃ instead of =.
    - The functor Set[E] → Sεt[T], X ↦ (X, ≈X) with
      x ≈X x' ≜ ⟦x ε X⟧ ∧ ⟦x' ε X⟧ ∧ ⟦x ≃ x'⟧, is full and faithful:
      Set[E] is a full subcategory of Sεt[T].

    As for Sεt (Set_eps.v), relations are defined on V × V and restricted
    to elements by strictness; ⋂_{x ∈ dom X} becomes a quantification over
    V guarded by ⟦x ε X⟧.

    Remark on compatibility in Set[E]. It must be guarded by ⟦x' ε X⟧ and
    ⟦y' ε Y⟧. Without these guards,
    ⟦x ≃ x'⟧ ⊃ ⟦y ≃ y'⟧ ⊃ R(x, y) ⊃ R(x', y') would, together with
    strictness, force ⟦x' ε X⟧ as soon as x' ≃ x ε X, which is false in
    general (x' ≜ {(⊥, ∅)} ≃ ∅ ε {(⊤, ∅)}, but ⟦x' ε {(⊤, ∅)}⟧ = ⊥). The
    guarded condition is exactly the compatibility of Sεt[T] for ≈X and
    ≈Y. *)

From Stdlib Require Import List Setoid Morphisms.
Import ListNotations.
From IZFe Require Import Syntax Deriv Theories Frame VE Model Realize Basic Set_eps.

(** ** Functors *)

Record functor (C D : category) := {
  fob : ob C -> ob D;
  fhom : forall {x y}, hom C x y -> hom D (fob x) (fob y);
  fhom_proper : forall x y (f g : hom C x y), heq f g -> heq (fhom f) (fhom g);
  fhom_id : forall x, heq (fhom (cid x)) (cid (fob x));
  fhom_comp : forall x y z (f : hom C x y) (g : hom C y z), heq (fhom (ccomp g f)) (ccomp (fhom g) (fhom f))
}.

Arguments fob {C D} _ _.
Arguments fhom {C D} _ {x y} _.

Definition full {C D} (Fu : functor C D) : Prop :=
  forall x y (g : hom D (fob Fu x) (fob Fu y)), exists f : hom C x y, heq (fhom Fu f) g.

Definition faithful {C D} (Fu : functor C D) : Prop :=
  forall x y (f g : hom C x y), heq (fhom Fu f) (fhom Fu g) -> heq f g.

Section Topos.

Context (F : frame).
Local Abbreviation V := (@V F).

#[local] Instance teq_equiv5 : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.

(** ** Sεt[T]: strict partial equivalence relations *)

Record per (X : V) := {
  pe :> V -> V -> pcar F;
  pe_proper : Rproper F pe;
  pe_strict : exists e, forall x x', pe x x' —[e]→ fand (eps x X) (eps x' X);
  pe_sym : exists e, forall x x', pe x x' —[e]→ pe x' x;
  pe_trans : exists e, forall x x' x'', fand (pe x x') (pe x' x'') —[e]→ pe x x''
}.

Arguments pe {X} _ _ _.

Record tob := { tset : V; tper : per tset }.

Local Notation "x ≈[ A ] y" := (pe (tper A) x y) (at level 65).

(** "In context" forms of symmetry and transitivity. *)
Lemma psym (A : tob) : exists s, forall (φ : F) e x y, φ —[e]→ x ≈[A] y -> φ —[e_comp e s]→ y ≈[A] x.
Proof. destruct (pe_sym _ (tper A)) as [s Hs]. exists s. intros. eapply f_comp; [eassumption|apply Hs]. Qed.

Lemma ptrans (A : tob) : exists t, forall (φ : F) e1 e2 x y z,
  φ —[e1]→ x ≈[A] y -> φ —[e2]→ y ≈[A] z -> φ —[e_comp (e_pair e1 e2) t]→ x ≈[A] z.
Proof.
  destruct (pe_trans _ (tper A)) as [t Ht]. exists t. intros.
  eapply f_comp; [apply n_pair; eassumption|apply Ht].
Qed.

Lemma prefl_l (A : tob) : exists r, forall (φ : F) e x y, φ —[e]→ x ≈[A] y -> φ —[e_comp e r]→ x ≈[A] x.
Proof.
  destruct (pe_sym _ (tper A)) as [s Hs], (pe_trans _ (tper A)) as [t Ht].
  exists (e_comp (e_pair e_id s) t). intros φ e x y H. eapply f_comp; [exact H|].
  eapply f_comp; [apply n_pair; [apply f_id|apply Hs]|apply Ht].
Qed.

Lemma prefl_r (A : tob) : exists r, forall (φ : F) e x y, φ —[e]→ x ≈[A] y -> φ —[e_comp e r]→ y ≈[A] y.
Proof.
  destruct (pe_sym _ (tper A)) as [s Hs], (pe_trans _ (tper A)) as [t Ht].
  exists (e_comp (e_pair s e_id) t). intros φ e x y H. eapply f_comp; [exact H|].
  eapply f_comp; [apply n_pair; [apply Hs|apply f_id]|apply Ht].
Qed.

Record thom (A B : tob) := {
  tr :> V -> V -> pcar F;
  tr_proper : Rproper F tr;
  t_strict : exists e, forall x y, tr x y —[e]→ fand (x ≈[A] x) (y ≈[B] y);
  t_total : exists e, forall x, x ≈[A] x —[e]→ fex (fun y : V => tr x y);
  t_func : exists e, forall x y y', fand (tr x y) (tr x y') —[e]→ y ≈[B] y';
  t_compat : exists e, forall x x' y y', fand (fand (x ≈[A] x') (y ≈[B] y')) (tr x y) —[e]→ tr x' y'
}.

Arguments tr {A B} _ _ _.

Definition theq {A B} (f g : thom A B) : Prop :=
  (exists e, forall x y, f x y —[e]→ g x y) /\ (exists e, forall x y, g x y —[e]→ f x y).

Lemma theq_equiv A B : Equivalence (@theq A B).
Proof.
  split.
  - intros f. split; exists e_id; intros; apply f_id.
  - intros f g [H1 H2]. split; assumption.
  - intros f g h [[e1 H1] [e1' H1']] [[e2 H2] [e2' H2']]. split.
    + exists (e_comp e1 e2). intros. eapply f_comp; [apply H1|apply H2].
    + exists (e_comp e2' e1'). intros. eapply f_comp; [apply H2'|apply H1'].
Qed.

#[local] Existing Instance theq_equiv.

(** Access to the conditions, in context. *)
Lemma strict1 {A B} (f : thom A B) : exists s, forall (φ : F) e x y, φ —[e]→ f x y -> φ —[e_comp (e_comp e s) e_fst]→ x ≈[A] x.
Proof. destruct (t_strict _ _ f) as [s Hs]. exists s. intros. eapply n_fst, f_comp; [eassumption|apply Hs]. Qed.
Lemma strict2 {A B} (f : thom A B) : exists s, forall (φ : F) e x y, φ —[e]→ f x y -> φ —[e_comp (e_comp e s) e_snd]→ y ≈[B] y.
Proof. destruct (t_strict _ _ f) as [s Hs]. exists s. intros. eapply n_snd, f_comp; [eassumption|apply Hs]. Qed.
Lemma compat {A B} (f : thom A B) : exists c, forall (φ : F) e1 e2 e3 x x' y y',
  φ —[e1]→ x ≈[A] x' -> φ —[e2]→ y ≈[B] y' -> φ —[e3]→ f x y -> φ —[e_comp (e_pair (e_pair e1 e2) e3) c]→ f x' y'.
Proof.
  destruct (t_compat _ _ f) as [c Hc]. exists c. intros.
  eapply f_comp; [apply n_pair; [apply n_pair|]; eassumption|apply Hc].
Qed.
Lemma func {A B} (f : thom A B) : exists c, forall (φ : F) e1 e2 x y y',
  φ —[e1]→ f x y -> φ —[e2]→ f x y' -> φ —[e_comp (e_pair e1 e2) c]→ y ≈[B] y'.
Proof.
  destruct (t_func _ _ f) as [c Hc]. exists c. intros.
  eapply f_comp; [apply n_pair; eassumption|apply Hc].
Qed.

(** *** The identity: ≈ itself *)

Definition tid (A : tob) : thom A A.
Proof.
  refine {| tr := pe (tper A); tr_proper := pe_proper _ (tper A) |}.
  - destruct (prefl_l A) as [r1 H1], (prefl_r A) as [r2 H2].
    eexists. intros x y. apply n_pair; [apply H1 with (y := y), f_id|apply H2 with (x := x), f_id].
  - eexists. intros x. apply (n_exI (fun y => x ≈[A] y) x), f_id.
  - destruct (psym A) as [s Hs], (ptrans A) as [t Ht].
    eexists. intros x y y'. apply Ht with (y := x); [apply Hs; apply f_fst|apply f_snd].
  - destruct (psym A) as [s Hs], (ptrans A) as [t Ht].
    eexists. intros x x' y y'. apply Ht with (y := y); [apply Ht with (y := x)|].
    + apply Hs. eapply n_fst, n_fst, f_id.
    + apply f_snd.
    + eapply n_snd, n_fst, f_id.
Defined.

(** *** Composition: (g ∘ f)(x, z) ≜ ⋃_β f(x, β) ∧ g(β, z) *)

Definition tcomp_rel {A B C} (g : thom B C) (f : thom A B) (x z : V) : pcar F :=
  fex (fun β : V => fand (f x β) (g β z)).

Lemma tcomp_proper {A B C} (g : thom B C) (f : thom A B) : Rproper F (tcomp_rel g f).
Proof.
  intros x x' z z' E1 E2. apply fex_proper. intros β. apply fand_proper.
  - apply (tr_proper _ _ f); [exact E1|reflexivity].
  - apply (tr_proper _ _ g); [reflexivity|exact E2].
Qed.

Definition tcomp {A B C} (g : thom B C) (f : thom A B) : thom A C.
Proof.
  refine {| tr := tcomp_rel g f; tr_proper := tcomp_proper g f |}.
  - destruct (strict1 f) as [s1 H1], (strict2 g) as [s2 H2].
    eexists. intros x z. apply (n_exE (fun β => fand (f x β) (g β z))); [apply f_id|]. intros β.
    apply n_pair; [apply H1 with (y := β); eapply n_fst, n_hyp0|apply H2 with (x := β); eapply n_snd, n_hyp0].
  - destruct (t_total _ _ f) as [e1 H1], (t_total _ _ g) as [e2 H2], (strict2 f) as [s S].
    eexists. intros x. apply (n_exE (fun β => f x β)); [apply H1|]. intros β.
    apply (n_exE (fun γ => g β γ)); [eapply f_comp; [apply S with (x := x); apply n_hyp0|apply H2]|]. intros γ.
    apply (n_exI (fun γ => tcomp_rel g f x γ) γ). apply (n_exI (fun β => fand (f x β) (g β γ)) β).
    apply n_pair; [apply n_wk, n_hyp0|apply n_hyp0].
  - destruct (func f) as [c1 H1], (func g) as [c2 H2], (compat g) as [c3 H3], (strict2 g) as [s S].
    eexists. intros x z z'.
    apply (n_exE (fun β => fand (f x β) (g β z))); [eapply n_fst, f_id|]. intros β.
    apply (n_exE (fun β => fand (f x β) (g β z'))); [eapply n_snd, n_wk, f_id|]. intros β'.
    apply H2 with (x := β').
    + apply H3 with (x := β) (y := z).
      * apply H1 with (x := x); [eapply n_fst, n_wk, n_hyp0|eapply n_fst, n_hyp0].
      * apply S with (x := β). eapply n_snd, n_wk, n_hyp0.
      * eapply n_snd, n_wk, n_hyp0.
    + eapply n_snd, n_hyp0.
  - destruct (compat f) as [c1 H1], (compat g) as [c2 H2], (strict2 f) as [s S].
    eexists. intros x x' z z'.
    apply (n_exE (fun β => fand (f x β) (g β z))); [eapply n_snd, f_id|]. intros β.
    apply (n_exI (fun β => fand (f x' β) (g β z')) β). apply n_pair.
    + apply H1 with (x := x) (y := β).
      * eapply n_fst, n_fst, n_wk, f_id.
      * apply S with (x := x). eapply n_fst, n_hyp0.
      * eapply n_fst, n_hyp0.
    + apply H2 with (x := β) (y := z).
      * apply S with (x := x). eapply n_fst, n_hyp0.
      * eapply n_snd, n_fst, n_wk, f_id.
      * eapply n_snd, n_hyp0.
Defined.

Lemma tcomp_proper_h A B C (g g' : thom B C) (f f' : thom A B) : theq g g' -> theq f f' -> theq (tcomp g f) (tcomp g' f').
Proof.
  assert (M : forall (g g' : thom B C) (f f' : thom A B), theq g g' -> theq f f' ->
            exists e, forall x z, tcomp g f x z —[e]→ tcomp g' f' x z).
  { intros g0 g0' f0 f0' [[e1 H1] _] [[e2 H2] _]. eexists. intros x z. cbn.
    apply (n_exE (fun β => fand (f0 x β) (g0 β z))); [apply f_id|]. intros β.
    apply (n_exI (fun β => fand (f0' x β) (g0' β z)) β).
    apply n_pair; [eapply f_comp; [eapply n_fst, n_hyp0|apply H2]|eapply f_comp; [eapply n_snd, n_hyp0|apply H1]]. }
  intros Hg Hf. split; apply M; auto; symmetry; auto.
Qed.

Lemma tid_l A B (f : thom A B) : theq (tcomp (tid B) f) f.
Proof.
  destruct (compat f) as [c H], (strict1 f) as [s S], (strict2 f) as [s' S']. split.
  - eexists. intros x z. cbn. apply (n_exE (fun β => fand (f x β) (β ≈[B] z))); [apply f_id|]. intros β.
    apply H with (x := x) (y := β); [apply S with (y := β); eapply n_fst, n_hyp0|eapply n_snd, n_hyp0|eapply n_fst, n_hyp0].
  - eexists. intros x z. cbn. apply (n_exI (fun β => fand (f x β) (β ≈[B] z)) z).
    apply n_pair; [apply f_id|apply S' with (x := x), f_id].
Qed.

Lemma tid_r A B (f : thom A B) : theq (tcomp f (tid A)) f.
Proof.
  destruct (compat f) as [c H], (strict1 f) as [s S], (strict2 f) as [s' S'], (psym A) as [ps P]. split.
  - eexists. intros x z. cbn. apply (n_exE (fun β => fand (x ≈[A] β) (f β z))); [apply f_id|]. intros β.
    apply H with (x := β) (y := z); [apply P; eapply n_fst, n_hyp0|apply S' with (x := β); eapply n_snd, n_hyp0|eapply n_snd, n_hyp0].
  - eexists. intros x z. cbn. apply (n_exI (fun β => fand (x ≈[A] β) (f β z)) x).
    apply n_pair; [apply S with (y := z), f_id|apply f_id].
Qed.

Lemma tassoc A B C D (f : thom A B) (g : thom B C) (h : thom C D) :
  theq (tcomp h (tcomp g f)) (tcomp (tcomp h g) f).
Proof.
  split.
  - eexists. intros x δ. cbn.
    apply (n_exE (fun β => fand (tcomp_rel g f x β) (h β δ))); [apply f_id|]. intros γ.
    apply (n_exE (fun β => fand (f x β) (g β γ))); [eapply n_fst, n_hyp0|]. intros β.
    apply (n_exI (fun β => fand (f x β) (tcomp_rel h g β δ)) β). apply n_pair; [eapply n_fst, n_hyp0|].
    apply (n_exI (fun γ => fand (g β γ) (h γ δ)) γ). apply n_pair; [eapply n_snd, n_hyp0|eapply n_snd, n_wk, n_hyp0].
  - eexists. intros x δ. cbn.
    apply (n_exE (fun β => fand (f x β) (tcomp_rel h g β δ))); [apply f_id|]. intros β.
    apply (n_exE (fun γ => fand (g β γ) (h γ δ))); [eapply n_snd, n_hyp0|]. intros γ.
    apply (n_exI (fun γ => fand (tcomp_rel g f x γ) (h γ δ)) γ). apply n_pair; [|eapply n_snd, n_hyp0].
    apply (n_exI (fun β => fand (f x β) (g β γ)) β). apply n_pair; [eapply n_fst, n_wk, n_hyp0|eapply n_fst, n_hyp0].
Qed.

Definition SepsT : category := {|
  ob := tob; hom := thom; heq := @theq; heq_equiv := theq_equiv;
  cid := tid; ccomp := @tcomp; ccomp_proper := tcomp_proper_h;
  cid_l := tid_l; cid_r := tid_r; cassoc := tassoc
|}.

End Topos.

(** ** Set[E] and the embedding into Sεt[T]

    Here ≃ must be, in V(E), uniformly reflexive, symmetric and
    transitive: this is Lemma 10, transported into V(E) by soundness
    (Theorem 26). We therefore take the hypotheses of the model again. *)

Section SetE.

Context (F : frame).
Context (Φ0 : Type) (enc : pcar F -> Φ0) (dec : Φ0 -> pcar F).
Context (dec_enc : forall φ, dec (enc φ) ≡ φ).
Local Abbreviation V := (@V F).
Context (coll : forall T : Type, (T -> V) -> (V -> V -> pcar F) -> V).
Context (coll_proper : forall T (xs xs' : T -> V) (ψ ψ' : V -> V -> pcar F),
  Rproper F ψ -> (forall t, teq (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
  teq (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> V) (ψ : V -> V -> pcar F), Rproper F ψ ->
  forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub (coll T xs ψ) s)).
Context (yfix : eexp -> fev F) (yfix_spec : fixpoint_comb F yfix).

#[local] Instance teq_equiv6 : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.

Local Notation "x ≈[ A ] y" := (pe F (tper F A) x y) (at level 65).

Lemma sem Γ φ : prv IZFm Γ φ -> exists e, forall ρ, ctx F Φ0 dec coll ρ Γ —[e]→ evf F Φ0 dec coll ρ φ.
Proof.
  intros H. apply (soundness F Φ0 dec coll coll_proper IZFe).
  - apply (thm26 F Φ0 enc dec dec_enc coll coll_proper coll_spec yfix yfix_spec).
  - eapply prv_mono; [exact IZFm_IZFe|exact H].
Qed.

(** *** ≃ is a uniform equivalence in V(E) *)

Lemma veqv_refl : exists e, forall (φ : F) (x : V), φ —[e]→ veqv x x.
Proof.
  destruct (sem [] _ eqv_refl) as [e He]. exists (e_comp e_top e). intros φ x.
  eapply f_comp; [apply f_top|apply (He (fun _ => x))].
Qed.

Lemma veqv_sym : exists e, forall x y : V, veqv x y —[e]→ veqv y x.
Proof.
  destruct (sem _ _ eqv_sym) as [e He]. exists (e_comp (e_pair e_top e_id) e). intros x y.
  eapply f_comp; [apply n_pair; [apply f_top|apply f_id]|apply (He (x .: y .: fun _ => x))].
Qed.

Lemma veqv_trans : exists e, forall x y z : V, fand (veqv x y) (veqv y z) —[e]→ veqv x z.
Proof.
  destruct (sem _ _ eqv_trans) as [e He]. exists (e_comp (e_pair (e_pair e_top e_snd) e_fst) e). intros x y z.
  eapply f_comp; [|apply (He (x .: y .: z .: fun _ => x))]. cbn.
  apply n_pair; [apply n_pair; [apply f_top|apply f_snd]|apply f_fst].
Qed.

(** *** The relation x ≈X x' ≜ ⟦x ε X⟧ ∧ ⟦x' ε X⟧ ∧ ⟦x ≃ x'⟧ *)

Definition eqvX (X : V) (x x' : V) : pcar F := fand (fand (eps x X) (eps x' X)) (veqv x x').

Lemma eqvX_proper X : Rproper F (eqvX X).
Proof.
  intros x x' y y' E1 E2. unfold eqvX.
  apply fand_proper; [apply fand_proper; apply eps_proper; auto; reflexivity|apply veqv_proper; auto].
Qed.

Definition perX (X : V) : per F X.
Proof.
  refine {| pe := eqvX X; pe_proper := eqvX_proper X |}.
  - exists e_fst. intros; apply f_fst.
  - destruct veqv_sym as [s Hs]. eexists. intros x x'. unfold eqvX.
    apply n_pair; [apply n_pair; [eapply n_snd, n_fst, f_id|eapply n_fst, n_fst, f_id]|].
    eapply f_comp; [eapply n_snd, f_id|apply Hs].
  - destruct veqv_trans as [t Ht]. eexists. intros x x' x''. unfold eqvX.
    apply n_pair; [apply n_pair; [eapply n_fst, n_fst, n_fst, f_id|eapply n_snd, n_fst, n_snd, f_id]|].
    eapply f_comp; [apply n_pair; [eapply n_snd, n_fst, f_id|eapply n_snd, n_snd, f_id]|apply Ht].
Defined.

Definition obX (X : V) : tob F := {| tset := X; tper := perX X |}.

(** *** The morphisms of Set[E] *)

Record ehom (X Y : V) := {
  er :> V -> V -> pcar F;
  er_proper : Rproper F er;
  e_strict : exists e, forall x y, er x y —[e]→ fand (eps x X) (eps y Y);
  e_total : exists e, forall x, eps x X —[e]→ fex (fun y : V => er x y);
  e_func : exists e, forall x y y', fand (er x y) (er x y') —[e]→ veqv y y';
  e_compat : exists e, forall x x' y y', fand (fand (eqvX X x x') (eqvX Y y y')) (er x y) —[e]→ er x' y'
}.

Arguments er {X Y} _ _ _.

Definition eheq {X Y} (f g : ehom X Y) : Prop :=
  (exists e, forall x y, f x y —[e]→ g x y) /\ (exists e, forall x y, g x y —[e]→ f x y).

(** From morphisms of Set[E] to morphisms of Sεt[T] and back: the same relation. *)
Definition to_T {X Y} (f : ehom X Y) : thom F (obX X) (obX Y).
Proof.
  refine {| tr := er f; tr_proper := er_proper _ _ f |}.
  - destruct (e_strict _ _ f) as [s Hs], veqv_refl as [r Hr]. eexists. intros x y. cbn. unfold eqvX.
    apply n_pair; (apply n_pair; [apply n_pair|apply Hr]);
      first [eapply n_fst, f_comp; [apply f_id|apply Hs] | eapply n_snd, f_comp; [apply f_id|apply Hs]].
  - destruct (e_total _ _ f) as [e He]. eexists. intros x. cbn. unfold eqvX.
    eapply f_comp; [eapply n_fst, n_fst, f_id|apply He].
  - destruct (e_func _ _ f) as [c Hc], (e_strict _ _ f) as [s Hs]. eexists. intros x y y'. cbn. unfold eqvX.
    apply n_pair; [apply n_pair|apply Hc].
    + eapply n_snd, f_comp; [eapply n_fst, f_id|apply Hs].
    + eapply n_snd, f_comp; [eapply n_snd, f_id|apply Hs].
  - destruct (e_compat _ _ f) as [c Hc]. exists c. intros. apply Hc.
Defined.

Definition of_T {X Y} (f : thom F (obX X) (obX Y)) : ehom X Y.
Proof.
  refine {| er := @tr F _ _ f; er_proper := tr_proper F _ _ f |}.
  - destruct (t_strict F _ _ f) as [s Hs]. eexists. intros x y.
    eapply f_comp; [apply Hs|]. cbn. unfold eqvX.
    apply n_pair; [eapply n_fst, n_fst, n_fst, f_id|eapply n_fst, n_fst, n_snd, f_id].
  - destruct (t_total F _ _ f) as [e He], veqv_refl as [r Hr]. eexists. intros x.
    eapply f_comp; [|apply He]. cbn. unfold eqvX. apply n_pair; [apply n_pair; apply f_id|apply Hr].
  - destruct (t_func F _ _ f) as [c Hc]. eexists. intros x y y'.
    eapply f_comp; [apply Hc|]. cbn. unfold eqvX. apply f_snd.
  - destruct (t_compat F _ _ f) as [c Hc]. exists c. intros. apply Hc.
Defined.

(** Set[E]: identities and compositions are those of Sεt[T]. *)
Definition eid (X : V) : ehom X X := of_T (tid F (obX X)).
Definition ecomp {X Y Z} (g : ehom Y Z) (f : ehom X Y) : ehom X Z := of_T (tcomp F (to_T g) (to_T f)).

Lemma eheq_T {X Y} (f g : ehom X Y) : eheq f g <-> theq F (to_T f) (to_T g).
Proof. reflexivity. Qed.

Lemma eheq_equiv X Y : Equivalence (@eheq X Y).
Proof.
  split.
  - intros f. split; exists e_id; intros; apply f_id.
  - intros f g [H1 H2]. split; assumption.
  - intros f g h [[e1 H1] [e1' H1']] [[e2 H2] [e2' H2']]. split.
    + exists (e_comp e1 e2). intros. eapply f_comp; [apply H1|apply H2].
    + exists (e_comp e2' e1'). intros. eapply f_comp; [apply H2'|apply H1'].
Qed.

Lemma ecomp_proper X Y Z (g g' : ehom Y Z) (f f' : ehom X Y) : eheq g g' -> eheq f f' -> eheq (ecomp g f) (ecomp g' f').
Proof. intros Hg Hf. exact (tcomp_proper_h F _ _ _ (to_T g) (to_T g') (to_T f) (to_T f') Hg Hf). Qed.

Lemma eid_l X Y (f : ehom X Y) : eheq (ecomp (eid Y) f) f.
Proof. exact (tid_l F _ _ (to_T f)). Qed.

Lemma eid_r X Y (f : ehom X Y) : eheq (ecomp f (eid X)) f.
Proof. exact (tid_r F _ _ (to_T f)). Qed.

Lemma eassoc X Y Z W (f : ehom X Y) (g : ehom Y Z) (h : ehom Z W) : eheq (ecomp h (ecomp g f)) (ecomp (ecomp h g) f).
Proof. exact (tassoc F _ _ _ _ (to_T f) (to_T g) (to_T h)). Qed.

Definition SetE : category := {|
  ob := V; hom := ehom; heq := @eheq; heq_equiv := eheq_equiv;
  cid := eid; ccomp := @ecomp; ccomp_proper := ecomp_proper;
  cid_l := eid_l; cid_r := eid_r; cassoc := eassoc
|}.
(** *** The functor Set[E] → Sεt[T] is full and faithful *)

Definition embed : functor SetE (SepsT F).
Proof.
  refine (Build_functor SetE (SepsT F) obX (fun X Y f => to_T f) _ _ _).
  - intros X Y f g H. exact H.
  - intros X. cbn. split; exists e_id; intros; apply f_id.
  - intros X Y Z f g. cbn. split; exists e_id; intros; apply f_id.
Defined.

Theorem embed_full : full embed.
Proof. intros X Y g. exists (of_T g). cbn. split; exists e_id; intros; apply f_id. Qed.

Theorem embed_faithful : faithful embed.
Proof. intros X Y f g H. exact H. Qed.

End SetE.
