(** * Theorem 26: V(E) realizes the axioms of IZFε

    Each axiom is first realized in a semantic form (on V(E) and
    compatible predicates), by a uniform evidence: it depends neither on
    the sets nor on the predicates. Case analyses are performed by the
    evidences themselves (elimination of ⋃, Church booleans inl/inr),
    never by inspection. *)

From Stdlib Require Import List Setoid Morphisms.
Import ListNotations.
From IZFe Require Import Syntax Deriv Theories Frame VE Model.

Section Realize.

Context (F : frame).
Context (Φ0 : Type) (enc : pcar F -> Φ0) (dec : Φ0 -> pcar F).
Context (dec_enc : forall φ, dec (enc φ) ≡ φ).

Local Notation V := (@V F).

Context (coll : forall T : Type, (T -> V) -> (V -> V -> pcar F) -> V).
Context (coll_proper : forall T (xs xs' : T -> V) (ψ ψ' : V -> V -> pcar F),
  Rproper F ψ -> (forall t, teq (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
  teq (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> V) (ψ : V -> V -> pcar F), Rproper F ψ ->
  forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub (coll T xs ψ) s)).
Context (yfix : eexp -> fev F) (yfix_spec : fixpoint_comb F yfix).

#[local] Instance teq_equiv' : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.

Local Notation vempty := (vempty F).
Local Notation vpair := (vpair F).
Local Notation vunion := (vunion F).
Local Notation vsep := (vsep F).
Local Notation vpower := (vpower F Φ0 dec).
Local Notation bsub := (bsub F Φ0 dec).
Local Notation vsuc := (vsuc F).
Local Notation snat := (snat F).
Local Notation pnat := (pnat F).
Local Notation vomega := (vomega F).
Local Notation vrepl := (vrepl F coll).
Local Notation tagT := (tagT F).
Local Notation tagF := (tagF F).

Definition fiff (A B : pcar F) : pcar F := fand (fimp A B) (fimp B A).

Lemma n_iff (φ A B : F) e1 e2 : fand φ A —[e1]→ B -> fand φ B —[e2]→ A -> φ —[e_pair (e_lam e1) (e_lam e2)]→ fiff A B.
Proof. intros; apply n_pair; apply n_lam; assumption. Qed.

(** ** Membership: introduction and elimination *)

Lemma n_eps_in (φ : F) e (y : V) t x : teq (sub y t) x -> φ —[e]→ lbl y t -> φ —[e_comp e e_exI]→ eps x y.
Proof.
  intros Ht H. eapply f_comp; [exact H|].
  exact (f_exI _ (fun u : { u : idx y | teq (sub y u) x } => lbl y (proj1_sig u)) (exist _ t Ht)).
Qed.

Lemma n_eps_el (φ χ : F) e0 e (x y : V) :
  φ —[e0]→ eps x y -> (forall t, teq (sub y t) x -> fand φ (lbl y t) —[e]→ χ) -> φ —[e_exE_ctx e0 e]→ χ.
Proof.
  intros H0 H. apply (n_exE (fun u : { u : idx y | teq (sub y u) x } => lbl y (proj1_sig u))); [exact H0|].
  intros [t Ht]. apply H, Ht.
Qed.

(** ** Church booleans *)

Lemma n_tagT (φ : F) : φ —[e_gen (e_gen (e_lam (e_lam (e_comp e_fst e_snd))))]→ tagT.
Proof. apply n_gen; intros A. apply n_gen; intros B. apply n_lam, n_lam. apply n_wk, n_hyp0. Qed.

Lemma n_tagF (φ : F) : φ —[e_gen (e_gen (e_lam (e_lam e_snd)))]→ tagF.
Proof. apply n_gen; intros A. apply n_gen; intros B. apply n_lam, n_lam, n_hyp0. Qed.

Lemma n_selT (φ A B : F) e : φ —[e]→ tagT -> φ —[e_comp (e_comp e e_incl) e_incl]→ fimp A (fimp B A).
Proof.
  intros H. eapply (n_inst (fun ψ => fimp A (fimp ψ A)) B).
  eapply (n_inst (fun φ0 => fall (fun ψ => fimp φ0 (fimp ψ φ0))) A). exact H.
Qed.

Lemma n_selF (φ A B : F) e : φ —[e]→ tagF -> φ —[e_comp (e_comp e e_incl) e_incl]→ fimp A (fimp B B).
Proof.
  intros H. eapply (n_inst (fun ψ => fimp A (fimp ψ ψ)) B).
  eapply (n_inst (fun φ0 => fall (fun ψ => fimp φ0 (fimp ψ ψ))) A). exact H.
Qed.

Definition PepsL (b : V) : pmor (Vset F) F :=
  Build_pmor (Vset F) F (fun z => eps z b) (fun z z' E => eps_proper F z z' b b E (teq_refl F b)).

Lemma n_veq_of_teq (φ : F) (x y : V) : teq x y -> φ —[e_refl]→ veq x y.
Proof. intros H. eapply n_eq; [apply veq_proper; [reflexivity|exact H]|apply n_refl]. Qed.

(** ** ∅ *)

Lemma R_empty : exists e, forall z, ftop —[e]→ fimp (eps z vempty) fbot.
Proof. exists (e_lam (e_exE_ctx e_snd e_id)). intros z. apply n_lam. eapply n_eps_el; [apply n_hyp0|]. intros []. Qed.

(** ** Pairing *)

Lemma R_pair : exists e, forall z x y, ftop —[e]→ fiff (eps z (vpair x y)) (for_ (veq z x) (veq z y)).
Proof.
  eexists. intros z x y. apply n_iff.
  - eapply n_eps_el; [apply n_hyp0|]. intros t Ht.
    set (D := for_ (veq z x) (veq z y)).
    set (A := fimp (veq z x) D). set (B := fimp (veq z y) D).
    assert (GA : forall φ, φ —[e_lam (e_kl e_snd)]→ A) by (intros; apply n_lam, n_orI1, n_hyp0).
    assert (GB : forall φ, φ —[e_lam (e_kr e_snd)]→ B) by (intros; apply n_lam, n_orI2, n_hyp0).
    destruct t; cbn in Ht.
    + eapply n_app; [eapply n_app; [eapply n_app; [apply n_selT, n_hyp0|apply GA]|apply GB]|].
      apply n_veq_of_teq. symmetry. exact Ht.
    + eapply n_app; [eapply n_app; [eapply n_app; [apply n_selF, n_hyp0|apply GA]|apply GB]|].
      apply n_veq_of_teq. symmetry. exact Ht.
  - apply (n_orE _ (veq z x) (veq z y)); [apply n_hyp0| |].
    + apply (n_leib (PepsL (vpair x y)) x z); [apply n_sym, n_hyp0|]. cbn.
      eapply (n_eps_in _ _ (vpair x y) true); [destruct x; reflexivity|]. apply n_tagT.
    + apply (n_leib (PepsL (vpair x y)) y z); [apply n_sym, n_hyp0|]. cbn.
      eapply (n_eps_in _ _ (vpair x y) false); [destruct y; reflexivity|]. apply n_tagF.
Qed.

(** ** Union: z ε ⋃x ⇔ ∃a. a ε x ∧ z ε a *)

Lemma R_union : exists e, forall x z, ftop —[e]→ fiff (eps z (vunion x)) (fex (fun a : V => fand (eps a x) (eps z a))).
Proof.
  eexists. intros [[T k] l] z. apply n_iff.
  - eapply n_eps_el; [apply n_hyp0|]. intros [t u] Ht.
    apply (n_exI (fun a : V => fand (eps a (existT _ (node T k) l)) (eps z a)) (sub (existT _ (node T k) l) t)).
    apply n_pair.
    + eapply (n_eps_in _ _ _ t); [reflexivity|]. eapply n_fst, n_hyp0.
    + eapply (n_eps_in _ _ (sub (existT _ (node T k) l) t) u); [exact Ht|]. eapply n_snd, n_hyp0.
  - apply (n_exE (fun a : V => fand (eps a (existT _ (node T k) l)) (eps z a))); [apply n_hyp0|]. intros a.
    eapply n_eps_el; [eapply n_fst, n_hyp0|]. intros t Ht.
    eapply n_eps_el.
    { eapply n_eq; [apply eps_proper; [reflexivity|symmetry; exact Ht]|]. apply n_wk. eapply n_snd, n_hyp0. }
    intros u Hu. eapply (n_eps_in _ _ (vunion (existT _ (node T k) l)) (existT _ t u)); [exact Hu|].
    apply n_pair; [apply n_wk, n_hyp0|apply n_hyp0].
Qed.

(** ** Weak power set *)

Lemma R_wpow : exists e, forall x a, ftop —[e]→
  fex (fun b : V => fand (eps b (vpower x)) (fall (fun z : V => fiff (eps z b) (fand (eps z x) (eps z a))))).
Proof.
  eexists. intros [[T k] l] a. set (X := existT (lab F) (node T k) l).
  set (g := fun t : idx X => enc (eps (sub X t) a)).
  apply (n_exI (fun b : V => fand (eps b (vpower X)) (fall (fun z : V => fiff (eps z b) (fand (eps z X) (eps z a))))) (bsub X g)).
  apply n_pair.
  - eapply (n_eps_in _ _ (vpower X) g); [reflexivity|]. apply f_top.
  - apply n_gen; intros z. apply n_iff.
    + eapply n_eps_el; [apply n_hyp0|]. intros t Ht. apply n_pair.
      * eapply (n_eps_in _ _ X t); [exact Ht|]. eapply n_snd, n_hyp0.
      * eapply n_eq; [apply eps_proper; [exact Ht|reflexivity]|]. eapply n_eq; [apply dec_enc|]. eapply n_fst, n_hyp0.
    + eapply n_eps_el; [eapply n_fst, n_hyp0|]. intros t Ht.
      eapply (n_eps_in _ _ (bsub X g) t); [exact Ht|]. apply n_pair.
      * eapply n_eq; [symmetry; apply dec_enc|]. eapply n_eq; [apply eps_proper; [symmetry; exact Ht|reflexivity]|].
        apply n_wk. eapply n_snd, n_hyp0.
      * apply n_hyp0.
Qed.

(** ** ∈, ⊆ and ≃ *)

Lemma R_mem : exists e, forall x y, ftop —[e]→ fiff (vmem x y) (fex (fun a : V => fand (veqv x a) (eps a y))).
Proof.
  eexists. intros x y. apply n_iff.
  - apply (n_exE (fun u : idx y => fand (lbl y u) (veqv x (sub y u)))); [apply n_hyp0|]. intros u.
    apply (n_exI (fun a : V => fand (veqv x a) (eps a y)) (sub y u)).
    apply n_pair; [eapply n_snd, n_hyp0|]. eapply (n_eps_in _ _ y u); [reflexivity|]. eapply n_fst, n_hyp0.
  - apply (n_exE (fun a : V => fand (veqv x a) (eps a y))); [apply n_hyp0|]. intros a.
    eapply n_eps_el; [eapply n_snd, n_hyp0|]. intros t Ht.
    apply (n_exI (fun u : idx y => fand (lbl y u) (veqv x (sub y u))) t). apply n_pair; [apply n_hyp0|].
    eapply n_eq; [apply veqv_proper; [reflexivity|symmetry; exact Ht]|]. apply n_wk. eapply n_fst, n_hyp0.
Qed.

Lemma R_sub : exists e, forall x y, ftop —[e]→ fiff (vsub x y) (fall (fun a : V => fimp (eps a x) (vmem a y))).
Proof.
  eexists. intros x y. apply n_iff.
  - apply n_gen; intros a. apply n_lam. eapply n_eps_el; [apply n_hyp0|]. intros t Ht.
    eapply n_eq; [apply vmem_proper; [exact Ht|reflexivity]|]. eapply n_app; [|apply n_hyp0].
    apply (n_inst (fun t => fimp (lbl x t) (vmem (sub x t) y)) t).
    eapply n_eq; [apply vsub_unfold|]. apply n_wk, n_wk, n_hyp0.
  - eapply n_eq; [symmetry; apply vsub_unfold|]. apply n_gen; intros t. apply n_lam.
    eapply n_app; [apply (n_inst (fun a : V => fimp (eps a x) (vmem a y)) (sub x t)); apply n_wk, n_hyp0|].
    eapply (n_eps_in _ _ x t); [reflexivity|apply n_hyp0].
Qed.

Lemma R_eqv : exists e, forall x y, ftop —[e]→ fiff (veqv x y) (fand (vsub x y) (vsub y x)).
Proof. eexists. intros x y. apply n_iff; apply n_hyp0. Qed.

(** ** Separation *)

Lemma R_sep : exists e, forall z a (φ : V -> pcar F), Pproper F φ ->
  ftop —[e]→ fiff (eps z (vsep a φ)) (fand (eps z a) (φ z)).
Proof.
  eexists. intros z [[T k] l] φ Hφ. apply n_iff.
  - eapply n_eps_el; [apply n_hyp0|]. intros t Ht. apply n_pair.
    + eapply (n_eps_in _ _ (existT _ (node T k) l) t); [exact Ht|]. eapply n_snd, n_hyp0.
    + eapply n_eq; [apply Hφ, Ht|]. eapply n_fst, n_hyp0.
  - eapply n_eps_el; [eapply n_fst, n_hyp0|]. intros t Ht.
    eapply (n_eps_in _ _ (vsep (existT _ (node T k) l) φ) t); [exact Ht|]. apply n_pair; [|apply n_hyp0].
    eapply n_eq; [apply Hφ; symmetry; exact Ht|]. apply n_wk. eapply n_snd, n_hyp0.
Qed.

(** ** Foundation, through the fixed point combinator

    F(t) ≜ e_incl @ λ(e_{∃,elim}(π₀ ; t)), r₀ ≜ y(F), r ≜ λ(π₁ ; r₀). *)

Definition Hind (φ : V -> pcar F) : pcar F :=
  fall (fun a : V => fimp (fall (fun b : V => fimp (eps b a) (φ b))) (φ a)).

Definition step (t : fev F) : fev F := e_app e_incl (e_gen (e_lam (e_exE (e_comp e_fst t)))).

Definition x_app (a b : eexp) : eexp := x_comp (x_pair b a) x_ev.
Definition x_gen (a : eexp) : eexp := x_lam (x_comp x_fst a).
Definition x_exE (a : eexp) : eexp :=
  x_app (x_comp x_snd x_incl) (x_gen (x_lam (x_comp (x_pair (x_comp x_fst x_fst) x_snd) a))).
Definition x_step : eexp := x_app x_incl (x_gen (x_lam (x_exE (x_comp x_fst x_var)))).

Lemma eeval_step t : eeval F t x_step = step t.
Proof. reflexivity. Qed.

Lemma ind_step t (φ : V -> pcar F) (Hφ : Pproper F φ) a :
  (forall u, Hind φ —[t]→ φ (sub a u)) -> Hind φ —[step t]→ φ a.
Proof.
  intros IH. unfold step. eapply n_app.
  - apply (f_incl F _ (fun a : V => fimp (fall (fun b : V => fimp (eps b a) (φ b))) (φ a)) a).
  - apply n_gen. intros b. apply n_lam.
    apply (f_exE _ _ (fun u : { u : idx a | teq (sub a u) b } => lbl a (proj1_sig u))).
    intros [u Hu]. eapply n_eq; [apply Hφ, Hu|]. eapply f_comp; [apply f_fst|apply IH].
Qed.

Definition yind : fev F := yfix x_step.

Lemma yind_spec (φ : V -> pcar F) (Hφ : Pproper F φ) : forall a : V, Hind φ —[yind]→ φ a.
Proof.
  intros [s l]. revert l. induction s as [T k IH]; intros l.
  apply yfix_spec. rewrite eeval_step. apply ind_step; [exact Hφ|]. intros u. apply IH.
Qed.

Lemma R_ind : exists e, forall φ : V -> pcar F, Pproper F φ ->
  ftop —[e]→ fimp (Hind φ) (fall (fun a : V => φ a)).
Proof.
  exists (e_lam (e_gen (e_comp e_snd yind))). intros φ Hφ. apply n_lam. apply n_gen. intros a.
  eapply f_comp; [apply f_snd|apply yind_spec, Hφ].
Qed.

(** ** Collection *)

Lemma R_coll : exists e, forall a (ψ : V -> V -> pcar F), Rproper F ψ ->
  ftop —[e]→ fimp (fall (fun α : V => fimp (eps α a) (fex (fun β : V => ψ α β))))
                  (fex (fun b : V => fall (fun α : V => fimp (eps α a) (fex (fun β : V => fand (eps β b) (ψ α β)))))).
Proof.
  eexists. intros a ψ Hψ. apply n_lam.
  set (W := vrepl a ψ). set (B := coll (idx a) (sub a) ψ).
  apply (n_exI (fun b : V => fall (fun α : V => fimp (eps α a) (fex (fun β : V => fand (eps β b) (ψ α β))))) W).
  apply n_gen; intros α. apply n_lam.
  eapply n_eps_el; [apply n_hyp0|]. intros t Ht.
  apply (n_exE (fun β => ψ α β)).
  { eapply n_app; [apply (n_inst (fun α : V => fimp (eps α a) (fex (fun β : V => ψ α β))) α); apply n_wk, n_wk, n_hyp0|].
    apply n_wk, n_hyp0. }
  intros β. destruct (coll_spec (idx a) (sub a) ψ Hψ t β) as [s Hs].
  assert (K : ψ α β ≡ ψ (sub a t) (sub B s)).
  { etransitivity; [apply Hψ; [symmetry; exact Ht|reflexivity]|exact Hs]. }
  apply (n_exI (fun β : V => fand (eps β W) (ψ α β)) (sub W (t, s))). apply n_pair.
  - eapply (n_eps_in _ _ W (t, s)); [reflexivity|]. apply n_pair; [apply n_wk, n_hyp0|].
    eapply n_eq; [exact K|apply n_hyp0].
  - eapply n_eq; [|apply n_hyp0]. etransitivity; [exact K|].
    apply Hψ; [exact Ht|apply teq_sym; unfold W, vrepl; apply (sub_mk F)].
Qed.

(** ** Replacement *)

Definition ExU (χ : V -> pcar F) : pcar F :=
  fex (fun β0 : V => fand (χ β0) (fall (fun β' : V => fimp (χ β') (veq β' β0)))).

Lemma R_repl : exists e, forall a (ψ : V -> V -> pcar F), Rproper F ψ -> forall β,
  ftop —[e]→ fimp (fall (fun α : V => fimp (eps α a) (ExU (ψ α))))
                  (fiff (eps β (vrepl a ψ)) (fex (fun α : V => fand (eps α a) (ψ α β)))).
Proof.
  eexists. intros a ψ Hψ β. apply n_lam.
  set (W := vrepl a ψ). set (B := coll (idx a) (sub a) ψ).
  apply n_iff.
  - eapply n_eps_el; [apply n_hyp0|]. intros [t s] Hts.
    apply (n_exI (fun α : V => fand (eps α a) (ψ α β)) (sub a t)). apply n_pair.
    + eapply (n_eps_in _ _ a t); [reflexivity|]. eapply n_fst, n_hyp0.
    + eapply n_eq; [|eapply n_snd, n_hyp0]. apply Hψ; [reflexivity|].
      apply (teq_trans _ _ (sub W (t, s))); [apply teq_sym; unfold W, vrepl; apply (sub_mk F)|exact Hts].
  - apply (n_exE (fun α : V => fand (eps α a) (ψ α β))); [apply n_hyp0|]. intros α.
    eapply n_eps_el; [eapply n_fst, n_hyp0|]. intros t Ht.
    apply (n_exE (fun β0 : V => fand (ψ α β0) (fall (fun β' : V => fimp (ψ α β') (veq β' β0))))).
    { eapply n_app; [apply (n_inst (fun α : V => fimp (eps α a) (ExU (ψ α))) α); apply n_wk, n_wk, n_wk, n_hyp0|].
      apply n_wk. eapply n_fst, n_hyp0. }
    intros β0. destruct (coll_spec (idx a) (sub a) ψ Hψ t β) as [s Hs].
    set (w := sub W (t, s)).
    assert (K : ψ α β ≡ ψ α w).
    { etransitivity; [apply Hψ; [symmetry; exact Ht|reflexivity]|]. etransitivity; [exact Hs|].
      apply Hψ; [exact Ht|apply teq_sym; unfold w, W, vrepl; apply (sub_mk F)]. }
    apply (n_leib (PepsL W) w β).
    + eapply n_trans.
      * eapply n_app; [apply (n_inst (fun β' : V => fimp (ψ α β') (veq β' β0)) w); eapply n_snd, n_hyp0|].
        eapply n_eq; [exact K|]. apply n_wk, n_wk. eapply n_snd, n_hyp0.
      * apply n_sym. eapply n_app; [apply (n_inst (fun β' : V => fimp (ψ α β') (veq β' β0)) β); eapply n_snd, n_hyp0|].
        apply n_wk, n_wk. eapply n_snd, n_hyp0.
    + cbn. eapply (n_eps_in _ _ W (t, s)); [reflexivity|]. apply n_pair; [apply n_wk, n_hyp0|].
      eapply n_eq; [|apply n_wk, n_wk; eapply n_snd, n_hyp0].
      etransitivity; [apply Hψ; [symmetry; exact Ht|reflexivity]|exact Hs].
Qed.

(** ** {α ε a | φ} ε 𝒫(a), and the elements of 𝒫(x) are subsets of x *)

Lemma R_seppow : exists e, forall a (φ : V -> pcar F), Pproper F φ -> ftop —[e]→ eps (vsep a φ) (vpower a).
Proof.
  eexists. intros a φ Hφ. eapply (n_eps_in _ _ (vpower a) (fun t => enc (φ (sub a t)))); [|apply f_top].
  destruct a as [s l]. exists eq_refl. cbn. apply rel_proper; [apply leq_refl|]. intros t. apply dec_enc.
Qed.

Lemma R_powres : exists e, forall x a, ftop —[e]→
  fimp (eps a (vpower x)) (fex (fun b : V => fall (fun α : V => fiff (eps α a) (fand (eps α x) (eps α b))))).
Proof.
  eexists. intros [[T k] l] a. set (X := existT (lab F) (node T k) l). apply n_lam.
  apply (n_exI (fun b : V => fall (fun α : V => fiff (eps α a) (fand (eps α X) (eps α b)))) a).
  apply n_gen; intros α. apply n_iff.
  - apply n_pair; [|apply n_hyp0].
    eapply n_eps_el; [apply n_wk, n_hyp0|]. intros g Hg.
    eapply n_eps_el; [eapply n_eq; [apply eps_proper; [reflexivity|symmetry; exact Hg]|apply n_wk, n_hyp0]|].
    intros t Ht. eapply (n_eps_in _ _ X t); [exact Ht|]. eapply n_snd, n_hyp0.
  - eapply n_snd, n_hyp0.
Qed.

(** ** ω *)

Definition Rom (x : V) : pcar F := for_ (veq x vempty) (fex (fun b : V => fand (eps b vomega) (veq x (vsuc b)))).

Lemma sub_omega n : teq (sub vomega n) (snat n).
Proof. apply (sub_mk F). Qed.

Lemma R_omega : exists e, forall x, ftop —[e]→ fiff (eps x vomega) (Rom x).
Proof.
  eexists. intros x.
  assert (G0 : forall φ, φ —[e_lam (e_kl (e_comp e_snd e_snd))]→ fimp (fand (pnat 0) (veq x (snat 0))) (Rom x)).
  { intros φ. apply n_lam, n_orI1. eapply n_snd, n_hyp0. }
  assert (GS : forall φ m, φ —[e_lam (e_kr (e_comp (e_pair (e_comp (e_comp (e_comp e_snd e_fst) e_snd) e_exI) (e_comp e_snd e_snd)) e_exI))]→
                 fimp (fand (pnat (S m)) (veq x (snat (S m)))) (Rom x)).
  { intros φ m. apply n_lam, n_orI2.
    apply (n_exI (fun b : V => fand (eps b vomega) (veq x (vsuc b))) (snat m)). apply n_pair.
    - eapply (n_eps_in _ _ vomega m); [apply sub_omega|]. eapply n_snd, n_fst, n_hyp0.
    - eapply n_snd, n_hyp0. }
  apply n_iff.
  - eapply n_eps_el; [apply n_hyp0|]. intros n Hn.
    assert (D : fand (fand ftop (eps x vomega)) (pnat n) —[e_pair e_snd e_refl]→ fand (pnat n) (veq x (snat n))).
    { apply n_pair; [apply n_hyp0|]. apply n_veq_of_teq. rewrite <- Hn. symmetry. apply sub_omega. }
    destruct n as [|m].
    + eapply n_app; [|exact D].
      eapply n_app; [eapply n_app; [apply (n_selT _ _ (fimp (fand (pnat 1) (veq x (snat 1))) (Rom x))); eapply n_fst, n_hyp0|apply G0]|apply GS].
    + eapply n_app; [|exact D].
      eapply n_app; [eapply n_app; [apply n_selF; eapply n_fst, n_hyp0|apply G0]|apply GS].
  - apply (n_orE _ (veq x vempty) (fex (fun b : V => fand (eps b vomega) (veq x (vsuc b))))); [apply n_hyp0| |].
    + apply (n_leib (PepsL vomega) vempty x); [apply n_sym, n_hyp0|]. cbn.
      eapply (n_eps_in _ _ vomega 0); [apply sub_omega|]. apply n_pair; [apply n_tagT|apply f_top].
    + apply (n_exE (fun b : V => fand (eps b vomega) (veq x (vsuc b)))); [apply n_hyp0|]. intros b.
      eapply n_eps_el; [eapply n_fst, n_hyp0|]. intros n Hn.
      apply (n_leib (PepsL vomega) (vsuc b) x); [apply n_sym, n_wk; eapply n_snd, n_hyp0|]. cbn.
      eapply (n_eps_in _ _ vomega (S n)).
      * etransitivity; [apply sub_omega|]. apply vsuc_proper. rewrite <- Hn. symmetry. apply sub_omega.
      * apply n_pair; [apply n_tagF|apply n_hyp0].
Qed.

(** ** The syntactic axioms *)

#[local] Instance eps_Proper : Proper (teq ==> teq ==> peq) (@eps F).
Proof. intros ? ? ? ? ? ?; apply eps_proper; assumption. Qed.
#[local] Instance veq_Proper : Proper (teq ==> teq ==> peq) (@veq F).
Proof. intros ? ? ? ? ? ?; apply veq_proper; assumption. Qed.
#[local] Instance vmem_Proper : Proper (teq ==> teq ==> peq) (@vmem F).
Proof. intros ? ? ? ? ? ?; apply vmem_proper; assumption. Qed.
#[local] Instance vsub_Proper : Proper (teq ==> teq ==> peq) (@vsub F).
Proof. intros ? ? ? ? ? ?; apply vsub_proper; assumption. Qed.
#[local] Instance veqv_Proper : Proper (teq ==> teq ==> peq) (@veqv F).
Proof. intros ? ? ? ? ? ?; apply veqv_proper; assumption. Qed.
#[local] Instance vpower_Proper : Proper (teq ==> teq) vpower.
Proof. intros ? ? ?; apply vpower_proper; assumption. Qed.
#[local] Instance fex_Proper I : Proper (pointwise_relation I peq ==> peq) (@fex F I).
Proof. intros f g H; apply fex_proper, H. Qed.
#[local] Instance fall_Proper I : Proper (pointwise_relation I peq ==> peq) (@fall F I).
Proof. intros f g H; apply fall_proper, H. Qed.
#[local] Instance for_Proper : Proper (peq ==> peq ==> peq) (@for_ F).
Proof. intros ? ? ? ? ? ?; apply for_proper; assumption. Qed.

Local Notation evt := (evt F Φ0 dec coll).
Local Notation evf := (evf F Φ0 dec coll).

Lemma evt_sht' ρ z t : teq (evt (z .: ρ) (sht t)) (evt ρ t).
Proof. apply evt_sht, coll_proper. Qed.

Lemma evf_inst' ρ φ t : evf ρ (inst φ t) ≡ evf (evt ρ t .: ρ) φ.
Proof. apply evf_inst, coll_proper. Qed.

Lemma evf_up1 ρ x y φ : evf (y .: x .: ρ) (renf (upr S) φ) ≡ evf (y .: ρ) φ.
Proof. apply (proj2 (ev_ren F Φ0 dec coll coll_proper)). intros [|n]; reflexivity. Qed.

Lemma evf_up2 ρ x y b φ : evf (y .: x .: b .: ρ) (renf (upr (upr S)) φ) ≡ evf (y .: x .: ρ) φ.
Proof. apply (proj2 (ev_ren F Φ0 dec coll coll_proper)). intros [|[|n]]; reflexivity. Qed.

Lemma evf_repl_body ρ α ψ b : evf (α .: ρ) (repl_body ψ b) ≡ evf (evt ρ b .: α .: ρ) ψ.
Proof.
  apply (proj2 (ev_subst F Φ0 dec coll coll_proper)). intros [|[|n]]; cbn; [apply evt_sht'|reflexivity|reflexivity].
Qed.

Lemma pproper_evf ρ φ : Pproper F (fun z => evf (z .: ρ) φ).
Proof. intros z z' E. apply (evf_proper F Φ0 dec coll coll_proper), venv_cons; [intros n; reflexivity|exact E]. Qed.

Lemma rproper_evf ρ ψ : Rproper F (fun α β => evf (β .: α .: ρ) ψ).
Proof.
  intros α α' β β' Eα Eβ. apply (evf_proper F Φ0 dec coll coll_proper).
  apply venv_cons; [apply venv_cons; [intros n; reflexivity|exact Eα]|exact Eβ].
Qed.

Ltac sem H := let e := fresh "e" in let He := fresh "He" in
  destruct H as [e He]; exists e; intros ρ; eapply fent_eq_r; [|apply He]; cbn [Model.evf Model.evt].

Ltac semp H := destruct H as [e He]; exists e; intros ρ; eapply fent_eq_r.

Ltac evsimpl := cbn [Model.evf Model.evt]; repeat setoid_rewrite evt_sht'.

Theorem thm26 φ : IZFe φ -> urealized F Φ0 dec coll φ.
Proof.
  intros H. destruct H as [φ H|ψ a b|φ a|x a].
  - destruct H.
    + semp R_empty; [|apply (He (evt ρ x))]. unfold A_empty. evsimpl. reflexivity.
    + semp R_omega; [|apply (He (evt ρ x))]. unfold A_omega, Rom, tsuc. evsimpl. reflexivity.
    + semp R_pair; [|apply (He (evt ρ z) (evt ρ x) (evt ρ y))]. unfold A_pair. evsimpl. reflexivity.
    + semp R_union; [|apply (He (evt ρ x) (evt ρ y))]. unfold A_union. evsimpl. reflexivity.
    + semp R_wpow; [|apply (He (evt ρ x) (evt ρ a))]. unfold A_wpow. evsimpl. reflexivity.
    + semp R_mem; [|apply (He (evt ρ x) (evt ρ y))]. unfold A_mem. evsimpl. reflexivity.
    + semp R_sub; [|apply (He (evt ρ x) (evt ρ y))]. unfold A_sub. evsimpl. reflexivity.
    + semp R_eqv; [|apply (He (evt ρ x) (evt ρ y))]. unfold A_eqv. evsimpl. reflexivity.
    + semp R_sep; [|apply (He (evt ρ z) (evt ρ y) _ (pproper_evf ρ φ))].
      unfold A_sep. evsimpl. rewrite evf_inst'. reflexivity.
    + semp R_ind; [|apply (He _ (pproper_evf ρ φ))].
      unfold A_ind, Hind. evsimpl. setoid_rewrite evf_up1. reflexivity.
    + semp R_coll; [|apply (He (evt ρ a) _ (rproper_evf ρ ψ))].
      unfold A_coll. evsimpl. setoid_rewrite evf_up2. reflexivity.
  - semp R_repl; [|apply (He (evt ρ a) _ (rproper_evf ρ ψ) (evt ρ b))].
    unfold A_repl, fExU, ExU. evsimpl. setoid_rewrite evf_repl_body. setoid_rewrite evf_up1. reflexivity.
  - destruct R_seppow as [e He]. exists e. intros ρ. apply (He _ _ (pproper_evf ρ φ)).
  - semp R_powres; [|apply (He (evt ρ x) (evt ρ a))]. unfold A_powres. evsimpl. reflexivity.
Qed.

(** Consequence: every theorem of IZFε is realized in V(E). *)
Corollary IZFe_realized φ : prv IZFe [] φ -> urealized F Φ0 dec coll φ.
Proof. apply soundness_closed; [exact coll_proper|exact thm26]. Qed.

End Realize.
