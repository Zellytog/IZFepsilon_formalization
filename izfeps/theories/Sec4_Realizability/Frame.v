(** * Evidenced frames (Section 4.1 of the paper)

    After Cohen, Miquey and Tate. An evidenced frame (Definition 18)
    consists of:
    - a setoid Φ of propositions;
    - a type E of evidences;
    - a relation e ⊩ φ ⩽ ψ, written here [φ —[e]→ ψ];
    with the evidences e_id, (;), e_⊤, ⟨·,·⟩, π₀, π₁, λ, e_ev and e_incl.

    As in Cohen, Miquey and Tate, the primitive structure is the universal
    implication φ ⊃ ⋂S, with λ and e_ev; φ ⊃ ψ and ⋂S are derived from it
    (φ ⊃ ⋂{ψ} and ⊤ ⊃ ⋂S). Introducing ⋂ with the same evidence (the
    initial version of Definition 18) would rule out partial PCAs: for
    S = ∅, it would require e·a to be defined for every e. Here
    e ⊩ ψ ⩽ φ for all φ ∈ S gives λ(π₀; e) ⊩ ψ ⩽ ⋂S. A subset S of Φ is a
    predicate Φ → Prop; ⋂ indexed by an arbitrary type is derived from it
    ([fall]), which fixes no universe of indices.

    ⊥, ∨ and ⋃ are encoded impredicatively (Notation 19). Φ is a setoid,
    which avoids extensionality. *)

From Stdlib Require Import Setoid Morphisms.

(** ** Setoids *)

Record pset := {
  pcar :> Type;
  peq : pcar -> pcar -> Prop;
  peq_refl : forall x, peq x x;
  peq_sym : forall x y, peq x y -> peq y x;
  peq_trans : forall x y z, peq x y -> peq y z -> peq x z
}.

Arguments peq {p} x y.
Arguments peq_refl {p} x.
Arguments peq_sym {p x y} _.
Arguments peq_trans {p x y z} _ _.

Notation "x ≡ y" := (peq x y) (at level 70, no associativity).

#[export] Instance peq_equiv (X : pset) : Equivalence (@peq X).
Proof. split; [intros x; apply peq_refl|intros x y; apply peq_sym|intros x y z; apply peq_trans]. Qed.

Record pmor (X Y : pset) := {
  pfun :> X -> Y;
  pfun_proper : forall x x', x ≡ x' -> pfun x ≡ pfun x'
}.

Arguments pfun {X Y} _ _.
Arguments pfun_proper {X Y} _ {x x'} _.

Definition pmor_comp {X Y Z} (f : pmor Y Z) (g : pmor X Y) : pmor X Z :=
  {| pfun := fun x => f (g x); pfun_proper := fun _ _ H => pfun_proper f (pfun_proper g H) |}.

Program Definition disc (A : Type) : pset := {| pcar := A; peq := @eq A |}.
Solve All Obligations with (intros; subst; reflexivity).

Program Definition PropS : pset := {| pcar := Prop; peq := iff |}.
Solve All Obligations with (cbn; tauto).

(** ** The structure *)

Record frame := {
  fprop :> pset;
  fev : Type;
  fent : fprop -> fev -> fprop -> Prop;
  fent_proper : forall φ φ' e ψ ψ', φ ≡ φ' -> ψ ≡ ψ' -> fent φ e ψ -> fent φ' e ψ';

  e_id : fev;
  f_id : forall φ, fent φ e_id φ;
  e_comp : fev -> fev -> fev;
  f_comp : forall φ ψ χ e1 e2, fent φ e1 ψ -> fent ψ e2 χ -> fent φ (e_comp e1 e2) χ;

  ftop : fprop;
  e_top : fev;
  f_top : forall φ, fent φ e_top ftop;

  fand : fprop -> fprop -> fprop;
  fand_proper : forall φ φ' ψ ψ', φ ≡ φ' -> ψ ≡ ψ' -> fand φ ψ ≡ fand φ' ψ';
  e_pair : fev -> fev -> fev;
  f_pair : forall φ ψ χ e1 e2, fent φ e1 ψ -> fent φ e2 χ -> fent φ (e_pair e1 e2) (fand ψ χ);
  e_fst : fev;
  f_fst : forall φ ψ, fent (fand φ ψ) e_fst φ;
  e_snd : fev;
  f_snd : forall φ ψ, fent (fand φ ψ) e_snd ψ;

  (** Universal implication φ ⊃ ⋂S (Cohen–Miquey–Tate). *)
  fuimp : fprop -> (fprop -> Prop) -> fprop;
  fuimp_proper : forall φ φ' (S T : fprop -> Prop), φ ≡ φ' -> (forall ψ, S ψ <-> T ψ) -> fuimp φ S ≡ fuimp φ' T;
  e_lam : fev -> fev;
  f_ulam : forall φ1 φ2 (S : fprop -> Prop) e, (forall ψ, S ψ -> fent (fand φ1 φ2) e ψ) -> fent φ1 (e_lam e) (fuimp φ2 S);
  e_ev : fev;
  f_uev : forall φ (S : fprop -> Prop) ψ, S ψ -> fent (fand φ (fuimp φ S)) e_ev ψ
}.

Arguments fent {f} φ e ψ : rename.
Arguments e_id {f} : rename.
Arguments e_comp {f} e1 e2 : rename.
Arguments ftop {f} : rename.
Arguments e_top {f} : rename.
Arguments fand {f} φ ψ : rename.
Arguments e_fst {f} : rename.
Arguments e_snd {f} : rename.
Arguments e_pair {f} e1 e2 : rename.
Arguments fuimp {f} φ S : rename.
Arguments e_lam {f} e : rename.
Arguments e_ev {f} : rename.

Notation "φ —[ e ]→ ψ" := (fent φ e ψ) (at level 70).

#[export] Instance fent_Proper (F : frame) : Proper (peq ==> eq ==> peq ==> iff) (@fent F).
Proof.
  intros φ φ' Hφ e e' <- ψ ψ' Hψ. split; apply fent_proper; auto; apply peq_sym; auto.
Qed.
#[export] Instance fand_Proper (F : frame) : Proper (peq ==> peq ==> peq) (@fand F).
Proof. intros ? ? ? ? ? ?; apply fand_proper; auto. Qed.
(** ** Implication and ⋂, derived from the universal implication

    φ ⊃ ψ ≜ φ ⊃ ⋂{ψ} and ⋂S ≜ ⊤ ⊃ ⋂S. Introducing ⋂ then requires the
    evidence λ(π₀; e) instead of e: this is what allows partial PCAs (for
    S = ∅, ⋂∅ does not require e·a to be defined). *)

Definition fimp {F : frame} (φ ψ : fprop F) : fprop F := fuimp φ (fun χ => χ ≡ ψ).

Lemma fimp_proper (F : frame) (φ φ' ψ ψ' : F) : φ ≡ φ' -> ψ ≡ ψ' -> fimp φ ψ ≡ fimp φ' ψ'.
Proof.
  intros H1 H2. apply fuimp_proper; [exact H1|]. intros χ. split; intros H.
  - exact (peq_trans H H2).
  - exact (peq_trans H (peq_sym H2)).
Qed.

#[export] Instance fimp_Proper (F : frame) : Proper (peq ==> peq ==> peq) (@fimp F).
Proof. intros ? ? ? ? ? ?; apply fimp_proper; auto. Qed.

Lemma f_lam (F : frame) (φ ψ χ : F) e : fand φ ψ —[e]→ χ -> φ —[e_lam e]→ fimp ψ χ.
Proof.
  intros H. apply f_ulam. intros χ' E. exact (fent_proper F _ _ e _ _ (peq_refl _) (peq_sym E) H).
Qed.

Lemma f_ev (F : frame) (φ ψ : F) : fand φ (fimp φ ψ) —[e_ev]→ ψ.
Proof. apply f_uev. apply peq_refl. Qed.

Definition fallP {F : frame} (S : fprop F -> Prop) : fprop F := fuimp ftop S.

Lemma fallP_proper (F : frame) (S T : fprop F -> Prop) : (forall ψ, S ψ <-> T ψ) -> fallP S ≡ fallP T.
Proof. intros H. apply fuimp_proper; [apply peq_refl|exact H]. Qed.

Definition e_gen {F : frame} (e : fev F) : fev F := e_lam (e_comp e_fst e).

Lemma f_genP (F : frame) (S : fprop F -> Prop) (φ : F) e :
  (forall ψ, S ψ -> φ —[e]→ ψ) -> φ —[e_gen e]→ fallP S.
Proof. intros H. apply f_ulam. intros ψ Hψ. eapply f_comp; [apply f_fst|apply H, Hψ]. Qed.

Definition e_incl {F : frame} : fev F := e_comp (e_pair e_top e_id) e_ev.

Lemma f_inclP (F : frame) (S : fprop F -> Prop) ψ : S ψ -> fallP S —[e_incl]→ ψ.
Proof. intros H. eapply f_comp; [apply f_pair; [apply f_top|apply f_id]|apply f_uev, H]. Qed.

(** ** ⋂ indexed by a type *)

#[universes(polymorphic)]
Definition fall {F : frame} {I : Type} (f : I -> fprop F) : fprop F :=
  fallP (fun ψ => exists i, ψ ≡ f i).

#[universes(polymorphic)]
Lemma fall_proper (F : frame) I (f g : I -> fprop F) : (forall i, f i ≡ g i) -> fall f ≡ fall g.
Proof.
  intros H. apply fallP_proper. intros ψ. split; intros [i Hi]; exists i.
  - exact (peq_trans Hi (H i)).
  - exact (peq_trans Hi (peq_sym (H i))).
Qed.

(** Two families with the same image have the same ⋂, even when indexed differently. *)
#[universes(polymorphic)]
Lemma fall_proper_idx (F : frame) I J (f : I -> fprop F) (g : J -> fprop F) :
  (forall i, exists j, f i ≡ g j) -> (forall j, exists i, g j ≡ f i) -> fall f ≡ fall g.
Proof.
  intros H1 H2. apply fallP_proper. intros ψ. split.
  - intros [i Hi]. destruct (H1 i) as [j Hj]. exists j. exact (peq_trans Hi Hj).
  - intros [j Hj]. destruct (H2 j) as [i Hi]. exists i. exact (peq_trans Hj Hi).
Qed.

#[universes(polymorphic)]
Lemma f_gen (F : frame) I (φ : fprop F) (f : I -> fprop F) e :
  (forall i, φ —[e]→ f i) -> φ —[e_gen e]→ fall f.
Proof.
  intros H. apply f_genP. intros ψ [i Hi].
  exact (fent_proper F φ φ e (f i) ψ (peq_refl φ) (peq_sym Hi) (H i)).
Qed.

#[universes(polymorphic)]
Lemma f_incl (F : frame) I (f : I -> fprop F) i : fall f —[e_incl]→ f i.
Proof. apply f_inclP. exists i. apply peq_refl. Qed.

Section Derived.

Context {F : frame}.

Lemma fent_eq φ φ' e (ψ : F) : φ ≡ φ' -> φ —[e]→ ψ -> φ' —[e]→ ψ.
Proof. intros H. apply fent_proper; [exact H|apply peq_refl]. Qed.

Lemma fent_eq_r (φ : F) e ψ ψ' : ψ ≡ ψ' -> φ —[e]→ ψ -> φ —[e]→ ψ'.
Proof. intros H. apply fent_proper; [apply peq_refl|exact H]. Qed.

Lemma fent_of_eq (φ ψ : F) : φ ≡ ψ -> φ —[e_id]→ ψ.
Proof. intros H. apply (fent_eq_r φ e_id φ ψ H), f_id. Qed.

(** e@e' ≜ ⟨e', e⟩ ; e_ev (Notation 19). *)
Definition e_app (e e' : fev F) : fev F := e_comp (e_pair e' e) e_ev.

(** ** Natural deduction under a context

    φ —[e]→ ψ reads "under φ, e proves ψ". *)

Lemma n_app (φ A B : F) e1 e2 : φ —[e1]→ fimp A B -> φ —[e2]→ A -> φ —[e_app e1 e2]→ B.
Proof. intros H1 H2. eapply f_comp; [apply f_pair; eassumption|apply f_ev]. Qed.

Lemma n_lam (φ A B : F) e : fand φ A —[e]→ B -> φ —[e_lam e]→ fimp A B.
Proof. apply f_lam. Qed.

Lemma n_fst (φ A B : F) e : φ —[e]→ fand A B -> φ —[e_comp e e_fst]→ A.
Proof. intros H. eapply f_comp; [exact H|apply f_fst]. Qed.

Lemma n_snd (φ A B : F) e : φ —[e]→ fand A B -> φ —[e_comp e e_snd]→ B.
Proof. intros H. eapply f_comp; [exact H|apply f_snd]. Qed.

Lemma n_pair (φ A B : F) e1 e2 : φ —[e1]→ A -> φ —[e2]→ B -> φ —[e_pair e1 e2]→ fand A B.
Proof. apply f_pair. Qed.

Lemma n_inst {I} (f : I -> F) i φ e : φ —[e]→ fall f -> φ —[e_comp e e_incl]→ f i.
Proof. intros H. eapply f_comp; [exact H|apply f_incl]. Qed.

Lemma n_gen {I} (f : I -> F) φ e : (forall i, φ —[e]→ f i) -> φ —[e_gen e]→ fall f.
Proof. apply f_gen. Qed.

Lemma n_hyp0 (φ A : F) : fand φ A —[e_snd]→ A.
Proof. apply f_snd. Qed.

Lemma n_wk (φ A B : F) e : φ —[e]→ B -> fand φ A —[e_comp e_fst e]→ B.
Proof. intros H. eapply f_comp; [apply f_fst|exact H]. Qed.

Lemma n_cut (φ A B : F) e1 e2 : φ —[e1]→ A -> fand φ A —[e2]→ B -> φ —[e_comp (e_pair e_id e1) e2]→ B.
Proof. intros H1 H2. eapply f_comp; [apply f_pair; [apply f_id|exact H1]|exact H2]. Qed.

Lemma n_eq (φ ψ ψ' : F) e : ψ ≡ ψ' -> φ —[e]→ ψ -> φ —[e]→ ψ'.
Proof. intros E H. exact (fent_eq_r _ _ _ _ E H). Qed.

Definition e_const (e : fev F) : fev F := e_comp e_top e.

Lemma n_const (φ ψ : F) e : ftop —[e]→ ψ -> φ —[e_const e]→ ψ.
Proof. intros H. eapply f_comp; [apply f_top|exact H]. Qed.

(** ** ⊥ ≜ ⋂_{χ ∈ Φ} χ *)

Definition fbot : F := fall (I := pcar F) (fun φ => φ).

Lemma f_bot (φ : F) : fbot —[e_incl]→ φ.
Proof. apply (f_incl _ _ (fun φ => φ) φ). Qed.

(** ** φ ∨ ψ ≜ ⋂_χ (φ ⊃ χ) ⊃ (ψ ⊃ χ) ⊃ χ *)

Definition for_ (φ ψ : F) : F :=
  fall (I := pcar F) (fun χ => fimp (fimp φ χ) (fimp (fimp ψ χ) χ)).

Lemma for_proper (φ φ' ψ ψ' : F) : φ ≡ φ' -> ψ ≡ ψ' -> for_ φ ψ ≡ for_ φ' ψ'.
Proof.
  intros H1 H2. apply fall_proper. intros χ. rewrite H1, H2. reflexivity.
Qed.

Definition e_kl (e : fev F) : fev F := e_gen (e_lam (e_lam (e_app (e_comp e_fst e_snd) (e_comp e_fst (e_comp e_fst e))))).
Definition e_kr (e : fev F) : fev F := e_gen (e_lam (e_lam (e_app e_snd (e_comp e_fst (e_comp e_fst e))))).

Lemma n_orI1 (φ A B : F) e : φ —[e]→ A -> φ —[e_kl e]→ for_ A B.
Proof.
  intros H. apply n_gen. intros χ. apply n_lam, n_lam.
  eapply n_app; [apply n_wk, n_hyp0|]. apply n_wk, n_wk, H.
Qed.

Lemma n_orI2 (φ A B : F) e : φ —[e]→ B -> φ —[e_kr e]→ for_ A B.
Proof.
  intros H. apply n_gen. intros χ. apply n_lam, n_lam.
  eapply n_app; [apply n_hyp0|]. apply n_wk, n_wk, H.
Qed.

Definition e_case (e0 e1 e2 : fev F) : fev F := e_app (e_app (e_comp e0 e_incl) (e_lam e1)) (e_lam e2).

(** Elimination of ∨ under a context. *)
Lemma n_orE (φ A B χ : F) e0 e1 e2 :
  φ —[e0]→ for_ A B -> fand φ A —[e1]→ χ -> fand φ B —[e2]→ χ -> φ —[e_case e0 e1 e2]→ χ.
Proof.
  intros H0 H1 H2. eapply n_app; [eapply n_app|].
  - apply (n_inst (fun χ0 => fimp (fimp A χ0) (fimp (fimp B χ0) χ0)) χ), H0.
  - apply n_lam, H1.
  - apply n_lam, H2.
Qed.

(** ** ⋃_{x ∈ X} φ(x) ≜ ⋂_χ (⋂_x (φ(x) ⊃ χ)) ⊃ χ *)

Definition fex {I : Type} (f : I -> F) : F :=
  fall (I := pcar F) (fun χ => fimp (fall (fun i => fimp (f i) χ)) χ).

Lemma fex_proper I (f g : I -> F) : (forall i, f i ≡ g i) -> fex f ≡ fex g.
Proof.
  intros H. apply fall_proper. intros χ. apply fimp_proper; [|apply peq_refl].
  apply fall_proper. intros i. apply fimp_proper; [apply H|apply peq_refl].
Qed.

Lemma fex_proper_idx I J (f : I -> F) (g : J -> F) :
  (forall i, exists j, f i ≡ g j) -> (forall j, exists i, g j ≡ f i) -> fex f ≡ fex g.
Proof.
  intros H1 H2. apply fall_proper. intros χ. apply fimp_proper; [|apply peq_refl].
  apply fall_proper_idx.
  - intros i. destruct (H1 i) as [j Hj]. exists j. rewrite Hj. reflexivity.
  - intros j. destruct (H2 j) as [i Hi]. exists i. rewrite Hi. reflexivity.
Qed.

(** e_∃ ⊩ φ(x) ⩽ ⋃ φ. *)
Definition e_exI : fev F := e_gen (e_lam (e_app (e_comp e_snd e_incl) e_fst)).

Lemma f_exI I (f : I -> F) i : f i —[e_exI]→ fex f.
Proof.
  apply n_gen. intros χ. apply n_lam. eapply n_app; [|apply f_fst].
  apply (n_inst (fun j => fimp (f j) χ) i). apply n_hyp0.
Qed.

Lemma n_exI {I} (f : I -> F) i φ e : φ —[e]→ f i -> φ —[e_comp e e_exI]→ fex f.
Proof. intros H. eapply f_comp; [exact H|apply f_exI]. Qed.

(** e_{∃,elim}(e) ⊩ θ ∧ ⋃ φ ⩽ ψ whenever e ⊩ θ ∧ φ(x) ⩽ ψ for all x. *)
Definition e_exE (e : fev F) : fev F :=
  e_app (e_comp e_snd e_incl) (e_gen (e_lam (e_comp (e_pair (e_comp e_fst e_fst) e_snd) e))).

Lemma f_exE I (θ : F) (f : I -> F) ψ e :
  (forall i, fand θ (f i) —[e]→ ψ) -> fand θ (fex f) —[e_exE e]→ ψ.
Proof.
  intros H. eapply n_app.
  - apply (n_inst (fun χ => fimp (fall (fun i => fimp (f i) χ)) χ) ψ), n_hyp0.
  - apply n_gen. intros i. apply n_lam.
    eapply f_comp; [apply f_pair; [eapply n_fst, f_fst|apply f_snd]|apply H].
Qed.

(** ∃-elimination under a context. *)
Definition e_exE_ctx (e0 e : fev F) : fev F := e_comp (e_pair e_id e0) (e_exE e).

Lemma n_exE {I} (f : I -> F) (φ χ : F) e0 e :
  φ —[e0]→ fex f -> (forall i, fand φ (f i) —[e]→ χ) -> φ —[e_exE_ctx e0 e]→ χ.
Proof.
  intros H0 H. eapply f_comp; [apply f_pair; [apply f_id|exact H0]|]. apply f_exE, H.
Qed.

(** [P] ≜ ⋃{− ∈ {⊤} | P}: a meta-level proposition, without computational content. *)
Definition fbr (P : Prop) : F := fex (fun _ : P => ftop).

End Derived.

Arguments fbot {F}.

(** ** Change of index *)

Lemma f_fex_map {F : frame} {I J : Type} (f : I -> F) (g : J -> F) (h : I -> J) :
  (forall i, f i ≡ g (h i)) -> fex f —[e_exE_ctx e_id (e_comp e_snd e_exI)]→ fex g.
Proof.
  intros H. apply (n_exE f); [apply f_id|]. intros i.
  eapply f_comp; [apply f_snd|]. eapply fent_eq; [apply peq_sym, H|]. apply (f_exI _ g (h i)).
Qed.

(** ** Leibniz equality (Definition 25)

    ⟦a = b⟧ ≜ ⋂_P (P(a) ⊃ P(b)), over the predicates P compatible with
    the setoid equality. The paper quantifies over the predicates on
    {a, b}; without excluded middle, such a predicate cannot be extended
    to the whole universe, hence this choice (both realize reflexivity
    and transport, which is all that is used). *)

Section Leibniz.

Context {F : frame}.

Definition leib {A : pset} (a b : A) : F := fall (I := pmor A F) (fun P => fimp (P a) (P b)).

Lemma leib_proper {A : pset} (a a' b b' : A) : a ≡ a' -> b ≡ b' -> leib a b ≡ leib a' b'.
Proof. intros Ea Eb. apply fall_proper. intros P. apply fimp_proper; apply pfun_proper; assumption. Qed.

Definition e_refl : fev F := e_gen (e_lam e_snd).

Lemma n_refl {A : pset} (a : A) (φ : F) : φ —[e_refl]→ leib a a.
Proof. apply n_gen. intros P. apply n_lam, n_hyp0. Qed.

Lemma n_leib {A : pset} (P : pmor A F) (a b : A) (φ : F) e1 e2 :
  φ —[e1]→ leib a b -> φ —[e2]→ P a -> φ —[e_app (e_comp e1 e_incl) e2]→ P b.
Proof.
  intros H1 H2. apply (n_app φ (P a) (P b)); [|exact H2].
  exact (n_inst (fun ψ : pmor A F => fimp (ψ a) (ψ b)) P φ e1 H1).
Qed.

Definition leibL {A : pset} (b : A) : pmor A F :=
  Build_pmor A F (fun z => leib z b) (fun z z' E => leib_proper z z' b b E (peq_refl b)).
Definition leibR {A : pset} (a : A) : pmor A F :=
  Build_pmor A F (fun z => leib a z) (fun z z' E => leib_proper a a z z' (peq_refl a) E).

Definition e_sym (e : fev F) : fev F := e_app (e_comp e e_incl) e_refl.

Lemma n_sym {A : pset} (a b : A) (φ : F) e : φ —[e]→ leib a b -> φ —[e_sym e]→ leib b a.
Proof. intros H. exact (n_leib (leibL a) a b φ e _ H (n_refl a φ)). Qed.

Definition e_trans (e1 e2 : fev F) : fev F := e_app (e_comp e2 e_incl) e1.

Lemma n_trans {A : pset} (a b c : A) (φ : F) e1 e2 :
  φ —[e1]→ leib a b -> φ —[e2]→ leib b c -> φ —[e_trans e1 e2]→ leib a c.
Proof. intros H1 H2. exact (n_leib (leibR a) b c φ e2 e1 H2 H1). Qed.

(** Equality is preserved by every morphism. *)
Lemma f_leib_map {A B : pset} (f : pmor A B) (a b : A) :
  leib a b —[e_gen e_incl]→ leib (f a) (f b).
Proof.
  apply n_gen. intros P. apply (f_incl F _ (fun ψ0 : pmor A F => fimp (ψ0 a) (ψ0 b)) (pmor_comp P f)).
Qed.

End Leibniz.

(** ** The operad generated by the structure, and the fixed point (Definitions 20–21)

    The functions E → E of the operad are described by expressions with
    one variable, built from the operations of the frame (with no other
    constant). A fixed point combinator maps each expression f to an
    evidence y(f) that does at least what f(y(f)) does. Taking it on
    expressions rather than on functions is a weaker hypothesis: a fixed
    point in the sense of the paper gives one here. *)

Section Operad.

Context (F : frame).

Inductive eexp : Type :=
| x_var | x_id | x_comp (a b : eexp) | x_top | x_pair (a b : eexp) | x_fst | x_snd
| x_lam (a : eexp) | x_ev | x_incl.

Fixpoint eeval (t : fev F) (a : eexp) : fev F :=
  match a with
  | x_var => t
  | x_id => e_id
  | x_comp a b => e_comp (eeval t a) (eeval t b)
  | x_top => e_top
  | x_pair a b => e_pair (eeval t a) (eeval t b)
  | x_fst => e_fst
  | x_snd => e_snd
  | x_lam a => e_lam (eeval t a)
  | x_ev => e_ev
  | x_incl => e_incl
  end.

Definition fixpoint_comb (y : eexp -> fev F) : Prop :=
  forall f (φ ψ : F), φ —[eeval (y f) f]→ ψ -> φ —[y f]→ ψ.

End Operad.




(** ** The frame of Prop (the intuitionistic order) *)

Program Definition prop_frame : frame := {|
  fprop := PropS;
  fev := unit;
  fent := fun φ _ ψ => φ -> ψ;
  e_id := tt; e_comp := fun _ _ => tt;
  ftop := True; e_top := tt;
  fand := and; e_fst := tt; e_snd := tt; e_pair := fun _ _ => tt;
  fuimp := fun A S => A -> forall ψ : Prop, S ψ -> ψ; e_lam := fun _ => tt; e_ev := tt
|}.
Solve All Obligations with (cbn in *; firstorder).

Lemma prop_fixpoint : fixpoint_comb prop_frame (fun _ => tt).
Proof. intros f φ ψ H. exact H. Qed.
