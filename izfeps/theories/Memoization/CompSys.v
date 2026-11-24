(** * Computational systems (Cohen–Miquey–Tate, Definition IV.1) and
    their demonic evidenced frame (Definition IV.3)

    A computational system has codes, states with a "possible future"
    preorder, a reduction c_f · c_a ↓σ→σ' c_r, a termination predicate
    c_f · c_a ↓σ, and functional completeness through codes λₙ.e. The set
    Σ of states is given by a predicate [ok] on a type of raw states (this
    avoids comparing proofs). The separator is the set of all codes
    (progress for all codes).

    The demonic frame: Φ = predicates σ, c ↦ φ^σ(c) stable under the
    future; e ⊩ φ ⩽ ψ ⟺ ∀σ ∈ Σ, ∀c, φ^σ(c) ⇒ e·c ⊩^σ_D ψ, where
    e·c ⊩^σ_D ψ says that e·c terminates at σ and every reduct c' (in a
    future σ') satisfies ψ^σ'(c'). Conjunction and universal implication
    are those of the paper (with the selectors λ₁.0 and λ₁.1). *)

From Stdlib Require Import Setoid Morphisms.
From IZFe Require Import Frame.

(** ** Expressions *)

Inductive gex (C : Type) : Type := gv (n : nat) | gc (c : C) | ga (f a : gex C).
Arguments gv {C} n. Arguments gc {C} c. Arguments ga {C} f a.

(** e[a]: variable 0 receives a, the others are shifted down. *)
Fixpoint subst0 {C} (e : gex C) (a : C) : gex C :=
  match e with
  | gv 0 => gc a
  | gv (S n) => gv n
  | gc c => gc c
  | ga f b => ga (subst0 f a) (subst0 b a)
  end.

Section Exprs.
Context {C S : Type} (red : C -> C -> S -> S -> C -> Prop) (term : C -> C -> S -> Prop).

Fixpoint ered (e : gex C) (σ σ' : S) (r : C) : Prop :=
  match e with
  | gv _ => False
  | gc c => r = c /\ σ' = σ
  | ga f a => exists σ1 cf σ2 ca, ered f σ σ1 cf /\ ered a σ1 σ2 ca /\ red cf ca σ2 σ' r
  end.

Fixpoint eterm (e : gex C) (σ : S) : Prop :=
  match e with
  | gv _ => False
  | gc _ => True
  | ga f a => eterm f σ /\ forall σ1 cf, ered f σ σ1 cf ->
      eterm a σ1 /\ forall σ2 ca, ered a σ1 σ2 ca -> term cf ca σ2
  end.
End Exprs.

(** ** The computational system *)

Record cs := {
  cd : Type;
  st : Type;
  ok : st -> Prop;
  st0 : st; ok0 : ok st0;
  fut : st -> st -> Prop;
  fut_refl : forall σ, fut σ σ;
  fut_trans : forall σ1 σ2 σ3, fut σ1 σ2 -> fut σ2 σ3 -> fut σ1 σ3;
  red : cd -> cd -> st -> st -> cd -> Prop;
  term : cd -> cd -> st -> Prop;
  red_fut : forall f a σ σ' r, red f a σ σ' r -> fut σ σ';
  red_ok : forall f a σ σ' r, ok σ -> red f a σ σ' r -> ok σ';
  progress : forall f a σ, ok σ -> term f a σ -> exists σ' r, red f a σ σ' r;
  lam : nat -> gex cd -> cd;
  lamS_red : forall n e a σ σ' r, red (lam (S n) e) a σ σ' r -> σ' = σ /\ r = lam n (subst0 e a);
  lamS_term : forall n e a σ, term (lam (S n) e) a σ;
  lam0_red : forall e a σ σ' r, red (lam 0 e) a σ σ' r -> ered red (subst0 e a) σ σ' r;
  lam0_term : forall e a σ, eterm red term (subst0 e a) σ -> term (lam 0 e) a σ
}.

Arguments red {c} _ _ _ _ _. Arguments term {c} _ _ _. Arguments fut {c} _ _. Arguments ok {c} _.
Arguments lam {c} _ _.

Section CSFrame.

Context (C : cs).
Local Abbreviation code := (cd C).
Local Abbreviation ex := (gex code).

(** ** Weakest precondition *)

(** f·a ⊩^σ_D Q: f·a terminates at σ and all its reducts satisfy Q. *)
Definition wpa (f a : code) (σ : st C) (Q : st C -> code -> Prop) : Prop :=
  term f a σ /\ forall σ' r, red f a σ σ' r -> Q σ' r.

Definition wp (e : ex) (σ : st C) (Q : st C -> code -> Prop) : Prop :=
  eterm (@red C) (@term C) e σ /\ forall σ' r, ered (@red C) e σ σ' r -> Q σ' r.

Lemma wp_c c σ (Q : st C -> code -> Prop) : Q σ c -> wp (gc c) σ Q.
Proof. intros H. split; [exact I|]. intros σ' r [-> ->]. exact H. Qed.

Lemma wp_a f a σ (Q : st C -> code -> Prop) :
  wp f σ (fun σ1 cf => wp a σ1 (fun σ2 ca => wpa cf ca σ2 Q)) -> wp (ga f a) σ Q.
Proof.
  intros [Hf Kf]. split.
  - split; [exact Hf|]. intros σ1 cf H1. destruct (Kf _ _ H1) as [Ha Ka]. split; [exact Ha|].
    intros σ2 ca H2. exact (proj1 (Ka _ _ H2)).
  - intros σ' r (σ1 & cf & σ2 & ca & H1 & H2 & H3). exact (proj2 (proj2 (Kf _ _ H1) _ _ H2) _ _ H3).
Qed.

Lemma wpa_lam0 e a σ Q : wp (subst0 e a) σ Q -> wpa (lam 0 e) a σ Q.
Proof. intros [H K]. split; [apply lam0_term, H|]. intros σ' r Hr. apply K, lam0_red, Hr. Qed.

Lemma wpa_lamS n e a σ (Q : st C -> code -> Prop) : Q σ (lam n (subst0 e a)) -> wpa (lam (S n) e) a σ Q.
Proof. intros H. split; [apply lamS_term|]. intros σ' r Hr. destruct (lamS_red _ _ _ _ _ _ _ Hr) as [-> ->]. exact H. Qed.

Lemma wpa_mono f a σ (Q Q' : st C -> code -> Prop) : (forall σ' r, Q σ' r -> Q' σ' r) -> wpa f a σ Q -> wpa f a σ Q'.
Proof. intros H [T K]. split; [exact T|]. intros; apply H, K; assumption. Qed.

Lemma wp_mono e σ (Q Q' : st C -> code -> Prop) : (forall σ' r, Q σ' r -> Q' σ' r) -> wp e σ Q -> wp e σ Q'.
Proof. intros H [T K]. split; [exact T|]. intros; apply H, K; assumption. Qed.

Lemma ered_okfut e σ σ' r : ok σ -> ered (@red C) e σ σ' r -> ok σ' /\ fut σ σ'.
Proof.
  revert σ σ' r. induction e as [n|c|f IHf a IHa]; intros σ σ' r Ok H; cbn in H.
  - destruct H.
  - destruct H as [-> ->]. split; [exact Ok|apply fut_refl].
  - destruct H as (σ1 & cf & σ2 & ca & H1 & H2 & H3).
    destruct (IHf _ _ _ Ok H1) as [O1 F1]. destruct (IHa _ _ _ O1 H2) as [O2 F2].
    split; [eapply red_ok; eassumption|]. eapply fut_trans; [eapply fut_trans; eassumption|eapply red_fut; eassumption].
Qed.

(** The reducts may be assumed to be in Σ and in the future. *)
Lemma wpa_okfut f a σ (Q : st C -> code -> Prop) :
  ok σ -> wpa f a σ (fun σ' r => ok σ' -> fut σ σ' -> Q σ' r) -> wpa f a σ Q.
Proof.
  intros Ok [T K]. split; [exact T|]. intros σ' r H. apply K; [exact H|eapply red_ok; eassumption|eapply red_fut; eassumption].
Qed.

Lemma wp_okfut e σ (Q : st C -> code -> Prop) :
  ok σ -> wp e σ (fun σ' r => ok σ' -> fut σ σ' -> Q σ' r) -> wp e σ Q.
Proof.
  intros Ok [T K]. split; [exact T|]. intros σ' r H. destruct (ered_okfut _ _ _ _ Ok H). apply K; assumption.
Qed.

(** ** Stable propositions *)

Record sprop := {
  sp :> st C -> code -> Prop;
  sp_stable : forall σ σ' c, fut σ σ' -> sp σ c -> sp σ' c
}.

Definition SP : pset.
Proof.
  refine {| pcar := sprop; peq := fun φ ψ => forall σ c, φ σ c <-> ψ σ c |}.
  - intros φ σ c. reflexivity.
  - intros φ ψ H σ c. symmetry. apply H.
  - intros φ ψ χ H1 H2 σ c. etransitivity; [apply H1|apply H2].
Defined.

Definition sent (φ : SP) (e : code) (ψ : SP) : Prop := forall σ c, ok σ -> φ σ c -> wpa e c σ ψ.

(** The selectors, and the pair ⟨x, y⟩ ≜ λf. f x y. *)
Definition cK : code := lam 1 (gv 0).
Definition cKI : code := lam 1 (gv 1).
Definition pairv (x y : code) : code := lam 0 (ga (ga (gv 0) (gc x)) (gc y)).
Definition cPAIR : code := lam 2 (ga (ga (gv 2) (gv 0)) (gv 1)).

Definition stop : sprop := {| sp := fun _ _ => True; sp_stable := fun _ _ _ _ H => H |}.

Definition sand (φ ψ : sprop) : sprop.
Proof.
  refine {| sp := fun σ c => forall σ', fut σ σ' -> ok σ' -> wpa c cK σ' φ /\ wpa c cKI σ' ψ |}.
  intros σ1 σ2 x H12 H σ' H2 Ok. apply H; [eapply fut_trans; eassumption|exact Ok].
Defined.

Definition suimp (φ : sprop) (S : sprop -> Prop) : sprop.
Proof.
  refine {| sp := fun σ c => forall σ', fut σ σ' -> ok σ' -> forall c1, φ σ' c1 -> forall ψ : sprop, S ψ -> wpa c c1 σ' ψ |}.
  intros σ1 σ2 x H12 H σ' H2 Ok. apply H; [eapply fut_trans; eassumption|exact Ok].
Defined.

Lemma pairv_K x y σ (Q : st C -> code -> Prop) : Q σ x -> wpa (pairv x y) cK σ Q.
Proof.
  intros H. apply wpa_lam0. cbn. apply wp_a, wp_a, wp_c. apply wp_c. apply wpa_lamS. cbn.
  apply wp_c. apply wpa_lam0. cbn. apply wp_c, H.
Qed.

Lemma pairv_KI x y σ (Q : st C -> code -> Prop) : Q σ y -> wpa (pairv x y) cKI σ Q.
Proof.
  intros H. apply wpa_lam0. cbn. apply wp_a, wp_a, wp_c. apply wp_c. apply wpa_lamS. cbn.
  apply wp_c. apply wpa_lam0. cbn. apply wp_c, H.
Qed.

Lemma pairv_and (φ ψ : sprop) σ x y : φ σ x -> ψ σ y -> sand φ ψ σ (pairv x y).
Proof.
  intros H1 H2 σ' Hf _. split; [apply pairv_K|apply pairv_KI]; eapply sp_stable; eassumption.
Qed.

Lemma cPAIR_spec x y σ (Q : st C -> code -> Prop) :
  Q σ (pairv x y) -> wp (ga (ga (gc cPAIR) (gc x)) (gc y)) σ Q.
Proof. intros H. apply wp_a, wp_a, wp_c, wp_c. apply wpa_lamS. cbn. apply wp_c. apply wpa_lamS. cbn. exact H. Qed.

(** ** The evidences *)

Definition cid : code := lam 0 (gv 0).
Definition ccomp (e1 e2 : code) : code := lam 0 (ga (gc e2) (ga (gc e1) (gv 0))).
Definition cpair (e1 e2 : code) : code := lam 0 (ga (ga (gc cPAIR) (ga (gc e1) (gv 0))) (ga (gc e2) (gv 0))).
Definition cfst : code := lam 0 (ga (gv 0) (gc cK)).
Definition csnd : code := lam 0 (ga (gv 0) (gc cKI)).
Definition clam (e : code) : code := lam 1 (ga (gc e) (ga (ga (gc cPAIR) (gv 0)) (gv 1))).
Definition cev : code := lam 0 (ga (ga (gv 0) (gc cKI)) (ga (gv 0) (gc cK))).

Lemma wpa_id c σ (Q : st C -> code -> Prop) : Q σ c -> wpa cid c σ Q.
Proof. intros H. apply wpa_lam0, wp_c, H. Qed.

Lemma wpa_comp e1 e2 c σ (Q : st C -> code -> Prop) :
  wpa e1 c σ (fun σ1 x => wpa e2 x σ1 Q) -> wpa (ccomp e1 e2) c σ Q.
Proof.
  intros [T K]. apply wpa_lam0. cbn. apply wp_a, wp_c, wp_a, wp_c, wp_c. split; [exact T|exact K].
Qed.

Ltac wps := repeat (cbn [subst0]; first [apply wp_a | apply wp_c | apply wpa_lamS | apply wpa_lam0]).

Definition cs_frame : frame.
Proof.
  refine {| fprop := SP; fev := code; fent := sent;
            e_id := cid; e_comp := ccomp; ftop := stop; e_top := cid;
            fand := sand; e_pair := cpair; e_fst := cfst; e_snd := csnd;
            fuimp := suimp; e_lam := clam; e_ev := cev |}.
  - intros φ φ' e ψ ψ' H1 H2 H σ c Ok Hc. apply H1 in Hc. eapply wpa_mono; [|apply H; assumption].
    intros; apply H2; assumption.
  - intros φ σ c _ H. apply wpa_id, H.
  - intros φ ψ χ e1 e2 H1 H2 σ c Ok H. apply wpa_comp. apply wpa_okfut; [exact Ok|].
    eapply wpa_mono; [|apply H1; assumption]. intros σ1 x Hx O1 _. apply H2; assumption.
  - intros φ σ c _ _. apply wpa_id. exact I.
  - intros φ φ' ψ ψ' H1 H2 σ c. cbn. split; intros H σ' F O; destruct (H σ' F O) as [A B];
      (split; [eapply wpa_mono; [|exact A]|eapply wpa_mono; [|exact B]]); intros; first [apply H1 | apply H2]; assumption.
  - intros φ ψ1 ψ2 e1 e2 H1 H2 σ c Ok H. unfold cpair. wps.
    apply wpa_okfut; [exact Ok|]. eapply wpa_mono; [|apply H1; assumption]. intros σ1 x Hx O1 F1. wps.
    apply wpa_okfut; [exact O1|]. eapply wpa_mono; [|apply H2; [exact O1|eapply sp_stable; eassumption]].
    intros σ2 y Hy O2 F2. wps. apply pairv_and; [eapply sp_stable; eassumption|exact Hy].
  - intros φ ψ σ p Ok H. unfold cfst. wps. exact (proj1 (H σ (fut_refl _ _) Ok)).
  - intros φ ψ σ p Ok H. unfold csnd. wps. exact (proj2 (H σ (fut_refl _ _) Ok)).
  - intros φ φ' S T H1 H2 σ c. cbn. split; intros H σ' F O c1 Hc1 ψ Hψ; apply H; auto; first [apply H1 | apply H2]; assumption.
  - intros φ1 φ2 S e H σ c Ok Hc. unfold clam. apply wpa_lamS. cbn [subst0].
    intros σ' F O c1 Hc1 ψ Hψ. wps. cbn [subst0]. apply (H ψ Hψ σ' (pairv c c1) O).
    apply pairv_and; [eapply sp_stable; eassumption|exact Hc1].
  - intros φ S ψ Hψ σ p Ok H. unfold cev. wps.
    apply wpa_okfut; [exact Ok|]. eapply wpa_mono; [|exact (proj2 (H σ (fut_refl _ _) Ok))].
    intros σ1 f Hf O1 F1. wps. apply wpa_okfut; [exact O1|].
    eapply wpa_mono; [|exact (proj1 (H σ1 F1 O1))]. intros σ2 x Hx O2 F2. exact (Hf σ2 F2 O2 x Hx ψ Hψ).
Defined.

(** ** Union, meta-level propositions, semantic rules *)

Definition sex {I : Type} (f : I -> sprop) : sprop.
Proof.
  refine {| sp := fun σ c => exists i, f i σ c |}.
  intros σ σ' c F [i H]. exists i. eapply sp_stable; eassumption.
Defined.

Definition sbr (P : Prop) : sprop := {| sp := fun _ _ => P; sp_stable := fun _ _ _ _ H => H |}.

Definition mkprop (p : st C -> code -> Prop) (H : forall σ σ' c, fut σ σ' -> p σ c -> p σ' c) : sprop :=
  {| sp := p; sp_stable := H |}.

Lemma fall_I {I} (f : I -> SP) σ c :
  (forall σ', fut σ σ' -> ok σ' -> forall d i, wpa c d σ' (f i)) -> @fall cs_frame I f σ c.
Proof.
  intros H σ' F O d _ ψ [i E]. eapply wpa_mono; [|exact (H σ' F O d i)]. intros σ'' r K. apply E, K.
Qed.

Lemma fall_E {I} (f : I -> SP) σ c d i : ok σ -> @fall cs_frame I f σ c -> wpa c d σ (f i).
Proof. intros O H. apply (H σ (fut_refl _ _) O d Logic.I (f i)). exists i. intros; reflexivity. Qed.

Lemma fimp_I (φ ψ : SP) σ c :
  (forall σ', fut σ σ' -> ok σ' -> forall x, φ σ' x -> wpa c x σ' ψ) -> @fimp cs_frame φ ψ σ c.
Proof.
  intros H σ' F O x Hx χ E. eapply wpa_mono; [|exact (H σ' F O x Hx)]. intros σ'' r K. apply E, K.
Qed.

Lemma fimp_E (φ ψ : SP) σ c x : ok σ -> @fimp cs_frame φ ψ σ c -> φ σ x -> wpa c x σ ψ.
Proof. intros O H Hx. apply (H σ (fut_refl _ _) O x Hx ψ). intros; reflexivity. Qed.

Lemma realize (φ : SP) e : (forall σ c, ok σ -> wpa e c σ φ) -> @ftop cs_frame —[e]→ φ.
Proof. intros H σ c O _. apply H, O. Qed.

End CSFrame.
