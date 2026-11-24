(** * Evidenced frames from PCAs, and a PCA on ℕ

    A PCA is given by a partial application, presented as a functional
    relation [ap a b r] ("a·b ↓ = r"), and by k, s with their always
    defined partial applications k·a, s·a, s·a·b (functions K1, S1, S2).
    This is the usual presentation, made constructive: the values of
    abstractions are computed without ever evaluating an application that
    could diverge.

    The frame (Cohen–Miquey–Tate): Φ = P(A), e ⊩ φ ⩽ ψ ⟺ ∀a ∈ φ, e·a↓ ∈ ψ,
    φ ⊃ ⋂S ≜ {c | ∀a ∈ φ, ∀ψ ∈ S, c·a↓ ∈ ψ}. It is a frame in the sense of
    Definition 18 with the universal implication (for S = ∅, no definition
    of c·a is required). The fixed point combinator is Turing's:
    y(f) ≜ W·W with W ≜ λw. λt. f(w·w)·t.

    Instance: the PCA of the combinators S, K coded in ℕ (n·m defined by
    an interpreter), with its frame and its fixed point. *)

From Stdlib Require Import Arith Lia Cantor.
From IZFe Require Import Frame.

Record pca := {
  pc :> Type;
  ap : pc -> pc -> pc -> Prop;
  ap_fun : forall a b r r', ap a b r -> ap a b r' -> r = r';
  pk : pc; ps : pc;
  K1 : pc -> pc; S1 : pc -> pc; S2 : pc -> pc -> pc;
  ap_k : forall a, ap pk a (K1 a);
  ap_k1 : forall a b, ap (K1 a) b a;
  ap_s : forall a, ap ps a (S1 a);
  ap_s1 : forall a b, ap (S1 a) b (S2 a b);
  ap_s2 : forall a b c r, ap (S2 a b) c r <-> exists x y, ap a c x /\ ap b c y /\ ap x y r
}.

Arguments ap {p} _ _ _.
Arguments pk {p}. Arguments ps {p}.
Arguments K1 {p} _. Arguments S1 {p} _. Arguments S2 {p} _ _.

Section PCAFrame.

Context (P : pca).

(** ** Combinatory terms and combinatory completeness *)

Inductive tm := tv (n : nat) | tc (a : P) | ta (t u : tm).

Fixpoint close (σ : nat -> P) (t : tm) : tm :=
  match t with tv n => tc (σ n) | tc a => tc a | ta t u => ta (close σ t) (close σ u) end.

Inductive ev : tm -> P -> Prop :=
| ev_c a : ev (tc a) a
| ev_a t u x y r : ev t x -> ev u y -> ap x y r -> ev (ta t u) r.

Definition eI : P := S2 pk pk.

Lemma ap_I a : ap eI a a.
Proof. apply ap_s2. exists (K1 a), (K1 a). split; [apply ap_k|split; [apply ap_k|apply ap_k1]]. Qed.

Definition KI : P := K1 eI.

Ltac evs := repeat match goal with
  | |- ev (tc _) _ => apply ev_c
  | |- ev (ta _ _) _ => eapply ev_a
  | |- ap _ _ _ => first [eassumption | apply ap_k | apply ap_k1 | apply ap_s | apply ap_s1 | apply ap_I]
  end.

(** Abstraction of variable 0. *)
Fixpoint abs (t : tm) : tm :=
  match t with
  | tv 0 => tc eI
  | tv (S n) => ta (tc pk) (tv n)
  | tc a => ta (tc pk) (tc a)
  | ta t u => ta (ta (tc ps) (abs t)) (abs u)
  end.

(** The value of λx. t, under the valuation σ of the other variables. *)
Fixpoint absv (σ : nat -> P) (t : tm) : P :=
  match t with
  | tv 0 => eI
  | tv (S n) => K1 (σ n)
  | tc a => K1 a
  | ta t u => S2 (absv σ t) (absv σ u)
  end.

Definition cons (a : P) (σ : nat -> P) : nat -> P := fun n => match n with 0 => a | S m => σ m end.

Lemma ev_abs σ t : ev (close σ (abs t)) (absv σ t).
Proof.
  induction t as [[|n]|a|t IHt u IHu]; cbn.
  - constructor.
  - econstructor; [constructor|constructor|apply ap_k].
  - econstructor; [constructor|constructor|apply ap_k].
  - econstructor; [econstructor; [constructor|exact IHt|apply ap_s]|exact IHu|apply ap_s1].
Qed.

(** β: (λx. t)·a ≃ t[a/x] (in the direction that is needed). *)
Lemma ap_absv σ t a r : ev (close (cons a σ) t) r -> ap (absv σ t) a r.
Proof.
  revert r. induction t as [[|n]|c|t IHt u IHu]; intros r H; cbn in *.
  - inversion H; subst. apply ap_I.
  - inversion H; subst. apply ap_k1.
  - inversion H; subst. apply ap_k1.
  - inversion H; subst. apply ap_s2. exists x, y. auto.
Qed.

Lemma ap_absv_abs σ t a : ap (absv σ (abs t)) a (absv (cons a σ) t).
Proof. apply ap_absv, ev_abs. Qed.

Definition σ0 : nat -> P := fun _ => pk.

(** ** The evidences *)

(** e₁ ; e₂ ≜ λx. e₂ (e₁ x) *)
Definition Bcomp : tm := ta (tv 1) (ta (tv 2) (tv 0)).
Definition e_compP (e1 e2 : P) : P := absv (cons e2 (cons e1 σ0)) Bcomp.
Definition COMP : P := absv σ0 (abs (abs Bcomp)).

Lemma comp_fwd e1 e2 a x r : ap e1 a x -> ap e2 x r -> ap (e_compP e1 e2) a r.
Proof. intros H1 H2. apply ap_absv. cbn. evs. Qed.

Lemma COMP_spec e1 e2 : exists c, ap COMP e1 c /\ ap c e2 (e_compP e1 e2).
Proof. eexists. split; [apply ap_absv_abs|apply ap_absv_abs]. Qed.

(** ⟨e₁, e₂⟩ ≜ λx. λf. f (e₁ x) (e₂ x) *)
Definition Bpair : tm := abs (ta (ta (tv 0) (ta (tv 3) (tv 1))) (ta (tv 2) (tv 1))).
Definition e_pairP (e1 e2 : P) : P := absv (cons e2 (cons e1 σ0)) Bpair.
Definition PAIR : P := absv σ0 (abs (abs Bpair)).

Lemma pair_fwd e1 e2 a r1 r2 : ap e1 a r1 -> ap e2 a r2 ->
  exists p, ap (e_pairP e1 e2) a p /\ ap p pk r1 /\ ap p KI r2.
Proof.
  intros H1 H2. eexists. split; [apply ap_absv_abs|]. split; apply ap_absv; cbn; evs.
Qed.

Lemma PAIR_spec e1 e2 : exists c, ap PAIR e1 c /\ ap c e2 (e_pairP e1 e2).
Proof. eexists. split; [apply ap_absv_abs|apply ap_absv_abs]. Qed.

(** λ(e) ≜ λx. λy. e (λf. f x y) *)
Definition Blam : tm := abs (ta (tv 2) (abs (ta (ta (tv 0) (tv 2)) (tv 1)))).
Definition e_lamP (e : P) : P := absv (cons e σ0) Blam.
Definition LAM : P := absv σ0 (abs Blam).

Lemma lam_fwd e a : exists V, ap (e_lamP e) a V /\
  forall b, exists p, ap p pk a /\ ap p KI b /\ forall r, ap e p r -> ap V b r.
Proof.
  eexists. split; [apply ap_absv_abs|]. intros b.
  exists (absv (cons b (cons a (cons e σ0))) (ta (ta (tv 0) (tv 2)) (tv 1))).
  split; [|split]; [apply ap_absv; cbn; evs|apply ap_absv; cbn; evs|].
  intros r H. apply ap_absv. cbn [close]. eapply ev_a; [apply ev_c|apply ev_abs|exact H].
Qed.

Lemma LAM_spec e : ap LAM e (e_lamP e).
Proof. apply ap_absv_abs. Qed.

Definition e_fstP : P := absv σ0 (ta (tv 0) (tc pk)).
Definition e_sndP : P := absv σ0 (ta (tv 0) (tc KI)).
Definition e_evP : P := absv σ0 (ta (ta (tv 0) (tc KI)) (ta (tv 0) (tc pk))).

Lemma fst_fwd p r : ap p pk r -> ap e_fstP p r.
Proof. intros H. apply ap_absv. cbn. evs. Qed.
Lemma snd_fwd p r : ap p KI r -> ap e_sndP p r.
Proof. intros H. apply ap_absv. cbn. evs. Qed.
Lemma ev_fwd p f x r : ap p KI f -> ap p pk x -> ap f x r -> ap e_evP p r.
Proof. intros H1 H2 H3. apply ap_absv. cbn. evs. Qed.

(** ** The frame *)

Program Definition PredS : pset := {| pcar := P -> Prop; peq := fun φ ψ => forall a, φ a <-> ψ a |}.
Solve All Obligations with (cbn; firstorder).

Definition pent (φ : PredS) (e : P) (ψ : PredS) : Prop := forall a, φ a -> exists r, ap e a r /\ ψ r.
Definition pand (φ ψ : PredS) : PredS := fun p => (exists r, ap p pk r /\ φ r) /\ (exists r, ap p KI r /\ ψ r).
Definition puimp (φ : PredS) (S : PredS -> Prop) : PredS :=
  fun c => forall a, φ a -> forall ψ : PredS, S ψ -> exists r, ap c a r /\ ψ r.

Definition pca_frame : frame.
Proof.
  refine {| fprop := PredS; fev := P; fent := pent;
            e_id := eI; e_comp := e_compP; ftop := (fun _ => True) : PredS; e_top := eI;
            fand := pand; e_pair := e_pairP; e_fst := e_fstP; e_snd := e_sndP;
            fuimp := puimp; e_lam := e_lamP; e_ev := e_evP |}.
  - intros φ φ' e ψ ψ' H1 H2 H a Ha. apply H1 in Ha. destruct (H a Ha) as (r & Hr & Hψ). exists r. split; [exact Hr|apply H2, Hψ].
  - intros φ a Ha. exists a. split; [apply ap_I|exact Ha].
  - intros φ ψ χ e1 e2 H1 H2 a Ha. destruct (H1 a Ha) as (x & Hx & Hψ). destruct (H2 x Hψ) as (r & Hr & Hχ).
    exists r. split; [eapply comp_fwd; eassumption|exact Hχ].
  - intros φ a _. exists a. split; [apply ap_I|exact I].
  - intros φ φ' ψ ψ' H1 H2 p. unfold pand. split; intros [(r & Hr & H) (r' & Hr' & H')];
      (split; [exists r; split; [exact Hr|apply H1, H]|exists r'; split; [exact Hr'|apply H2, H']]).
  - intros φ ψ χ e1 e2 H1 H2 a Ha. destruct (H1 a Ha) as (r1 & Hr1 & Hψ), (H2 a Ha) as (r2 & Hr2 & Hχ).
    destruct (pair_fwd e1 e2 a r1 r2 Hr1 Hr2) as (p & Hp & Hp1 & Hp2).
    exists p. split; [exact Hp|split; [exists r1|exists r2]; auto].
  - intros φ ψ p [(r & Hr & H) _]. exists r. split; [apply fst_fwd, Hr|exact H].
  - intros φ ψ p [_ (r & Hr & H)]. exists r. split; [apply snd_fwd, Hr|exact H].
  - intros φ φ' S T H1 H2 c. unfold puimp. split; intros H a Ha ψ Hψ.
    + apply H; [apply H1, Ha|apply H2, Hψ].
    + apply H; [apply H1, Ha|apply H2, Hψ].
  - intros φ1 φ2 S e H a Ha. destruct (lam_fwd e a) as (V & HV & HV').
    exists V. split; [exact HV|]. intros b Hb ψ Hψ. destruct (HV' b) as (p & Hp1 & Hp2 & Hp).
    destruct (H ψ Hψ p) as (r & Hr & Hr'); [split; [exists a|exists b]; auto|].
    exists r. split; [apply Hp, Hr|exact Hr'].
  - intros φ S ψ Hψ p [(x & Hx & Hφ) (f & Hf & Hc)]. destruct (Hc x Hφ ψ Hψ) as (r & Hr & H).
    exists r. split; [eapply ev_fwd; eassumption|exact H].
Defined.

(** The frame is consistent: ⊥ is not realized. *)
Lemma pca_consistent : ~ exists e, @ftop pca_frame —[e]→ fbot.
Proof.
  intros [e H]. destruct (H pk I) as (r & _ & Hr).
  destruct (Hr pk I (fun _ => False)) as (r' & _ & []).
  exists (fun _ => False). intros a. reflexivity.
Qed.

(** ** Turing's fixed point combinator *)

(** The term computing f(u), for an expression f of the operad. *)
Fixpoint codeT (u : tm) (f : eexp) : tm :=
  match f with
  | x_var => u
  | x_comp a b => ta (ta (tc COMP) (codeT u a)) (codeT u b)
  | x_pair a b => ta (ta (tc PAIR) (codeT u a)) (codeT u b)
  | x_lam a => ta (tc LAM) (codeT u a)
  | c => tc (eeval pca_frame pk c)
  end.

Lemma close_codeT ρ u f : close ρ (codeT u f) = codeT (close ρ u) f.
Proof. induction f; cbn; congruence. Qed.

Lemma codeT_ev u v f : ev u v -> ev (codeT u f) (eeval pca_frame v f).
Proof.
  intros Hu. induction f; cbn; try apply ev_c; try exact Hu.
  - destruct (COMP_spec (eeval pca_frame v f1) (eeval pca_frame v f2)) as (c & H1 & H2).
    eapply ev_a; [eapply ev_a; [apply ev_c|exact IHf1|exact H1]|exact IHf2|exact H2].
  - destruct (PAIR_spec (eeval pca_frame v f1) (eeval pca_frame v f2)) as (c & H1 & H2).
    eapply ev_a; [eapply ev_a; [apply ev_c|exact IHf1|exact H1]|exact IHf2|exact H2].
  - eapply ev_a; [apply ev_c|exact IHf|apply LAM_spec].
Qed.

Definition Bw (f : eexp) : tm := ta (codeT (ta (tv 1) (tv 1)) f) (tv 0).
Definition Wc (f : eexp) : P := absv σ0 (abs (Bw f)).
Definition pca_fix (f : eexp) : P := absv (cons (Wc f) σ0) (Bw f).

Lemma pca_fix_unfold f : ap (Wc f) (Wc f) (pca_fix f).
Proof. apply ap_absv_abs. Qed.

Lemma pca_fix_step f a r : ap (eeval pca_frame (pca_fix f) f) a r -> ap (pca_fix f) a r.
Proof.
  intros H. apply ap_absv. unfold Bw. cbn [close]. rewrite close_codeT.
  eapply ev_a; [|apply ev_c|exact H]. apply codeT_ev. cbn. eapply ev_a; [apply ev_c|apply ev_c|apply pca_fix_unfold].
Qed.

Theorem pca_fixpoint : fixpoint_comb pca_frame pca_fix.
Proof.
  intros f φ ψ H a Ha. destruct (H a Ha) as (r & Hr & Hψ). exists r. split; [apply pca_fix_step, Hr|exact Hψ].
Qed.

End PCAFrame.

(** ** A PCA on ℕ: the coded combinators S, K

    n = 5q + t: t = 0 codes k, t = 1 codes s, t = 2 codes k·q, t = 3 codes
    s·q, t = 4 codes s·x·y with (x, y) = q decoded by the Cantor pairing.
    The application n·m is defined by an interpreter (an inductive
    relation), which may diverge (for instance ω·ω with ω = s·i·i). *)

Definition nK1 (a : nat) : nat := 5 * a + 2.
Definition nS1 (a : nat) : nat := 5 * a + 3.
Definition nS2 (a b : nat) : nat := 5 * Cantor.to_nat (a, b) + 4.

Inductive apN : nat -> nat -> nat -> Prop :=
| apN_k n a : n mod 5 = 0 -> apN n a (nK1 a)
| apN_k1 n b : n mod 5 = 2 -> apN n b (n / 5)
| apN_s n a : n mod 5 = 1 -> apN n a (nS1 a)
| apN_s1 n b : n mod 5 = 3 -> apN n b (nS2 (n / 5) b)
| apN_s2 n c x y u v r : n mod 5 = 4 -> Cantor.of_nat (n / 5) = (x, y) ->
    apN x c u -> apN y c v -> apN u v r -> apN n c r.

Lemma dec5 q r : r < 5 -> (5 * q + r) mod 5 = r /\ (5 * q + r) / 5 = q.
Proof.
  intros H. split.
  - symmetry. apply (Nat.mod_unique _ _ q); lia.
  - symmetry. apply (Nat.div_unique _ _ _ r); lia.
Qed.

Lemma apN_fun a b r r' : apN a b r -> apN a b r' -> r = r'.
Proof.
  intros H. revert r'. induction H; intros r' H'; inversion H'; subst; try congruence.
  match goal with E1 : Cantor.of_nat ?q = (?x, ?y), E2 : Cantor.of_nat ?q = (?x', ?y') |- _ =>
    rewrite E1 in E2; injection E2 as <- <- end.
  match goal with K1 : apN x c ?u', K2 : apN y c ?v', K3 : apN ?u' ?v' r' |- _ =>
    apply IHapN1 in K1; apply IHapN2 in K2; subst; apply IHapN3, K3 end.
Qed.

Definition natPCA : pca.
Proof.
  refine {| pc := nat; ap := apN; ap_fun := apN_fun; pk := 0; ps := 1; K1 := nK1; S1 := nS1; S2 := nS2 |}.
  - intros a. apply apN_k. reflexivity.
  - intros a b. destruct (dec5 a 2 ltac:(lia)) as [H1 H2]. unfold nK1. rewrite <- H2 at 2. apply apN_k1, H1.
  - intros a. apply apN_s. reflexivity.
  - intros a b. destruct (dec5 a 3 ltac:(lia)) as [H1 H2]. unfold nS1. rewrite <- H2 at 2. apply apN_s1, H1.
  - intros a b c r. destruct (dec5 (Cantor.to_nat (a, b)) 4 ltac:(lia)) as [H1 H2]. unfold nS2. split.
    + intros H. inversion H; subst; try (rewrite H1 in H0; discriminate).
      rewrite H2, Cantor.cancel_of_to in H3. injection H3 as -> ->. eauto.
    + intros (u & v & Hu & Hv & H). eapply apN_s2; [exact H1|rewrite H2; apply Cantor.cancel_of_to|exact Hu|exact Hv|exact H].
Defined.

Definition nat_frame : frame := pca_frame natPCA.

Theorem nat_fixpoint : fixpoint_comb nat_frame (pca_fix natPCA).
Proof. apply pca_fixpoint. Qed.

Lemma nat_consistent : ~ exists e, @ftop nat_frame —[e]→ fbot.
Proof. apply pca_consistent. Qed.
