(** * Monadic combinatory algebras (Cohen–Grunfeld–Kirst–Miquey) as
    instances of the construction

    A monadic combinatory algebra (MCA) is a set A of codes with a monad M
    and a Kleisli application (−)·(−) : A × A → M A, together with codes
    λⁿ.e for the expressions e with n+1 free variables (Definitions 3–5 of
    "From partial to monadic: combinatory algebra with effects"):
      λⁿ⁺¹.e · c = η(λⁿ.e[c])        λ⁰.e · c = ν(e[c])
    where ν evaluates a closed expression in call-by-value (Definition 4).
    An M-modality ♢ : M X → (X → Ω) → Ω satisfying After-Return,
    After-Bind and monotonicity turns an MCA into an evidenced frame
    (Definition 13, Theorem 16): propositions are predicates φ : A → Ω and
    e ⊩ φ ⩽ ψ ⟺ ∀c, φ(c) ⩽ ♢(e·c)(ψ).

    Formalisation choices:
    - Ω = Prop (the truth values of the meta-theory);
    - the abstraction laws are only required through the modality
      (♢(λⁿ⁺¹.e · c) = ♢(η(λⁿ.e[c])) and ♢(λ⁰.e · c) = ♢(ν(e[c]))), which is
      all the frame uses; the monad laws are not needed;
    - the separator is the set of all codes (as for computational systems,
      Memoization/CompSys.v); consistency is proven for instances.

    We build the evidenced frame (with the universal implication of
    Definition 18), a fixed point combinator in the sense of Definition 21
    (a guarded Turing combinator: y(f) ≜ W·W with W ≜ λw. λt. f(w·w)·t,
    where W·W is pure thanks to the abstraction laws), and deduce
    Theorem 26 for the model V(E) of any MCA. *)

From Stdlib Require Import Setoid Morphisms.
From IZFe Require Import Frame.

(** ** Expressions with free variables *)

Inductive xp (C : Type) : Type := xv (n : nat) | xc (c : C) | xa (f a : xp C).
Arguments xv {C} n. Arguments xc {C} c. Arguments xa {C} f a.

(** e[c]: variable 0 receives c, the others are shifted down. *)
Fixpoint xsub0 {C} (e : xp C) (c : C) : xp C :=
  match e with
  | xv 0 => xc c
  | xv (S n) => xv n
  | xc d => xc d
  | xa f a => xa (xsub0 f c) (xsub0 a c)
  end.

(** ν: call-by-value evaluation of an expression (Definition 4); free
    variables, which never occur in closed expressions, evaluate to a
    default code d. *)
Fixpoint xeval {C} {M : Type -> Type} (ret : C -> M C) (bind : M C -> (C -> M C) -> M C)
    (app : C -> C -> M C) (d : C) (e : xp C) : M C :=
  match e with
  | xv _ => ret d
  | xc c => ret c
  | xa f a => bind (xeval ret bind app d f) (fun cf => bind (xeval ret bind app d a) (fun ca => app cf ca))
  end.

(** ** Monadic combinatory algebras with a modality *)

Record mca := {
  mc : Type;
  M : Type -> Type;
  ret : forall X, X -> M X;
  bind : forall X Y, M X -> (X -> M Y) -> M Y;
  app : mc -> mc -> M mc;
  mlam : nat -> xp mc -> mc;
  dia : forall X, M X -> (X -> Prop) -> Prop;
  dia_ret : forall X (x : X) Q, dia X (ret X x) Q <-> Q x;
  dia_bind : forall X Y (m : M X) (f : X -> M Y) Q, dia Y (bind X Y m f) Q <-> dia X m (fun x => dia Y (f x) Q);
  dia_mono : forall X (m : M X) (Q Q' : X -> Prop), (forall x, Q x -> Q' x) -> dia X m Q -> dia X m Q';
  lamS_law : forall n e c Q, dia mc (app (mlam (S n) e) c) Q <-> dia mc (ret mc (mlam n (xsub0 e c))) Q;
  lam0_law : forall e c Q, dia mc (app (mlam 0 e) c) Q <->
    dia mc (xeval (ret mc) (bind mc mc) app (mlam 0 (xv 0)) (xsub0 e c)) Q
}.

Arguments ret {_ X} _. Arguments bind {_ X Y} _ _. Arguments app {_} _ _.
Arguments mlam {_} _ _. Arguments dia {_ X} _ _.

Section MCAFrame.

Context (A : mca).
Local Notation code := (mc A).

(** f·a ⊩ Q, through the modality. *)
Local Notation W f a Q := (dia (app f a) Q).

(** ** Weakest precondition of an expression *)

Fixpoint wpe (e : xp code) (Q : code -> Prop) : Prop :=
  match e with
  | xv _ => False
  | xc c => Q c
  | xa f a => wpe f (fun cf => wpe a (fun ca => W cf ca Q))
  end.

Lemma wpe_mono e (Q Q' : code -> Prop) : (forall c, Q c -> Q' c) -> wpe e Q -> wpe e Q'.
Proof.
  revert Q Q'. induction e as [n|c|f IHf a IHa]; intros Q Q' H; cbn; auto.
  apply IHf. intros cf. apply IHa. intros ca. apply dia_mono, H.
Qed.

Lemma wpe_eval d e Q : wpe e Q -> dia (xeval (@ret A code) (@bind A code code) app d e) Q.
Proof.
  revert Q. induction e as [n|c|f IHf a IHa]; intros Q H; cbn in *.
  - destruct H.
  - apply dia_ret, H.
  - apply dia_bind. eapply dia_mono; [|apply IHf, H]. intros cf Hcf. cbn.
    apply dia_bind. eapply dia_mono; [|apply IHa, Hcf]. intros ca Hca. exact Hca.
Qed.

Lemma W_lam0 e c Q : wpe (xsub0 e c) Q -> W (mlam 0 e) c Q.
Proof. intros H. apply lam0_law, wpe_eval, H. Qed.

Lemma W_lamS n e c (Q : code -> Prop) : Q (mlam n (xsub0 e c)) -> W (mlam (S n) e) c Q.
Proof. intros H. apply lamS_law, dia_ret, H. Qed.

Ltac wps := repeat (cbn [xsub0 wpe]; first [apply W_lamS | apply W_lam0]).

(** ** Propositions, selectors and pairs *)

Program Definition MP : pset := {| pcar := code -> Prop; peq := fun φ ψ => forall c, φ c <-> ψ c |}.
Solve All Obligations with (cbn; firstorder).

Definition ment (φ : MP) (e : code) (ψ : MP) : Prop := forall c, φ c -> W e c ψ.

Definition cK : code := mlam 1 (xv 0).
Definition cKI : code := mlam 1 (xv 1).
Definition pairv (x y : code) : code := mlam 0 (xa (xa (xv 0) (xc x)) (xc y)).
Definition cPAIR : code := mlam 2 (xa (xa (xv 2) (xv 0)) (xv 1)).

Definition mand (φ ψ : MP) : MP := fun c => W c cK φ /\ W c cKI ψ.
Definition muimp (φ : MP) (S : MP -> Prop) : MP :=
  fun c => forall c1, φ c1 -> forall ψ : MP, S ψ -> W c c1 ψ.

Lemma pairv_and (φ ψ : MP) x y : φ x -> ψ y -> mand φ ψ (pairv x y).
Proof. intros H1 H2. split; unfold pairv, cK, cKI; wps; assumption. Qed.

(** ** The evidences *)

Definition cid : code := mlam 0 (xv 0).
Definition ccomp (e1 e2 : code) : code := mlam 0 (xa (xc e2) (xa (xc e1) (xv 0))).
Definition cpair (e1 e2 : code) : code := mlam 0 (xa (xa (xc cPAIR) (xa (xc e1) (xv 0))) (xa (xc e2) (xv 0))).
Definition cfst : code := mlam 0 (xa (xv 0) (xc cK)).
Definition csnd : code := mlam 0 (xa (xv 0) (xc cKI)).
Definition clam (e : code) : code := mlam 1 (xa (xc e) (xa (xa (xc cPAIR) (xv 0)) (xv 1))).
Definition cev : code := mlam 0 (xa (xa (xv 0) (xc cKI)) (xa (xv 0) (xc cK))).

Definition mca_frame : frame.
Proof.
  refine {| fprop := MP; fev := code; fent := ment;
            e_id := cid; e_comp := ccomp; ftop := (fun _ => True) : MP; e_top := cid;
            fand := mand; e_pair := cpair; e_fst := cfst; e_snd := csnd;
            fuimp := muimp; e_lam := clam; e_ev := cev |}.
  - intros φ φ' e ψ ψ' H1 H2 H c Hc. apply H1 in Hc. eapply dia_mono; [|apply H, Hc]. intros; apply H2; assumption.
  - intros φ c H. unfold cid. wps. exact H.
  - intros φ ψ χ e1 e2 H1 H2 c H. unfold ccomp. wps. eapply dia_mono; [|apply H1, H]. exact H2.
  - intros φ c _. unfold cid. wps. exact I.
  - intros φ φ' ψ ψ' H1 H2 c. cbn. unfold mand. split; intros [Ha Hb];
      (split; [eapply dia_mono; [|exact Ha]|eapply dia_mono; [|exact Hb]]); intros; first [apply H1 | apply H2]; assumption.
  - intros φ ψ1 ψ2 e1 e2 H1 H2 c H. unfold cpair. wps.
    eapply dia_mono; [|apply H1, H]. intros x Hx. cbn. unfold cPAIR. wps.
    eapply dia_mono; [|apply H2, H]. intros y Hy. wps. apply pairv_and; assumption.
  - intros φ ψ p [H _]. unfold cfst. wps. exact H.
  - intros φ ψ p [_ H]. unfold csnd. wps. exact H.
  - intros φ φ' S T H1 H2 c. cbn. unfold muimp. split; intros H c1 Hc1 ψ Hψ; apply H; first [apply H1 | apply H2]; assumption.
  - intros φ1 φ2 S e H c Hc. unfold clam. wps. intros c1 Hc1 ψ Hψ. wps. unfold cPAIR. wps.
    apply (H ψ Hψ). apply pairv_and; assumption.
  - intros φ S ψ Hψ p [Hx Hf]. unfold cev. wps.
    eapply dia_mono; [|exact Hf]. intros f Hf'. cbn.
    eapply dia_mono; [|exact Hx]. intros x Hx'. exact (Hf' x Hx' ψ Hψ).
Defined.

(** ** The fixed point combinator *)

(** Codes computing the operations of the frame on their arguments. *)
Definition COMP : code := mlam 2 (xa (xv 1) (xa (xv 0) (xv 2))).
Definition PAIRE : code := mlam 2 (xa (xa (xc cPAIR) (xa (xv 0) (xv 2))) (xa (xv 1) (xv 2))).
Definition LAM : code := mlam 2 (xa (xv 0) (xa (xa (xc cPAIR) (xv 1)) (xv 2))).

(** The expression computing f(u), for an expression f of the operad. *)
Fixpoint codeT (u : xp code) (f : eexp) : xp code :=
  match f with
  | x_var => u
  | x_comp a b => xa (xa (xc COMP) (codeT u a)) (codeT u b)
  | x_pair a b => xa (xa (xc PAIRE) (codeT u a)) (codeT u b)
  | x_lam a => xa (xc LAM) (codeT u a)
  | c => xc (eeval mca_frame cid c)
  end.

Lemma xsub0_codeT u f c : xsub0 (codeT u f) c = codeT (xsub0 u c) f.
Proof. induction f; cbn; congruence. Qed.

(** If u computes (purely) the value v, then codeT u f computes f(v). *)
Lemma codeT_spec u v f : (forall Q, Q v -> wpe u Q) -> forall Q, Q (eeval mca_frame v f) -> wpe (codeT u f) Q.
Proof.
  intros Hu. induction f; intros Q H; cbn [codeT wpe]; try exact H; try (apply Hu; exact H).
  - apply IHf1. unfold COMP. wps. apply IHf2. wps. exact H.
  - apply IHf1. unfold PAIRE. wps. apply IHf2. wps. exact H.
  - apply IHf. unfold LAM. wps. exact H.
Qed.

Definition Bw (f : eexp) : xp code := xa (codeT (xa (xv 0) (xv 0)) f) (xv 1).
Definition Wc (f : eexp) : code := mlam 1 (Bw f).
Definition mca_fix (f : eexp) : code := mlam 0 (xa (codeT (xa (xc (Wc f)) (xc (Wc f))) f) (xv 0)).

(** W·W is pure and returns y(f). *)
Lemma WW_pure f Q : Q (mca_fix f) -> W (Wc f) (Wc f) Q.
Proof. intros H. unfold Wc at 1. apply W_lamS. unfold Bw. cbn [xsub0]. rewrite xsub0_codeT. exact H. Qed.

Theorem mca_fixpoint : fixpoint_comb mca_frame mca_fix.
Proof.
  intros f φ ψ H c Hc. unfold mca_fix at 1. apply W_lam0. cbn [xsub0]. rewrite xsub0_codeT. cbn [xsub0 wpe].
  apply (codeT_spec _ (mca_fix f)); [|exact (H c Hc)].
  intros Q HQ. cbn [wpe]. apply WW_pure, HQ.
Qed.

(** ** Consistency

    ⊥ is not realized as soon as no computation is ♢-certain to produce a
    result satisfying the empty predicate (the progress condition of
    Definition 14 for all codes). *)
Lemma mca_consistent : (forall f a : code, ~ W f a (fun _ => False)) -> ~ exists e, @ftop mca_frame —[e]→ fbot.
Proof.
  intros Prog [e H]. pose proof (H e I) as He. apply (Prog e e). eapply dia_mono; [|exact He].
  intros r Hr. apply (Prog r e). apply (Hr e I (fun _ => False)). exists (fun _ => False). intros c. reflexivity.
Qed.

End MCAFrame.
