(** * The model V(E): sets, relations and constructions (Section 4.2)

    The elements of V(E) (Definition 24) are represented by labelled
    Aczel-style trees: a shape (a family of subshapes indexed by a type)
    and, at each node, a proposition of Φ per branch. Two sets are equal
    (in the setoid sense) if they have the same shape and ≡ labels; we do
    not quotient by bisimulation.

    Meta-theoretical hypotheses (paragraph "Meta-theory and
    formalization"):
    - Φ is essentially small: [enc], [dec] to a type Φ₀ in the same
      universe as the indices of the trees;
    - a collection procedure by values ([coll]). *)

From Stdlib Require Import Setoid Morphisms.
From IZFe Require Import Frame.

Inductive shape : Type := node (T : Type) (k : T -> shape).

Section VE.

Context (F : frame).

Fixpoint lab (s : shape) : Type :=
  match s with node T k => forall t : T, (pcar F * lab (k t))%type end.

Definition V : Type := { s : shape & lab s }.

Fixpoint leq (s : shape) : lab s -> lab s -> Prop :=
  match s as s0 return lab s0 -> lab s0 -> Prop with
  | node T k => fun l l' => forall t, fst (l t) ≡ fst (l' t) /\ leq (k t) (snd (l t)) (snd (l' t))
  end.

Lemma leq_refl s : forall l, leq s l l.
Proof. induction s as [T k IH]; intros l t. split; [apply peq_refl|apply IH]. Qed.

Lemma leq_sym s : forall l l', leq s l l' -> leq s l' l.
Proof.
  induction s as [T k IH]; intros l l' H t. destruct (H t) as [H1 H2].
  split; [apply peq_sym, H1|apply IH, H2].
Qed.

Lemma leq_trans s : forall l l' l'', leq s l l' -> leq s l' l'' -> leq s l l''.
Proof.
  induction s as [T k IH]; intros l l' l'' H H' t. destruct (H t) as [H1 H2], (H' t) as [H1' H2'].
  split; [eapply peq_trans; eassumption|eapply IH; eassumption].
Qed.

Definition teq (v w : V) : Prop :=
  exists E : projT1 v = projT1 w, leq (projT1 w) (eq_rect _ lab (projT2 v) _ E) (projT2 w).

Lemma teq_refl v : teq v v.
Proof. exists eq_refl. apply leq_refl. Qed.

Lemma teq_sym v w : teq v w -> teq w v.
Proof.
  destruct v as [s l], w as [s' l']; intros [E H]; cbn in *. destruct E. exists eq_refl. apply leq_sym, H.
Qed.

Lemma teq_trans u v w : teq u v -> teq v w -> teq u w.
Proof.
  destruct u as [s l], v as [s' l'], w as [s'' l'']; intros [E H] [E' H']; cbn in *.
  destruct E, E'. exists eq_refl. eapply leq_trans; eassumption.
Qed.

Definition Vset : pset := {| pcar := V; peq := teq; peq_refl := teq_refl; peq_sym := teq_sym; peq_trans := teq_trans |}.

Definition idxS (s : shape) : Type := match s with node T _ => T end.
Definition subS (s : shape) : idxS s -> shape := match s as s0 return idxS s0 -> shape with node T k => k end.
Definition labS (s : shape) : lab s -> forall t : idxS s, (pcar F * lab (subS s t))%type :=
  match s as s0 return lab s0 -> forall t : idxS s0, (pcar F * lab (subS s0 t))%type with
  | node T k => fun l => l
  end.

Lemma leq_lab s l l' : leq s l l' ->
  forall t, fst (labS s l t) ≡ fst (labS s l' t) /\ leq (subS s t) (snd (labS s l t)) (snd (labS s l' t)).
Proof. destruct s as [T k]. exact (fun H => H). Qed.

(** dom(x), the labels and the branches. *)
Definition idx (v : V) : Type := idxS (projT1 v).
Definition lbl (v : V) (t : idx v) : pcar F := fst (labS (projT1 v) (projT2 v) t).
Definition sub (v : V) (t : idx v) : V := existT _ (subS (projT1 v) t) (snd (labS (projT1 v) (projT2 v) t)).

Lemma teq_br s l l' t : leq s l l' ->
  lbl (existT _ s l) t ≡ lbl (existT _ s l') t /\ teq (sub (existT _ s l) t) (sub (existT _ s l') t).
Proof.
  intros H. destruct (leq_lab s l l' H t) as [H1 H2]. split; [exact H1|]. exists eq_refl. exact H2.
Qed.

(** Building a set from its branches: {(fₜ.1, fₜ.2) | t ∈ T}. *)
Definition mk (T : Type) (f : T -> (pcar F * V)%type) : V :=
  existT _ (node T (fun t => projT1 (snd (f t)))) (fun t => (fst (f t), projT2 (snd (f t)))).

Lemma sub_mk T f t : teq (sub (mk T f) t) (snd (f t)).
Proof. unfold sub; cbn. destruct (snd (f t)) as [s l]. apply teq_refl. Qed.

(** ** The relations (Definition 25) *)

(** ⟦x = y⟧, Leibniz. *)
Definition veq (x y : V) : pcar F := leib (A := Vset) x y.

Lemma veq_proper x x' y y' : teq x x' -> teq y y' -> veq x y ≡ veq x' y'.
Proof. intros; apply leib_proper; assumption. Qed.

(** ⟦x ε y⟧ ≜ ⋃_{(φ, x) ∈ y} φ: the branches of y equal to x. *)
Definition eps (x y : V) : pcar F := fex (fun t : { t : idx y | teq (sub y t) x } => lbl y (proj1_sig t)).

Lemma eps_proper x x' y y' : teq x x' -> teq y y' -> eps x y ≡ eps x' y'.
Proof.
  intros Ex Ey. destruct y as [s l], y' as [s' l'], Ey as [E H]; cbn in E, H. destruct E.
  apply fex_proper_idx.
  - intros [t Ht]. assert (Ht' : teq (sub (existT _ s l') t) x').
    { eapply teq_trans; [apply teq_sym, (proj2 (teq_br s l l' t H))|]. eapply teq_trans; [exact Ht|exact Ex]. }
    exists (exist _ t Ht'). exact (proj1 (teq_br s l l' t H)).
  - intros [t Ht]. assert (Ht' : teq (sub (existT _ s l) t) x).
    { eapply teq_trans; [apply (proj2 (teq_br s l l' t H))|]. eapply teq_trans; [exact Ht|apply teq_sym, Ex]. }
    exists (exist _ t Ht'). exact (peq_sym (proj1 (teq_br s l l' t H))).
Qed.

(** A branch t of y is an element: lbl y t ⩽ ⟦y(t) ε y⟧. *)
Definition br (y : V) (t : idx y) : { u : idx y | teq (sub y u) (sub y t) } := exist _ t (teq_refl _).

Lemma eps_br y t : lbl y t —[e_exI]→ eps (sub y t) y.
Proof. exact (f_exI _ (fun u : { u : idx y | teq (sub y u) (sub y t) } => lbl y (proj1_sig u)) (br y t)). Qed.

(** (x ⊆ y, y ⊆ x), by recursion on x: the pair avoids a mutual
    recursion. *)
Fixpoint subP (s : shape) : lab s -> V -> (pcar F * pcar F)%type :=
  match s as s0 return lab s0 -> V -> (pcar F * pcar F)%type with
  | node T k => fun l y =>
      let E t z := subP (k t) (snd (l t)) z in
      (fall (fun t : T => fimp (fst (l t))
               (fex (fun u : idx y => fand (lbl y u) (fand (fst (E t (sub y u))) (snd (E t (sub y u))))))),
       fall (fun u : idx y => fimp (lbl y u)
               (fex (fun t : T => fand (fst (l t)) (fand (snd (E t (sub y u))) (fst (E t (sub y u))))))))
  end.

Definition subV (x y : V) := subP (projT1 x) (projT2 x) y.

Definition pequiv (p q : (pcar F * pcar F)%type) : Prop := fst p ≡ fst q /\ snd p ≡ snd q.

Lemma subP_proper_r s : forall l y y', teq y y' -> pequiv (subP s l y) (subP s l y').
Proof.
  induction s as [T k IH]; intros l y y' Ey.
  destruct y as [s' l'], y' as [s'' l''], Ey as [E H]; cbn in E, H. destruct E.
  split; cbn [subP fst snd].
  - apply fall_proper; intros t. apply fimp_proper; [apply peq_refl|]. apply fex_proper; intros u.
    destruct (teq_br s' l' l'' u H) as [J1 J2].
    apply fand_proper; [exact J1|].
    destruct (IH t (snd (l t)) _ _ J2) as [I1 I2]. apply fand_proper; assumption.
  - apply fall_proper; intros u. destruct (teq_br s' l' l'' u H) as [J1 J2].
    apply fimp_proper; [exact J1|]. apply fex_proper; intros t.
    apply fand_proper; [apply peq_refl|].
    destruct (IH t (snd (l t)) _ _ J2) as [I1 I2]. apply fand_proper; assumption.
Qed.

Lemma subP_proper_l s : forall l l' y, leq s l l' -> pequiv (subP s l y) (subP s l' y).
Proof.
  induction s as [T k IH]; intros l l' y H.
  split; cbn [subP fst snd].
  - apply fall_proper; intros t. apply fimp_proper; [exact (proj1 (H t))|]. apply fex_proper; intros u.
    apply fand_proper; [apply peq_refl|].
    destruct (IH t (snd (l t)) (snd (l' t)) (sub y u) (proj2 (H t))) as [I1 I2]. apply fand_proper; assumption.
  - apply fall_proper; intros u. apply fimp_proper; [apply peq_refl|]. apply fex_proper; intros t.
    apply fand_proper; [exact (proj1 (H t))|].
    destruct (IH t (snd (l t)) (snd (l' t)) (sub y u) (proj2 (H t))) as [I1 I2]. apply fand_proper; assumption.
Qed.

Lemma subV_proper x x' y y' : teq x x' -> teq y y' -> pequiv (subV x y) (subV x' y').
Proof.
  intros Ex Ey. destruct x as [s l], x' as [s' l'], Ex as [E H]; cbn in E, H. destruct E.
  destruct (subP_proper_r s l y y' Ey) as [A1 A2]. destruct (subP_proper_l s l l' y' H) as [B1 B2].
  split; eapply peq_trans; eassumption.
Qed.

Lemma subP_swap s : forall l y,
  snd (subP s l y) ≡ fst (subV y (existT _ s l)) /\ fst (subP s l y) ≡ snd (subV y (existT _ s l)).
Proof.
  induction s as [T k IH]; intros l [[U k'] l']. cbn [subP subV projT1 projT2 fst snd].
  unfold sub, lbl; cbn [projT1 projT2 idxS subS labS].
  split.
  - apply fall_proper; intros u. apply fimp_proper; [apply peq_refl|]. apply fex_proper; intros t.
    apply fand_proper; [apply peq_refl|].
    destruct (IH t (snd (l t)) (existT _ (k' u) (snd (l' u)))) as [I1 I2].
    apply fand_proper; assumption.
  - apply fall_proper; intros t. apply fimp_proper; [apply peq_refl|]. apply fex_proper; intros u.
    apply fand_proper; [apply peq_refl|].
    destruct (IH t (snd (l t)) (existT _ (k' u) (snd (l' u)))) as [I1 I2].
    apply fand_proper; [exact I2|exact I1].
Qed.

(** ⟦x ⊆ y⟧, ⟦x ≃ y⟧, ⟦x ∈ y⟧. *)
Definition vsub (x y : V) : pcar F := fst (subV x y).
Definition veqv (x y : V) : pcar F := fand (vsub x y) (vsub y x).
Definition vmem (x y : V) : pcar F := fex (fun u : idx y => fand (lbl y u) (veqv x (sub y u))).

Lemma vsub_proper x x' y y' : teq x x' -> teq y y' -> vsub x y ≡ vsub x' y'.
Proof. intros Ex Ey. exact (proj1 (subV_proper x x' y y' Ex Ey)). Qed.

Lemma veqv_proper x x' y y' : teq x x' -> teq y y' -> veqv x y ≡ veqv x' y'.
Proof. intros Ex Ey. apply fand_proper; apply vsub_proper; assumption. Qed.

Lemma vmem_proper x x' y y' : teq x x' -> teq y y' -> vmem x y ≡ vmem x' y'.
Proof.
  intros Ex Ey. destruct y as [s l], y' as [s' l'], Ey as [E H]; cbn in E, H. destruct E.
  apply fex_proper. intros t. destruct (teq_br s l l' t H) as [H1 H2].
  apply fand_proper; [exact H1|]. apply veqv_proper; [exact Ex|exact H2].
Qed.

(** ⟦x ⊆ y⟧ ≡ ⋂_{(φ, z) ∈ x} (φ ⊃ ⟦z ∈ y⟧). *)
Lemma vsub_unfold x y : vsub x y ≡ fall (fun t : idx x => fimp (lbl x t) (vmem (sub x t) y)).
Proof.
  destruct x as [[T k] l]. unfold vsub, subV. cbn [subP projT1 projT2 fst].
  apply fall_proper; intros t. apply fimp_proper; [apply peq_refl|]. apply fex_proper; intros u.
  apply fand_proper; [apply peq_refl|]. unfold veqv, vsub, subV. cbn [projT1 projT2].
  apply fand_proper; [apply peq_refl|].
  exact (proj1 (subP_swap (k t) (snd (l t)) (sub y u))).
Qed.

(** ** The constructions *)

Context (Φ0 : Type) (enc : pcar F -> Φ0) (dec : Φ0 -> pcar F).
Context (dec_enc : forall φ, dec (enc φ) ≡ φ).

Definition rel (s : shape) : lab s -> (idxS s -> pcar F) -> lab s :=
  match s as s0 return lab s0 -> (idxS s0 -> pcar F) -> lab s0 with
  | node T k => fun l g t => (fand (g t) (fst (l t)), snd (l t))
  end.

Lemma rel_proper s l l' g g' : leq s l l' -> (forall t, g t ≡ g' t) -> leq s (rel s l g) (rel s l' g').
Proof.
  destruct s as [T k]; intros H Hg t. destruct (H t) as [H1 H2]. split; [apply fand_proper; auto|exact H2].
Qed.

(** inl ≜ ⋂_{φ,ψ} φ ⊃ ψ ⊃ φ and inr ≜ ⋂_{φ,ψ} φ ⊃ ψ ⊃ ψ: Church booleans. *)
Definition tagT : pcar F := fall (fun φ : pcar F => fall (fun ψ : pcar F => fimp φ (fimp ψ φ))).
Definition tagF : pcar F := fall (fun φ : pcar F => fall (fun ψ : pcar F => fimp φ (fimp ψ ψ))).

Definition vempty : V := existT lab (node Empty_set (fun e : Empty_set => match e with end))
  (fun e : Empty_set => match e with end).

(** ⟦{x, y}⟧ ≜ {(inl, x), (inr, y)}. *)
Definition vpair (a b : V) : V :=
  existT _ (node bool (fun c => if c then projT1 a else projT1 b))
      (fun c => match c as c0 return (pcar F * lab (if c0 then projT1 a else projT1 b))%type with
                | true => (tagT, projT2 a)
                | false => (tagF, projT2 b)
                end).

Lemma vpair_proper a a' b b' : teq a a' -> teq b b' -> teq (vpair a b) (vpair a' b').
Proof.
  destruct a as [s l], a' as [s' l'], b as [r m], b' as [r' m']. intros [E H] [E' H']; cbn in *. destruct E, E'.
  exists eq_refl. intros [|]; (split; [apply peq_refl|]); assumption.
Qed.

(** ⟦⋃x⟧ ≜ {(φ ∧ ψ, z) | (φ, y) ∈ x, (ψ, z) ∈ y}. *)
Definition vunion (a : V) : V :=
  existT _ (node { t : idxS (projT1 a) & idxS (subS (projT1 a) t) }
      (fun p => subS (subS (projT1 a) (projT1 p)) (projT2 p)))
      (fun p => (fand (fst (labS (projT1 a) (projT2 a) (projT1 p)))
                      (fst (labS _ (snd (labS (projT1 a) (projT2 a) (projT1 p))) (projT2 p))),
                 snd (labS _ (snd (labS (projT1 a) (projT2 a) (projT1 p))) (projT2 p)))).

Lemma vunion_proper a a' : teq a a' -> teq (vunion a) (vunion a').
Proof.
  destruct a as [s l], a' as [s' l']. intros [E H]; cbn in *. destruct E.
  exists eq_refl. intros [t u]; cbn.
  destruct (leq_lab s l l' H t) as [H1 H2]. destruct (leq_lab _ _ _ H2 u) as [H3 H4].
  split; [apply fand_proper; assumption|exact H4].
Qed.

(** ⟦{x ε a | φ(x)}⟧ ≜ {(⟦φ(x)⟧ ∧ ψ, x) | (ψ, x) ∈ a}. *)
Definition vsep (a : V) (φ : V -> pcar F) : V :=
  existT _ (projT1 a) (rel (projT1 a) (projT2 a) (fun t => φ (sub a t))).

Definition Pproper (φ : V -> pcar F) : Prop := forall x x', teq x x' -> φ x ≡ φ x'.

Lemma vsep_proper a a' (φ φ' : V -> pcar F) :
  Pproper φ -> teq a a' -> (forall z, φ z ≡ φ' z) -> teq (vsep a φ) (vsep a' φ').
Proof.
  destruct a as [s l], a' as [s' l']. intros Hp [E H] Hφ; cbn in *. destruct E.
  exists eq_refl. cbn. apply rel_proper; [exact H|]. intros t.
  eapply peq_trans; [|apply Hφ]. apply Hp. exact (proj2 (teq_br s l l' t H)).
Qed.

(** ⟦𝒫(x)⟧ ≜ {(⊤, b_g) | g : dom(x) → Φ₀}, b_g ≜ {(g(t) ∧ ψₜ, xₜ)}. *)
Definition bsub (x : V) (g : idx x -> Φ0) : V := existT _ (projT1 x) (rel (projT1 x) (projT2 x) (fun t => dec (g t))).

Definition vpower (x : V) : V :=
  existT _ (node (idx x -> Φ0) (fun _ => projT1 x)) (fun g => (ftop, rel (projT1 x) (projT2 x) (fun t => dec (g t)))).

Lemma vpower_proper x x' : teq x x' -> teq (vpower x) (vpower x').
Proof.
  destruct x as [s l], x' as [s' l']. intros [E H]; cbn in *. destruct E.
  exists eq_refl. intros g. split; [apply peq_refl|]. apply rel_proper; [exact H|]. intros; apply peq_refl.
Qed.

(** ω: sₙ ≜ Sⁿ(∅), S(b) ≜ ⋃{b, {b, b}}, codes ⌜0⌝ ≜ inl ∧ ⊤, ⌜n+1⌝ ≜ inr ∧ ⌜n⌝. *)
Definition vsuc (b : V) : V := vunion (vpair b (vpair b b)).

Lemma vsuc_proper b b' : teq b b' -> teq (vsuc b) (vsuc b').
Proof. intros H. apply vunion_proper, vpair_proper; [exact H|apply vpair_proper; exact H]. Qed.

Fixpoint snat (n : nat) : V := match n with O => vempty | S m => vsuc (snat m) end.
Fixpoint pnat (n : nat) : pcar F := match n with O => fand tagT ftop | S m => fand tagF (pnat m) end.

Definition vomega : V := mk nat (fun n => (pnat n, snat n)).

(** ** Collection by values, and replacement *)

Definition Rproper (ψ : V -> V -> pcar F) : Prop :=
  forall x x' y y', teq x x' -> teq y y' -> ψ x y ≡ ψ x' y'.

(** The collection procedure: for a family (xₜ) and a relation ψ, a
    set B that reaches, for each t, all the values of β ↦ ψ(xₜ, β). *)
Context (coll : forall T : Type, (T -> V) -> (V -> V -> pcar F) -> V).
Context (coll_proper : forall T (xs xs' : T -> V) (ψ ψ' : V -> V -> pcar F),
  Rproper ψ -> (forall t, teq (xs t) (xs' t)) -> (forall x y, ψ x y ≡ ψ' x y) ->
  teq (coll T xs ψ) (coll T xs' ψ')).
Context (coll_spec : forall T (xs : T -> V) (ψ : V -> V -> pcar F), Rproper ψ ->
  forall t β, exists s, ψ (xs t) β ≡ ψ (xs t) (sub (coll T xs ψ) s)).

(** The collection set {(φ ∧ ⟦ψ(α, β)⟧, β) | (φ, α) ∈ a, β ∈ B}. *)
Definition vrepl (a : V) (ψ : V -> V -> pcar F) : V :=
  let B := coll (idx a) (sub a) ψ in
  mk (idx a * idx B) (fun p => (fand (lbl a (fst p)) (ψ (sub a (fst p)) (sub B (snd p))), sub B (snd p))).

Lemma vrepl_proper a a' ψ ψ' : Rproper ψ -> teq a a' -> (forall x y, ψ x y ≡ ψ' x y) ->
  teq (vrepl a ψ) (vrepl a' ψ').
Proof.
  intros Hψ Ha Hψ'. destruct a as [s l], a' as [s' l'], Ha as [E H]; cbn in E, H. destruct E.
  assert (HB : teq (coll _ (sub (existT _ s l)) ψ) (coll _ (sub (existT _ s l')) ψ')).
  { apply coll_proper; [exact Hψ| |exact Hψ']. intros t. exact (proj2 (teq_br s l l' t H)). }
  unfold vrepl, mk. cbn zeta.
  set (B := coll _ (sub (existT _ s l)) ψ) in *. set (B' := coll _ (sub (existT _ s l')) ψ') in *.
  clearbody B B'. destruct B as [r m], B' as [r' m'], HB as [E' H']; cbn in E', H'. destruct E'.
  exists eq_refl. intros [t u]. cbn. destruct (teq_br r m m' u H') as [K1 K2].
  split.
  - apply fand_proper; [exact (proj1 (teq_br s l l' t H))|].
    eapply peq_trans; [apply Hψ; [exact (proj2 (teq_br s l l' t H))|exact K2]|apply Hψ'].
  - exact (proj2 (leq_lab r m m' H' u)).
Qed.

End VE.

Arguments V {F}.
Arguments Vset F : clear implicits.
Arguments teq {F} v w.
Arguments idx {F} v.
Arguments lbl {F} v t.
Arguments sub {F} v t.
Arguments eps {F} x y.
Arguments veq {F} x y.
Arguments vmem {F} x y.
Arguments vsub {F} x y.
Arguments veqv {F} x y.
Arguments mk {F} T f.
