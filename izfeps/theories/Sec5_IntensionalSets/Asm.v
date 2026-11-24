(** * Assemblies (Section 5.4)

    - Definition 31: pre-assemblies (X, E) with E : X → Φ, and assemblies
      (each E(x) realized); morphisms are the functions tracked by an
      evidence: ⋂_x E(x) ⊃ E(f x) is realized, which we write in the
      equivalent form ∃e. ∀x. e ⊩ E(x) ⩽ E(f x).
    - The preAsm[E]-tripos: T(X, E) ≜ {x ↦ φ(x) ∧ E(x)}, that is Φ^X
      preordered by φ ⊑ ψ ≜ ∃e. ∀x. e ⊩ E(x) ∧ φ(x) ⩽ ψ(x). It is a tripos
      in the sense of Definition 29 (Pitts).
    - Definition 32: ε-pre-assemblies X ∈ V(E), and ε-assemblies (in
      V(E)⁺). Between ε-pre-assemblies, the morphisms of Sεt are exactly
      those of Set[E]: the full subcategory of Sεt on ε-pre-assemblies
      embeds fully and faithfully into Set[E] (Section 5.3), by the
      identity on objects and relations. *)

From Stdlib Require Import List Setoid Morphisms.
Import ListNotations.
From IZFe Require Import Syntax Deriv Theories Frame VE Model Realize Set_eps Cartesian Tripos Topos.

(** ** Full subcategories *)

Definition fullsub (C : category) (P : ob C -> Prop) : category := {|
  ob := { x : ob C | P x };
  hom := fun x y => hom C (proj1_sig x) (proj1_sig y);
  heq := fun x y => @heq C (proj1_sig x) (proj1_sig y);
  heq_equiv := fun x y => heq_equiv C (proj1_sig x) (proj1_sig y);
  cid := fun x => cid (proj1_sig x);
  ccomp := fun x y z => @ccomp C (proj1_sig x) (proj1_sig y) (proj1_sig z);
  ccomp_proper := fun x y z => ccomp_proper C (proj1_sig x) (proj1_sig y) (proj1_sig z);
  cid_l := fun x y => cid_l C (proj1_sig x) (proj1_sig y);
  cid_r := fun x y => cid_r C (proj1_sig x) (proj1_sig y);
  cassoc := fun x y z w => cassoc C (proj1_sig x) (proj1_sig y) (proj1_sig z) (proj1_sig w)
|}.

Section PreAsm.

Context (F : frame).

(** ** Pre-assemblies and assemblies (Definition 31) *)

Record pasm := { car : Type; ex : car -> pcar F }.

Definition tracked (X Y : pasm) (f : car X -> car Y) : Prop :=
  exists e, forall x, ex X x —[e]→ ex Y (f x).

Record ahom (X Y : pasm) := { af :> car X -> car Y; af_tracked : tracked X Y af }.

Arguments af {X Y} _ _.

Definition aheq {X Y} (f g : ahom X Y) : Prop := forall x, f x = g x.

Lemma aheq_equiv X Y : Equivalence (@aheq X Y).
Proof. split; [intros f x; reflexivity|intros f g H x; symmetry; apply H|intros f g h H1 H2 x; etransitivity; [apply H1|apply H2]]. Qed.

Definition aid (X : pasm) : ahom X X.
Proof. refine (Build_ahom X X (fun x => x) _). exists e_id. intros; apply f_id. Defined.

Definition acomp {X Y Z} (g : ahom Y Z) (f : ahom X Y) : ahom X Z.
Proof.
  refine (Build_ahom X Z (fun x => g (f x)) _).
  destruct (af_tracked _ _ f) as [e1 H1], (af_tracked _ _ g) as [e2 H2].
  exists (e_comp e1 e2). intros x. eapply f_comp; [apply H1|apply H2].
Defined.

Definition preAsm : category.
Proof.
  refine {| ob := pasm; hom := ahom; heq := @aheq; heq_equiv := aheq_equiv;
            cid := aid; ccomp := @acomp |}.
  - intros X Y Z g g' f f' Hg Hf x. cbn. rewrite Hf. apply Hg.
  - intros X Y f x. reflexivity.
  - intros X Y f x. reflexivity.
  - intros X Y Z W f g h x. reflexivity.
Defined.

Definition realized_ex (X : pasm) : Prop := forall x, exists e, ftop —[e]→ ex X x.

Definition Asm : category := fullsub preAsm realized_ex.

(** ** preAsm[E] is cartesian *)

Definition aone : pasm := {| car := unit; ex := fun _ => ftop |}.
Definition aprod (X Y : pasm) : pasm := {| car := car X * car Y; ex := fun p => fand (ex X (fst p)) (ex Y (snd p)) |}.

Definition abang X : ahom X aone.
Proof. refine (Build_ahom X aone (fun _ => tt) _). exists e_top. intros; apply f_top. Defined.
Definition apr1 X Y : ahom (aprod X Y) X.
Proof. refine (Build_ahom (aprod X Y) X fst _). exists e_fst. intros; apply f_fst. Defined.
Definition apr2 X Y : ahom (aprod X Y) Y.
Proof. refine (Build_ahom (aprod X Y) Y snd _). exists e_snd. intros; apply f_snd. Defined.

Definition apair A X Y (f : ahom A X) (g : ahom A Y) : ahom A (aprod X Y).
Proof.
  refine (Build_ahom A (aprod X Y) (fun a => (f a, g a)) _).
  destruct (af_tracked _ _ f) as [e1 H1], (af_tracked _ _ g) as [e2 H2].
  exists (e_pair e1 e2). intros a. apply n_pair; [apply H1|apply H2].
Defined.

Definition preAsm_cart : cartesian preAsm.
Proof.
  refine (Build_cartesian preAsm aone abang _ aprod apr1 apr2 apair _ _ _).
  - intros X f x. cbn. destruct (f x). reflexivity.
  - intros A X Y f g a. reflexivity.
  - intros A X Y f g a. reflexivity.
  - intros A X Y f g h H1 H2 a. cbn in *. rewrite <- H1, <- H2. cbn. destruct (h a); reflexivity.
Defined.

(** ** The preAsm[E]-tripos *)

Section Fib.

Context (X : pasm).

Definition ale (p q : car X -> pcar F) : Prop := exists e, forall x, fand (ex X x) (p x) —[e]→ q x.

Definition afib : preheyting.
Proof.
  refine {| hcar := car X -> pcar F; hle := ale;
            htop := fun _ => ftop; hbot := fun _ => fbot;
            hand := fun p q x => fand (p x) (q x); hor := fun p q x => for_ (p x) (q x);
            himp := fun p q x => fimp (p x) (q x) |}.
  - intros p. exists e_snd. intros; apply f_snd.
  - intros p q r [e1 H1] [e2 H2]. exists (e_comp (e_pair e_fst e1) e2). intros x.
    eapply f_comp; [apply n_pair; [apply f_fst|apply H1]|apply H2].
  - intros p. exists e_top. intros; apply f_top.
  - intros p. exists (e_comp e_snd e_incl). intros x. eapply f_comp; [apply f_snd|apply f_bot].
  - intros r p q. split.
    + intros [e H]. split; [exists (e_comp e e_fst)|exists (e_comp e e_snd)]; intros x; [eapply n_fst|eapply n_snd]; apply H.
    + intros [[e1 H1] [e2 H2]]. exists (e_pair e1 e2). intros x. apply n_pair; [apply H1|apply H2].
  - intros p q r. split.
    + intros [e H]. split; [exists (e_comp (e_pair e_fst (e_kl e_snd)) e)|exists (e_comp (e_pair e_fst (e_kr e_snd)) e)];
        intros x; (eapply f_comp; [|apply H]); apply n_pair; [apply f_fst| |apply f_fst|];
        [apply n_orI1, f_snd|apply n_orI2, f_snd].
    + intros [[e1 H1] [e2 H2]]. eexists. intros x.
      apply (n_orE _ (p x) (q x)); [apply f_snd| |].
      * eapply f_comp; [|apply H1]. apply n_pair; [eapply n_fst, n_wk, f_id|apply n_hyp0].
      * eapply f_comp; [|apply H2]. apply n_pair; [eapply n_fst, n_wk, f_id|apply n_hyp0].
  - intros r p q. split.
    + intros [e H]. eexists. intros x. apply n_lam. eapply f_comp; [|apply H].
      apply n_pair; [eapply n_fst, n_fst, f_id|apply n_pair; [eapply n_snd, n_fst, f_id|apply f_snd]].
    + intros [e H]. eexists. intros x. eapply n_app; [eapply f_comp; [|apply H]|].
      * apply n_pair; [apply f_fst|eapply n_fst, f_snd].
      * eapply n_snd, f_snd.
Defined.

End Fib.

Definition areidx {X Y : pasm} (f : ahom X Y) (q : afib Y) : afib X := fun x => q (f x).

Lemma hiso_refl {H : preheyting} (a : H) : hiso a a.
Proof. split; apply hle_refl. Qed.

Lemma areidx_mono X Y (f : ahom X Y) (p q : afib Y) : hle p q -> hle (areidx f p) (areidx f q).
Proof.
  intros [e H]. destruct (af_tracked _ _ f) as [e1 H1]. exists (e_comp (e_pair (e_comp e_fst e1) e_snd) e). intros x.
  eapply f_comp; [apply n_pair; [eapply f_comp; [apply f_fst|apply H1]|apply f_snd]|apply H].
Qed.

Definition adiag (X : pasm) : ahom X (aprod X X) := apair X X X (aid X) (aid X).

Definition aeqd (X : pasm) (p : afib X) : afib (aprod X X) :=
  fun xx => fand (fbr (F := F) (fst xx = snd xx)) (p (fst xx)).

Lemma aeqd_adj X (p : afib X) (r : afib (aprod X X)) : hle (aeqd X p) r <-> hle p (areidx (adiag X) r).
Proof.
  split.
  - intros [e H]. eexists. intros x. eapply f_comp; [|apply (H (x, x))]. cbn.
    apply n_pair; [apply n_pair; apply f_fst|apply n_pair; [|apply f_snd]].
    apply (n_exI (fun _ : x = x => ftop) eq_refl), f_top.
  - intros [e H]. eexists. intros [x x'].
    apply (n_exE (fun _ : x = x' => ftop)); [eapply n_fst, n_snd, f_id|]. intros E. cbn in E. subst x'.
    eapply f_comp; [|apply (H x)]. apply n_pair; [eapply n_fst, n_fst, n_wk, f_id|eapply n_snd, n_snd, n_wk, f_id].
Qed.

Definition aex (G X : pasm) (r : afib (aprod G X)) : afib G := fun γ => fex (fun x : car X => fand (ex X x) (r (γ, x))).
Definition aall (G X : pasm) (r : afib (aprod G X)) : afib G := fun γ => fall (fun x : car X => fimp (ex X x) (r (γ, x))).

Lemma aex_adj G X (r : afib (aprod G X)) (p : afib G) : hle (aex G X r) p <-> hle r (areidx (apr1 G X) p).
Proof.
  split.
  - intros [e H]. eexists. intros [γ x]. eapply f_comp; [|apply (H γ)]. cbn.
    apply n_pair; [eapply n_fst, n_fst, f_id|]. apply (n_exI (fun x => fand (ex X x) (r (γ, x))) x).
    apply n_pair; [eapply n_snd, n_fst, f_id|apply f_snd].
  - intros [e H]. eexists. intros γ.
    apply (n_exE (fun x => fand (ex X x) (r (γ, x)))); [apply f_snd|]. intros x.
    eapply f_comp; [|apply (H (γ, x))]. cbn.
    apply n_pair; [apply n_pair; [eapply n_fst, n_wk, f_id|eapply n_fst, n_hyp0]|eapply n_snd, n_hyp0].
Qed.

Lemma aall_adj G X (r : afib (aprod G X)) (p : afib G) : hle p (aall G X r) <-> hle (areidx (apr1 G X) p) r.
Proof.
  split.
  - intros [e H]. eexists. intros [γ x]. cbn.
    eapply n_app; [apply (n_inst (fun x => fimp (ex X x) (r (γ, x))) x)|eapply n_snd, n_fst, f_id].
    eapply f_comp; [|apply (H γ)]. apply n_pair; [eapply n_fst, n_fst, f_id|apply f_snd].
  - intros [e H]. eexists. intros γ. apply n_gen. intros x. apply n_lam.
    eapply f_comp; [|apply (H (γ, x))]. cbn.
    apply n_pair; [apply n_pair; [eapply n_fst, n_fst, f_id|apply f_snd]|eapply n_snd, n_fst, f_id].
Qed.

Definition apow (X : pasm) : pasm := {| car := car X -> pcar F; ex := fun _ => ftop |}.
Definition amem (X : pasm) : afib (aprod X (apow X)) := fun p => snd p (fst p).

Theorem preAsm_tripos : tripos preAsm preAsm_cart.
Proof.
  refine (Build_tripos preAsm preAsm_cart afib (@areidx) areidx_mono _ _ _ _ _ _ _ _
            aeqd aeqd_adj aex aall aex_adj aall_adj _ _ apow amem _); intros; try apply hiso_refl.
  - split; exists e_snd; intros a; unfold areidx; cbn in H; rewrite (H a); apply f_snd.
  - unshelve eexists (Build_ahom Y (apow X) (fun y x => φ (x, y)) _); [exists e_top; intros; apply f_top|].
    split; exists e_snd; intros [a b]; apply f_snd.
Defined.

End PreAsm.

(** ** ε-pre-assemblies and ε-assemblies (Definition 32) *)

Section EpsAsm.

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

#[local] Instance teq_equiv7 : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.

Local Notation eqvX := (eqvX F).
Local Notation ehom := (ehom F).
Local Notation SetE := (SetE F Φ0 enc dec dec_enc coll coll_proper coll_spec yfix yfix_spec).

(** X is an ε-pre-assembly if ⋂_{x, x'} ⟦x ε X⟧ ∧ ⟦x' ε X⟧ ∧ ⟦x ≃ x'⟧ ⊃ ⟦x = x'⟧ is realized. *)
Definition epasm (X : V) : Prop := exists e, forall x x' : V, eqvX X x x' —[e]→ veq x x'.

(** V(E)⁺: the labels are realized, hereditarily. *)
Inductive vplus : V -> Prop :=
  vplus_intro (x : V) : (forall t, (exists e, ftop —[e]→ lbl x t) /\ vplus (sub x t)) -> vplus x.

Definition easm (X : V) : Prop := epasm X /\ vplus X.

(** The associated pre-assembly: E(x) ≜ ⟦x ε X⟧ on dom(X). *)
Definition epasm_pasm (X : V) : pasm F := {| car := idx X; ex := fun t => eps (sub X t) X |}.

Lemma epasm_pasm_realized X : vplus X -> realized_ex F (epasm_pasm X).
Proof. intros [x H] t. destruct (H t) as [[e He] _]. exists (e_comp e e_exI). eapply f_comp; [exact He|apply eps_br]. Qed.

(** ⟦x = y⟧ implies ⟦x ≃ y⟧. *)
Lemma veq_veqv : exists e, forall x y : V, veq x y —[e]→ veqv x y.
Proof.
  destruct (veqv_refl F Φ0 enc dec dec_enc coll coll_proper coll_spec yfix yfix_spec) as [r Hr].
  eexists. intros x y.
  apply (n_tr F (fun z => veqv x z) (fun z z' E => veqv_proper F _ _ _ _ (teq_refl F x) E) x y); [apply f_id|apply Hr].
Qed.

(** Between ε-pre-assemblies, a morphism of Sεt is a morphism of Set[E]… *)
Definition to_E {X Y} (HX : epasm X) (HY : epasm Y) (f : shom F X Y) : ehom X Y.
Proof.
  refine (Build_ehom F X Y (@hr F X Y f) (@hr_proper F X Y f) _ _ _ _).
  - destruct (h_strict F X Y f) as [s Hs]. exists s. intros x y. apply (Hs (x, y)).
  - exact (h_total F X Y f).
  - destruct (func_e F f) as [c Hc], veq_veqv as [v Hv]. exists (e_comp c v). intros x y y'.
    eapply f_comp; [apply Hc|apply Hv].
  - destruct HX as [ex Hx], HY as [ey Hy]. eexists. intros x x' y y'.
    apply (n_tr F (fun b => f x' b) (hr_r_proper F f x') y y').
    + eapply f_comp; [eapply n_snd, n_fst, f_id|apply Hy].
    + apply (n_tr F (fun a => f a y) (hr_l_proper F f y) x x').
      * eapply f_comp; [eapply n_fst, n_fst, f_id|apply Hx].
      * apply f_snd.
Defined.

(** … and conversely. *)
Definition to_S {X Y} (HY : epasm Y) (f : ehom X Y) : shom F X Y.
Proof.
  refine (Build_shom F X Y (@er F X Y f) (er_proper F _ _ f) _ (e_total F _ _ f) _).
  - destruct (e_strict F _ _ f) as [s Hs]. exists s. intros [x y]. apply Hs.
  - destruct (e_func F _ _ f) as [c Hc], (e_strict F _ _ f) as [s Hs], HY as [ey Hy].
    eexists. intros [[x y] y']. cbn. eapply f_comp; [|apply Hy]. unfold Topos.eqvX.
    apply n_pair; [apply n_pair|apply Hc].
    + eapply n_snd, f_comp; [eapply n_fst, f_id|apply Hs].
    + eapply n_snd, f_comp; [eapply n_snd, f_id|apply Hs].
Defined.

Definition EpsPreAsm : category := fullsub (Seps F) epasm.

Definition epasm_embed : functor EpsPreAsm SetE.
Proof.
  refine (Build_functor EpsPreAsm SetE (fun X => proj1_sig X)
            (fun X Y f => to_E (proj2_sig X) (proj2_sig Y) f) _ _ _).
  - intros X Y f g [H1 H2]. split.
    + destruct H1 as [e H]. exists e. intros x y. apply (H (x, y)).
    + destruct H2 as [e H]. exists e. intros x y. apply (H (x, y)).
  - intros [X HX]. cbn. destruct (proj2_sig (exist _ X HX)) as [e He] eqn:E.
    destruct veq_veqv as [v Hv]. split.
    + eexists. intros x y. cbn. unfold id_rel, Topos.eqvX.
      apply n_pair; [apply n_pair; [apply f_fst|]|eapply f_comp; [apply f_snd|apply Hv]].
      apply (n_tr F (fun z => eps z X) (eps_l_proper F X) x y); [apply f_snd|apply f_fst].
    + eexists. intros x y. cbn. unfold id_rel, Topos.eqvX.
      apply n_pair; [eapply n_fst, n_fst, f_id|apply He].
  - intros X Y Z f g. split; exists e_id; intros; apply f_id.
Defined.

Theorem epasm_full : full epasm_embed.
Proof.
  intros [X HX] [Y HY] g. exists (to_S HY g). split; exists e_id; intros; apply f_id.
Qed.

Theorem epasm_faithful : faithful epasm_embed.
Proof.
  intros X Y f g [[e1 H1] [e2 H2]]. split; [exists e1|exists e2]; intros [x y]; [apply H1|apply H2].
Qed.

End EpsAsm.
