(** * The usual tripos as a restriction of the Sεt-tripos (end of Section 5.2)

    The paper sends a set X of the meta-theory to x̌ ≜ {(⊤, y̌) | y ∈ x}
    and uses that names are separated (x̌ ≠ y̌ ⇒ ⟦x̌ = y̌⟧ ⩽ ⊥), which
    requires classical logic. Here we assume, for a type X, codes
    [code : X → V] that are injective for tree equality ([code_inj], a
    named hypothesis); ∇X ≜ {(⊤, code x) | x ∈ X}. An instance is given
    for X = ℕ, with the von Neumann integers sₙ.

    Under this hypothesis:
    - ∇ extends to functions (∇g(α, β) ≜ ⋃_x [α ≡ code x] ∧ ⟦β = code(g x)⟧)
      and preserves identities and compositions;
    - the fibre over ∇X is equivalent to Φ^X uniformly preordered (the
      fibre of the tripos of the frame over X). *)

From Stdlib Require Import Setoid Morphisms Arith Lia.
From IZFe Require Import Frame VE Set_eps Tripos.

Section Nabla.

Context (F : frame).
Local Notation V := (@V F).
Local Notation tpred := (tpred F).

#[local] Instance teq_equiv9 : Equivalence (@teq F).
Proof. split; [intros x; apply teq_refl|intros x y; apply teq_sym|intros x y z; apply teq_trans]. Qed.
#[local] Existing Instance sheq_equiv.

(** ** Coded types *)

Record coded := {
  ctype :> Type;
  code : ctype -> V;
  code_inj : forall x y, teq (code x) (code y) -> x = y
}.

Arguments code {c} _.

Definition nab (X : coded) : V := mk X (fun x => (ftop, code x)).

Lemma nab_sub (X : coded) (x : X) : teq (sub (nab X) x) (code x).
Proof. apply (sub_mk F). Qed.

Lemma nab_in (X : coded) (x : X) (φ : F) : φ —[e_comp e_top e_exI]→ eps (code x) (nab X).
Proof. eapply (n_eps_in F _ _ (nab X) x); [apply nab_sub|apply f_top]. Qed.

(** ** ∇ on functions *)

Section Map.

Context (X Y : coded) (g : X -> Y).

Definition nab_rel (α β : V) : pcar F := fex (fun x : X => fand (fbr (teq α (code x))) (veq β (code (g x)))).

Lemma nab_rel_proper : Rproper F nab_rel.
Proof.
  intros α α' β β' Eα Eβ. apply fex_proper_idx.
  - intros x. exists x. apply fand_proper; [|apply veq_proper; [exact Eβ|reflexivity]].
    apply fex_proper_idx; intros H; [exists (teq_trans F _ _ _ (teq_sym F _ _ Eα) H)|exists (teq_trans F _ _ _ Eα H)]; reflexivity.
  - intros x. exists x. apply fand_proper; [|apply veq_proper; [symmetry; exact Eβ|reflexivity]].
    apply fex_proper_idx; intros H; [exists (teq_trans F _ _ _ Eα H)|exists (teq_trans F _ _ _ (teq_sym F _ _ Eα) H)]; reflexivity.
Qed.

Lemma n_br (φ χ : F) (P : Prop) e0 e : φ —[e0]→ fbr P -> (P -> fand φ ftop —[e]→ χ) -> φ —[e_exE_ctx e0 e]→ χ.
Proof. intros H0 H. apply (n_exE (fun _ : P => ftop)); [exact H0|]. intros p. apply H, p. Qed.

Lemma n_brI (φ : F) (P : Prop) : P -> φ —[e_comp e_top e_exI]→ fbr P.
Proof. intros p. apply (n_exI (fun _ : P => ftop) p), f_top. Qed.

Definition snab : shom F (nab X) (nab Y).
Proof.
  refine {| hr := nab_rel; hr_proper := nab_rel_proper |}.
  - eexists. intros [α β]. cbn. apply (n_exE (fun x : X => fand (fbr (teq α (code x))) (veq β (code (g x))))); [apply f_id|].
    intros x. eapply n_br; [eapply n_fst, n_hyp0|]. intros Hx. apply n_pair.
    + eapply n_eq; [apply eps_proper; [symmetry; exact Hx|reflexivity]|apply nab_in].
    + apply (n_tr F (fun z => eps z (nab Y)) (eps_l_proper F _) (code (g x)) β); [apply n_sym; eapply n_snd, n_wk, n_hyp0|apply nab_in].
  - eexists. intros α. eapply (n_eps_el F _ _ _ _ α (nab X)); [apply f_id|]. intros x Hx.
    apply (n_exI (fun β => nab_rel α β) (code (g x))). apply (n_exI (fun x0 : X => fand (fbr (teq α (code x0))) (veq (code (g x)) (code (g x0)))) x).
    apply n_pair; [apply n_brI; rewrite <- Hx; apply nab_sub|apply n_refl].
  - eexists. intros [[α β] β']. cbn.
    apply (n_exE (fun x : X => fand (fbr (teq α (code x))) (veq β (code (g x))))); [eapply n_fst, f_id|]. intros x.
    apply (n_exE (fun x : X => fand (fbr (teq α (code x))) (veq β' (code (g x))))); [eapply n_snd, n_wk, f_id|]. intros x'.
    eapply n_br; [eapply n_fst, n_wk, n_hyp0|]. intros Hx.
    eapply n_br; [eapply n_fst, n_wk, n_hyp0|]. intros Hx'.
    assert (E : x = x') by (apply code_inj; rewrite <- Hx, <- Hx'; reflexivity). subst x'.
    eapply n_trans; [eapply n_snd, n_wk, n_wk, n_wk, n_hyp0|]. apply n_sym. eapply n_snd, n_wk, n_wk, n_hyp0.
Defined.

End Map.

(** A meta-level function passes to Leibniz equality of codes. *)
Lemma code_map_veq (Y Z : coded) (h : Y -> Z) : exists e, forall y y', veq (code y) (code y') —[e]→ veq (code (h y)) (code (h y')).
Proof.
  set (P := fun y z => fex (fun y0 : Y => fand (fbr (teq z (code y0))) (veq (code (h y)) (code (h y0))))).
  assert (HP : forall y, Pproper F (P y)).
  { intros y z z' E. apply fex_proper. intros y0. apply fand_proper; [|reflexivity].
    apply fex_proper_idx; intros H; [exists (teq_trans F _ _ _ (teq_sym F _ _ E) H)|exists (teq_trans F _ _ _ E H)]; reflexivity. }
  eexists. intros y y'.
  eapply (n_exE (fun y0 : Y => fand (fbr (teq (code y') (code y0))) (veq (code (h y)) (code (h y0))))).
  - apply (n_tr F (P y) (HP y) (code y) (code y')); [apply f_id|].
    apply (n_exI (fun y0 : Y => fand (fbr (teq (code y) (code y0))) (veq (code (h y)) (code (h y0)))) y).
    apply n_pair; [apply n_brI; reflexivity|apply n_refl].
  - intros y0. eapply n_br; [eapply n_fst, n_hyp0|]. intros H. apply code_inj in H. subst y0.
    eapply n_snd, n_wk, n_hyp0.
Qed.

(** ∇ preserves identity and composition. *)
Lemma nab_id (X : coded) : sheq F (snab X X (fun x => x)) (sid F (nab X)).
Proof.
  split.
  - eexists. intros [α β]. cbn. apply (n_exE (fun x : X => fand (fbr (teq α (code x))) (veq β (code x)))); [apply f_id|].
    intros x. eapply n_br; [eapply n_fst, n_hyp0|]. intros Hx. apply n_pair.
    + eapply n_eq; [apply eps_proper; [symmetry; exact Hx|reflexivity]|apply nab_in].
    + eapply n_trans; [apply n_veq_of_teq, Hx|]. apply n_sym. eapply n_snd, n_wk, n_hyp0.
  - eexists. intros [α β]. cbn. eapply (n_eps_el F _ _ _ _ α (nab X)); [eapply n_fst, f_id|]. intros x Hx.
    apply (n_exI (fun x0 : X => fand (fbr (teq α (code x0))) (veq β (code x0))) x).
    apply n_pair; [apply n_brI; rewrite <- Hx; apply nab_sub|].
    eapply n_trans; [apply n_sym; eapply n_snd, n_wk, f_id|]. apply n_veq_of_teq. rewrite <- Hx. apply nab_sub.
Qed.

Lemma nab_comp (X Y Z : coded) (g : X -> Y) (h : Y -> Z) :
  sheq F (snab X Z (fun x => h (g x))) (scomp F (snab Y Z h) (snab X Y g)).
Proof.
  split.
  - eexists. intros [α γ]. cbn. apply (n_exE (fun x : X => fand (fbr (teq α (code x))) (veq γ (code (h (g x)))))); [apply f_id|].
    intros x. apply (n_exI (fun β => fand (nab_rel X Y g α β) (nab_rel Y Z h β γ)) (code (g x))). apply n_pair.
    + apply (n_exI (fun x0 : X => fand (fbr (teq α (code x0))) (veq (code (g x)) (code (g x0)))) x).
      apply n_pair; [eapply n_fst, n_hyp0|apply n_refl].
    + apply (n_exI (fun y : Y => fand (fbr (teq (code (g x)) (code y))) (veq γ (code (h y)))) (g x)).
      apply n_pair; [apply n_brI; reflexivity|eapply n_snd, n_hyp0].
  - destruct (code_map_veq Y Z h) as [e0 H0].
    eexists. intros [α γ]. cbn. apply (n_exE (fun β => fand (nab_rel X Y g α β) (nab_rel Y Z h β γ))); [apply f_id|]. intros β.
    apply (n_exE (fun x : X => fand (fbr (teq α (code x))) (veq β (code (g x))))); [eapply n_fst, n_hyp0|]. intros x.
    apply (n_exE (fun y : Y => fand (fbr (teq β (code y))) (veq γ (code (h y))))); [eapply n_snd, n_wk, n_hyp0|]. intros y.
    apply (n_exI (fun x0 : X => fand (fbr (teq α (code x0))) (veq γ (code (h (g x0))))) x).
    apply n_pair; [eapply n_fst, n_wk, n_hyp0|].
    eapply n_trans; [eapply n_snd, n_hyp0|]. eapply f_comp; [|apply H0].
    eapply n_br; [eapply n_fst, n_hyp0|]. intros Hy.
    eapply n_trans; [apply n_veq_of_teq; symmetry; exact Hy|]. eapply n_snd, n_wk, n_wk, n_hyp0.
Qed.

(** ** The fibre over ∇X and Φ^X *)

Section Fib.

Context (X : coded).

Definition ule (φ ψ : X -> pcar F) : Prop := exists e, forall x, φ x —[e]→ ψ x.

Definition toS (p : tpred) : X -> pcar F := fun x => p (code x).

Program Definition fromS (φ : X -> pcar F) : tpred := {| tp := fun z => fex (fun x : X => fand (fbr (teq z (code x))) (φ x)) |}.
Next Obligation.
  intros z z' E. apply fex_proper. intros x. apply fand_proper; [|reflexivity].
  apply fex_proper_idx; intros H; [exists (teq_trans F _ _ _ (teq_sym F _ _ E) H)|exists (teq_trans F _ _ _ E H)]; reflexivity.
Qed.

Lemma toS_mono p q : tle F (nab X) p q <-> ule (toS p) (toS q).
Proof.
  split.
  - intros [e H]. eexists. intros x. eapply f_comp; [|apply H]. apply n_pair; [apply nab_in|apply f_id].
  - intros [e H]. eexists. intros z. eapply (n_eps_el F _ _ _ _ z (nab X)); [apply f_fst|]. intros x Hx.
    eapply (n_eq _ (q (code x))); [apply tp_proper; rewrite <- Hx; symmetry; apply nab_sub|].
    eapply f_comp; [|apply (H x)]. unfold toS.
    eapply (n_eq _ (p z)); [apply tp_proper; rewrite <- Hx; apply nab_sub|]. eapply n_snd, n_wk, f_id.
Qed.

Lemma fromS_mono φ ψ : ule φ ψ -> tle F (nab X) (fromS φ) (fromS ψ).
Proof.
  intros [e H]. eexists. intros z. cbn. apply (n_exE (fun x : X => fand (fbr (teq z (code x))) (φ x))); [apply f_snd|]. intros x.
  apply (n_exI (fun x : X => fand (fbr (teq z (code x))) (ψ x)) x). apply n_pair; [eapply n_fst, n_hyp0|].
  eapply f_comp; [eapply n_snd, n_hyp0|apply H].
Qed.

Lemma to_from φ : ule (toS (fromS φ)) φ /\ ule φ (toS (fromS φ)).
Proof.
  split.
  - eexists. intros x. cbn. apply (n_exE (fun y : X => fand (fbr (teq (code x) (code y))) (φ y))); [apply f_id|]. intros y.
    eapply n_br; [eapply n_fst, n_hyp0|]. intros H. apply code_inj in H. subst y. eapply n_snd, n_wk, n_hyp0.
  - eexists. intros x. cbn. apply (n_exI (fun y : X => fand (fbr (teq (code x) (code y))) (φ y)) x).
    apply n_pair; [apply n_brI; reflexivity|apply f_id].
Qed.

Lemma from_to p : tiso F (nab X) (fromS (toS p)) p.
Proof.
  split.
  - eexists. intros z. cbn. apply (n_exE (fun x : X => fand (fbr (teq z (code x))) (p (code x)))); [apply f_snd|]. intros x.
    eapply n_br; [eapply n_fst, n_hyp0|]. intros H. eapply (n_eq _ (p (code x))); [apply tp_proper; symmetry; exact H|].
    eapply n_snd, n_wk, n_hyp0.
  - eexists. intros z. cbn. eapply (n_eps_el F _ _ _ _ z (nab X)); [apply f_fst|]. intros x Hx.
    apply (n_exI (fun y : X => fand (fbr (teq z (code y))) (p (code y))) x).
    apply n_pair; [apply n_brI; rewrite <- Hx; apply nab_sub|].
    eapply (n_eq _ (p z)); [apply tp_proper; rewrite <- Hx; apply nab_sub|]. eapply n_snd, n_wk, f_id.
Qed.

End Fib.

(** ** An instance: ℕ, coded by sₙ *)

Fixpoint pathP (d : nat) (s : shape) : Prop :=
  match d, s with
  | 0, _ => True
  | S d, node T k => exists t, pathP d (k t)
  end.

Lemma pathP_down d : forall s, pathP (S d) s -> pathP d s.
Proof.
  induction d as [|d IH]; intros [T k]; cbn; [auto|]. intros [t Ht]. exists t. apply IH, Ht.
Qed.

Lemma pathP_S d s : pathP (S d) s <-> exists t : idxS s, pathP d (subS s t).
Proof. destruct s; reflexivity. Qed.

Lemma pathP_snat d m : pathP d (projT1 (snat F m)) <-> d <= m.
Proof.
  revert d. induction m as [|m IH]; intros [|d]; cbn; split; try lia; auto.
  - intros [[] _].
  - intros [[[|] u] Hu]; cbn in Hu.
    + assert (S d <= m) by (apply IH, pathP_S; exists u; exact Hu). lia.
    + cbn in Hu. assert (d <= m) by (apply IH; destruct u; exact Hu). lia.
  - intros H. exists (existT _ false true). cbn. apply IH. lia.
Qed.

Lemma snat_inj n m : teq (snat F n) (snat F m) -> n = m.
Proof.
  intros [E _]. assert (H1 : pathP n (projT1 (snat F m))) by (rewrite <- E; apply pathP_snat; lia).
  assert (H2 : pathP m (projT1 (snat F n))) by (rewrite E; apply pathP_snat; lia).
  apply pathP_snat in H1. apply pathP_snat in H2. lia.
Qed.

Definition nat_coded : coded := {| ctype := nat; code := snat F; code_inj := snat_inj |}.

End Nabla.
