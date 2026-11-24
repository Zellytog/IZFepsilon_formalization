(** * Kuratowski pairs: injectivity for Leibniz equality

    ⟨x, y⟩ ≜ {{x, x}, {x, y}}. Injectivity only needs the pairing axiom:
    we derive it in the subtheory [PairT] (only the instances of the
    pairing axiom), which allows transporting it into V(E) through the
    soundness of deduction, with no hypothesis on the frame. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax Deriv Theories.

Definition kpair (x y : term) : term := tpair (tpair x x) (tpair x y).

Definition PairT (φ : form) : Prop := exists x y z, φ = A_pair x y z.

Lemma PairT_closed : closed_sub PairT.
Proof. intros φ σ (x & y & z & ->). exists (subt σ x), (subt σ y), (subt σ z). reflexivity. Qed.

#[export] Instance closed_pairT : Closed PairT := PairT_closed.
#[export] Instance ext_pairT : Ext PairT IZFm := fun φ '(ex_intro _ x (ex_intro _ y (ex_intro _ z E))) =>
  eq_ind_r IZFm (M_pair x y z) E.

Lemma pairT x y z : PairT (A_pair x y z).
Proof. exists x, y, z. reflexivity. Qed.

Local Notation "Γ ⊢p φ" := (prv PairT Γ φ) (at level 70).

Lemma pair_l : [] ⊢p fEps x0 (tpair x0 x1).
Proof. axm (pairT x0 x1 x0). iffr 0. apply p_orI1, p_refl. Qed.

Lemma pair_r : [] ⊢p fEps x1 (tpair x0 x1).
Proof. axm (pairT x0 x1 x1). iffr 0. apply p_orI2, p_refl. Qed.

Lemma sing_eq : [fEps x0 (tpair x1 x1)] ⊢p fEq x0 x1.
Proof. axm (pairT x1 x1 x0). iffm 0; [hyp|]. dor 0; hyp. Qed.

(** Transport of membership along =. *)
Lemma eps_tr_r : [fEq x1 x2; fEps x0 x1] ⊢p fEps x0 x2.
Proof. rew (fEps x1 x0) x1 x2; hyp. Qed.

Lemma kp_inj1 : [fEq (kpair x0 x1) (kpair x2 x3)] ⊢p fEq x0 x2.
Proof.
  unfold kpair.
  cut_ (fEps (tpair x0 x0) (tpair (tpair x2 x2) (tpair x2 x3))).
  { lem eps_tr_r (sl [tpair x0 x0; tpair (tpair x0 x0) (tpair x0 x1); tpair (tpair x2 x2) (tpair x2 x3)]); [hyp|].
    lem pair_l (sl [tpair x0 x0; tpair x0 x1]). }
  axm (pairT (tpair x2 x2) (tpair x2 x3) (tpair x0 x0)). iffm 0; [hyp|]. dor 0.
  - lem sing_eq (sl [x0; x2]).
    lem eps_tr_r (sl [x0; tpair x0 x0; tpair x2 x2]); [hyp|lem pair_l (sl [x0; x0])].
  - lem eq_sym_l (sl [x2; x0]). lem sing_eq (sl [x2; x0]).
    lem eps_tr_r (sl [x2; tpair x2 x3; tpair x0 x0]); [lem eq_sym_l (sl [tpair x0 x0; tpair x2 x3]); hyp|].
    lem pair_l (sl [x2; x3]).
Qed.

(** Sublemma: if x = x' and y' = x, then y = y'. *)
Lemma kp_aux : [fEq x0 x2; fEq x3 x0; fEq (kpair x0 x1) (kpair x2 x3)] ⊢p fEq x1 x3.
Proof.
  unfold kpair.
  cut_ (fEps (tpair x0 x1) (tpair (tpair x2 x2) (tpair x2 x3))).
  { lem eps_tr_r (sl [tpair x0 x1; tpair (tpair x0 x0) (tpair x0 x1); tpair (tpair x2 x2) (tpair x2 x3)]); [hyp|].
    lem pair_r (sl [tpair x0 x0; tpair x0 x1]). }
  axm (pairT (tpair x2 x2) (tpair x2 x3) (tpair x0 x1)). iffm 0; [hyp|].
  cut_ (fEq x2 x3).
  { lem eq_trans_l (sl [x2; x0; x3]); [lem eq_sym_l (sl [x0; x2]); hyp|lem eq_sym_l (sl [x3; x0]); hyp]. }
  dor 1.
  - (* {x, y} = {x', x'} : y = x' = y' *)
    lem eq_trans_l (sl [x1; x2; x3]); [|hyp].
    lem sing_eq (sl [x1; x2]). lem eps_tr_r (sl [x1; tpair x0 x1; tpair x2 x2]); [hyp|lem pair_r (sl [x0; x1])].
  - (* {x, y} = {x', y'} : y = x' or y = y' *)
    cut_ (fEps x1 (tpair x2 x3)); [lem eps_tr_r (sl [x1; tpair x0 x1; tpair x2 x3]); [hyp|lem pair_r (sl [x0; x1])]|].
    axm (pairT x2 x3 x1). iffm 0; [hyp|]. dor 0; [|hyp].
    lem eq_trans_l (sl [x1; x2; x3]); hyp.
Qed.

Lemma kp_inj2 : [fEq (kpair x0 x1) (kpair x2 x3)] ⊢p fEq x1 x3.
Proof.
  unfold kpair. haveL kp_inj1 (sl [x0; x1; x2; x3]); [hyp|].
  cut_ (fEps (tpair x2 x3) (tpair (tpair x0 x0) (tpair x0 x1))).
  { lem eps_tr_r (sl [tpair x2 x3; tpair (tpair x2 x2) (tpair x2 x3); tpair (tpair x0 x0) (tpair x0 x1)]);
      [lem eq_sym_l (sl [tpair (tpair x0 x0) (tpair x0 x1); tpair (tpair x2 x2) (tpair x2 x3)]); hyp|].
    lem pair_r (sl [tpair x2 x2; tpair x2 x3]). }
  axm (pairT (tpair x0 x0) (tpair x0 x1) (tpair x2 x3)). iffm 0; [hyp|]. dor 0.
  - (* {x', y'} = {x, x} : y' = x *)
    lem kp_aux (sl [x0; x1; x2; x3]); [hyp| |hyp].
    lem sing_eq (sl [x3; x0]). lem eps_tr_r (sl [x3; tpair x2 x3; tpair x0 x0]); [hyp|lem pair_r (sl [x2; x3])].
  - (* {x', y'} = {x, y} *)
    cut_ (fEps x3 (tpair x0 x1)); [lem eps_tr_r (sl [x3; tpair x2 x3; tpair x0 x1]); [hyp|lem pair_r (sl [x2; x3])]|].
    axm (pairT x0 x1 x3). iffm 0; [hyp|]. dor 0.
    + lem kp_aux (sl [x0; x1; x2; x3]); hyp.
    + lem eq_sym_l (sl [x3; x1]). hyp.
Qed.

Lemma kp_inj : [] ⊢p fImp (fEq (kpair x0 x1) (kpair x2 x3)) (fAnd (fEq x0 x2) (fEq x1 x3)).
Proof. intro_imp. split_and; [lem kp_inj1 (sl [x0; x1; x2; x3])|lem kp_inj2 (sl [x0; x1; x2; x3])]; hyp. Qed.
