(** * Theorem 8: definitions by recursion on ω, inside IZFε

    Statement (free variables g, a, X): if a ε X and g is the graph of a
    function ω × X → X,
      ∀n ε ω. ∀x ε X. ∃!y. y ε X ∧ ⟨⟨n, x⟩, y⟩ ε g,
    then there is f ⊆ ω × X, the graph of a function ω → X, such that
    ⟨0, a⟩ ε f and ⟨n, x⟩ ε f ∧ ⟨⟨n, x⟩, y⟩ ε g ⇒ ⟨S n, y⟩ ε f; in other
    words rec(0) = a and rec(S n) = g⟨n, rec(n)⟩.

    Proof of the paper (Knaster–Tarski): f is the least subset of ω × X
    closed under the two rules, obtained by separation
      f ≜ {p ε ω × X | ∀A. Cl(A) ⇒ p ε A}
    (impredicative separation, without going through P(ω × X)). By
    minimality, f is closed and every pair of f comes from one of the two
    rules; functionality is proven by induction (Theorem 7), with S
    injective and S n ≠ 0. ω × X ≜ ⋃{{⟨n, x⟩ | x ε X} | n ε ω} is built by
    replacement. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax Deriv Theories Basic Arith Pairs.

Local Notation "Γ ⊢e φ" := (prv IZFe Γ φ) (at level 70).

Definition sh (k : nat) (t : term) : term := rent (Nat.add k) t.

(** ω × X *)
Definition tW (X : term) : term :=
  tunion (trepl tomega (fEq x0 (trepl (sh 2 X) (fEq x0 (kpair x3 x1))))).

(** Premise of replacement for ψ(β, α) ≜ β = t(α). *)
Ltac exu := intro_all; intro_imp; unfold fExU; cbn;
  match goal with |- prv _ _ (fEx (fAnd (fEq x0 ?t) _)) => exists_ (subt (fun k => tvar (pred k)) t) end;
  split_and; [apply p_refl|intro_all; intro_imp; hyp].

Lemma mem_W : [] ⊢e fIff (fEps x0 (tW x1)) (fEx (fAnd (fEps x0 tomega) (fEx (fAnd (fEps x0 x3) (fEq x2 (kpair x1 x0)))))).
Proof.
  unfold tW. split_iff.
  - axm (M_union (trepl tomega (fEq x0 (trepl (sh 2 x1) (fEq x0 (kpair x3 x1))))) x0). iffm 0; [hyp|].
    dex 0. dand 0.
    axm (E_repl (fEq x0 (trepl x4 (fEq x0 (kpair x3 x1)))) tomega x0). mp 0; [exu|].
    iffm 0; [hyp|]. dex 0. dand 0.
    cut_ (fEps x2 (trepl x3 (fEq x0 (kpair x2 x1)))); [rew (fEps x3 x0) x1 (trepl x3 (fEq x0 (kpair x2 x1))); hyp|].
    axm (E_repl (fEq x0 (kpair x2 x1)) x3 x2). mp 0; [exu|]. iffm 0; [hyp|]. dex 0. dand 0.
    exists_ x1. split_and; [hyp|]. exists_ x0. split_and; hyp.
  - dex 0. dand 0. dex 1. dand 0.
    axm (M_union (trepl tomega (fEq x0 (trepl x5 (fEq x0 (kpair x3 x1))))) x2). iffr 0.
    exists_ (trepl x3 (fEq x0 (kpair x3 x1))). split_and.
    + axm (E_repl (fEq x0 (trepl x5 (fEq x0 (kpair x3 x1)))) tomega (trepl x3 (fEq x0 (kpair x3 x1)))).
      mp 0; [exu|]. iffr 0. exists_ x1. split_and; [hyp|apply p_refl].
    + axm (E_repl (fEq x0 (kpair x3 x1)) x3 x2). mp 0; [exu|]. iffr 0. exists_ x0. split_and; hyp.
Qed.

#[local] Instance ext_pe : Ext PairT IZFe := fun φ H => E_base _ (ext_pairT φ H).

Lemma zero_omega : [] ⊢e fEps tempty tomega.
Proof. axm (M_omega tempty). iffr 0. apply p_orI1, p_refl. Qed.

Lemma suc_omega : [fEps x0 tomega] ⊢e fEps (tsuc x0) tomega.
Proof. axm (M_omega (tsuc x0)). iffr 0. apply p_orI2. exists_ x0. split_and; [hyp|apply p_refl]. Qed.

Lemma W_intro : [fEps x0 tomega; fEps x1 x2] ⊢e fEps (kpair x0 x1) (tW x2).
Proof.
  haveL mem_W (sl [kpair x0 x1; x2]). iffr 0. exists_ x0. split_and; [hyp|]. exists_ x1. split_and; [hyp|apply p_refl].
Qed.

Lemma W_pair : [fEps (kpair x0 x1) (tW x2)] ⊢e fAnd (fEps x0 tomega) (fEps x1 x2).
Proof.
  haveL mem_W (sl [kpair x0 x1; x2]). iffm 0; [hyp|]. dex 0. dand 0. dex 1. dand 0.
  haveL kp_inj1 (sl [x2; x3; x1; x0]); [hyp|]. haveL kp_inj2 (sl [x2; x3; x1; x0]); [hyp|].
  split_and.
  - rew (fEps x0 tomega) x1 x2; [lem eq_sym_l (sl [x2; x1]); hyp|hyp].
  - rew (fEps x0 x5) x0 x3; [lem eq_sym_l (sl [x3; x0]); hyp|hyp].
Qed.

(** ** The successor *)

Lemma suc_ne0 : [fEq (tsuc x0) tempty] ⊢e fBot.
Proof.
  cut_ (fEps x0 tempty); [rew (fEps x1 x0) (tsuc x0) tempty; [hyp|lem eps_suc (sl [x0])]|].
  axm (M_empty x0). app 0. hyp.
Qed.

Lemma suc_el : [fEps x0 (tsuc x1)] ⊢e fOr (fEps x0 x1) (fEq x0 x1).
Proof.
  unfold tsuc. axm (M_union (tpair x1 (tpair x1 x1)) x0). iffm 0; [hyp|]. dex 0. dand 0.
  axm (M_pair x2 (tpair x2 x2) x0). iffm 0; [hyp|]. dor 0.
  - apply p_orI1. rew (fEps x2 x0) x0 x2; hyp.
  - apply p_orI2. lem sing_eq (sl [x1; x2]). rew (fEps x2 x0) x0 (tpair x2 x2); hyp.
Qed.

Lemma no2cycle : [fEps x0 x1; fEps x1 x0] ⊢e fBot.
Proof.
  axm (M_ind (fAll (fImp (fEps x1 x0) (fImp (fEps x0 x1) fBot)))). mp 0.
  - intro_all. intro_imp. intro_all. intro_imp. intro_imp.
    spec 2 x0. mp 0; [hyp|]. spec 0 x1. app2 0; hyp.
  - spec 0 x0. spec 0 x1. app2 0; hyp.
Qed.

Lemma suc_inj : [fEq (tsuc x0) (tsuc x1)] ⊢e fEq x0 x1.
Proof.
  cut_ (fEps x0 (tsuc x1)); [rew (fEps x1 x0) (tsuc x0) (tsuc x1); [hyp|lem eps_suc (sl [x0])]|].
  cut_ (fEps x1 (tsuc x0)).
  { rew (fEps x2 x0) (tsuc x1) (tsuc x0); [lem eq_sym_l (sl [tsuc x0; tsuc x1]); hyp|lem eps_suc (sl [x1])]. }
  haveL suc_el (sl [x0; x1]); [hyp|]. haveL suc_el (sl [x1; x0]); [hyp|].
  dor 1; [|hyp]. dor 1; [|lem eq_sym_l (sl [x1; x0]); hyp].
  apply p_botE. lem no2cycle (sl [x0; x1]); hyp.
Qed.

(** ** The relation f: the least closed subset of ω × X *)

(** Cl(A): ⟨0, a⟩ ε A and ∀n x y. n ε ω ⇒ x ε X ⇒ ⟨n, x⟩ ε A ⇒ ⟨⟨n, x⟩, y⟩ ε g ⇒ ⟨S n, y⟩ ε A. *)
Definition Cl (A g a X : term) : form :=
  fAnd (fEps (kpair tempty a) A)
       (fAll (fAll (fAll (fImp (fEps x2 tomega) (fImp (fEps x1 (sh 3 X))
          (fImp (fEps (kpair x2 x1) (sh 3 A)) (fImp (fEps (kpair (kpair x2 x1) x0) (sh 3 g))
             (fEps (kpair (tsuc x2) x0) (sh 3 A))))))))).

Definition Phi (g a X : term) : form := fAll (fImp (Cl x0 (sh 2 g) (sh 2 a) (sh 2 X)) (fEps x1 x0)).

(** f ≜ {p ε ω × X | ∀A. Cl(A) ⇒ p ε A} *)
Definition tf (g a X : term) : term := tsep (tW X) (Phi g a X).

(** g is the graph of a function ω × X → X. *)
Definition Hg (g X : term) : form :=
  fAll (fAll (fImp (fEps x1 tomega) (fImp (fEps x0 (sh 2 X))
    (fEx (fAnd (fEps x0 (sh 3 X)) (fAnd (fEps (kpair (kpair x2 x1) x0) (sh 3 g))
       (fAll (fImp (fEps (kpair (kpair x3 x2) x0) (sh 4 g)) (fEq x0 x1))))))))).

(** Variables: g = 0, a = 1, X = 2. *)

Lemma f_zero : [fEps x1 x2] ⊢e fEps (kpair tempty x1) (tf x0 x1 x2).
Proof.
  axm (M_sep (Phi x0 x1 x2) (tW x2) (kpair tempty x1)). iffr 0. split_and.
  - lem W_intro (sl [tempty; x1; x2]); [lem zero_omega (sl [])|hyp].
  - intro_all. intro_imp. dand 0. hyp.
Qed.

Lemma f_step : [Hg x0 x2] ⊢e fAll (fAll (fAll (fImp (fEps x2 tomega)
  (fImp (fEps (kpair x2 x1) (tf x3 x4 x5)) (fImp (fEps (kpair (kpair x2 x1) x0) x3)
     (fEps (kpair (tsuc x2) x0) (tf x3 x4 x5))))))).
Proof.
  do 3 intro_all. do 3 intro_imp.
  axm (M_sep (Phi x3 x4 x5) (tW x5) (kpair x2 x1)). iffm 0; [hyp|]. dand 0.
  haveL W_pair (sl [x2; x1; x5]); [hyp|]. dand 0.
  spec 10 x2. spec 0 x1. mp 0; [hyp|]. mp 0; [hyp|]. dex 0. dand 0. dand 1.
  spec 1 x1. mp 0; [hyp|].
  axm (M_sep (Phi x4 x5 x6) (tW x6) (kpair (tsuc x3) x1)). iffr 0. split_and.
  - lem W_intro (sl [tsuc x3; x1; x6]); [lem suc_omega (sl [x3]); hyp|].
    rew (fEps x0 x7) x0 x1; [lem eq_sym_l (sl [x1; x0]); hyp|hyp].
  - intro_all. intro_imp. cut_ (fEps (kpair x4 x3) x0); [spec 17 x0; mp 0; [hyp|hyp]|].
    dand 1. spec 1 x4. spec 0 x3. spec 0 x2. mp 0; [hyp|]. mp 0; [hyp|]. mp 0; [hyp|]. mp 0; [hyp|]. hyp.
Qed.

(** ** Inversion: every pair of f comes from one of the two rules *)

(** Ψ(p) : p = ⟨0, a⟩ ∨ ∃m x' y. p = ⟨S m, y⟩ ∧ m ε ω ∧ ⟨m, x'⟩ ε f ∧ ⟨⟨m, x'⟩, y⟩ ε g. *)
Definition Psi (g a X : term) : form :=
  fOr (fEq x0 (kpair tempty (sh 1 a)))
      (fEx (fEx (fEx (fAnd (fEq x3 (kpair (tsuc x2) x0)) (fAnd (fEps x2 tomega)
         (fAnd (fEps (kpair x2 x1) (tf (sh 4 g) (sh 4 a) (sh 4 X))) (fEps (kpair (kpair x2 x1) x0) (sh 4 g)))))))).

Lemma clA : [fEps x1 x2; Hg x0 x2] ⊢e Cl (tsep (tf x0 x1 x2) (Psi x0 x1 x2)) x0 x1 x2.
Proof.
  unfold Cl at 1. split_and.
  - axm (M_sep (Psi x0 x1 x2) (tf x0 x1 x2) (kpair tempty x1)). iffr 0. split_and.
    + lem f_zero (sl [x0; x1; x2]). hyp.
    + apply p_orI1, p_refl.
  - do 3 intro_all. do 4 intro_imp.
    cut_ (fEps (kpair x2 x1) (tf x3 x4 x5)).
    { axm (M_sep (Psi x3 x4 x5) (tf x3 x4 x5) (kpair x2 x1)). iffm 0; [hyp|]. dand 0. hyp. }
    haveL f_step (sl [x3; x4; x5]); [hyp|]. spec 0 x2. spec 0 x1. spec 0 x0.
    mp 0; [hyp|]. mp 0; [hyp|]. mp 0; [hyp|].
    axm (M_sep (Psi x3 x4 x5) (tf x3 x4 x5) (kpair (tsuc x2) x0)). iffr 0. split_and; [hyp|].
    apply p_orI2. exists_ x2. exists_ x1. exists_ x0.
    split_and; [apply p_refl|split_and; [hyp|split_and; hyp]].
Qed.

Lemma f_inv : [fEps x1 x2; Hg x0 x2] ⊢e fAll (fAll (fImp (fEps (kpair x1 x0) (tf x2 x3 x4))
  (fOr (fAnd (fEq x1 tempty) (fEq x0 x3))
       (fEx (fEx (fAnd (fEps x1 tomega) (fAnd (fEps (kpair x1 x0) (tf x4 x5 x6))
          (fAnd (fEps (kpair (kpair x1 x0) x2) x4) (fEq x3 (tsuc x1)))))))))).
Proof.
  do 2 intro_all. intro_imp.
  haveL clA (sl [x2; x3; x4]); [hyp|hyp|].
  axm (M_sep (Phi x2 x3 x4) (tW x4) (kpair x1 x0)). iffm 0; [hyp|]. dand 0.
  spec 1 (tsep (tf x2 x3 x4) (Psi x2 x3 x4)). mp 0; [hyp|].
  axm (M_sep (Psi x2 x3 x4) (tf x2 x3 x4) (kpair x1 x0)). iffm 0; [hyp|]. dand 0. dor 1.
  - apply p_orI1. haveL kp_inj1 (sl [x1; x0; tempty; x3]); [hyp|]. haveL kp_inj2 (sl [x1; x0; tempty; x3]); [hyp|].
    split_and; hyp.
  - dex 0. dex 0. dex 0. dand 0. dand 1. dand 1.
    haveL kp_inj1 (sl [x4; x3; tsuc x2; x0]); [hyp|]. haveL kp_inj2 (sl [x4; x3; tsuc x2; x0]); [hyp|].
    apply p_orI2. exists_ x2. exists_ x1. split_and; [hyp|split_and; [hyp|split_and; [|hyp]]].
    rew (fEps (kpair (kpair x3 x2) x0) x6) x0 x3; [lem eq_sym_l (sl [x3; x0]); hyp|hyp].
Qed.

(** ** The theorem *)

(** Rec(f), with f = 0, g = 1, a = 2, X = 3:
    (A) f ⊆ ω × X;
    (B) ∀n ε ω. ∃!y. y ε X ∧ ⟨n, y⟩ ε f;
    (C) ⟨0, a⟩ ε f;
    (D) ⟨n, x⟩ ε f ∧ ⟨⟨n, x⟩, y⟩ ε g ⇒ ⟨S n, y⟩ ε f, for n ε ω. *)
Definition Rec : form :=
  fAnd (fAll (fImp (fEps x0 x1) (fEx (fEx (fAnd (fEps x1 tomega) (fAnd (fEps x0 x6) (fEq x2 (kpair x1 x0))))))))
 (fAnd (fAll (fImp (fEps x0 tomega) (fEx (fAnd (fEps x0 x5) (fAnd (fEps (kpair x1 x0) x2)
          (fAll (fImp (fEps (kpair x2 x0) x3) (fEq x0 x1))))))))
 (fAnd (fEps (kpair tempty x2) x0)
       (fAll (fAll (fAll (fImp (fEps x2 tomega) (fImp (fEps (kpair x2 x1) x3)
          (fImp (fEps (kpair (kpair x2 x1) x0) x4) (fEps (kpair (tsuc x2) x0) x3))))))))).

(** φ(n) for Theorem 7 (n = 0, g = 1, a = 2, X = 3). *)
Definition Fn : form :=
  fEx (fAnd (fEps x0 x4) (fAnd (fEps (kpair x1 x0) (tf x2 x3 x4))
    (fAll (fImp (fEps (kpair x2 x0) (tf x3 x4 x5)) (fEq x0 x1))))).

Theorem thm8 : [fEps x1 x2; Hg x0 x2] ⊢e fEx Rec.
Proof.
  exists_ (tf x0 x1 x2). split_and; [|split_and; [|split_and]].
  - intro_all. intro_imp.
    axm (M_sep (Phi x1 x2 x3) (tW x3) x0). iffm 0; [hyp|]. dand 0.
    haveL mem_W (sl [x0; x3]). iffm 0; [hyp|]. dex 0. dand 0. dex 1. dand 0.
    exists_ x1. exists_ x0. split_and; [hyp|split_and; hyp].
  - cut_ (ind_omega Fn); [eapply prv_mono; [exact IZFm_IZFe|eapply prv_weak; [apply thm7|intros ? []]]|].
    mp 0; [|mp 0; [|hyp]].
    + exists_ x1. split_and; [hyp|split_and; [lem f_zero (sl [x0; x1; x2]); hyp|]].
      intro_all. intro_imp. haveL f_inv (sl [x1; x2; x3]); [hyp|hyp|].
      spec 0 tempty. spec 0 x0. mp 0; [hyp|]. dor 0.
      * dand 0. hyp.
      * dex 0. dex 0. dand 0. dand 1. dand 1.
        apply p_botE. lem suc_ne0 (sl [x1]). lem eq_sym_l (sl [tempty; tsuc x1]). hyp.
    + intro_all. intro_imp. intro_imp. dex 0. dand 0. dand 1.
      spec 10 x1. spec 0 x0. mp 0; [hyp|]. mp 0; [hyp|]. dex 0. dand 0. dand 1.
      exists_ x0. split_and; [hyp|split_and].
      * haveL f_step (sl [x3; x4; x5]); [hyp|]. spec 0 x2. spec 0 x1. spec 0 x0.
        mp 0; [hyp|]. mp 0; [hyp|]. mp 0; [hyp|]. hyp.
      * intro_all. intro_imp. haveL f_inv (sl [x4; x5; x6]); [hyp|hyp|].
        spec 0 (tsuc x3). spec 0 x0. mp 0; [hyp|]. dor 0.
        -- dand 0. apply p_botE. lem suc_ne0 (sl [x3]). hyp.
        -- dex 0. dex 0. dand 0. dand 1. dand 1.
           haveL suc_inj (sl [x5; x1]); [hyp|].
           cut_ (fEps (kpair x5 x0) (tf x6 x7 (tvar 8))).
           { rew (fEps (kpair x0 x1) (tf x7 (tvar 8) (tvar 9))) x1 x5; [lem eq_sym_l (sl [x5; x1]); hyp|hyp]. }
           spec 26 x0. mp 0; [hyp|]. spec 19 x2. app 0.
           cut_ (fEps (kpair (kpair x5 x0) x2) x6).
           { rew (fEps (kpair (kpair x0 x1) x3) x7) x1 x5; [lem eq_sym_l (sl [x5; x1]); hyp|hyp]. }
           rew (fEps (kpair (kpair x6 x0) x3) x7) x0 x4; hyp.
  - lem f_zero (sl [x0; x1; x2]). hyp.
  - lem f_step (sl [x0; x1; x2]). hyp.
Qed.

(** Closed form: ∀X a g. a ε X ⇒ g : ω × X → X ⇒ ∃f. Rec(f). *)
Corollary thm8_closed : [] ⊢e fAll (fAll (fAll (fImp (fEps x1 x2) (fImp (Hg x0 x2) (fEx Rec))))).
Proof. do 3 intro_all. do 2 intro_imp. lem thm8 (sl [x0; x1; x2]); hyp. Qed.
