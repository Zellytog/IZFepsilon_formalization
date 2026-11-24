(** * Total replacement, in IZF (value of {ψ(α) | α ε a}) *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax ISyntax ILogic Graph GSubst ED.

(** P(β, α) placed at depth d: β ↦ a, α ↦ b, parameters shifted by d. *)
Definition rp (a b d : nat) : nat -> nat :=
  fun n => match n with 0 => a | 1 => b | S (S k) => d + k end.

Lemma iren_iren ξ ζ φ : iren ξ (iren ζ φ) = iren (fun k => ξ (ζ k)) φ.
Proof. apply iren_comp. reflexivity. Qed.

Lemma i_nthc Γ n A B : nth_error Γ n = Some A -> A = B -> Γ ⊢i B.
Proof. intros H <-. exact (i_nth _ _ _ _ H). Qed.

Ltac ieq := unfold iinst; rewrite ?iren_iren; icong;
  try (apply iren_ext; let k := fresh "k" in intros k; destruct k as [|[|[|[|[|[|[|k]]]]]]]; reflexivity);
  try reflexivity.
Ltac phyp := let rec go n :=
  lazymatch n with 25 => fail | _ => first [eapply (i_nthc _ n); [reflexivity|solve [ieq]] | go (S n)] end
  in go 0.

Lemma repl_ex u (P : iform) :
  [] ⊢i iEx (iAll (iIff (iMem 0 1)
    (iAnd (iAll (iImp (iMem 0 (3 + u)) (iEx (iAnd (iren (rp 0 1 4) P) (iAll (iImp (iren (rp 0 2 5) P) (iEq 0 1)))))))
          (iEx (iAnd (iMem 0 (3 + u)) (iren (rp 1 0 3) P)))))).
Proof.
  iax (I_sep (iAll (iImp (iMem 0 (2 + u)) (iEx (iAnd (iren (rp 0 1 3) P) (iAll (iImp (iren (rp 0 2 4) P) (iEq 0 1))))))) u).
  idex 0.
  (* s = 0 *)
  iax (I_coll (iren (rp 0 1 3) P) 0). imp 0.
  { iintro_all. apply i_impI. ispec 2 0. iffm 0; [ihyp|]. idand 0. ispec 1 0. imp 0; [ihyp|].
    idex 0. idand 0. iexists 0. phyp. }
  idex 0.
  (* b = 0, s = 1 *)
  iax (I_sep (iAnd (iAll (iImp (iMem 0 (4 + u)) (iEx (iAnd (iren (rp 0 1 5) P) (iAll (iImp (iren (rp 0 2 6) P) (iEq 0 1)))))))
                   (iEx (iAnd (iMem 0 (4 + u)) (iren (rp 1 0 4) P)))) 0).
  idex 0. iexists 0. iintro_all. apply i_iffI.
  - ispec 1 0. iffm 0; [ihyp|]. idand 0. idand 1. apply i_andI; phyp.
  - idand 0. ispec 3 0. iffr 0. apply i_andI; [|apply i_andI; phyp].
    idex 2. idand 0. ispec 4 0. imp 0; [ihyp|]. idex 0. idand 0.
    icut (iMem 1 5); [ispec 17 1; iffr 0; apply i_andI; [ihyp|phyp]|].
    ispec 15 1. imp 0; [ihyp|]. idex 0. idand 0.
    ispec 7 3. imp 0; [phyp|]. ispec 9 0. imp 0; [phyp|].
    irew (iMem 0 6) 0 3; [eapply ieq_trans_t; [ihyp|apply ieq_sym_t; ihyp]|ihyp].
Qed.

Lemma ED_repl a ψ : (forall ρ Γ, Γ ⊢i iEx (D a (sh 1 ρ) 0)) -> forall ρ Γ, Γ ⊢i iEx (D (trepl a ψ) (sh 1 ρ) 0).
Proof.
  intros Ha.
  apply (ED_un a (trepl a ψ) (fun ρ u =>
    iAnd (iAll (iImp (iMem 0 (S (S u))) (iEx (iAnd (T ψ (0 .: 1 .: sh 3 ρ)) (iAll (iImp (T ψ (0 .: 2 .: sh 4 ρ)) (iEq 0 1)))))))
         (iEx (iAnd (iMem 0 (S (S u))) (T ψ (1 .: 0 .: sh 2 ρ)))))); [exact Ha| |].
  - intros Γ ρ u p H. eapply ii_trans; [apply (char1 _ _ _ _ _ H)|]. cbn [iren]. rewrite !Tiren.
    iicong; apply ii_T_ext; pwsolve.
  - intros Γ ρ u. eapply iprv_weak; [eapply i_conv; [|apply (repl_ex u (T ψ (0 .: 1 .: sh 2 ρ)))]|intros ? []].
    rewrite !Tiren. tcong.
Qed.

(** Every term has a value, which is unique, in IZF. *)
Theorem HED t : forall ρ Γ, Γ ⊢i iEx (D t (sh 1 ρ) 0).
Proof.
  induction t.
  - apply ED_var.
  - apply ED_empty.
  - apply ED_omega.
  - apply ED_pair; assumption.
  - apply ED_union; assumption.
  - apply ED_pow; assumption.
  - apply ED_sep; assumption.
  - apply ED_repl; assumption.
Qed.
