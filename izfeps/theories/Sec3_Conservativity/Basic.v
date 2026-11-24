(** * Lemma 10: the behaviour of ∈ in IZF⁻ε *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Syntax Deriv Theories.

Notation "Γ ⊢m φ" := (prv IZFm Γ φ) (at level 70).

(** ** 10.1: x ⊆ x, by ε-induction *)

Lemma sub_refl : [] ⊢m fAll (fSub x0 x0).
Proof.
  axm (M_ind (fSub x0 x0)). app 0. intro_all. intro_imp.
  axm (M_sub x0 x0). iffr 0. intro_all. intro_imp.
  axm (M_mem x0 x1). iffr 0. exists_ x0. split_and; [|hyp].
  axm (M_eqv x0 x0). iffr 0. split_and; spec 4 x0; app 0; hyp.
Qed.

Lemma sub_refl1 : [] ⊢m fSub x0 x0.
Proof. haveL sub_refl (sl []). spec 0 x0. hyp. Qed.

Lemma eqv_refl : [] ⊢m fEqv x0 x0.
Proof. axm (M_eqv x0 x0). iffr 0. split_and; lem sub_refl1 (sl [x0]). Qed.

Lemma eqv_l : [fEqv x0 x1] ⊢m fSub x0 x1.
Proof. axm (M_eqv x0 x1). iffm 0; [hyp|]. dand 0. hyp. Qed.

Lemma eqv_r : [fEqv x0 x1] ⊢m fSub x1 x0.
Proof. axm (M_eqv x0 x1). iffm 0; [hyp|]. dand 0. hyp. Qed.

Lemma eqv_intro : [fSub x0 x1; fSub x1 x0] ⊢m fEqv x0 x1.
Proof. axm (M_eqv x0 x1). iffr 0. split_and; hyp. Qed.

(** ** 10.2: a ε x ⇒ a ∈ x *)

Lemma eps_mem : [fEps x0 x1] ⊢m fMem x0 x1.
Proof. axm (M_mem x0 x1). iffr 0. exists_ x0. split_and; [|hyp]. lem eqv_refl (sl [x0]). Qed.

(** ** 10.3: (∀a. a ∈ x ⇒ a ∈ y) ⇒ x ⊆ y *)

Lemma sub_of_mem : [fAll (fImp (fMem x0 x1) (fMem x0 x2))] ⊢m fSub x0 x1.
Proof.
  axm (M_sub x0 x1). iffr 0. intro_all. intro_imp.
  spec 2 x0. app 0. lem eps_mem (sl [x0; x1]). hyp.
Qed.

(** Unfolding ⊆ and ∈. *)
Lemma sub_elim : [fSub x1 x2; fEps x0 x1] ⊢m fMem x0 x2.
Proof. axm (M_sub x1 x2). iffm 0; [hyp|]. spec 0 x0. app 0. hyp. Qed.

(** ** 10.4: x ⊆ y ⇒ (∀a. a ∈ y ⇒ a ∈ z) ⇒ x ⊆ z *)

Lemma sub_mem_trans : [fSub x0 x1; fAll (fImp (fMem x0 x2) (fMem x0 x3))] ⊢m fSub x0 x2.
Proof.
  axm (M_sub x0 x2). iffr 0. intro_all. intro_imp.
  spec 3 x0. app 0. lem sub_elim (sl [x0; x1; x2]); hyp.
Qed.

(** ** 10.5: x ⊆ y ⇒ y ⊆ z ⇒ x ⊆ z, by ε-induction on y *)

Definition Φtrans : form := fAll (fAll (fImp (fSub x1 x2) (fImp (fSub x2 x0) (fSub x1 x0)))).

Lemma sub_trans : [] ⊢m fAll Φtrans.
Proof.
  axm (M_ind Φtrans). app 0. intro_all. intro_imp.
  intro_all. intro_all. intro_imp. intro_imp.
  (* z = 0, x = 1, y = 2 ; Γ = [y ⊆ z; x ⊆ y; IH; …] *)
  keep [0; 1; 2].
  axm (M_sub x1 x0). iffr 0. intro_all. intro_imp.
  (* a = 0, z = 1, x = 2, y = 3 ; Γ = [a ε x; _; y ⊆ z; x ⊆ y; IH] *)
  keep [0; 2; 3; 4].
  (* a ∈ y *)
  cut_ (fMem x0 x3); [lem sub_elim (sl [x0; x2; x3]); hyp|].
  axm (M_mem x0 x3). iffm 0; [hyp|]. dex 0. dand 0.
  (* a' = 0, a = 1, z = 2, x = 3, y = 4 *)
  keep [0; 1; 7; 9].
  cut_ (fMem x0 x2); [lem sub_elim (sl [x0; x4; x2]); hyp|].
  axm (M_mem x0 x2). iffm 0; [hyp|]. dex 0. dand 0.
  (* a'' = 0, a' = 1, a = 2, z = 3, y = 5 *)
  keep [0; 1; 6; 7; 9].
  axm (M_mem x2 x3). iffr 0. exists_ x0. split_and; [|hyp].
  (* IH at a' *)
  spec 5 x1. mp 0; [hyp|].
  (* Γ = [Φ(a'); _; a' ≃ a''; a'' ε z; a ≃ a'; a' ε y; IH] *)
  lem eqv_intro (sl [x2; x0]).
  - spec 0 x2. spec 0 x0. app2 0; [lem eqv_l (sl [x2; x1]); hyp|lem eqv_l (sl [x1; x0]); hyp].
  - spec 0 x0. spec 0 x2. app2 0; [lem eqv_r (sl [x1; x0]); hyp|lem eqv_r (sl [x2; x1]); hyp].
Qed.

Lemma sub_trans1 : [fSub x0 x1; fSub x1 x2] ⊢m fSub x0 x2.
Proof. haveL sub_trans (sl []). spec 0 x1. spec 0 x0. spec 0 x2. app2 0; hyp. Qed.

Lemma eqv_sym : [fEqv x0 x1] ⊢m fEqv x1 x0.
Proof. lem eqv_intro (sl [x1; x0]); [lem eqv_r (sl [x0; x1])|lem eqv_l (sl [x0; x1])]; hyp. Qed.

Lemma eqv_trans : [fEqv x0 x1; fEqv x1 x2] ⊢m fEqv x0 x2.
Proof.
  lem eqv_intro (sl [x0; x2]).
  - lem sub_trans1 (sl [x0; x1; x2]); [lem eqv_l (sl [x0; x1])|lem eqv_l (sl [x1; x2])]; hyp.
  - lem sub_trans1 (sl [x2; x1; x0]); [lem eqv_r (sl [x1; x2])|lem eqv_r (sl [x0; x1])]; hyp.
Qed.

(** ** 10.6: x ⊆ y ⇔ (∀a. a ∈ x ⇒ a ∈ y) *)

Lemma mem_sub : [fMem x0 x1; fSub x1 x2] ⊢m fMem x0 x2.
Proof.
  axm (M_mem x0 x1). iffm 0; [hyp|]. dex 0. dand 0.
  (* a' = 0, a = 1, x = 2, y = 3 ; Γ = [a ≃ a'; a' ε x; …; x ⊆ y] *)
  cut_ (fMem x0 x3); [lem sub_elim (sl [x0; x2; x3]); hyp|].
  axm (M_mem x0 x3). iffm 0; [hyp|]. dex 0. dand 0.
  (* a'' = 0, a' = 1, a = 2, y = 4 *)
  axm (M_mem x2 x4). iffr 0. exists_ x0. split_and; [|hyp].
  lem eqv_trans (sl [x2; x1; x0]); hyp.
Qed.

Lemma sub_iff : [] ⊢m fIff (fSub x0 x1) (fAll (fImp (fMem x0 x1) (fMem x0 x2))).
Proof.
  split_iff.
  - intro_all. intro_imp. lem mem_sub (sl [x0; x1; x2]); hyp.
  - lem sub_of_mem (sl [x0; x1]). hyp.
Qed.

(** ∈ is compatible with ≃ on the left. *)
Lemma mem_eqv_l : [fEqv x0 x1; fMem x0 x2] ⊢m fMem x1 x2.
Proof.
  axm (M_mem x0 x2). iffm 0; [hyp|]. dex 0. dand 0.
  (* a' = 0, x = 1, y = 2, z = 3 *)
  axm (M_mem x2 x3). iffr 0. exists_ x0. split_and; [|hyp].
  lem eqv_trans (sl [x2; x1; x0]); [lem eqv_sym (sl [x1; x2])|]; hyp.
Qed.

Lemma mem_cong : [fEqv x0 x1; fEqv x2 x3; fMem x0 x2] ⊢m fMem x1 x3.
Proof.
  cut_ (fMem x1 x2); [lem mem_eqv_l (sl [x0; x1; x2]); hyp|].
  lem mem_sub (sl [x1; x2; x3]); [hyp|lem eqv_l (sl [x2; x3]); hyp].
Qed.

Lemma sub_cong : [fEqv x0 x1; fEqv x2 x3; fSub x0 x2] ⊢m fSub x1 x3.
Proof.
  lem sub_trans1 (sl [x1; x0; x3]); [lem eqv_r (sl [x0; x1]); hyp|].
  lem sub_trans1 (sl [x0; x2; x3]); [hyp|lem eqv_l (sl [x2; x3]); hyp].
Qed.

Lemma eqv_cong : [fEqv x0 x1; fEqv x2 x3; fEqv x0 x2] ⊢m fEqv x1 x3.
Proof.
  lem eqv_trans (sl [x1; x0; x3]); [lem eqv_sym (sl [x0; x1]); hyp|].
  lem eqv_trans (sl [x0; x2; x3]); hyp.
Qed.

Lemma eqv_refl_t Γ t : Γ ⊢m fEqv t t.
Proof. lem eqv_refl (sl [t]). Qed.

Lemma eqv_sym_t Γ s t : Γ ⊢m fEqv s t -> Γ ⊢m fEqv t s.
Proof. intros H. lem eqv_sym (sl [s; t]). exact H. Qed.

Lemma eps_mem_t Γ s t : Γ ⊢m fEps s t -> Γ ⊢m fMem s t.
Proof. intros H. lem eps_mem (sl [s; t]). exact H. Qed.
