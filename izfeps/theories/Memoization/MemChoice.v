(** * Memoization and choice (Cohen–Abreu Faro–Tate, Cohen–Miquey–Tate)

    In the demonic evidenced frame of the system with memoized streams
    (MemSys.v), despite non-determinism (ndnat):
    - countable choice and dependent choice for indices in ℕ
      (computational witnesses: ∃j:ℕ realized by ⟨n_j, r⟩) are realized,
      with no hypothesis;
    - for an arbitrary index set I (∃i ∈ I without computational content,
      as in UFam), they are realized under a named hypothesis of choice in
      the meta-theory, used to attach an index to each memoized element.

    The realizer allocates a memoized stream whose generator calls the
    totality realizer; memoization freezes, in each state, a single
    element per position, hence functionality. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From IZFe Require Import Frame CompSys MemSys.

Local Abbreviation SPm := (SP MemCS).
Local Abbreviation F := (cs_frame MemCS).
Local Abbreviation W := (wpa MemCS).

(** ** Rules for the primitives *)

Lemma W_succ n σ (Q : log -> code -> Prop) : Q σ (Num (S n)) -> W Succ (Num n) σ Q.
Proof. intros H. split; [constructor|]. intros σ' r Hr. inversion Hr; subst. exact H. Qed.

Lemma W_memo g σ (Q : log -> code -> Prop) : Q σ (Memo1 g) -> W Memo g σ Q.
Proof. intros H. split; [constructor|]. intros σ' r Hr. inversion Hr; subst. exact H. Qed.

Lemma W_memo1 g c0 σ (Q : log -> code -> Prop) :
  Q (EAlloc g c0 :: σ) (Lookup (length (tbls σ))) -> W (Memo1 g) c0 σ Q.
Proof. intros H. split; [constructor|]. intros σ' r Hr. inversion Hr; subst. exact H. Qed.

Ltac mwps := repeat (cbn [subst0]; first [apply wp_a | apply wp_c | apply wpa_lamS | apply wpa_lam0]).

Lemma pairv_inj x y x' y' : pairv MemCS x y = pairv MemCS x' y' -> x = x' /\ y = y'.
Proof. intros H. injection H as -> ->. split; reflexivity. Qed.

(** A proposition realized by a code in a valid state has a reduct. *)
Lemma W_red f a σ Q : valid σ -> W f a σ Q -> exists σ' r, mred f a σ σ' r /\ Q σ' r /\ valid σ' /\ mfut σ σ'.
Proof.
  intros V [T K]. destruct (mprogress _ _ _ T) as (σ' & r & H). exists σ', r.
  split; [exact H|split; [exact (K _ _ H)|split; [exact (mred_valid _ _ _ _ _ H V)|exact (mred_fut _ _ _ _ _ H)]]].
Qed.

(** ** Integers *)

Definition Nn (n : nat) : SPm := mkprop MemCS (fun σ c => c = Num n) (fun _ _ _ _ H => H).
Definition D : code := Num 0.

Definition TotN (S : nat -> nat -> SPm) : SPm :=
  @fall F nat (fun n => @fimp F (Nn n) (sex MemCS (fun j => sand MemCS (Nn j) (S n j)))).

Definition SubN (S R : nat -> nat -> SPm) : SPm :=
  @fall F nat (fun n => @fall F nat (fun j => @fimp F (S n j) (R n j))).

Definition FunN (S : nat -> nat -> SPm) : SPm :=
  @fall F nat (fun n => @fall F nat (fun j => @fall F nat (fun j' =>
    @fimp F (sand MemCS (S n j) (S n j')) (sbr MemCS (j = j'))))).

(** CC on ℕ: ∀R ⊆ ℕ × ℕ. (∀n. ∃j. R(n, j)) ⇒ ∃S ⊆ R functional and total. *)
Definition CCN : SPm :=
  @fall F (nat -> nat -> SPm) (fun R => @fimp F (TotN R)
    (sex MemCS (fun S : nat -> nat -> SPm => sand MemCS (SubN S R) (sand MemCS (FunN S) (TotN S))))).

(** ** CC on ℕ *)

Section CCNat.

Context (R : nat -> nat -> SPm).

Definition PC (k : nat) : SPm.
Proof.
  refine (mkprop MemCS (fun σ p => exists y, p = pairv MemCS (Num k) y /\
             sex MemCS (fun j => sand MemCS (Nn j) (R k j)) σ y) _).
  intros σ σ' c Fu (y & -> & H). exists y. split; [reflexivity|]. eapply sp_stable; eassumption.
Defined.

(** Generator: λp. ⟨succ (π₀ p), t·d·(succ (π₀ p))⟩ *)
Definition genC_body (t : gex code) (p : gex code) : gex code :=
  ga (ga (gc (cPAIR MemCS)) (ga (gc Succ) (ga p (gc (cK MemCS)))))
     (ga (ga t (gc D)) (ga (gc Succ) (ga p (gc (cK MemCS))))).
Definition genC (t : code) : code := Lam 0 (genC_body (gc t) (gv 0)).
Definition cGenC : code := Lam 1 (genC_body (gv 0) (gv 1)).

Lemma genC_step t σ p k : valid σ -> TotN R σ t -> PC k σ p ->
  W (genC t) p σ (fun σ' c' => PC (S k) σ' c' /\ True).
Proof.
  intros V Ht (y & -> & Hy). unfold genC, genC_body. mwps.
  apply W_succ. mwps.
  apply wpa_okfut; [exact V|]. eapply wpa_mono; [|apply (fall_E MemCS _ σ t D (S k) V Ht)].
  intros σx t' Ht' Vx Fx. mwps. apply W_succ.
  apply wpa_okfut; [exact Vx|]. eapply wpa_mono; [|apply (fimp_E MemCS _ _ σx t' (Num (S k)) Vx Ht' eq_refl)].
  intros σ1 y' Hy' V1 F1. mwps. split; [exists y'; split; [reflexivity|exact Hy']|exact I].
Qed.

Definition SC (l n j : nat) : SPm.
Proof.
  refine (mkprop MemCS (fun σ c => tentry σ l n = Some (pairv MemCS (Num n) c) /\ sand MemCS (Nn j) (R n j) σ c) _).
  intros σ σ' c Fu [H1 H2]. split; [exact (tentry_fut _ _ _ _ _ Fu H1)|eapply sp_stable; eassumption].
Defined.

(** λL. λd. λm. let y := (L m)·π₁ in ⟨y·π₀, y⟩ *)
Definition BT : gex code :=
  ga (ga (gc (cPAIR MemCS)) (ga (ga (ga (gv 0) (gv 2)) (gc (cKI MemCS))) (gc (cK MemCS))))
     (ga (ga (gv 0) (gv 2)) (gc (cKI MemCS))).
Definition cTOTS : code := Lam 2 BT.

Section Tot.
Context (t y0 : code) (σ1 : log) (V1 : valid σ1) (Ht : TotN R σ1 t).
Local Abbreviation c0 := (pairv MemCS (Num 0) y0).
Local Abbreviation σA := (EAlloc (genC t) c0 :: σ1).
Local Abbreviation l := (length (tbls σ1)).
Context (P0 : PC 0 σA c0).

Lemma HstepC σ c k : valid σ -> mfut σA σ -> PC k σ c -> W (genC t) c σ (fun σ' c' => PC (S k) σ' c' /\ True).
Proof.
  intros V Fu H. apply genC_step; [exact V| |exact H]. eapply sp_stable; [|exact Ht].
  eapply mfut_trans; [|exact Fu]. exists [EAlloc (genC t) c0]. reflexivity.
Qed.

Lemma tots_ok σ : valid σ -> mfut σA σ -> TotN (SC l) σ (Lam 1 (subst0 BT (Lookup l))).
Proof.
  intros V Fu. apply fall_I. intros σ' F' O' d n. mwps. apply fimp_I. intros σ'' F'' O'' m Hm.
  cbn in Hm. subst m. mwps.
  assert (FA : mfut σA σ'') by (eapply mfut_trans; [exact Fu|eapply mfut_trans; eassumption]).
  apply wpa_okfut; [exact O''|].
  eapply wpa_mono; [|exact (lookup_wpa (genC t) c0 σ1 PC (fun _ _ => True) P0 HstepC n σ'' O'' FA)].
  intros σa e (He & Va & Fa) _ _.
  destruct (proj1 (stream (genC t) c0 σ1 PC (fun _ _ => True) P0 HstepC σa Va Fa) n e He) as (y & -> & Hy).
  mwps. destruct Hy as (j & Hj).
  apply wpa_okfut; [exact Va|]. eapply wpa_mono; [|exact (proj1 (Hj σa (mfut_refl σa) Va))].
  intros σb r Hr Vb Fb. cbn in Hr. subst r. mwps.
  apply wpa_okfut; [exact Vb|].
  eapply wpa_mono; [|exact (lookup_wpa (genC t) c0 σ1 PC (fun _ _ => True) P0 HstepC n σb Vb (mfut_trans _ _ _ Fa Fb))].
  intros σc e' (He' & Vc & Fc) _ Fbc.
  pose proof (tentry_fut _ _ _ _ _ (mfut_trans _ _ _ Fb Fbc) He) as He2. rewrite He' in He2. injection He2 as ->.
  mwps. exists j. apply pairv_and; [reflexivity|]. split; [exact He'|].
  eapply sp_stable; [exact (mfut_trans _ _ _ Fb Fbc)|exact Hj].
Qed.
End Tot.

Definition cSUB : code := Lam 2 (ga (gv 2) (gc (cKI MemCS))).
Definition cFUN : code := Lam 3 (gv 3).

Lemma sub_ok l σ : SubN (SC l) R σ cSUB.
Proof.
  apply fall_I. intros σ1 F1 O1 d n. mwps. apply fall_I. intros σ2 F2 O2 d2 j. mwps.
  apply fimp_I. intros σ3 F3 O3 x [_ Hx]. mwps. exact (proj2 (Hx σ3 (mfut_refl _) O3)).
Qed.

Lemma fun_ok l σ : FunN (SC l) σ cFUN.
Proof.
  apply fall_I. intros σ1 F1 O1 d n. mwps. apply fall_I. intros σ2 F2 O2 d2 j. mwps.
  apply fall_I. intros σ3 F3 O3 d3 j'. mwps. apply fimp_I. intros σ4 F4 O4 x Hx. mwps. cbn.
  destruct (W_red _ _ _ _ O4 (proj1 (Hx σ4 (mfut_refl _) O4))) as (σ5 & c1 & _ & [H1a H1b] & V5 & F5).
  destruct (W_red _ _ _ _ V5 (proj2 (Hx σ5 F5 V5))) as (σ6 & c2 & _ & [H2a H2b] & V6 & F6).
  pose proof (tentry_fut _ _ _ _ _ F6 H1a) as E. rewrite H2a in E. injection E as E.
  subst c2.
  pose proof (@sp_stable MemCS _ σ5 σ6 c1 F6 H1b) as H1c.
  destruct (W_red _ _ _ _ V6 (proj1 (H1c σ6 (mfut_refl _) V6))) as (σ7 & r & Hr & Hrj & _).
  pose proof (proj2 (proj1 (H2b σ6 (mfut_refl _) V6)) _ _ Hr) as Hrj'. cbn in Hrj, Hrj'. congruence.
Qed.

End CCNat.

(** λc. λd. λt. ⟨SUB, ⟨FUN, TOTS (memo (gen t) ⟨0, t·d·0⟩)⟩⟩ *)
Definition cCC : code :=
  Lam 2 (ga (ga (gc (cPAIR MemCS)) (gc cSUB))
            (ga (ga (gc (cPAIR MemCS)) (gc cFUN))
                (ga (gc cTOTS)
                    (ga (ga (gc Memo) (ga (gc cGenC) (gv 2)))
                        (ga (ga (gc (cPAIR MemCS)) (gc (Num 0))) (ga (ga (gv 2) (gc D)) (gc (Num 0)))))))).

Theorem cc_nat : @ftop F —[cCC]→ CCN.
Proof.
  apply realize. intros σ c O. mwps. apply fall_I. intros σ1 F1 O1 d R. mwps.
  apply fimp_I. intros σ2 F2 O2 t Ht. mwps. apply W_memo. mwps.
  apply wpa_okfut; [exact O2|]. eapply wpa_mono; [|apply (fall_E MemCS _ σ2 t D 0 O2 Ht)].
  intros σx t' Ht' Vx Fx. mwps.
  apply wpa_okfut; [exact Vx|]. eapply wpa_mono; [|apply (fimp_E MemCS _ _ σx t' (Num 0) Vx Ht' eq_refl)].
  intros σy y0 Hy0 Vy Fy. mwps. apply W_memo1. mwps.
  set (σA := EAlloc (genC t) (pairv MemCS (Num 0) y0) :: σy).
  assert (FyA : mfut σy σA) by (exists [EAlloc (genC t) (pairv MemCS (Num 0) y0)]; reflexivity).
  assert (VA : valid σA) by (constructor; exact Vy).
  assert (Hty : TotN R σy t) by exact (@sp_stable MemCS _ σ2 σy t (mfut_trans _ _ _ Fx Fy) Ht).
  assert (P0 : PC R 0 σA (pairv MemCS (Num 0) y0)).
  { exists y0. split; [reflexivity|]. exact (@sp_stable MemCS _ σy σA y0 FyA Hy0). }
  exists (SC R (length (tbls σy))). apply pairv_and; [apply sub_ok|]. apply pairv_and; [apply fun_ok|].
  exact (tots_ok R t y0 σy Hty P0 σA VA (mfut_refl _)).
Qed.

(** ** DC on ℕ *)

Definition StepN (Sr R : nat -> nat -> SPm) : SPm :=
  @fall F nat (fun n => @fall F nat (fun i => @fall F nat (fun j =>
    @fimp F (sand MemCS (Sr n i) (Sr (S n) j)) (R i j)))).

(** DC on ℕ: ∀R. (∀i. ∃j. R(i, j)) ⇒ ∀i₀. ∃S functional, total, S(0, i₀),
    and S(n, i) ∧ S(n+1, j) ⇒ R(i, j). *)
Definition DCN : SPm :=
  @fall F (nat -> nat -> SPm) (fun R => @fimp F (TotN R)
    (@fall F nat (fun i0 => @fimp F (Nn i0)
      (sex MemCS (fun Sr : nat -> nat -> SPm =>
         sand MemCS (FunN Sr) (sand MemCS (TotN Sr) (sand MemCS (Sr 0 i0) (StepN Sr R)))))))).

Section DCNat.

Context (R : nat -> nat -> SPm).

Definition PD (i0 k : nat) : SPm.
Proof.
  refine (mkprop MemCS (fun σ c => match k with
    | 0 => c = pairv MemCS (Num i0) D
    | S _ => exists i j y, c = pairv MemCS (Num j) (pairv MemCS (Num i) y) /\ sand MemCS (Nn j) (R i j) σ y
    end) _).
  intros σ σ' c Fu H. destruct k; [exact H|]. destruct H as (i & j & y & -> & H).
  exists i, j, y. split; [reflexivity|]. eapply sp_stable; eassumption.
Defined.

Definition LinkD (c c' : code) : Prop :=
  exists i z j y, c = pairv MemCS (Num i) z /\ c' = pairv MemCS (Num j) (pairv MemCS (Num i) y).

Lemma PD_form i0 k σ c : PD i0 k σ c -> exists i z, c = pairv MemCS (Num i) z.
Proof. destruct k; cbn; [intros ->; eauto|intros (i & j & y & -> & _); eauto]. Qed.

(** λm. λy. ⟨y·π₀, ⟨m, y⟩⟩ *)
Definition cLP : code :=
  Lam 1 (ga (ga (gc (cPAIR MemCS)) (ga (gv 1) (gc (cK MemCS)))) (ga (ga (gc (cPAIR MemCS)) (gv 0)) (gv 1))).

(** Generator: λp. LP (p·π₀) (t·d·(p·π₀)) *)
Definition genD_body (t p : gex code) : gex code :=
  ga (ga (gc cLP) (ga p (gc (cK MemCS)))) (ga (ga t (gc D)) (ga p (gc (cK MemCS)))).
Definition genD (t : code) : code := Lam 0 (genD_body (gc t) (gv 0)).
Definition cGenD : code := Lam 1 (genD_body (gv 0) (gv 1)).

Lemma genD_step i0 t σ p k : valid σ -> TotN R σ t -> PD i0 k σ p ->
  W (genD t) p σ (fun σ' c' => PD i0 (S k) σ' c' /\ LinkD p c').
Proof.
  intros V Ht Hp. destruct (PD_form _ _ _ _ Hp) as (i & z & ->). unfold genD, genD_body. mwps.
  apply wpa_okfut; [exact V|]. eapply wpa_mono; [|apply (fall_E MemCS _ σ t D i V Ht)].
  intros σ1 t' Ht' V1 F1. mwps.
  apply wpa_okfut; [exact V1|]. eapply wpa_mono; [|apply (fimp_E MemCS _ _ σ1 t' (Num i) V1 Ht' eq_refl)].
  intros σ2 y (j & Hj) V2 F2. mwps.
  apply wpa_okfut; [exact V2|]. eapply wpa_mono; [|exact (proj1 (Hj σ2 (mfut_refl _) V2))].
  intros σ3 r Hr V3 F3. cbn in Hr. subst r. mwps. split.
  - exists i, j, y. split; [reflexivity|]. exact (@sp_stable MemCS _ σ2 σ3 y F3 Hj).
  - exists i, z, j, y. split; reflexivity.
Qed.

Definition SD (l n i : nat) : SPm.
Proof.
  refine (mkprop MemCS (fun σ c => tentry σ l n = Some c /\ exists z, c = pairv MemCS (Num i) z) _).
  intros σ σ' c Fu [H1 H2]. split; [exact (tentry_fut _ _ _ _ _ Fu H1)|exact H2].
Defined.

Lemma fun_okD l σ : FunN (SD l) σ cFUN.
Proof.
  apply fall_I. intros σ1 F1 O1 d n. mwps. apply fall_I. intros σ2 F2 O2 d2 j. mwps.
  apply fall_I. intros σ3 F3 O3 d3 j'. mwps. apply fimp_I. intros σ4 F4 O4 x Hx. mwps. cbn.
  destruct (W_red _ _ _ _ O4 (proj1 (Hx σ4 (mfut_refl _) O4))) as (σ5 & c1 & _ & [H1a (z1 & E1)] & V5 & F5).
  destruct (W_red _ _ _ _ V5 (proj2 (Hx σ5 F5 V5))) as (σ6 & c2 & _ & [H2a (z2 & E2)] & V6 & F6).
  pose proof (tentry_fut _ _ _ _ _ F6 H1a) as E. rewrite H2a in E. injection E as E. subst c1 c2.
  apply pairv_inj in E as [E _]. congruence.
Qed.

Definition BTD : gex code :=
  ga (ga (gc (cPAIR MemCS)) (ga (ga (gv 0) (gv 2)) (gc (cK MemCS)))) (ga (gv 0) (gv 2)).
Definition cTOTD : code := Lam 2 BTD.

(** λd₁ d₂ d₃ x. (λ_ v. v) (x·π₀) (x·π₁·π₁·π₁·π₁): x·π₀ is evaluated first. *)
Definition cSTEPD : code :=
  Lam 3 (ga (ga (gc (cKI MemCS)) (ga (gv 3) (gc (cK MemCS))))
            (ga (ga (ga (ga (gv 3) (gc (cKI MemCS))) (gc (cKI MemCS))) (gc (cKI MemCS))) (gc (cKI MemCS)))).

Section TotD.
Context (t : code) (i0 : nat) (σ1 : log) (V1 : valid σ1) (Ht : TotN R σ1 t).
Local Abbreviation c0 := (pairv MemCS (Num i0) D).
Local Abbreviation σA := (EAlloc (genD t) c0 :: σ1).
Local Abbreviation l := (length (tbls σ1)).

Lemma P0D : PD i0 0 σA c0.
Proof. reflexivity. Qed.

Lemma HstepD σ c k : valid σ -> mfut σA σ -> PD i0 k σ c -> W (genD t) c σ (fun σ' c' => PD i0 (S k) σ' c' /\ LinkD c c').
Proof.
  intros V Fu H. apply genD_step; [exact V| |exact H].
  apply (@sp_stable MemCS _ σ1 σ t); [|exact Ht]. eapply mfut_trans; [|exact Fu]. exists [EAlloc (genD t) c0]. reflexivity.
Qed.

Local Abbreviation STR := (stream (genD t) c0 σ1 (PD i0) LinkD P0D HstepD).
Local Abbreviation LK := (lookup_wpa (genD t) c0 σ1 (PD i0) LinkD P0D HstepD).

Lemma tots_okD σ : valid σ -> mfut σA σ -> TotN (SD l) σ (Lam 1 (subst0 BTD (Lookup l))).
Proof.
  intros V Fu. apply fall_I. intros σ' F' O' d n. mwps. apply fimp_I. intros σ'' F'' O'' m Hm.
  cbn in Hm. subst m. mwps.
  assert (FA : mfut σA σ'') by (eapply mfut_trans; [exact Fu|eapply mfut_trans; eassumption]).
  apply wpa_okfut; [exact O''|]. eapply wpa_mono; [|exact (LK n σ'' O'' FA)].
  intros σa e (He & Va & Fa) _ _.
  destruct (PD_form _ _ _ _ (proj1 (STR σa Va Fa) n e He)) as (i & z & ->). mwps.
  apply wpa_okfut; [exact Va|]. eapply wpa_mono; [|exact (LK n σa Va Fa)].
  intros σc e' (He' & Vc & Fc) _ Fac.
  pose proof (tentry_fut _ _ _ _ _ Fac He) as He2. rewrite He' in He2. injection He2 as ->.
  mwps. exists i. apply pairv_and; [reflexivity|]. split; [exact He'|eexists; reflexivity].
Qed.

Lemma step_okD σ : valid σ -> mfut σA σ -> StepN (SD l) R σ cSTEPD.
Proof.
  intros V Fu. apply fall_I. intros σ1' F1 O1 d n. mwps. apply fall_I. intros σ2 F2 O2 d2 i. mwps.
  apply fall_I. intros σ3 F3 O3 d3 j. mwps. apply fimp_I. intros σ4 F4 O4 x Hx. mwps.
  assert (FA : mfut σA σ4) by (eapply mfut_trans; [exact Fu|eapply mfut_trans; [exact F1|eapply mfut_trans; [exact F2|eapply mfut_trans; eassumption]]]).
  apply wpa_okfut; [exact O4|]. eapply wpa_mono; [|exact (proj1 (Hx σ4 (mfut_refl _) O4))].
  intros σ5 c1 [H1a (z1 & ->)] V5 F5. mwps.
  apply wpa_okfut; [exact V5|]. eapply wpa_mono; [|exact (proj2 (Hx σ5 F5 V5))].
  intros σ6 c2 [H2a (z2 & ->)] V6 F6.
  assert (FA6 : mfut σA σ6) by (eapply mfut_trans; [exact FA|eapply mfut_trans; eassumption]).
  destruct (STR σ6 V6 FA6) as [IP IL].
  pose proof (IP _ _ H2a) as (i' & j' & y & E & Hy). cbn in E.
  pose proof (IL _ _ _ (tentry_fut _ _ _ _ _ F6 H1a) H2a) as (i'' & z & j'' & y' & E1 & E2).
  apply pairv_inj in E as [Ej E]. injection Ej as <-.
  apply pairv_inj in E1 as [Ei _]. injection Ei as <-.
  apply pairv_inj in E2 as [_ E2]. rewrite E in E2. apply pairv_inj in E2 as [Ei' <-]. injection Ei' as ->.
  subst z2. mwps.
  apply wpa_okfut; [exact V6|]. eapply wpa_mono; [|exact (proj2 (Hy σ6 (mfut_refl _) V6))].
  intros σ7 r Hr V7 F7. mwps. exact Hr.
Qed.

End TotD.

End DCNat.

(** λc d t d' m₀. ⟨FUN, ⟨TOTS (memo (gen t) ⟨m₀, d⟩), ⟨⟨m₀, d⟩, STEP⟩⟩⟩ *)
Definition cDC : code :=
  let C0 := ga (ga (gc (cPAIR MemCS)) (gv 4)) (gc D) in
  Lam 4 (ga (ga (gc (cPAIR MemCS)) (gc cFUN))
            (ga (ga (gc (cPAIR MemCS)) (ga (gc cTOTD) (ga (ga (gc Memo) (ga (gc cGenD) (gv 2))) C0)))
                (ga (ga (gc (cPAIR MemCS)) C0) (gc cSTEPD)))).

Theorem dc_nat : @ftop F —[cDC]→ DCN.
Proof.
  apply realize. intros σ c O. unfold cDC. mwps. apply fall_I. intros σ1 F1 O1 d R. mwps.
  apply fimp_I. intros σ2 F2 O2 t Ht. mwps. apply fall_I. intros σ3 F3 O3 d' i0. mwps.
  apply fimp_I. intros σ4 F4 O4 m Hm. cbn in Hm. subst m. mwps. apply W_memo. mwps. apply W_memo1. mwps.
  set (σA := EAlloc (genD t) (pairv MemCS (Num i0) D) :: σ4).
  assert (VA : valid σA) by (constructor; exact O4).
  assert (Ht4 : TotN R σ4 t) by exact (@sp_stable MemCS _ σ2 σ4 t (mfut_trans _ _ _ F3 F4) Ht).
  exists (SD (length (tbls σ4))). apply pairv_and; [apply fun_okD|]. apply pairv_and.
  - exact (tots_okD R t i0 σ4 Ht4 σA VA (mfut_refl _)).
  - apply pairv_and.
    + split; [|eexists; reflexivity]. unfold tentry.
      replace (tget _ _) with (Some (genD t, [pairv MemCS (Num i0) D])) by (symmetry; exact (tget_A (genD t) (pairv MemCS (Num i0) D) σ4)).
      reflexivity.
    + exact (step_okD R t i0 σ4 Ht4 σA VA (mfut_refl _)).
Qed.

(** ** Arbitrary indices

    For an arbitrary index set I, ∃i ∈ I is a union (without
    computational witness). An index is attached to each memoized element
    using a hypothesis of choice in the meta-theory, applied to the
    element and to the state where it was recorded (which does not depend
    on the current state). *)

(** The recording state of element n of table ℓ: the smallest suffix
    of the log that contains it. *)
Fixpoint recst (l n : nat) (σ : log) : option log :=
  match σ with
  | [] => None
  | e :: σ' => match recst l n σ' with
      | Some r => Some r
      | None => match tentry (e :: σ') l n with Some _ => Some (e :: σ') | None => None end
      end
  end.

Lemma recst_cons l n e σ : recst l n (e :: σ) = match recst l n σ with
      | Some r => Some r
      | None => match tentry (e :: σ) l n with Some _ => Some (e :: σ) | None => None end
      end.
Proof. reflexivity. Qed.

Lemma recst_spec l n σ r : recst l n σ = Some r -> mfut r σ /\ tentry r l n <> None.
Proof.
  revert r. induction σ as [|e σ IH]; intros r; [discriminate|]. rewrite recst_cons.
  destruct (recst l n σ) as [r'|] eqn:E.
  - intros H. injection H as <-. destruct (IH r' eq_refl) as [Fr H]. split; [|exact H].
    eapply mfut_trans; [exact Fr|exists [e]; reflexivity].
  - destruct (tentry (e :: σ) l n) eqn:T; [|discriminate]. intros H. injection H as <-.
    split; [apply mfut_refl|congruence].
Qed.

Lemma recst_some l n σ c : tentry σ l n = Some c -> exists r, recst l n σ = Some r.
Proof.
  destruct σ as [|e σ]; intros H.
  - unfold tentry, tget in H. cbn in H. destruct l; discriminate.
  - rewrite recst_cons. destruct (recst l n σ) as [r|]; [eauto|]. rewrite H. eauto.
Qed.

Lemma recst_fut l n σ σ' r : mfut σ σ' -> recst l n σ = Some r -> recst l n σ' = Some r.
Proof.
  intros [ext ->] H. induction ext as [|e ext IH]; [exact H|]. cbn [app]. rewrite recst_cons, IH. reflexivity.
Qed.

Lemma recst_A g c0 σ0 σ n r : valid σ -> mfut (EAlloc g c0 :: σ0) σ -> recst (length (tbls σ0)) n σ = Some r ->
  valid r /\ mfut (EAlloc g c0 :: σ0) r /\ mfut r σ /\
  exists c, tentry r (length (tbls σ0)) n = Some c /\ tentry σ (length (tbls σ0)) n = Some c.
Proof.
  intros V Fu Hr. destruct (recst_spec _ _ _ _ Hr) as [Fr Tr].
  destruct (tentry r (length (tbls σ0)) n) as [c|] eqn:Ec; [|congruence].
  split; [exact (valid_fut _ _ Fr V)|]. split.
  - apply (knows_A g c0 σ0 r σ Fr Fu). unfold tentry in Ec. destruct (tget r _); congruence.
  - split; [exact Fr|]. exists c. split; [reflexivity|exact (tentry_fut _ _ _ _ _ Fr Ec)].
Qed.

Section AnyIndex.

Context (Ix : Type).

(** Choice (relativized to the domain) in the meta-theory, for
    families indexed by X with values in Ix. *)
Definition AC_dom (X : Type) : Prop :=
  forall Q : X -> Ix -> Prop, exists f : X -> Ix, forall x, (exists i, Q x i) -> Q x (f x).

Definition TotI (Sr : nat -> Ix -> SPm) : SPm :=
  @fall F nat (fun n => @fimp F (Nn n) (sex MemCS (fun i => Sr n i))).

Definition SubI (Sr R : nat -> Ix -> SPm) : SPm :=
  @fall F nat (fun n => @fall F Ix (fun i => @fimp F (Sr n i) (R n i))).

Definition FunI (Sr : nat -> Ix -> SPm) : SPm :=
  @fall F nat (fun n => @fall F Ix (fun i => @fall F Ix (fun i' =>
    @fimp F (sand MemCS (Sr n i) (Sr n i')) (sbr MemCS (i = i'))))).

(** CC: ∀R ⊆ ℕ × I. (∀n ∈ ℕ. ∃i ∈ I. R(n, i)) ⇒ ∃S ⊆ R functional and total. *)
Definition CCI : SPm :=
  @fall F (nat -> Ix -> SPm) (fun R => @fimp F (TotI R)
    (sex MemCS (fun Sr : nat -> Ix -> SPm => sand MemCS (SubI Sr R) (sand MemCS (FunI Sr) (TotI Sr))))).

(** *** CC *)

Section CCAny.

Context (R : nat -> Ix -> SPm).

Definition QC (x : nat * code * log) (i : Ix) : Prop := let '(n, y, r) := x in R n i r y.

Definition PCI (k : nat) : SPm.
Proof.
  refine (mkprop MemCS (fun σ p => exists y, p = pairv MemCS (Num k) y /\ sex MemCS (fun i => R k i) σ y) _).
  intros σ σ' c Fu (y & -> & H). exists y. split; [reflexivity|]. eapply sp_stable; eassumption.
Defined.

Lemma genCI_step t σ p k : valid σ -> TotI R σ t -> PCI k σ p ->
  W (genC t) p σ (fun σ' c' => PCI (S k) σ' c' /\ True).
Proof.
  intros V Ht (y & -> & Hy). unfold genC, genC_body. mwps.
  apply W_succ. mwps.
  apply wpa_okfut; [exact V|]. eapply wpa_mono; [|apply (fall_E MemCS _ σ t D (S k) V Ht)].
  intros σx t' Ht' Vx Fx. mwps. apply W_succ.
  apply wpa_okfut; [exact Vx|]. eapply wpa_mono; [|apply (fimp_E MemCS _ _ σx t' (Num (S k)) Vx Ht' eq_refl)].
  intros σ1 y' Hy' V1 F1. mwps. split; [exists y'; split; [reflexivity|exact Hy']|exact Logic.I].
Qed.

Context (f : nat * code * log -> Ix) (Hf : forall x, (exists i, QC x i) -> QC x (f x)).

(** S(n, i): element n is ⟨n, c⟩, and i is the index chosen for c at
    its recording state. *)
Definition SCI (l n : nat) (i : Ix) : SPm.
Proof.
  refine (mkprop MemCS (fun σ c => tentry σ l n = Some (pairv MemCS (Num n) c) /\
             (exists r, recst l n σ = Some r /\ i = f (n, c, r)) /\ R n i σ c) _).
  intros σ σ' c Fu (H1 & (r & Hr & ->) & H3). split; [exact (tentry_fut _ _ _ _ _ Fu H1)|].
  split; [exists r; split; [exact (recst_fut _ _ _ _ _ Fu Hr)|reflexivity]|eapply sp_stable; eassumption].
Defined.

Definition cSUBI : code := Lam 2 (gv 2).

Lemma sub_okI l σ : SubI (SCI l) R σ cSUBI.
Proof.
  apply fall_I. intros σ1 F1 O1 d n. mwps. apply fall_I. intros σ2 F2 O2 d2 i. mwps.
  apply fimp_I. intros σ3 F3 O3 x (_ & _ & Hx). mwps. exact Hx.
Qed.

Lemma fun_okI l σ : FunI (SCI l) σ cFUN.
Proof.
  apply fall_I. intros σ1 F1 O1 d n. mwps. apply fall_I. intros σ2 F2 O2 d2 i. mwps.
  apply fall_I. intros σ3 F3 O3 d3 i'. mwps. apply fimp_I. intros σ4 F4 O4 x Hx. mwps. cbn.
  destruct (W_red _ _ _ _ O4 (proj1 (Hx σ4 (mfut_refl _) O4))) as (σ5 & c1 & _ & (H1a & (r1 & Hr1 & E1) & _) & V5 & F5).
  destruct (W_red _ _ _ _ V5 (proj2 (Hx σ5 F5 V5))) as (σ6 & c2 & _ & (H2a & (r2 & Hr2 & E2) & _) & V6 & F6).
  pose proof (tentry_fut _ _ _ _ _ F6 H1a) as E. rewrite H2a in E. injection E as E.
  pose proof (recst_fut _ _ _ _ _ F6 Hr1) as Hr1'. rewrite Hr2 in Hr1'. injection Hr1' as Er.
  subst. reflexivity.
Qed.

Definition BTI : gex code := ga (ga (gv 0) (gv 2)) (gc (cKI MemCS)).
Definition cTOTI : code := Lam 2 BTI.

Section TotCI.
Context (t y0 : code) (σ1 : log) (Ht : TotI R σ1 t).
Local Abbreviation c0 := (pairv MemCS (Num 0) y0).
Local Abbreviation σA := (EAlloc (genC t) c0 :: σ1).
Local Abbreviation l := (length (tbls σ1)).
Context (P0 : PCI 0 σA c0).

Lemma HstepCI σ c k : valid σ -> mfut σA σ -> PCI k σ c -> W (genC t) c σ (fun σ' c' => PCI (S k) σ' c' /\ True).
Proof.
  intros V Fu H. apply genCI_step; [exact V| |exact H].
  apply (@sp_stable MemCS _ σ1 σ t); [|exact Ht]. eapply mfut_trans; [|exact Fu]. exists [EAlloc (genC t) c0]. reflexivity.
Qed.

Local Abbreviation STR := (stream (genC t) c0 σ1 PCI (fun _ _ => True) P0 HstepCI).
Local Abbreviation LK := (lookup_wpa (genC t) c0 σ1 PCI (fun _ _ => True) P0 HstepCI).

Lemma pickI σ n y : valid σ -> mfut σA σ -> tentry σ l n = Some (pairv MemCS (Num n) y) ->
  sex MemCS (fun i => SCI l n i) σ y.
Proof.
  intros V Fu He. destruct (recst_some _ _ _ _ He) as [r Hr].
  destruct (recst_A _ _ _ _ _ _ V Fu Hr) as (Vr & FAr & Fr & c & Ec & Ec').
  rewrite He in Ec'. injection Ec' as <-.
  destruct (proj1 (STR r Vr FAr) n _ Ec) as (y' & E & Hy'). apply pairv_inj in E as [_ <-].
  pose proof (Hf (n, y, r) Hy') as HR. cbn in HR.
  exists (f (n, y, r)). split; [exact He|]. split; [exists r; split; [exact Hr|reflexivity]|].
  exact (@sp_stable MemCS _ r σ y Fr HR).
Qed.

Lemma tots_okI σ : valid σ -> mfut σA σ -> TotI (SCI l) σ (Lam 1 (subst0 BTI (Lookup l))).
Proof.
  intros V Fu. apply fall_I. intros σ' F' O' d n. mwps. apply fimp_I. intros σ'' F'' O'' m Hm.
  cbn in Hm. subst m. mwps.
  assert (FA : mfut σA σ'') by (eapply mfut_trans; [exact Fu|eapply mfut_trans; eassumption]).
  apply wpa_okfut; [exact O''|]. eapply wpa_mono; [|exact (LK n σ'' O'' FA)].
  intros σa e (He & Va & Fa) _ _.
  destruct (proj1 (STR σa Va Fa) n e He) as (y & -> & _). mwps.
  exact (pickI σa n y Va Fa He).
Qed.

End TotCI.
End CCAny.

(** λc. λd. λt. ⟨SUB, ⟨FUN, TOT (memo (gen t) ⟨0, t·d·0⟩)⟩⟩ *)
Definition cCCI : code :=
  Lam 2 (ga (ga (gc (cPAIR MemCS)) (gc cSUBI))
            (ga (ga (gc (cPAIR MemCS)) (gc cFUN))
                (ga (gc cTOTI)
                    (ga (ga (gc Memo) (ga (gc cGenC) (gv 2)))
                        (ga (ga (gc (cPAIR MemCS)) (gc (Num 0))) (ga (ga (gv 2) (gc D)) (gc (Num 0)))))))).

Theorem cc_any : AC_dom (nat * code * log) -> @ftop F —[cCCI]→ CCI.
Proof.
  intros AC. apply realize. intros σ c O. mwps. apply fall_I. intros σ1 F1 O1 d R.
  destruct (AC (QC R)) as [f Hf]. mwps.
  apply fimp_I. intros σ2 F2 O2 t Ht. mwps. apply W_memo. mwps.
  apply wpa_okfut; [exact O2|]. eapply wpa_mono; [|apply (fall_E MemCS _ σ2 t D 0 O2 Ht)].
  intros σx t' Ht' Vx Fx. mwps.
  apply wpa_okfut; [exact Vx|]. eapply wpa_mono; [|apply (fimp_E MemCS _ _ σx t' (Num 0) Vx Ht' eq_refl)].
  intros σy y0 Hy0 Vy Fy. mwps. apply W_memo1. mwps.
  set (σA := EAlloc (genC t) (pairv MemCS (Num 0) y0) :: σy).
  assert (FyA : mfut σy σA) by (exists [EAlloc (genC t) (pairv MemCS (Num 0) y0)]; reflexivity).
  assert (VA : valid σA) by (constructor; exact Vy).
  assert (Hty : TotI R σy t) by exact (@sp_stable MemCS _ σ2 σy t (mfut_trans _ _ _ Fx Fy) Ht).
  assert (P0 : PCI R 0 σA (pairv MemCS (Num 0) y0)).
  { exists y0. split; [reflexivity|]. exact (@sp_stable MemCS _ σy σA y0 FyA Hy0). }
  exists (SCI R f (length (tbls σy))). apply pairv_and; [apply sub_okI|]. apply pairv_and; [apply fun_okI|].
  exact (tots_okI R f Hf t y0 σy Hty P0 σA VA (mfut_refl _)).
Qed.

(** *** DC *)

Definition TotR (R : Ix -> Ix -> SPm) : SPm := @fall F Ix (fun i => sex MemCS (fun j => R i j)).

Definition StepI (Sr : nat -> Ix -> SPm) (R : Ix -> Ix -> SPm) : SPm :=
  @fall F nat (fun n => @fall F Ix (fun i => @fall F Ix (fun j =>
    @fimp F (sand MemCS (Sr n i) (Sr (S n) j)) (R i j)))).

(** DC: ∀R ⊆ I × I. (∀i. ∃j. R(i, j)) ⇒ ∀i₀. ∃S ⊆ ℕ × I functional,
    total, with S(0, i₀) and S(n, i) ∧ S(n+1, j) ⇒ R(i, j). *)
Definition DCI : SPm :=
  @fall F (Ix -> Ix -> SPm) (fun R => @fimp F (TotR R)
    (@fall F Ix (fun i0 =>
      sex MemCS (fun Sr : nat -> Ix -> SPm =>
        sand MemCS (FunI Sr) (sand MemCS (TotI Sr) (sand MemCS (Sr 0 i0) (StepI Sr R))))))).

Section DCAny.

Context (R : Ix -> Ix -> SPm).

Definition QD (x : Ix * code * log) (j : Ix) : Prop := let '(i, y, r) := x in R i j r y.

(** The elements k ≥ 1 of the stream are reducts of t·d: they realize
    ∃j. R(i, j) for every i. *)
Definition PDI (k : nat) : SPm.
Proof.
  refine (mkprop MemCS (fun σ c => match k with 0 => True | S _ => forall i, sex MemCS (fun j => R i j) σ c end) _).
  intros σ σ' c Fu H. destruct k; [exact H|]. intros i. eapply sp_stable; [exact Fu|exact (H i)].
Defined.

(** Generator: λ_. t·d *)
Definition genI (t : code) : code := Lam 0 (ga (gc t) (gc D)).
Definition cGenI : code := Lam 1 (ga (gv 0) (gc D)).

Context (i0 : Ix).

Lemma genI_step t σ c k : valid σ -> TotR R σ t -> W (genI t) c σ (fun σ' c' => PDI (S k) σ' c' /\ True).
Proof.
  intros V Ht. unfold genI. mwps.
  destruct (fall_E MemCS _ σ t D i0 V Ht) as [T _]. split; [exact T|].
  intros σ' r Hr. split; [|exact Logic.I]. intros i. exact (proj2 (fall_E MemCS _ σ t D i V Ht) σ' r Hr).
Qed.

Context (f : Ix * code * log -> Ix) (Hf : forall x, (exists j, QD x j) -> QD x (f x)).

(** The index of element k: i₀ for k = 0, then chosen from the
    previous index, the element and its recording state. *)
Fixpoint idx (l : nat) (σ : log) (k : nat) : option Ix :=
  match k with
  | 0 => Some i0
  | S k => match idx l σ k, tentry σ l (S k), recst l (S k) σ with
           | Some i, Some y, Some r => Some (f (i, y, r))
           | _, _, _ => None
           end
  end.

Lemma idx_fut l σ σ' k i : mfut σ σ' -> idx l σ k = Some i -> idx l σ' k = Some i.
Proof.
  intros Fu. induction k as [|k IH] in i |- *; [exact (fun H => H)|]. cbn.
  destruct (idx l σ k) as [i1|] eqn:E1; [|discriminate].
  destruct (tentry σ l (S k)) as [y|] eqn:E2; [|discriminate].
  destruct (recst l (S k) σ) as [r|] eqn:E3; [|discriminate].
  rewrite (IH _ eq_refl), (tentry_fut _ _ _ _ _ Fu E2), (recst_fut _ _ _ _ _ Fu E3). exact (fun H => H).
Qed.

Lemma idx_some l σ n c : tentry σ l n = Some c -> exists i, idx l σ n = Some i.
Proof.
  revert c; induction n as [|n IH]; intros c H; [exists i0; reflexivity|].
  pose proof (tentry_some_lt _ _ _ _ H) as L.
  destruct (tentry_lt σ l n ltac:(lia)) as [c' Hc'].
  destruct (IH _ Hc') as [i Hi]. destruct (recst_some _ _ _ _ H) as [r Hr].
  cbn. rewrite Hi, H, Hr. eauto.
Qed.

Definition SDI (l n : nat) (i : Ix) : SPm.
Proof.
  refine (mkprop MemCS (fun σ c => tentry σ l n = Some c /\ idx l σ n = Some i) _).
  intros σ σ' c Fu [H1 H2]. split; [exact (tentry_fut _ _ _ _ _ Fu H1)|exact (idx_fut _ _ _ _ _ Fu H2)].
Defined.

Lemma fun_okDI l σ : FunI (SDI l) σ cFUN.
Proof.
  apply fall_I. intros σ1 F1 O1 d n. mwps. apply fall_I. intros σ2 F2 O2 d2 i. mwps.
  apply fall_I. intros σ3 F3 O3 d3 i'. mwps. apply fimp_I. intros σ4 F4 O4 x Hx. mwps. cbn.
  destruct (W_red _ _ _ _ O4 (proj1 (Hx σ4 (mfut_refl _) O4))) as (σ5 & c1 & _ & [_ I1] & V5 & F5).
  destruct (W_red _ _ _ _ V5 (proj2 (Hx σ5 F5 V5))) as (σ6 & c2 & _ & [_ I2] & V6 & F6).
  pose proof (idx_fut _ _ _ _ _ F6 I1) as I1'. congruence.
Qed.

Definition BTDI : gex code := ga (gv 0) (gv 2).
Definition cTOTDI : code := Lam 2 BTDI.

(** λd₁ d₂ d₃ x. (λ_ v. v) (x·π₀) (x·π₁): x·π₀ is evaluated first. *)
Definition cSTEPI : code :=
  Lam 3 (ga (ga (gc (cKI MemCS)) (ga (gv 3) (gc (cK MemCS)))) (ga (gv 3) (gc (cKI MemCS)))).

Section TotDI.
Context (t : code) (σ1 : log) (Ht : TotR R σ1 t).
Local Abbreviation σA := (EAlloc (genI t) D :: σ1).
Local Abbreviation l := (length (tbls σ1)).

Lemma P0DI : PDI 0 σA D.
Proof. exact Logic.I. Qed.

Lemma HstepDI σ c k : valid σ -> mfut σA σ -> PDI k σ c -> W (genI t) c σ (fun σ' c' => PDI (S k) σ' c' /\ True).
Proof.
  intros V Fu _. apply genI_step; [exact V|].
  apply (@sp_stable MemCS _ σ1 σ t); [|exact Ht]. eapply mfut_trans; [|exact Fu]. exists [EAlloc (genI t) D]. reflexivity.
Qed.

Local Abbreviation STR := (stream (genI t) D σ1 PDI (fun _ _ => True) P0DI HstepDI).
Local Abbreviation LK := (lookup_wpa (genI t) D σ1 PDI (fun _ _ => True) P0DI HstepDI).

Lemma tots_okDI σ : valid σ -> mfut σA σ -> TotI (SDI l) σ (Lam 1 (subst0 BTDI (Lookup l))).
Proof.
  intros V Fu. apply fall_I. intros σ' F' O' d n. mwps. apply fimp_I. intros σ'' F'' O'' m Hm.
  cbn in Hm. subst m. mwps.
  assert (FA : mfut σA σ'') by (eapply mfut_trans; [exact Fu|eapply mfut_trans; eassumption]).
  apply wpa_okfut; [exact O''|]. eapply wpa_mono; [|exact (LK n σ'' O'' FA)].
  intros σa e (He & Va & Fa) _ _.
  destruct (idx_some _ _ _ _ He) as [i Hi]. exists i. split; [exact He|exact Hi].
Qed.

Lemma step_okDI σ : valid σ -> mfut σA σ -> StepI (SDI l) R σ cSTEPI.
Proof.
  intros V Fu. apply fall_I. intros σ1' F1 O1 d n. mwps. apply fall_I. intros σ2 F2 O2 d2 i. mwps.
  apply fall_I. intros σ3 F3 O3 d3 j. mwps. apply fimp_I. intros σ4 F4 O4 x Hx. mwps.
  assert (FA : mfut σA σ4) by (eapply mfut_trans; [exact Fu|eapply mfut_trans; [exact F1|eapply mfut_trans; [exact F2|eapply mfut_trans; eassumption]]]).
  apply wpa_okfut; [exact O4|]. eapply wpa_mono; [|exact (proj1 (Hx σ4 (mfut_refl _) O4))].
  intros σ5 c1 [_ I1] V5 F5. mwps.
  apply wpa_okfut; [exact V5|]. eapply wpa_mono; [|exact (proj2 (Hx σ5 F5 V5))].
  intros σ6 c2 [H2a I2] V6 F6. mwps.
  assert (FA6 : mfut σA σ6) by (eapply mfut_trans; [exact FA|eapply mfut_trans; eassumption]).
  pose proof (idx_fut _ _ _ _ _ F6 I1) as I1'. cbn in I2. rewrite I1', H2a in I2.
  destruct (recst l (S n) σ6) as [r|] eqn:Hr; [|discriminate]. injection I2 as <-.
  destruct (recst_A _ _ _ _ _ _ V6 FA6 Hr) as (Vr & FAr & Fr & c & Ec & Ec').
  rewrite H2a in Ec'. injection Ec' as <-.
  pose proof (proj1 (STR r Vr FAr) (S n) c2 Ec) as Pc. cbn in Pc.
  pose proof (Hf (i, c2, r) (Pc i)) as HR. cbn in HR.
  exact (@sp_stable MemCS _ r σ6 c2 Fr HR).
Qed.

End TotDI.
End DCAny.

(** λc d t d'. ⟨FUN, ⟨TOT (memo (λ_. t·d) d), ⟨d, STEP⟩⟩⟩ *)
Definition cDCI : code :=
  Lam 3 (ga (ga (gc (cPAIR MemCS)) (gc cFUN))
            (ga (ga (gc (cPAIR MemCS)) (ga (gc cTOTDI) (ga (ga (gc Memo) (ga (gc cGenI) (gv 2))) (gc D))))
                (ga (ga (gc (cPAIR MemCS)) (gc D)) (gc cSTEPI)))).

Theorem dc_any : AC_dom (Ix * code * log) -> @ftop F —[cDCI]→ DCI.
Proof.
  intros AC. apply realize. intros σ c O. unfold cDCI. mwps. apply fall_I. intros σ1 F1 O1 d R.
  destruct (AC (QD R)) as [f Hf]. mwps.
  apply fimp_I. intros σ2 F2 O2 t Ht. mwps. apply fall_I. intros σ3 F3 O3 d' i0. mwps.
  apply W_memo. mwps. apply W_memo1. mwps.
  set (σA := EAlloc (genI t) D :: σ3).
  assert (VA : valid σA) by (constructor; exact O3).
  assert (Ht3 : TotR R σ3 t) by exact (@sp_stable MemCS _ σ2 σ3 t F3 Ht).
  exists (SDI i0 f (length (tbls σ3))). apply pairv_and; [apply fun_okDI|]. apply pairv_and.
  - exact (tots_okDI R i0 f t σ3 Ht3 σA VA (mfut_refl _)).
  - apply pairv_and.
    + split; [|reflexivity]. unfold tentry.
      replace (tget _ _) with (Some (genI t, [D])) by (symmetry; exact (tget_A (genI t) D σ3)).
      reflexivity.
    + exact (step_okDI R i0 f Hf t σ3 Ht3 σA VA (mfut_refl _)).
Qed.

End AnyIndex.
