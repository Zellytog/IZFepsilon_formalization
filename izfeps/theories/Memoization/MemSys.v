(** * A computational system with non-determinism and memoized streams

    Codes: λₙ.e, the integers n, succ, ndnat (non-deterministic: ndnat·c
    reduces to any integer), memo, memo₁ g, lookupₗ. memo·g·c₀ allocates
    a table ℓ, with generator g and first element c₀, and returns
    lookupₗ. lookupₗ·n returns element n of the stream; if it is missing,
    it fills the table in order: element k+1 is a reduct of
    g·(element k), recorded unless it was filled in the meantime.

    States: logs of events (most recent first); the future is log
    extension. Σ is the set of valid logs: each recorded element is an
    actual reduct of the generator, computed from an earlier valid
    state. *)

From Stdlib Require Import List Arith Lia Wellfounded.Inverse_Image Wf_nat.
Import ListNotations.
From IZFe Require Import Frame CompSys.

Inductive code : Type :=
| Lam (n : nat) (e : gex code)
| Num (n : nat)
| Succ | NdNat | Memo
| Memo1 (g : code)
| Lookup (l : nat).

Inductive event := EAlloc (g c0 : code) | EEntry (l : nat) (c : code).
Definition log := list event.

Fixpoint upd {A} (l : nat) (f : A -> A) (xs : list A) : list A :=
  match xs, l with
  | [], _ => []
  | x :: xs, 0 => f x :: xs
  | x :: xs, S l => x :: upd l f xs
  end.

Fixpoint tbls (σ : log) : list (code * list code) :=
  match σ with
  | [] => []
  | EAlloc g c0 :: σ => tbls σ ++ [(g, [c0])]
  | EEntry l c :: σ => upd l (fun p => (fst p, snd p ++ [c])) (tbls σ)
  end.

Definition tget (σ : log) (l : nat) : option (code * list code) := nth_error (tbls σ) l.
Definition tlen (σ : log) (l : nat) : nat := match tget σ l with Some (_, s) => length s | None => 0 end.
Definition tentry (σ : log) (l n : nat) : option code :=
  match tget σ l with Some (_, s) => nth_error s n | None => None end.
Definition tgen (σ : log) (l : nat) : option code := match tget σ l with Some (g, _) => Some g | None => None end.
Definition tlast (σ : log) (l : nat) : option code := tentry σ l (tlen σ l - 1).

Definition fill (l : nat) (c : code) (σ σ1 : log) : log :=
  if Nat.eqb (tlen σ1 l) (tlen σ l) then EEntry l c :: σ1 else σ1.

Inductive mred : code -> code -> log -> log -> code -> Prop :=
| r_lamS n e a σ : mred (Lam (S n) e) a σ σ (Lam n (subst0 e a))
| r_lam0 e a σ σ' r : mered (subst0 e a) σ σ' r -> mred (Lam 0 e) a σ σ' r
| r_succ n σ : mred Succ (Num n) σ σ (Num (S n))
| r_nd c n σ : mred NdNat c σ σ (Num n)
| r_memo g σ : mred Memo g σ σ (Memo1 g)
| r_memo1 g c0 σ : mred (Memo1 g) c0 σ (EAlloc g c0 :: σ) (Lookup (length (tbls σ)))
| r_hit l n σ c : tentry σ l n = Some c -> mred (Lookup l) (Num n) σ σ c
| r_fill l n σ g last σ1 c σ' r : tlen σ l <= n -> tgen σ l = Some g -> tlast σ l = Some last ->
    mred g last σ σ1 c -> mred (Lookup l) (Num n) (fill l c σ σ1) σ' r -> mred (Lookup l) (Num n) σ σ' r
with mered : gex code -> log -> log -> code -> Prop :=
| er_c c σ : mered (gc c) σ σ c
| er_a f a σ σ1 cf σ2 ca σ3 r : mered f σ σ1 cf -> mered a σ1 σ2 ca -> mred cf ca σ2 σ3 r -> mered (ga f a) σ σ3 r.

Inductive mterm : code -> code -> log -> Prop :=
| t_lamS n e a σ : mterm (Lam (S n) e) a σ
| t_lam0 e a σ : meterm (subst0 e a) σ -> mterm (Lam 0 e) a σ
| t_succ n σ : mterm Succ (Num n) σ
| t_nd c σ : mterm NdNat c σ
| t_memo g σ : mterm Memo g σ
| t_memo1 g c0 σ : mterm (Memo1 g) c0 σ
| t_hit l n σ c : tentry σ l n = Some c -> mterm (Lookup l) (Num n) σ
| t_fill l n σ g last : tlen σ l <= n -> tgen σ l = Some g -> tlast σ l = Some last -> mterm g last σ ->
    (forall σ1 c, mred g last σ σ1 c -> mterm (Lookup l) (Num n) (fill l c σ σ1)) -> mterm (Lookup l) (Num n) σ
with meterm : gex code -> log -> Prop :=
| et_c c σ : meterm (gc c) σ
| et_a f a σ : meterm f σ -> (forall σ1 cf, mered f σ σ1 cf -> meterm a σ1) ->
    (forall σ1 cf σ2 ca, mered f σ σ1 cf -> mered a σ1 σ2 ca -> mterm cf ca σ2) -> meterm (ga f a) σ.

Inductive valid : log -> Prop :=
| v_nil : valid []
| v_alloc g c0 σ : valid σ -> valid (EAlloc g c0 :: σ)
| v_entry l c σa σ1 g last : valid σa -> tgen σa l = Some g -> tlast σa l = Some last ->
    mred g last σa σ1 c -> valid σ1 -> tlen σ1 l = tlen σa l -> valid (EEntry l c :: σ1).

Definition mfut (σ σ' : log) : Prop := exists ext, σ' = ext ++ σ.

Scheme mred_mut := Induction for mred Sort Prop with mered_mut := Induction for mered Sort Prop.
Scheme mterm_mut := Induction for mterm Sort Prop with meterm_mut := Induction for meterm Sort Prop.

(** ** Basic properties *)

Lemma mfut_refl σ : mfut σ σ.
Proof. exists []. reflexivity. Qed.

Lemma mfut_trans σ1 σ2 σ3 : mfut σ1 σ2 -> mfut σ2 σ3 -> mfut σ1 σ3.
Proof. intros [e1 ->] [e2 ->]. exists (e2 ++ e1). apply app_assoc. Qed.

Lemma fill_fut l c σ σ1 : mfut σ1 (fill l c σ σ1).
Proof. unfold fill. destruct Nat.eqb; [exists [EEntry l c]; reflexivity|apply mfut_refl]. Qed.

Lemma mred_fut : forall f a σ σ' r, mred f a σ σ' r -> mfut σ σ'.
Proof.
  apply (mred_mut (fun f a σ σ' r _ => mfut σ σ') (fun e σ σ' r _ => mfut σ σ')); intros; try apply mfut_refl; auto.
  - exists [EAlloc g c0]. reflexivity.
  - eapply mfut_trans; [eassumption|]. eapply mfut_trans; [apply fill_fut|eassumption].
  - eapply mfut_trans; [eassumption|eapply mfut_trans; eassumption].
Qed.

Lemma mred_valid : forall f a σ σ' r, mred f a σ σ' r -> valid σ -> valid σ'.
Proof.
  apply (mred_mut (fun f a σ σ' r _ => valid σ -> valid σ') (fun e σ σ' r _ => valid σ -> valid σ')); intros; auto.
  - constructor; assumption.
  - apply H0. unfold fill. destruct (Nat.eqb (tlen σ1 l) (tlen σ l)) eqn:E; [|auto].
    apply Nat.eqb_eq in E. econstructor; eauto.
Qed.

Lemma mprogress : forall f a σ, mterm f a σ -> exists σ' r, mred f a σ σ' r.
Proof.
  apply (mterm_mut (fun f a σ _ => exists σ' r, mred f a σ σ' r) (fun e σ _ => exists σ' r, mered e σ σ' r)).
  - intros. do 2 eexists. constructor.
  - intros e a σ m (σ' & r & H). exists σ', r. constructor; exact H.
  - intros. do 2 eexists. constructor.
  - intros c σ. exists σ, (Num 0). constructor.
  - intros. do 2 eexists. constructor.
  - intros. do 2 eexists. constructor.
  - intros l n σ c H. exists σ, c. constructor; exact H.
  - intros l n σ g last Hl Hg Hlast mg (σ1 & c & H) mk IHk. destruct (IHk σ1 c H) as (σ' & r & K).
    exists σ', r. eapply r_fill; eauto.
  - intros c σ. exists σ, c. constructor.
  - intros f a σ mf (σ1 & cf & H1) ma IHa mt IHt. destruct (IHa σ1 cf H1) as (σ2 & ca & H2).
    destruct (IHt σ1 cf σ2 ca H1 H2) as (σ3 & r & H3). exists σ3, r. econstructor; eauto.
Qed.

(** ** The computational system *)

Lemma mered_ered e σ σ' r : mered e σ σ' r -> ered mred e σ σ' r.
Proof.
  revert σ σ' r. induction e; intros σ σ' r H; inversion H; subst; cbn.
  - split; reflexivity.
  - do 4 eexists. split; [apply IHe1; eassumption|split; [apply IHe2; eassumption|eassumption]].
Qed.

Lemma ered_mered e σ σ' r : ered mred e σ σ' r -> mered e σ σ' r.
Proof.
  revert σ σ' r. induction e; intros σ σ' r H; cbn in H.
  - destruct H.
  - destruct H as [-> ->]. constructor.
  - destruct H as (σ1 & cf & σ2 & ca & H1 & H2 & H3). econstructor; eauto.
Qed.

Lemma eterm_meterm e σ : eterm mred mterm e σ -> meterm e σ.
Proof.
  revert σ. induction e; intros σ H; cbn in H.
  - destruct H.
  - constructor.
  - destruct H as [Hf K]. constructor; [apply IHe1, Hf| |].
    + intros σ1 cf H1. apply IHe2, (K _ _ (mered_ered _ _ _ _ H1)).
    + intros σ1 cf σ2 ca H1 H2. exact (proj2 (K _ _ (mered_ered _ _ _ _ H1)) _ _ (mered_ered _ _ _ _ H2)).
Qed.

Definition MemCS : cs.
Proof.
  refine {| cd := code; st := log; ok := valid; st0 := []; ok0 := v_nil; fut := mfut;
            fut_refl := mfut_refl; fut_trans := mfut_trans; red := mred; term := mterm;
            red_fut := mred_fut; lam := Lam |}.
  - intros f a σ σ' r Ok H. exact (mred_valid _ _ _ _ _ H Ok).
  - intros f a σ _ H. exact (mprogress _ _ _ H).
  - intros n e a σ σ' r H. inversion H; subst. split; reflexivity.
  - intros. constructor.
  - intros e a σ σ' r H. inversion H; subst. apply mered_ered. assumption.
  - intros e a σ H. constructor. apply eterm_meterm, H.
Defined.

(** ** Tables only grow *)

Lemma nth_upd {A} l (f : A -> A) xs k :
  nth_error (upd l f xs) k = if Nat.eqb k l then option_map f (nth_error xs l) else nth_error xs k.
Proof.
  revert l k. induction xs as [|x xs IH]; intros l k.
  - destruct l, k; cbn; try reflexivity; destruct (Nat.eqb k l); reflexivity.
  - destruct l as [|l], k as [|k]; cbn; try reflexivity. apply IH.
Qed.

Lemma length_upd {A} l (f : A -> A) xs : length (upd l f xs) = length xs.
Proof. revert l. induction xs; intros [|l]; cbn; auto. Qed.

Definition sub_tbls (σ σ' : log) : Prop :=
  forall l g s, tget σ l = Some (g, s) -> exists s', tget σ' l = Some (g, s ++ s').

Lemma sub_tbls_refl σ : sub_tbls σ σ.
Proof. intros l g s H. exists []. rewrite app_nil_r. exact H. Qed.

Lemma sub_tbls_trans σ1 σ2 σ3 : sub_tbls σ1 σ2 -> sub_tbls σ2 σ3 -> sub_tbls σ1 σ3.
Proof.
  intros H1 H2 l g s H. destruct (H1 _ _ _ H) as [s1 K1]. destruct (H2 _ _ _ K1) as [s2 K2].
  exists (s1 ++ s2). rewrite app_assoc. exact K2.
Qed.

Lemma sub_tbls_step e σ : sub_tbls σ (e :: σ).
Proof.
  intros l g s H. unfold tget in *. destruct e as [g' c0|l' c]; cbn.
  - exists []. rewrite app_nil_r. rewrite nth_error_app1; [exact H|]. apply nth_error_Some. congruence.
  - rewrite nth_upd. destruct (Nat.eqb l l') eqn:E.
    + apply Nat.eqb_eq in E. subst. rewrite H. exists [c]. reflexivity.
    + exists []. rewrite app_nil_r. exact H.
Qed.

Lemma sub_tbls_fut σ σ' : mfut σ σ' -> sub_tbls σ σ'.
Proof.
  intros [ext ->]. induction ext as [|e ext IH]; [apply sub_tbls_refl|].
  eapply sub_tbls_trans; [exact IH|apply sub_tbls_step].
Qed.

Lemma tentry_fut σ σ' l n c : mfut σ σ' -> tentry σ l n = Some c -> tentry σ' l n = Some c.
Proof.
  intros F H. unfold tentry in *. destruct (tget σ l) as [[g s]|] eqn:E; [|discriminate].
  destruct (sub_tbls_fut _ _ F _ _ _ E) as [s' K]. rewrite K. rewrite nth_error_app1; [exact H|].
  apply nth_error_Some. congruence.
Qed.

Lemma tgen_fut σ σ' l g : mfut σ σ' -> tgen σ l = Some g -> tgen σ' l = Some g.
Proof.
  intros F H. unfold tgen in *. destruct (tget σ l) as [[g0 s]|] eqn:E; [|discriminate]. injection H as ->.
  destruct (sub_tbls_fut _ _ F _ _ _ E) as [s' K]. rewrite K. reflexivity.
Qed.

Lemma tlen_fut σ σ' l : mfut σ σ' -> tlen σ l <= tlen σ' l.
Proof.
  intros F. unfold tlen. destruct (tget σ l) as [[g s]|] eqn:E; [|lia].
  destruct (sub_tbls_fut _ _ F _ _ _ E) as [s' K]. rewrite K, length_app. lia.
Qed.

Lemma tentry_lt σ l n : n < tlen σ l -> exists c, tentry σ l n = Some c.
Proof.
  unfold tlen, tentry. destruct (tget σ l) as [[g s]|]; [|lia]. intros H.
  destruct (nth_error s n) eqn:E; [eauto|]. apply nth_error_None in E. lia.
Qed.

Lemma tentry_some_lt σ l n c : tentry σ l n = Some c -> n < tlen σ l.
Proof.
  unfold tlen, tentry. destruct (tget σ l) as [[g s]|]; [|discriminate]. intros H.
  apply nth_error_Some. congruence.
Qed.

Lemma tbls_nonempty σ l g s : tget σ l = Some (g, s) -> s <> [].
Proof.
  unfold tget. revert l g s. induction σ as [|[g' c0|l' c] σ IH]; intros l g s H; cbn in H.
  - destruct l; discriminate.
  - destruct (Nat.lt_ge_cases l (length (tbls σ))) as [L|L].
    + rewrite nth_error_app1 in H by exact L. eapply IH, H.
    + rewrite nth_error_app2 in H by exact L. destruct (l - length (tbls σ)) as [|k]; cbn in H.
      * injection H as -> <-. discriminate.
      * destruct k; discriminate.
  - rewrite nth_upd in H. destruct (Nat.eqb l l'); [|eapply IH, H].
    destruct (nth_error (tbls σ) l') as [[g0 s0]|]; cbn in H; [|discriminate]. injection H as -> <-.
    destruct s0; discriminate.
Qed.

(** Two suffixes of the same log are comparable. *)
Lemma suffix_cmp σ1 σ2 σ : mfut σ1 σ -> mfut σ2 σ -> mfut σ1 σ2 \/ mfut σ2 σ1.
Proof.
  intros [e1 ->] [e2 E]. revert e2 E. induction e1 as [|x e1 IH]; intros e2 E.
  - right. exists e2. exact E.
  - destruct e2 as [|y e2]; cbn in E.
    + left. exists (x :: e1). symmetry. exact E.
    + injection E as -> E. apply (IH e2 E).
Qed.

Lemma length_fut σ σ' : mfut σ σ' -> length σ <= length σ'.
Proof. intros [e ->]. rewrite length_app. lia. Qed.

Lemma valid_tail e σ : valid (e :: σ) -> valid σ.
Proof. intros H. inversion H; subst; assumption. Qed.

Lemma valid_fut σ σ' : mfut σ σ' -> valid σ' -> valid σ.
Proof. intros [ext ->]. induction ext; cbn; auto. intros H. apply IHext, (valid_tail _ _ H). Qed.

Lemma length_tbls_fut σ σ' : mfut σ σ' -> length (tbls σ) <= length (tbls σ').
Proof.
  intros [ext ->]. induction ext as [|[g c0|l c] ext IH]; cbn; [lia| |].
  - rewrite length_app. cbn. lia.
  - rewrite length_upd. exact IH.
Qed.

Lemma tentry_alloc g c0 σ l k c : tget σ l <> None -> tentry (EAlloc g c0 :: σ) l k = Some c -> tentry σ l k = Some c.
Proof.
  intros H. unfold tentry, tget in *. cbn. rewrite nth_error_app1; [exact (fun x => x)|].
  apply nth_error_Some, H.
Qed.

Lemma tentry_entry l' c' σ l k c : tentry (EEntry l' c' :: σ) l k = Some c ->
  tentry σ l k = Some c \/ (l' = l /\ c' = c /\ k = tlen σ l).
Proof.
  unfold tentry, tlen, tget. cbn. rewrite nth_upd. destruct (Nat.eqb l l') eqn:E; [|left; exact H].
  apply Nat.eqb_eq in E. subst l'. destruct (nth_error (tbls σ) l) as [[g s]|]; cbn; [|discriminate].
  intros H. destruct (Nat.lt_ge_cases k (length s)) as [L|L].
  - left. rewrite nth_error_app1 in H by exact L. exact H.
  - right. rewrite nth_error_app2 in H by exact L. destruct (k - length s) as [|j] eqn:K; cbn in H.
    + injection H as <-. split; [reflexivity|split; [reflexivity|lia]].
    + destruct j; discriminate.
Qed.

Lemma tlen_entry l c σ : tget σ l <> None -> tlen (EEntry l c :: σ) l = S (tlen σ l).
Proof.
  unfold tlen, tget. cbn. rewrite nth_upd, Nat.eqb_refl. destruct (nth_error (tbls σ) l) as [[g s]|]; [|congruence].
  intros _. cbn. rewrite length_app. cbn. lia.
Qed.

Lemma fill_valid l c σ σ1 g last : valid σ -> tgen σ l = Some g -> tlast σ l = Some last ->
  mred g last σ σ1 c -> valid (fill l c σ σ1).
Proof.
  intros V Hg Hl Hr. pose proof (mred_valid _ _ _ _ _ Hr V) as V1. unfold fill.
  destruct (Nat.eqb (tlen σ1 l) (tlen σ l)) eqn:E; [|exact V1]. apply Nat.eqb_eq in E.
  eapply v_entry; [exact V|exact Hg|exact Hl|exact Hr|exact V1|exact E].
Qed.

(** A reduction of lookup returns the requested element of the stream. *)
Lemma lookup_red l n σ σ' r : mred (Lookup l) (Num n) σ σ' r -> tentry σ' l n = Some r.
Proof.
  intros H. remember (Lookup l) as f. remember (Num n) as a. revert Heqf Heqa.
  induction H; intros Ef Ea; try discriminate.
  - injection Ef as ->. injection Ea as ->. exact H.
  - apply IHmred2; assumption.
Qed.

(** ** The invariant of memoized streams

    If c₀ realizes P(0) at allocation, and if the generator g sends every
    realizer of P(k) to realizers of P(k+1) (relating the old and the new
    element by Link), then, in every valid future state, element k of the
    table realizes P(k), and two consecutive elements are related by
    Link. *)

Section Stream.

Context (g c0 : code) (σ0 : log).
Local Notation l := (length (tbls σ0)).
Local Notation σA := (EAlloc g c0 :: σ0).
Context (VA : valid σA).
Context (P : nat -> sprop MemCS) (Link : code -> code -> Prop).
Context (P0 : P 0 σA c0).
Context (Hstep : forall σ c k, valid σ -> mfut σA σ -> P k σ c ->
  wpa MemCS g c σ (fun σ' c' => P (S k) σ' c' /\ Link c c')).

Lemma tget_A : tget σA l = Some (g, [c0]).
Proof. unfold tget. cbn. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma after_A σ : mfut σA σ -> exists s, tget σ l = Some (g, c0 :: s).
Proof. intros F. destruct (sub_tbls_fut _ _ F _ _ _ tget_A) as [s H]. exists s. exact H. Qed.

(** Every suffix that knows table ℓ is a future of the allocation. *)
Lemma knows_A σa σ : mfut σa σ -> mfut σA σ -> tget σa l <> None -> mfut σA σa.
Proof.
  intros F1 F2 H. destruct (suffix_cmp _ _ _ F1 F2) as [K|K]; [|exact K].
  destruct K as [[|e ext] E].
  - cbn in E. subst. apply mfut_refl.
  - exfalso. apply H. cbn in E. injection E as _ E.
    assert (F : mfut σa σ0) by (exists ext; exact E).
    unfold tget. apply nth_error_None. apply length_tbls_fut, F.
Qed.

Lemma stream σ : valid σ -> mfut σA σ ->
  (forall k c, tentry σ l k = Some c -> P k σ c) /\
  (forall k c c', tentry σ l k = Some c -> tentry σ l (S k) = Some c' -> Link c c').
Proof.
  induction σ as [σ IH] using (well_founded_induction (wf_inverse_image _ nat _ (@length _) lt_wf)).
  intros V [[|e ext] E].
  - cbn in E. subst σ. unfold tentry. rewrite tget_A. split.
    + intros [|[|k]] c H; cbn in H; try discriminate. injection H as <-. exact P0.
    + intros [|k] c c' H H'; cbn in *; discriminate.
  - cbn in E. set (σ' := ext ++ σA) in E. subst σ.
    assert (F' : mfut σA σ') by (exists ext; reflexivity).
    assert (V' : valid σ') by exact (valid_tail _ _ V).
    assert (Fs : mfut σ' (e :: σ')) by (exists [e]; reflexivity).
    destruct (IH σ' ltac:(cbn; lia) V' F') as [IP IL].
    destruct (after_A _ F') as [s0 Hs0].
    destruct e as [g' c0'|l' c].
    + assert (Hk : tget σ' l <> None) by congruence. split.
      * intros k c H. eapply sp_stable; [exact Fs|]. apply IP, (tentry_alloc _ _ _ _ _ _ Hk H).
      * intros k c c' H H'. apply (IL k); eapply tentry_alloc; eassumption.
    + inversion V as [| |l0 c1 σa σ1 g'' last Va Hg Hlast Hred V1 Hlen]; subst.
      assert (Fa : mfut σa σ') by exact (mred_fut _ _ _ _ _ Hred).
      destruct (Nat.eq_dec l' l) as [El|El].
      * subst l'. assert (FA : mfut σA σa) by (apply (knows_A σa σ'); [exact Fa|exact F'|unfold tgen in Hg; destruct (tget σa l); congruence]).
        assert (Eg : g'' = g).
        { pose proof (tgen_fut _ _ l g FA ltac:(unfold tgen; rewrite tget_A; reflexivity)). congruence. }
        subst g''. destruct (IH σa ltac:(pose proof (length_fut _ _ Fa); cbn; lia) Va FA) as [IPa ILa].
        destruct (after_A _ FA) as [sa Hsa].
        assert (Lpos : tlen σa l = S (length sa)) by (unfold tlen; rewrite Hsa; reflexivity).
        assert (Plast : P (tlen σa l - 1) σa last) by (apply IPa; exact Hlast).
        destruct (Hstep _ _ _ Va FA Plast) as [_ K]. destruct (K _ _ Hred) as [Pc Lc].
        replace (S (tlen σa l - 1)) with (tlen σ' l) in Pc by lia.
        assert (Elast : tentry σ' l (tlen σ' l - 1) = Some last).
        { rewrite Hlen. exact (tentry_fut _ _ _ _ _ Fa Hlast). }
        split.
        -- intros k c' H. destruct (tentry_entry _ _ _ _ _ _ H) as [H1|(_ & <- & ->)].
           ++ eapply sp_stable; [exact Fs|]. apply IP, H1.
           ++ eapply sp_stable; [exact Fs|exact Pc].
        -- intros k c1 c2 H1 H2.
           destruct (tentry_entry _ _ _ _ _ _ H1) as [K1|(_ & <- & ->)];
           destruct (tentry_entry _ _ _ _ _ _ H2) as [K2|(_ & <- & E2)].
           ++ exact (IL _ _ _ K1 K2).
           ++ replace k with (tlen σ' l - 1) in K1 by lia. rewrite Elast in K1. injection K1 as <-. exact Lc.
           ++ pose proof (tentry_some_lt _ _ _ _ K2). lia.
           ++ lia.
      * split.
        -- intros k c' H. destruct (tentry_entry _ _ _ _ _ _ H) as [H1|(? & _)]; [|congruence].
           eapply sp_stable; [exact Fs|]. apply IP, H1.
        -- intros k c1 c2 H1 H2.
           destruct (tentry_entry _ _ _ _ _ _ H1) as [K1|(? & _)]; [|congruence].
           destruct (tentry_entry _ _ _ _ _ _ H2) as [K2|(? & _)]; [|congruence].
           exact (IL _ _ _ K1 K2).
Qed.

Lemma lookup_term : forall m n σ, S n - tlen σ l <= m -> valid σ -> mfut σA σ -> mterm (Lookup l) (Num n) σ.
Proof.
  induction m as [|m IH]; intros n σ M V F.
  - destruct (tentry_lt σ l n ltac:(lia)) as [c Hc]. eapply t_hit; exact Hc.
  - destruct (Nat.lt_ge_cases n (tlen σ l)) as [L|L].
    + destruct (tentry_lt σ l n L) as [c Hc]. eapply t_hit; exact Hc.
    + destruct (after_A _ F) as [s Hs].
      assert (Hg : tgen σ l = Some g) by (unfold tgen; rewrite Hs; reflexivity).
      assert (Hlen : tlen σ l = S (length s)) by (unfold tlen; rewrite Hs; reflexivity).
      destruct (tentry_lt σ l (tlen σ l - 1) ltac:(lia)) as [last Hlast].
      pose proof (proj1 (stream σ V F) _ _ Hlast) as Plast.
      destruct (Hstep _ _ _ V F Plast) as [T K].
      eapply t_fill; [exact L|exact Hg|exact Hlast|exact T|].
      intros σ1 c Hr. pose proof (mred_fut _ _ _ _ _ Hr) as F1.
      assert (V2 : valid (fill l c σ σ1)) by (eapply fill_valid; eauto).
      assert (F2 : mfut σA (fill l c σ σ1)) by (eapply mfut_trans; [exact F|eapply mfut_trans; [exact F1|apply fill_fut]]).
      apply IH; [|exact V2|exact F2].
      assert (G : tlen σ l < tlen (fill l c σ σ1) l).
      { pose proof (tlen_fut _ _ l F1). unfold fill. destruct (Nat.eqb (tlen σ1 l) (tlen σ l)) eqn:E.
        - rewrite tlen_entry; [lia|]. destruct (after_A _ (mfut_trans _ _ _ F F1)) as [s1 Hs1]. congruence.
        - apply Nat.eqb_neq in E. lia. }
      lia.
Qed.

Lemma lookup_wpa n σ : valid σ -> mfut σA σ ->
  wpa MemCS (Lookup l) (Num n) σ (fun σ' c => tentry σ' l n = Some c /\ valid σ' /\ mfut σA σ').
Proof.
  intros V F. split; [eapply lookup_term; [reflexivity|exact V|exact F]|].
  intros σ' r Hr. split; [exact (lookup_red _ _ _ _ _ Hr)|].
  split; [exact (mred_valid _ _ _ _ _ Hr V)|exact (mfut_trans _ _ _ F (mred_fut _ _ _ _ _ Hr))].
Qed.

End Stream.
