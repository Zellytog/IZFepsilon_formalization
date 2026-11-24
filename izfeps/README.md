# IZFε — Rocq formalisation

Formalisation of the paper *IZFepsilon: A decomposition of realizability for
intuitionistic set theory*. Self-contained project: it depends only on the
Rocq Stdlib (no category-theory library, no generic machinery for formal
systems).

There are no axioms and no `Admitted`. `theories/Check.v` runs
`Print Assumptions` on the main results, and they all answer *Closed under
the global context*. The meta-theoretical hypotheses of the model (fixed
point, collection, Φ essentially small) are named hypotheses (`Context`),
as announced in the paper. The same goes for choice in the meta-theory
(`AC_dom`) in the versions of CC/DC with arbitrary indices.

## Building

Requires Rocq ≥ 9.2 (for the `Abbreviation` command) and the Rocq Stdlib.

```sh
make
```

## Layout

All files live under the logical prefix `IZFe` (`-Q theories IZFe` in `_RocqProject`).

| Folder | Contents |
|---|---|
| `theories/Sec2_IZFeps` | Section 2: syntax, deduction, the theories IZF⁻ε / IZFε / IZF⁺ε, Theorems 7 and 8 |
| `theories/Sec3_Conservativity` | Section 3: IZF, Lemmas 10, 11, 16, Theorems 12 and 17 (extension by definition) |
| `theories/Sec4_Realizability` | Section 4: evidenced frames, V(E), soundness, Theorem 26 |
| `theories/Sec5_IntensionalSets` | Section 5: Sεt, the Sεt-tripos, ∇, Sεt[T] and Set[E], assemblies |
| `theories/Examples` | PCAs as evidenced frames, a PCA on ℕ and its model V(E) |
| `theories/MCA` | Monadic combinatory algebras (Cohen–Grunfeld–Kirst–Miquey): frame, fixed point, model, a non-deterministic instance |
| `theories/Memoization` | Computational systems (Cohen–Miquey–Tate), memoized streams, CC and DC |
| `theories/Check.v` | `Print Assumptions` on the main results |

The folders follow the paper, not the dependency order: Theorems 7 and 8
(Section 2) use Lemmas 10 and 11 (Section 3), for instance.

## Paper ↔ Rocq correspondence

| Paper | File | Rocq statement |
|---|---|---|
| Def. 1, 5 (signature Lₙ) | `Sec2_IZFeps/Syntax.v` | mutual inductive `term`/`form`; the binders `tsep`, `trepl` replace the tower Lₙ (`tlevel`/`flevel` measure the level) |
| Remark 2 (intensional equality) | `Sec2_IZFeps/Deriv.v` | `p_refl`, `p_leib` |
| Def. 3 (IZF⁻ε) | `Sec2_IZFeps/Theories.v` | `IZFm` (axioms `A_empty` … `A_coll`) |
| Def. 6 (IZFε) | `Sec2_IZFeps/Theories.v` | `IZFe` (`A_repl`, `A_seppow`, `A_powres`) |
| Def. 15 (IZF⁺ε) | `Sec2_IZFeps/Theories.v` | `IZFp` (`A_ext`) |
| — (closure under substitution) | `Sec2_IZFeps/Theories.v` | `IZFm_closed`, `IZFe_closed`, `IZFp_closed` |
| Theorem 7 (induction on ω) | `Sec2_IZFeps/Arith.v` | `thm7` |
| Theorem 8 (recursion, Knaster–Tarski) | `Sec2_IZFeps/Recursion.v` | `thm8`, `thm8_closed`; ω × X: `tW`, `mem_W`; least closed relation: `tf`; `f_zero`, `f_step`, `f_inv`; S injective and ≠ 0: `suc_inj`, `suc_ne0` |
| Kuratowski pairs (Section 2.2) | `Sec2_IZFeps/Pairs.v` | `kp_inj` |
| IZF (Section 3) | `Sec3_Conservativity/ISyntax.v` | `iform`, `iprv`, `IZF` (weak power set, weak collection) |
| Lemma 10.1–10.6 | `Sec3_Conservativity/Basic.v` | `sub_refl`, `eps_mem`, `sub_of_mem`, `sub_mem_trans`, `sub_trans`, `sub_iff` |
| Lemma 11 | `Sec3_Conservativity/Extension.v` | `lemma11` (usable form: `l11_conv`) |
| Theorem 12 | `Sec3_Conservativity/Thm12.v` | `IZF_tr` (axioms), `thm12` (derivations), `IZFm_extends_IZF` |
| Lemma 16 | `Sec3_Conservativity/Conserv.v` | `lemma16`, `sub_eps` |
| Theorem 13 (extension by definition), on the whole tower Lₙ | `Sec3_Conservativity/Graph.v` | graphs `G` of terms, translation `T` of L_IZF⁺ε into L_IZF |
| — (the translation commutes with substitutions) | `Sec3_Conservativity/GSubst.v` | `GT_subst` |
| Theorem 17: ∃! of values | `Sec3_Conservativity/ED.v`, `Repl.v` | `ED_var` … `ED_omega`, `ED_repl`; all terms: `HED` |
| Theorem 17: axioms | `Sec3_Conservativity/Ax17.v` | `ax_empty` … `ax_ext`, `HAX` |
| Theorem 17: rules, conservativity | `Sec3_Conservativity/Thm17.v` | `sound17`, `T_tr`, `thm17`; `conservative_IZFe`, `conservative_IZFm`, `IZFm_iff`, `IZFe_iff`, `IZFp_iff` |
| Def. 18 (evidenced frames, with universal implication) | `Sec4_Realizability/Frame.v` | `frame` (`fuimp`, `f_ulam`, `f_uev`); derived: `fimp`, `fallP`, `f_genP`, `e_incl`; encoded ⊥, ∨, ⋃: `fbot`, `for_`, `fex` |
| Notation 19 | `Sec4_Realizability/Frame.v` | `e_app`, `n_orI1/2`, `n_orE`, `f_exI`, `f_exE`, `fbr` |
| Def. 20–21 (operad, fixed point) | `Sec4_Realizability/Frame.v` | `eexp`, `eeval`, `fixpoint_comb` |
| Def. 24 (V(E)) | `Sec4_Realizability/VE.v` | labelled Aczel trees `V`, equality `teq` |
| Def. 25 (interpretation) | `Sec4_Realizability/VE.v`, `Model.v` | `eps`, `vmem`, `vsub`, `veqv`, `veq`, `vempty`, `vpair`, `vunion`, `vpower`, `vsep`, `vomega`, `vrepl`; `evt`/`evf` |
| — ("standard interpretation of formula constructors") | `Sec4_Realizability/Model.v` | `soundness` |
| Theorem 26 | `Sec4_Realizability/Realize.v` | `thm26`, `IZFe_realized` (semantic realizers `R_*`, foundation `R_ind` through the fixed point) |
| Def. 27 (Sεt) | `Sec5_IntensionalSets/Set_eps.v` | `shom`, `sheq`, `sid`, `scomp`, `Seps` |
| Prop. 28 (Sεt is cartesian) | `Sec5_IntensionalSets/Cartesian.v` | `Seps_cart` |
| Def. 29 (tripos, Pitts) | `Sec5_IntensionalSets/Tripos.v` | `preheyting`, `tripos` |
| Prop. 30 (the Sεt-tripos) | `Sec5_IntensionalSets/Tripos.v` | `Seps_tripos` |
| ∇ : Set → Sεt, fibre over ∇X | `Sec5_IntensionalSets/Nabla.v` | `snab`, `nab_id`, `nab_comp`, `toS_mono`, `fromS_mono`, `to_from`, `from_to`, instance `nat_coded` |
| Section 5.3: Sεt[T] (objects (X, ≈), functional relations) | `Sec5_IntensionalSets/Topos.v` | `per`, `tob`, `thom`, `SepsT` (category) |
| Section 5.3: Set[E], and Set[E] → Sεt[T] full subcategory | `Sec5_IntensionalSets/Topos.v` | `ehom`, `SetE`, `eqvX`/`perX` (x ≈X x'), `embed`, `embed_full`, `embed_faithful` |
| Def. 31 (assemblies, pre-assemblies) | `Sec5_IntensionalSets/Asm.v` | `pasm`, `ahom`, `preAsm`, `Asm` |
| Section 5.4: the preAsm[E]-tripos | `Sec5_IntensionalSets/Asm.v` | `preAsm_cart`, `afib`, `preAsm_tripos` |
| Def. 32 (ε-pre-assemblies, ε-assemblies) | `Sec5_IntensionalSets/Asm.v` | `epasm`, `vplus` (V(E)⁺), `easm`, `epasm_pasm`; Sεt = Set[E] between ε-pre-assemblies: `epasm_embed`, `epasm_full`, `epasm_faithful` |
| Frames from PCAs (Ex. 22, PCA case) | `Examples/PCA.v` | `pca`, `pca_frame`, Turing combinator `pca_fix`, `pca_fixpoint`, `pca_consistent` |
| A PCA on ℕ | `Examples/PCA.v`, `NatModel.v` | `natPCA` (coded S, K, application by an interpreter), `nat_frame`, `nat_fixpoint`, `nat_consistent`; V(E) ⊩ IZFε: `nat_IZFe_realized` |
| MCAs with a modality → evidenced frame (CGKM, Def. 3–5, 13, Th. 16) | `MCA/MCAFrame.v` | `mca` (monad, application, λ codes, modality ♢ with After-Return, After-Bind, monotonicity), `mca_frame`; consistency under progress: `mca_consistent` |
| Remark 23: fixed point combinator for MCAs | `MCA/MCAFrame.v` | guarded Turing combinator `mca_fix`, `mca_fixpoint` |
| V(E) ⊩ IZFε for any MCA | `MCA/MCAModel.v` | `mca_IZFe_realized` |
| A non-deterministic MCA (powerset monad, angelic modality) | `MCA/NdMCA.v` | `nd_mca`, `flip_nd`, `nd_fixpoint`, `nd_consistent`, `nd_IZFe_realized` |
| Computational systems (Cohen–Miquey–Tate, Def. IV.1) | `Memoization/CompSys.v` | `cs` (states, Σ = `ok`, future, `red`/`term`, λ codes); weakest preconditions `wpa`, `wp` |
| Demonic evidenced frame (CMT, Def. IV.3) | `Memoization/CompSys.v` | `sprop` (stable predicates), `sent`, `sand`, `suimp`, `cs_frame`; ∃ as a union `sex`, `sbr` |
| System with non-determinism and memoized streams | `Memoization/MemSys.v` | codes `NdNat`, `Memo`, `Memo1`, `Lookup`; logs `log`, `valid`, `mfut`; `MemCS`; stream invariant `stream`, `lookup_wpa` |
| Memoization ⇒ countable choice (Cohen–Abreu Faro–Tate, CMT) | `Memoization/MemChoice.v` | indices in ℕ (computational witnesses): `CCN`, `cc_nat`; arbitrary indices, under `AC_dom (nat * code * log)`: `CCI`, `cc_any` |
| Memoization ⇒ dependent choice | `Memoization/MemChoice.v` | indices in ℕ: `DCN`, `dc_nat`; arbitrary indices, under `AC_dom (Ix * code * log)`: `DCI`, `dc_any` |

## Formalisation choices

- **Syntax.** De Bruijn indices without intrinsic scoping, simultaneous
  substitutions, σ-calculus proven once (`Syntax.v`). Axioms are
  functions of their arguments (terms, and a formula for schemes); their
  free variables are the parameters x⃗, implicitly universal. IZF has its
  own language L_IZF = {∈, ⊆, =} (`ISyntax.v`); the translation φ ↦ φ^ε
  (`Extension.v`, `tr`) reads = as ≃.
- **Proof mode.** Internal derivations use tactics on hypotheses referred
  to by their rank (`spec`, `app`, `mp`, `dex`, `iffm`, `lem`, `rew`,
  `keep`…, in `Deriv.v`/`Theories.v`); `fnorm` normalises substitutions
  on abstract formulas (schemes).
- **Frames.** The primitive structure is the universal implication
  φ ⊃ ⋂S of Cohen–Miquey–Tate (λ, e_ev); φ ⊃ ψ ≜ φ ⊃ ⋂{ψ} and
  ⋂S ≜ ⊤ ⊃ ⋂S are derived from it. Introducing ⋂ with the same evidence
  (the first version of Definition 18) ruled out partial PCAs: for S = ∅
  it requires e·a↓ for every e. Instead, e ⊩ ψ ⩽ φ (∀φ ∈ S) gives
  λ(π₀; e) ⊩ ψ ⩽ ⋂S. ⋂ ranges over subsets of Φ (`Φ → Prop`); ⋂ indexed
  by a type is derived from it.
- **PCAs.** Partial application is presented as a functional relation,
  with k·a, s·a, s·a·b given by functions (K1, S1, S2): abstractions are
  computed without evaluating any application. The PCA on ℕ is that of
  the coded combinators S, K (n = 5q + tag, Cantor pairing for s·x·y),
  with application given by an interpreter that may diverge; it is not
  K1 in the strict sense (acceptable numbering of partial recursive
  functions, universal function, s-m-n), which would require a
  computability development of its own.
- **⟦x ε y⟧** is that of the paper: ⋃ of the labels of the branches of y
  equal (as trees) to x.
- **⟦x = y⟧** is Leibniz equality on the compatible predicates on the
  whole of V(E) (the paper quantifies over predicates on {x, y};
  extending such a predicate would require excluded middle). We never use
  ⟦x = y⟧ ⩽ ⊥ for x ≠ y.
- **Fixed point.** A combinator on the *expressions* of the operad
  (`fixpoint_comb`), a weaker hypothesis than the paper's.
- **Collection.** Hypotheses `coll`, `coll_proper`, `coll_spec`: we
  collect values (∀t β ∃s, ψ(xₜ, β) ≡ ψ(xₜ, B_s)). The collection set is
  that of the paper, and is also used for replacement.
- **Trees.** No quotient; more intensional than set-theoretic V(E). In
  type theory without axioms, an equality between two trees does not give
  back equalities between their components (this would require
  uniqueness of identity proofs between types). Hence:
  - injectivity of Kuratowski pairs is obtained for Leibniz equality, by
    deriving `kp_inj` in the subtheory of the pairing axiom (`Pairs.v`)
    and transporting it into V(E) through `soundness` (`Cartesian.v`,
    `kp_inj_sem`);
  - for ∇, separation of names is the named hypothesis `code_inj` (record
    `coded`), proven for ℕ coded by the sₙ (`snat_inj`).
- **Sεt.** Morphisms are relations on V × V that are compatible, strict,
  total and functional (for Leibniz equality); this is equivalent to the
  indexing by dom(x) × dom(y) of Definition 27.
- **Theorem 17.** Rather than iterating Theorem 13 symbol by symbol, we
  give directly the translation obtained by eliminating all the symbols
  of the tower: each term t becomes its graph G(t, ρ, y) ("y is the value
  of t"), ε and ∈ become ∈, ≃ and = become =. The symbols are read in IZF
  as: ∅; ω = the least inductive set; {x, y}; ⋃x; 𝒫(x) = the power set;
  {α ε a | φ} = separation; {ψ(α) | α ε a} = the total construction
  {β | (∀α ∈ a. ∃!β. ψ) ∧ ∃α ∈ a. ψ(α, β)} (existence by collection). No
  hypothesis remains: uniqueness and existence of values (`HED`), axioms
  (`HAX`), rules (`sound17`), round trip on L_IZF (`T_tr`).
- **Set[E] (Section 5.3).** Compatibility is guarded by ⟦x' ε X⟧ and
  ⟦y' ε Y⟧:
  ⋂ ⟦x' ε X⟧ ∧ ⟦x ≃ x'⟧ ⊃ ⟦y' ε Y⟧ ∧ ⟦y ≃ y'⟧ ⊃ R(x, y) ⊃ R(x', y').
  Without the guards, strictness would force ⟦x' ε X⟧ as soon as
  x' ≃ x ε X, which is false (x' = {(⊥, ∅)} ≃ ∅ ε {(⊤, ∅)}). With them,
  this is the compatibility of Sεt[T] for ≈X, ≈Y, which gives the full
  subcategory. Lemma 10 (≃ is reflexive, symmetric, transitive) is
  transported into V(E) by soundness: Set[E] therefore depends on the
  hypotheses of the model (collection, fixed point).
- **Section 5.4.** Tracking of a function of assemblies, "⋂ₓ E(x) ⊃
  E(f x) is realized", is written ∃e. ∀x. e ⊩ E(x) ⩽ E(f x)
  (equivalent). The claim "an ε-pre-assembly behaves like a
  pre-assembly, but its morphisms in Sεt are those of the topos" is
  rendered as: between ε-pre-assemblies, the morphisms of Sεt and those
  of Set[E] coincide (full and faithful functor, identity on objects and
  relations).
- **Theorem 8.** Stated with graphs: g ⊆ (ω × X) × X with
  ∀n ε ω ∀x ε X ∃!y. y ε X ∧ ⟨⟨n, x⟩, y⟩ ε g, and f ⊆ ω × X with
  ∀n ε ω ∃!y. y ε X ∧ ⟨n, y⟩ ε f, ⟨0, a⟩ ε f and
  ⟨n, x⟩ ε f ∧ ⟨⟨n, x⟩, y⟩ ε g ⇒ ⟨S n, y⟩ ε f (∃! for intensional
  equality). The intersection ⋂{A ε P(ω × X) | F(A) ⊆ A} is taken by
  impredicative separation on ω × X, without going through P(ω × X);
  ω × X ≜ ⋃{{⟨n, x⟩ | x ε X} | n ε ω} by replacement. Injectivity of S
  ("by ε-induction") comes from the absence of 2-cycles x ε y ε x.
- **MCAs.** Ω = Prop. The abstraction laws (λⁿ⁺¹.e · c = η(λⁿ.e[c]),
  λ⁰.e · c = ν(e[c])) are only required through the modality, which is
  all the frame uses; the monad laws are not needed. The separator is the
  set of all codes; the progress condition of Definition 14 only serves
  consistency (`mca_consistent`). The fixed point combinator (not given
  in CGKM) is a guarded Turing combinator y(f) ≜ W·W with
  W ≜ λw. λt. f(w·w)·t: W·W is pure (it returns η(y(f))), so the
  modality sees y(f)·c exactly as f(y(f))·c. The instance is a
  relational λ-calculus with a code flip (flip·c returns λ₁.0 or λ₁.1),
  in the powerset monad with the angelic modality ♢ m Q ≜ ∃x ∈ m. Q(x);
  big-step semantics makes divergence the empty set of results.
- **Computational systems (CMT).** Σ is a predicate `ok` on states
  (rather than a subtype); the separator is the set of all codes. The
  propositions of the demonic frame are the predicates σ, c ↦ Prop that
  are stable under the future; e ⊩ φ ⩽ ψ if, from every state of Σ, every
  realizer of φ is sent by e to a terminating computation all of whose
  reducts realize ψ. Pairs and projections are encoded with λ
  (⟨x, y⟩ ≜ λf. f x y).
- **Memoization.** States are logs of events (allocation of a table,
  recording of an element), the future being log extension; Σ is the set
  of valid logs, where each recorded element is an actual reduct of the
  generator. Tables are *streams*: memo·g·c₀ allocates a table with first
  element c₀ and returns lookupₗ; lookupₗ·n fills the missing elements in
  order (element k+1 is a reduct of g·(element k), recorded unless it was
  filled in the meantime). Non-determinism (ndnat) shows that choice does
  not come from a deterministic computation.
- **Choice over ℕ.** ∃j ∈ ℕ is realized by ⟨n_j, r⟩. For CC, the stream
  memoizes ⟨n, t·d·n⟩; for DC, ⟨j, ⟨i, r⟩⟩ with r ⊩ R(i, j), the generator
  calling t on the previous index. S(n, j) says that element n is memoized
  and carries index j: functionality comes from memoization freezing the
  element. No hypothesis.
- **Choice over an arbitrary I.** ∃i ∈ I is a union, without
  computational witness; an index is attached to each memoized element
  through a named hypothesis of choice in the meta-theory,
  `AC_dom X : ∀Q ⊆ X × I. ∃f. ∀x. (∃i. Q(x, i)) ⇒ Q(x, f x)`, applied to
  the element and to its *recording state* (`recst`, the smallest suffix
  of the log containing it), which does not depend on the current state.
  For CC, X = ℕ × codes × logs is countable: this is countable choice in
  the meta-theory (in relativized form). For DC, the elements are reducts
  of t·d (they realize ∀i ∃j R(i, j)), and the index of element k+1 is
  chosen from that of element k (X = I × codes × logs). The relativized
  form avoids relying on uniqueness of proofs (which AC on a subtype would
  require) or on excluded middle (to make Q total).

## Not formalised (at this stage)

- the conjecture of Section 5.3 (Set[E] → Sεt[T] essentially surjective),
  which is not proven in the paper;
- K1 in the strict sense (see above); collection remains a named
  hypothesis for V(E).
