---
layout: ../../layouts/Deep.astro
title: QIQTH.StandardSubspaceModular
eyebrow: StandardSubspaceModular · section of the QIQT-H book
description: QIQTH.StandardSubspaceModular — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← SpectralTheorem](/browser/qiqth-spectral-spectraltheorem) · [StandardSubspaceModularFlow →](/browser/qiqth-standardsubspacemodularflow) </small>

<small>StandardSubspaceModular · entries 753–807 of 1000</small>

<a id="d-qiqth-standardsubspacemodular-projk"></a>
**Definition 753** (`projK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L44)</small>

**RvD `P`** — the real-orthogonal projection onto the standard subspace `𝒦`.

$$
P\,H\,S \;:=\; (S.\mathrm{cl}).\mathrm{starProjection}
$$

<small>Used by [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge), [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [`gConstancy_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [`oneParticleBW_of_stripKMSrvd_density`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [`oneParticleBW_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-complete), [`oneParticleBW_wedge_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-wedge-complete), and 51 more.</small>

<a id="d-qiqth-standardsubspacemodular-projik"></a>
**Definition 754** (`projIK`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L48)</small>

**RvD `Q`** — the real-orthogonal projection onto `i𝒦 = mulI 𝒦`.

$$
Q\,H\,S \;:=\; (S.\mathrm{cl}.\mathrm{mulI}).\mathrm{starProjection}
$$

<small>Used by [`ComparisonDatum`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum), [`oneParticleBW_of_comparison`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison), [`comparisonDatum_of_gConstancy`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-comparisondatum-of-gconstancy), [`modUnitary_eq_of_orbit_compare`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare), [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`projIK_idem`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik-idem), [`rvdR_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-apply), [`rvdR_inner_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self), and 28 more.</small>

<a id="d-qiqth-standardsubspacemodular-rvdr"></a>
**Definition 755** (`rvdR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L52)</small>

**RvD `R = P + Q`** (Definition 2.1).

$$
R\,H\,S \;:=\; \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{P}\,S + \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{Q}\,S
$$

<small>Used by [`rvdR_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-apply), [`rvdR_inner_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self), [`rvdR_inner_self_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self-nonneg), [`rvdR_inner_self_le`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self-le), [`rvdR_inner_symm`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-symm), [`rvdR_eq_zero`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-eq-zero), [`rvdR_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-smul-i), [`rvdR_smul_complex`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-smul-complex), and 23 more.</small>

<a id="d-qiqth-standardsubspacemodular-projk-idem"></a>
**Lemma 756** (`projK_idem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L55)</small>

`P` is idempotent (a projection).

$$
\mathrm{IsIdempotentElem}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{P}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdRC_mul_rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [`rvdPmQ_mul_rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr), [`rvdSqrtR_range_dense_in_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-range-dense-in-k).</small>

<a id="d-qiqth-standardsubspacemodular-projik-idem"></a>
**Lemma 757** (`projIK_idem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L59)</small>

`Q` is idempotent (a projection).

$$
\mathrm{IsIdempotentElem}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{Q}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdRC_mul_rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [`rvdPmQ_mul_rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr), [`eq_of_mem_K_of_inner_perp_IK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-eq-of-mem-k-of-inner-perp-ik).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-apply"></a>
**Lemma 758** (`rvdR_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L63)</small>

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,\xi = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{P}\,S)\,\xi + (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{Q}\,S)\,\xi
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdR_inner_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self), [`rvdR_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-smul-i), [`rvdPmQ_eq_zero`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-eq-zero), [`modConj_projIK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [`modConj_projK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projk-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-inner-self"></a>
**Lemma 759** (`rvdR_inner_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L67)</small>

**RvD Prop 2.2(1), key identity:** `⟪R ξ, ξ⟫ = ‖P ξ‖² + ‖Q ξ‖²`. (Each projection is self-adjoint idempotent, so `⟪P ξ, ξ⟫ = ‖P ξ‖²`.) This is the quadratic form whose vanishing forces `P ξ = Q ξ = 0`, the crux of `R`'s injectivity and hence of the well-definedness of the modular operator.

$$
\langle {(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,\xi},{\xi}\rangle = {\|(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{P}\,S)\,\xi\|}^{2} + {\|(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{Q}\,S)\,\xi\|}^{2}
$$

*Proof.* By [`rvdR_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-apply). $\square$

<small>Used by [`rvdR_inner_self_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self-nonneg), [`rvdR_inner_self_le`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self-le), [`rvdR_eq_zero`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-eq-zero).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-inner-self-nonneg"></a>
**Lemma 760** (`rvdR_inner_self_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L80)</small>

`0 ≤ ⟪R ξ, ξ⟫` — the lower half of RvD's `0 ≤ R ≤ 2`.

$$
0 \le \langle {(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,\xi},{\xi}\rangle
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`rvdR_inner_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self). $\square$

<small>Used by [`rvdRC_isPositive`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-ispositive).</small>

<a id="d-qiqth-standardsubspacemodular-norm-projk-apply-le"></a>
**Lemma 761** (`norm_projK_apply_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L85)</small>

`P` is a contraction: `‖P ξ‖ ≤ ‖ξ‖`.

$$
\|(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{P}\,S)\,\xi\| \le \|\xi\|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdR_inner_self_le`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self-le).</small>

<a id="d-qiqth-standardsubspacemodular-norm-projik-apply-le"></a>
**Lemma 762** (`norm_projIK_apply_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L89)</small>

`Q` is a contraction: `‖Q ξ‖ ≤ ‖ξ‖`.

$$
\|(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{Q}\,S)\,\xi\| \le \|\xi\|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdR_inner_self_le`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self-le).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-inner-self-le"></a>
**Lemma 763** (`rvdR_inner_self_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L93)</small>

`⟪R ξ, ξ⟫ ≤ 2‖ξ‖²` — the upper half of RvD's `0 ≤ R ≤ 2` (each projection is a contraction, so `‖P ξ‖² + ‖Q ξ‖² ≤ 2‖ξ‖²`).

$$
\langle {(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,\xi},{\xi}\rangle \le 2 \cdot {\|\xi\|}^{2}
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`rvdR_inner_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self), [`norm_projK_apply_le`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-norm-projk-apply-le), [`norm_projIK_apply_le`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-norm-projik-apply-le). $\square$

<small>Used by [`rvdR_le_two`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-le-two).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-inner-symm"></a>
**Lemma 764** (`rvdR_inner_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L106)</small>

**`R` is symmetric** (self-adjoint in the inner-product sense): `⟪R x, y⟫ = ⟪x, R y⟫`. Each projection `P, Q` is self-adjoint (`inner_starProjection_left_eq_right`).  (The stronger *operator-level* statement `IsSelfAdjoint (rvdR S)` — `star R = R` — is `rvdR_isSelfAdjoint` below, available now that `open ClosedSubmodule` supplies `InnerProductSpace ℝ H` and hence the adjoint/`Star` on `H →L[ℝ] H`.)

$$
\langle {(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,x},{y}\rangle = \langle {x},{(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,y}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdRC_isSymmetric`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-issymmetric), [`rvdR_le_two`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-le-two).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-eq-zero"></a>
**Lemma 765** (`rvdR_eq_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L117)</small>

**RvD Prop 2.2(1): `R` is injective.**  If `R ξ = 0` then `⟪R ξ, ξ⟫ = 0`, so by `rvdR_inner_self` both `‖P ξ‖ = ‖Q ξ‖ = 0`; hence `ξ ⊥ 𝒦` and `ξ ⊥ i𝒦`, i.e. `ξ ∈ 𝒦ᗮ ⊓ (i𝒦)ᗮ = (𝒦 ⊔ i𝒦)ᗮ = ⊤ᗮ = ⊥` using `S.IsCyclic` (`𝒦 + i𝒦` dense). Injectivity of `R` is what makes the modular operator well-defined.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,\xi = 0 \to \xi = 0
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`rvdR_inner_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self). $\square$

<small>Used by [`rvdPmQ_eq_zero`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-eq-zero).</small>

<a id="d-qiqth-standardsubspacemodular-projk-isselfadjoint"></a>
**Lemma 766** (`projK_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L166)</small>

`P` is self-adjoint as a bounded operator (`star (projK S) = projK S`).

$$
\mathrm{IsSelfAdjoint}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{P}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdPmQ_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint).</small>

<a id="d-qiqth-standardsubspacemodular-projik-isselfadjoint"></a>
**Lemma 767** (`projIK_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L170)</small>

`Q` is self-adjoint as a bounded operator.

$$
\mathrm{IsSelfAdjoint}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{Q}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdPmQ_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint), [`inner_real_of_mem_K_perp_IK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-inner-real-of-mem-k-perp-ik).</small>

<a id="d-qiqth-standardsubspacemodular-projik-smul-i"></a>
**Lemma 768** (`projIK_smul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L223)</small>

**Conjugation identity (1)**: `Q(i·ξ) = i·(P ξ)` (`projIK = J·projK·J⁻¹`, `J =` mult-by-`i`). Proved by the variational characterization: `i·(P ξ) ∈ i𝒦`, and `i·ξ − i·(P ξ) = i·(ξ − P ξ)` is `⊥ᵣ i𝒦` because mult-by-`i` is an isometry and `ξ − P ξ ⊥ᵣ 𝒦`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{Q}\,S)\,(i \cdot \xi) = i \cdot (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{P}\,S)\,\xi
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`projK_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk-smul-i), [`rvdR_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-smul-i), [`rvdPmQ_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-smul-i), [`modConj_smul_I`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-smul-i), [`inner_real_of_mem_K_perp_IK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-inner-real-of-mem-k-perp-ik).</small>

<a id="d-qiqth-standardsubspacemodular-projk-smul-i"></a>
**Lemma 769** (`projK_smul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L244)</small>

**Conjugation identity (2)**: `P(i·ξ) = i·(Q ξ)`.  Algebraic consequence of (1) (`projIK_smul_I`) via `i·(i··) = −·`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{P}\,S)\,(i \cdot \xi) = i \cdot (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{Q}\,S)\,\xi
$$

*Proof.* By [`projIK_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik-smul-i). $\square$

<small>Used by [`rvdR_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-smul-i), [`rvdPmQ_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-smul-i), [`modConj_smul_I`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-smul-i).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-smul-i"></a>
**Lemma 770** (`rvdR_smul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L255)</small>

**`R = P + Q` is ℂ-linear**: `R(i·ξ) = i·(R ξ)`.  Combines the two conjugation identities; this is exactly the commutation with mult-by-`i` that lets `R` be viewed as a complex-linear operator `Rℂ : H →L[ℂ] H`, on which the complex continuous functional calculus (`CFC.sqrt`) applies.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,(i \cdot \xi) = i \cdot (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,\xi
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`rvdR_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-apply), [`projIK_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik-smul-i), [`projK_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk-smul-i). $\square$

<small>Used by [`rvdR_smul_complex`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-smul-complex), [`rvdRC_isSymmetric`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-issymmetric).</small>

<a id="d-qiqth-standardsubspacemodular-clm-eq-of-eqon-k"></a>
**Lemma 771** (`clm_eq_of_eqOn_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L263)</small>

**Operator equality from equality on `𝒦`** (RvD Theorem 3.8 capstone): two continuous `ℂ`-linear operators that agree on the standard subspace `𝒦` agree everywhere.  By `ℂ`-linearity they then agree on `i𝒦` (`q ∈ i𝒦 ⟹ −i·q ∈ 𝒦`), hence on the algebraic sum `𝒦 + i𝒦`, which is **dense** (`IsCyclic`, `𝒦 ⊔ i𝒦 = ⊤`); continuity finishes.  This lifts the per-vector identity `V_t η = Δ^{it} η` on `𝒦` (from `eq_of_mem_K_of_inner_perp_IK`) to the operator identity `V_t = Δ^{it}` discharging `hUniq`.

$$
(\forall x\in S.\mathrm{cl}, A\,x = B\,x) \to A = B
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`modUnitary_eq_of_orbit_compare`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-smul-complex"></a>
**Lemma 772** (`rvdR_smul_complex`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L288)</small>

**Full ℂ-`map_smul` for `R`**: `R(c·x) = c·(R x)` for every `c : ℂ`.  Decompose `c = c.re + c.im·i`; the real part uses ℝ-linearity, the imaginary part `rvdR_smul_I`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,(c \cdot x) = c \cdot (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,x
$$

*Proof.* By [`rvdR_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-smul-i). $\square$

<small>Used by [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc"></a>
**Definition 773** (`rvdRC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L310)</small>

`R = P + Q` as a genuine **ℂ-linear** continuous operator (same underlying map as `rvdR S`).

$$
R\,H\,S \;:=\; \{\mathrm{toFun} :=(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S) , \mathrm{map\_add}^{\prime} :=\cdots , \mathrm{map\_smul}^{\prime} :=\cdots , \mathrm{cont} :=\cdots \}
$$

<small>Used by [`borelFC_congr_ae`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-borelfc-congr-ae), [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [`rvdSpecMeasure`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure), [`devSpecReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal), [`devSpecReal_measurable`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-measurable), [`devSpecReal_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-devspecreal-norm-le), [`deviceOpReal`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopreal), [`deviceOpC`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc), and 98 more.</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-apply"></a>
**Lemma 774** (`rvdRC_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L317)</small>

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)\,x = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdRC_isPositive`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-ispositive), [`modConj_projIK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [`modConj_projK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projk-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-issymmetric"></a>
**Lemma 775** (`rvdRC_isSymmetric`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L327)</small>

`Rℂ` is **complex-symmetric**: `⟪Rℂ x, y⟫_ℂ = ⟪x, Rℂ y⟫_ℂ`.  `Re` is `rvdR_inner_symm`; `Im` follows from it via the `i`-twist and ℂ-linearity (`rvdR_smul_I`).

$$
((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)).\mathrm{IsSymmetric}
$$

*Proof.* By [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`rvdR_inner_symm`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-symm), [`rvdR_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-smul-i). $\square$

<small>Used by [`rvdRC_isPositive`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-ispositive), [`rvdTwoSubRC_isSymmetric`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric), [`diagInt_specCoord`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-diagint-speccoord).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-ispositive"></a>
**Lemma 776** (`rvdRC_isPositive`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L338)</small>

**`Rℂ` is a positive operator** in the complex C\*-algebra `H →L[ℂ] H`.  Self-adjoint (`rvdRC_isSymmetric`) with `0 ≤ Re⟪Rℂ x, x⟫ = ⟪R x, x⟫_ℝ` (`rvdR_inner_self_nonneg`).  Hence `0 ≤ Rℂ` in the Loewner order and the continuous functional calculus square root `CFC.sqrt (Rℂ)` — the `R^{1/2}` factor of the Rieffel–Van Daele polar decomposition — is available.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S).\mathrm{IsPositive}
$$

*Proof.* By [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`rvdR_inner_self_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self-nonneg), [`rvdRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-apply), [`rvdRC_isSymmetric`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-issymmetric). $\square$

<small>Used by [`rvdRC_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-nonneg).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-nonneg"></a>
**Lemma 777** (`rvdRC_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L347)</small>

`0 ≤ Rℂ` in the Loewner order (operator nonnegativity), from `rvdRC_isPositive`.

This is the maximal honest step toward the RvD square root `R^{1/2}` right now: `Rℂ` is a genuine positive operator, so `R^{1/2} = CFC.sqrt Rℂ` is *mathematically* available — but the Mathlib `CFC.sqrt` requires `StarOrderedRing (H →L[ℂ] H)`, an instance Mathlib has NOT yet established for operator algebras (it is flagged as future work in `InnerProductSpace/Positive.lean`: "when we have `StarOrderedRing (E →L[𝕜] E)`").  So the polar-decomposition factor `R^{1/2}` is blocked on that single missing instance, not on our construction; `rvdRC_isPositive`/`rvdRC_nonneg` is exactly the hypothesis the square root will consume once it lands.

$$
0 \le \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S
$$

*Proof.* By [`rvdRC_isPositive`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-ispositive). $\square$

<small>Used by [`rvdSqrtR_mul_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr-mul-self), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq"></a>
**Definition 778** (`rvdPmQ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L359)</small>

**RvD `P − Q`** — the self-adjoint operator whose polar decomposition `JT = P − Q` (RvD Definition 2.1) yields the modular conjugation `J` and the positive `T`.

$$
(P-Q)\,H\,S \;:=\; \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{P}\,S - \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{Q}\,S
$$

<small>Used by [`rvdPmQ_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint), [`rvdPmQ_eq_zero`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-eq-zero), [`rvdPmQ_injective`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-injective), [`rvdPmQ_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-smul-i), [`rvdRC_mul_rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [`rvdPmQ_commute_A`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-commute-a), [`rvdT_injective`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-injective), [`rvdT_norm_eq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-norm-eq), and 31 more.</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint"></a>
**Lemma 779** (`rvdPmQ_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L363)</small>

`P − Q` is self-adjoint (its polar decomposition `J·T` then has `J` self-adjoint, `T ≥ 0`).

$$
\mathrm{IsSelfAdjoint}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`projK_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk-isselfadjoint), [`projIK_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik-isselfadjoint). $\square$

<small>Used by [`rvdT_norm_eq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-eq-zero"></a>
**Lemma 780** (`rvdPmQ_eq_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L367)</small>

**`D = P − Q` is injective** (kernel-free).  `Dξ = 0 ⟹ Pξ = Qξ ∈ 𝒦 ∩ i𝒦 = {0}` (`IsSeparating`), so `Pξ = Qξ = 0`, whence `Rξ = Pξ + Qξ = 0` and `ξ = 0` (`rvdR_eq_zero`). Injectivity of `D` is what makes the modular conjugation `J` (of `D = J·T`) a full involution `J² = 1` rather than a partial isometry.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)\,\xi = 0 \to \xi = 0
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`rvdR_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-apply), [`rvdR_eq_zero`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-eq-zero). $\square$

<small>Used by [`rvdPmQ_injective`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-injective).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-injective"></a>
**Lemma 781** (`rvdPmQ_injective`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L387)</small>

**`D = P − Q` is injective.**

$$
\mathrm{Injective}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)
$$

*Proof.* By [`rvdPmQ_eq_zero`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-eq-zero). $\square$

<small>Used by [`rvdT_injective`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-injective), [`rvdRC_mul_rvdTwoSubRC_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective).</small>

<a id="d-qiqth-standardsubspacemodular-rvdr-le-two"></a>
**Lemma 782** (`rvdR_le_two`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L393)</small>

**RvD upper bound `R ≤ 2`** (operator form): `2·1 − R` is positive.  With `rvdR_isPositive` (`0 ≤ R`) this is the complete RvD bound `0 ≤ R ≤ 2` at the operator level — `2 − R` is then also positive, so BOTH `R^{1/2}` and `(2 − R)^{1/2}` exist by the continuous functional calculus, the two factors of the polar decomposition `T = R^{1/2}(2 − R)^{1/2}` (RvD Prop 2.2(2)).

$$
(2 \cdot 1 - \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S).\mathrm{IsPositive}
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`rvdR_inner_self_le`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-self-le), [`rvdR_inner_symm`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-inner-symm). $\square$

<small>Used by [`rvdTwoSubRC_isPositive`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-smul-i"></a>
**Lemma 783** (`rvdPmQ_smul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L424)</small>

**`D = P − Q` is conjugate-linear** (anti-ℂ-linear): `D(i·ξ) = −i·(D ξ)`.  In contrast to the ℂ-linear `R = P + Q` (`rvdR_smul_I`), the difference `D` anticommutes with mult-by-`i` — this is exactly the structural reason the modular conjugation `J` of the polar decomposition `J·T = P − Q` is *antiunitary* (conjugate-linear) rather than unitary.  Immediate from the conjugation identities `projK_smul_I`, `projIK_smul_I`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)\,(i \cdot \xi) = -(i \cdot (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)\,\xi)
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`projIK_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik-smul-i), [`projK_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk-smul-i). $\square$

<small>Used by [`rvdPmQ_smul_conj`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-smul-conj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc"></a>
**Definition 784** (`rvdTwoSubRC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L444)</small>

**RvD `2 − R`** as a ℂ-linear operator. With `0 ≤ R` (`rvdRC_nonneg`) and `R ≤ 2` this is the second positive factor `(2 − R)` whose square root pairs with `R^{1/2}` in `T = R^{1/2}(2 − R)^{1/2}`.

$$
(2-R)\,H\,S \;:=\; 2 \cdot 1 - \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S
$$

<small>Used by [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq), [`rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply), [`rvdTwoSubRC_isSymmetric`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric), [`rvdTwoSubRC_isPositive`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive), [`rvdTwoSubRC_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg), [`rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [`rvdSqrtTwoSubR_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-nonneg), [`rvdSqrtTwoSubR_mul_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self), and 33 more.</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc-apply"></a>
**Lemma 785** (`rvdTwoSubRC_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L449)</small>

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,x = 2 \cdot x - (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S)\,x
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik). $\square$

<small>Used by [`rvdTwoSubRC_isSymmetric`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric), [`rvdRC_mul_rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply), [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [`modConj_projIK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projik-modconj), [`modConj_projK_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-projk-modconj), [`rvdPmQ_mul_rvdRC_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs), [`rvdRC_E_two_levelSet`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-e-two-levelset), [`modUnitary_commute_rvdPmQ_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric"></a>
**Lemma 786** (`rvdTwoSubRC_isSymmetric`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L453)</small>

`2 − R` is complex-symmetric (`1` and `Rℂ` both are).

$$
((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)).\mathrm{IsSymmetric}
$$

*Proof.* By [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdRC_isSymmetric`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-issymmetric), [`rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply). $\square$

<small>Used by [`rvdTwoSubRC_isPositive`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive).</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive"></a>
**Lemma 787** (`rvdTwoSubRC_isPositive`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L465)</small>

**`0 ≤ 2 − R`** (the upper RvD bound `R ≤ 2` in operator form).  The pointwise `reApplyInnerSelf` of the ℂ-operator `(2:ℂ)•1 − Rℂ` is *definitionally* that of the ℝ-operator `(2:ℝ)•1 − R` (both are `Re⟪(2 • x − R x), x⟫`, and `(2:ℂ)•x = (2:ℝ)•x`), so positivity transfers directly from the already-proven `rvdR_le_two`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S).\mathrm{IsPositive}
$$

*Proof.* By [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`rvdR_le_two`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr-le-two), [`rvdTwoSubRC_isSymmetric`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-issymmetric). $\square$

<small>Used by [`rvdTwoSubRC_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg), [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc).</small>

<a id="d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg"></a>
**Lemma 788** (`rvdTwoSubRC_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L473)</small>

`0 ≤ 2 − R` in the Loewner order.

$$
0 \le \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S
$$

*Proof.* By [`rvdTwoSubRC_isPositive`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-ispositive). $\square$

<small>Used by [`rvdSqrtTwoSubR_mul_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self), [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrtr"></a>
**Definition 789** (`rvdSqrtR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L477)</small>

**RvD `R^{1/2}`** — the continuous-functional-calculus square root of `R`, now available.

$$
R^{1/2}\,H\,S \;:=\; \mathrm{sqrt}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)
$$

<small>Used by [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`gConstancy_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs), [`oneParticleBW_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-inputs), [`oneParticleBW_of_stripKMSrvd_density`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-stripkmsrvd-density), [`gConstancy_entire`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire), [`gFunction_top_edge_real_all`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all), [`gConstancy_entire_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [`gConstancy_eta_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom), and 32 more.</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrttwosubr"></a>
**Definition 790** (`rvdSqrtTwoSubR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L480)</small>

**RvD `(2 − R)^{1/2}`**.

$$
\sqrt{2-R}\,H\,S \;:=\; \mathrm{sqrt}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)
$$

<small>Used by [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [`modConj_deviceOpC_neg_half`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq), [`rvdSqrtTwoSubR_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-nonneg), [`rvdSqrtTwoSubR_mul_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self), [`rvdSqrtR_commute_rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr), [`rvdT`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt), [`rvdT_sq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-sq), and 12 more.</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrtr-nonneg"></a>
**Lemma 791** (`rvdSqrtR_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L483)</small>

`0 ≤ R^{1/2}`.

$$
0 \le \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc). $\square$

<small>Used by [`rvdT_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-nonneg), [`modConj_rvdSqrtR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrtr-modconj).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrttwosubr-nonneg"></a>
**Lemma 792** (`rvdSqrtTwoSubR_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L486)</small>

`0 ≤ (2 − R)^{1/2}`.

$$
0 \le \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S
$$

*Proof.* By [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc). $\square$

<small>Used by [`rvdT_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-nonneg).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrtr-mul-self"></a>
**Lemma 793** (`rvdSqrtR_mul_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L489)</small>

`R^{1/2} · R^{1/2} = R`.

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S = \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S
$$

*Proof.* By [`rvdRC_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-nonneg). $\square$

<small>Used by [`rvdT_sq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-sq), [`modConjSqrtR_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjsqrtr-sq).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self"></a>
**Lemma 794** (`rvdSqrtTwoSubR_mul_self`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L493)</small>

`(2 − R)^{1/2} · (2 − R)^{1/2} = 2 − R`.

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S = \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S
$$

*Proof.* By [`rvdTwoSubRC_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-nonneg). $\square$

<small>Used by [`rvdT_sq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-sq), [`rvdSqrtTwoSubR_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-injective), [`rvdSqrtR_modConj_of_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdsqrtr-modconj-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc"></a>
**Lemma 795** (`rvdRC_commute_rvdTwoSubRC`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L498)</small>

`R` and `2 − R` commute (the second is `2·1 − R`, an affine function of the first).

$$
\mathrm{Commute}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S)\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`rvdSqrtR_commute_rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr), [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [`rvdRC_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdt), [`rvdRC_mul_rvdTwoSubRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-isselfadjoint), [`rvdRC_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-injective).</small>

<a id="d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr"></a>
**Lemma 796** (`rvdSqrtR_commute_rvdSqrtTwoSubR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L504)</small>

The square roots commute: `√R = cfcₙ √ R` commutes with `2 − R` (a function of `R`), and then with `√(2 − R) = cfcₙ √ (2 − R)`.  Both applications use `Commute.cfcₙ_nnreal` (`CFC.sqrt = cfcₙ NNReal.sqrt`).

$$
\mathrm{Commute}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S)
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdRC_commute_rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-commute-rvdtwosubrc). $\square$

<small>Used by [`rvdT_sq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-sq), [`rvdT_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-nonneg), [`modConj_rvdT_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt-modconj), [`modConj_fixed_of_sqrtR_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt"></a>
**Definition 797** (`rvdT`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L513)</small>

**RvD `T`** — the positive part of the polar decomposition `J·T = P − Q`, `T = R^{1/2}(2 − R)^{1/2}`.

$$
T\,H\,S \;:=\; \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S
$$

<small>Used by [`rvdT_sq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-sq), [`rvdT_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-nonneg), [`rvdT_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-isselfadjoint), [`rvdT_injective`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-injective), [`rvdT_norm_eq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [`rvdPmQ_commute_rvdT_apply`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt-apply), [`rvdT_restrictScalars_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), and 18 more.</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-sq"></a>
**Lemma 798** (`rvdT_sq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L516)</small>

**RvD Prop 2.2(2): `T² = R(2 − R)`.**  Using that `R^{1/2}` and `(2 − R)^{1/2}` commute, the product `T² = R^{1/2}(2−R)^{1/2}R^{1/2}(2−R)^{1/2}` regroups into `(R^{1/2})²((2−R)^{1/2})² = R(2−R)`. With `J² = 1` and `JT = P − Q`, this is `(P − Q)² = R(2 − R)` — the modular-operator factorization.

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{T}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{T}\,S = \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S
$$

*Proof.* By [`rvdSqrtR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr), [`rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [`rvdSqrtR_mul_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr-mul-self), [`rvdSqrtTwoSubR_mul_self`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-mul-self), [`rvdSqrtR_commute_rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr). $\square$

<small>Used by [`rvdT_injective`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-injective), [`rvdT_norm_eq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-nonneg"></a>
**Lemma 799** (`rvdT_nonneg`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L533)</small>

`T = R^{1/2}(2−R)^{1/2}` is **positive** — a product of two commuting positive operators.

$$
0 \le \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{T}\,S
$$

*Proof.* By [`rvdSqrtR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr), [`rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [`rvdSqrtR_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr-nonneg), [`rvdSqrtTwoSubR_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr-nonneg), [`rvdSqrtR_commute_rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr-commute-rvdsqrttwosubr). $\square$

<small>Used by [`rvdT_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-isselfadjoint), [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-isselfadjoint"></a>
**Lemma 800** (`rvdT_isSelfAdjoint`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L538)</small>

`T` is self-adjoint (it is positive).

$$
\mathrm{IsSelfAdjoint}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{T}\,S)
$$

*Proof.* By [`rvdT_nonneg`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-nonneg). $\square$

<small>Used by [`rvdT_norm_eq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [`rvdT_restrictScalars_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [`rvdT_real_inner_symm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-real-inner-symm).</small>

<a id="d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply"></a>
**Lemma 801** (`rvdRC_mul_rvdTwoSubRC_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L551)</small>

**`T² = D²` as maps**: `(R(2−R)) ξ = (P − Q)((P − Q) ξ)`.  Both sides reduce to `P ξ + Q ξ − P(Q ξ) − Q(P ξ)` by idempotency of `P, Q` (`R² = R + (PQ+QP)`, so `R(2−R) = 2R − R² = R − (PQ+QP) = (P−Q)²`).  This is what transfers `‖T ξ‖ = ‖D ξ‖` (the modular conjugation is an isometry from `T` to `D`).

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,\xi = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)\,\xi)
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr), [`projK_idem`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk-idem), [`projIK_idem`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik-idem), [`rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc-apply). $\square$

<small>Used by [`rvdPmQ_commute_A`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-commute-a), [`rvdT_injective`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-injective), [`rvdT_norm_eq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-norm-eq), [`rvdRC_mul_rvdTwoSubRC_injective`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-injective).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-commute-a"></a>
**Lemma 802** (`rvdPmQ_commute_A`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L567)</small>

**`D` commutes with `A = R(2−R) = T²`** (the inductive base for `D·T = T·D`).  Trivial because `A = D²` as maps (`rvdRC_mul_rvdTwoSubRC_apply`): `D·D² = D³ = D²·D`.  The full `D·√A = √A·D` (the antilinear modular-conjugation commutation, whence `J² = 1`) follows from this base by the closed-commutant argument — `{Y | D∘Y = Y∘D}` is a closed real *-subalgebra ⊇ `elemental ℝ A ∋ √A`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,\xi) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{R}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc}{(2-R)}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)\,\xi)
$$

*Proof.* By [`rvdRC_mul_rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply). $\square$

<small>Used by [`rvdPmQ_commute_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-commute-rvdt), [`modUnitary_commute_rvdPmQ_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary-commute-rvdpmq-rs).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-injective"></a>
**Lemma 803** (`rvdT_injective`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L575)</small>

**`T = R^{1/2}(2−R)^{1/2}` is injective.**  `T² = R(2−R) = D²` (`rvdT_sq`, `rvdRC_mul_rvdTwoSubRC_apply`) is injective because `D = P−Q` is (`rvdPmQ_injective`), and `T` injective follows.  `T` injective ⟹ `range T` dense (`(range T)‾ = (ker T)ᗮ = H`), which is what makes the modular conjugation `J : T ξ ↦ D ξ` extend to all of `H`.

$$
\mathrm{Injective}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{T}\,S)
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdPmQ`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq), [`rvdPmQ_injective`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-injective), [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdT_sq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-sq), [`rvdRC_mul_rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply). $\square$

<small>Used by [`rvdT_restrictScalars_denseRange`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdt-restrictscalars-denserange), [`modConj_fixed_of_sqrtR_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-rvdt-norm-eq"></a>
**Lemma 804** (`rvdT_norm_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L607)</small>

**The modular-conjugation isometry: `‖T ξ‖ = ‖D ξ‖`** (RvD polar decomposition `D = J·T`). `D = P − Q` is conjugate-linear and `T = R^{1/2}(2−R)^{1/2}` is its positive modulus `|D|`; the map `J : T ξ ↦ D ξ` is therefore a well-defined antiunitary (the modular conjugation).  Proved from `T² = D²` (`rvdRC_mul_rvdTwoSubRC_apply` via `rvdT_sq`) and self-adjointness of both `T` and `D`.

$$
\|(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt}{T}\,S)\,\xi\| = \|(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)\,\xi\|
$$

*Proof.* By [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdPmQ_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-isselfadjoint), [`rvdTwoSubRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdtwosubrc), [`rvdT_sq`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-sq), [`rvdT_isSelfAdjoint`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdt-isselfadjoint), [`rvdRC_mul_rvdTwoSubRC_apply`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc-mul-rvdtwosubrc-apply). $\square$

<small>Used by [`modConj_rvdT`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdt), [`modConj_norm`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-norm).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr"></a>
**Lemma 805** (`rvdPmQ_mul_rvdR`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L627)</small>

**RvD intertwiner `D·R = (2−R)·D`.**

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S = (2 \cdot 1 - \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S) \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`projIK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik), [`projK_idem`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk-idem), [`projIK_idem`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik-idem). $\square$

<small>Used by [`rvdPmQ_anticommute_rvdR_sub_one`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-anticommute-rvdr-sub-one), [`rvdPmQ_mul_rvdRC_rs`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdrc-rs).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-anticommute-rvdr-sub-one"></a>
**Lemma 806** (`rvdPmQ_anticommute_rvdR_sub_one`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L645)</small>

**`D` ANTICOMMUTES with `R − 1`:** `D·(R−1) = −(R−1)·D`.  Because `D·R = (2−R)·D` (`rvdPmQ_mul_rvdR`), so `D·(R−1) = (2−R)·D − D = (1−R)·D = −(R−1)·D`.  This is the engine for the modular **covariance** `[U_t, D] = 0`: `D` antilinear + `D·(R−1)=−(R−1)·D` makes `D` COMMUTE with `i·(R−1)`, and `U_t = u_t(R)` is (a Borel function) of `i·(R−1)` with `conj(u_t(2−r)) = u_t(r)`.

$$
\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S \cdot (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S - 1) = -((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdr}{R}\,S - 1) \cdot \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)
$$

*Proof.* By [`rvdPmQ_mul_rvdR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-mul-rvdr). $\square$

<small>Used by [`rvdPmQ_rvdRC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdpmq-rvdrc).</small>

<a id="d-qiqth-standardsubspacemodular-rvdpmq-smul-conj"></a>
**Lemma 807** (`rvdPmQ_smul_conj`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StandardSubspaceModular.lean#L671)</small>

**`D` is conjugate-(ℂ-)linear:** `D(c•ξ) = conj(c)·Dξ` for every `c : ℂ`.  From ℝ-linearity plus the `i`-case `rvdPmQ_smul_I` (`D(i•ξ)=−i•Dξ`), expanding `c = c.re + c.im·i`.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)\,(c \cdot \xi) = (\mathrm{starRingEnd}\,\mathbb{C})\,c \cdot (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq}{(P-Q)}\,S)\,\xi
$$

*Proof.* By [`rvdPmQ_smul_I`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdpmq-smul-i). $\square$

<small>Used by [`cfcΩ_intertwine`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfc-intertwine).</small>

---
<small>[← all sections](/browser) · [← SpectralTheorem](/browser/qiqth-spectral-spectraltheorem) · [StandardSubspaceModularFlow →](/browser/qiqth-standardsubspacemodularflow) </small>