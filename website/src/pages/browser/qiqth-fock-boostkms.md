---
layout: ../../layouts/Deep.astro
title: QIQTH.Fock.BoostKMS
eyebrow: Fock · section of the QIQT-H book
description: QIQTH.Fock.BoostKMS — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← EinsteinFieldEquation](/browser/qiqth-einsteinfieldequation) · [CyclicWitness →](/browser/qiqth-fock-cyclicwitness) </small>

<small>Fock · entries 94–208 of 1000</small>

<a id="d-qiqth-fock-boostkms-inner-krepl2"></a>
**Lemma 94** (`inner_KrepL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L22)</small>

**The `L²` inner product of two wedge modes as a concrete rapidity integral.** `⟪KrepL2 f, KrepL2 g⟫ = ∫ conj(Krep m f θ)·Krep m g θ dθ` (via `L2.inner_def` + `MemLp.coeFn_toLp`).

$$
\langle {\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf}},{\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,\mathrm{hg}}\rangle = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta) \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`inner_boostUnitary_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [`norm_toLp_Krep_eq_sqrt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-tolp-krep-eq-sqrt).</small>

<a id="d-qiqth-fock-boostkms-inner-krepl2-general"></a>
**Lemma 95** (`inner_KrepL2_general`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L33)</small>

**The `L²` inner product of a wedge mode against an ARBITRARY `h ∈ L²` as a concrete integral**: `⟪KrepL2 f, h⟫ = ∫ conj(Krep m f θ)·h(θ) dθ`.  The concrete form of the Reeh–Schlieder *totality* condition: `{KrepL2 f : f nice}` is total iff the only `h` with `∫ conj(Krep f)·h = 0` for all nice `f` is `h = 0`.

$$
\langle {\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf}},{h}\rangle = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta) \cdot h\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`niceWedge_isCyclic_of_total_integral`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral), [`niceWedgeCyclic_of_fourier_ne_zero`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-boostkms-inner-boostunitary-krepl2"></a>
**Lemma 96** (`inner_boostUnitary_KrepL2`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L44)</small>

**The real-axis edge.** `⟪KrepL2 g, boostUnitary a (KrepL2 f)⟫ = ∫ conj(Krep m g θ)·Krep m f (θ−a) dθ`. Combines `boostUnitary_KrepL2` (boost acts by `boostTest`), `inner_KrepL2`, and the amplitude boost- covariance `Krep m (boostTest (−a) f) θ = Krep m f (θ−a)`. This is the orbit correlation `f(t) = ⟪η, V_t ξ⟫` of `StripKMSrvd` (with `V_t = boostUnitary a`, `a` the rapidity).

$$
\mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,(-a)\,f))\,2\,\mathrm{volume} \to \langle {\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,\mathrm{hg}},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,(\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf})}\rangle = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta) \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - a)
$$

*Proof.* By [`inner_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-krepl2), [`Krep_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-boost), [`boostUnitary_KrepL2`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-krepl2). $\square$

<small>Used by [`symm_edge_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-symm-edge-eq-inner).</small>

<a id="d-qiqth-fock-boostkms-symm-edge-eq-shifted"></a>
**Lemma 97** (`symm_edge_eq_shifted`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L58)</small>

**Symmetric ↔ shifted edge (change of variables `θ ↦ θ+πt`).** The KMS function's symmetric real-axis form equals the boost-orbit form: `∫ conj(Krep g (θ+πt))·Krep f (θ−πt) dθ = ∫ conj(Krep g θ)·Krep f (θ−2πt) dθ` (translation invariance).

$$
\int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,(\theta + \pi \cdot t)) \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - \pi \cdot t) = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta) \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - 2 \cdot \pi \cdot t)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`symm_edge_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-symm-edge-eq-inner).</small>

<a id="d-qiqth-fock-boostkms-symm-edge-eq-inner"></a>
**Lemma 98** (`symm_edge_eq_inner`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L70)</small>

**The KMS top edge `f(t) = ⟪η, V_t ξ⟫` in symmetric (KMS-function) form.** Combining `symm_edge_eq_shifted` and `inner_boostUnitary_KrepL2`: the symmetric integral `∫ conj(Krep g (θ+πt))·Krep f (θ−πt) dθ` — the `t`-real value of the KMS function `F(z)=∫ conj(KrepCont g (θ+πz̄))·KrepCont f (θ−πz)` — equals `⟪KrepL2 g, boostUnitary(2πt) (KrepL2 f)⟫`. (Boost sign `+2π` here; `StripKMSrvd`'s `V_t=boostUnitary(−2π·)` is matched by orienting `t`.)

$$
\mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,(-(2 \cdot \pi \cdot t))\,f))\,2\,\mathrm{volume} \to \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,(\theta + \pi \cdot t)) \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - \pi \cdot t) = \langle {\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,\mathrm{hg}},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,(\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf})}\rangle
$$

*Proof.* By [`inner_boostUnitary_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-boostunitary-krepl2), [`symm_edge_eq_shifted`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-symm-edge-eq-shifted). $\square$

<small>Used by [`kmsFun_ofReal_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner).</small>

<a id="d-qiqth-fock-boostkms-kmsfun"></a>
**Definition 99** (`kmsFun`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L82)</small>

**The KMS function** `F(z) = ∫ conj(KrepCont g (conj(θ+πz)))·KrepCont f (θ−πz) dθ` — the candidate `StripKMSrvd` witness. `H^#(θ+πz) = conj(H(conj(θ+πz)))` with `H = KrepCont g`, `Ξ = KrepCont f`; for `z` in the strip `{−1<Im z<0}` both factors are evaluated with imaginary part in `(0,π)` (the good damping region).

$$
\mathrm{kmsFun}\,m\,f\,g\,z \;:=\; \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z)
$$

<small>Used by [`kmsFun_ofReal`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal), [`kmsFun_ofReal_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [`kmsFun_sub_I`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-i), [`kmsFun_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableat), [`kmsFun_differentiableOn`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableon), [`kmsFunCut_tendsto_closed`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed), [`norm_kmsFun_sub_kmsFunCut_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le), [`kmsFun_add_left`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-add-left), and 12 more.</small>

<a id="d-qiqth-fock-boostkms-kmsfun-ofreal"></a>
**Lemma 100** (`kmsFun_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L90)</small>

**The KMS function on the real axis** equals the symmetric integral (via `KrepCont_ofReal`): the real-axis arguments are real, so each `KrepCont` collapses to `Krep` and the inner conjugation is trivial.

$$
\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,t = \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,(\theta + \pi \cdot t)) \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - \pi \cdot t)
$$

*Proof.* By [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`KrepCont_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal). $\square$

<small>Used by [`kmsFun_ofReal_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [`kmsFun_sub_I`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-i).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner"></a>
**Lemma 101** (`kmsFun_ofReal_eq_inner`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L101)</small>

**The KMS top edge for `kmsFun`**: `F(t) = ⟪KrepL2 g, boostUnitary(2πt) (KrepL2 f)⟫` (`kmsFun_ofReal` ∘ `symm_edge_eq_inner`).

$$
\mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,(-(2 \cdot \pi \cdot t))\,f))\,2\,\mathrm{volume} \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,t = \langle {\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,\mathrm{hg}},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,(\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf})}\rangle
$$

*Proof.* By [`symm_edge_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-symm-edge-eq-inner), [`kmsFun_ofReal`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal). $\square$

<small>Used by [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-sub-i"></a>
**Lemma 102** (`kmsFun_sub_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L110)</small>

**The KMS bottom edge `F(t−i) = conj(F(t))`** (for real `f,g`). At `z=t−i` the `iπ`-shift puts both `KrepCont` arguments at imaginary part `+π`, so `KrepCont_add_pi_I` (A3) collapses each to `conj(Krep …)`: `F(t−i) = ∫ Krep g(θ+πt)·conj(Krep f(θ−πt)) dθ = conj(F(t))`. With the top edge (`kmsFun_ofReal_eq_inner`) and `⟪V_t ξ,η⟫ = conj⟪η,V_t ξ⟫`, this is the bottom-edge requirement `f(t−i) = ⟪V_t ξ,η⟫` of `StripKMSrvd`.

$$
(\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \forall (t : \mathbb{R}), \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,(t - i) = (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,t)
$$

*Proof.* By [`kmsFun_ofReal`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal), [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep), [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`KrepCont_add_pi_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i). $\square$

<small>Used by [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot).</small>

<a id="d-qiqth-fock-boostkms-differentiable-reflkrepcont"></a>
**Lemma 103** (`differentiable_reflKrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L133)</small>

**The reflected amplitude `u ↦ conj(KrepCont g(conj u))` is entire** (Schwarz reflection: `conj∘F∘conj` is holomorphic when `F` is). Via `DifferentiableAt.star_conj` + `differentiable_KrepCont`. This is the `g` factor `H^#` of the KMS-function integrand — the holomorphy ingredient for `kmsFun`.

$$
\mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \mathrm{Differentiable}\,\mathbb{C}\,\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u))
$$

*Proof.* By [`differentiable_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Used by [`differentiable_kmsIntegrand`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-differentiable-kmsintegrand), [`hasDerivAt_kmsIntegrand_z`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z), [`continuous_deriv_reflKrepCont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-deriv-reflkrepcont).</small>

<a id="d-qiqth-fock-boostkms-norm-reflkrepcont-le"></a>
**Lemma 104** (`norm_reflKrepCont_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L145)</small>

**Strip-decay of the reflected amplitude** `‖reflKrep(u)‖ = ‖KrepCont g(conj u)‖` for `−π ≤ Im u ≤ 0` (so `Im(conj u) ∈ [0,π]`): `≤ (1/√2)(∫‖g‖)·exp(−(m sin(−Im u)δ)·cosh(Re u))`. The `g`-factor bound for the `kmsFun` integrand (`reflKrep(θ+πz)`, where `Im(θ+πz)=π Im z ∈(−π,0)` for `z` in the strip).

$$
0 \le m \to \forall \{g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{u : \mathbb{C}\}, -\pi \le u.\mathrm{im} \to u.\mathrm{im} \le 0 \to \|(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u))\| \le (1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|g\,x\|) \cdot \exp\,(-(m \cdot \sin\,(-u.\mathrm{im}) \cdot \delta) \cdot \cosh\,u.\mathrm{re})
$$

*Proof.* By [`norm_KrepCont_le_exp_decay_gen`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen). $\square$

<small>Used by [`integrable_kmsIntegrand`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-integrable-kmsintegrand), [`norm_term2_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-term2-le).</small>

<a id="d-qiqth-fock-boostkms-deriv-reflkrepcont-eq"></a>
**Lemma 105** (`deriv_reflKrepCont_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L159)</small>

The derivative of the reflected amplitude: `deriv(u ↦ conj(KrepCont g(conj u))) u = conj(deriv(KrepCont g)(conj u))` (Schwarz reflection, `HasDerivAt.conj_conj`).

$$
\mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall (u : \mathbb{C}), \mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,u = (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{deriv}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g)\,((\mathrm{starRingEnd}\,\mathbb{C})\,u))
$$

*Proof.* By [`differentiable_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Used by [`norm_deriv_reflKrepCont_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-deriv-reflkrepcont-le).</small>

<a id="d-qiqth-fock-boostkms-norm-deriv-reflkrepcont-le"></a>
**Lemma 106** (`norm_deriv_reflKrepCont_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L171)</small>

**Strip-decay of the reflected amplitude's derivative**: `‖deriv reflKrep(u)‖ = ‖deriv KrepCont g(conj u)‖ ≤ (1/√2)·|m|·cosh(Re u)·exp(−(m sin(−Im u)δ)·cosh(Re u))·∫(|x₀|+|x₁|)‖g‖` for `−π≤Im u≤0`. The `deriv reflKrep` factor bound for the `kmsFun` integrand's `z`-derivative.

$$
0 \le m \to \forall \{g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{u : \mathbb{C}\}, -\pi \le u.\mathrm{im} \to u.\mathrm{im} \le 0 \to \|\mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,u\| \le 1 / \sqrt 2 \cdot (|m| \cdot \cosh\,u.\mathrm{re} \cdot \exp\,(-(m \cdot \sin\,(-u.\mathrm{im}) \cdot \delta) \cdot \cosh\,u.\mathrm{re}) \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|g\,x\|)
$$

*Proof.* By [`deriv_reflKrepCont_eq`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-deriv-reflkrepcont-eq), [`norm_deriv_KrepCont_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay). $\square$

<small>Used by [`norm_term1_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-term1-le).</small>

<a id="d-qiqth-fock-boostkms-differentiable-kmsintegrand"></a>
**Lemma 107** (`differentiable_kmsIntegrand`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L186)</small>

**The `kmsFun` integrand is entire in `z`** (for `f,g` continuous with compact support). The `g`-factor `conj(KrepCont g(conj(θ+πz)))` = `differentiable_reflKrepCont ∘ (affine)`, the `f`-factor `KrepCont f(θ−πz)` = `differentiable_KrepCont ∘ (affine)`; the product is differentiable. This is the per-`θ` (`h_diff`) ingredient for the parametric-integral holomorphy of `F` (`DiffContOnCl`).

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall (\theta : \mathbb{R}), \mathrm{Differentiable}\,\mathbb{C}\,\lambda z \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z)
$$

*Proof.* By [`differentiable_reflKrepCont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-differentiable-reflkrepcont), [`differentiable_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Used by [`kmsFunCut_continuousOn`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-continuouson).</small>

<a id="d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z"></a>
**Lemma 108** (`hasDerivAt_kmsIntegrand_z`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L198)</small>

**The `kmsFun` integrand's `z`-derivative** (product/chain rule): for fixed `θ`, the integrand `conj(KrepCont g(conj(θ+πz)))·KrepCont f(θ−πz)` has derivative `[deriv reflKrep(θ+πz)·π]·KrepCont f(θ−πz) + reflKrep(θ+πz)·[deriv KrepCont f(θ−πz)·(−π)]`. The `h_diff` ingredient (with explicit value, for the domination bound) of the dominated-derivative theorem for `kmsFun`'s holomorphy.

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall (\theta : \mathbb{R}) (z : \mathbb{C}), ({\lambda z \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z)})'({z})={\mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,(\theta + \pi \cdot z) \cdot \pi \cdot \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z) + (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot (\mathrm{deriv}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f)\,(\theta - \pi \cdot z) \cdot -\pi)}
$$

*Proof.* By [`differentiable_reflKrepCont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-differentiable-reflkrepcont), [`differentiable_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Used by [`kmsFun_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableat), [`kmsFunCut_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-boostkms-norm-two-term-le"></a>
**Lemma 109** (`norm_two_term_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L219)</small>

Norm decomposition of the integrand `z`-derivative value (from `hasDerivAt_kmsIntegrand_z`) into its four factors: `‖A·π·C + B·(D·(−π))‖ ≤ π·‖A‖·‖C‖ + π·‖B‖·‖D‖`.

$$
\|A \cdot \pi \cdot C + B \cdot (D \cdot -\pi)\| \le \pi \cdot (\|A\| \cdot \|C\|) + \pi \cdot (\|B\| \cdot \|D\|)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`kmsIntegrand_deriv_bound`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound).</small>

<a id="d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta"></a>
**Lemma 110** (`continuous_kmsIntegrand_in_theta`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L228)</small>

**The `kmsFun` integrand is continuous in `θ`** (for fixed `z`) — the measurability (`hF_meas`) ingredient for the parametric-integral holomorphy of `F`. `KrepCont` is continuous (entire), composed with the continuous `θ`-maps `θ↦conj(θ+πz)`, `θ↦θ−πz`, and `conj`.

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall (z : \mathbb{C}), \mathrm{Continuous}\,\lambda \theta \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z)
$$

*Proof.* By [`differentiable_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Used by [`integrable_kmsIntegrand`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-integrable-kmsintegrand), [`kmsFun_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableat), [`kmsFunCut_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableat), [`kmsFunCut_continuousOn`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-continuouson).</small>

<a id="d-qiqth-fock-boostkms-continuous-deriv-reflkrepcont"></a>
**Lemma 111** (`continuous_deriv_reflKrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L240)</small>

`deriv reflKrep` is continuous (`reflKrep` entire ⟹ deriv analytic ⟹ continuous).

$$
\mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \mathrm{Continuous}\,(\mathrm{deriv}\,\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))
$$

*Proof.* By [`differentiable_reflKrepCont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-differentiable-reflkrepcont). $\square$

<small>Used by [`continuous_kmsIntegrand_deriv_in_theta`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta).</small>

<a id="d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta"></a>
**Lemma 112** (`continuous_kmsIntegrand_deriv_in_theta`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L247)</small>

**The `kmsFun` integrand's `z`-derivative value is continuous in `θ`** — the `hF'_meas` (derivative measurability) ingredient. Each of the four factors is continuous in `θ`.

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall (z : \mathbb{C}), \mathrm{Continuous}\,\lambda \theta \mapsto \mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,(\theta + \pi \cdot z) \cdot \pi \cdot \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z) + (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot (\mathrm{deriv}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f)\,(\theta - \pi \cdot z) \cdot -\pi)
$$

*Proof.* By [`continuous_deriv_reflKrepCont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-deriv-reflkrepcont), [`differentiable_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont), [`continuous_deriv_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-continuous-deriv-krepcont). $\square$

<small>Used by [`kmsFun_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableat), [`kmsFunCut_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-boostkms-integrable-kmsintegrand"></a>
**Lemma 113** (`integrable_kmsIntegrand`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L262)</small>

**`hF_int` — the `kmsFun` integrand is integrable in `θ`** at an interior strip point `z` (`−1<Im z<0`). `‖integrand‖ = ‖reflKrep(θ+πz)‖·‖KrepCont f(θ−πz)‖ ≤ C_g·(C_f·exp(−(mσδf)·cosh(θ−π Re z)))` (the `g`-factor bounded, the `f`-factor decaying, `σ=sin(−π Im z)>0`), dominated by an integrable translate of `exp(−c·cosh)`.

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\deltaf \deltag : \mathbb{R}\}, 0 < \deltaf \to 0 < \deltag \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \deltaf \le x\,1 - x\,0 \wedge \deltaf \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \deltag \le x\,1 - x\,0 \wedge \deltag \le x\,1 + x\,0) \to \forall \{z : \mathbb{C}\}, -1 < z.\mathrm{im} \to z.\mathrm{im} < 0 \to \mathrm{Integrable}\,(\lambda \theta \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z))\,\mathrm{volume}
$$

*Proof.* By [`norm_reflKrepCont_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-reflkrepcont-le), [`continuous_kmsIntegrand_in_theta`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [`integrable_exp_neg_const_mul_cosh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-integrable-exp-neg-const-mul-cosh), [`sin_neg_pi_mul_pos`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-sin-neg-pi-mul-pos), [`norm_KrepCont_le_exp_decay_gen`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen). $\square$

<small>Used by [`kmsFun_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableat), [`kmsFunCut_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-boostkms-exists-sin-min"></a>
**Lemma 114** (`exists_sin_min`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L366)</small>

**Decay-rate lower bound over a strip-interior ball.** If `closedBall z₀ ε ⊆ {−1<Im<0}`, the decay rate `σ(z)=sin(−π·Im z)` has a positive lower bound `σmin` on the ball (continuous positive fn on a compact set attains a positive min). The `c₀` for `cosh_shift_exp_le` in the `h_bound` assembly.

$$
0 < \varepsilon \to (\forall z\in \bar{B}\,z_{0}\,\varepsilon, -1 < z.\mathrm{im} \wedge z.\mathrm{im} < 0) \to \exists \sigma\mathrm{min}, 0 < \sigma\mathrm{min} \wedge \forall z\in \bar{B}\,z_{0}\,\varepsilon, \sigma\mathrm{min} \le \sin\,(-(\pi \cdot z.\mathrm{im}))
$$

*Proof.* By [`sin_neg_pi_mul_pos`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-sin-neg-pi-mul-pos). $\square$

<small>Used by [`kmsFun_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableat), [`kmsFunCut_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-boostkms-norm-term1-le"></a>
**Lemma 115** (`norm_term1_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L380)</small>

**`h_bound` term 1**: `‖deriv reflKrep(θ+πz)‖·‖KrepCont f(θ−πz)‖ ≤ Cdg·Cf·(e^{πR}·cosh θ·exp(−κ·cosh θ))` (`κ = m σmin δ e^{−πR}`), via `prod_norm_bound_cosh_shift` (the `deriv reflKrep` factor decays in `cosh(θ+π Re z)`, the `KrepCont f` factor is bounded by `Cf`).

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{z : \mathbb{C}\}, -1 < z.\mathrm{im} \to z.\mathrm{im} < 0 \to \forall \{\sigma\mathrm{min} R : \mathbb{R}\}, 0 < \sigma\mathrm{min} \to \sigma\mathrm{min} \le \sin\,(-(\pi \cdot z.\mathrm{im})) \to |z.\mathrm{re}| \le R \to \forall (\theta : \mathbb{R}), \|\mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,(\theta + \pi \cdot z)\| \cdot \|\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z)\| \le 1 / \sqrt 2 \cdot (|m| \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|g\,x\|) \cdot (1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|f\,x\|) \cdot (\exp\,(\pi \cdot R) \cdot \cosh\,\theta \cdot \exp\,(-(m \cdot \sigma\mathrm{min} \cdot \delta \cdot \exp\,(-(\pi \cdot R)) \cdot \cosh\,\theta)))
$$

*Proof.* By [`norm_deriv_reflKrepCont_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-deriv-reflkrepcont-le), [`sin_neg_pi_mul_pos`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-sin-neg-pi-mul-pos), [`prod_norm_bound_cosh_shift`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-prod-norm-bound-cosh-shift), [`norm_KrepCont_le_exp_decay_gen`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen). $\square$

<small>Used by [`kmsIntegrand_deriv_bound`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound).</small>

<a id="d-qiqth-fock-boostkms-norm-term2-le"></a>
**Lemma 116** (`norm_term2_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L420)</small>

**`h_bound` term 2**: `‖reflKrep(θ+πz)‖·‖deriv KrepCont f(θ−πz)‖ ≤ Cdf·Cg·(e^{πR}·cosh θ·exp(−κ·cosh θ))` (mirror of term 1, with the `deriv` on the `f`-factor: `deriv KrepCont f` decaying in `cosh(θ−π Re z)`, `reflKrep` bounded by `Cg`).

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{z : \mathbb{C}\}, -1 < z.\mathrm{im} \to z.\mathrm{im} < 0 \to \forall \{\sigma\mathrm{min} R : \mathbb{R}\}, 0 < \sigma\mathrm{min} \to \sigma\mathrm{min} \le \sin\,(-(\pi \cdot z.\mathrm{im})) \to |z.\mathrm{re}| \le R \to \forall (\theta : \mathbb{R}), \|(\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z)))\| \cdot \|\mathrm{deriv}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f)\,(\theta - \pi \cdot z)\| \le 1 / \sqrt 2 \cdot (|m| \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|f\,x\|) \cdot (1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|g\,x\|) \cdot (\exp\,(\pi \cdot R) \cdot \cosh\,\theta \cdot \exp\,(-(m \cdot \sigma\mathrm{min} \cdot \delta \cdot \exp\,(-(\pi \cdot R)) \cdot \cosh\,\theta)))
$$

*Proof.* By [`norm_reflKrepCont_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-reflkrepcont-le), [`sin_neg_pi_mul_pos`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-sin-neg-pi-mul-pos), [`prod_norm_bound_cosh_shift`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-prod-norm-bound-cosh-shift), [`norm_deriv_KrepCont_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay). $\square$

<small>Used by [`kmsIntegrand_deriv_bound`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound).</small>

<a id="d-qiqth-fock-boostkms-kmsintegrand-deriv-bound"></a>
**Lemma 117** (`kmsIntegrand_deriv_bound`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L462)</small>

**The `h_bound` pointwise content**: `‖F'(z,θ)‖ ≤ π·(Cdg·Cf + Cdf·Cg)·(e^{πR}·cosh θ·exp(−κ·cosh θ))`, `κ = m σmin δ e^{−πR}` — a `z`-independent (for the ball) integrable-in-`θ` bound on the integrand `z`-derivative. Combines `norm_two_term_le` + `norm_term1_le` + `norm_term2_le`.

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{z : \mathbb{C}\}, -1 < z.\mathrm{im} \to z.\mathrm{im} < 0 \to \forall \{\sigma\mathrm{min} R : \mathbb{R}\}, 0 < \sigma\mathrm{min} \to \sigma\mathrm{min} \le \sin\,(-(\pi \cdot z.\mathrm{im})) \to |z.\mathrm{re}| \le R \to \forall (\theta : \mathbb{R}), \|\mathrm{deriv}\,(\lambda u \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,u)))\,(\theta + \pi \cdot z) \cdot \pi \cdot \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z) + (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot (\mathrm{deriv}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f)\,(\theta - \pi \cdot z) \cdot -\pi)\| \le \pi \cdot ((1 / \sqrt 2 \cdot (|m| \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|g\,x\|) \cdot (1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|f\,x\|) + 1 / \sqrt 2 \cdot (|m| \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|f\,x\|) \cdot (1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|g\,x\|)) \cdot (\exp\,(\pi \cdot R) \cdot \cosh\,\theta \cdot \exp\,(-(m \cdot \sigma\mathrm{min} \cdot \delta \cdot \exp\,(-(\pi \cdot R)) \cdot \cosh\,\theta))))
$$

*Proof.* By [`norm_two_term_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-two-term-le), [`norm_term1_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-term1-le), [`norm_term2_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-term2-le). $\square$

<small>Used by [`kmsFun_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableat), [`kmsFunCut_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-differentiableat"></a>
**Lemma 118** (`kmsFun_differentiableAt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L485)</small>

** `kmsFun m f g` is differentiable at every interior strip point** (`−1<Im z₀<0`), for `f,g` continuous with compact support strictly inside the wedge (uniform margin `δ>0`). The holomorphy half of `DiffContOnCl`. Assembles the six dominated-derivative hypotheses (`hF_meas`, `hF_int`, `hF'_meas`, `h_diff`, `h_bound`, `bound_integrable` — all proven) over a strip-interior ball (with `σ_min` from `exists_sin_min`, `R` from the ball).

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{z_{0} : \mathbb{C}\}, -1 < z_{0}.\mathrm{im} \to z_{0}.\mathrm{im} < 0 \to \mathrm{DifferentiableAt}\,\mathbb{C}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g)\,z_{0}
$$

*Proof.* By [`hasDerivAt_kmsIntegrand_z`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z), [`continuous_kmsIntegrand_in_theta`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [`continuous_kmsIntegrand_deriv_in_theta`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta), [`integrable_kmsIntegrand`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-integrable-kmsintegrand), [`exists_sin_min`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-exists-sin-min), [`kmsIntegrand_deriv_bound`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound), [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`integrable_cosh_mul_exp_neg_const_mul_cosh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-integrable-cosh-mul-exp-neg-const-mul-cosh). $\square$

<small>Used by [`kmsFun_differentiableOn`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableon).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-differentiableon"></a>
**Lemma 119** (`kmsFun_differentiableOn`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L559)</small>

**`kmsFun m f g` is holomorphic on the whole open strip** `{−1<Im z<0}` — the `DifferentiableOn` half of `DiffContOnCl`, an immediate corollary of `kmsFun_differentiableAt` (the strip is open, so `DifferentiableAt` at each point gives `DifferentiableWithinAt`).

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \mathrm{DifferentiableOn}\,\mathbb{C}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g)\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0)
$$

*Proof.* By [`kmsFun_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableat). $\square$

<small>Used by [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut"></a>
**Definition 120** (`kmsFunCut`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L664)</small>

**θ-truncated KMS function** (cutoff `R`): the same integrand as `kmsFun`, but integrated over the compact rapidity window `θ ∈ [−R,R]`. The truncation device (GPT-5.5): the compact θ-domain makes `kmsFunCut R` holomorphic on the open strip, continuous on the closed strip, and trivially BOUNDED there — with **no** logarithmic blow-up — so Hadamard three-lines bounds it by the edge constant `B` for every `R`, and `R→∞` (dominated convergence) transfers the bound to `kmsFun`.

$$
\mathrm{kms}\,m\,f\,g\,R\,z \;:=\; \int (\theta : \mathbb{R}) in \mathrm{Icc}\,(-R)\,R, (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z)
$$

<small>Used by [`norm_kmsFunCut_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-le), [`kmsFunCut_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableat), [`kmsFunCut_differentiableOn`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableon), [`kmsFunCut_continuousOn`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-continuouson), [`kmsFunCut_ofReal`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-ofreal), [`kmsFunCut_sub_I`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-sub-i), [`norm_kmsFunCut_diff_ofReal_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le), [`norm_kmsFunCut_diff_sub_I_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le), and 5 more.</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfuncut-le"></a>
**Lemma 121** (`norm_kmsFunCut_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L673)</small>

**Trivial closed-strip bound for `kmsFunCut`** (`Im z ∈ [−1,0]`, `R ≥ 0`): `‖kmsFunCut R z‖ ≤ C_g·C_f·2R` with `C_h = (1/√2)∫‖h‖`. Each `KrepCont` factor has argument imaginary part `−π·Im z ∈ [0,π]`, so the plain bound `norm_KrepCont_le_const` applies; integrate the constant `C_g·C_f` over `[−R,R]` (measure `2R`). This is the `BddAbove` Hadamard needs — finite for each `R`, the log-blowup absent.

$$
0 \le m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 \le \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{R : \mathbb{R}\}, 0 \le R \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,z\| \le (1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|g\,x\|) \cdot (1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|f\,x\|) \cdot (2 \cdot R)
$$

*Proof.* By [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`norm_KrepCont_le_const`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-const). $\square$

<small>Used by [`norm_kmsFunCut_diff_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-differentiableat"></a>
**Lemma 122** (`kmsFunCut_differentiableAt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L711)</small>

**`kmsFunCut Rc` is differentiable at every interior strip point** (`−1<Im z₀<0`) — the open-strip (`DifferentiableOn`) half of `DiffContOnCl` for the truncated function. Same dominated-derivative assembly as `kmsFun_differentiableAt`, but over the restricted measure `volume.restrict [−Rc,Rc]`; the interior `σ`-damped bound (`kmsIntegrand_deriv_bound`) and integrability transfer to the restricted measure via `.integrableOn`.

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall (\mathrm{Rc} : \mathbb{R}) \{z_{0} : \mathbb{C}\}, -1 < z_{0}.\mathrm{im} \to z_{0}.\mathrm{im} < 0 \to \mathrm{DifferentiableAt}\,\mathbb{C}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,\mathrm{Rc})\,z_{0}
$$

*Proof.* By [`hasDerivAt_kmsIntegrand_z`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z), [`continuous_kmsIntegrand_in_theta`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [`continuous_kmsIntegrand_deriv_in_theta`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta), [`integrable_kmsIntegrand`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-integrable-kmsintegrand), [`exists_sin_min`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-exists-sin-min), [`kmsIntegrand_deriv_bound`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsintegrand-deriv-bound), [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`integrable_cosh_mul_exp_neg_const_mul_cosh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-integrable-cosh-mul-exp-neg-const-mul-cosh). $\square$

<small>Used by [`kmsFunCut_differentiableOn`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableon).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-differentiableon"></a>
**Lemma 123** (`kmsFunCut_differentiableOn`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L790)</small>

**`kmsFunCut Rc` is holomorphic on the open strip** `{−1<Im z<0}` — the `DifferentiableOn` half of `DiffContOnCl` for the truncated function (immediate from `kmsFunCut_differentiableAt`).

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall (\mathrm{Rc} : \mathbb{R}), \mathrm{DifferentiableOn}\,\mathbb{C}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,\mathrm{Rc})\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0)
$$

*Proof.* By [`kmsFunCut_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableat). $\square$

<small>Used by [`norm_kmsFunCut_diff_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-continuouson"></a>
**Lemma 124** (`kmsFunCut_continuousOn`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L801)</small>

**`kmsFunCut Rc` is continuous on the CLOSED strip** `{−1≤Im z≤0}` — the `ContinuousOn` half of `DiffContOnCl`. This is where the θ-truncation pays off: the integrand is dominated by the **constant** `C_g·C_f` uniformly on the closed strip (no degeneration, since `‖KrepCont‖ ≤ C` for `Im arg ∈ [0,π]`), which is integrable on the finite-measure window `[−Rc,Rc]`; `continuousOn_of_dominated` + the integrand's `z`-continuity (`differentiable_kmsIntegrand`) close it.

$$
0 \le m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 \le \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall (\mathrm{Rc} : \mathbb{R}), \mathrm{ContinuousOn}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,\mathrm{Rc})\,(\mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0)
$$

*Proof.* By [`differentiable_kmsIntegrand`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-differentiable-kmsintegrand), [`continuous_kmsIntegrand_in_theta`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`norm_KrepCont_le_const`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-const). $\square$

<small>Used by [`norm_kmsFunCut_diff_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-ofreal"></a>
**Lemma 125** (`kmsFunCut_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L852)</small>

**`kmsFunCut` on the real axis** — same `KrepCont→Krep` collapse as `kmsFun_ofReal`, over `[−R,R]`.

$$
\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,t = \int (\theta : \mathbb{R}) in \mathrm{Icc}\,(-R)\,R, (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,(\theta + \pi \cdot t)) \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - \pi \cdot t)
$$

*Proof.* By [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`KrepCont_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal). $\square$

<small>Used by [`kmsFunCut_sub_I`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-sub-i), [`norm_kmsFunCut_diff_ofReal_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-sub-i"></a>
**Lemma 126** (`kmsFunCut_sub_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L904)</small>

**`kmsFunCut` bottom edge** `F(t−i) = conj F(t)` (real `f,g`) — same `iπ`-shift collapse as `kmsFun_sub_I`, over `[−R,R]`.

$$
(\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \forall (R t : \mathbb{R}), \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,(t - i) = (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,t)
$$

*Proof.* By [`kmsFunCut_ofReal`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-ofreal), [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep), [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`KrepCont_add_pi_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i). $\square$

<small>Used by [`norm_kmsFunCut_diff_sub_I_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le).</small>

<a id="d-qiqth-fock-boostkms-norm-le-of-strip-edges"></a>
**Lemma 127** (`norm_le_of_strip_edges`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L937)</small>

**Abstract Hadamard-on-the-strip bound.** A function `Φ` holomorphic on the open strip `{−1<Im z<0}`, continuous and bounded on the closed strip, with both boundary lines `≤ b`, satisfies `‖Φ z‖ ≤ b` everywhere in the closed strip. Rotate `w↦−i·w` onto `verticalClosedStrip 0 1` and apply `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` (edge consts `b,b`, `b^(1−s)·b^s=b`). The reusable core of the truncation argument (used for `kmsFunCut` and for the annular differences `kmsFunCut S − kmsFunCut R`).

$$
\mathrm{DifferentiableOn}\,\mathbb{C}\,\Phi\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0) \to \mathrm{ContinuousOn}\,\Phi\,(\mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0) \to \mathrm{BddAbove}\,(\mathrm{norm} \circ \Phi '' \mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0) \to (\forall (t : \mathbb{R}), \|\Phi\,t\| \le b) \to (\forall (t : \mathbb{R}), \|\Phi\,(t - i)\| \le b) \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\Phi\,z\| \le b
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`norm_kmsFunCut_diff_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-real-l2-inner-le"></a>
**Lemma 128** (`real_L2_inner_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1098)</small>

**Real Cauchy–Schwarz** for nonnegative `L²` functions: `∫ u·v ≤ √(∫u²)·√(∫v²)`. Hölder `p=q=2`.

$$
\mathrm{MemLp}\,u\,2\,\mu \to \mathrm{MemLp}\,v\,2\,\mu \to 0 \le [\mu] u \to 0 \le [\mu] v \to \int (\theta : \mathbb{R}), u\,\theta \cdot v\,\theta \partial \mu \le \sqrt (\int (\theta : \mathbb{R}), {u\,\theta}^{2} \partial \mu) \cdot \sqrt (\int (\theta : \mathbb{R}), {v\,\theta}^{2} \partial \mu)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`tail_term_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-tail-term-le).</small>

<a id="d-qiqth-fock-boostkms-tail-term-le"></a>
**Lemma 129** (`tail_term_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1114)</small>

**One shifted-tail term**: with the cutoff indicator tied to the FIRST factor's shift `+c`, `∫ 1_{R<|θ+c|}·‖Krep h₁(θ+c)‖·‖Krep h₂(θ+d)‖ ≤ T_{h₁}(R)·‖Krep h₂‖₂`. Real Cauchy–Schwarz (`real_L2_inner_le`) on `1_{·}·‖Krep h₁(·+c)‖` and `‖Krep h₂(·+d)‖`, then translation-invariance (`integral_add_right_eq_self`) turns each shifted slice integral into the `t`-independent tail / full norm.

$$
\mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{2})\,2\,\mathrm{volume} \to \forall (R c d : \mathbb{R}), \int (\theta : \mathbb{R}), \{\theta|R < |\theta + c|\}.\mathbf{1}\,1\,\theta \cdot (\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{1}\,(\theta + c)\| \cdot \|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{2}\,(\theta + d)\|) \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{1}\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,h_{2}\,\theta\|}^{2})
$$

*Proof.* By [`real_L2_inner_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-real-l2-inner-le). $\square$

<small>Used by [`tail_integral_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-tail-integral-le).</small>

<a id="d-qiqth-fock-boostkms-tail-geom"></a>
**Lemma 130** (`tail_geom`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1163)</small>

**Shifted-tail geometry** (the crux of the annular bound): if `|θ| > R` then `|θ+a| > R` or `|θ−a| > R`. Since `2|θ| = |(θ+a)+(θ−a)| ≤ |θ+a|+|θ−a|`, both `≤ R` would force `|θ| ≤ R`. This is why the scalar KMS product has uniformly small edge tails even though the individual `L²` slices do not.

$$
R < |\theta| \to R < |\theta + a| \vee R < |\theta - a|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`tail_integral_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-tail-integral-le).</small>

<a id="d-qiqth-fock-boostkms-tail-integral-le"></a>
**Lemma 131** (`tail_integral_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1177)</small>

**The full tail integral bound** `∫_{|θ|>R} ‖Krep g(θ+πt)‖·‖Krep f(θ−πt)‖ ≤ ε_R`, UNIFORM in `t`, with `ε_R = T_g(R)·‖Krep f‖₂ + T_f(R)·‖Krep g‖₂`. Split the `{|θ|>R}` indicator by `tail_geom` into the two shifted tails and apply `tail_term_le` to each. The scalar product's edge tail is `t`-uniform — the heart of the annular-difference route to closed-strip continuity.

$$
\mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall (R : \mathbb{R}), \int (\theta : \mathbb{R}), \{\theta|R < |\theta|\}.\mathbf{1}\,1\,\theta \cdot (\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,(\theta + \pi \cdot t)\| \cdot \|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,(\theta - \pi \cdot t)\|) \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) + \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2})
$$

*Proof.* By [`tail_term_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-tail-term-le), [`tail_geom`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-tail-geom). $\square$

<small>Used by [`norm_kmsFunCut_diff_ofReal_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le"></a>
**Lemma 132** (`norm_kmsFunCut_diff_ofReal_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1268)</small>

**Annular top-edge bound** (`S ≥ R`): `‖kmsFunCut S t − kmsFunCut R t‖ ≤ ε_R` UNIFORMLY in `t`. The difference is `∫ (1_{Icc(−S,S)} − 1_{Icc(−R,R)})·I` whose integrand has norm `≤ 1_{|θ|>R}·w` pointwise (`I` is the real-axis integrand, `w=‖I‖`; on `|θ|≤R` it cancels, on `R<|θ|≤S` it is `I`, beyond `S` it is `0`); then `norm_integral_le_integral_norm` + `integral_mono` + `tail_integral_le`.

$$
\mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{R S : \mathbb{R}\}, R \le S \to \|\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,S\,t - \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,t\| \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) + \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2})
$$

*Proof.* By [`kmsFunCut_ofReal`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-ofreal), [`tail_integral_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-tail-integral-le). $\square$

<small>Used by [`norm_kmsFunCut_diff_sub_I_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le), [`norm_kmsFunCut_diff_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le"></a>
**Lemma 133** (`norm_kmsFunCut_diff_sub_I_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1349)</small>

**Annular bottom-edge bound** (`S ≥ R`, real `f,g`): same `ε_R` as the top edge, via `kmsFunCut_sub_I` (`F(t−i)=conj F(t)`) ⟹ the difference is the conjugate of the top-edge difference, equal norm.

$$
(\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{R S : \mathbb{R}\}, R \le S \to \|\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,S\,(t - i) - \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,(t - i)\| \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) + \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2})
$$

*Proof.* By [`kmsFunCut_sub_I`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-sub-i), [`norm_kmsFunCut_diff_ofReal_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le). $\square$

<small>Used by [`norm_kmsFunCut_diff_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le"></a>
**Lemma 134** (`norm_kmsFunCut_diff_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1360)</small>

**The annular difference is `≤ ε_R` on the WHOLE closed strip** (`S ≥ R`). `kmsFunCut S − kmsFunCut R` is `DiffContOnCl` + bounded (difference of two such), and both boundary lines are `≤ ε_R` (`norm_kmsFunCut_diff_ofReal_le`/`_sub_I_le`); `norm_le_of_strip_edges` propagates the edge bound inward. Combined with `ε_R → 0` this is the uniform-Cauchy property of `{kmsFunCut n}` on the closed strip.

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{R S : \mathbb{R}\}, 0 \le R \to R \le S \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,S\,z - \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,z\| \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) + \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2})
$$

*Proof.* By [`norm_kmsFunCut_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-le), [`kmsFunCut_differentiableOn`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableon), [`kmsFunCut_continuousOn`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-continuouson), [`norm_le_of_strip_edges`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-le-of-strip-edges), [`norm_kmsFunCut_diff_ofReal_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-ofreal-le), [`norm_kmsFunCut_diff_sub_I_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-sub-i-le). $\square$

<small>Used by [`norm_kmsFun_sub_kmsFunCut_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le).</small>

<a id="d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed"></a>
**Lemma 135** (`integrable_kmsFun_integrand_closed`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1390)</small>

**The `kmsFun` integrand is integrable at every CLOSED-strip `z`** (`−1≤Im z≤0`). Both slices are `L²` via `memLp_KrepCont_affine_closed` (arg `Im = −π·Im z ∈ [0,π]`, including the edges), so the product is integrable by AM-GM and the integrand by `integrable_norm_iff`. This is the per-`z` input that makes `kmsFunCut n z → kmsFun z` hold up to the boundary.

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \mathrm{Integrable}\,(\lambda \theta \mapsto (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,g\,((\mathrm{starRingEnd}\,\mathbb{C})\,(\theta + \pi \cdot z))) \cdot \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{\mathrm{KrepCont}}\,m\,f\,(\theta - \pi \cdot z))\,\mathrm{volume}
$$

*Proof.* By [`memLp_KrepCont_affine_closed`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed). $\square$

<small>Used by [`kmsFunCut_tendsto_closed`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed), [`kmsFun_add_left`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-add-left), [`kmsFun_add_right`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-add-right).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed"></a>
**Lemma 136** (`kmsFunCut_tendsto_closed`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1447)</small>

**`kmsFunCut n z → kmsFun z` up to the boundary**: for closed-strip `z`, `tendsto_setIntegral_of_monotone` (`⋃ₙ[−n,n]=ℝ`) with the closed-strip integrability `integrable_kmsFun_integrand_closed`.

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \mathrm{Tendsto}\,(\lambda n \mapsto \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,(n)\,z)\,\mathrm{atTop}\,(\mathrm{nhds}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,z))
$$

*Proof.* By [`integrable_kmsFun_integrand_closed`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed), [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont). $\square$

<small>Used by [`norm_kmsFun_sub_kmsFunCut_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le"></a>
**Lemma 137** (`norm_kmsFun_sub_kmsFunCut_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1472)</small>

**Uniform error `‖kmsFun z − kmsFunCut R z‖ ≤ ε_R`** on the closed strip (`R ≥ 0`). Pass `S→∞` to the limit in `norm_kmsFunCut_diff_le` via `kmsFunCut_tendsto_closed` + `le_of_tendsto`.

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{R : \mathbb{R}\}, 0 \le R \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,z - \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,R\,z\| \le \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) + \sqrt (\int (\theta : \mathbb{R}) in \{\theta|R < |\theta|\}, {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2}) \cdot \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g\,\theta\|}^{2})
$$

*Proof.* By [`norm_kmsFunCut_diff_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-diff-le), [`kmsFunCut_tendsto_closed`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-tendsto-closed). $\square$

<small>Used by [`norm_kmsFun_le_norm_mul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul).</small>

<a id="d-qiqth-fock-boostkms-kmsfuncut-zero"></a>
**Lemma 138** (`kmsFunCut_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1546)</small>

`kmsFunCut m f g 0 z = 0` — the cutoff window `[−0,0] = {0}` has measure zero.

$$
\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut}{\mathrm{kms}}\,m\,f\,g\,0\,z = 0
$$

*Proof.* By [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont). $\square$

<small>Used by [`norm_kmsFun_le_norm_mul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-add-left"></a>
**Lemma 139** (`kmsFun_add_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1571)</small>

**`kmsFun` is additive in the `f` slot** on the closed strip (continuous compact-support real wedge `f₁,f₂,g` with `MemLp` amplitudes). `KrepCont_add` distributes the `f`-factor; the outer integral splits by `integral_add` (each summand integrable via `integrable_kmsFun_integrand_closed`).

$$
0 < m \to \forall \{f_{1} f_{2} g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,(f_{1} + f_{2})\,g\,z = \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{1}\,g\,z + \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{2}\,g\,z
$$

*Proof.* By [`integrable_kmsFun_integrand_closed`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed), [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`KrepCont_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-add). $\square$

<small>Used by [`kmsFun_sub_left`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-left).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-add-right"></a>
**Lemma 140** (`kmsFun_add_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1598)</small>

**`kmsFun` is additive in the `g` slot** on the closed strip. Same as `kmsFun_add_left` but on the conjugated `g`-factor (`KrepCont_add` + `map_add` for `conj`).

$$
0 < m \to \forall \{f g_{1} g_{2} : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g_{1} \to \mathrm{HasCompactSupport}\,g_{1} \to \mathrm{Continuous}\,g_{2} \to \mathrm{HasCompactSupport}\,g_{2} \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{2})\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,(g_{1} + g_{2})\,z = \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g_{1}\,z + \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g_{2}\,z
$$

*Proof.* By [`integrable_kmsFun_integrand_closed`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed), [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`KrepCont_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-add). $\square$

<small>Used by [`kmsFun_sub_right`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-right).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-sub-left"></a>
**Lemma 141** (`kmsFun_sub_left`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1624)</small>

**`f`-slot subtraction identity**: `kmsFun m (f₁−f₂) g = kmsFun m f₁ g − kmsFun m f₂ g` on the closed strip (from `kmsFun_add_left`; `f₁−f₂` is again nice — `δ`-margin on the union of supports, real, `MemLp`).

$$
0 < m \to \forall \{f_{1} f_{2} g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,(f_{1} - f_{2})\,g\,z = \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{1}\,g\,z - \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{2}\,g\,z
$$

*Proof.* By [`kmsFun_add_left`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-add-left), [`memLp_Krep_sub`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krep-sub). $\square$

<small>Used by [`norm_kmsFun_sub_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-sub-le).</small>

<a id="d-qiqth-fock-boostkms-kmsfun-sub-right"></a>
**Lemma 142** (`kmsFun_sub_right`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1651)</small>

**`g`-slot subtraction identity**: `kmsFun m f (g₁−g₂) = kmsFun m f g₁ − kmsFun m f g₂` (from `kmsFun_add_right`; `g₁−g₂` is again nice).

$$
0 < m \to \forall \{f g_{1} g_{2} : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g_{1} \to \mathrm{HasCompactSupport}\,g_{1} \to \mathrm{Continuous}\,g_{2} \to \mathrm{HasCompactSupport}\,g_{2} \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,2\,\mathrm{volume} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{2})\,2\,\mathrm{volume} \to \forall \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,(g_{1} - g_{2})\,z = \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g_{1}\,z - \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g_{2}\,z
$$

*Proof.* By [`kmsFun_add_right`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-add-right), [`memLp_Krep_sub`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krep-sub). $\square$

<small>Used by [`norm_kmsFun_sub_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-sub-le).</small>

<a id="d-qiqth-fock-boostkms-norm-tolp-krep-eq-sqrt"></a>
**Lemma 143** (`norm_toLp_Krep_eq_sqrt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1678)</small>

**`L²`-norm of a one-particle vector as an integral**: `‖KrepL2 f‖ = √(∫‖Krep m f‖²)`. Via `inner_KrepL2` (`⟪KrepL2 f, KrepL2 f⟫ = ∫ conj(Krep f)·Krep f = ↑∫‖Krep f‖²`) and `inner_self_eq_norm_sq`. The bridge from the analytic strip bound (in `∫‖Krep‖²`) to the Hilbert norms `‖ξ‖,‖η‖` for the closure/threading argument.

$$
\|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hf}\| = \sqrt (\int (\theta : \mathbb{R}), {\|\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta\|}^{2})
$$

*Proof.* By [`inner_KrepL2`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-krepl2). $\square$

<small>Used by [`norm_kmsFun_le_norm_mul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul).</small>

<a id="d-qiqth-fock-boostkms-minkowskifourier-smul"></a>
**Lemma 144** (`minkowskiFourier_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1695)</small>

**`minkowskiFourier` is `ℂ`-homogeneous in the test function**: `(c·f)^_M = c·f̂_M`.

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,(\lambda x \mapsto c \cdot f\,x)\,p = c \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,f\,p
$$

*Proof.* By [`minkowskiDot`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot). $\square$

<small>Used by [`Krep_smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-krep-smul).</small>

<a id="d-qiqth-fock-boostkms-krep-smul"></a>
**Lemma 145** (`Krep_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1703)</small>

**`Krep` is `ℂ`-homogeneous in the test function**: `Krep m (c·f) = c·Krep m f`.

$$
(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,\lambda x \mapsto c \cdot f\,x) = \lambda \theta \mapsto c \cdot \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f\,\theta
$$

*Proof.* By [`minkowskiFourier_smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-minkowskifourier-smul), [`massShell`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell), [`minkowskiFourier`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier). $\square$

<small>Used by [`vec_smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-smul).</small>

<a id="d-qiqth-fock-boostkms-krepl2-add"></a>
**Lemma 146** (`KrepL2_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1708)</small>

**`KrepL2` respects addition**: `KrepL2(f₁+f₂) = KrepL2 f₁ + KrepL2 f₂` in `L²`. `MemLp.toLp_add` + `MemLp.toLp_eq_toLp_iff` (`Krep(f₁+f₂) =ᵐ Krep f₁ + Krep f₂`, `Krep_add`). With `KrepL2_sub` and the real scalar law, this makes `{KrepL2 f : f nice}` an ℝ-subspace, so `span_ℝ` adds nothing: every span element is a single `KrepL2` of a nice function — collapsing the closure threading to single nice generator pairs.

$$
\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(f_{1} + f_{2}))\,\cdots = \mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,\mathrm{hf}_{1}L + \mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L
$$

*Proof.* By [`Krep_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krep-add). $\square$

<small>Used by [`vec_add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-add).</small>

<a id="d-qiqth-fock-boostkms-krepl2-sub"></a>
**Lemma 147** (`KrepL2_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1721)</small>

**`KrepL2` respects subtraction**: `KrepL2(f₁−f₂) = KrepL2 f₁ − KrepL2 f₂` in `L²`. `MemLp.toLp_sub` + `MemLp.toLp_eq_toLp_iff` (the `Lp` elements agree since `Krep(f₁−f₂) =ᵐ Krep f₁ − Krep f₂`, `Krep_sub`). Lets `‖KrepL2(Fₙ−Fₘ)‖ = ‖ξₙ − ξₘ‖ → 0` drive the closure Cauchy argument.

$$
\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(f_{1} - f_{2}))\,\cdots = \mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,\mathrm{hf}_{1}L - \mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L
$$

*Proof.* By [`Krep_sub`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krep-sub). $\square$

<small>Used by [`norm_kmsFun_sub_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-sub-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul"></a>
**Lemma 148** (`norm_kmsFun_le_norm_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1733)</small>

**Strip bound in Hilbert norms**: `‖kmsFun z‖ ≤ 2·‖KrepL2 g‖·‖KrepL2 f‖` on the closed strip. The `R=0` annular constant `ε₀` rewritten via `{0<|θ|} =ᵐ ℝ` and `norm_toLp_Krep_eq_sqrt`. The Cauchy–Schwarz-type bound `‖F z‖ ≤ C·‖η‖·‖ξ‖` controlling the span-closure threading.

$$
0 < m \to \forall \{f g : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,g \to \mathrm{HasCompactSupport}\,g \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), g\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(g\,x) = g\,x) \to \forall (\mathrm{hfL} : \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume}) (\mathrm{hgL} : \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,2\,\mathrm{volume}) \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,z\| \le 2 \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,\mathrm{hgL}\| \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hfL}\|
$$

*Proof.* By [`kmsFunCut`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut), [`norm_kmsFun_sub_kmsFunCut_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-sub-kmsfuncut-le), [`kmsFunCut_zero`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-zero), [`norm_toLp_Krep_eq_sqrt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-tolp-krep-eq-sqrt). $\square$

<small>Used by [`norm_kmsFun_sub_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-sub-le).</small>

<a id="d-qiqth-fock-boostkms-norm-kmsfun-sub-le"></a>
**Lemma 149** (`norm_kmsFun_sub_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1762)</small>

**Difference bound (closure Cauchy keystone)**: on the closed strip, `‖kmsFun f₁ g₁ z − kmsFun f₂ g₂ z‖ ≤ 2‖KrepL2 g₁‖·‖KrepL2 f₁ − KrepL2 f₂‖ + 2‖KrepL2 g₁ − KrepL2 g₂‖·‖KrepL2 f₂‖`. Difference identity (`kmsFun_sub_left/right`) ⟹ `kmsFun_{f₁−f₂,g₁}+kmsFun_{f₂,g₁−g₂}`, each bounded by `norm_kmsFun_le_norm_mul` and rewritten via `KrepL2_sub`. The controlling estimate for the BCF Cauchy net.

$$
0 < m \to \forall \{f_{1} f_{2} g_{1} g_{2} : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \mathrm{Continuous}\,g_{1} \to \mathrm{HasCompactSupport}\,g_{1} \to \mathrm{Continuous}\,g_{2} \to \mathrm{HasCompactSupport}\,g_{2} \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{f}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \mathrm{g}\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{f}\,x) = \mathrm{f}\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{g}\,x) = \mathrm{g}\,x) \to \forall (\mathrm{hf}_{1}L : \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,2\,\mathrm{volume}) (\mathrm{hf}_{2}L : \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,2\,\mathrm{volume}) (\mathrm{hg}_{1}L : \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,2\,\mathrm{volume}) (\mathrm{hg}_{2}L : \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{2})\,2\,\mathrm{volume}) \{z : \mathbb{C}\}, -1 \le z.\mathrm{im} \to z.\mathrm{im} \le 0 \to \|\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{1}\,g_{1}\,z - \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f_{2}\,g_{2}\,z\| \le 2 \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,\mathrm{hg}_{1}L\| \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,\mathrm{hf}_{1}L - \mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L\| + 2 \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,\mathrm{hg}_{1}L - \mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{2})\,\mathrm{hg}_{2}L\| \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L\|
$$

*Proof.* By [`kmsFun_sub_left`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-left), [`kmsFun_sub_right`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-right), [`KrepL2_sub`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-krepl2-sub), [`norm_kmsFun_le_norm_mul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-le-norm-mul), [`memLp_Krep_sub`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krep-sub). $\square$

<small>Used by [`dist_kmsBCF_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-dist-kmsbcf-le).</small>

<a id="d-qiqth-fock-boostkms-memlp-krep-boosttest"></a>
**Lemma 150** (`memLp_Krep_boostTest`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1811)</small>

**Boost-translate preserves `L²`**: `MemLp (Krep m (boostTest a f)) 2` from `MemLp (Krep m f) 2`, since `Krep m (boostTest a f) = Krep m f ∘ (·+a)` (`Krep_boost`) and translation is measure-preserving.

$$
\mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \forall (a : \mathbb{R}), \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,a\,f))\,2\,\mathrm{volume}
$$

*Proof.* By [`Krep_boost`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-boost). $\square$

<small>Used by [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot).</small>

<a id="d-qiqth-fock-boostkms-kmsbcf"></a>
**Definition 151** (`kmsBCF`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1842)</small>

**(c1) The KMS witness as a bounded continuous function on the closed strip** (nice `f,g`). Continuous via `kmsFun_continuousOn_closed`, bounded by `2‖KrepL2 g‖·‖KrepL2 f‖` via `norm_kmsFun_le_norm_mul`. The vehicle for the uniform-Cauchy limit (`norm_kmsFun_sub_le`) in the span-closure threading to `StripKMSrvd 𝒦_W`.

$$
\mathrm{kmsBCF}\,m\,\mathrm{hm}\,f\,g\,\mathrm{hf}\,\mathrm{hfc}\,\mathrm{hg}\,\mathrm{hgc}\,\delta\,h\delta\,\mathrm{hmf}\,\mathrm{hmg}\,\mathrm{hfr}\,\mathrm{hgr}\,\mathrm{hfL}\,\mathrm{hgL} \;:=\; \mathrm{ofNormedAddCommGroup}\,((\mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0).\mathrm{restr}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g))\,\cdots \,(2 \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g)\,\mathrm{hgL}\| \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,\mathrm{hfL}\|)\,\cdots
$$

<small>Used by [`kmsBCF_apply`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf-apply), [`dist_kmsBCF_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-dist-kmsbcf-le), [`kmsBCF_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf-congr), [`bcf`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf), [`bcf_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-congr), [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), and 1 more.</small>

<a id="d-qiqth-fock-boostkms-kmsbcf-apply"></a>
**Lemma 152** (`kmsBCF_apply`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1862)</small>

$$
(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\mathrm{hf}\,\mathrm{hfc}\,\mathrm{hg}\,\mathrm{hgc}\,h\delta\,\mathrm{hmf}\,\mathrm{hmg}\,\mathrm{hfr}\,\mathrm{hgr}\,\mathrm{hfL}\,\mathrm{hgL})\,z = \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun}{\mathrm{kmsFun}}\,m\,f\,g\,z
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`dist_kmsBCF_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-dist-kmsbcf-le), [`kmsBCF_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf-congr), [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-dist-kmsbcf-le"></a>
**Lemma 153** (`dist_kmsBCF_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1872)</small>

**(c2) BCF Cauchy-control step**: `dist (kmsBCF f₁ g₁) (kmsBCF f₂ g₂) ≤ ` the difference bound. Via `BoundedContinuousFunction.dist_le` + the pointwise `norm_kmsFun_sub_le`. (Common margin `δ`.)

$$
\mathrm{dist}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\mathrm{hf}_{1}\,\mathrm{hf}_{1}c\,\mathrm{hg}_{1}\,\mathrm{hg}_{1}c\,h\delta\,\mathrm{hmf}_{1}\,\mathrm{hmg}_{1}\,\mathrm{hf}_{1}r\,\mathrm{hg}_{1}r\,\mathrm{hf}_{1}L\,\mathrm{hg}_{1}L)\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\mathrm{hf}_{2}\,\mathrm{hf}_{2}c\,\mathrm{hg}_{2}\,\mathrm{hg}_{2}c\,h\delta\,\mathrm{hmf}_{2}\,\mathrm{hmg}_{2}\,\mathrm{hf}_{2}r\,\mathrm{hg}_{2}r\,\mathrm{hf}_{2}L\,\mathrm{hg}_{2}L) \le 2 \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,\mathrm{hg}_{1}L\| \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{1})\,\mathrm{hf}_{1}L - \mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L\| + 2 \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{1})\,\mathrm{hg}_{1}L - \mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,g_{2})\,\mathrm{hg}_{2}L\| \cdot \|\mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f_{2})\,\mathrm{hf}_{2}L\|
$$

*Proof.* By [`kmsFun`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun), [`norm_kmsFun_sub_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-sub-le), [`kmsBCF_apply`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf-apply). $\square$

<small>Used by [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le).</small>

<a id="d-qiqth-fock-boostkms-kmsbcf-congr"></a>
**Lemma 154** (`kmsBCF_congr`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1899)</small>

**`kmsBCF` is independent of the margin `δ`** (the BCF is determined by its coeFn `kmsFun m f g`, which has no `δ`). Lets the closure Cauchy sequence over approximants with shrinking margins `δₙ→0` be compared at a common (minimal) `δ` via `dist_kmsBCF_le`.

$$
\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\mathrm{hf}\,\mathrm{hfc}\,\mathrm{hg}\,\mathrm{hgc}\,h\delta\,\mathrm{hmf}\,\mathrm{hmg}\,\mathrm{hfr}\,\mathrm{hgr}\,\mathrm{hfL}\,\mathrm{hgL} = \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\mathrm{hf}\,\mathrm{hfc}\,\mathrm{hg}\,\mathrm{hgc}\,h\delta'\,\mathrm{hmf}^{\prime}\,\mathrm{hmg}^{\prime}\,\mathrm{hfr}\,\mathrm{hgr}\,\mathrm{hfL}\,\mathrm{hgL}
$$

*Proof.* By [`kmsFun`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun), [`kmsBCF_apply`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf-apply). $\square$

<small>Used by [`bcf_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-congr).</small>

<a id="d-qiqth-fock-boostkms-nicetest"></a>
**Lemma 155** (`NiceTest`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1917)</small>

**A nice wedge test function**: the bundled data for a one-particle generator of the wedge standard subspace — continuous, compactly supported, real, with a `δ`-margin inside the wedge, and `L²` on-shell amplitude.  This is the standard AQFT wedge-localization core class (compactly-supported `δ`-margin functions), closed under `±`, so the generators `{NiceTest.vec}` already form an ℝ-subspace — and the BW/KMS extension over `closure(span(niceWedgeGenSet))` reduces to a closure limit over single nice generator PAIRS (no density theorem; the `kmsBCF` Cauchy limit closes the span).

$$
\mathbb{R} \to Type
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`mk`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-mk), [`f`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-f), [`cont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cont), [`cpt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cpt), [`δ`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest), [`hδ`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-h), [`margin`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-margin), [`real`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-real), and 29 more.</small>

<a id="d-qiqth-fock-boostkms-nicetest-mk"></a>
**Lemma 156** (`mk`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1923)</small>

$$
\{m : \mathbb{R}\} \to (f : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}) \to \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to (\delta : \mathbb{R}) \to 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,f)\,2\,\mathrm{volume} \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest}{\mathrm{NiceTest}}\,m
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-add), [`boost`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-boost), [`zero`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-zero), [`smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-smul), [`bumpNiceTestW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpnicetestw).</small>

<a id="d-qiqth-fock-boostkms-nicetest-f"></a>
**Definition 157** (`f`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1925)</small>

the underlying test function

$$
f\,m\,\mathrm{self} \;:=\; \mathrm{self}.1
$$

<small>Used by [`cont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cont), [`cpt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cpt), [`margin`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-margin), [`real`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-real), [`memLp`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-memlp), [`vec`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec), [`add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-add), [`vec_add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-add), and 15 more.</small>

<a id="d-qiqth-fock-boostkms-nicetest-cont"></a>
**Lemma 158** (`cont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1926)</small>

$$
\mathrm{Continuous}\,\mathrm{self}.f
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`vec_add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-add), [`bcf`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf), [`bcf_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-congr), [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-cpt"></a>
**Lemma 159** (`cpt`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1927)</small>

$$
\mathrm{HasCompactSupport}\,\mathrm{self}.f
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`vec_add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-add), [`bcf`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf), [`bcf_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-congr), [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest"></a>
**Definition 160** (`δ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1929)</small>

the wedge margin

$$
\delta\,m\,\mathrm{self} \;:=\; \mathrm{self}.4
$$

<small>Used by [`hδ`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-h), [`margin`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-margin), [`add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-add), [`margin_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-margin-le), [`bcf`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf), [`bcf_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-congr), [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), and 4 more.</small>

<a id="d-qiqth-fock-boostkms-nicetest-h"></a>
**Lemma 161** (`hδ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1930)</small>

$$
0 < \mathrm{self}.\delta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`bcf_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-congr), [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [`smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-smul), [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-margin"></a>
**Lemma 162** (`margin`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1931)</small>

$$
\mathrm{self}.f\,x \ne 0 \to \mathrm{self}.\delta \le x\,1 - x\,0 \wedge \mathrm{self}.\delta \le x\,1 + x\,0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`margin_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-margin-le).</small>

<a id="d-qiqth-fock-boostkms-nicetest-real"></a>
**Lemma 163** (`real`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1932)</small>

$$
(\mathrm{starRingEnd}\,\mathbb{C})\,(\mathrm{self}.f\,x) = \mathrm{self}.f\,x
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`bcf`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf), [`bcf_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-congr), [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-memlp"></a>
**Lemma 164** (`memLp`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1933)</small>

$$
\mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,\mathrm{self}.f)\,2\,\mathrm{volume}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`vec`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec), [`vec_add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-add), [`bcf`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf), [`bcf_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-congr), [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [`vec_boost`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-boost), and 5 more.</small>

<a id="d-qiqth-fock-boostkms-nicetest-vec"></a>
**Definition 165** (`vec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1935)</small>

The one-particle vector `KrepL2 f ∈ L²` of a nice test function.

$$
\mathrm{vec}\,m\,N \;:=\; \mathrm{toLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,N.f)\,\cdots
$$

<small>Used by [`vec_add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-add), [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [`bcf_cauchySeq`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-cauchyseq), [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [`niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset), [`mem_niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-mem-nicewedgegenset), [`niceWedgeGenSet_add_mem`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset-add-mem), and 11 more.</small>

<a id="d-qiqth-fock-boostkms-nicetest-add"></a>
**Definition 166** (`add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1939)</small>

**Nice tests are closed under addition** (margin → `min`, support → union): the sum is again nice. The structural engine behind `span_ℝ(niceWedgeGenSet) = niceWedgeGenSet`.

$$
\mathrm{add}\,m\,N_{1}\,N_{2} \;:=\; \{f :=N_{1}.f + N_{2}.f , \mathrm{cont} :=\cdots , \mathrm{cpt} :=\cdots , \delta :=\mathrm{min}\,N_{1}.\delta\,N_{2}.\delta , h\delta :=\cdots , \mathrm{margin} :=\cdots , \mathrm{real} :=\cdots , \mathrm{memLp} :=\cdots \}
$$

<small>Used by [`vec_add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-add), [`niceWedgeGenSet_add_mem`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset-add-mem).</small>

<a id="d-qiqth-fock-boostkms-nicetest-vec-add"></a>
**Lemma 167** (`vec_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1958)</small>

**`NiceTest.add` realizes Hilbert-space addition**: `(N₁.add N₂).vec = N₁.vec + N₂.vec` (via `KrepL2_add`).

$$
(N_{1}.\mathrm{add}\,N_{2}).\mathrm{vec} = N_{1}.\mathrm{vec} + N_{2}.\mathrm{vec}
$$

*Proof.* By [`KrepL2_add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-krepl2-add), [`f`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-f), [`cont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cont), [`cpt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cpt), [`memLp`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-memlp). $\square$

<small>Used by [`niceWedgeGenSet_add_mem`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset-add-mem).</small>

<a id="d-qiqth-fock-boostkms-nicetest-margin-le"></a>
**Lemma 168** (`margin_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1987)</small>

**Margin monotonicity**: a nice test's `δ`-margin also holds at any smaller `δ₀ ≤ δ`. Lets a pair of nice tests with different margins be compared at the common (smaller) margin.

$$
\delta_{0} \le N.\delta \to \forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), N.f\,x \ne 0 \to \delta_{0} \le x\,1 - x\,0 \wedge \delta_{0} \le x\,1 + x\,0
$$

*Proof.* By [`margin`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-margin). $\square$

<small>Used by [`bcf_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-congr), [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-bcf"></a>
**Definition 169** (`bcf`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L1994)</small>

**The KMS witness BCF for a pair of nice tests** (`N` in the `ξ` slot, `M` in the `η` slot), built at the common margin `min N.δ M.δ`.  The `NiceTest`-bundled form of `kmsBCF`, the vehicle for the Cauchy limit.

$$
\mathrm{bcf}\,m\,\mathrm{hm}\,N\,M \;:=\; \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\cdots \,\cdots \,\cdots \,\cdots \,\cdots \,\cdots \,\cdots \,\cdots \,\cdots \,\cdots \,\cdots
$$

<small>Used by [`bcf_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-congr), [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le), [`bcf_cauchySeq`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-cauchyseq), [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-bcf-congr"></a>
**Lemma 170** (`bcf_congr`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2003)</small>

**`NiceTest.bcf` at an arbitrary common margin `δ'`** (δ-independence of `kmsBCF`, `kmsBCF_congr`).

$$
\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,N\,M = \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf}{\mathrm{kmsBCF}}\,\mathrm{hm}\,\cdots \,\cdots \,\cdots \,\cdots \,h\delta'\,\mathrm{hmf}^{\prime}\,\mathrm{hmg}^{\prime}\,\cdots \,\cdots \,\cdots \,\cdots
$$

*Proof.* By [`kmsBCF_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf-congr), [`δ`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest), [`hδ`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-h), [`margin_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-margin-le). $\square$

<small>Used by [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le).</small>

<a id="d-qiqth-fock-boostkms-nicetest-dist-bcf-le"></a>
**Lemma 171** (`dist_bcf_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2015)</small>

**(c2, `NiceTest` form) BCF Cauchy-control**: `dist (N₁.kmsBCF M₁) (N₂.kmsBCF M₂)` is bounded by the Hilbert-norm difference bound, reconciling the per-pair margins at the four-way minimum via `NiceTest.bcf_congr`, then `dist_kmsBCF_le`.  The keystone for the closure Cauchy sequence.

$$
\mathrm{dist}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,N_{1}\,M_{1})\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,N_{2}\,M_{2}) \le 2 \cdot \|M_{1}.\mathrm{vec}\| \cdot \|N_{1}.\mathrm{vec} - N_{2}.\mathrm{vec}\| + 2 \cdot \|M_{1}.\mathrm{vec} - M_{2}.\mathrm{vec}\| \cdot \|N_{2}.\mathrm{vec}\|
$$

*Proof.* By [`kmsBCF`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf), [`dist_kmsBCF_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-dist-kmsbcf-le), [`f`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-f), [`cont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cont), [`cpt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cpt), [`δ`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest), [`hδ`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-h), [`real`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-real), [`memLp`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-memlp), [`margin_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-margin-le), [`bcf_congr`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-congr). $\square$

<small>Used by [`bcf_cauchySeq`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-cauchyseq).</small>

<a id="d-qiqth-fock-boostkms-nicetest-bcf-cauchyseq"></a>
**Lemma 172** (`bcf_cauchySeq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2037)</small>

**(c2→limit) The KMS-witness BCFs of `L²`-convergent approximants form a Cauchy sequence.**  If `(N n).vec → ξ` and `(M n).vec → η` in `L²`, then `n ↦ (N n).bcf (M n)` is `CauchySeq` in `closedStrip →ᵇ ℂ` — from `NiceTest.dist_bcf_le` (the product difference bound) plus boundedness of the convergent norm sequences and Cauchyness of the vectors.  Since `closedStrip →ᵇ ℂ` is a `CompleteSpace`, this Cauchy sequence converges (next step), giving the closure KMS witness.

$$
\mathrm{Tendsto}\,(\lambda n \mapsto (N\,n).\mathrm{vec})\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi) \to \mathrm{Tendsto}\,(\lambda n \mapsto (M\,n).\mathrm{vec})\,\mathrm{atTop}\,(\mathrm{nhds}\,\eta) \to \mathrm{CauchySeq}\,\lambda n \mapsto \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,(N\,n)\,(M\,n)
$$

*Proof.* By [`dist_bcf_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-dist-bcf-le). $\square$

<small>Used by [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top"></a>
**Lemma 173** (`bcf_apply_eq_top`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2087)</small>

**(c4) BCF top edge**: at a closed-strip point `z` with `(z:ℂ) = t` (real), `N.bcf M z = ⟪M.vec, boostUnitary(2πt) N.vec⟫` — the `StripKMSrvd` top-boundary value, via `kmsFun_ofReal_eq_inner`.

$$
z = t \to (\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,N\,M)\,z = \langle {M.\mathrm{vec}},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,N.\mathrm{vec}}\rangle
$$

*Proof.* By [`kmsFun`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun), [`kmsFun_ofReal_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [`memLp_Krep_boostTest`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-memlp-krep-boosttest), [`kmsBCF`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf), [`kmsBCF_apply`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf-apply), [`f`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-f), [`cont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cont), [`cpt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cpt), [`δ`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest), [`real`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-real), [`memLp`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-memlp). $\square$

<small>Used by [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot"></a>
**Lemma 174** (`bcf_apply_eq_bot`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2096)</small>

**(c4) BCF bottom edge**: at a closed-strip point `z` with `(z:ℂ) = t − i`, `N.bcf M z = ⟪boostUnitary(2πt) N.vec, M.vec⟫` — the `StripKMSrvd` bottom-boundary value, via `kmsFun_sub_I` + `inner_conj_symm`.

$$
z = t - i \to (\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf}{\mathrm{bcf}}\,\mathrm{hm}\,N\,M)\,z = \langle {(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,N.\mathrm{vec}},{M.\mathrm{vec}}\rangle
$$

*Proof.* By [`kmsFun`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun), [`kmsFun_ofReal_eq_inner`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal-eq-inner), [`kmsFun_sub_I`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-i), [`memLp_Krep_boostTest`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-memlp-krep-boosttest), [`kmsBCF`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf), [`kmsBCF_apply`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf-apply), [`f`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-f), [`cont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cont), [`cpt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cpt), [`δ`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest), [`real`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-real), [`memLp`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-memlp), [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep). $\square$

<small>Used by [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicewedgegenset"></a>
**Definition 175** (`niceWedgeGenSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2105)</small>

**The nice-core wedge generating set**: the one-particle vectors `KrepL2 f` from *nice* wedge test functions.  The standard BW wedge-localization core; an ℝ-subspace as a set (closed under `±` via `NiceTest.add`/`vec_add`), so `span_ℝ` of it adds nothing.

$$
\mathcal{G}\,m \;:=\; \mathrm{range}\,\lambda N \mapsto N.\mathrm{vec}
$$

<small>Used by [`mem_niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-mem-nicewedgegenset), [`niceWedgeGenSet_add_mem`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset-add-mem), [`boostUnitary_mapsTo_niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [`zero_mem_niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-zero-mem-nicewedgegenset), [`niceWedgeGenSet_smul_mem`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset-smul-mem), [`niceWedgeSubmodule`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgesubmodule), [`niceWedgeClosedSubmodule_coe`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe), [`niceWedge_isCyclic_of_dense`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense), and 5 more.</small>

<a id="d-qiqth-fock-boostkms-mem-nicewedgegenset"></a>
**Lemma 176** (`mem_niceWedgeGenSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2111)</small>

Membership unfolding for `niceWedgeGenSet`: `ξ` is a nice generator iff it is some `NiceTest.vec`.

$$
\xi \in \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m \leftrightarrow \exists N, N.\mathrm{vec} = \xi
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure).</small>

<a id="d-qiqth-fock-boostkms-nicewedgegenset-add-mem"></a>
**Lemma 177** (`niceWedgeGenSet_add_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2115)</small>

**`niceWedgeGenSet` is closed under addition** (witness: `NiceTest.add`), the set-level statement that it is already an ℝ-subspace (so `span_ℝ` collapses to it).

$$
\xi \in \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m \to \eta \in \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m \to \xi + \eta \in \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m
$$

*Proof.* By [`NiceTest`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest), [`vec`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec), [`add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-add), [`vec_add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-add). $\square$

<small>Used by [`niceWedgeSubmodule`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgesubmodule).</small>

<a id="d-qiqth-fock-boostkms-nicetest-boost"></a>
**Definition 178** (`boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2149)</small>

**The boost of a nice test is again nice** (the standard wedge-localization core is boost-invariant). `f := boostTest(−a) N.f`; the wedge margin `δ` rescales to `δ·e^{−|a|} > 0` (the boost scales the lightcone coords by `e^{∓a}`), continuity/compact-support transport through the boost homeomorphism, realness and `L²` are preserved (`memLp_Krep_boostTest` via `Krep_boost`).

$$
\mathrm{boost}\,m\,N\,a \;:=\; \{f :=\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-boosttest}{\phi_{B}}\,(-a)\,N.f , \mathrm{cont} :=\cdots , \mathrm{cpt} :=\cdots , \delta :=N.\delta \cdot \exp\,(-|a|) , h\delta :=\cdots , \mathrm{margin} :=\cdots , \mathrm{real} :=\cdots , \mathrm{memLp} :=\cdots \}
$$

<small>Used by [`vec_boost`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-boost), [`boostUnitary_mapsTo_niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [`niceWedgeCyclic_of_fourier_ne_zero`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-boostkms-nicetest-vec-boost"></a>
**Lemma 179** (`vec_boost`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2185)</small>

**`NiceTest.boost` realizes the boost unitary**: `boostUnitary a N.vec = (N.boost a).vec` (`boostUnitary_KrepL2`).

$$
(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a)\,N.\mathrm{vec} = (N.\mathrm{boost}\,a).\mathrm{vec}
$$

*Proof.* By [`f`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-f), [`memLp`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-memlp), [`boostUnitary_KrepL2`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-boostunitary-krepl2). $\square$

<small>Used by [`boostUnitary_mapsTo_niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [`niceWedgeCyclic_of_fourier_ne_zero`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero).</small>

<a id="d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset"></a>
**Lemma 180** (`boostUnitary_mapsTo_niceWedgeGenSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2190)</small>

** The nice-core wedge generating set is boost-closed**: `boostUnitary a` maps `niceWedgeGenSet m` into itself.  Supplies the `𝒦`-invariance `hInv` for the `+2π` nice-core BW discharge (`oneParticleBW_niceWedge`).

$$
\mathrm{MapsTo}\,((\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,a))\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m)\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m)
$$

*Proof.* By [`NiceTest`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest), [`vec`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec), [`boost`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-boost), [`vec_boost`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-boost). $\square$

<small>Used by [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge).</small>

<a id="d-qiqth-fock-boostkms-nicetest-zero"></a>
**Definition 181** (`zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2220)</small>

**The zero nice test** (`f = 0`): witnesses `NiceTest m` is inhabited and `0 ∈ niceWedgeGenSet`.

$$
\mathrm{zero}\,m \;:=\; \{f :=\lambda x \mapsto 0 , \mathrm{cont} :=\mathrm{\_proof\_1} , \mathrm{cpt} :=\mathrm{\_proof\_2} , \delta :=1 , h\delta :=\mathrm{\_proof\_3} , \mathrm{margin} :=\mathrm{\_proof\_4} , \mathrm{real} :=\mathrm{\_proof\_5} , \mathrm{memLp} :=\cdots \}
$$

<small>Used by [`zero_vec`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-zero-vec), [`zero_mem_niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-zero-mem-nicewedgegenset).</small>

<a id="d-qiqth-fock-boostkms-nicetest-smul"></a>
**Definition 182** (`smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2231)</small>

**Real-scalar multiple of a nice test** (`c·f`): again nice (`c·f ≠ 0 ⟹ f ≠ 0`, so the margin holds at the same `δ`; realness uses `c` real).

$$
\mathrm{smul}\,m\,c\,N \;:=\; \{f :=\lambda x \mapsto c \cdot N.f\,x , \mathrm{cont} :=\cdots , \mathrm{cpt} :=\cdots , \delta :=N.\delta , h\delta :=\cdots , \mathrm{margin} :=\cdots , \mathrm{real} :=\cdots , \mathrm{memLp} :=\cdots \}
$$

<small>Used by [`vec_smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-smul), [`niceWedgeGenSet_smul_mem`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset-smul-mem).</small>

<a id="d-qiqth-fock-boostkms-nicetest-zero-vec"></a>
**Lemma 183** (`zero_vec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2243)</small>

`(NiceTest.zero m).vec = 0`.

$$
(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-zero}{\mathrm{zero}}\,m).\mathrm{vec} = 0
$$

*Proof.* By [`f`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-f), [`memLp`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-memlp), [`V`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-v), [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep), [`Krep_zero`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-zero). $\square$

<small>Used by [`zero_mem_niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-zero-mem-nicewedgegenset).</small>

<a id="d-qiqth-fock-boostkms-nicetest-vec-smul"></a>
**Lemma 184** (`vec_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2251)</small>

**`NiceTest.smul` realizes Hilbert-space real-scalar multiplication**: `(N.smul c).vec = c • N.vec`.

$$
(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-smul}{\mathrm{smul}}\,c\,N).\mathrm{vec} = c \cdot N.\mathrm{vec}
$$

*Proof.* By [`Krep_smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-krep-smul), [`f`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-f), [`memLp`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-memlp), [`V`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-v), [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep). $\square$

<small>Used by [`niceWedgeGenSet_smul_mem`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset-smul-mem).</small>

<a id="d-qiqth-fock-boostkms-zero-mem-nicewedgegenset"></a>
**Lemma 185** (`zero_mem_niceWedgeGenSet`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2262)</small>

**`0 ∈ niceWedgeGenSet`.**

$$
0 \in \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m
$$

*Proof.* By [`NiceTest`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest), [`vec`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec), [`zero`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-zero), [`zero_vec`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-zero-vec). $\square$

<small>Used by [`niceWedgeSubmodule`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgesubmodule).</small>

<a id="d-qiqth-fock-boostkms-nicewedgegenset-smul-mem"></a>
**Lemma 186** (`niceWedgeGenSet_smul_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2266)</small>

**`niceWedgeGenSet` is closed under real-scalar multiplication.**

$$
\xi \in \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m \to c \cdot \xi \in \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m
$$

*Proof.* By [`NiceTest`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest), [`vec`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec), [`smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-smul), [`vec_smul`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-smul). $\square$

<small>Used by [`niceWedgeSubmodule`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgesubmodule).</small>

<a id="d-qiqth-fock-boostkms-nicewedgesubmodule"></a>
**Definition 187** (`niceWedgeSubmodule`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2272)</small>

**`niceWedgeGenSet` is an ℝ-subspace** (carrier of an explicit `Submodule`): closed under `+`, real `•`, and contains `0`.  Hence `span_ℝ (niceWedgeGenSet) = niceWedgeGenSet` as a set (`niceWedgeGenSet_span_eq`), so the nice-core ClosedSubmodule is literally `closure (niceWedgeGenSet m)`.

$$
\mathrm{niceWedgeSubmodule}\,m \;:=\; \{\mathrm{carrier} :=\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m , \mathrm{add\_mem}^{\prime} :=\cdots , \mathrm{zero\_mem}^{\prime} :=\cdots , \mathrm{smul\_mem}^{\prime} :=\cdots \}
$$

<small>Used by [`niceWedgeClosedSubmodule`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule), [`niceWedgeClosedSubmodule_coe`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe).</small>

<a id="d-qiqth-fock-boostkms-nicewedgeclosedsubmodule"></a>
**Definition 188** (`niceWedgeClosedSubmodule`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2288)</small>

**The nice-core wedge subspace as a `ClosedSubmodule ℝ`** — the carrier object of the (would-be) wedge standard subspace, whose underlying set is exactly `closure (niceWedgeGenSet m)`.  This is the `S`-carrier the Reeh–Schlieder standardness (separating + cyclic) would be proved about; the carrier itself is elementary (the topological closure of the nice ℝ-subspace).

$$
\mathcal{K}\,m \;:=\; (\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgesubmodule}{\mathrm{niceWedgeSubmodule}}\,m).\mathrm{closure}
$$

<small>Used by [`niceWedgeClosedSubmodule_coe`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe), [`niceWedgeStandardSubspace`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgestandardsubspace), [`niceWedge_isCyclic_of_dense`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense), [`niceWedge_isCyclic_of_total`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total), [`niceWedge_isCyclic_of_total_integral`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral), [`niceWedge_isSeparating_of_no_complex_line`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-isseparating-of-no-complex-line), [`oneParticleBW_niceWedge_of_standard`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard), [`NiceWedgeSeparating`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeseparating), and 1 more.</small>

<a id="d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe"></a>
**Lemma 189** (`niceWedgeClosedSubmodule_coe`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2295)</small>

The carrier set of `niceWedgeClosedSubmodule m` is `closure (niceWedgeGenSet m)`.

$$
(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m) = \overline{{\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m}}
$$

*Proof.* By [`niceWedgeSubmodule`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgesubmodule). $\square$

<small>Used by [`niceWedge_isCyclic_of_dense`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense), [`oneParticleBW_niceWedge_of_standard`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard), [`niceWedgeSeparating_pos_mass`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass).</small>

<a id="d-qiqth-fock-boostkms-nicewedgestandardsubspace"></a>
**Definition 190** (`niceWedgeStandardSubspace`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2301)</small>

**The nice-core wedge standard subspace, GIVEN the Reeh–Schlieder properties** (separating + cyclic). Carrier = `niceWedgeClosedSubmodule m` (= `closure (niceWedgeGenSet m)`).  Separating and cyclic are the two — and only two — remaining inputs: the genuine Reeh–Schlieder frontier, isolated here as named hypotheses (the carrier and everything else is elementary and built).

$$
\mathcal{K}\,m\,\mathrm{hsep}\,\mathrm{hcyc} \;:=\; \{\mathrm{cl} :=\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m , \mathrm{IsSeparating} :=\mathrm{hsep} , \mathrm{IsCyclic} :=\mathrm{hcyc}\}
$$

<small>Used by [`oneParticleBW_niceWedge_of_standard`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard), [`oneParticleBW_niceWedge_reehSchlieder`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [`oneParticleBW_niceWedge_unconditional`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [`freeField_modularEnergy_eq_boostCharge`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [`freeField_oneParticle_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-oneparticle-hflux), [`freeField_component_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-component-hflux), [`freeField_kd_conclusion`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [`qiqt_gr_freefield`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-fock-boostkms-closedsubmodule-sup-muli-invariant"></a>
**Lemma 191** (`ClosedSubmodule_sup_mulI_invariant`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2316)</small>

**`K ⊔ iK` is `i`-invariant**: `(K ⊔ K.mulI).mulI = K ⊔ K.mulI` (`mulI_sup` + `mulI_mulI_eq` + `sup_comm`). Term-mode (`exact`) absorbs the `mulI` instance-diamond that defeats `rw`.

$$
(KK.\mathrm{mulI}).\mathrm{mulI} = KK.\mathrm{mulI}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`ClosedSubmodule_sup_mulI_eq_top_of_dense`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-closedsubmodule-sup-muli-eq-top-of-dense).</small>

<a id="d-qiqth-fock-boostkms-closedsubmodule-smul-i-mem"></a>
**Lemma 192** (`closedSubmodule_smul_I_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2326)</small>

**An `i`-invariant real closed submodule is closed under `i•`**: `S.mulI = S`, `x ∈ S` ⟹ `I • x ∈ S`.

$$
S.\mathrm{mulI} = S \to \forall \{x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})\}, x \in S \to i \cdot x \in S
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`closedSubmodule_smul_complex_mem`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-closedsubmodule-smul-complex-mem).</small>

<a id="d-qiqth-fock-boostkms-closedsubmodule-smul-complex-mem"></a>
**Lemma 193** (`closedSubmodule_smul_complex_mem`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2337)</small>

**An `i`-invariant real closed submodule is closed under `ℂ`-scalar multiplication** (a complex subspace): `c • x ∈ S` for `c : ℂ`, via `c • x = c.re • x + c.im • (I • x)`.

$$
S.\mathrm{mulI} = S \to \forall \{x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})\}, x \in S \to \forall (c : \mathbb{C}), c \cdot x \in S
$$

*Proof.* By [`closedSubmodule_smul_I_mem`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-closedsubmodule-smul-i-mem). $\square$

<small>Used by [`ClosedSubmodule_sup_mulI_eq_top_of_dense`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-closedsubmodule-sup-muli-eq-top-of-dense).</small>

<a id="d-qiqth-fock-boostkms-closedsubmodule-sup-muli-eq-top-of-dense"></a>
**Lemma 194** (`ClosedSubmodule_sup_mulI_eq_top_of_dense`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2351)</small>

** General cyclicity from density**: for ANY real closed submodule `K` and generating set `G ⊆ K` whose *complex* span is dense, `K ⊔ K.mulI = ⊤`.  `K ⊔ K.mulI` is `i`-invariant (a closed ℂ-subspace) ⊇ `G` ⊇ closure of its dense ℂ-span `= ⊤`.  The reusable engine: applies to the right wedge (`niceWedgeGenSet`), and to the complement `Kᗮ` for the dual separating reduction.

$$
\forall G\subseteq K, \mathrm{Dense}\,(\mathrm{span}\,\mathbb{C}\,G) \to KK.\mathrm{mulI} = \top
$$

*Proof.* By [`ClosedSubmodule_sup_mulI_invariant`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-closedsubmodule-sup-muli-invariant), [`closedSubmodule_smul_complex_mem`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-closedsubmodule-smul-complex-mem). $\square$

<small>Used by [`niceWedge_isCyclic_of_dense`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense).</small>

<a id="d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense"></a>
**Lemma 195** (`niceWedge_isCyclic_of_dense`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2376)</small>

** The cyclic frontier in natural Reeh–Schlieder form**: the nice-core wedge subspace is CYCLIC (`hcyc`) as soon as the *complex* span of the nice one-particle vectors is dense in `L²(ℝ)`.  Instance of `ClosedSubmodule_sup_mulI_eq_top_of_dense` with `G = niceWedgeGenSet m ⊆ K = niceWedgeClosedSubmodule m` (`niceWedgeClosedSubmodule_coe` + `subset_closure`).  This converts the lattice identity `hcyc` into the standard analytic statement `Dense (span_ℂ (niceWedgeGenSet m))` — the Reeh–Schlieder wedge-totality.

$$
\mathrm{Dense}\,(\mathrm{span}\,\mathbb{C}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m)) \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \top
$$

*Proof.* By [`niceWedgeClosedSubmodule_coe`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe), [`ClosedSubmodule_sup_mulI_eq_top_of_dense`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-closedsubmodule-sup-muli-eq-top-of-dense). $\square$

<small>Used by [`niceWedge_isCyclic_of_total`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total).</small>

<a id="d-qiqth-fock-boostkms-nicewedge-dense-of-total"></a>
**Lemma 196** (`niceWedge_dense_of_total`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2389)</small>

** Density from totality (the sharpest analytic form)**: `span_ℂ (niceWedgeGenSet m)` is dense as soon as the nice wedge generators are TOTAL — no nonzero `h ∈ L²(ℝ)` is orthogonal to every `KrepL2 f`.  Pure Hilbert-space machinery on the *complex* orthogonal complement (`orthogonal_eq_bot_iff` / `topologicalClosure_eq_top_iff`), which on `Lp ℂ 2` is the unambiguous `InnerProductSpace ℂ` — NO instance diamond.  Chains with `niceWedge_isCyclic_of_dense`: the cyclic Reeh–Schlieder frontier is now exactly "`{KrepL2 f : f nice}` is total in `L²(ℝ)`" — the canonical wedge-totality statement.

$$
(\forall (h : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\forall (N : \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest}{\mathrm{NiceTest}}\,m), \langle {N.\mathrm{vec}},{h}\rangle = 0) \to h = 0) \to \mathrm{Dense}\,(\mathrm{span}\,\mathbb{C}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m))
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`niceWedge_isCyclic_of_total`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total).</small>

<a id="d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total"></a>
**Lemma 197** (`niceWedge_isCyclic_of_total`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2410)</small>

** Cyclicity from totality**: the nice-core wedge subspace is cyclic as soon as `{KrepL2 f : f nice}` is total in `L²(ℝ)` (`niceWedge_dense_of_total` ∘ `niceWedge_isCyclic_of_dense`).  The cyclic Reeh–Schlieder frontier in its canonical, sharpest form — no instance plumbing, no density bookkeeping.

$$
(\forall (h : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\forall (N : \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest}{\mathrm{NiceTest}}\,m), \langle {N.\mathrm{vec}},{h}\rangle = 0) \to h = 0) \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \top
$$

*Proof.* By [`niceWedge_isCyclic_of_dense`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-dense), [`niceWedge_dense_of_total`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-dense-of-total). $\square$

<small>Used by [`niceWedge_isCyclic_of_total_integral`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral).</small>

<a id="d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total-integral"></a>
**Lemma 198** (`niceWedge_isCyclic_of_total_integral`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2420)</small>

** Cyclicity from totality, in fully EXPLICIT integral form** (the precise Reeh–Schlieder statement): cyclic as soon as the only `h ∈ L²(ℝ)` with `∫ conj(Krep m f θ)·h(θ) dθ = 0` for every nice wedge `f` is `h = 0`.  Via `inner_KrepL2_general` (`⟪KrepL2 f, h⟫ = ∫ conj(Krep f)·h`).  This is the cyclic frontier as a concrete integral-vanishing condition on the on-shell amplitudes — the textbook wedge-totality, no abstraction.

$$
(\forall (h : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\forall (N : \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest}{\mathrm{NiceTest}}\,m), \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,N.f\,\theta) \cdot h\,\theta = 0) \to h = 0) \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \top
$$

*Proof.* By [`inner_KrepL2_general`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-krepl2-general), [`memLp`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-memlp), [`vec`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec), [`niceWedge_isCyclic_of_total`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-iscyclic-of-total). $\square$

<small>Used by [`oneParticleBW_niceWedge_reehSchlieder`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [`oneParticleBW_niceWedge_unconditional`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [`freeField_modularEnergy_eq_boostCharge`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [`freeField_oneParticle_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-oneparticle-hflux), [`freeField_component_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-component-hflux), [`freeField_kd_conclusion`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [`qiqt_gr_freefield`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-fock-boostkms-closedsubmodule-smul-i-mem-of-mem-muli"></a>
**Lemma 199** (`closedSubmodule_smul_I_mem_of_mem_mulI`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2505)</small>

**`v ∈ K.mulI ⟹ I • v ∈ K`**: the `mulI` membership direction, via `mem_mapEquiv_iff` + `I⁻¹ = -I` + the real-subspace closure (`I•v = (-1)•((-I)•v)`).  Uses the unambiguous ℂ `scalarSMulCLE` — NO ℝ-instance tangle (unlike the `ᗮ` route).  The engine for the DIRECT separating reduction.

$$
v \in K.\mathrm{mulI} \to i \cdot v \in K
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`niceWedge_isSeparating_of_no_complex_line`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedge-isseparating-of-no-complex-line).</small>

<a id="d-qiqth-fock-boostkms-nicewedge-isseparating-of-no-complex-line"></a>
**Lemma 200** (`niceWedge_isSeparating_of_no_complex_line`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2518)</small>

** The separating frontier in DIRECT form** (sidestepping the `ᗮ` instance tangle): the nice-core wedge subspace is SEPARATING (`hsep`) as soon as it contains NO nonzero complex line — the only `v` with both `v ∈ K` and `I • v ∈ K` is `v = 0`.  Via `mem_inf` + `closedSubmodule_smul_I_mem_of_mem_mulI`, all on the unambiguous ℂ `mulI` (no orthogonal complement, no ℝ-inner-product diamond).  For the free field this is the non-degeneracy of the one-particle symplectic form (Pauli–Jordan) — the dual analytic Reeh–Schlieder input.

$$
(\forall v\in \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m, i \cdot v \in \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m \to v = 0) \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \bot
$$

*Proof.* By [`closedSubmodule_smul_I_mem_of_mem_mulI`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-closedsubmodule-smul-i-mem-of-mem-muli). $\square$

<small>Used by [`oneParticleBW_niceWedge_reehSchlieder`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [`oneParticleBW_niceWedge_unconditional`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [`freeField_modularEnergy_eq_boostCharge`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [`freeField_oneParticle_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-oneparticle-hflux), [`freeField_component_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-component-hflux), [`freeField_kd_conclusion`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [`qiqt_gr_freefield`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-fock-boostkms-stripkmsrvd-closure"></a>
**Lemma 201** (`stripKMSrvd_closure`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2535)</small>

** (c3+c4) The RvD Def 3.4 KMS witness extended to the CLOSURE of the nice generators**, axiom-free. For `ξ, η ∈ closure (niceWedgeGenSet m)` there is a bounded function `F`, holomorphic on the open strip and continuous to its closure, with the boost-KMS boundary values `F(t) = ⟪η, V(2πt) ξ⟫`, `F(t−i) = ⟪V(2πt) ξ, η⟫`. Construction: pick nice approximants `Nₙ.vec → ξ`, `Mₙ.vec → η`; their witness BCFs `(Nₙ).bcf (Mₙ)` form a Cauchy sequence (`bcf_cauchySeq`) with limit `b` in the complete space `closedStrip →ᵇ ℂ`; `F := dite`-extend `b` by `0` off the strip. …

$$
0 < m \to \forall \{\xi \eta : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})\}, \xi \in \overline{{\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m}} \to \eta \in \overline{{\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m}} \to \exists F, \mathrm{DiffContOnCl}\,\mathbb{C}\,F\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0) \wedge (\exists C, \forall (z : \mathbb{C}), \|F\,z\| \le C) \wedge (\forall (t : \mathbb{R}), F\,t = \langle {\eta},{(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,\xi}\rangle) \wedge \forall (t : \mathbb{R}), F\,(t - i) = \langle {(\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,\xi},{\eta}\rangle
$$

*Proof.* By [`kmsFun`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun), [`kmsFun_differentiableOn`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableon), [`kmsBCF`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf), [`kmsBCF_apply`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsbcf-apply), [`NiceTest`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest), [`f`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-f), [`cont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cont), [`cpt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-cpt), [`δ`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest), [`hδ`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-h), [`real`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-real), [`memLp`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-memlp), [`vec`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec), [`margin_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-margin-le), [`bcf`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf), [`bcf_cauchySeq`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-cauchyseq), [`bcf_apply_eq_top`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-top), [`bcf_apply_eq_bot`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-bcf-apply-eq-bot), [`mem_niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-mem-nicewedgegenset). $\square$

<small>Used by [`stripKMSrvd_boostUnitary`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-boostunitary), [`niceWedgeSeparating_pos_mass`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass).</small>

<a id="d-qiqth-fock-boostkms-stripkmsrvd-boostunitary"></a>
**Lemma 202** (`stripKMSrvd_boostUnitary`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2645)</small>

** `StripKMSrvd` (RvD Def 3.4) for the boost group on the FULL wedge standard subspace**, axiom-free. The free-field Bisognano–Wichmann KMS condition: the rapidity-boost unitary group `t ↦ V(2πt)` satisfies the RvD half-strip KMS condition on `closure (niceWedgeGenSet m)` — the standard wedge subspace.  Immediate packaging of `stripKMSrvd_closure` (each generator pair gets the bounded-holomorphic KMS witness).  This is the object RvD Theorem 3.8 consumes to identify the boost generator with the modular Hamiltonian — now a THEOREM, not a labelled `hKMS` hypothesis.

$$
0 < m \to \href{/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd}{\mathrm{StripKMSrvd}}\,(\lambda t \mapsto (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t)))\,(\overline{{\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m}})
$$

*Proof.* By [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure). $\square$

<small>Used by [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge).</small>

<a id="d-qiqth-fock-boostkms-oneparticlebw-nicewedge"></a>
**Lemma 203** (`oneParticleBW_niceWedge`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2656)</small>

** One-particle Bisognano–Wichmann for the nice-core wedge subspace — `hKMS` DISCHARGED at the constructed `+2π` sign**, axiom-free.  For a standard subspace `S` whose carrier is the nice-core wedge subspace `closure (niceWedgeGenSet m)` and the rapidity-boost group `V t = boostUnitary(2πt)`, the modular flow IS the boost: `modUnitary S t = V t`.  The genuine RvD Def 3.4 KMS condition (`hKMS`) is no longer a labelled hypothesis — it is supplied by the machine-checked `stripKMSrvd_boostUnitary`; the `𝒦`-invariance by `boostUnitary_mapsTo_niceWedgeGenSet` (+ `Set.MapsTo.closure`); the contraction-group structure by the boost group laws. …

$$
0 < m \to \forall (S : \mathrm{StandardSubspace}\,(\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})) (V : \mathbb{R} \to (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume}) \to L[\mathbb{C}] (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), S.\mathrm{cl} = \overline{{\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset}{\mathcal{G}}\,m}} \to (\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,x) \to \forall (t : \mathbb{R}), \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [`boostUnitary_mapsTo_niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-boostunitary-mapsto-nicewedgegenset), [`stripKMSrvd_boostUnitary`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-boostunitary), [`boostUnitary_add_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary-add-apply), [`boostUnitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary-zero-apply), [`continuous_boostUnitary_apply`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-continuous-boostunitary-apply), [`StripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd), [`oneParticleBW_complete`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-complete), [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`mem_K_iff_projK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [`gaussSmear`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear), [`gaussSmear_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear-mem-k). $\square$

<small>Used by [`oneParticleBW_niceWedge_of_standard`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard).</small>

<a id="d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard"></a>
**Lemma 204** (`oneParticleBW_niceWedge_of_standard`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2706)</small>

** The nice-core wedge BW, conditional ONLY on Reeh–Schlieder** (separating + cyclic).  For the boost `V t = boostUnitary(2πt)`, the modular flow of the nice-core wedge standard subspace IS the boost. Combines `niceWedgeStandardSubspace` with `oneParticleBW_niceWedge`, making explicit that the ENTIRE remaining gap to an unconditional free-field one-particle BW is the two Reeh–Schlieder properties (the cited frontier) — every analytic input (the KMS condition, the `𝒦`-invariance, the boost-group structure) is discharged.

$$
0 < m \to \forall (V : \mathbb{R} \to (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume}) \to L[\mathbb{C}] (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,x) \to \forall (\mathrm{hsep} : \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \bot ) (\mathrm{hcyc} : \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m).\mathrm{mulI} = \top ) (t : \mathbb{R}), \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\mathrm{hsep}\,\mathrm{hcyc})\,t = V\,t
$$

*Proof.* By [`niceWedgeClosedSubmodule_coe`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe), [`oneParticleBW_niceWedge`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge). $\square$

<small>Used by [`oneParticleBW_niceWedge_reehSchlieder`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder).</small>

<a id="d-qiqth-fock-boostkms-nicewedgeseparating"></a>
**Definition 205** (`NiceWedgeSeparating`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2767)</small>

**The Reeh–Schlieder SEPARATING condition** (the nice-core wedge subspace has no nonzero complex line): the only `v` with `v ∈ K` and `I•v ∈ K` is `v = 0` — the one-particle symplectic non-degeneracy (Pauli–Jordan).  One of the two analytic facts the free-field one-particle BW rests on; named here as a first-class goal for an analytic proof.

$$
\mathrm{NiceWedgeSeparating}\,m \;:=\; \forall v\in \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m, i \cdot v \in \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule}{\mathcal{K}}\,m \to v = 0
$$

<small>Used by [`oneParticleBW_niceWedge_reehSchlieder`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [`niceWedgeSeparating_pos_mass`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass).</small>

<a id="d-qiqth-fock-boostkms-nicewedgecyclic"></a>
**Definition 206** (`NiceWedgeCyclic`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2775)</small>

**The Reeh–Schlieder CYCLIC condition** (wedge-totality of the on-shell amplitudes): the only `h ∈ L²(ℝ)` with `∫ conj(Krep m f θ)·h(θ) dθ = 0` for every nice wedge `f` is `h = 0` — Paley–Wiener / edge-of-the-wedge.  The other analytic fact the free-field one-particle BW rests on.

$$
\mathrm{NiceWedgeCyclic}\,m \;:=\; \forall (h : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\forall (N : \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest}{\mathrm{NiceTest}}\,m), \int (\theta : \mathbb{R}), (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,N.f\,\theta) \cdot h\,\theta = 0) \to h = 0
$$

<small>Used by [`niceWedgeCyclic_of_fourier_ne_zero`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero), [`oneParticleBW_niceWedge_reehSchlieder`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder), [`niceWedgeCyclic_bumpW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw), [`niceWedgeCyclic_of_bumpW_fourier_ne_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-of-bumpw-fourier-ne-zero), [`niceWedgeCyclic_pos_mass`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-pos-mass).</small>

<a id="d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero"></a>
**Lemma 207** (`niceWedgeCyclic_of_fourier_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2784)</small>

** `NiceWedgeCyclic` from the Wiener–Tauberian theorem.**  The wedge-totality Reeh–Schlieder condition holds as soon as there is ONE nice generator `N₀` whose one-particle Fourier transform is nonzero almost everywhere.  Proof: `h ⊥` every nice generator ⟹ `h ⊥` the whole rapidity-boost orbit of `N₀` (boosts of a nice generator are nice generators, `NiceTest.vec_boost`; the orthogonality is the integral via `inner_KrepL2_general`); then the complete L²-Wiener theorem (`boost_orbit_total_of_fourier_ne_zero`) forces `h = 0`.  This reduces the entire cyclic Reeh–Schlieder input to the SINGLE concrete analytic fact `𝓕(N₀.vec) ≠ 0` a.e. — no edge-of-the-wedge analyticity.

$$
(\forall (\xi : \mathbb{R}), (\mathcal{F}\,N_{0}.\mathrm{vec})\,\xi \ne 0) \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgecyclic}{\mathrm{NiceWedgeCyclic}}\,m
$$

*Proof.* By [`inner_KrepL2_general`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-inner-krepl2-general), [`f`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-f), [`memLp`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-memlp), [`boost`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-boost), [`vec_boost`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicetest-vec-boost), [`Krep`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep), [`boostUnitary`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary), [`boost_orbit_total_of_fourier_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-boost-orbit-total-of-fourier-ne-zero). $\square$

<small>Used by [`niceWedgeCyclic_bumpW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw).</small>

<a id="d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder"></a>
**Lemma 208** (`oneParticleBW_niceWedge_reehSchlieder`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/BoostKMS.lean#L2800)</small>

** THE free-field one-particle Bisognano–Wichmann, reduced to its TWO analytic Reeh–Schlieder inputs.** `modUnitary S t = boostUnitary(2πt)` for the nice-core wedge standard subspace, given ONLY the two named Reeh–Schlieder conditions: `NiceWedgeSeparating m` (no complex line / Pauli–Jordan) and `NiceWedgeCyclic m` (wedge-totality / Paley–Wiener).  NO lattice, NO instance, NO labelled-KMS hypotheses remain: every structural step (the KMS condition, the `𝒦`-invariance, the boost group, the standard-subspace construction, BOTH Reeh–Schlieder lattice reductions) is machine-checked and axiom-free. …

$$
0 < m \to \forall (V : \mathbb{R} \to (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume}) \to L[\mathbb{C}] (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,x) \to \forall (\mathrm{hsep} : \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeseparating}{\mathrm{NiceWedgeSeparating}}\,m) (\mathrm{hcyc} : \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgecyclic}{\mathrm{NiceWedgeCyclic}}\,m) (t : \mathbb{R}), \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t = V\,t
$$

*Proof.* By [`oneParticleBW_niceWedge_of_standard`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-of-standard). $\square$

<small>Used by [`oneParticleBW_niceWedge_unconditional`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional).</small>

---
<small>[← all sections](/browser) · [← EinsteinFieldEquation](/browser/qiqth-einsteinfieldequation) · [CyclicWitness →](/browser/qiqth-fock-cyclicwitness) </small>