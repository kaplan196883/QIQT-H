---
layout: ../../layouts/Deep.astro
title: QIQTH.KMSCorrelation
eyebrow: KMSCorrelation · section of the QIQT-H book
description: QIQTH.KMSCorrelation — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← KGStressConservation](/browser/qiqth-kgstressconservation) · [LocalizedMode →](/browser/qiqth-localizedmode) </small>

<small>KMSCorrelation · entries 469–489 of 1000</small>

<a id="d-qiqth-standardsubspacemodular-corrc-bdd-halfstrip"></a>
**Lemma 469** (`corrC_bdd_halfStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L67)</small>

**Uniform bound of the KMS correlation on the HALF strip** `{−1/2 ≤ Im z ≤ 0}` (the strip RvD Thm 3.8 / Prop 3.5 actually use): `‖corrC ξ V n η z‖ ≤ ‖ξ‖·e^{n/4}·‖η‖·√(π/n)`, since `(Im z)² ≤ 1/4` there. The bounded-holomorphic input the *correct-strip* `g`-function argument consumes (with `diffContOnCl_corrC` restricted to `kmsHalfStripOpen` and `eqOn_of_im_zero_edge_halfStrip`).

$$
0 < n \to \forall (\eta \xi : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to \forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstrip}{S_{1/2}}, \|\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-corrc}{\mathrm{corrC}}\,\xi\,V\,n\,\eta\,z\| \le \|\xi\| \cdot (\exp\,(n / 4) \cdot \|\eta\| \cdot \sqrt (\pi / n))
$$

*Proof.* By [`corrC_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-corrc-norm-le). $\square$

<small>Used by [`gFunction_bottom_real_of_kms_match`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match).</small>

<a id="d-qiqth-standardsubspacemodular-gfunction-eq-zero-const"></a>
**Lemma 470** (`gFunction_eq_zero_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L192)</small>

**The device g-function is constant on the real axis** (RvD Theorem 3.8 constancy, the analytic heart of the GConstancy output): if the device g-function `g(z) = ⟪J·d_z(R)ζ, V_z η_n⟫` is real on BOTH half-strip edges `Im z = 0` and `Im z = −1/2`, then `g(t) = g(0)` for every real `t`.  The g-function is bounded-holomorphic (`diffContOnCl_gFunction`, `gFunction_norm_le` + `gaussSmearC_norm_le` give the uniform bound `2√2‖ζ‖·e^{n/4}‖η‖√(π/n)` since `(Im z)² ≤ 1/4`), so the two-edge half-strip Phragmén–Lindelöf (`eqConst_of_im_zero_halfStrip`) forces it constant on the open half-strip; continuity to the closure (`Set.EqOn.closure`) propagates the constant to the real axis. …

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to \forall (t : \mathbb{R}), ((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,t))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,t) = ((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,0))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,0)
$$

*Proof.* By [`gFunction_norm_le`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-norm-le), [`diffContOnCl_gFunction`](/browser/qiqth-modularrelativeentropy#d-qiqth-diffcontoncl-gfunction), [`gaussSmearC_norm_le`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc-norm-le), [`kmsHalfStripOpen`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstripopen), [`eqConst_of_im_zero_halfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqconst-of-im-zero-halfstrip). $\square$

<small>Used by [`gConstancy_entire`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-entire"></a>
**Lemma 471** (`gConstancy_entire`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L232)</small>

**GConstancy for the entire vectors** (RvD Theorem 3.8 output, assembled): from the g-function constancy `g(t) = g(0)` and the edge value identities, `⟪V_t η_n, Δ^{it}(J ξ)⟫ = ⟪η_n, J ξ⟫` for `ξ = √R ζ`, `η_n = gaussSmear`.  `gFunction_eq_zero_const` gives `g(t) = g(0)`; `gFunction_real_eq` evaluates the top edge `g(t) = ⟪Δ^{it}(Jξ), V_t η_n⟫`, `gFunction_zero` the origin `g(0) = ⟪Jξ, η_n⟫`; conjugating (`inner_conj_symm`) flips both slots to the GConstancy form.  This is exactly `GConstancy S V` evaluated at `(η_n, √R ζ)` — the analytic conclusion of RvD Theorem 3.8, modulo the two edge-reality inputs.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to \forall (t : \mathbb{R}), \langle {(V\,t)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))}\rangle = \langle {\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)}\rangle
$$

*Proof.* By [`gFunction_eq_zero_const`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const), [`gFunction_zero`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-zero), [`gFunction_real_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-real-eq). $\square$

<small>Used by [`gConstancy_entire_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all"></a>
**Lemma 472** (`gFunction_top_edge_real_all`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L253)</small>

**Top-edge reality of the g-function, `∀ z` form** (the `h0` input to `gFunction_eq_zero_const`): if `ξ = √R ζ ∈ 𝒦` and the V-orbit `V_s(gaussSmear)` stays in `𝒦`, then `Im g(z) = 0` on the whole edge `Im z = 0`.  Any `z` with `Im z = 0` is real (`z = ↑z.re`), so this is just `gFunction_top_edge_real` at `t = z.re`.  Geometric — the always-available top edge of the device g-function.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to (\forall (s : \mathbb{R}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to \forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0
$$

*Proof.* By [`gFunction_top_edge_real`](/browser/qiqth-modularrelativeentropy#d-qiqth-gfunction-top-edge-real). $\square$

<small>Used by [`gConstancy_entire_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom"></a>
**Lemma 473** (`gConstancy_entire_of_bottom`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L268)</small>

**GConstancy for the entire vectors, reduced to the BOTTOM-EDGE KMS reality** (the precise residual of the RvD Theorem 3.8 discharge).  With the geometric inputs (`ξ = √R ζ ∈ 𝒦`, the V-orbit stays in `𝒦`) the top-edge reality is automatic (`gFunction_top_edge_real_all`), so the ENTIRE analytic g-function argument collapses to a single hypothesis: `h1`, the reality of `g` on the mid-line `Im z = −1/2`.  That mid-line reality is exactly the KMS input (`HalfStripReal` / `StripKMSrvd`).  Conclusion: `⟪V_t η_n, Δ^{it}(Jξ)⟫ = ⟪η_n, Jξ⟫` (GConstancy at the entire vector `η_n` and `ξ = √R ζ`) — everything but the bottom-edge KMS step is now machine-checked.

$$
0 < n \to \forall (\eta : H), (\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to (\forall (s : \mathbb{R}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to \forall (t : \mathbb{R}), \langle {(V\,t)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))}\rangle = \langle {\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)}\rangle
$$

*Proof.* By [`gConstancy_entire`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire), [`gFunction_top_edge_real_all`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-top-edge-real-all). $\square$

<small>Used by [`gConstancy_eta_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit"></a>
**Lemma 474** (`gConstancy_of_entireVec_limit`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L288)</small>

**GConstancy density**: GConstancy holds for `η` if it holds for every normalised entire vector `entireVec V n η` (`n → ∞`).  The entire vectors converge to `η` (`entireVec_tendsto`), and both sides `⟪V_t·, w⟫`, `⟪·, w⟫` are continuous, so the constant equality passes to the limit (`tendsto_nhds_unique`). This lifts the entire-vector GConstancy (`gConstancy_entire_of_bottom`) to the genuine `η ∈ 𝒦`.

$$
(\mathrm{Continuous}\,\lambda s \mapsto (V\,s)\,\eta) \to (\forall (s : \mathbb{R}), \|(V\,s)\,\eta\| \le \|\eta\|) \to (V\,0)\,\eta = \eta \to (\forall (n : \mathbb{R}), 0 < n \to \langle {(V\,t)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec}{\mathrm{ev}}\,V\,n\,\eta)},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec}{\mathrm{ev}}\,V\,n\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle) \to \langle {(V\,t)\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle
$$

*Proof.* By [`gaussSmear`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear), [`entireVec_tendsto`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec-tendsto). $\square$

<small>Used by [`gConstancy_eta_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-real-smul"></a>
**Lemma 475** (`gConstancy_real_smul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L308)</small>

**GConstancy is real-scalar linear in the vector**: if GConstancy holds for `v`, it holds for `c • v` (`c : ℝ`).  `V_t` is ℂ-linear (so commutes with the real scalar) and `⟪·, w⟫` pulls out `conj(c) = c` (`inner_smul_left`, `c` real).  This bridges `gConstancy_entire_of_bottom` (for `gaussSmear`) to the normalised entire vector `entireVec = √(n/π) • gaussSmear` the density limit consumes.

$$
\langle {(V\,t)\,v},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {v},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle \to \langle {(V\,t)\,(c \cdot v)},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {c \cdot v},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`gConstancy_eta_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-eta-of-bottom"></a>
**Lemma 476** (`gConstancy_eta_of_bottom`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L317)</small>

**GConstancy for `η ∈ 𝒦` reduced to the bottom-edge KMS reality** (the full density+scaling closeout): `⟪V_t η, Δ^{it}(Jξ)⟫ = ⟪η, Jξ⟫` for `ξ = √R ζ`, given the geometric inputs (`ξ ∈ 𝒦`, the orbit stays in `𝒦` for every entire vector) and the bottom-edge reality `h1` for every entire vector.  Chains `gConstancy_entire_of_bottom` (GConstancy for `gaussSmear V n η`) → `gConstancy_real_smul` (scale to the normalised `entireVec = √(n/π)·gaussSmear`) → `gConstancy_of_entireVec_limit` (`n → ∞`, `entireVec → η`). So the FULL GConstancy at `η` (any `η ∈ 𝒦` with the orbit hypotheses) now rests only on the bottom-edge mid-line KMS reality — the single labelled input of RvD Theorem 3.8.

$$
(\mathrm{Continuous}\,\lambda t \mapsto (V\,t)\,\eta) \to (\forall (t : \mathbb{R}), \|(V\,t)\,\eta\| \le \|\eta\|) \to (\forall (s t : \mathbb{R}), (V\,s)\,((V\,t)\,\eta) = (V\,(s + t))\,\eta) \to (V\,0)\,\eta = \eta \to (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to (\forall (n : \mathbb{R}), 0 < n \to \forall (s : \mathbb{R}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) = (V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)) \to (\forall (n : \mathbb{R}), 0 < n \to \forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,z))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,z)).\mathrm{im} = 0) \to \forall (t : \mathbb{R}), \langle {(V\,t)\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))}\rangle = \langle {\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)}\rangle
$$

*Proof.* By [`gConstancy_entire_of_bottom`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-entire-of-bottom), [`gConstancy_of_entireVec_limit`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-of-entirevec-limit), [`gConstancy_real_smul`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-real-smul), [`entireVec`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-entirevec). $\square$

<small>Used by [`gConstancy_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-of-tendsto-xi"></a>
**Lemma 477** (`gConstancy_of_tendsto_xi`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L340)</small>

**GConstancy is closed in `ξ`** (continuity in the second-slot vector): if GConstancy at `(η, ξ_k)` holds for a sequence `ξ_k → ξ`, it holds at `(η, ξ)`.  Both sides `⟪V_t η, Δ^{it}(J·)⟫` and `⟪η, J·⟫` are continuous in `ξ` (`modConj`, `modUnitary` continuous, inner continuous), so the equality passes to the limit (`tendsto_nhds_unique`).  This lifts GConstancy from `ξ = √R ζ` (`gConstancy_eta_of_bottom`) to any `ξ` in the closure of the `√R`-range — and `√R` has dense range (`R` injective via `rvdRC_mul_rvdTwoSubRC_injective`), the `ξ = √R ζ` reconciliation.

$$
\mathrm{Tendsto}\,\xis\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi) \to (\forall (k : \mathbb{N}), \langle {(V\,t)\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\mathrm{s}\,k))}\rangle = \langle {\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\mathrm{s}\,k)}\rangle) \to \langle {(V\,t)\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`gConstancy_xi_of_density`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-xi-of-density).</small>

<a id="d-qiqth-standardsubspacemodular-gconstancy-xi-of-density"></a>
**Lemma 478** (`gConstancy_xi_of_density`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L359)</small>

**GConstancy at every `ξ ∈ 𝒦`, from the `√R`-vector GConstancy + the `√R`-range density** (the `ξ`-side closeout).  Given GConstancy holds at every `√R ζ ∈ 𝒦` (`hsqrt`, supplied by `gConstancy_eta_of_bottom`) and the `√R`-range is dense in `𝒦` (`hdense`: every `ξ ∈ 𝒦` is a limit of `√R ζ_k ∈ 𝒦` — the structural fact that `√R` has dense range, `R` injective via `rvdRC_mul_rvdTwoSubRC_injective`), GConstancy holds at every `ξ ∈ 𝒦` by closedness in `ξ` (`gConstancy_of_tendsto_xi`).  This is exactly the `∀ ξ ∈ 𝒦` premise of the comparison wrapper `comparisonDatum_of_gConstancy`, completing the `ξ`-reconciliation modulo the named `√R`-density input.

$$
(\forall (\zeta : H), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \langle {(V\,t)\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))}\rangle = \langle {\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)}\rangle) \to (\forall \xi\in S.\mathrm{cl}, \exists \zetas, (\forall (k : \mathbb{N}), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k)) \wedge \mathrm{Tendsto}\,(\lambda k \mapsto (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,(\mathrm{s}\,k))\,\mathrm{atTop}\,(\mathrm{nhds}\,\xi)) \to \forall \xi\in S.\mathrm{cl}, \langle {(V\,t)\,\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi)}\rangle = \langle {\eta},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\xi}\rangle
$$

*Proof.* By [`gConstancy_of_tendsto_xi`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gconstancy-of-tendsto-xi). $\square$

<small>Used by [`gConstancy_of_inputs`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-gconstancy-of-inputs).</small>

<a id="d-qiqth-standardsubspacemodular-modunitary-eq-of-orbit-compare"></a>
**Lemma 479** (`modUnitary_eq_of_orbit_compare`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L474)</small>

**CORRECTED top-level assembly of RvD Theorem 3.8** (`hUniq` discharge, faithful form).  Supersedes `modUnitary_eq_of_orbit_inner`, whose hypotheses `⟨w, ·_t η⟩ = ⟨w, η⟩` are VACUOUS (they would force `V_t = id`; see the FRAMEWORK CAVEAT in AxiomAudit).  The correct orbit datum is the *U-vs-Δ comparison* `⟨w, V_t η⟩ = ⟨w, Δ^{it} η⟩` directly — what RvD's `g`-function constancy + the KMS-matching against `⟨h(z), Δ^{it}ξ⟩` actually produce (the KMS condition is applied to the pair `(η, Δ^{it}ξ)`, so `Δ^{it}` genuinely enters; it does NOT factor through `⟨w, η⟩`).  This hypothesis is satisfiable and non-vacuous. …

$$
(\forall \eta\in S.\mathrm{cl}, (V\,t)\,\eta \in S.\mathrm{cl}) \to (\forall \eta\in S.\mathrm{cl}, (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\eta \in S.\mathrm{cl}) \to (\forall \eta\in S.\mathrm{cl}, \forall (w : H), (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projik}{\mathrm{projIK}}\,S)\,w = 0 \to \langle {w},{(V\,t)\,\eta}\rangle = \langle {w},{(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,\eta}\rangle) \to \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t = V\,t
$$

*Proof.* By [`projK`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk), [`clm_eq_of_eqOn_K`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-clm-eq-of-eqon-k), [`mem_K_iff_projK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-mem-k-iff-projk), [`eq_of_mem_K_of_inner_perp_IK`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-eq-of-mem-k-of-inner-perp-ik). $\square$

<small>Used by [`oneParticleBW_of_comparison`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-oneparticlebw-of-comparison).</small>

<a id="d-qiqth-standardsubspacemodular-clm-eq-of-inner-self-eq"></a>
**Lemma 480** (`clm_eq_of_inner_self_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L494)</small>

**Polarization bridge: diagonal quadratic forms pin a bounded operator** (final step of the *diagonal-correlation* route to the `hUniq` discharge).  Over `ℂ`, two bounded operators with equal diagonal forms `⟨ξ, A ξ⟩ = ⟨ξ, B ξ⟩` for all `ξ` are equal — the polarization identity packaged as `inner_map_self_eq_zero` applied to `A − B`.  This converts the SCALAR correlation equality that strip-uniqueness delivers (`modCorrExt`, the `Δ`-side `⟨ξ, Δ^{iz} ξ⟩`, against a competitor's KMS extension `F`) into the operator identity `Δ^{it} = V_t`.  Unlike the discredited `corrC(Jξ)` constancy route, this bridge is non-vacuous: it is the standard, correct closeout once the diagonal correlations `⟨ξ, V_t ξ⟩ = ⟨ξ, Δ^{it} ξ⟩` are shown equal for every `ξ`.

$$
(\forall (\xi : H), \langle {A\,\xi},{\xi}\rangle = \langle {B\,\xi},{\xi}\rangle) \to A = B
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`borelFC_congr_ae`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-borelfc-congr-ae).</small>

<a id="d-qiqth-standardsubspacemodular-borelfc-congr-ae"></a>
**Lemma 481** (`borelFC_congr_ae`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L512)</small>

**The bounded Borel FC depends only on the a.e. class of its symbol**: `f(R) = g(R)` whenever `f =ᵐ g` against every spectral measure `μ^R_x`.  Via `rvdSpec_borelFC_diag` (`⟪x, f(R)x⟫ = ∫ f dμ^R_x`) the diagonals agree (`integral_congr_ae`), so `clm_eq_of_inner_self_eq` gives `f(R) = g(R)`.  This is the tool for `deviceOpC(−i/2) = √(2−R)`: the device character `d_{−i/2}` and `√(2−r)` differ ONLY on the spectral endpoints `{0,2}`, which carry no spectral mass once `R` and `2−R` are injective (`E({0,2}) = 0`).

$$
(\forall (x : H), f =[\href{/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure}{\mu^{R}}\,S\,x] g) \to \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\mathrm{hf}\,\mathrm{hC0f}\,\mathrm{hCf} = \href{/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc}{\Phi_{B}}\,(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc}{\mathrm{rvdRC}}\,S)\,\cdots \,\mathrm{hg}\,\mathrm{hC0g}\,\mathrm{hCg}
$$

*Proof.* By [`clm_eq_of_inner_self_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-clm-eq-of-inner-self-eq), [`rvdSpec_borelFC_diag`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspec-borelfc-diag). $\square$

<small>Used by [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq).</small>

<a id="d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq"></a>
**Lemma 482** (`deviceOpC_neg_half_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L534)</small>

**The bottom-edge device operator is `√(2−R)`**: `deviceOpC(−i/2) = rvdSqrtTwoSubR`.  The device character `d_{−i/2}(r) = √(2−r)` on `(0,2)` (`devChar_neg_half_I`) and the continuous symbol `√(2−·)` gives `√(2−R)` (`cfcCont_sqrtTwoSub_eq`); the two symbols differ ONLY at the spectral endpoints `{0,2}` (where the piecewise `modCharC = 1` swaps the value), and those are `μ^R_x`-null (`rvdSpecMeasure_endpoints`), so `borelFC_congr_ae` identifies the operators.  This completes the device/J algebra at the bottom edge: `J·deviceOpC(−i/2)ζ = J√(2−R)ζ = √R ζ = ξ` — RvD's `(2−R)^{1/2}ζ = Jξ`, the half-modular-shift `Δ^{1/2} = J` on `𝒦`.  The sole prior unproven step of the bottom-edge KMS reality (A) is thereby reduced to the KMS reflection (a2/a3).

$$
\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(-(i / 2))\,\cdots \,\cdots = \href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr}{\sqrt{2-R}}\,S
$$

*Proof.* By [`borelFC_congr_ae`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-borelfc-congr-ae), [`rvdSpecMeasure`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure), [`cfcCont_sqrtTwoSub_eq`](/browser/qiqth-modularrelativeentropy#d-qiqth-cfccont-sqrttwosub-eq), [`rvdSpecMeasure_endpoints`](/browser/qiqth-modularrelativeentropy#d-qiqth-rvdspecmeasure-endpoints), [`borelFC`](/browser/qiqth-spectral-spectraltheorem#d-qiqth-spectraltheorem-borelfc), [`rvdRC`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdrc), [`rvdRC_isSelfAdjoint`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-isselfadjoint), [`rvdRC_spectrum_mem_Icc`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-rvdrc-spectrum-mem-icc), [`cfcCont`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-cfccont), [`devChar`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar), [`devChar_neg_half_I`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-devchar-neg-half-i). $\square$

<small>Used by [`modConj_deviceOpC_neg_half`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half"></a>
**Lemma 483** (`modConj_deviceOpC_neg_half`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L562)</small>

**`J` applied to the bottom-edge device vector**: `J·deviceOpC(−i/2)ζ = √R(Jζ)`.  From `deviceOpC(−i/2) = √(2−R)` (`deviceOpC_neg_half_eq`) and the bottom-edge sqrt swap `J√(2−R) = √R·J` (`modConj_rvdSqrtTwoSubR_modConj` + `modConj_sq`).  For a `J`-fixed `ζ` this is `√Rζ = ξ`.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,((\href{/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc}{\mathrm{dev}_{\mathbb{C}}}\,S\,(-(i / 2))\,\cdots \,\cdots )\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta)
$$

*Proof.* By [`deviceOpC_neg_half_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-deviceopc-neg-half-eq), [`rvdSqrtTwoSubR`](/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrttwosubr), [`modConj_sq`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-sq), [`modConj_rvdSqrtTwoSubR_modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-rvdsqrttwosubr-modconj). $\square$

<small>Used by [`modConj_deviceVecF_bottom_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq"></a>
**Lemma 484** (`modConj_deviceVecF_bottom_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L575)</small>

**The bottom-edge g-vector**: `J·deviceVecF(t − i/2) = Δ^{it}·√R(Jζ)`.  Combines the device/J commute (`modConj_deviceVecF_bottom`) with `J·deviceOpC(−i/2)ζ = √R(Jζ)` (`modConj_deviceOpC_neg_half`).  This is the FIRST slot of the bottom-edge g-function `g(t − i/2) = ⟪J·deviceVecF(t−i/2), gaussSmearC(t−i/2)⟫` made explicit, now that `deviceOpC(−i/2) = √(2−R)` is proven.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)) = (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta))
$$

*Proof.* By [`modConj_deviceOpC_neg_half`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-deviceopc-neg-half), [`deviceOpC`](/browser/qiqth-modularrelativeentropy#d-qiqth-deviceopc), [`modConj_deviceVecF_bottom`](/browser/qiqth-modularrelativeentropy#d-qiqth-modconj-devicevecf-bottom). $\square$

<small>Used by [`modConj_deviceVecF_bottom_eq_fixed`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-fixed).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-fixed"></a>
**Lemma 485** (`modConj_deviceVecF_bottom_eq_fixed`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L584)</small>

**The bottom-edge g-vector for a `J`-fixed `ζ`**: `J·deviceVecF(t − i/2) = Δ^{it}·√Rζ = Δ^{it}ξ` (`ξ = √Rζ`).  This is RvD's `(2−R)^{1/2}ζ = Jξ` at the operator-vector level: the bottom-edge device vector, conjugated by `J`, is exactly the modular flow `Δ^{it}` applied to `ξ = √Rζ`.  The reality of `⟪Δ^{it}ξ, gaussSmearC(t−i/2)⟫` is then the bottom-edge KMS input `h1`.

$$
(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,\zeta = \zeta \to \forall (t : \mathbb{R}), (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)) = (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)
$$

*Proof.* By [`modConj_deviceVecF_bottom_eq`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq). $\square$

<small>Used by [`modConj_deviceVecF_bottom_eq_of_mem_K`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k"></a>
**Lemma 486** (`modConj_deviceVecF_bottom_eq_of_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L594)</small>

**The bottom-edge g-vector under the `gConstancy_eta_of_bottom` hypothesis** `√Rζ ∈ 𝒦`: `J·deviceVecF(t − i/2) = Δ^{it}·√Rζ = Δ^{it}ξ`.  The condition `√Rζ ∈ 𝒦` makes `ζ` `J`-fixed (`modConj_fixed_of_sqrtR_mem_K`, the bounded Tomita relation `Jξ = Δ^{1/2}ξ` on `𝒦`), so the general bottom-edge value `Δ^{it}√R(Jζ)` collapses to `Δ^{it}√Rζ`.  This resolves the `√Rζ∈𝒦`-vs-`Jζ=ζ` condition gap, in exactly the form the bottom-edge KMS reality `h1` consumes.

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (t : \mathbb{R}), (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)) = (\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)
$$

*Proof.* By [`modConj_deviceVecF_bottom_eq_fixed`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-fixed), [`modConj_fixed_of_sqrtR_mem_K`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj-fixed-of-sqrtr-mem-k). $\square$

<small>Used by [`gFunction_bottom_eq_of_mem_K`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k).</small>

<a id="d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k"></a>
**Lemma 487** (`gFunction_bottom_eq_of_mem_K`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L605)</small>

**The bottom-edge g-function value made fully explicit** (for `√Rζ ∈ 𝒦`): `g(t − i/2) = ⟪J·deviceVecF(t−i/2), w⟫ = ⟪Δ^{it}·√Rζ, w⟫ = ⟪Δ^{it}ξ, w⟫`.  With `w = gaussSmearC(t−i/2)`, the bottom-edge KMS reality `h1` becomes precisely `Im⟪Δ^{it}ξ, gaussSmearC(t−i/2)⟫ = 0` (`ξ = √Rζ ∈ 𝒦`) — the clean target of the remaining a2/a3 KMS reflection (RvD's reality on the lower edge, via `Δ^{1/2} = J` and the half-strip Phragmén–Lindelöf transfer from the proven mid-line KMS function `stripKMSrvd_real_midline`).

$$
(\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (w : H) (t : \mathbb{R}), ((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)))\,w = \langle {(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)},{w}\rangle
$$

*Proof.* By [`modConj_deviceVecF_bottom_eq_of_mem_K`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-modconj-devicevecf-bottom-eq-of-mem-k), [`modConj`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconj), [`modConjBilin_apply`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin-apply). $\square$

<small>Used by [`gFunction_bottom_real_of_kms_match`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match).</small>

<a id="d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match"></a>
**Lemma 488** (`gFunction_bottom_real_of_kms_match`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L686)</small>

**The g-function bottom-edge reality from the KMS f-transfer (RvD Theorem 3.8's actual route).** The bottom-edge g-value equals the auxiliary orbit correlation with the device FROZEN at its bottom-edge value `ξ_t = Δ^{it}ξ` (`ξ = √Rζ ∈ 𝒦`): `g(t−i/2) = ⟪ξ_t, gaussSmearC(t−i/2)⟫ = corrC ξ_t V n η (t−i/2)`. `corrC ξ_t` is entire (`differentiable_corrC`) and bounded on the half-strip (`corrC_bdd_halfStrip`).  RvD's argument: the K.M.S. condition applied to the pair `(η, Δ^{it}ξ)` yields a bounded-holomorphic `f` matching this auxiliary `corrC ξ_t` on the real axis with `f(t−i/2)` REAL. …

$$
0 < n \to \forall (\eta : H) \{\zeta : H\}, (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (t : \mathbb{R}), (\mathrm{Continuous}\,\lambda s \mapsto (V\,s)\,\eta) \to (\forall (s : \mathbb{R}), \|(V\,s)\,\eta\| \le \|\eta\|) \to \forall \{f : \mathbb{C} \to \mathbb{C}\} \{M : \mathbb{R}\}, \mathrm{DiffContOnCl}\,\mathbb{C}\,f\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}} \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstrip}{S_{1/2}}, \|f\,z\| \le M) \to (\forall (s : \mathbb{R}), f\,s = \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-corrc}{\mathrm{corrC}}\,((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta))\,V\,n\,\eta\,s) \to (f\,(t - i / 2)).\mathrm{im} = 0 \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,(t - i / 2))).\mathrm{im} = 0
$$

*Proof.* By [`corrC_bdd_halfStrip`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-corrc-bdd-halfstrip), [`gFunction_bottom_eq_of_mem_K`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-eq-of-mem-k), [`differentiable_corrC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-differentiable-corrc), [`eqOn_of_im_zero_edge_halfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-halfstrip). $\square$

<small>Used by [`gFunction_bottom_real_of_faithful_kms`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms).</small>

<a id="d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms"></a>
**Lemma 489** (`gFunction_bottom_real_of_faithful_kms`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/KMSCorrelation.lean#L734)</small>

**The bottom-edge KMS reality `h1` from the FAITHFUL-convention half-strip witness.**  RvD Definition 3.4 (read from source, pp.194-195) states the KMS function with the orbit in the LINEAR inner-product slot: `f(t) = ⟨U_tξ, η⟩` with RvD's `⟨·,·⟩` *linear-first* (forced — `⟨h(z),Δ^{it}ξ⟩` must be entire), i.e. in Mathlib `f(t) = inner ℂ η (V_t ξ)`.  For the pair `(ξ' = gaussSmear, η' = ξ_t = Δ^{it}ξ)` this is `f(s) = ⟪ξ_t, V_s·gaussSmear⟫ = corrC ξ_t V n η s` (the real-axis value of the bottom-edge auxiliary `gFunction_bottom_eq_of_mem_K` + `gaussSmearC_ofReal`). …

$$
0 < n \to \forall (\eta : H) \{\zeta : H\}, (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-projk}{\mathrm{projK}}\,S)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta) = (\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta \to \forall (t : \mathbb{R}), (\mathrm{Continuous}\,\lambda s \mapsto (V\,s)\,\eta) \to (\forall (s : \mathbb{R}), \|(V\,s)\,\eta\| \le \|\eta\|) \to (\forall (s u : \mathbb{R}), (V\,s)\,((V\,u)\,\eta) = (V\,(s + u))\,\eta) \to \forall \{f : \mathbb{C} \to \mathbb{C}\} \{M : \mathbb{R}\}, \mathrm{DiffContOnCl}\,\mathbb{C}\,f\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}} \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstrip}{S_{1/2}}, \|f\,z\| \le M) \to (\forall (s : \mathbb{R}), f\,s = \langle {(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,S\,t)\,((\href{/browser/qiqth-standardsubspacemodular#d-qiqth-standardsubspacemodular-rvdsqrtr}{R^{1/2}}\,S)\,\zeta)},{(V\,s)\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmear}{g}\,V\,n\,\eta)}\rangle) \to (f\,(t - i / 2)).\mathrm{im} = 0 \to (((\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modconjbilin}{J}\,S)\,(\href{/browser/qiqth-modularrelativeentropy#d-qiqth-devicevecf}{\mathrm{dev}}\,S\,\zeta\,(t - i / 2)))\,(\href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc}{g}\,V\,n\,\eta\,(t - i / 2))).\mathrm{im} = 0
$$

*Proof.* By [`gFunction_bottom_real_of_kms_match`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [`gaussSmearC_ofReal`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-gausssmearc-ofreal), [`corrC`](/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-corrc). $\square$

<small>Used by [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd).</small>

---
<small>[← all sections](/browser) · [← KGStressConservation](/browser/qiqth-kgstressconservation) · [LocalizedMode →](/browser/qiqth-localizedmode) </small>