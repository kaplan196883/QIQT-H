---
layout: ../../layouts/Deep.astro
title: QIQTH.StripUniqueness
eyebrow: StripUniqueness · section of the QIQT-H book
description: QIQTH.StripUniqueness — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← StandardSubspaceModularFlow](/browser/qiqth-standardsubspacemodularflow) · [ValueSelection →](/browser/qiqth-valueselection) </small>

<small>StripUniqueness · entries 979–992 of 1000</small>

<a id="d-qiqth-stripuniqueness-kmsstrip"></a>
**Definition 979** (`kmsStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L30)</small>

The (closed) **KMS strip** `{0 ≤ Im z ≤ 1}` — the inverse temperature is normalised to `β = 1`.

$$
S \;:=\; \mathrm{im} ^{-1}{}' \mathrm{Icc}\,0\,1
$$

<small>Used by [`im_zero_on_strip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-im-zero-on-strip), [`eqConst_of_im_zero_strip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqconst-of-im-zero-strip).</small>

<a id="d-qiqth-stripuniqueness-kmsstripopen"></a>
**Definition 980** (`kmsStripOpen`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L33)</small>

The **open** KMS strip `{0 < Im z < 1}`.

$$
S^{\circ} \;:=\; \mathrm{im} ^{-1}{}' \mathrm{Ioo}\,0\,1
$$

<small>Used by [`im_zero_on_strip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-im-zero-on-strip), [`eqConst_of_im_zero_strip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqconst-of-im-zero-strip), [`eqConst_of_im_zero_halfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqconst-of-im-zero-halfstrip).</small>

<a id="d-qiqth-stripuniqueness-im-zero-on-strip"></a>
**Lemma 981** (`im_zero_on_strip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L95)</small>

**Max-modulus on the strip: vanishing imaginary part propagates from the edges to the interior.** If `g` is bounded-holomorphic on the KMS strip (`DiffContOnCl` + a uniform bound) and its **imaginary part vanishes on both boundary edges** (`Im g = 0` on `Im z = 0` and `Im z = 1`), then `Im g = 0` on the whole closed strip.  Proof: `|exp(±i·g)| = exp(∓Im g) = 1` on the edges, so by `PhragmenLindelof`'s horizontal-strip max-modulus principle `|exp(i·g)| ≤ 1` and `|exp(−i·g)| ≤ 1` throughout, forcing `Im g = 0`.  This is the reflection-free substitute for RvD's "real on both edges ⇒ constant" step (the crux of the KMS-uniqueness Theorem 3.8).

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,g\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmsstripopen}{S^{\circ}} \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmsstripopen}{S^{\circ}}, \|g\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (g\,z).\mathrm{im} = 0) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 1 \to (g\,z).\mathrm{im} = 0) \to \forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmsstrip}{S}, (g\,z).\mathrm{im} = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`eqConst_of_im_zero_strip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqconst-of-im-zero-strip).</small>

<a id="d-qiqth-stripuniqueness-eqconst-of-im-zero-strip"></a>
**Lemma 982** (`eqConst_of_im_zero_strip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L147)</small>

**Bounded-holomorphic with imaginary part zero on both strip edges ⟹ constant.**  Combining the max-modulus propagation `im_zero_on_strip` (`Im g = 0` throughout) with the open-mapping corollary `AnalyticOnNhd.eq_const_of_re_eq_const` (a holomorphic function with constant real part is constant): since `Re(i·g) = −Im g = 0` on the (open, connected) strip, `i·g` is constant, hence `g` is constant. This is RvD Theorem 3.8's "real on both edges ⇒ constant" conclusion, obtained reflection-free.

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,g\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmsstripopen}{S^{\circ}} \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmsstripopen}{S^{\circ}}, \|g\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (g\,z).\mathrm{im} = 0) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 1 \to (g\,z).\mathrm{im} = 0) \to \exists c, \forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmsstripopen}{S^{\circ}}, g\,z = c
$$

*Proof.* By [`kmsStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmsstrip), [`im_zero_on_strip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-im-zero-on-strip). $\square$

<small>Used by [`eqConst_of_im_zero_halfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqconst-of-im-zero-halfstrip).</small>

<a id="d-qiqth-stripuniqueness-kmshalfstrip"></a>
**Definition 983** (`kmsHalfStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L250)</small>

The (closed) **half KMS strip** `{−1/2 ≤ Im z ≤ 0}` — the strip RvD Theorem 3.8 / Prop 3.5 actually use: the `g`-function lives here, with the lower edge `Im = −1/2` (the half-shift `Δ^{1/2} = J`).

$$
S_{1/2} \;:=\; \mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-(1/2))\,0
$$

<small>Used by [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`corrC_bdd_halfStrip`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-corrc-bdd-halfstrip), [`gFunction_bottom_real_of_kms_match`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [`gFunction_bottom_real_of_faithful_kms`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [`eqZero_of_im_zero_edge_halfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-halfstrip), [`eqOn_of_im_zero_edge_halfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-halfstrip).</small>

<a id="d-qiqth-stripuniqueness-kmshalfstripopen"></a>
**Definition 984** (`kmsHalfStripOpen`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L254)</small>

The **open** half KMS strip `{−1/2 < Im z < 0}`.

$$
S^{\circ}_{1/2} \;:=\; \mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-(1/2))\,0
$$

<small>Used by [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`gFunction_eq_zero_const`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const), [`gFunction_bottom_real_of_kms_match`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match), [`gFunction_bottom_real_of_faithful_kms`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-faithful-kms), [`eqZero_of_im_zero_edge_halfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-halfstrip), [`eqOn_of_im_zero_edge_halfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-halfstrip), [`eqConst_of_im_zero_halfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqconst-of-im-zero-halfstrip).</small>

<a id="d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-halfstrip"></a>
**Lemma 985** (`eqZero_of_im_zero_edge_halfStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L258)</small>

**One-edge boundary uniqueness on the HALF strip** `{−1/2 ≤ Im z ≤ 0}`: a function bounded-holomorphic there and vanishing on the *top* edge `Im z = 0` vanishes on the whole closed half-strip.  Same Hadamard three-lines route as `eqZero_of_im_zero_edge`, rotated to the vertical strip `re⁻¹'[−1/2, 0]` with the zero edge at `u = 0` (`‖f‖ ≤ M^{1−θ}·0^θ = 0` interior), then `Set.EqOn.of_subset_closure`.  This is the CORRECT-strip analytic core of RvD Theorem 3.8 (the full-strip `corrC` framework mis-modeled it).

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,f\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}} \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstrip}{S_{1/2}}, \|f\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to f\,z = 0) \to \forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstrip}{S_{1/2}}, f\,z = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`eqOn_of_im_zero_edge_halfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-halfstrip).</small>

<a id="d-qiqth-stripuniqueness-eqon-of-im-zero-edge-halfstrip"></a>
**Lemma 986** (`eqOn_of_im_zero_edge_halfStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L319)</small>

**One-edge determination on the HALF strip** (RvD Prop 3.5 / Theorem 3.8 setting): two bounded-holomorphic functions on `{−1/2 ≤ Im z ≤ 0}` agreeing on the top edge `Im z = 0` agree on the whole closed half-strip. Apply `eqZero_of_im_zero_edge_halfStrip` to `F − G`.  This is the correct-strip analog of `eqOn_of_im_zero_edge`: the matching step where the entire-orbit correlation `⟨h(z), w⟩` and the KMS function (which share their `Im = 0` boundary values `⟨U_t ξ, η⟩`) coincide on the half-strip, so the KMS function's lower-edge `Im = −1/2` reality transfers to the orbit correlation.

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,F\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}} \to \mathrm{DiffContOnCl}\,\mathbb{C}\,G\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}} \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstrip}{S_{1/2}}, \|F\,z\| \le M) \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstrip}{S_{1/2}}, \|G\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to F\,z = G\,z) \to \mathrm{EqOn}\,F\,G\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstrip}{S_{1/2}}
$$

*Proof.* By [`eqZero_of_im_zero_edge_halfStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-halfstrip). $\square$

<small>Used by [`gFunction_bottom_real_of_kms_match`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-bottom-real-of-kms-match).</small>

<a id="d-qiqth-stripuniqueness-eqconst-of-im-zero-halfstrip"></a>
**Lemma 987** (`eqConst_of_im_zero_halfStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L333)</small>

**Real on both edges ⟹ constant on the HALF-strip** `{−1/2 < Im z < 0}`.  Adapts the unit-strip two-edge Phragmén–Lindelöf constancy (`eqConst_of_im_zero_strip`, edges `Im = 0`, `Im = 1`) via the affine map `φ(w) = −w/2`, which maps `{0 < Im w < 1}` onto `{−1/2 < Im z < 0}` (top edge `Im w = 0 ↦ Im z = 0`, bottom edge `Im w = 1 ↦ Im z = −1/2`).  `G(w) = g(−w/2)` is bounded-holomorphic on the unit strip and real on both its edges, hence constant; pulling back gives `g` constant on the half-strip.  This is the constancy the RvD Theorem 3.8 g-function (real on `Im = 0` and `Im = −1/2`) consumes.

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,g\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}} \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}}, \|g\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to (g\,z).\mathrm{im} = 0) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = -(1/2) \to (g\,z).\mathrm{im} = 0) \to \exists c, \forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmshalfstripopen}{S^{\circ}_{1/2}}, g\,z = c
$$

*Proof.* By [`kmsStripOpen`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-kmsstripopen), [`eqConst_of_im_zero_strip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqconst-of-im-zero-strip). $\square$

<small>Used by [`gFunction_eq_zero_const`](/browser/qiqth-kmscorrelation#d-qiqth-standardsubspacemodular-gfunction-eq-zero-const).</small>

<a id="d-qiqth-stripuniqueness-negstrip"></a>
**Definition 988** (`negStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L368)</small>

The **unit KMS strip** `{−1 ≤ Im z ≤ 0}` and its interior — the strip of RvD Definition 3.4 (the full-width KMS condition, before Proposition 3.5 folds it to the half-strip).

$$
S^{-} \;:=\; \mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0
$$

<small>Used by [`stripKMSrvd_real_midline`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd-real-midline), [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd), [`eqZero_of_im_zero_edge_negStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-negstrip), [`eqOn_of_im_zero_edge_negStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-negstrip), [`real_on_midline_of_conj_flip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-real-on-midline-of-conj-flip).</small>

<a id="d-qiqth-stripuniqueness-negstripopen"></a>
**Definition 989** (`negStripOpen`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L371)</small>

$$
S^{-} \;:=\; \mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0
$$

<small>Used by [`eqZero_of_im_zero_edge_negStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-negstrip), [`eqOn_of_im_zero_edge_negStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-negstrip), [`real_on_midline_of_conj_flip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-real-on-midline-of-conj-flip).</small>

<a id="d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-negstrip"></a>
**Lemma 990** (`eqZero_of_im_zero_edge_negStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L374)</small>

**One-edge boundary uniqueness on the UNIT strip** `{−1 ≤ Im z ≤ 0}`: a function bounded-holomorphic there and vanishing on the top edge `Im z = 0` vanishes on the whole closed strip.  Same Hadamard three-lines route as `eqZero_of_im_zero_edge_halfStrip`, on `re⁻¹'[−1, 0]`.  This is the uniqueness that powers RvD Proposition 3.5's reflection argument (the full-width KMS strip of Definition 3.4).

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,f\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstripopen}{S^{-}} \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstrip}{S^{-}}, \|f\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to f\,z = 0) \to \forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstrip}{S^{-}}, f\,z = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`eqOn_of_im_zero_edge_negStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-negstrip).</small>

<a id="d-qiqth-stripuniqueness-eqon-of-im-zero-edge-negstrip"></a>
**Lemma 991** (`eqOn_of_im_zero_edge_negStrip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L431)</small>

**One-edge determination on the UNIT strip** `{−1 ≤ Im z ≤ 0}`: two bounded-holomorphic functions agreeing on the top edge `Im z = 0` agree on the whole closed strip.  Apply `eqZero_of_im_zero_edge_negStrip` to `F − G`.  The full-width companion of `eqOn_of_im_zero_edge_halfStrip`, the uniqueness RvD Proposition 3.5 invokes for the KMS extension on `{−1 ≤ Im ≤ 0}`.

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,F\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstripopen}{S^{-}} \to \mathrm{DiffContOnCl}\,\mathbb{C}\,G\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstripopen}{S^{-}} \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstrip}{S^{-}}, \|F\,z\| \le M) \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstrip}{S^{-}}, \|G\,z\| \le M) \to (\forall (z : \mathbb{C}), z.\mathrm{im} = 0 \to F\,z = G\,z) \to \mathrm{EqOn}\,F\,G\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstrip}{S^{-}}
$$

*Proof.* By [`eqZero_of_im_zero_edge_negStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqzero-of-im-zero-edge-negstrip). $\square$

<small>Used by [`real_on_midline_of_conj_flip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-real-on-midline-of-conj-flip).</small>

<a id="d-qiqth-stripuniqueness-real-on-midline-of-conj-flip"></a>
**Lemma 992** (`real_on_midline_of_conj_flip`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/StripUniqueness.lean#L443)</small>

**RvD Proposition 3.5 — reality on the mid-line.**  A bounded-holomorphic `f` on the unit strip `{−1 < Im z < 0}` (`DiffContOnCl`), satisfying the *conjugate-flip* boundary relation `f(t − i) = conj(f(t))` on the real axis, is **real on the mid-line** `Im z = −1/2`: `Im f(t − i/2) = 0` for all real `t`.  This is RvD's reflection argument: the reflected function `g(z) = conj(f(conj z − i))` is holomorphic (`DifferentiableAt.conj_conj`), bounded, and agrees with `f` on the edge `Im = 0` (`g(t) = conj(f(t − i)) = conj(conj(f(t))) = f(t)` by the flip), so `g = f` on the strip (`eqOn_of_im_zero_edge_negStrip`); evaluating at `t − i/2` gives `f(t − i/2) = conj(f(t − i/2))`. …

$$
\mathrm{DiffContOnCl}\,\mathbb{C}\,f\,\href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstripopen}{S^{-}} \to (\forall z\in \href{/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-negstrip}{S^{-}}, \|f\,z\| \le M) \to (\forall (t : \mathbb{R}), f\,(t - i) = (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,t)) \to \forall (t : \mathbb{R}), (f\,(t - i / 2)).\mathrm{im} = 0
$$

*Proof.* By [`eqOn_of_im_zero_edge_negStrip`](/browser/qiqth-stripuniqueness#d-qiqth-stripuniqueness-eqon-of-im-zero-edge-negstrip). $\square$

<small>Used by [`stripKMSrvd_real_midline`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-stripkmsrvd-real-midline), [`h1_of_stripKMSrvd`](/browser/qiqth-fock-oneparticlebw#d-qiqth-fock-oneparticlebw-h1-of-stripkmsrvd).</small>

---
<small>[← all sections](/browser) · [← StandardSubspaceModularFlow](/browser/qiqth-standardsubspacemodularflow) · [ValueSelection →](/browser/qiqth-valueselection) </small>