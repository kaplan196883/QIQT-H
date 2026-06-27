---
layout: ../../layouts/Deep.astro
title: QIQTH.Fock.CyclicWitness
eyebrow: Fock · section of the QIQT-H book
description: QIQTH.Fock.CyclicWitness — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← BoostKMS](/browser/qiqth-fock-boostkms) · [FreeFieldHFlux →](/browser/qiqth-fock-freefieldhflux) </small>

<small>Fock · entries 209–230 of 1000</small>

<a id="d-qiqth-fock-cyclicwitness-bump1w"></a>
**Definition 209** (`bump1W`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L218)</small>

A width-`R` 1D bump (`rIn = R/2`, `rOut = R`).

$$
\mathrm{bump1W}\,R\,\mathrm{hR}\,c \;:=\; \{\mathrm{rIn} :=R / 2 , \mathrm{rOut} :=R , \mathrm{rIn\_pos} :=\cdots , \mathrm{rIn\_lt\_rOut} :=\cdots \}
$$

<small>Used by [`bump1W_rOut`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w-rout), [`bump1W_rIn`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w-rin), [`bumpRealW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw), [`bumpRealW_contDiff`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw-contdiff), [`bumpCW_contDiff`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw-contdiff), [`bumpRealW_support_subset`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw-support-subset), [`minkowskiFourier_bumpCW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw), [`Krep_bumpCW_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero), and 3 more.</small>

<a id="d-qiqth-fock-cyclicwitness-bump1w-rout"></a>
**Lemma 210** (`bump1W_rOut`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L222)</small>

$$
(\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,c).\mathrm{rOut} = R
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`bumpRealW_support_subset`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw-support-subset), [`bump1W_fourier_ne_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w-fourier-ne-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-bump1w-rin"></a>
**Lemma 211** (`bump1W_rIn`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L224)</small>

$$
(\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,c).\mathrm{rIn} = R / 2
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`bump1W_fourier_ne_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w-fourier-ne-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-bumprealw"></a>
**Definition 212** (`bumpRealW`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L226)</small>

The width-`R` 2D product bump on `V = Fin 2 → ℝ`.

$$
\mathrm{bump}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX}\,x \;:=\; (\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cT})\,(x\,0) \cdot (\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cX})\,(x\,1)
$$

<small>Used by [`bumpCW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw), [`bumpRealW_contDiff`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw-contdiff), [`bumpRealW_support_subset`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw-support-subset), [`bumpCW_hasCompactSupport`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw-hascompactsupport).</small>

<a id="d-qiqth-fock-cyclicwitness-bumpcw"></a>
**Definition 213** (`bumpCW`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L230)</small>

$$
\mathrm{bumpCW}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX}\,x \;:=\; (\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw}{\mathrm{bump}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX}\,x)
$$

<small>Used by [`bumpCW_contDiff`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw-contdiff), [`bumpCW_continuous`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw-continuous), [`bumpCW_hasCompactSupport`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw-hascompactsupport), [`bumpNiceTestW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpnicetestw), [`niceWedgeCyclic_bumpW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw), [`minkowskiFourier_bumpCW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw), [`Krep_bumpCW_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero), [`Krep_bumpCW_ne_zero_of`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of).</small>

<a id="d-qiqth-fock-cyclicwitness-bumprealw-contdiff"></a>
**Lemma 214** (`bumpRealW_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L233)</small>

$$
({\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw}{\mathrm{bump}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX}})\in C^{\infty}
$$

*Proof.* By [`bump1W`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w). $\square$

<small>Used by [`bumpCW_contDiff`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw-contdiff).</small>

<a id="d-qiqth-fock-cyclicwitness-bumpcw-contdiff"></a>
**Lemma 215** (`bumpCW_contDiff`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L241)</small>

$$
({\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX}})\in C^{\infty}
$$

*Proof.* By [`bump1W`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w), [`bumpRealW_contDiff`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw-contdiff). $\square$

<small>Used by [`bumpCW_continuous`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw-continuous), [`niceWedgeCyclic_bumpW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw).</small>

<a id="d-qiqth-fock-cyclicwitness-bumpcw-continuous"></a>
**Lemma 216** (`bumpCW_continuous`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L244)</small>

$$
\mathrm{Continuous}\,(\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX})
$$

*Proof.* By [`bumpCW_contDiff`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw-contdiff). $\square$

<small>Used by [`Krep_bumpCW_ne_zero_of`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of).</small>

<a id="d-qiqth-fock-cyclicwitness-bumprealw-support-subset"></a>
**Lemma 217** (`bumpRealW_support_subset`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L251)</small>

$$
\mathrm{support}\,(\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw}{\mathrm{bump}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX}) \subseteq \{x||x\,0 - \mathrm{cT}| \le R \wedge |x\,1 - \mathrm{cX}| \le R\}
$$

*Proof.* By [`bump1W`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w), [`bump1W_rOut`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w-rout). $\square$

<small>Used by [`bumpCW_hasCompactSupport`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw-hascompactsupport).</small>

<a id="d-qiqth-fock-cyclicwitness-bumpcw-hascompactsupport"></a>
**Lemma 218** (`bumpCW_hasCompactSupport`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L264)</small>

$$
\mathrm{HasCompactSupport}\,(\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX})
$$

*Proof.* By [`bumpRealW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw), [`bumpRealW_support_subset`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumprealw-support-subset). $\square$

<small>Used by [`niceWedgeCyclic_bumpW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw), [`Krep_bumpCW_ne_zero_of`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of).</small>

<a id="d-qiqth-fock-cyclicwitness-bumpnicetestw"></a>
**Definition 219** (`bumpNiceTestW`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L287)</small>

A width-`R` wedge-supported nice generator centred at `(0, cX)` with `2R < cX` (margin `δ = cX − 2R`).

$$
\mathrm{bumpNiceTestW}\,m\,R\,\mathrm{cX}\,\mathrm{hR}\,\mathrm{hm}\,\mathrm{hcX} \;:=\; \{f :=\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,0\,\mathrm{cX} , \mathrm{cont} :=\cdots , \mathrm{cpt} :=\cdots , \delta :=\mathrm{cX} - 2 \cdot R , h\delta :=\cdots , \mathrm{margin} :=\cdots , \mathrm{real} :=\cdots , \mathrm{memLp} :=\cdots \}
$$

<small>Used by [`niceWedgeCyclic_bumpW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw).</small>

<a id="d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw"></a>
**Lemma 220** (`niceWedgeCyclic_bumpW`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L305)</small>

`NiceWedgeCyclic` from the width-`R` bump generator, modulo its amplitude being nonzero.

$$
m \ne 0 \to 2 \cdot R < \mathrm{cX} \to \neg \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\cdots .\mathrm{toSchwartzMap}\,\cdots ) =[\mathrm{volume}] 0 \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgecyclic}{\mathrm{NiceWedgeCyclic}}\,m
$$

*Proof.* By [`niceWedgeCyclic_of_fourier_ne_zero`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgecyclic-of-fourier-ne-zero), [`bumpNiceTestW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpnicetestw), [`fourierL2_Krep_ne_zero`](/browser/qiqth-fock-wienerl2#d-qiqth-fock-wienerl2-fourierl2-krep-ne-zero). $\square$

<small>Used by [`niceWedgeCyclic_of_bumpW_fourier_ne_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-of-bumpw-fourier-ne-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw"></a>
**Lemma 221** (`minkowskiFourier_bumpCW`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L314)</small>

The width-`R` amplitude factorizes (Fubini), mirroring `minkowskiFourier_bumpC`.

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier}{\mathcal{F}}\,(\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX})\,p = (\int (y : \mathbb{R}), \exp\,(-i \cdot (p\,0 \cdot y)) \cdot ((\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cT})\,y)) \cdot \int (y : \mathbb{R}), \exp\,(i \cdot (p\,1 \cdot y)) \cdot ((\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cX})\,y)
$$

*Proof.* By [`minkowskiDot`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot). $\square$

<small>Used by [`Krep_bumpCW_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-krep-bumpcw-zero"></a>
**Lemma 222** (`Krep_bumpCW_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L337)</small>

The width-`R` bump amplitude at `θ = 0`, factored.

$$
\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX})\,0 = 1 / \sqrt 2 \cdot ((\int (y : \mathbb{R}), \exp\,(-i \cdot (m \cdot y)) \cdot ((\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cT})\,y)) \cdot \int (y : \mathbb{R}), ((\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cX})\,y))
$$

*Proof.* By [`minkowskiFourier_bumpCW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-minkowskifourier-bumpcw), [`massShell`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell), [`minkowskiFourier`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier). $\square$

<small>Used by [`Krep_bumpCW_ne_zero_of`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of).</small>

<a id="d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of"></a>
**Lemma 223** (`Krep_bumpCW_ne_zero_of`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L347)</small>

The width-`R` amplitude is `≢ 0` as soon as the 1D integral `∫ e^{−imy}·bump1W R cT(y) dy ≠ 0`.

$$
\int (y : \mathbb{R}), \exp\,(-i \cdot (m \cdot y)) \cdot ((\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,\mathrm{cT})\,y) \ne 0 \to \neg \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{\mathrm{Krep}}\,m\,(\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw}{\mathrm{bumpCW}}\,R\,\mathrm{hR}\,\mathrm{cT}\,\mathrm{cX}) =[\mathrm{volume}] 0
$$

*Proof.* By [`bumpCW_continuous`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw-continuous), [`bumpCW_hasCompactSupport`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bumpcw-hascompactsupport), [`Krep_bumpCW_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-zero), [`V`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-v), [`Krep_continuous`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep-continuous). $\square$

<small>Used by [`niceWedgeCyclic_of_bumpW_fourier_ne_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-of-bumpw-fourier-ne-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-fourier-re-eq"></a>
**Lemma 224** (`fourier_re_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L373)</small>

The real part of the 1D Fourier integrand for an arbitrary real weight `g`: `Re(e^{−imy}·g(y)) = cos(my)·g(y)`.

$$
(\exp\,(-i \cdot (m \cdot y)) \cdot (g\,y)).\mathrm{re} = \cos\,(m \cdot y) \cdot g\,y
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`bump1W_fourier_ne_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w-fourier-ne-zero).</small>

<a id="d-qiqth-fock-cyclicwitness-bump1w-fourier-ne-zero"></a>
**Lemma 225** (`bump1W_fourier_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L381)</small>

**The width-`R` 1D bump Fourier integral is nonzero whenever `m·R < π/2`**: its real part `∫ cos(my)·bump1W R 0(y) dy > 0`, since `cos(my) > 0` on the support `|y| < R` (as `|my| ≤ mR < π/2`).

$$
0 < m \to \forall (\mathrm{hR} : 0 < R), m \cdot R < \pi / 2 \to \int (y : \mathbb{R}), \exp\,(-i \cdot (m \cdot y)) \cdot ((\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,0)\,y) \ne 0
$$

*Proof.* By [`bump1W_rOut`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w-rout), [`bump1W_rIn`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w-rin), [`fourier_re_eq`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-fourier-re-eq). $\square$

<small>Used by [`niceWedgeCyclic_pos_mass`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-pos-mass).</small>

<a id="d-qiqth-fock-cyclicwitness-nicewedgecyclic-of-bumpw-fourier-ne-zero"></a>
**Lemma 226** (`niceWedgeCyclic_of_bumpW_fourier_ne_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L444)</small>

**`NiceWedgeCyclic` from a width-`R` bump whose 1D amplitude is nonzero.**

$$
m \ne 0 \to 2 \cdot R < \mathrm{cX} \to \int (y : \mathbb{R}), \exp\,(-i \cdot (m \cdot y)) \cdot ((\href{/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w}{\mathrm{bump1W}}\,R\,\mathrm{hR}\,0)\,y) \ne 0 \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgecyclic}{\mathrm{NiceWedgeCyclic}}\,m
$$

*Proof.* By [`niceWedgeCyclic_bumpW`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-bumpw), [`Krep_bumpCW_ne_zero_of`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-krep-bumpcw-ne-zero-of). $\square$

<small>Used by [`niceWedgeCyclic_pos_mass`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-pos-mass).</small>

<a id="d-qiqth-fock-cyclicwitness-nicewedgecyclic-pos-mass"></a>
**Lemma 227** (`niceWedgeCyclic_pos_mass`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L451)</small>

** THE CYCLIC REEH–SCHLIEDER INPUT, UNCONDITIONALLY DISCHARGED FOR ALL `m > 0`, axiom-free.** `NiceWedgeCyclic m` holds with no hypotheses for *every* positive mass.  Take the width-`R` wedge bump with `R = π/(4m)`, centred at `(0, 2R+1)`: then `m·R = π/4 < π/2`, so `cos(m y) > 0` on its whole support and the amplitude's real part `∫ cos(m y)·bump1W R(y) dy > 0` (`bump1W_fourier_ne_zero`); the complete Wiener–Tauberian machinery does the rest.  The free-field one-particle Bisognano–Wichmann's cyclic Reeh–Schlieder input is now a *theorem*, not a hypothesis, for the full physical mass range `m > 0` — every step (Wiener theorem, FT-holomorphy, L²↔L¹ agreement, witness, amplitude) machine-checked and axiom-free. …

$$
0 < m \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgecyclic}{\mathrm{NiceWedgeCyclic}}\,m
$$

*Proof.* By [`bump1W_fourier_ne_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-bump1w-fourier-ne-zero), [`niceWedgeCyclic_of_bumpW_fourier_ne_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgecyclic-of-bumpw-fourier-ne-zero). $\square$

<small>Used by [`oneParticleBW_niceWedge_unconditional`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [`freeField_modularEnergy_eq_boostCharge`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [`freeField_oneParticle_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-oneparticle-hflux), [`freeField_component_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-component-hflux), [`freeField_kd_conclusion`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [`qiqt_gr_freefield`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-fock-cyclicwitness-strip-eqzero-of-top-edge-zero"></a>
**Lemma 228** (`strip_eqZero_of_top_edge_zero`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L468)</small>

**Strip boundary-uniqueness (top edge zero ⟹ bottom edge zero).**  A function `Φ` holomorphic on the open strip `{−1 < Im z < 0}`, continuous and bounded on the closed strip, that vanishes on the *entire* top edge (`Φ(t) = 0 ∀ real t`), vanishes on the bottom edge too (`Φ(t − i) = 0 ∀ t`).  Proof: the asymmetric Hadamard three-lines bound with top constant `0` gives `‖Φ z‖ ≤ 0^{1−s}·B^{s}` (`s = −Im z`), which is `0` for every interior point (`s < 1`), so `Φ` vanishes on the open strip; the bottom edge then follows by continuity (approach `t − i` from inside).  This is the modular/KMS uniqueness that the separating proof needs.

$$
\mathrm{DifferentiableOn}\,\mathbb{C}\,\Phi\,(\mathrm{im} ^{-1}{}' \mathrm{Ioo}\,(-1)\,0) \to \mathrm{ContinuousOn}\,\Phi\,(\mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0) \to \mathrm{BddAbove}\,(\mathrm{norm} \circ \Phi '' \mathrm{im} ^{-1}{}' \mathrm{Icc}\,(-1)\,0) \to (\forall (t : \mathbb{R}), \Phi\,t = 0) \to \forall (t : \mathbb{R}), \Phi\,(t - i) = 0
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`niceWedgeSeparating_pos_mass`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass).</small>

<a id="d-qiqth-fock-cyclicwitness-nicewedgeseparating-pos-mass"></a>
**Lemma 229** (`niceWedgeSeparating_pos_mass`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L594)</small>

** THE SEPARATING Reeh–Schlieder input, DISCHARGED for all `m > 0`, axiom-free (Pauli–Jordan).** `NiceWedgeSeparating m`: the only `v` with both `v` and `i·v` in the nice-core wedge subspace `K` is `v = 0` (symplectic non-degeneracy / no nonzero complex line).  Proof — pure modular/KMS: from the boost-KMS witness (`stripKMSrvd_closure`) take `F_vv` for `(v,v)` and `F_c` for `(i·v, v)`; both `v, i·v ∈ K = closure(genSet)`. On the TOP edge `F_c(t) = ⟪v, U_t(i v)⟫ = i⟪v, U_t v⟫ = i·F_vv(t)`, so `D := F_c − i·F_vv` vanishes on the whole top edge.  `D` is holomorphic on the strip, continuous and bounded on its closure, so by strip boundary-uniqueness (`strip_eqZero_of_top_edge_zero`) it vanishes on the BOTTOM edge too. …

$$
0 < m \to \href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeseparating}{\mathrm{NiceWedgeSeparating}}\,m
$$

*Proof.* By [`niceWedgeGenSet`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgegenset), [`niceWedgeClosedSubmodule`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule), [`niceWedgeClosedSubmodule_coe`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgeclosedsubmodule-coe), [`stripKMSrvd_closure`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-stripkmsrvd-closure), [`strip_eqZero_of_top_edge_zero`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-strip-eqzero-of-top-edge-zero), [`boostUnitary`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary), [`boostUnitary_zero_apply`](/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary-zero-apply). $\square$

<small>Used by [`oneParticleBW_niceWedge_unconditional`](/browser/qiqth-fock-cyclicwitness#d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional), [`freeField_modularEnergy_eq_boostCharge`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-modularenergy-eq-boostcharge), [`freeField_oneParticle_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-oneparticle-hflux), [`freeField_component_hFlux`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-component-hflux), [`freeField_kd_conclusion`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-freefield-kd-conclusion), [`qiqt_gr_freefield`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield).</small>

<a id="d-qiqth-fock-cyclicwitness-oneparticlebw-nicewedge-unconditional"></a>
**Theorem 230** (`oneParticleBW_niceWedge_unconditional`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/CyclicWitness.lean#L693)</small>

** THE free-field one-particle Bisognano–Wichmann — FULLY UNCONDITIONAL, axiom-free.** For every mass `m > 0` and every candidate boost representation `V t = boostUnitary(2πt)`, the modular flow of the nice-core wedge standard subspace equals the boost: `modUnitary S t = V t`, with NO Reeh–Schlieder hypotheses whatsoever.  BOTH analytic inputs are now discharged internally and unconditionally: `niceWedgeSeparating_pos_mass` (Pauli–Jordan symplectic non-degeneracy, via the KMS uniqueness argument) and `niceWedgeCyclic_pos_mass` (wedge-totality, via the Wiener–Tauberian theorem). …

$$
(\forall (t : \mathbb{R}) (x : (\mathrm{Lp}\,\mathbb{C}\,2\,\mathrm{volume})), (V\,t)\,x = (\href{/browser/qiqth-fock-oneparticle#d-qiqth-fock-oneparticle-boostunitary}{U}\,(2 \cdot \pi \cdot t))\,x) \to \forall (t : \mathbb{R}), \href{/browser/qiqth-standardsubspacemodularflow#d-qiqth-standardsubspacemodular-modunitary}{\Delta}\,(\href{/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-nicewedgestandardsubspace}{\mathcal{K}}\,m\,\cdots \,\cdots )\,t = V\,t
$$

*Proof.* By [`oneParticleBW_niceWedge_reehSchlieder`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-oneparticlebw-nicewedge-reehschlieder). $\square$

<small>Used by [`freeField_modularEnergy_eq_boostCharge`](/browser/qiqth-fock-freefieldhflux#d-qiqth-fock-freefield-modularenergy-eq-boostcharge).</small>

---
<small>[← all sections](/browser) · [← BoostKMS](/browser/qiqth-fock-boostkms) · [FreeFieldHFlux →](/browser/qiqth-fock-freefieldhflux) </small>