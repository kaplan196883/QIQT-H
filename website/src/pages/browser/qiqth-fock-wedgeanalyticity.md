---
layout: ../../layouts/Deep.astro
title: QIQTH.Fock.WedgeAnalyticity
eyebrow: Fock · section of the QIQT-H book
description: QIQTH.Fock.WedgeAnalyticity — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← SchwartzDecay](/browser/qiqth-fock-schwartzdecay) · [WienerL2 →](/browser/qiqth-fock-wienerl2) </small>

<small>Fock · entries 326–383 of 1000</small>

<a id="d-qiqth-fock-wedgeanalyticity-minkowskidot"></a>
**Definition 326** (`minkowskiDotℂ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L24)</small>

**Complex Minkowski pairing** `p · x = p₀x₀ − p₁x₁` for a complex momentum `p` and a real point `x`.

$$
\eta\,p\,x \;:=\; p\,0 \cdot (x\,0) - p\,1 \cdot (x\,1)
$$

<small>Used by [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`minkowskiDotℂ_massShellℂ_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal), [`KrepCont_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [`kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel), [`hasDerivAt_minkowskiDotℂ_massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-minkowskidot-massshell), [`hasDerivAt_kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel), [`continuous_kernel_in_x`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x), [`norm_kernel_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), and 5 more.</small>

<a id="d-qiqth-fock-wedgeanalyticity-massshell"></a>
**Definition 327** (`massShellℂ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L27)</small>

**The complexified mass shell** `p_m(ζ) = (m cosh ζ, m sinh ζ)` (`ℂ`-valued momentum at complex rapidity `ζ`). On the real axis it is `massShell m θ`; it satisfies `p_m(ζ+iπ) = −p_m(ζ)`.

$$
\mathrm{MS}\,m\,\zeta \;:=\; ![m \cdot \mathrm{cosh}\,\zeta , m \cdot \mathrm{sinh}\,\zeta]
$$

<small>Used by [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`massShellℂ_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell-ofreal), [`massShellℂ_add_pi_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell-add-pi-i), [`minkowskiDotℂ_massShellℂ_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal), [`KrepCont_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [`kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel), [`hasDerivAt_minkowskiDotℂ_massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-minkowskidot-massshell), [`hasDerivAt_kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel), and 7 more.</small>

<a id="d-qiqth-fock-wedgeanalyticity-krepcont"></a>
**Definition 328** (`KrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L31)</small>

**The analytically continued localized amplitude** `(K_ℂ f)(ζ) = 2^{-1/2}·∫ e^{−i·p_m(ζ)·x} f(x) dx`.


<small>Used by [`kmsFun`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun), [`kmsFun_ofReal`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal), [`kmsFun_sub_I`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-i), [`differentiable_reflKrepCont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-differentiable-reflkrepcont), [`norm_reflKrepCont_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-reflkrepcont-le), [`deriv_reflKrepCont_eq`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-deriv-reflkrepcont-eq), [`norm_deriv_reflKrepCont_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-deriv-reflkrepcont-le), [`differentiable_kmsIntegrand`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-differentiable-kmsintegrand), and 34 more.</small>

<a id="d-qiqth-fock-wedgeanalyticity-massshell-ofreal"></a>
**Lemma 329** (`massShellℂ_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L39)</small>

On the real axis the complexified mass shell is the real one: `p_m(θ) = massShell m θ` (cast to `ℂ`).

$$
\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell}{\mathrm{MS}}\,m\,(\theta)\,i = (\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,\theta\,i)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`minkowskiDotℂ_massShellℂ_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal).</small>

<a id="d-qiqth-fock-wedgeanalyticity-massshell-add-pi-i"></a>
**Lemma 330** (`massShellℂ_add_pi_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L45)</small>

**The `iπ`-shift identity `p_m(ζ + iπ) = −p_m(ζ)`** — the analytic engine of the boundary conjugation `ψ_f(θ+iπ) = conj(ψ_f(θ))`. Immediate from `cosh(ζ+iπ)=−cosh ζ`, `sinh(ζ+iπ)=−sinh ζ`.

$$
\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell}{\mathrm{MS}}\,m\,(\zeta + \pi \cdot i) = -\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell}{\mathrm{MS}}\,m\,\zeta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`kernel_add_pi_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i).</small>

<a id="d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal"></a>
**Lemma 331** (`minkowskiDotℂ_massShellℂ_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L53)</small>

The complex pairing on the real-axis mass shell is the real pairing (cast to `ℂ`).

$$
\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot}{\eta}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell}{\mathrm{MS}}\,m\,\theta)\,x = (\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot}{\eta}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell}{\mathrm{MS}}\,m\,\theta)\,x)
$$

*Proof.* By [`massShellℂ_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell-ofreal). $\square$

<small>Used by [`KrepCont_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [`kernel_add_pi_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i).</small>

<a id="d-qiqth-fock-wedgeanalyticity-krepcont-ofreal"></a>
**Lemma 332** (`KrepCont_ofReal`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L58)</small>

**A1a — real-axis agreement.** The continued amplitude restricted to the real rapidity axis is the original localized amplitude: `(K_ℂ f)(θ) = (K f)(θ)`.

$$
\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f\,\theta = \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f\,\theta
$$

*Proof.* By [`minkowskiDot`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot), [`massShell`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell), [`minkowskiFourier`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskifourier), [`minkowskiDotℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot), [`massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell), [`minkowskiDotℂ_massShellℂ_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal). $\square$

<small>Used by [`kmsFun_ofReal`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-ofreal), [`kmsFunCut_ofReal`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-ofreal), [`KrepCont_add_pi_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i), [`Krep_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krep-add), [`memLp_KrepCont_affine_closed`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed).</small>

<a id="d-qiqth-fock-wedgeanalyticity-cosh-ofreal-add-ofreal-mul-i"></a>
**Lemma 333** (`cosh_ofReal_add_ofReal_mul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L69)</small>

`cosh(θ + iλ) = cosh θ cos λ + i sinh θ sin λ` (real/imaginary split at a complex rapidity).

$$
\mathrm{cosh}\,(\theta + \lambda \cdot i) = (\cosh\,\theta \cdot \cos\,\lambda) + (\sinh\,\theta \cdot \sin\,\lambda) \cdot i
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`norm_kernel_eq`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq).</small>

<a id="d-qiqth-fock-wedgeanalyticity-sinh-ofreal-add-ofreal-mul-i"></a>
**Lemma 334** (`sinh_ofReal_add_ofReal_mul_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L77)</small>

`sinh(θ + iλ) = sinh θ cos λ + i cosh θ sin λ`.

$$
\mathrm{sinh}\,(\theta + \lambda \cdot i) = (\sinh\,\theta \cdot \cos\,\lambda) + (\cosh\,\theta \cdot \sin\,\lambda) \cdot i
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`norm_kernel_eq`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq).</small>

<a id="d-qiqth-fock-wedgeanalyticity-kernel"></a>
**Definition 335** (`kernel`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L111)</small>

The analytic-continuation **kernel** `K(ζ, x) = exp(−i·p_m(ζ)·x)`.

$$
\mathrm{kernel}\,m\,x\,\zeta \;:=\; \exp\,(-i \cdot \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot}{\eta}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell}{\mathrm{MS}}\,m\,\zeta)\,x)
$$

<small>Used by [`hasDerivAt_kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel), [`kernelDeriv`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernelderiv), [`hasDerivAt_kernel_mul`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel-mul), [`continuous_kernel_in_x`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x), [`norm_kernel_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), [`norm_kernelDeriv_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le), [`continuous_kernelDeriv_in_x`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-continuous-kernelderiv-in-x), [`hasDerivAt_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont), and 8 more.</small>

<a id="d-qiqth-fock-wedgeanalyticity-hasderivat-minkowskidot-massshell"></a>
**Lemma 336** (`hasDerivAt_minkowskiDotℂ_massShellℂ`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L115)</small>

The `ζ`-derivative of the complex pairing `p_m(ζ)·x = m coshζ·x₀ − m sinhζ·x₁` is `m sinhζ·x₀ − m coshζ·x₁`.

$$
({\lambda \zeta \mapsto \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot}{\eta}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell}{\mathrm{MS}}\,m\,\zeta)\,x})'({\zeta})={m \cdot \mathrm{sinh}\,\zeta \cdot (x\,0) - m \cdot \mathrm{cosh}\,\zeta \cdot (x\,1)}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`hasDerivAt_kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel).</small>

<a id="d-qiqth-fock-wedgeanalyticity-hasderivat-kernel"></a>
**Lemma 337** (`hasDerivAt_kernel`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L128)</small>

**A1b (pointwise).** For each `x`, the kernel `ζ ↦ K(ζ,x)` is complex-differentiable everywhere, with `dK/dζ = K(ζ,x)·(−i·(m sinhζ·x₀ − m coshζ·x₁))` — the chain rule through `exp`. So for each fixed `x` the integrand is entire in the rapidity parameter (the per-`x` half of the dominated-convergence holomorphy argument).

$$
({\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x})'({\zeta})={\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta \cdot (-i \cdot (m \cdot \mathrm{sinh}\,\zeta \cdot (x\,0) - m \cdot \mathrm{cosh}\,\zeta \cdot (x\,1)))}
$$

*Proof.* By [`minkowskiDotℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot), [`massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell), [`hasDerivAt_minkowskiDotℂ_massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-minkowskidot-massshell). $\square$

<small>Used by [`hasDerivAt_kernel_mul`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel-mul).</small>

<a id="d-qiqth-fock-wedgeanalyticity-kernelderiv"></a>
**Definition 338** (`kernelDeriv`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L142)</small>

The integrand-derivative value `K'(ζ,x) = K(ζ,x)·(−i·(m sinhζ·x₀ − m coshζ·x₁))`.

$$
\mathrm{K}'\,m\,x\,\zeta \;:=\; \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta \cdot (-i \cdot (m \cdot \mathrm{sinh}\,\zeta \cdot (x\,0) - m \cdot \mathrm{cosh}\,\zeta \cdot (x\,1)))
$$

<small>Used by [`hasDerivAt_kernel_mul`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel-mul), [`norm_kernelDeriv_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le), [`continuous_kernelDeriv_in_x`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-continuous-kernelderiv-in-x), [`hasDerivAt_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont), [`differentiable_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont), [`deriv_KrepCont_eq`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-deriv-krepcont-eq), [`norm_kernelDeriv_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay), [`norm_deriv_KrepCont_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-hasderivat-kernel-mul"></a>
**Lemma 339** (`hasDerivAt_kernel_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L147)</small>

The full integrand `ζ ↦ K(ζ,x)·f(x)` is complex-differentiable, derivative `K'(ζ,x)·f(x)` (the `h_diff` ingredient for the dominated parametric-derivative assembly).

$$
({\lambda \zeta \mapsto \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta \cdot f\,x})'({\zeta})={\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta \cdot f\,x}
$$

*Proof.* By [`hasDerivAt_kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel). $\square$

<small>Used by [`hasDerivAt_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont).</small>

<a id="d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x"></a>
**Lemma 340** (`continuous_kernel_in_x`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L153)</small>

The kernel is continuous in `x` (for fixed `ζ`) — gives `ae`-strong-measurability of the integrand.

$$
\mathrm{Continuous}\,\lambda x \mapsto \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta
$$

*Proof.* By [`minkowskiDotℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot), [`massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell). $\square$

<small>Used by [`continuous_kernelDeriv_in_x`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-continuous-kernelderiv-in-x), [`hasDerivAt_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont), [`KrepCont_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-exp-le-exp-norm"></a>
**Lemma 341** (`norm_exp_le_exp_norm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L159)</small>

`‖exp z‖ ≤ e^{‖z‖}` and `‖exp(−z)‖ ≤ e^{‖z‖}` (from `‖exp z‖ = e^{Re z}` and `±Re z ≤ ‖z‖`).

$$
\|\exp\,z\| \le \exp\,\|z\|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`norm_exp_neg_le_exp_norm`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-exp-neg-le-exp-norm), [`norm_cosh_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-cosh-le), [`norm_sinh_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-sinh-le), [`norm_kernel_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-exp-neg-le-exp-norm"></a>
**Lemma 342** (`norm_exp_neg_le_exp_norm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L163)</small>

$$
\|\exp\,(-z)\| \le \exp\,\|z\|
$$

*Proof.* By [`norm_exp_le_exp_norm`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-exp-le-exp-norm). $\square$

<small>Used by [`norm_cosh_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-cosh-le), [`norm_sinh_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-sinh-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-cosh-le"></a>
**Lemma 343** (`norm_cosh_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L167)</small>

`‖cosh ζ‖ ≤ e^{‖ζ‖}` (crude growth bound from `cosh ζ = (e^ζ + e^{−ζ})/2`).

$$
\|\mathrm{cosh}\,\zeta\| \le \exp\,\|\zeta\|
$$

*Proof.* By [`norm_exp_le_exp_norm`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-exp-le-exp-norm), [`norm_exp_neg_le_exp_norm`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-exp-neg-le-exp-norm). $\square$

<small>Used by [`norm_kernel_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), [`norm_kernelDeriv_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-cosh-le-cosh-re"></a>
**Lemma 344** (`norm_cosh_le_cosh_re`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L178)</small>

`‖cosh ζ‖ ≤ cosh(Re ζ)` (sharp real-part bound, `‖e^{±ζ}‖ = e^{±Re ζ}`).

$$
\|\mathrm{cosh}\,\zeta\| \le \cosh\,\zeta.\mathrm{re}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`norm_kernelDeriv_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-sinh-le-cosh-re"></a>
**Lemma 345** (`norm_sinh_le_cosh_re`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L187)</small>

`‖sinh ζ‖ ≤ cosh(Re ζ)` (sharp real-part bound).

$$
\|\mathrm{sinh}\,\zeta\| \le \cosh\,\zeta.\mathrm{re}
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`norm_kernelDeriv_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-sinh-le"></a>
**Lemma 346** (`norm_sinh_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L196)</small>

`‖sinh ζ‖ ≤ e^{‖ζ‖}` (crude growth bound from `sinh ζ = (e^ζ − e^{−ζ})/2`).

$$
\|\mathrm{sinh}\,\zeta\| \le \exp\,\|\zeta\|
$$

*Proof.* By [`norm_exp_le_exp_norm`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-exp-le-exp-norm), [`norm_exp_neg_le_exp_norm`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-exp-neg-le-exp-norm). $\square$

<small>Used by [`norm_kernel_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), [`norm_kernelDeriv_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-term-le"></a>
**Lemma 347** (`norm_term_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L207)</small>

A bound for a term `(m·c)·a − (m·s)·b` with `‖c‖,‖s‖ ≤ e^r`: `≤ |m|·e^r·(|a|+|b|)`. Used for both the pairing `p_m(ζ)·x` (`c,s = cosh,sinh`) and its `ζ`-derivative (`c,s = sinh,cosh`).

$$
\|c\| \le \exp\,r \to \|s\| \le \exp\,r \to \forall (a b : \mathbb{R}), \|m \cdot c \cdot a - m \cdot s \cdot b\| \le |m| \cdot \exp\,r \cdot (|a| + |b|)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`norm_kernel_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-le), [`norm_kernelDeriv_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernel-le"></a>
**Lemma 348** (`norm_kernel_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L220)</small>

`‖K(ζ,x)‖ ≤ exp(|m|·e^{‖ζ‖}·(|x₀|+|x₁|))` (kernel growth bound; `‖exp(−i·D)‖ ≤ exp‖D‖`, `‖D‖` bound).

$$
\|\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta\| \le \exp\,(|m| \cdot \exp\,\|\zeta\| \cdot (|x\,0| + |x\,1|))
$$

*Proof.* By [`minkowskiDotℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot), [`massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell), [`norm_exp_le_exp_norm`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-exp-le-exp-norm), [`norm_cosh_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-cosh-le), [`norm_sinh_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-sinh-le), [`norm_term_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-term-le). $\square$

<small>Used by [`norm_kernelDeriv_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le"></a>
**Lemma 349** (`norm_kernelDeriv_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L228)</small>

`‖K'(ζ,x)‖ ≤ exp(B)·B` with `B = |m|·e^{‖ζ‖}·(|x₀|+|x₁|)` (the integrand-derivative growth bound).

$$
\|\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta\| \le \exp\,(|m| \cdot \exp\,\|\zeta\| \cdot (|x\,0| + |x\,1|)) \cdot (|m| \cdot \exp\,\|\zeta\| \cdot (|x\,0| + |x\,1|))
$$

*Proof.* By [`kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel), [`norm_cosh_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-cosh-le), [`norm_sinh_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-sinh-le), [`norm_term_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-term-le), [`norm_kernel_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-le). $\square$

<small>Used by [`hasDerivAt_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont).</small>

<a id="d-qiqth-fock-wedgeanalyticity-continuous-kernelderiv-in-x"></a>
**Lemma 350** (`continuous_kernelDeriv_in_x`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L239)</small>

The integrand-derivative is continuous in `x` (for fixed `ζ`) — gives measurability.

$$
\mathrm{Continuous}\,\lambda x \mapsto \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta
$$

*Proof.* By [`kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel), [`continuous_kernel_in_x`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x). $\square$

<small>Used by [`hasDerivAt_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont).</small>

<a id="d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont"></a>
**Lemma 351** (`hasDerivAt_KrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L246)</small>

**A1b-ii-β — holomorphy of `KrepCont`.** For `f` continuous with compact support, `ζ ↦ KrepCont m f ζ` is complex-differentiable at every `ζ₀`, with derivative `(1/√2)·∫ K'(ζ₀,x)·f(x)`. Proven by the dominated parametric-derivative theorem (𝕜 = ℂ): the per-`x` derivative is `hasDerivAt_kernel_mul`, and the ball-domination uses `norm_kernelDeriv_le` + the compact bound `‖x‖ ≤ M` on `tsupport f`.

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall (\zeta_{0} : \mathbb{C}), ({\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f})'({\zeta_{0}})={1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta_{0} \cdot f\,x}
$$

*Proof.* By [`kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel), [`hasDerivAt_kernel_mul`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-kernel-mul), [`continuous_kernel_in_x`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x), [`norm_kernelDeriv_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le), [`continuous_kernelDeriv_in_x`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-continuous-kernelderiv-in-x). $\square$

<small>Used by [`differentiable_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont), [`deriv_KrepCont_eq`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-deriv-krepcont-eq).</small>

<a id="d-qiqth-fock-wedgeanalyticity-differentiable-krepcont"></a>
**Lemma 352** (`differentiable_KrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L289)</small>

**A1b — `KrepCont m f` is entire** for `f` continuous with compact support.

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Differentiable}\,\mathbb{C}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f)
$$

*Proof.* By [`kernelDeriv`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernelderiv), [`hasDerivAt_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont). $\square$

<small>Used by [`differentiable_reflKrepCont`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-differentiable-reflkrepcont), [`deriv_reflKrepCont_eq`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-deriv-reflkrepcont-eq), [`differentiable_kmsIntegrand`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-differentiable-kmsintegrand), [`hasDerivAt_kmsIntegrand_z`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-hasderivat-kmsintegrand-z), [`continuous_kmsIntegrand_in_theta`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-kmsintegrand-in-theta), [`continuous_kmsIntegrand_deriv_in_theta`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta), [`continuous_deriv_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-continuous-deriv-krepcont), [`memLp_KrepCont_affine`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine).</small>

<a id="d-qiqth-fock-wedgeanalyticity-continuous-deriv-krepcont"></a>
**Lemma 353** (`continuous_deriv_KrepCont`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L294)</small>

**`deriv (KrepCont m f)` is continuous** (entire ⟹ analytic ⟹ deriv analytic ⟹ continuous, `AnalyticAt.deriv`). The measurability ingredient (`hF'_meas`) for the dominated-derivative theorem.

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \mathrm{Continuous}\,(\mathrm{D}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f))
$$

*Proof.* By [`differentiable_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont). $\square$

<small>Used by [`continuous_kmsIntegrand_deriv_in_theta`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-continuous-kmsintegrand-deriv-in-theta).</small>

<a id="d-qiqth-fock-wedgeanalyticity-deriv-krepcont-eq"></a>
**Lemma 354** (`deriv_KrepCont_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L300)</small>

The rapidity-derivative of `KrepCont m f` as an integral: `(K_ℂ f)'(ζ) = 2^{-1/2}·∫ K'(ζ,x)·f(x) dx`.

$$
\mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall (\zeta : \mathbb{C}), \mathrm{D}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f)\,\zeta = 1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta \cdot f\,x
$$

*Proof.* By [`hasDerivAt_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-hasderivat-krepcont). $\square$

<small>Used by [`norm_deriv_KrepCont_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i"></a>
**Lemma 355** (`kernel_add_pi_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L307)</small>

The kernel's `iπ`-boundary conjugation: `K(θ+iπ, x) = conj(K(θ, x))`. Engine: `p_m(θ+iπ) = −p_m(θ)` and `p_m(θ)·x` real, so `exp(−i·(−p_m(θ)·x)) = conj(exp(−i·p_m(θ)·x))`.

$$
\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,(\theta + \pi \cdot i) = (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\theta)
$$

*Proof.* By [`minkowskiDot`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-minkowskidot), [`massShell`](/browser/qiqth-fock-localization#d-qiqth-fock-localization-massshell), [`minkowskiDotℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot), [`massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell), [`massShellℂ_add_pi_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell-add-pi-i), [`minkowskiDotℂ_massShellℂ_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot-massshell-ofreal). $\square$

<small>Used by [`KrepCont_add_pi_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i).</small>

<a id="d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i"></a>
**Lemma 356** (`KrepCont_add_pi_I`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L319)</small>

**A3 — boundary conjugation of the continued amplitude.** For *real* `f`, `ψ_f(θ+iπ) = conj(ψ_f(θ))` (`= conj(Krep m f θ)`). This is the relation that turns the top edge `⟪η, V_t ξ⟫` into the KMS bottom edge `⟪V_t ξ, η⟫`.

$$
(\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to \forall (\theta : \mathbb{R}), \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f\,(\theta + \pi \cdot i) = (\mathrm{starRingEnd}\,\mathbb{C})\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f\,\theta)
$$

*Proof.* By [`minkowskiDotℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot), [`massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell), [`KrepCont_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [`kernel_add_pi_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel-add-pi-i). $\square$

<small>Used by [`kmsFun_sub_I`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-i), [`kmsFunCut_sub_I`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-sub-i), [`memLp_KrepCont_affine_closed`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed).</small>

<a id="d-qiqth-fock-wedgeanalyticity-sq-div-eight-le-cosh"></a>
**Lemma 357** (`sq_div_eight_le_cosh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L360)</small>

`θ²/8 ≤ cosh θ` — a crude quadratic lower bound (`cosh θ ≥ e^{|θ|}/2 ≥ (1+|θ|/2)²/2 ≥ θ²/8`), the comparison feeding the Gaussian domination of the wedge-mode strip decay.

$$
{\theta}^{2} / 8 \le \cosh\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`integrable_exp_neg_const_mul_cosh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-integrable-exp-neg-const-mul-cosh).</small>

<a id="d-qiqth-fock-wedgeanalyticity-integrable-exp-neg-const-mul-cosh"></a>
**Lemma 358** (`integrable_exp_neg_const_mul_cosh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L375)</small>

**A2 (decay building block).** `θ ↦ exp(−c·cosh θ)` is integrable over `ℝ` for `c > 0` — by Gaussian domination `exp(−c cosh θ) ≤ exp(−(c/8)·θ²)` (`sq_div_eight_le_cosh`). The `θ`-integrability that the interior-`λ` strip decay of the wedge mode reduces to (the damping exponent is `∝ −cosh θ`).

$$
0 < c \to \mathrm{Integrable}\,(\lambda \theta \mapsto \exp\,(-(c \cdot \cosh\,\theta)))\,\mathrm{vol}
$$

*Proof.* By [`sq_div_eight_le_cosh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-sq-div-eight-le-cosh). $\square$

<small>Used by [`integrable_kmsIntegrand`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-integrable-kmsintegrand), [`integrable_cosh_mul_exp_neg_const_mul_cosh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-integrable-cosh-mul-exp-neg-const-mul-cosh), [`memLp_KrepCont_affine`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine).</small>

<a id="d-qiqth-fock-wedgeanalyticity-abs-sinh-le-cosh"></a>
**Lemma 359** (`abs_sinh_le_cosh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L386)</small>

`|sinh θ| ≤ cosh θ` (`cosh±sinh = e^{±θ} ≥ 0`).

$$
|\sinh\,\theta| \le \cosh\,\theta
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`cosh_add_le_exp_abs_mul`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-cosh-add-le-exp-abs-mul), [`exp_neg_abs_mul_le_cosh_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-exp-neg-abs-mul-le-cosh-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-cosh-add-abs-sinh"></a>
**Lemma 360** (`cosh_add_abs_sinh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L392)</small>

`cosh s + |sinh s| = e^{|s|}` and `cosh s − |sinh s| = e^{−|s|}`.

$$
\cosh\,s + |\sinh\,s| = \exp\,|s|
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`cosh_add_le_exp_abs_mul`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-cosh-add-le-exp-abs-mul).</small>

<a id="d-qiqth-fock-wedgeanalyticity-cosh-sub-abs-sinh"></a>
**Lemma 361** (`cosh_sub_abs_sinh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L402)</small>

$$
\cosh\,s - |\sinh\,s| = \exp\,(-|s|)
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`exp_neg_abs_mul_le_cosh_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-exp-neg-abs-mul-le-cosh-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-cosh-add-le-exp-abs-mul"></a>
**Lemma 362** (`cosh_add_le_exp_abs_mul`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L412)</small>

**`cosh(θ+s) ≤ e^{|s|}·cosh θ`** (shift upper bound — makes the shifting-peak strip decay uniform).

$$
\cosh\,(\theta + s) \le \exp\,|s| \cdot \cosh\,\theta
$$

*Proof.* By [`abs_sinh_le_cosh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-abs-sinh-le-cosh), [`cosh_add_abs_sinh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-cosh-add-abs-sinh). $\square$

<small>Used by [`cosh_shift_exp_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-cosh-shift-exp-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-exp-neg-abs-mul-le-cosh-add"></a>
**Lemma 363** (`exp_neg_abs_mul_le_cosh_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L421)</small>

**`e^{−|s|}·cosh θ ≤ cosh(θ+s)`** (shift lower bound).

$$
\exp\,(-|s|) \cdot \cosh\,\theta \le \cosh\,(\theta + s)
$$

*Proof.* By [`abs_sinh_le_cosh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-abs-sinh-le-cosh), [`cosh_sub_abs_sinh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-cosh-sub-abs-sinh). $\square$

<small>Used by [`cosh_shift_exp_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-cosh-shift-exp-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-sin-neg-pi-mul-pos"></a>
**Lemma 364** (`sin_neg_pi_mul_pos`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L440)</small>

`0 < sin(−π·w)` for `−1 < w < 0` (the decay rate `σ = sin(−π·Im z)` is positive on the open strip).

$$
-1 < w \to w < 0 \to 0 < \sin\,(-(\pi \cdot w))
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`integrable_kmsIntegrand`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-integrable-kmsintegrand), [`exists_sin_min`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-exists-sin-min), [`norm_term1_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-term1-le), [`norm_term2_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-term2-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-cosh-shift-exp-le"></a>
**Lemma 365** (`cosh_shift_exp_le`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L444)</small>

**The shifted `cosh·exp` made uniform.** For `|s| ≤ S`, `0 < c₀ ≤ c`: `cosh(θ+s)·exp(−c·cosh(θ+s)) ≤ e^S·cosh θ·exp(−c₀·e^{−S}·cosh θ)`. The core estimate that turns the shifting-peak strip decay (`s = πRe z` over a `z`-ball) into a `z`-uniform integrable-in-`θ` bound.

$$
|s| \le S \to 0 < c_{0} \to c_{0} \le c \to \cosh\,(\theta + s) \cdot \exp\,(-(c \cdot \cosh\,(\theta + s))) \le \exp\,S \cdot \cosh\,\theta \cdot \exp\,(-(c_{0} \cdot \exp\,(-S) \cdot \cosh\,\theta))
$$

*Proof.* By [`cosh_add_le_exp_abs_mul`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-cosh-add-le-exp-abs-mul), [`exp_neg_abs_mul_le_cosh_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-exp-neg-abs-mul-le-cosh-add). $\square$

<small>Used by [`prod_norm_bound_cosh_shift`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-prod-norm-bound-cosh-shift).</small>

<a id="d-qiqth-fock-wedgeanalyticity-prod-norm-bound-cosh-shift"></a>
**Lemma 366** (`prod_norm_bound_cosh_shift`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L466)</small>

**The `h_bound` core estimate.** A `cosh(θ+s)·exp(−c·cosh(θ+s))`-decaying factor (`na`) times a bounded factor (`nb ≤ Cb`), made `z`-uniform: `na·nb ≤ Cd·Cb·(e^S·cosh θ·exp(−c₀·e^{−S}·cosh θ))`. Both terms of the `kmsFun` integrand `z`-derivative reduce to this (via the four factor bounds + `cosh_shift_exp_le`).

$$
\mathrm{na} \le \mathrm{Cd} \cdot (\cosh\,(\theta + s) \cdot \exp\,(-(c \cdot \cosh\,(\theta + s)))) \to \mathrm{nb} \le \mathrm{Cb} \to 0 \le \mathrm{nb} \to 0 \le \mathrm{Cb} \to 0 \le \mathrm{Cd} \to |s| \le S \to 0 < c_{0} \to c_{0} \le c \to \mathrm{na} \cdot \mathrm{nb} \le \mathrm{Cd} \cdot \mathrm{Cb} \cdot (\exp\,S \cdot \cosh\,\theta \cdot \exp\,(-(c_{0} \cdot \exp\,(-S) \cdot \cosh\,\theta)))
$$

*Proof.* By [`cosh_shift_exp_le`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-cosh-shift-exp-le). $\square$

<small>Used by [`norm_term1_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-term1-le), [`norm_term2_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-term2-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-integrable-cosh-mul-exp-neg-const-mul-cosh"></a>
**Lemma 367** (`integrable_cosh_mul_exp_neg_const_mul_cosh`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L480)</small>

**A2 (derivative-decay building block).** `s ↦ cosh s·exp(−c·cosh s)` is integrable over `ℝ` for `c > 0`. The integrand-derivative bound (`‖kernelDeriv‖ ≲ cosh(s)·exp(−c·cosh s)`, the `cosh` polynomial factor against the double-exponential damping) reduces to this. Via `cosh s ≤ (1/c)·exp((c/2)cosh s)` (`Real.two_mul_le_exp`) ⟹ `cosh s·exp(−c cosh s) ≤ (1/c)·exp(−(c/2)cosh s)`.

$$
0 < c \to \mathrm{Integrable}\,(\lambda s \mapsto \cosh\,s \cdot \exp\,(-(c \cdot \cosh\,s)))\,\mathrm{vol}
$$

*Proof.* By [`integrable_exp_neg_const_mul_cosh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-integrable-exp-neg-const-mul-cosh). $\square$

<small>Used by [`kmsFun_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-differentiableat), [`kmsFunCut_differentiableAt`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-differentiableat).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernel-eq"></a>
**Lemma 368** (`norm_kernel_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L516)</small>

The exact kernel modulus on the strip: `‖K(θ+iλ,x)‖ = exp(m sinλ·(sinhθ·x₀ − coshθ·x₁))`.

$$
\|\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,(\theta + \lambda \cdot i)\| = \exp\,(m \cdot \sin\,\lambda \cdot (\sinh\,\theta \cdot x\,0 - \cosh\,\theta \cdot x\,1))
$$

*Proof.* By [`minkowskiDotℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot), [`massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell), [`cosh_ofReal_add_ofReal_mul_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-cosh-ofreal-add-ofreal-mul-i), [`sinh_ofReal_add_ofReal_mul_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-sinh-ofreal-add-ofreal-mul-i). $\square$

<small>Used by [`norm_kernel_eq'`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq), [`norm_kernel_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernel-eq"></a>
**Lemma 369** (`norm_kernel_eq'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L528)</small>

The exact kernel modulus at a **general** complex `ζ`: `‖K(ζ,x)‖ = exp(m sin(Im ζ)·(sinh(Re ζ)·x₀ − cosh(Re ζ)·x₁))` (rewrite `ζ = Re ζ + i·Im ζ`, then `norm_kernel_eq`).

$$
\|\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta\| = \exp\,(m \cdot \sin\,\zeta.\mathrm{im} \cdot (\sinh\,\zeta.\mathrm{re} \cdot x\,0 - \cosh\,\zeta.\mathrm{re} \cdot x\,1))
$$

*Proof.* By [`norm_kernel_eq`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq). $\square$

<small>Used by [`norm_kernel_le_exp_decay'`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay"></a>
**Lemma 370** (`norm_kernel_le_exp_decay`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L536)</small>

**Pointwise strip-decay of the kernel.** For `x` with wedge margin `δ` (`δ ≤ x₁∓x₀`) and `0≤λ≤π`, `‖K(θ+iλ,x)‖ ≤ exp(−(m sinλ δ)·coshθ)` — double-exponential decay in `θ` for interior `λ`.

$$
0 \le m \to \forall \{x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}\} \{\delta : \mathbb{R}\}, \delta \le x\,1 - x\,0 \to \delta \le x\,1 + x\,0 \to \forall \{\theta \lambda : \mathbb{R}\}, 0 \le \lambda \to \lambda \le \pi \to \|\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,(\theta + \lambda \cdot i)\| \le \exp\,(-(m \cdot \sin\,\lambda \cdot \delta) \cdot \cosh\,\theta)
$$

*Proof.* By [`norm_kernel_eq`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq). $\square$

<small>Used by [`norm_KrepCont_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay"></a>
**Lemma 371** (`norm_kernel_le_exp_decay'`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L553)</small>

**Pointwise strip-decay of the kernel at a general `ζ`** (`0 ≤ Im ζ ≤ π`, `x` with wedge margin `δ`): `‖K(ζ,x)‖ ≤ exp(−(m sin(Im ζ) δ)·cosh(Re ζ))`. The general-`ζ` form powering the `z`-derivative decay.

$$
0 \le m \to \forall \{x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}\} \{\delta : \mathbb{R}\}, \delta \le x\,1 - x\,0 \to \delta \le x\,1 + x\,0 \to \forall \{\zeta : \mathbb{C}\}, 0 \le \zeta.\mathrm{im} \to \zeta.\mathrm{im} \le \pi \to \|\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel}{\mathrm{kernel}}\,m\,x\,\zeta\| \le \exp\,(-(m \cdot \sin\,\zeta.\mathrm{im} \cdot \delta) \cdot \cosh\,\zeta.\mathrm{re})
$$

*Proof.* By [`norm_kernel_eq'`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-eq). $\square$

<small>Used by [`norm_kernelDeriv_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay"></a>
**Lemma 372** (`norm_kernelDeriv_le_exp_decay`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L568)</small>

**Pointwise strip-decay of `kernelDeriv` at a general `ζ`**: `‖K'(ζ,x)‖ ≤ exp(−c·cosh(Re ζ))·|m|· cosh(Re ζ)·(|x₀|+|x₁|)` (`c = m sin(Im ζ) δ`). Kernel decay (`norm_kernel_le_exp_decay'`) × `poly` bound (`‖poly‖ ≤ |m|·cosh(Re ζ)·(|x₀|+|x₁|)` via `norm_sinh/cosh_le_cosh_re`). The `cosh(Re ζ)` polynomial factor against the double-exponential damping — the integrand of the `z`-derivative domination.

$$
0 \le m \to \forall \{x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}\} \{\delta : \mathbb{R}\}, \delta \le x\,1 - x\,0 \to \delta \le x\,1 + x\,0 \to \forall \{\zeta : \mathbb{C}\}, 0 \le \zeta.\mathrm{im} \to \zeta.\mathrm{im} \le \pi \to \|\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernelderiv}{\mathrm{K}{}'}\,m\,x\,\zeta\| \le \exp\,(-(m \cdot \sin\,\zeta.\mathrm{im} \cdot \delta) \cdot \cosh\,\zeta.\mathrm{re}) \cdot (|m| \cdot \cosh\,\zeta.\mathrm{re} \cdot (|x\,0| + |x\,1|))
$$

*Proof.* By [`kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel), [`norm_cosh_le_cosh_re`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-cosh-le-cosh-re), [`norm_sinh_le_cosh_re`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-sinh-le-cosh-re), [`norm_kernel_le_exp_decay'`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay). $\square$

<small>Used by [`norm_deriv_KrepCont_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay"></a>
**Lemma 373** (`norm_KrepCont_le_exp_decay`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L592)</small>

**A2 (step 1) — pointwise strip-decay of the continued amplitude.** For wedge-supported `f` (uniform margin `δ` via `exists_wedge_margin`) and `0≤λ≤π`, `‖KrepCont m f (θ+iλ)‖ ≤ (1/√2)·(∫‖f‖)·exp(−(m sinλ δ)·coshθ)`. The decay factor (double-exponential in `θ` for interior `λ`) is what makes `KrepCont m f (·+iλ) ∈ L²`.

$$
0 \le m \to \forall \{f : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{\theta \lambda : \mathbb{R}\}, 0 \le \lambda \to \lambda \le \pi \to \|\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f\,(\theta + \lambda \cdot i)\| \le (1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|f\,x\|) \cdot \exp\,(-(m \cdot \sin\,\lambda \cdot \delta) \cdot \cosh\,\theta)
$$

*Proof.* By [`minkowskiDotℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot), [`massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell), [`kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel), [`norm_kernel_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernel-le-exp-decay). $\square$

<small>Used by [`norm_KrepCont_le_exp_decay_gen`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-deriv-krepcont-le-exp-decay"></a>
**Lemma 374** (`norm_deriv_KrepCont_le_exp_decay`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L621)</small>

**Pointwise strip-decay of `deriv KrepCont`.** For wedge-supported `f` (margin `δ`) and `0≤Im ζ≤π`, `‖deriv(KrepCont m f) ζ‖ ≤ (1/√2)·|m|·cosh(Re ζ)·exp(−c·cosh(Re ζ))·∫(|x₀|+|x₁|)‖f‖` (`c=m sin(Im ζ)δ`). The `z`-derivative norm bound: `cosh(Re ζ)·exp(−c·cosh(Re ζ))` decay (× a finite constant).

$$
0 \le m \to \forall \{f : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{\zeta : \mathbb{C}\}, 0 \le \zeta.\mathrm{im} \to \zeta.\mathrm{im} \le \pi \to \|\mathrm{D}\,(\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f)\,\zeta\| \le 1 / \sqrt 2 \cdot (|m| \cdot \cosh\,\zeta.\mathrm{re} \cdot \exp\,(-(m \cdot \sin\,\zeta.\mathrm{im} \cdot \delta) \cdot \cosh\,\zeta.\mathrm{re}) \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (|x\,0| + |x\,1|) \cdot \|f\,x\|)
$$

*Proof.* By [`kernelDeriv`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernelderiv), [`deriv_KrepCont_eq`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-deriv-krepcont-eq), [`norm_kernelDeriv_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-kernelderiv-le-exp-decay). $\square$

<small>Used by [`norm_deriv_reflKrepCont_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-deriv-reflkrepcont-le), [`norm_term2_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-term2-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen"></a>
**Lemma 375** (`norm_KrepCont_le_exp_decay_gen`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L655)</small>

**Pointwise strip-decay of `KrepCont` at a general complex argument `w`** (`0≤Im w≤π`, `f` wedge-supported): `‖KrepCont m f w‖ ≤ (1/√2)·(∫‖f‖)·exp(−(m sin(Im w)δ)·cosh(Re w))` (rewrite `w = Re w + i·Im w`).

$$
0 \le m \to \forall \{f : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{w : \mathbb{C}\}, 0 \le w.\mathrm{im} \to w.\mathrm{im} \le \pi \to \|\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f\,w\| \le (1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|f\,x\|) \cdot \exp\,(-(m \cdot \sin\,w.\mathrm{im} \cdot \delta) \cdot \cosh\,w.\mathrm{re})
$$

*Proof.* By [`norm_KrepCont_le_exp_decay`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay). $\square$

<small>Used by [`norm_reflKrepCont_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-reflkrepcont-le), [`integrable_kmsIntegrand`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-integrable-kmsintegrand), [`norm_term1_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-term1-le), [`norm_KrepCont_le_const`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-const), [`memLp_KrepCont_affine`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine).</small>

<a id="d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-const"></a>
**Lemma 376** (`norm_KrepCont_le_const`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L666)</small>

**Plain `KrepCont` bound on the closed strip** (`0≤Im w≤π`, `f` wedge-supported with `δ≥0`): `‖KrepCont m f w‖ ≤ (1/√2)·∫‖f‖` — the strip-damping factor `exp(−(m sin(Im w)δ)·cosh(Re w)) ≤ 1` since its exponent is `≤ 0` (`sin(Im w)≥0` on `[0,π]`, `m,δ,cosh ≥ 0`). This `Re`-uniform constant bound is what makes the truncated KMS integral trivially bounded on the closed strip (no log-blowup).

$$
0 \le m \to \forall \{f : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, 0 \le \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{w : \mathbb{C}\}, 0 \le w.\mathrm{im} \to w.\mathrm{im} \le \pi \to \|\href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f\,w\| \le 1 / \sqrt 2 \cdot \int (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), \|f\,x\|
$$

*Proof.* By [`norm_KrepCont_le_exp_decay_gen`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen). $\square$

<small>Used by [`norm_kmsFunCut_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfuncut-le), [`kmsFunCut_continuousOn`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfuncut-continuouson).</small>

<a id="d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine"></a>
**Lemma 377** (`memLp_KrepCont_affine`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L724)</small>

**A2 (step 2′) — affine-argument `L²` membership.** For `m > 0`, wedge-supported `f`, and a complex offset `c₀` with `Im c₀ ∈ (0,π)`, the slice `θ ↦ KrepCont m f (θ + c₀)` is in `L²(dθ)`. The argument's imaginary part is the constant `Im c₀` (strip-interior ⟹ `sin > 0`), and the real part is `θ + Re c₀`; pointwise domination by `C·exp(−c·cosh(θ+Re c₀))` (`norm_KrepCont_le_exp_decay_gen`) against the `L²` translate of `C·exp(−c·cosh)` (`measurePreserving_add_right`). Generalizes `memLp_KrepCont_strip` to a real shift of the strip slice — the form the two boost-KMS slices take.

$$
0 < m \to \forall \{f : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to \forall \{c_{0} : \mathbb{C}\}, 0 < c_{0}.\mathrm{im} \to c_{0}.\mathrm{im} < \pi \to \mathrm{MemLp}\,(\lambda \theta \mapsto \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f\,(\theta + c_{0}))\,2\,\mathrm{vol}
$$

*Proof.* By [`differentiable_KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-differentiable-krepcont), [`integrable_exp_neg_const_mul_cosh`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-integrable-exp-neg-const-mul-cosh), [`norm_KrepCont_le_exp_decay_gen`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-norm-krepcont-le-exp-decay-gen). $\square$

<small>Used by [`memLp_KrepCont_affine_closed`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed).</small>

<a id="d-qiqth-fock-wedgeanalyticity-krepcont-add"></a>
**Lemma 378** (`KrepCont_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L757)</small>

**`KrepCont` is additive in the test function** (for continuous compact-support `f₁,f₂`): the defining integral `∫ kernel·f` is linear in `f`, with each `kernel·fᵢ` integrable (continuous, compact support). The sesquilinearity foundation for threading `stripKMSrvd_pair` over the wedge span.

$$
\mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \forall (\zeta : \mathbb{C}), \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,(f_{1} + f_{2})\,\zeta = \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f_{1}\,\zeta + \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f_{2}\,\zeta
$$

*Proof.* By [`minkowskiDotℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-minkowskidot), [`massShellℂ`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-massshell), [`kernel`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-kernel), [`continuous_kernel_in_x`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-continuous-kernel-in-x). $\square$

<small>Used by [`kmsFun_add_left`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-add-left), [`kmsFun_add_right`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-add-right), [`Krep_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krep-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-krep-add"></a>
**Lemma 379** (`Krep_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L775)</small>

**`Krep` (real axis) is additive in the test function** — `KrepCont_add` at real argument (`KrepCont_ofReal`). Used for the `MemLp` closure of the wedge-test class under `+`/`−` in the span-closure threading.

$$
\mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \forall (\theta : \mathbb{R}), \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,(f_{1} + f_{2})\,\theta = \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f_{1}\,\theta + \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f_{2}\,\theta
$$

*Proof.* By [`KrepCont`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont), [`KrepCont_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [`KrepCont_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-add). $\square$

<small>Used by [`KrepL2_add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-krepl2-add), [`Krep_sub`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krep-sub), [`memLp_Krep_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krep-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-krep-sub"></a>
**Lemma 380** (`Krep_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L783)</small>

**`Krep` (real axis) respects subtraction** — `Krep m (f₁−f₂) = Krep m f₁ − Krep m f₂` (from `Krep_add`).

$$
\mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \forall (\theta : \mathbb{R}), \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,(f_{1} - f_{2})\,\theta = \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f_{1}\,\theta - \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f_{2}\,\theta
$$

*Proof.* By [`Krep_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krep-add). $\square$

<small>Used by [`KrepL2_sub`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-krepl2-sub), [`memLp_Krep_sub`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krep-sub).</small>

<a id="d-qiqth-fock-wedgeanalyticity-memlp-krep-add"></a>
**Lemma 381** (`memLp_Krep_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L793)</small>

**`MemLp` closure under addition**: `MemLp (Krep m (f₁+f₂)) 2` from `MemLp (Krep m fᵢ) 2`, via `Krep_add` (`Krep(f₁+f₂)=Krep f₁+Krep f₂`) + `MemLp.add`. The additive companion of `memLp_Krep_sub`; together they make the nice one-particle vectors `{KrepL2 f}` closed under `±`, i.e. an ℝ-subspace.

$$
\mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f_{1})\,2\,\mathrm{vol} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f_{2})\,2\,\mathrm{vol} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,(f_{1} + f_{2}))\,2\,\mathrm{vol}
$$

*Proof.* By [`Krep_add`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krep-add). $\square$

<small>Used by [`KrepL2_add`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-krepl2-add).</small>

<a id="d-qiqth-fock-wedgeanalyticity-memlp-krep-sub"></a>
**Lemma 382** (`memLp_Krep_sub`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L804)</small>

**`MemLp` closure under subtraction**: `MemLp (Krep m (f₁−f₂)) 2` from `MemLp (Krep m fᵢ) 2`, via `Krep_sub` (`Krep(f₁−f₂)=Krep f₁−Krep f₂`) + `MemLp.sub`.

$$
\mathrm{Continuous}\,f_{1} \to \mathrm{HasCompactSupport}\,f_{1} \to \mathrm{Continuous}\,f_{2} \to \mathrm{HasCompactSupport}\,f_{2} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f_{1})\,2\,\mathrm{vol} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f_{2})\,2\,\mathrm{vol} \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,(f_{1} - f_{2}))\,2\,\mathrm{vol}
$$

*Proof.* By [`Krep_sub`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krep-sub). $\square$

<small>Used by [`kmsFun_sub_left`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-left), [`kmsFun_sub_right`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-kmsfun-sub-right), [`KrepL2_sub`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-krepl2-sub), [`norm_kmsFun_sub_le`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-norm-kmsfun-sub-le).</small>

<a id="d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine-closed"></a>
**Lemma 383** (`memLp_KrepCont_affine_closed`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Fock/WedgeAnalyticity.lean#L814)</small>

**Affine-argument `L²` membership on the CLOSED strip** `Im c₀ ∈ [0,π]`. Extends `memLp_KrepCont_affine` to the two boundary heights: at `Im c₀ = 0` the slice is a real-axis translate `Krep m f(·+Re c₀)` (`KrepCont_ofReal`), at `Im c₀ = π` it is the conjugate `conj(Krep m f(·+Re c₀))` (`KrepCont_add_pi_I`, `MemLp.star`) — both in `L²` via the `MemLp (Krep m f) 2` hypothesis; the interior is `memLp_KrepCont_affine`. This supplies the edge `L²` slices needed to integrate the `kmsFun` integrand up to the boundary.

$$
0 < m \to \forall \{f : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V} \to \mathbb{C}\}, \mathrm{Continuous}\,f \to \mathrm{HasCompactSupport}\,f \to \forall \{\delta : \mathbb{R}\}, 0 < \delta \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), f\,x \ne 0 \to \delta \le x\,1 - x\,0 \wedge \delta \le x\,1 + x\,0) \to (\forall (x : \href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-v}{V}), (\mathrm{starRingEnd}\,\mathbb{C})\,(f\,x) = f\,x) \to \mathrm{MemLp}\,(\href{/browser/qiqth-fock-localization#d-qiqth-fock-localization-krep}{K}\,m\,f)\,2\,\mathrm{vol} \to \forall \{c_{0} : \mathbb{C}\}, 0 \le c_{0}.\mathrm{im} \to c_{0}.\mathrm{im} \le \pi \to \mathrm{MemLp}\,(\lambda \theta \mapsto \href{/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont}{K_{\mathbb{C}}}\,m\,f\,(\theta + c_{0}))\,2\,\mathrm{vol}
$$

*Proof.* By [`KrepCont_ofReal`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-ofreal), [`KrepCont_add_pi_I`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-krepcont-add-pi-i), [`memLp_KrepCont_affine`](/browser/qiqth-fock-wedgeanalyticity#d-qiqth-fock-wedgeanalyticity-memlp-krepcont-affine). $\square$

<small>Used by [`integrable_kmsFun_integrand_closed`](/browser/qiqth-fock-boostkms#d-qiqth-fock-boostkms-integrable-kmsfun-integrand-closed).</small>

---
<small>[← all sections](/browser) · [← SchwartzDecay](/browser/qiqth-fock-schwartzdecay) · [WienerL2 →](/browser/qiqth-fock-wienerl2) </small>