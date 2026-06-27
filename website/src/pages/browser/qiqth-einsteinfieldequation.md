---
layout: ../../layouts/Deep.astro
title: QIQTH.EinsteinFieldEquation
eyebrow: EinsteinFieldEquation · section of the QIQT-H book
description: QIQTH.EinsteinFieldEquation — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← EinsteinEquationOfState](/browser/qiqth-einsteinequationofstate) · [BoostKMS →](/browser/qiqth-fock-boostkms) </small>

<small>EinsteinFieldEquation · entries 83–93 of 1000</small>

<a id="d-qiqth-curvature-div02"></a>
**Definition 83** (`div02`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L30)</small>

**Raised divergence** `∇^μ X_{μν} = g^{μρ} ∇_ρ X_{μν}` of a `(0,2)` tensor field.

$$
\mathrm{div02}\,n\,g\,\mathrm{gi}\,X\,\nu\,x \;:=\; \sum_{\mu} \sum_{\rho} g^{{\mu}{\rho}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderiv02}{\nabla^{2}}\,g\,\mathrm{gi}\,X\,\rho\,\mu\,\nu\,x
$$

<small>Used by [`div02_add`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02-add), [`div02_scalar_metric`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02-scalar-metric), [`divRiemann_trace_eq`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-divriemann-trace-eq), [`twice_contracted_bianchi`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-twice-contracted-bianchi), [`einstein_field_equation`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation), [`einstein_field_equation_real`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real), [`einstein_field_equation_real_global`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real-global), [`jacobson_einstein_equation_of_state`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-jacobson-einstein-equation-of-state), and 10 more.</small>

<a id="d-qiqth-curvature-div02-add"></a>
**Lemma 84** (`div02_add`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L35)</small>

The raised divergence is additive in the tensor field.

$$
(\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto X\,y\,a\,b)\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto Y\,y\,a\,b)\,\rho\,x) \to \forall (\nu : \mathrm{Fin}\,n), \href{/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a b \mapsto X\,y\,a\,b + Y\,y\,a\,b})_{{\nu}}({x})} = \href{/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02}{(\nabla\!\cdot {X})_{{\nu}}({x})} + \href{/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02}{(\nabla\!\cdot {Y})_{{\nu}}({x})}
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`pd_add`](/browser/qiqth-curvature#d-qiqth-curvature-pd-add), [`christoffel`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel), [`covDeriv02`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv02). $\square$

<small>Used by [`einstein_field_equation`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation), [`div02_kgStress_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-eq).</small>

<a id="d-qiqth-curvature-div02-scalar-metric"></a>
**Lemma 85** (`div02_scalar_metric`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L53)</small>

**The divergence of `f·g` is `∂_ν f`.** Metric compatibility kills the connection terms; the inverse metric collapses the contraction. (This is what makes the cosmological-constant term `Λ·g` covariantly constant.)

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to \forall (f : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathbb{R}) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), (\forall (\rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\rho\,x) \to \forall (\nu : \mathrm{Fin}\,n), \href{/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a b \mapsto f\,y \cdot g_{{a}{b}}({y})})_{{\nu}}({x})} = \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({f})({x})}
$$

*Proof.* By [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul), [`christoffel`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel), [`covDeriv02`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv02), [`metric_compat`](/browser/qiqth-curvature#d-qiqth-curvature-metric-compat). $\square$

<small>Used by [`einstein_field_equation`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation), [`div02_kgStress_eq`](/browser/qiqth-kgstressconservation#d-qiqth-curvature-div02-kgstress-eq).</small>

<a id="d-qiqth-curvature-divriemann-trace-eq"></a>
**Lemma 86** (`divRiemann_trace_eq`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L93)</small>

**T3 of the twice-contracted Bianchi**: `∑_ρ ∑_{σν} g^{σν} ∇_ρ R^ρ_{σνλ} = −∇^μ Ric_{μλ}`. Sum `gi_trace_covDerivRiem_ricci` over `ρ` and match `−div02(ricci)` (raised Ricci divergence) term-by-term via `sum_comm` + metric symmetry.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mathrm{lam} : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\rho} \sum_{\sigma} \sum_{\nu} g^{{\sigma}{\nu}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivriem}{\nabla\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\rho\,\sigma\,\nu\,\mathrm{lam}\,x = -(\nabla\!\cdot {\lambda y a b \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})}})_{{\mathrm{lam}}}({x})
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`covDeriv02`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv02), [`gi_trace_covDerivRiem_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderivriem-ricci). $\square$

<small>Used by [`twice_contracted_bianchi`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-twice-contracted-bianchi).</small>

<a id="d-qiqth-curvature-twice-contracted-bianchi"></a>
**Lemma 87** (`twice_contracted_bianchi`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L130)</small>

**The twice-contracted (second) Bianchi identity** `∇^μ Ric_{μλ} = ½ ∂_λ R` — the contracted Bianchi `∇^μ G_{μλ}=0` in trace form. Obtained by contracting `second_bianchi_contracted` with `g^{σν}`: the three traced terms are `∂_λR` (`gi_trace_covDeriv_ricci`), `div02(ricci)` (the Ricci divergence), and `−div02(ricci)` (`divRiemann_trace_eq`), giving `∂_λR − div02 − div02 = 0`. Machine-checked, axiom-free — this **discharges the `bianchi` hypothesis** of `einstein_field_equation`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mathrm{lam} : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), (\nabla\!\cdot {\lambda y a b \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a}{b}}({y})}})_{{\mathrm{lam}}}({x}) = 1/2 \cdot \partial_{{\mathrm{lam}}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-scalarcurv}{R({y})}})({x})
$$

*Proof.* By [`covDeriv02`](/browser/qiqth-curvature#d-qiqth-curvature-covderiv02), [`covDerivRiem`](/browser/qiqth-curvature#d-qiqth-curvature-covderivriem), [`second_bianchi_contracted`](/browser/qiqth-curvature#d-qiqth-curvature-second-bianchi-contracted), [`gi_trace_covDeriv_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-gi-trace-covderiv-ricci), [`divRiemann_trace_eq`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-divriemann-trace-eq). $\square$

<small>Used by [`einstein_field_equation_real`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real).</small>

<a id="d-qiqth-curvature-metric-contraction-trace"></a>
**Lemma 88** (`metric_contraction_trace`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L194)</small>

**The metric–inverse-metric trace is the dimension: `g^{μν} g_{μν} = n`.**  Contracting the metric with its inverse over both indices yields `∑_μ δ^μ_μ = n` (the number of dimensions).

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\mu} \sum_{\nu} g^{{\mu}{\nu}}({x}) \cdot g_{{\mu}{\nu}}({x}) = n
$$

*Proof.* Immediate from the definitions. $\square$

<small>Used by [`hreg_kg`](/browser/qiqth-hregexplicitkg#d-qiqth-curvature-hreg-kg).</small>

<a id="d-qiqth-curvature-einstein-field-equation"></a>
**Lemma 89** (`einstein_field_equation`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L234)</small>

**The Einstein field equation as the thermodynamic equation of state** (Jacobson, PRL 1995), completed: from the post-crux relation + conservation + contracted Bianchi + metric compatibility, `a·T_{μν} = G_{μν} + Λ·g_{μν}` with `Λ := f + ½R` **covariantly constant**. The cited physics (Clausius/Raychaudhuri → `crux`, conservation → `conserv`) and the geometry (contracted Bianchi → `bianchi`) are explicit labeled hypotheses; the closure is machine-checked, axiom-free. `tr` is the scalar curvature `R`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to \forall (T \mathrm{Ric} : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathrm{Fin}\,n \to \mathbb{R}) (f \mathrm{tr} : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathbb{R}) (a : \mathbb{R}) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), (\forall (\rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \to (\forall (\rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,\mathrm{tr}\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto g_{{a}{b}}({y}))\,\rho\,x) \to (\forall (a b \rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,(\lambda y \mapsto \mathrm{Ric}\,y\,a\,b)\,\rho\,x) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a^{\prime} b : \mathrm{Fin}\,n), a \cdot T_{{a^{\prime}}{b}}({y}) = \mathrm{Ric}\,y\,a^{\prime}\,b + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (\nu : \mathrm{Fin}\,n), \href{/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x})} = 0) \to (\forall (\nu : \mathrm{Fin}\,n), \href{/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02}{(\nabla\!\cdot {\mathrm{Ric}})_{{\nu}}({x})} = 1/2 \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\mathrm{tr}})({x})}) \to (\forall (\mu \nu : \mathrm{Fin}\,n), a \cdot T_{{\mu}{\nu}}({x}) = \mathrm{Ric}\,x\,\mu\,\nu - 1/2 \cdot \mathrm{tr}\,x \cdot g_{{\mu}{\nu}}({x}) + (f\,x + 1/2 \cdot \mathrm{tr}\,x) \cdot g_{{\mu}{\nu}}({x})) \wedge \forall (\nu : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda y \mapsto f\,y + 1/2 \cdot \mathrm{tr}\,y})({x})} = 0
$$

*Proof.* By [`pd_add`](/browser/qiqth-curvature#d-qiqth-curvature-pd-add), [`pd_const_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const-mul), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`div02_add`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02-add), [`div02_scalar_metric`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02-scalar-metric). $\square$

<small>Used by [`einstein_field_equation_real`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real).</small>

<a id="d-qiqth-curvature-einstein-field-equation-real"></a>
**Lemma 90** (`einstein_field_equation_real`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L269)</small>

**The Einstein field equation from the thermodynamic equation of state — with the ACTUAL curvature.** Instantiating `einstein_field_equation` at `Ric = ricci g gi`, `R = scalarCurv g gi`, and discharging the `bianchi` hypothesis with the machine-checked `twice_contracted_bianchi` (`∇^μRic=½∂R`). The conclusion now features the **genuine Einstein tensor** `einsteinTensor = Ric − ½R·g`: `a·T_{μν} = G_{μν} + Λ·g_{μν}`,  `Λ := f + ½R` covariantly constant. The ONLY remaining hypotheses are the **cited physics** — the post-crux Clausius relation `a·T = Ric + f·g` (area law + Unruh + Raychaudhuri, supplied as `crux`) and local conservation `∇^μ(aT)=0` (`conserv`). Everything geometric is now proven; axiom-free.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (T : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathrm{Fin}\,n \to \mathbb{R}) (f : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathbb{R}) (a : \mathbb{R}) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), (\forall (\rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a^{\prime} b : \mathrm{Fin}\,n), a \cdot T_{{a^{\prime}}{b}}({y}) = \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({y})} + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (\nu : \mathrm{Fin}\,n), \href{/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x})} = 0) \to (\forall (\mu \nu : \mathrm{Fin}\,n), a \cdot T_{{\mu}{\nu}}({x}) = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + (f\,x + 1/2 \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-scalarcurv}{R({x})}) \cdot g_{{\mu}{\nu}}({x})) \wedge \forall (\nu : \mathrm{Fin}\,n), \partial_{{\nu}}({\lambda y \mapsto f\,y + 1/2 \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-scalarcurv}{R({y})}})({x}) = 0
$$

*Proof.* By [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`PdiffAt_ricci`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-ricci), [`twice_contracted_bianchi`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-twice-contracted-bianchi), [`einstein_field_equation`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation). $\square$

<small>Used by [`einstein_field_equation_real_global`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real-global).</small>

<a id="d-qiqth-curvature-einstein-field-equation-real-global"></a>
**Lemma 91** (`einstein_field_equation_real_global`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L300)</small>

**The Einstein field equation with a GENUINE cosmological constant.** If the cited physics holds at *every* point (`crux` everywhere — it already is — and `conserv` everywhere), then `Λ := f + ½R` is a true **constant** (not just covariantly constant at a point), by `const_of_pd_zero` on the connected domain `Point n`. The Einstein field equation holds globally: `a·T_{μν} = G_{μν} + Λ·g_{μν}`   for a single constant `Λ`. Axiom-free; the only hypotheses are the cited physics + smoothness of `f + ½R`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (T : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathrm{Fin}\,n \to \mathbb{R}) (f : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathbb{R}) (a : \mathbb{R}), (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (\rho : \mathrm{Fin}\,n), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \to (\mathrm{Differentiable}\,\mathbb{R}\,\lambda y \mapsto f\,y + 1/2 \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-scalarcurv}{R({y})}) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a^{\prime} b : \mathrm{Fin}\,n), a \cdot T_{{a^{\prime}}{b}}({y}) = \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({y})} + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (\nu : \mathrm{Fin}\,n), \href{/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x})} = 0) \to \exists \Lambda, \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (\mu \nu : \mathrm{Fin}\,n), a \cdot T_{{\mu}{\nu}}({x}) = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`const_of_pd_zero`](/browser/qiqth-curvature#d-qiqth-curvature-const-of-pd-zero), [`einstein_field_equation_real`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real). $\square$

<small>Used by [`jacobson_einstein_equation_of_state`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-jacobson-einstein-equation-of-state).</small>

<a id="d-qiqth-curvature-crux-of-pernull"></a>
**Lemma 92** (`crux_of_pernull`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L328)</small>

**Phase 3 — wire the per-null Clausius relation to the tensor crux.** This *derives* the `crux` hypothesis (`a·T = R + f·g`) used everywhere above, from the genuinely primitive **per-null Clausius relation**: at each point, the heat tensor `a·T − R` vanishes on the *entire null cone* of the metric `g x`. That per-null relation is exactly Jacobson's premise (the Clausius relation `δQ = TδS` imposed on every local Rindler horizon, with horizon entropy `∝` area). The upgrade from per-null-direction to a tensor is the algebraic crux, here for the **general (curved) Lorentzian metric** via `symmTensor_eq_smul_metric_of_null_general` — the Lorentzian structure enters as the pointwise congruence to Minkowski `g x = Pᵀ·η·P` (Sylvester's law). …

$$
(\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), T_{{a^{\prime}}{b}}({x}) = T_{{b}{a^{\prime}}}({x})) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({x})} = \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{b}{a^{\prime}}}({x})}) \to \forall (P \mathrm{Pinv} : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\lambda a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({x}) - \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({x})}})({v},{v}) = 0) \to \exists f, \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), a \cdot T_{{a^{\prime}}{b}}({x}) = \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({x})} + f\,x \cdot g_{{a^{\prime}}{b}}({x})
$$

*Proof.* By [`symmTensor_eq_smul_metric_of_null_general`](/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-symmtensor-eq-smul-metric-of-null-general). $\square$

<small>Used by [`jacobson_einstein_equation_of_state`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-jacobson-einstein-equation-of-state).</small>

<a id="d-qiqth-curvature-jacobson-einstein-equation-of-state"></a>
**Lemma 93** (`jacobson_einstein_equation_of_state`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/EinsteinFieldEquation.lean#L361)</small>

# THE END-TO-END THEOREM — Jacobson's Einstein equation of state, wired together

`jacobson_einstein_equation_of_state` is the **single** theorem assembling the whole derivation: from the per-null Clausius relation (Jacobson's one physics premise) to the **Einstein field equation with a genuine cosmological constant**, `a·T_{μν} = G_{μν} + Λ·g_{μν}`. It composes the two halves — `crux_of_pernull` (front) and `einstein_field_equation_real_global` (back) — through the proportionality scalar `f`. …

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a b : \mathrm{Fin}\,4), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b : \mathrm{Fin}\,4), ({\lambda y \mapsto g^{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,4), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (T : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}) (a : \mathbb{R}), (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), T_{{a^{\prime}}{b}}({x}) = T_{{b}{a^{\prime}}}({x})) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({x})} = \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{b}{a^{\prime}}}({x})}) \to \forall (P \mathrm{Pinv} : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}} \to \mathrm{Fin}\,4 \to \mathrm{Fin}\,4 \to \mathbb{R}), (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} P_{{i}{k}}({x}) \cdot (P^{-1})_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), \sum_{k} (P^{-1})_{{i}{k}}({x}) \cdot P_{{k}{j}}({x}) = \delta_{ij}) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (i j : \mathrm{Fin}\,4), g_{{i}{j}}({x}) = \sum_{k} \sum_{l} P_{{k}{i}}({x}) \cdot \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-gm}{\eta_{{k}{l}}} \cdot P_{{l}{j}}({x})) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (v : \mathrm{Fin}\,4 \to \mathbb{R}), \href{/browser/qiqth-einsteinequationofstate#d-qiqth-einsteineos-bl}{({g\,x})({v},{v})} = 0 \to ({\lambda a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({x}) - \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({x})}})({v},{v}) = 0) \to (\forall (f : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}} \to \mathbb{R}), (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (a^{\prime} b : \mathrm{Fin}\,4), a \cdot T_{{a^{\prime}}{b}}({y}) = \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{a^{\prime}}{b}}({y})} + f\,y \cdot g_{{a^{\prime}}{b}}({y})) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (\rho : \mathrm{Fin}\,4), \href{/browser/qiqth-curvature#d-qiqth-curvature-pdiffat}{\mathrm{PdiffAt}}\,f\,\rho\,x) \wedge \mathrm{Differentiable}\,\mathbb{R}\,\lambda y \mapsto f\,y + 1/2 \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-scalarcurv}{R({y})}) \to (\forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (\nu : \mathrm{Fin}\,4), \href{/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-div02}{(\nabla\!\cdot {\lambda y a^{\prime} b \mapsto a \cdot T_{{a^{\prime}}{b}}({y})})_{{\nu}}({x})} = 0) \to \exists \Lambda, \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{4}}}) (\mu \nu : \mathrm{Fin}\,4), a \cdot T_{{\mu}{\nu}}({x}) = \href{/browser/qiqth-curvature#d-qiqth-curvature-einsteintensor}{G_{{\mu}{\nu}}({x})} + \Lambda \cdot g_{{\mu}{\nu}}({x})
$$

*Proof.* By [`einstein_field_equation_real_global`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-einstein-field-equation-real-global), [`crux_of_pernull`](/browser/qiqth-einsteinfieldequation#d-qiqth-curvature-crux-of-pernull). $\square$

<small>Used by [`qiqt_bekenstein_gives_gr`](/browser/qiqth-qiqttogr#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr).</small>

---
<small>[← all sections](/browser) · [← EinsteinEquationOfState](/browser/qiqth-einsteinequationofstate) · [BoostKMS →](/browser/qiqth-fock-boostkms) </small>