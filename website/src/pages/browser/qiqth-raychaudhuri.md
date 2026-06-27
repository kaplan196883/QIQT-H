---
layout: ../../layouts/Deep.astro
title: QIQTH.Raychaudhuri
eyebrow: Raychaudhuri · section of the QIQT-H book
description: QIQTH.Raychaudhuri — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← QiqtToGR](/browser/qiqth-qiqttogr) · [RaychaudhuriCongruence →](/browser/qiqth-raychaudhuricongruence) </small>

<small>Raychaudhuri · entries 564–574 of 1000</small>

<a id="d-qiqth-curvature-covderiv2vec"></a>
**Definition 564** (`covDeriv2Vec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L28)</small>

**Second covariant derivative of a vector field**, `∇_μ ∇_ν V^ρ`. Treating `W^ρ_ν := ∇_ν V^ρ` (`= covDerivVec`) as a `(1,1)` tensor: `∇_μ W^ρ_ν = ∂_μ W^ρ_ν + Γ^ρ_{μσ} W^σ_ν − Γ^σ_{μν} W^ρ_σ`.


<small>Used by [`ricci_identity`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-ricci-identity), [`ricci_identity_contracted`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-ricci-identity-contracted), [`covDeriv2Vec_trace`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec-trace), [`raychaudhuri_focusing`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-raychaudhuri-focusing), [`geodesic_leibniz`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-geodesic-leibniz), [`raychaudhuri_geodesic`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-raychaudhuri-geodesic).</small>

<a id="d-qiqth-curvature-pd-covderivvec"></a>
**Lemma 565** (`pd_covDerivVec`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L36)</small>

The partial derivative of `∇_ν V^ρ`, expanded via the product rule: `∂_μ(∇_ν V^ρ) = ∂_μ∂_ν V^ρ + Σ_σ (∂_μ Γ^ρ_{νσ}) V^σ + Σ_σ Γ^ρ_{νσ} ∂_μ V^σ`.

$$
(\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mu \nu \rho : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \partial_{{\mu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\rho}}({y})}})({x}) = \partial_{{\mu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\nu}}({\lambda z \mapsto V\,z\,\rho})({y})}})({x}) + \sum_{\sigma} (\partial_{{\mu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{\sigma}}({y})}})({x}) \cdot V\,x\,\sigma + \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{\rho}}_{{\nu}{\sigma}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\mu}}({\lambda y \mapsto V\,y\,\sigma})({x})})
$$

*Proof.* By [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`pd_add`](/browser/qiqth-curvature#d-qiqth-curvature-pd-add), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul), [`PdiffAt_pd`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-pd). $\square$

<small>Used by [`ricci_identity`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-ricci-identity).</small>

<a id="d-qiqth-curvature-ricci-identity"></a>
**Lemma 566** (`ricci_identity`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L57)</small>

**The Ricci identity** — the commutator of covariant derivatives is the Riemann curvature: `(∇_μ ∇_ν − ∇_ν ∇_μ) V^ρ = R^ρ_{σμν} V^σ`. The geometric heart of Raychaudhuri focusing.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\mu \nu \rho : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\mu\,\nu\,\rho\,x - \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\nu\,\mu\,\rho\,x = \sum_{\sigma} \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\rho\,\sigma\,\mu\,\nu\,x \cdot V\,x\,\sigma
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`pd_comm`](/browser/qiqth-curvature#d-qiqth-curvature-pd-comm), [`christoffel_symm`](/browser/qiqth-curvature#d-qiqth-curvature-christoffel-symm), [`covDerivVec`](/browser/qiqth-curvature#d-qiqth-curvature-covderivvec), [`pd_covDerivVec`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-pd-covderivvec). $\square$

<small>Used by [`ricci_identity_contracted`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-ricci-identity-contracted).</small>

<a id="d-qiqth-curvature-ricci-identity-contracted"></a>
**Lemma 567** (`ricci_identity_contracted`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L93)</small>

**The contracted Ricci identity** — tracing the commutator on the upper index (`ρ = μ`, summed) turns the Riemann tensor into the **Ricci tensor**: `∑_μ (∇_μ∇_ν − ∇_ν∇_μ) V^μ = R_{σν} V^σ`. This is exactly the step that introduces the `R_{μν}` focusing term into the expansion evolution.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\mu} (\href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\mu\,\nu\,\mu\,x - \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\nu\,\mu\,\mu\,x) = \sum_{\sigma} \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})} \cdot V\,x\,\sigma
$$

*Proof.* By [`riemann`](/browser/qiqth-curvature#d-qiqth-curvature-riemann), [`ricci_identity`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-ricci-identity). $\square$

<small>Used by [`raychaudhuri_focusing`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-raychaudhuri-focusing).</small>

<a id="d-qiqth-curvature-expansion"></a>
**Definition 568** (`expansion`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L110)</small>

**The expansion** `θ = ∇_μ V^μ` — the covariant divergence of a vector field.

$$
\mathrm{expansion}\,n\,g\,\mathrm{gi}\,V\,x \;:=\; \sum_{\mu} \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\mu}}{}^{{\mu}}({x})}
$$

<small>Used by [`qiqt_gr_freefield_complete`](/browser/qiqth-qiqtgrcomplete#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete), [`qiqt_gr_freefield_complete_covCong`](/browser/qiqth-qiqtgrcovcong#d-qiqth-wedgekmstogr-qiqt-gr-freefield-complete-covcong), [`qiqt_gr_freefield_localized'`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield-localized), [`qiqt_gr_freefield_nullEnergy`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield-nullenergy), [`qiqt_gr_freefield_geom`](/browser/qiqth-qiqtgrfreefield#d-qiqth-wedgekmstogr-qiqt-gr-freefield-geom), [`qiqt_gr_freefield_gaussian`](/browser/qiqth-qiqtgrgaussian#d-qiqth-wedgekmstogr-qiqt-gr-freefield-gaussian), [`qiqt_gr_ppwave`](/browser/qiqth-qiqtgrppwave#d-qiqth-wedgekmstogr-qiqt-gr-ppwave), [`qiqt_gr_freefield_thermo`](/browser/qiqth-qiqtgrthermo#d-qiqth-wedgekmstogr-qiqt-gr-freefield-thermo), and 8 more.</small>

<a id="d-qiqth-curvature-covderiv2vec-trace"></a>
**Lemma 569** (`covDeriv2Vec_trace`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L115)</small>

**Covariant derivative commutes with contraction** (the geodesic-direction Γ terms cancel by torsion-freeness): the trace `∑_μ ∇_ν ∇_μ V^μ` is just the ordinary derivative of the expansion, `∂_ν θ`. This is what turns `∇_ν(∇_μ V^μ)` into `∂_ν θ` in the Raychaudhuri derivation.

$$
(\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\mu} \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\nu\,\mu\,\mu\,x = \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-expansion}{\theta({y})}})({x})
$$

*Proof.* By [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`add`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-add), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`PdiffAt_pd`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-pd), [`covDerivVec`](/browser/qiqth-curvature#d-qiqth-curvature-covderivvec). $\square$

<small>Used by [`raychaudhuri_focusing`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-raychaudhuri-focusing).</small>

<a id="d-qiqth-curvature-raychaudhuri-focusing"></a>
**Lemma 570** (`raychaudhuri_focusing`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L134)</small>

**The Raychaudhuri focusing equation.** Contracting the (contracted) Ricci identity with `V` gives the evolution of the expansion `θ` along `V`, with the **Ricci focusing term `−R_{σν}V^σV^ν`** made explicit:

`V^ν ∂_ν θ = Σ_{μν} V^ν ∇_μ∇_ν V^μ − R_{σν} V^σ V^ν`.

This is Jacobson's focusing step (the geometry of his front half). For a *geodesic* `V` (`V^σ∇_σV^μ=0`) the first right-hand term equals `−(∇_μV^ν)(∇_νV^μ)` (the `−½θ²−σ²` shear part); that geodesic simplification is the remaining (Leibniz) polish. Holds for any vector field.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\nu} V\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-expansion}{\theta({y})}})({x}) = \sum_{\nu} \sum_{\mu} V\,x\,\nu \cdot \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\mu\,\nu\,\mu\,x - \sum_{\nu} \sum_{\sigma} \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})} \cdot V\,x\,\sigma \cdot V\,x\,\nu
$$

*Proof.* By [`ricci_identity_contracted`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-ricci-identity-contracted), [`covDeriv2Vec_trace`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec-trace). $\square$

<small>Used by [`raychaudhuri_geodesic`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-raychaudhuri-geodesic).</small>

<a id="d-qiqth-curvature-geodesic-divergence-leibniz"></a>
**Lemma 571** (`geodesic_divergence_leibniz`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L162)</small>

**Partial-Leibniz of the geodesic acceleration.** For a geodesic vector field `V` (`Σ_ν V^ν ∇_ν V^μ = 0` as a field), the divergence of the acceleration vanishes, expanded by the product rule: `Σ_ν (∂_μ V^ν · ∇_ν V^μ + V^ν · ∂_μ(∇_ν V^μ)) = 0`. The step that lets `Σ V^ν∇_μ∇_νV^μ` be rewritten as `−(∇_μV^ν)(∇_νV^μ)` (the `−½θ²−σ²` shear part).

$$
(\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (\mu : \mathrm{Fin}\,n), \sum_{\nu} V\,y\,\nu \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})} = 0) \to \forall (\mu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\nu} (\href{/browser/qiqth-curvature#d-qiqth-curvature-pd}{\partial_{{\mu}}({\lambda y \mapsto V\,y\,\nu})({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({x})} + V\,x\,\nu \cdot \partial_{{\mu}}({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})}})({x})) = 0
$$

*Proof.* By [`PdiffAt`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat), [`pd_const`](/browser/qiqth-curvature#d-qiqth-curvature-pd-const), [`PdiffAt_of_contDiff`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-of-contdiff), [`mul`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-mul), [`add`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-add), [`PdiffAt_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-sum), [`pd_sum`](/browser/qiqth-curvature#d-qiqth-curvature-pd-sum), [`pd_mul`](/browser/qiqth-curvature#d-qiqth-curvature-pd-mul), [`PdiffAt_pd`](/browser/qiqth-curvature#d-qiqth-curvature-pdiffat-pd). $\square$

<small>Used by [`geodesic_leibniz`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-geodesic-leibniz).</small>

<a id="d-qiqth-curvature-geodesic-leibniz"></a>
**Lemma 572** (`geodesic_leibniz`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L186)</small>

**Geodesic Leibniz identity.** For a geodesic field `V`, the Raychaudhuri second-derivative term is the shear/expansion quadratic: `Σ_{νμ} V^ν ∇_μ∇_ν V^μ = − Σ_{μν} (∇_μ V^ν)(∇_ν V^μ)`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (\mu : \mathrm{Fin}\,n), \sum_{\nu} V\,y\,\nu \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})} = 0) \to \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\nu} \sum_{\mu} V\,x\,\nu \cdot \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec}{\nabla^{2}}\,g\,\mathrm{gi}\,V\,\mu\,\nu\,\mu\,x = -\sum_{\mu} \sum_{\nu} \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({x})}
$$

*Proof.* By [`pd`](/browser/qiqth-curvature#d-qiqth-curvature-pd), [`geodesic_divergence_leibniz`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-geodesic-divergence-leibniz). $\square$

<small>Used by [`raychaudhuri_geodesic`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-raychaudhuri-geodesic).</small>

<a id="d-qiqth-curvature-raychaudhuri-geodesic"></a>
**Lemma 573** (`raychaudhuri_geodesic`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L239)</small>

**The Raychaudhuri equation** (geodesic congruence), in Jacobson's exact form:

`V^ν ∂_ν θ = − (∇_μ V^ν)(∇_ν V^μ) − R_{σν} V^σ V^ν`.

The expansion `θ` of a geodesic congruence focuses, driven by the shear/expansion quadratic `−(∇V)(∇V)` (Jacobson's `−½θ²−σ²`, the term he *neglects* near a stationary horizon) and the **Ricci focusing term `−R(V,V)`** (the term he *uses*). Assembled from `raychaudhuri_focusing` and `geodesic_leibniz`. **The full geometry of Jacobson's front half is now machine-checked, axiom-free.**

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (\mu : \mathrm{Fin}\,n), \sum_{\nu} V\,y\,\nu \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})} = 0) \to \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\nu} V\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-expansion}{\theta({y})}})({x}) = -\sum_{\mu} \sum_{\nu} \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({x})} - \sum_{\nu} \sum_{\sigma} \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})} \cdot V\,x\,\sigma \cdot V\,x\,\nu
$$

*Proof.* By [`covDeriv2Vec`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-covderiv2vec), [`raychaudhuri_focusing`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-raychaudhuri-focusing), [`geodesic_leibniz`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-geodesic-leibniz). $\square$

<small>Used by [`raychaudhuri_focusing_at_equilibrium`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-raychaudhuri-focusing-at-equilibrium).</small>

<a id="d-qiqth-curvature-raychaudhuri-focusing-at-equilibrium"></a>
**Lemma 574** (`raychaudhuri_focusing_at_equilibrium`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/Raychaudhuri.lean#L259)</small>

**Leading-order Raychaudhuri focusing at equilibrium — the geometric content of Jacobson's `hFocus`.**  At a moment of *local equilibrium* (a stationary/bifurcation horizon, where the shear–expansion quadratic `(∇_μV^ν)(∇_νV^μ)` vanishes — `θ = σ = ω = 0`, the condition Jacobson imposes), the Raychaudhuri equation collapses to **pure Ricci focusing**:

`V^ν ∂_ν θ = − R_{σν} V^σ V^ν`   (i.e. …

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to \forall (V : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}} \to \mathrm{Fin}\,n \to \mathbb{R}), (\forall (\mu : \mathrm{Fin}\,n), ({\lambda y \mapsto V\,y\,\mu})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (\mu : \mathrm{Fin}\,n), \sum_{\nu} V\,y\,\nu \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({y})} = 0) \to \forall (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\mu} \sum_{\nu} \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\mu}}{}^{{\nu}}({x})} \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-covderivvec}{(\nabla {V})_{{\nu}}{}^{{\mu}}({x})} = 0 \to \sum_{\nu} V\,x\,\nu \cdot \partial_{{\nu}}({\lambda y \mapsto \href{/browser/qiqth-raychaudhuri#d-qiqth-curvature-expansion}{\theta({y})}})({x}) = -\sum_{\nu} \sum_{\sigma} \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})} \cdot V\,x\,\sigma \cdot V\,x\,\nu
$$

*Proof.* By [`raychaudhuri_geodesic`](/browser/qiqth-raychaudhuri#d-qiqth-curvature-raychaudhuri-geodesic). $\square$

<small>Used by [`hFocus_of_raychaudhuri`](/browser/qiqth-qiqttogr#d-qiqth-qiqttogr-hfocus-of-raychaudhuri).</small>

---
<small>[← all sections](/browser) · [← QiqtToGR](/browser/qiqth-qiqttogr) · [RaychaudhuriCongruence →](/browser/qiqth-raychaudhuricongruence) </small>