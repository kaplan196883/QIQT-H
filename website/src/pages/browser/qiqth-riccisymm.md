---
layout: ../../layouts/Deep.astro
title: QIQTH.RicciSymm
eyebrow: RicciSymm · section of the QIQT-H book
description: QIQTH.RicciSymm — definitions, lemmas and theorems with explanations and proofs, from the QIQT-H Lean development.
---

<small>[← all sections](/browser) · [← RelEntPositivity](/browser/qiqth-relentpositivity) · [PVM →](/browser/qiqth-spectral-pvm) </small>

<small>RicciSymm · entries 584–585 of 1000</small>

<a id="d-qiqth-curvature-lowered-riemann-pair-symm"></a>
**Lemma 584** (`lowered_riemann_pair_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RicciSymm.lean#L21)</small>

**Pair-symmetry of the lowered Riemann tensor** `R_{abcd} = R_{cdab}` (with `R_{pqrs} = ∑α g_{pα}R^α_{qrs}`). The classical algebraic consequence of: first-pair antisymmetry (`lowered_riemann_antisymm`), last-pair antisymmetry (`riemann_antisymm`), and the first Bianchi identity (`riemann_first_bianchi`).  Proof: sum the Bianchi identity over the four cyclic first-index placements; the cross terms cancel by the antisymmetries, leaving `2(R_{abcd} − R_{cdab}) = 0`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (a b c d : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \sum_{\alpha} g_{{a}{\alpha}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\alpha\,b\,c\,d\,x = \sum_{\alpha} g_{{c}{\alpha}}({x}) \cdot \href{/browser/qiqth-curvature#d-qiqth-curvature-riemann}{\mathrm{Riem}}\,g\,\mathrm{gi}\,\alpha\,d\,a\,b\,x
$$

*Proof.* By [`riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-riemann-antisymm), [`riemann_first_bianchi`](/browser/qiqth-curvature#d-qiqth-curvature-riemann-first-bianchi), [`lowered_riemann_antisymm`](/browser/qiqth-curvature#d-qiqth-curvature-lowered-riemann-antisymm). $\square$

<small>Used by [`ricci_symm`](/browser/qiqth-riccisymm#d-qiqth-curvature-ricci-symm).</small>

<a id="d-qiqth-curvature-ricci-symm"></a>
**Lemma 585** (`ricci_symm`). &nbsp;<small>[source ↗](https://github.com/kaplan196883/QIQT-H/blob/main/lean/mathlib/QIQTH/RicciSymm.lean#L84)</small>

** Ricci symmetry `R_{σν} = R_{νσ}`** — discharges `hric_symm`.  Write the Ricci tensor as the `gi`-raised lowered-Riemann trace (`ricci_eq_trace`), apply the pair-symmetry of the lowered Riemann (`lowered_riemann_pair_symm`) termwise, then reconcile by `Finset.sum_comm` + symmetry of `gi`.

$$
(\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g_{{a}{b}}({y}) = g_{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), g^{{a}{b}}({y}) = g^{{b}{a}}({y})) \to (\forall (y : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}) (a b : \mathrm{Fin}\,n), \sum_{\sigma} g_{{a}{\sigma}}({y}) \cdot g^{{\sigma}{b}}({y}) = \delta_{ab}) \to (\forall (a b : \mathrm{Fin}\,n), ({\lambda y \mapsto g_{{a}{b}}({y})})\in C^{\infty}) \to (\forall (a b c : \mathrm{Fin}\,n), ({\lambda y \mapsto \href{/browser/qiqth-curvature#d-qiqth-curvature-christoffel}{\Gamma^{{a}}_{{b}{c}}({y})}})\in C^{\infty}) \to \forall (\sigma \nu : \mathrm{Fin}\,n) (x : \href{/browser/qiqth-curvature#d-qiqth-curvature-point}{M^{{n}}}), \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\sigma}{\nu}}({x})} = \href{/browser/qiqth-curvature#d-qiqth-curvature-ricci}{R_{{\nu}{\sigma}}({x})}
$$

*Proof.* By [`riemann`](/browser/qiqth-curvature#d-qiqth-curvature-riemann), [`lowered_riemann_pair_symm`](/browser/qiqth-riccisymm#d-qiqth-curvature-lowered-riemann-pair-symm). $\square$

<small>Used by [`qiqt_bekenstein_gives_gr`](/browser/qiqth-qiqttogr#d-qiqth-qiqttogr-qiqt-bekenstein-gives-gr).</small>

---
<small>[← all sections](/browser) · [← RelEntPositivity](/browser/qiqth-relentpositivity) · [PVM →](/browser/qiqth-spectral-pvm) </small>