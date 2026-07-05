# THE HEAT-KERNEL PREFACTOR — the π²-content of the induced-G 12π, derived (P1–P3, then vein exhausts)

**Status:** COMPLETE (2026-07-05) — P1–P3 landed; flat-space vein now EXHAUSTED per the consult. Axiom-free std-3, budget 0. **Loop:** fe280fa3. **Commits LOCAL ONLY** (session no-push).
**Consult:** fable high-reasoning agent a6648d51a04b97602 (2026-07-05) — LOAD-BEARING (case i),
not the decorative a₀ trap; the LAST flat-space increment, vein exhausts after.

## Binding verdict (the honesty boundary)

This is the direct continuation of the a₁ campaign and moves ONE transcendental — the π² in
the (4π)⁻² = 1/(16π²) heat-kernel prefactor, i.e. the entire π-content of the cited 12π
induced-Newton normalization — from CITED to DERIVED. Why it is LOAD-BEARING, not the
decorative a₀ prefactor flagged last consult: standing alone (times a₀) the prefactor feeds
only Λ/cosmological-constant = decorative; **the a₁ campaign is exactly what lets the SAME
prefactor multiply a₁ and land on the R-coefficient's 12π.** The win is deliberately narrow —
derives the π² only; leaves ½, 16π, κ = 1/6, and the species charge b = Σnᵢcᵢ CARRIED/cited —
the SAME magnitude of win as a₁'s 2t nugget (which left κ=1/6 carried). By the repo's own
house style that qualifies as load-bearing.

Physics: 1/(16πG) = ½·(4πs)⁻²|₄·a₁·[∫ds/s² e⁻ˢᵐ²]; at ξ=0 assembles to Λ²/(12π). The only
transcendental is the π in (4π)⁻² (the Gaussian prefactor); ½, 16π, κ=1/6, b are rational or
carried; Λ² is derived (`cutoff_moment`). **DO NOT build the proper-time Γ-integral**: the
physical d=4 integral ∫ds/s² e⁻ˢᵐ² is DIVERGENT (a=−1), regularized by the Λ² cutoff which is
ALREADY discharged; the convergent Γ-integral (Mathlib `integral_rpow_mul_exp_neg_mul_Ioi`,
a>0) reaches only super-renormalizable/decorative a₂ terms. After P1–P3 the flat-space vein
IS EXHAUSTED — everything else (κ=1/6, ½/16π conventions, b, curved-space Seeley–DeWitt, the
numerical value of G) is carried geometry or divergent-regularization, none flat-space-reachable.

Verified Mathlib API: `integral_fintype_prod_volume_eq_pow`/`_eq_prod` (Pi.lean, already used
in gaussianMoment_diag), `integral_gaussian` (∫e⁻ᵇˣ² = √(π/b)), and the repo's `heatDensity_oneD`
(the d=1 prefactor). Connection point: `SakharovRatio.lean:19` (the 12π currently listed
verbatim as "NOT formalized / cited frontier") + `InducedNewtonConstant.effSpeciesN` (/(12π)).

## The increments (new file `QIQTH/HeatKernelDDim.lean`)

- [x] **P1 — the general-d Gaussian prefactor (the derived nugget).**
  `heatDensity_dDim (d)(t)(ht:0<t) : (1/(2π))^d * ∫ k:(Fin d→ℝ), exp(-(t·∑ᵢ (k i)²)) =
  (1/√(4πt))^d`. Route: exp(-(t·∑ k_i²)) = ∏ᵢ exp(-(t·(k i)²)) (Real.exp_sum / exp-of-sum),
  rewrite integrand as product, `integral_fintype_prod_volume_eq_pow` (f y = exp(-(t·y²))) →
  (∫ e⁻ᵗʸ²)^d, then (1/2π)^d·(∫)^d = ((1/2π)·∫)^d = (1/√(4πt))^d via heatDensity_oneD +
  mul_pow. Risk LOW (same machinery as gaussianMoment_diag; only fiddle = exp-sum→prod-exp).
- [x] **P2 — the d=4 specialization.** `heat_prefactor_fourD (t)(ht) :
  (1/(2π))^4 * ∫ k:(Fin 4→ℝ), exp(-(t·∑ᵢ (k i)²)) = 1/(16π²·t²)`. Route: P1 at d=4,
  (√(4πt))⁻¹^4 = (4πt)⁻² = 1/(16π²t²), sqrt algebra. Risk LOW.
- [x] **P3 — the normalization assembly (the a₁-style wire into 12π).**
  `inducedInvG_normalization_assembly (ξ P κ)(hP : P = 1/(16π²))(hκ : κ = 1/6) :
  (16π)*(1/2)*P*(κ-ξ) = (κ-ξ)/(2π)`, corollary at ξ=0 = 1/(12π) (matches SakharovRatio +
  effSpeciesN cited 12π). Fills the 1/16π² slot with the DERIVED prefactor (P2's t-independent
  part), κ=1/6 + 16π + ½ CARRIED — the exact analogue of heat_a1_of_RNC. Proof: field_simp/ring.
  Risk LOW.

## The checkpoint language (verbatim)

HAVE: "The π-transcendental content of the induced-Newton-constant normalization is derived:
the general-d flat-space heat-kernel prefactor (1/√(4πt))^d = (4πt)^{−d/2}
(`heatDensity_dDim`, from the product of d one-dimensional Gaussians), its d=4 value
1/(16π²t²) (`heat_prefactor_fourD`), and the assembly `(16π)·½·(1/16π²)·(1/6−ξ) = (1/6−ξ)/2π`
(= 1/12π at ξ=0, `inducedInvG_normalization_assembly`) — matching the 12π in SakharovRatio and
effSpeciesN. Together with the a₁ campaign (the 2t Gaussian-moment contraction), the entire
flat-space analysis of the induced-G R-coefficient — the (4π)^{−d/2} prefactor AND the a₁
contraction — is machine-checked. This moves the π-content of the cited 12π normalization from
CITED to DERIVED. Axiom-free, std-3."

HAVE NOT: "The win is exactly the π transcendental; the rational/convention factors ½, 16π,
the conformal value κ = 1/6, and the species charge b = Σnᵢcᵢ remain CARRIED/cited, as does
the curved-space Seeley–DeWitt geometry (no Riemannian heat kernel in Mathlib) and the Λ²
cutoff REGULARIZATION SCHEME (the physical d=4 proper-time integral ∫ds/s² e⁻ˢᵐ² is divergent
— carried, with the cutoff algebra already discharged as `cutoff_moment`). This does NOT
compute the numerical value of G, does NOT derive κ or the effective-action conventions, and
does NOT formalize the curved-space heat kernel. After this the flat-space analysis vein is
EXHAUSTED; the numerical-G frontier's remaining content is all carried geometry or
divergent regularization."

## Per-increment discipline

`cd lean/mathlib && ~/.elan/bin/lake build <target>` green; `#print axioms` std-3;
`bash scripts/axiom_budget_check.sh` budget 0; AxiomAudit pins; wire QIQTH.lean; ONE commit
on main with the Co-Authored-By: Claude Opus 4.8 trailer; **LOCAL ONLY — no push until the
user says so**; update this checklist + Progress log AND LEAN_RESULTS_INVENTORY.md; NO sorry;
NEVER claim the numerical value of G, that κ=1/6 or the conventions are derived, a curved-space
heat kernel, or the proper-time integral (divergent) — the π-transcendental ONLY; NEVER claim
an increment too hard (attempt, iterate, checkpoint after a genuine failed attempt with the
error); check sibling jobs (stray website/.tex edits — LEAVE THEM) first; explicit git paths
only (Lean + plan + inventory + audit).

## Progress log

- **2026-07-05** — Scoped (consult: LOAD-BEARING case i — the a₁ campaign flips the prefactor
  from decorative to load-bearing; derives the π² in 16π²/12π; the LAST flat-space increment,
  vein exhausts after; proper-time Γ-integral explicitly NOT built — divergent/decorative).
  Continues the productive heat-kernel vein opened by THE HEAT-KERNEL a₁ campaign (complete).

- **2026-07-05** — **P1–P3 LANDED — CAMPAIGN COMPLETE (green first try).** HeatKernelDDim.lean:
  heatDensity_dDim ((1/2π)^d ∫ exp(-(t∑k²)) = (1/√(4πt))^d — the general-d prefactor from the
  product of d 1-D Gaussians via integral_fintype_prod_volume_eq_pow); heat_prefactor_fourD
  (= 1/(16π²t²)); inducedInvG_normalization_assembly ((16π)·½·(1/16π²)·(κ−ξ) = (κ−ξ)/2π) +
  the ξ=0 corollary = 1/(12π) — matching the cited SakharovRatio/effSpeciesN 12π. THE
  π-TRANSCENDENTAL OF THE INDUCED-G 12π NORMALIZATION IS DERIVED. κ=1/6, ½, 16π, species
  charge b stay carried. **The flat-space analysis vein is now EXHAUSTED** (proper-time
  Γ-integral divergent/decorative; everything else carried geometry or regularization).
  Std-3, budget 0. Per the standing directive the loop continues, but this branch is done.
