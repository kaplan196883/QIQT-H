# RECENTER CAMPAIGN — the 2-point / all-base-point parametrix (unconditional a₁=R/6)

Commissioned by the user 2026-07-30 (chose "Commission recenter campaign" at the honest checkpoint).
Goal: discharge the single terminal primitive `hEboundW` (the width-2 residual bound for ALL base points q),
turning the conditional a₁=R/6 (trueKernel_diagonal_a1_eq_R6) into UNCONDITIONAL.

## The wall (Step-1 finding, 6678447a)
- The repo HAS arbitrary-center machinery: `ExpMap.expMap g gi hC p v`, `PullbackMetric.expPullbackMetric g gi hC p = exp_p^*g`,
  arbitrary-center RNC gauge jets (g̃(0)=g(p)=δ, ∂g̃(0)=0, Γ̃(0)=0, symmetry, smooth inverse, closed ∂²g̃(0)).
- BUT `expPullbackMetric` is only `ContDiffOn ℝ 2` on the exp-ball (SHARP: fderiv exp costs one order), while the whole C4c
  far-field residual chain (`near_uncutResidual_gaussianWide_ball`, cutoff/annulus bricks) demands `ContDiff ℝ ⊤`-global.
- So the recenter needs: (A) a FINITE-REGULARITY refactor of the residual chain (⊤-global → ContDiffAt/ContDiffOn 2 on a nbhd/ball),
  then (B) connect `expPullbackMetric`'s q-centered gauge jets into the (now finite-reg) chain, then (C) the injectivity-ball
  cutoff (χ supported where the q-chart is valid; beyond it χ=0 so no cross-chart far-field), then (D) assemble hEboundW ∀q.
- Precedent: finite-reg `PdiffAt` extractors at `ContDiffAt ℝ 2` ALREADY exist (PullbackMetric.lean:1527, RNCExpansion.lean:659, at 0).

## Bricks (R-series)
- R1 [NEXT] laplaceBeltrami_mul_C2 — Δ_g(fh)=fΔ_gh+hΔ_gf+2gⁱʲ∂ᵢf∂ⱼh from `ContDiffAt ℝ 2 f x`+`ContDiffAt ℝ 2 h x`+metric-symm-at-x
  (finite-reg version of laplaceBeltrami_mul), + the general-x ContDiffAt-2 PdiffAt extractors (generalize the existing at-0 ones).
- R2 finite-reg pd_pd_mul / pd_mul chain + finite-reg near-diagonal residual slice (residualN0_local_baseKernelW_slice at ContDiffAt 2).
- R3 finite-reg cutoff-residual + annulus bounds (weaken CutoffResidualGlobalBound / CutoffAnnulusBounds / ParametrixHAnnulusBounds to ContDiffOn 2 on ball).
- R4 connect expPullbackMetric q-centered gauge jets → the finite-reg residual chain hypotheses (per base point q).
- R5 injectivity-ball cutoff: 2-point χ(p,q) supported in {dist<inj}, H̃=χ·H on the q-chart, residual vanishes beyond.
- R6 assemble: q-centered hEbound for all q ⟹ hEboundW via hEboundW_of_uniform_perBasePoint (6678447a) ⟹ discharge hInt/convergence ⟹ unconditional a₁=R/6.
Decompose honestly; checkpoint at each genuine sub-wall. a₁=R/6 NOT claimed until R6.

## Progress
- R1 ✅ (`pending-hash`) LaplaceBeltramiFiniteReg.lean: laplaceBeltrami_mul_C2 + pd_pd_mul_C2 + PdiffAt_of_contDiffAt (ContDiffAt 1⟹PdiffAt) + PdiffAt_pd_of_contDiffAt (ContDiffAt 2⟹PdiffAt(pd·)). Full ContDiffAt 2, no carried hyps, metric enters only as values (no metric-reg hyp). [AF] std-3. Extractors reusable by R2+. NEXT R2 = finite-reg near-diagonal residual slice + the ContDiffOn 2 → ContDiffAt 2 interior bridge (ContDiffOn.contDiffAt + IsOpen.mem_nhds) so the C² Leibniz rules apply to the actual pullback-metric residual.
- R2 ✅ CutoffResidualFiniteReg.lean: cutoffResidual_global_gaussianWide_bound_C2 (far-field cutoff residual, hH ∞→ContDiffAt 2 H via laplaceBeltrami_mul_C2; same conclusion, all carries genuine) + contDiffAt_two_of_contDiffOn_two bridge (ContDiffOn 2 + IsOpen + mem → ContDiffAt 2, feeds expPullbackMetric into the chain). [AF] std-3. NEXT R3 = near-diagonal residual slice residualN0_local_baseKernelW_slice / near_uncutResidual_gaussianWide_ball at finite regularity (RNC 2-jet — HARDER: derives hEnear rather than carrying it, reproves the 2nd-order Taylor/parametrix expansion without C^∞ jets).
