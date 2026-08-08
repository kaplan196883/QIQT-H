# JET-4 TOWER — unconditional exp∈C⁴ ⟹ discharge hfd3 ⟹ TRULY UNCONDITIONAL a₁=R/6

User asked "why not (a)?" 2026-07-31 — commissioned. (a) = the ONLY path to truly-unconditional a₁=R/6
(discharge hfd3 = ContDiffOn 1 (fderiv³ exp_p), the sole remaining "carried" hypothesis of the exp side
of the recenter capstone trueKernel_diagonal_a1_recenter).

## KEY FINDING: it's a FAITHFUL MIRROR of the complete jet-3 tower (NOT a research unknown)
The jet-3 tower is COMPLETE in ExpMapContDiff3.lean (~4000 lines), and Rung-3 (expMap_contDiffOn_three,
unconditional, :4713) discharges its `ContDiffOn 1 (fderiv² exp)` hypothesis via:
  expJetD3_two_pt_diff (:4585, Lipschitz of fderiv³exp ⟹ fderiv²exp∈C¹) + expMap_fderiv2_hasFDerivAt
  + contDiffOn_succ_of_fderivWithin → expMap_contDiffOn_three_of_fderiv2_contDiffOn_one.
Rung-4 (discharge hfd3 = ContDiffOn 1 (fderiv³exp)) is the SAME pattern one Fréchet order up, needing the
jet-4 tower (mirror each jet-3 lemma). Templates (jet-3 → jet-4):
- expJet3Rhs (:242) + _apply/_continuousOn/_norm_le (:256-375)  →  expJet4Rhs (4th-variation ODE RHS)
- expJet3Fund_local (:474) / _shifted (:612) / _glue (:814) / expJet3Fund (:996) / _unique/_value_bound  →  expJet4Fund (fundamental solution via IsPicardLindelof)
- expJet3Val_v_two_pt_diff (:4165) [analytic heart, two-point Lipschitz]  →  expJet4Val_v_two_pt_diff
- expJetD3_two_pt_diff (:4585)  →  expJetD4_two_pt_diff
- expMap_fderiv2_hasFDerivAt + Rung-3 capstone  →  expMap_fderiv3_hasFDerivAt + Rung-4 capstone (hfd3 discharged ⟹ expMap_contDiffOn_four UNCONDITIONAL)

## Bricks (J4-series)
- J4-1 ✅ (5e44674e) expJet4Rhs (4th-variation ODE RHS field) + expJet4Rhs_apply + _continuousOn (Icc 0 1) + _norm_le — mirror expJet3Rhs (ExpMapContDiff3.lean:242-375) one order up.
- J4-2 expJet4Fund (fundamental solution): _local + _shifted + _glue + expJet4Fund + _unique + _value_bound + _value_bound_Icc — mirror expJet3Fund chain.
- J4-3 expJet4Val_v_two_pt_diff (analytic heart, two-point Lipschitz ‖R⁴_v(1)−R⁴_w(1)‖≤C‖v−w‖‖h‖‖k‖‖l‖‖m‖) — mirror expJet3Val_v_two_pt_diff.
- J4-4 expJetD4_two_pt_diff — mirror expJetD3_two_pt_diff.
- J4-5 expMap_fderiv3_hasFDerivAt + assemble: fderiv³exp Lipschitz⟹continuous + differentiable ⟹ ContDiffOn 1 (fderiv³exp) = hfd3 ⟹ feed expMap_contDiffOn_four_of_fderiv3_contDiffOn_one (eb8ab4cd) ⟹ expMap_contDiffOn_four UNCONDITIONAL.
  ★ SCOPE REALIZATION (2026-07-31): fderiv³exp = expJetD3 already (via expMap_fderiv2_hasFDerivAt.fderiv). expJetD4_two_pt_diff (J4-4b) gives CONTINUITY of fderiv⁴ (Lipschitz) but NOT differentiability of fderiv³ — that genuinely needs the order-4 QUADRATIC little-o remainder, i.e. the whole order-4 chain mirroring ExpMapContDiff3's ~2000-line order-3 chain: expJet4_residual_bound (mirror :1187) → expJet4_remainder_quadratic_bound (mirror :1605) → _' (mirror :3144) → _unif (mirror :3576) → expMap_fderiv3_hasFDerivAt (mirror expMap_fderiv2_hasFDerivAt :3898). This is the LARGEST remaining jet-tower rung — decompose into J4-5a..J4-5e.
  - J4-5a COMPLETE ✅ (ed0aefe9) ExpJet4Residual.lean: expJet4_residual_hasDerivWithinAt (pointwise residual-ODE identity S=Qw−Qv−R) + expJet4_residual_bound (Grönwall endpoint ‖Qw1−Qv1−R1‖≤ρ·exp Kstar, mirror expJet3_residual_bound:1187). Honest firewall hr/hKstar as order-3. [AF] std-3.
  - J4-5b: expJet4_remainder_quadratic_bound (mirror ExpMapContDiff3:1605) — the deep O(‖m‖²) Faà-di-Bruno cancellation. ⚠ A first attempt landed a TAUTOLOGY (hyp hRes = conclusion; REJECTED, file deleted — NOT committed). The real cancellation is blocked on three genuinely-absent order-4 D⁴F primitives ⟹ decomposed:
    - J4-5b-prereq COMPLETE ✅ (0d78bbb7) ExpJet4Prereq.lean: (1) expJet_fderiv4_lipschitzOnWith (2) geodesicField_D3F_second_order_taylor (D⁴F-Lipschitz input → D³F quadratic Taylor remainder) (3) fderiv4_geodesicField_symm_{ab,bc,cd,cyc} (full S₄). All proved OUTRIGHT, std-3, no tautology.
    - J4-5b-real COMPLETE ✅ (941aa4aa) ExpJet4Remainder.lean (815 lines): expJet4_remainder_quadratic_bound — the FULL 14-term Faà-di-Bruno O(‖m‖²) cancellation DERIVED via a 5-block telescope (Block0 top-var→T14; Block1 pure D³F/D⁴F via geodesicField_D3F_second_order_taylor+fderiv4_symm_cyc→T1/T4/T6/T7; Blocks2-4 D²F cross-terms→remaining 9). ⚠ NON-TAUTOLOGICAL (verified): conclusion DERIVED, carried hyps are strictly lower-order INPUTS only (1st→2nd + 2nd→3rd variation residuals on DIFFERENT quantities, solution Lipschitz, value bounds, ODE data) = exactly the order-3 hFVh/hFVk/hQlip firewall. std-3, no sorry. maxHeartbeats 6400000.
    - J4-5c COMPLETE ✅ (c6a51d89) ExpJet4RemainderP.lean: expJet4_remainder_quadratic_bound' (explicit-factor ≤C·‖h‖‖k‖‖l‖‖m‖², h,k,l-indep witness; same 5-block telescope threaded with factors). std-3, non-tautological.
    - J4-5d = expJet4_remainder_quadratic_bound_unif (mirror ExpMapContDiff3:3576) — discharges J4-5c's carried inputs + calls J4-5c. Input-discharge lemmas: hFP*←expJet2FirstVar_residual_Icc_unif (EXISTS :3474); hQlip←expJet3Val_v_two_pt_Icc_const (EXISTS ExpJet4Val:104); hQlipkl←expJet2_v_two_pt_Icc_unif (EXISTS :3523); hV*←expJet2/3Fund_value_bound_Icc (EXIST). ONLY MISSING = hFQ* (second→third variation residual).
      - J4-5d1 COMPLETE ✅ (1977b674) ExpJet3SecondVarResidual.lean: expJet3SecondVar_residual_Icc_unif (‖Q²_{v+l}(h,k)−Q²_v(h,k)−Q³_v(h,k,l)‖≤C₀·‖h‖‖k‖‖l‖², genuine expJet2Curve/expJet3Curve) — O(‖l‖²) DERIVED via gronwall_vec_residual_Icc + expJet3_remainder_quadratic_bound_unif + expJet3_residual_hasDerivWithinAt. std-3, non-tautological.
      - J4-5d2 COMPLETE ✅ (46d5ca1d) ExpJet4RemainderUnif.lean: expJet4_remainder_quadratic_bound_unif (single up-front ∃C₀ uniform over m/Φ'/h/k/l). STRONGEST non-tautology: hyps = ONLY base ODE data; ALL analytic inputs discharged inside (hFP*/hFQ*/hQlip*/hV*). Bound DERIVED by re-inlining the 5-block cancellation with UNIFORM tube bounds (calling _' gives m-dependent const — same reason order-3 _unif re-inlines). Also landed helper expJet3Val_v_two_pt_Icc_unif. std-3.
    - J4-5e COMPLETE ✅ (31622a4a) ExpMapFDeriv3.lean: expMap_fderiv3_hasFDerivAt (HasFDerivAt (fun w=>fderiv³exp w) (expJetD4…v) v) — exact mirror of expMap_fderiv2_hasFDerivAt:3898 one order up; HasFDerivAt DERIVED via little-o, operator bound from expJet4_remainder_quadratic_bound_unif + expJet4_residual_bound Grönwall + expJetPi. std-3, non-tautological, green first try.
    - J4-5f COMPLETE ✅★★★ (efd56678) ExpMapContDiffFour.lean: expMap_contDiffOn_four — ContDiffOn ℝ 4 (expMap g gi hC p) (ball 0 expRho), hypotheses ONLY (g,gi,hC,p). exp∈C⁴ is now UNCONDITIONAL — the whole jet-4 tower's payoff. std-3. THE JET-4 TOWER IS COMPLETE.
  - J4-6a COMPLETE ✅ (b94102d7) PullbackMetricC3Uncond.lean: expMap_fderiv3_contDiffOn_one (hfd3 UNCONDITIONAL, from expMap_contDiffOn_four via 3× ContDiffOn.fderiv_of_isOpen) + contDiffOn_expPullbackMetric_three_uncond (g̃∈C³ UNCONDITIONAL, no hfd3). std-3.
    ★ CONSUMER MAP: the 4 RNC jet-value facts (hg0/hΓ/hdg0/htr) need only g̃∈C² — ALREADY unconditional. hfd3 sits on the RESIDUAL-regularity branch: #2 christoffel_expPullback_contDiffAt_two (RecenterConnectC3b:68) → #3 hw0_expPullback (RecenterConnectC3c:131) → #4 near_uncutResidual_expPullback_clean (RecenterConnectC3c:219) → #5 cutoffResidual_expPullback_hEboundW (RecenterCutoffC3:97). Chain terminates at #5 (hEboundW_of_perBasePoint_bound takes bounds abstractly).
  - J4-7 COMPLETE ✅ (760153df) RecenterResidualUncond.lean: 4 _uncond wrappers (christoffel_expPullback_contDiffAt_two_uncond, hw0_expPullback_uncond, near_uncutResidual_expPullback_clean_uncond, cutoffResidual_expPullback_hEboundW_uncond) — each drops hfd3, keeps genuine geometric hyps. Residual branch hfd3-FREE end-to-end. std-3.
  - J4-8 COMPLETE ✅ (03da1c8a) RecenterAnnulusUncond.lean: expPullbackMetricInv_continuousOn_of_isUnit (g̃ nondeg on S ⟹ g̃⁻¹ ContinuousOn S) + cutoffResidual_expPullback_hEboundW_uncond2 (DROPS hgi_ann+hLapChi_ann, derived internally, replaced by weaker ContinuousOn residue hgi_cont/hchris_cont). std-3. ⚠ SUB-WALL: g̃-nondeg-on-BALL MISSING (repo has it only at 0; expRho is a CONFINEMENT radius via exists_confined_tube_family, NOT conjugate-point-free — full-ball nondeg needs no-conjugate-points).
  - J4-9 IN FLIGHT: g̃-nondeg on a DEFINITE sub-ball B(0,ρ₀), now reachable via exp∈C⁴: fderiv exp(0) invertible + fderiv exp continuous (exp∈C⁴) ⟹ invertible on nbhd (openness of units); g(p)=I + g continuous ⟹ g nondeg near p ⟹ g̃=Jᵀ(g∘exp)J nondeg on B(0,ρ₀). Covers small annuli (b≤ρ₀) ⟹ discharges hgi_cont/hchris_cont there. ⚠ ExpJacobian* family (Flow/Regularity/Ricci/Rescale) has Jacobian=variational flow + C² entries/det + Raychaudhuri-for-det but NO invertibility — J4-9 adds it near 0.
  - J4-9 COMPLETE ✅ (c815d30d) PullbackMetricNondegNearZero.lean: expPullbackMetric_isUnit_near_zero (g̃ nondeg on B(0,ρ₀) via Units.isOpen) + expPullbackMetricInv_continuousOn_ball. std-3. ρ₀ non-explicit < expRho.
  ★★ STRATEGIC PIVOT (GPT-5.5 consult 2026-07-31): the full-ball no-conjugate-points wall is AVOIDED, not fought. a₁=R/6 is a LOCAL DIAGONAL invariant ⟹ cut the q-centered parametrix off INSIDE B(0,ρ₀) (local radius r<ρ₀ where nondeg holds); cutoff-annulus/far-field ⟹ t^{-N}·exp(-c·r²/t)=O(t^m) ∀m FLAT tail, cannot affect t⁰/t¹ diagonal coeffs. Reframed frontier = local-support parametrix + flat-tail estimates + Levi/Duhamel convergence trio (NO global no-conjugate theorem).
  - J4-10 COMPLETE (ec5b6225) FlatTail.lean: exp_neg_inv_flat (∀t>0, (1/t)^k·exp(-a/t)≤C·t^N, C=(k+N)!/a^(k+N)). std-3. The far-field O(t^N) tool.
  - Then J4-11+ = local-parametrix radius refactor (cutoff support ⊆ B(0,r), r<ρ₀; uniform-small-r for q near p via openness) + hunif (localized wide-Gaussian residual) + hHdiag/hE (concrete local parametrix API) + hcoord (local, widened) + hEmeas (mechanical) + convergence trio (hDuhamel/hCorrHigher; hInter DONE 4bff8b12 — the real wall, later).
  ⚠ a₁=R/6 STILL CONDITIONAL: remaining = convergence trio (hDuhamel via leviSeries_volterra+hInter, hCorrHigher) + geometric wiring (hcoord/hEmeas + the abstract hHdiag/hE + hDH/hDConv/hCH/hCConv on the capstone).
    Then J4-5e(expMap_fderiv3_hasFDerivAt :3898, via opNorm_le_bound + expJetD4) → hfd3 → exp∈C⁴.
  Then J4-5c(_' :3144) → J4-5d(_unif :3576) → J4-5e(expMap_fderiv3_hasFDerivAt mirror :3898, packages via expJetD4) → hfd3 → exp∈C⁴.
- J4-6 discharge hfd3 wherever the recenter chain carries it (R3c-1 contDiffOn_expPullbackMetric_three → g̃∈C³ unconditional → the whole recenter conditional set loses hfd3).
Each brick = a green [AF] std-3 mirror. LONG but every rung is reachable. Then a₁=R/6 loses hfd3 (still conditional on the convergence trio + geometric wiring until those land too).

## Progress
- J4-1 ✅ (5e44674e) ExpJet4Rhs.lean: expJet4Rhs (14-term Faà-di-Bruno RHS) + _apply/_continuousOn/_norm_le, mirror expJet3Rhs. [AF] std-3. Confirmed the tower IS a faithful mirror (14 terms = the one-order-up analog of jet-3's 4).
- (parallel) hInter ✅ (4bff8b12) LeviInterchange.lean: heatConv_leviSeries_interchange — the convergence-trio interchange FULLY discharged; NOT a Mathlib gap (integral_tsum_of_summable_integral_norm + built domination). Reduces trueKernel's hInter carry to hEbound/hEzero/hEmeas. Convergence trio now: hDuhamel (via leviSeries_volterra + this hInter) + hCorrHigher remain.
- J4-2a ✅ ExpJet4Fund.lean: expJet4Fund_local (local PL existence, verbatim mirror of expJet3Fund_local). [AF] std-3. NEXT J4-2b = expJet4Field_continuousOn → expJet4Fund_shifted → _glue → expJet4Fund ([0,1] global capstone, mirror expJet3Fund chain ExpMapContDiff3.lean:581-996).
- J4-2c ✅ ExpJet4FundBounds.lean: expJet4Fund_unique + expJet4Fund_value_bound + _value_bound_Icc (mirror expJet3Fund_unique/_value_bound/_value_bound_Icc). J4-3 prereqs (uniqueness pins witness; value_bound_Icc = M₄ a-priori bound) in place. [AF] std-3. NEXT J4-3 = expJet4Val_v_two_pt_diff (two-point Lipschitz analytic HEART, mirror expJet3Val_v_two_pt_diff:4165 — hardest rung, reuses shared expFund_two_pt_diff_Icc; decompose if huge).
- J4-3 (ingredients) ✅ ExpJet4Val.lean: expJet3Val_v_two_pt_Icc_const (new [0,1]-uniform 3rd-var two-point bound) + expJet4_v_residual_hasDerivWithinAt (residual-ODE identity) + expJet4Val_v_two_pt_diff_gronwall (Grönwall app, carries genuine hrbound). [AF] std-3. Full expJet4Val_v_two_pt_diff NOT closed. NEXT J4-3-remainder = discharge the 51-term ρ₄-telescope (1 [DF]Rw + 5 D⁴F(1+1+1+1) + 24 D³F(2+1+1) + 9 D²F(2+2) + 12 D²F(3+1)): define expJet4VtpConst, prove hrbound (consuming expJet3Val_v_two_pt_Icc_const + expJet3Fund_value_bound_Icc + expJet2_v_two_pt_Icc_const + expJet2Fund_value_bound_Icc + new hD4diff/Kstar4 via clmApply4_norm_le), feed expJet4Val_v_two_pt_diff_gronwall + ring-close → full expJet4Val_v_two_pt_diff. Then J4-4 expJetD4_two_pt_diff → J4-5 hfd3.
- J4-3 COMPLETE ✅ ExpJet4ValFull.lean: expJet4Val_v_two_pt_diff (full 51-term ρ₄-telescope closed inline via 15-group telescope + clm4_diff_eq/regroup14; carries genuine hLipD4F/Kstar4). [AF] std-3. THE HARDEST rung done. NEXT J4-4 = expJetD4_two_pt_diff (lift value two-point-diff to derivative-operator two-point-diff ‖expJetD4_v − expJetD4_w‖≤C‖v−w‖, mirror expJetD3_two_pt_diff ExpMapContDiff3.lean:4585 via π + iterated opNorm_le_bound) → J4-5 hfd3 (expMap_fderiv3_hasFDerivAt + assemble ⟹ ContDiffOn 1 (fderiv³exp)=hfd3 ⟹ expMap_contDiffOn_four_of_fderiv3_contDiffOn_one eb8ab4cd ⟹ exp∈C⁴ UNCONDITIONAL) → J4-6 discharge hfd3 in R3c-1.
- J4-4 (foundation) ✅ ExpJet4D.lean: Layer A expJet3Curve + trilinearity + Layer B expJet4Val + expJet4Val_congr. [AF] std-3. Full expJetD4_two_pt_diff NOT closed — needs J4-4b sub-chain: (1) expJet4Rhs_{add,smul}_{h,k,l,m} (8 source-linearity, absent; via simp[expJet4Rhs_apply,map_add/smul]+abel) → (2) expJet3CurveG + expJet4Val_{add,smul} + expJet4ValG (6 expJet2Curve + 4 expJet3CurveG slots) + _norm_le + multilinearity → (3) expJetD4Inner/expJetD4 (quadrilinear CLM via mkContinuous₂/mkContinuous, mirror expJetD3Inner/expJetD3) → (4) expJetD4_two_pt_diff (project expJet4Val_v_two_pt_diff + 4× opNorm_le_bound). Then J4-5 hfd3.
- J4-4b COMPLETE ✅ ExpJet4DFull.lean (b38c5ea2, 2302 lines): full chain (1)→(4), GOAL expJetD4_two_pt_diff LANDED. (1) 8 matched-Q source-linearity (simp+abel, no regroup14 needed) (2) expJet4Val/expJet3CurveG multilinearity + expJet_fderiv4_tube_bddAbove_unif + expJet4ValG(def)+_norm_le+8 multilinearity (3) expJetD4Inner/Mid/expJetD4 quadrilinear CLM (nested mkContinuous₂/mkContinuous) (4) expJetD4_two_pt_diff = ‖expJetD4…v−…w‖≤expJet4VtpConst·‖v−w‖ (project expJet4Val_v_two_pt_diff by expJetPi + 4× opNorm_le_bound). [AF] std-3, genuine hyps = expJetD3_two_pt_diff's constants one order up. maxSynthPendingDepth 4, heartbeats up to 6400000. NEXT J4-5.

## POST-JET4 GEOMETRIC WIRING + TWO-POINT PHASE (2026-07-31)
- J4-10 ✅ (ec5b6225) FlatTail.lean exp_neg_inv_flat — far-field O(t^N) tool.
- J4-11 ✅ (4ac02119) AnnulusContinuityWithinRho.lean — within-ρ₀ continuity producers.
- J4-12 ✅ (f3353aec) RecenterCutoffLocal.lean cutoffResidual_expPullback_hEboundW_uncond3 — hgi_cont/hchris_cont DISCHARGED (local-support). Cutoff-residual branch now hyps-only-(g,gi,p)+genuine-residues.
- ★★ 2nd GPT-5.5 consult: NO research wall left. Remaining = TWO-POINT CONSTRUCTION + Duhamel/Levi, all tractable-but-laborious.
  hunif reduces (hEboundW_of_uniform_perBasePoint RecenterReduction:86) to `∀ q τ>0 p, |E τ p q|≤C·gaussDdim(2τ)(p−q)`. Base-point (q) regularity AVOIDABLE — exp_q/g̃_q is the SAME construction at base q ⟹ "uniform in q" = uniform CONSTANTS over compact q-nbhd (bounded geometry).
  - Brick A (HARDEST): uniform local-geometry packet ∃U∋p ∃ρ ∀q∈U (exp_q C⁴ + g̃_q C³ + nondeg on ball ρ + uniform norm bounds) via compactness/bounded geometry.
  - Brick B: uniform residual const B (refactor uncond3 so B=f(uniform metric-jet bounds)).
  - Brick C (easiest, needs exp_q⁻¹): Vmap identification E τ p q = R_q τ (Vmap q p).
  - ⚠ hcoord SAME-WIDTH may be TOO STRONG (blows up τ→0 if bi-Lipschitz c<1) — FIX = capstone width constant (β≥α/c²) or narrower q-Gaussian. CHECK before building toward it.
  - SINGLE HARDEST = Levi/Duhamel convergence (hDuhamel/hCorrHigher) — time-singular convolutions, Gaussian-semigroup, dominated convergence. Substantial Lean, NOT research-grade.
- J4-13 IN FLIGHT = SCOPING: map the two-point phase into concrete ordered sub-bricks (verify exp_q⁻¹/Vmap existence, base-point q-dependence, capstone E/Vmap/hcoord exact shapes, uncond3-B uniformizability, hcoord width issue) → precise J4-14+ plan.

## J4-13 SCOPING RESULT — ordered two-point sub-brick plan (no research wall; Brick A = bottleneck)
Findings: (1) Vmap=exp_q⁻¹ is an ABSTRACT free param, NEVER built (forward expMap + hasStrictFDerivAt_expMap ExpMap.lean:796 exist ⟹ IFT gives inverse). (2) base-point q: per-fixed-point .choose/[irreducible], NO q-uniformity ⟹ Brick A bounded-geometry refactor NEEDED (bottleneck). (3) hcoord SAME-WIDTH gaussDdim(2τ)(Vmap)≤D·gaussDdim(2τ)(p−q) CONFIRMED too strong (unsatisfiable uniform D if geodesic<chart dist); fix H1 = width margin (exploit gaussDdimWide −r²/8τ vs gaussDdim −r²/4τ slack). (4) Levi/Duhamel: hInter DONE, hInt producible, hCorrHigher DISCHARGED (corrHigher_witness TrueKernelA1Reduced:78), hE DISCHARGED (E:=heatOp g gi H); ONLY hDuhamel genuine (parametrix duhamel_principle HeatDuhamel:183 + hDelta δ-IC crux). (5) uncond3 B explicit arithmetic (CutoffResidualFiniteReg:101) over per-q pieces ⟹ uniform-B = Brick A.
Ordered: A uniform local-geometry packet (HARD bottleneck, base-point bounded-geometry; everything funnels through) → B uniform residual const → C1 build Vmap via IFT (MODERATE, foundational, currently UNBUILT) → C2 E-identification → H1 hcoord width-fix + H2 gaussian-comparison (trivial) → hEmeas → hHdiag/D1/D2 (trivial wiring) → D3 hDuhamel (HARD, parametrix duhamel + δ-IC) → Z final assembly (trueKernel_diagonal_a1_eq_R6_residual TrueKernelA1Reduced:153).
Single hardest = Brick A (laborious-not-research). J4-14 = C1 (build Vmap = exp_q⁻¹ local inverse via IFT — foundational, independent of the A bottleneck for fixed q).

## ★★★ 3rd GPT-5.5 CONSULT (2026-07-31) — CRITICAL: LOCALIZE the goal (global ∀q is FALSE for general g)
- J4-16 A1 ✅ (bb18d47a) BoundedGeometry.lean; J4-17 A2 ✅ (a7a54652) BoundedGeometryConfine.lean = geodesic_apriori_confinement_uniform (uniform ρ,C₀ over compact K, FULLY DERIVED via compact-uniform IsPicardLindelof.of_time_independent). The HARD CORE of Brick A is done.
- ⚠⚠ Q1 (load-bearing): the capstone's hunif `∀ q : Point n, |E τ p q|≤B·gaussDdim(2τ)(p−q)` with a SINGLE global B is MATHEMATICALLY FALSE for a general (wild-at-∞) metric g (B_q's jets blow up as q→∞). The honest a₁=R/6 is LOCAL/POINTWISE ⟹ LOCALIZE: restate the concrete instantiation with `q ∈ K` (compact) or fixed q₀. NO a₁=R/6 content lost; NO bounded-geometry hypothesis needed for the local theorem (Option A = add bounded-geometry only if you want global; NOT recommended). ⟹ the honest target = COMPACT-UNIFORM a₁=R/6, for which J4-17's uniform confinement is exactly right.
- Q2 minimal cut: ONE compact-uniform exp-jet PACKAGE lemma (∀q∈K: exp_q on B(0,ρ₀) + confined + D exp_q close to Id + pullback jets bounded) ⟹ all of {M,W,L,Kg,Kc2,Mann,a,b} follow as compact suprema. Free-ish: a,Kg,Kc2,Mann. Genuine uniform work: M,W,L (uniform pullback-metric jets), ρ₀ (common nondeg radius), b (uniform near-zero radius). HARDEST = ρ₀ via a uniform `‖D_v exp_q(v)−Id‖≤A·‖v‖` estimate (NOT a min of pointwise IFT radii) ⟹ ρ₀≤min r (1/2A).
- Honest path: (1) LOCALIZE capstone instantiation to q∈K. (2) uniform confinement (J4-17 ✅). (3) uniform exp-jet package (the real remaining bottleneck = uniform-over-q analogue of the exp regularity). (4) common ρ₀ via ‖D exp−Id‖≤A‖v‖. (5) common b,a. (6) M,W,L,Kg,Kc2,Mann by compact sup. (7) single compact-uniform B ⟹ hunif for q∈K. ⟹ compact-uniform unconditional a₁=R/6.
- J4-18 = the uniform exp-jet package core: uniform ‖D_v exp_q(v)−Id‖≤A·‖v‖ over q∈K,‖v‖≤r ⟹ common nondeg radius ρ₀ (the hardest single input). Substantial (uniform exp-Jacobian control over (q,v)); decompose.

## HONEST REDUCTION ENDPOINT (2026-07-31, after J4-21) + grind into (J) per feedback_close_all_gaps
- J4-18..J4-21 landed: common nondeg radius (930fa71c) · hjet-diff discharged→(I1)+(I2) (ca40bc9b) · ODE-uniqueness flow-bridge F=expMap on overlap (cda21bee) · (I2)→one joint-continuity input (J) (d09d25a8).
- ★ The compact-uniform (local) a₁=R/6 exp-jet package is now REDUCED to TWO clean minimal inputs: (I1) uniform injectivity radius r≤expRho q over K [dissolves under re-architect onto F, which has uniform domain ρ]; (J) joint 2nd-order smooth-dependence continuity `(q,v)↦‖fderiv²(exp_q)v‖` on K×ball. Both = genuine Mathlib gaps: Mathlib ODE has NO higher smooth-dependence-on-IC (only Picard-Lindelöf+Grönwall); repo GeodesicSmoothDep is 1st-order only (geodesicVariation_exists), explicitly "does NOT build the 2nd-order Jacobi eqn (L2)". Repo tools available: geodesicVariation_exists (1st-order), geodesicVariation_hswap, decay_order_two_remainder_convex (general 2nd-order Taylor remainder).
- ⚖ HONEST: commissioned target (exp∈C⁴/hfd3) DONE unconditional; remaining local a₁=R/6 = (J) [2nd-order smooth-dependence tower] + re-architect onto F + hDuhamel + localized assembly = LARGE multi-session. Per feedback_close_all_gaps (grind large walls to full closure, don't stop at conditional milestone), GRINDING (J) as a new sub-tower (the 2nd-order Jacobi / joint-C² geodesic-flow development, uniform over base), decomposed like the jet-4 tower.
- J4-22 = SCOPE the 2nd-order smooth-dependence tower (extend GeodesicSmoothDep 1st-order → joint 2nd-order for (J); decompose into sub-bricks: christoffel 2-jet uniform bounds, the 2nd variational/Jacobi equation, its existence+continuity, joint (q,v) continuity of fderiv²(exp)) + land the first reachable sub-brick.

- **J4-35** (bce4f86c) `AutonomousSmoothDep.lean` — abstract smooth-dependence engine for autonomous C2 field Phi:E->E (6 thms, ns QIQTH.AutonomousDep): residual ODE + residual Gronwall + IC-deriv existence (cond+uncond via hNb discharge from C2 bound) + two-point flow-Lipschitz + quadratic-remainder discharge. Near-verbatim generalization of the PROVEN geodesicVariation_exists. std-3, budget 0. THE largest analytic component of (h3a). Remaining (h3a) = mechanical: apply to G(Y,V)=(F(Y),DF(Y)V).
- **J4-36** (IN FLIGHT) `JacobiOperatorBaseDeriv.lean` — apply the engine to the doubled tangent field G ⟹ (h3a) = HasFDerivAt of Jacobi solution operator in base IC ⟹ close hid ⟹ discharge (J).

- **J4-37** (JacobiOperatorFDeriv.lean) — (c)+(d) analytic BRIDGE J4-36-scalar-core → POINTWISE hid: block formula → doubled second-factor 2nd-var ODE → endpoint=Zf (secondVariation_endpoint_unique) → directional⟹CLM-value → hid_of_doubled_data (= the hid predicate, DERIVED). (h3a) analytic firewall DISSOLVED pointwise. (J) reduced to uniform-SUPPLY residual: doubled families + hlink + hdiff over compact K ⟹ ∀q∈K hid ⟹ feed expMap_common_nondeg_radius ⟹ (J). Uses only existing machinery. [AF] std-3.

- **J4-38** (JacobiUniformSupply.lean) — supply (S3) hdiff DERIVED: expMap_jetMap_differentiableAt{,_uniform} (DifferentiableAt (fun w=>fderiv(expMap q) w) v from expMap_contDiffOn_four via ContDiffAt.fderiv_right; uniform ∀q∈K ∀v∈closedBall 0 r<expRho). (S3) off the list. (J) reduced to entangled (S1)+(S2): doubled families as ONE doubledField integral curve (geodesic⊗Jacobi, confined) + hlink, uniform over K ⟹ ∀q∈K hid ⟹ (J). [AF] std-3.

- **J4-39** (JacobiDoubledFamily.lean) — the CLOSE bridge: expMap_common_nondeg_radius_of_doubled_supply DISCHARGES the opaque hid from gate (J). Specializes Fam:=expMap, DERIVES hid over K via hid_of_doubled_data, chains to expMap_common_nondeg_radius_of_velocity_ode_data. Concl = ∃ρ₀>0 ∀q∈K IsUnit(fderiv(expMap q) v) = (J). No hid/HasFDerivAt/hbnd carried. (J) reduced to the (S1)+(S2) doubled-family SUPPLY construction (carried as genuine ODE data). GPT-5.5-confirmed non-circular. [AF] std-3.

- **J4-40** (DoubledFamilyConstruction.lean) — reuse cores (doubledField_prod_hasDerivAt = hYode is product-rule repackaging of geodesic-flow tensor Jacobi-field; doubledField_equilibrium; doubledField_prod_mem_prod) + CRITICAL FINDING: the J4-35..J4-39 doubled-family supply is UNSATISFIABLE for a!=0 (hmem forall s in compact S vs hIC Y s 0 = base + s.p unbounded). Theorems true+std-3 but reduction illusory as quantified. FIX = bounded-s reformulation (forall s:R -> forall s in Icc(-sigma)sigma). J4-41 = the reformulation. [AF] std-3.

- **J4-41** (AutonomousSmoothDep, JacobiOperatorBaseDeriv, JacobiOperatorFDeriv, JacobiDoubledFamily) — BOUNDED-s reformulation RESOLVES the J4-40 unsatisfiability: every forall s:R supply binder (hmem/hIC/hYode/hlink/hNb) -> forall s in Icc(-sigma)sigma (sigma>0 threaded). Supply now SATISFIABLE (bounded IC segment + Gronwall spread fits compact ball). Same theorem names; HasDerivAt...0 preserved (littleO on nhds 0 via min-radius/Icc_mem_nhds). Full chain green, 5 tops std-3. Doubled-family construction now assemblable. [AF] std-3.

- **J4-42** (GenericJacobiExists.lean) — (J1) the hard residual PROVED: generic [0,1] linear-ODE (Jacobi) existence over ARBITRARY continuous base curve. linODE_exists_on_Icc (ContinuousOn A [0,1]+seed => exists J solving J prime = A.J) via N>2sup|A| nodes + prefix-induction gluing of single-subinterval Picard-Lindelof (single-[0,1] impossible for Lip>=1, GPT-5.5 confirmed). Two-sided linODE_exists_hasDerivAt_Icc + geodesic specializations geodesicJacobi_exists_*. (J) not self-contained: (J2) doubled-family assembly remains. [AF] std-3.

- **J4-43** (DoubledFamilyAssembly.lean) — (A1) confined_doubled_family_exists: the per-seed confined doubled integral-curve HEART of (S1). DERIVED welding geodesic_apriori_confinement_uniform (P) + geodesicJacobi_exists_on_Icc (J) + doubledField_prod_hasDerivAt. Hyps=hC+IsCompact K. ⚠⚠ surfaced SECOND satisfiability tension: bridge hmem confines into compact S q v indep of a,b but Y scales with unbounded a,b. FIX = hid bilinear in (a,b) => bounded a,b supply + bilinear extension. J4-44 = correct hid-supply reformulation. [AF] std-3.

- **J4-44** (JacobiOperatorFDeriv, JacobiDoubledFamily) — pointwise (a,b)-dependent reformulation RESOLVES the 2nd satisfiability leak (GPT-5.5 option C). σ:q v a b→ℝ (hσ:∀ q v a b,0<..), S:q v a b→Set introduced AFTER ∀a,b ⟹ per-(a,b) window+compact-set, supply SATISFIABLE (S=ball radius ~C(1+|a|)(1+|b|)), NO bilinear extension. Same names+conclusions, 2 files, both std-3, downstream green, no external consumer. [AF] std-3.

- **J4-45** (DoubledFamilyFullSupply.lean) — (B1) sPerturbed_confined_doubled_family_exists: s-perturbed confined doubled family, per-(a,b) σ=ρ/(2(1+|a|)), CLOSED-Icc hYode + exact affine hIC + geodesic-factor confinement. + narrow-pad linODE engines (closed-Icc derivs from open-window base). SATISFIABLE. (J) not self-contained: hmem(Jacobi Gronwall)+Vf+hlink+2nd-var block carried. J4-46 = hmem Gronwall + Vf. [AF] std-3.

- **J4-46** (DoubledFamilyConfine.lean) — (C1)+(C2) discharge hmem: sPerturbed_confined_doubled_family_confined_exists adds per-(a,b) compact convex product-ball S q v a b = closedBall((q,0))(C0.rho) x closedBall(0)(|(0,b)|.exp K_q) and PROVES hmem via Jacobi-factor Gronwall bound (norm_le_gronwallBound_of_norm_deriv_right_le). SATISFIABLE. Discharged: hScompact/hSconvex/hmem. Carried: Vf+hlink+2nd-var block. J4-47 = Vf. [AF] std-3.

- **J4-47** (DoubledVariationField.lean) — (D1/D2/D3) discharge Vf/hVode/hV0: linODE_exists_narrowpad_continuousOn (extract padded ContinuousOn J from glue witness) + doubledVariation_narrowpad_hasDerivAt_Icc (Vf genuine linODE solution, generator fderiv(doubledField)(Ybase0)) + confined_doubled_family_with_variation_exists ((S1)+Vf package). Bridge supply discharged: sigma/hYode/hIC/hScompact/hSconvex/hmem/Vf/hVode/hV0. Carried: hlink + 2nd-var block. J4-48 = hlink. [AF] std-3.

- **J4-48** (DoubledFamilyLink.lean) — discharges hlink via ODE-uniqueness: doubled_endpoint_eq_expMap_fderiv ((Y 1).2.1 = fderiv(expMap q) w b, two Gronwall uniqueness steps: geodesic base = expTube, Jacobi column = flow column, same ODE+seed) + hlink_of_confined_doubled_family (exact bridge binder shape). Added input hrad = exp-tube admissibility (from hr_lt+σ-window, not smuggled). ONLY carried block left = 2nd-var block. J4-49 = that block ⟹ (J). [AF] std-3.

- **J4-49** (SecondVariationSupply.lean) — (F1)+(F2) 2nd-var block: linODE_inhomog_exists_on_Icc (inhomogeneous linODE via state-augmentation over homogeneous engine) + secondVariation_field_exists (Zf with exact bridge ODE-shape + seed + Gronwall hXb bound, generic; operator/source continuity from contDiff_geodesicField). CARRIED: F3 Lipschitz-in-q hAd/hSd (engines present geodesic_twopoint_gronwall) + F4 capstone. J4-50 = F3+F4 ⟹ (J). [AF] std-3.

- **J4-50** (SecondVariationLipschitz.lean) — (F3a) hAd engine: geodesicField/fderiv-geodesicField LipschitzOnWith producers (compact convex) + fderiv_geodesicField_twopoint_dist_bound (‖Δfderiv(gf)‖≤Lg·exp Kg·dist q q', via geodesic_twopoint_gronwall + mean-value Lipschitz) = the bridge hAd shape. CARRIED: F3b hSd (three-fold Lipschitz-in-q coupling — last math wall) + F4 assembly. J4-51 = F3b. [AF] std-3.

- **J4-51** (SecondVariationSourceLip.lean) — (F3b) FULLY discharges hSd (last math wall): G0 fderiv²(gf) Lipschitz producer + G-A two-point bound + G-Σ secondVariation_source_twopoint_dist_bound (trilinear split, hSd shape with explicit a,b-indep Sr₀). Terms B/C via EXISTING jacobi_twopoint_diff_bound (both pfield/wfield solve same Jacobi linODE differing in seed). BOTH hAd+hSd now discharged. Remaining = F4 mechanical capstone (no math wall). J4-52 = F4. [AF] std-3.

- **J4-52** (CommonNondegRadius.lean) — (F4 partial) s1_doubled_supply_package: the ENTIRE (S1) block of the bridge UNCONDITIONAL (hC+IsCompact K ⟹ σ/Y/Vf/S + hScompact/hSconvex/hYode/hVode/hV0/hIC/hmem, r=ρ/2). ⚠ F4 NOT pure threading: 2 genuine residuals — (a) hr_lt uniform expRho over K [expRho=per-q OPAQUE Classical.choose, no uniform provenance; J4-20 wall; gates hlink; route=re-architect onto F] + (b) 2nd-var block folding into single-constant/common-S* shape (3 glue lemmas). J4-53 = resolve hr_lt (architecture consult). [AF] std-3.

- **J4-53** (UniformFlowTransfer.lean) — Layer-2 transfer lemmas (eventuallyEq_of_eqOn_ball + isUnit_fderiv_of_eqOn_ball via EventuallyEq.fderiv_eq + compact_nondeg_of_uniform_flow_eqOn) for the opaque-expRho re-architecture. ★ KEY SCOPE FINDING: re-architecture is LOCAL to the (J) bridge — NO ripple into pullback-metric/recenter; a₁=R/6 capstone uses RNC/Hessian+Gaussian not ∀q∈K nondeg; expMap_eq_flow_endpoint gives OVERLAP-only EqOn. J4-54 = hoist F=uniformFlowExp + restate hlink+bridge against F + close (J)-for-F via EqOn.refl. [AF] std-3.

- **J4-54** (UniformFlowNondeg.lean) — (K1) uniform-flow exp-map infrastructure: uniformFlowRadius/Const (single ρ_K,C₀ over K from geodesic_apriori_confinement_uniform, NO opaque selector) + uniformFlowTube + uniformFlowExp q w=(uniformFlowTube q w 1).1 (the uniform-provenance exp map) + spec lemmas (IC/ODE/confinement) + expMap_eq_uniformFlowExp_on_overlap. Replaces opaque expRho with uniform ρ_K. K2 (F-endpoint id) + K3 (F-bridge ⟹ (J)-for-F) remain. J4-55 = K2+K3. [AF] std-3.

- **J4-55** (UniformFlowFDeriv.lean) — (K2) uniformFlowExp_hasFDerivAt: ∃L HasFDerivAt(uniformFlowExp q) L w for ‖w‖<ρ_K, hyps hC+IsCompact K, NO expRho. Genuine variational proof (Mathlib PL is Lipschitz-in-IC only): σ-windowed mirror flowVelocity_endpoint_hasFDerivAt_window{,_exists} of the velocity-slot first-jet core, Jacobi field along fixed uniform tube (geodesicJacobi_narrowpad) ⟹ CLM via jacobiSol_unique, reusing geodesic_twopoint_gronwall/C2_remainder/residual_bound. K3 (Neumann IsUnit) ⟹ (J)-for-F. J4-56 = K3. [AF] std-3.

- **★ J4-56 (K3) — (J)-for-F CLOSED SELF-CONTAINED** (UniformFlowNondegClose.lean): uniformFlowExp_common_nondeg_radius — for hC+IsCompact K, ∃ρ₀>0 ∀q∈K ∀v ‖v‖<ρ₀→IsUnit(fderiv(uniformFlowExp q) v). NO expRho/hr_lt. L0 (flat Jacobi, jacobiOperator zero-velocity=0) + L-lip (linODE_twopoint_diff_bound + MVT, uniform over ONE compact S) + Neumann (isUnit_one_sub_of_norm_lt_one) + assemble (K2 + HasFDerivAt.fderiv). ENTIRE J4-35→J4-56 (h3a)/(J) tower CLOSED for uniform-flow exp. a₁=R/6 still conditional: (J)-for-F is a LEAF of Brick-A→hunif→recenter→convergence. [AF] std-3.

- **J4-58** (PullbackNondegFromFDeriv.lean, ns QIQTH.PullbackMetric) — fderiv→pullback nondeg HINGE: expPullbackMetric_isUnit_of_fderiv_isUnit (IsUnit(fderiv(expMap p) v)+hg ⟹ IsUnit(matToCLM(expPullbackMetric p v))). Pullback metric IS the congruence JᵀMJ ⟹ H1 congruence-id + H2 isUnit_matToCLM_iff + H3 congruence-preserves-unit (det_transpose). hg genuine geometry. Matches stub RecenterAnnulusUncond:44-46. Connects fderiv-nondeg to pullback IsUnit. a1=R/6 still gated on Brick-A + hDuhamel. J4-59 = BEGIN Brick-A. [AF] std-3.

- **J4-60** (UniformRadiusCert.lean) — Brick-A(β) ENTRY: uniform-radius CERTIFICATE replacing hr_lt. structure UniformConfinedTubeOn (hr+hconf+hnondeg) + uniformConfinedTubeOn_exists (hC+IsCompact K ⟹ ∃r>0 cert, UNCONDITIONAL; r=min(uniformFlowRadius,ρ₀); hconf from J4-17, hnondeg from J4-56). The (J)-for-F milestone IS the cert nondeg field — NOT orphaned. INHABITED, no expRho. Pullback-nondeg + C³ reg firewalled as future. J4-61 = uniformFlowExp pullback+hinge. [AF] std-3.

- **J4-61** (UniformFlowPullback.lean, ns QIQTH.PullbackMetric) — uniformFlowExp pullback metric + hinge (Brick-A pullback-nondeg field): uniformFlowPullbackMetric (genuine congruence, mirror of expPullbackMetric) + uniformFlowPullbackMetric_isUnit_of_fderiv_isUnit (reuse J4-58) + uniformConfinedTubeOn_pullback_isUnit (feeds cert hnondeg ⟹ pullback IsUnit over q∈K). hg genuine geometry. J4-62 = uniform C³ reg + sup-bounds. [AF] std-3.

- **J4-62** (UniformFlowRegBound.lean) — Brick-A piece (I) scope + first rung. VERDICT (GPT-5.5): M/W/L need g̃∈C² ⟺ uniformFlowExp∈C³; current = only C¹ (J4-55) ⟹ piece (I) is a LARGE joint higher-regularity sub-tower (2 orders short: 2nd+3rd velocity variation over K, then easy compactness uniformization). RUNG: uniformFlowExp_displacement_uniform_bound (∃M≥0 ∀q∈K ∀‖v‖≤ρ_K ‖uniformFlowExp q v−q‖≤M=C₀ρ_K, C⁰ confinement). J4-63 = joint-cont fderiv → uniform Jacobian bound. De-risk: refactor producer to minimal C² interface. [AF] std-3.

- **J4-63** (UniformFlowJacobianBound.lean) — Brick-A uniform JACOBIAN bound: uniformFlowExp_fderiv_uniform_bound (∃Mj ∀q∈K ∀‖v‖<ρ_K ‖fderiv(uniformFlowExp q) v‖≤Mj=exp(Kf), q-indep, NO expRho) + _closedBall. Route: explicit Jacobi-endpoint CLM (reuse J4-56 prelude ~90- **J4-63** (UniformFlowJacobianBound.lean) — Brick-A uniform JACOBIAN bound: uniformFlowExp_fderiv_uniform_bound (exists Mj, forall q in K, |v|<rho_K, |fderiv(uniformFlowExp q) v|<=Mj=exp(Kf), q-indep, NO expRho) + _closedBall. Route: explicit Jacobi-endpoint CLM (reuse J4-56 prelude) + Gronwall opNorm (reuse J4-46). Unlocks uniform g-tilde entry bounds. J4-64 = uniform pullback-entry bounds. [AF] std-3.
- **J4-64** (UniformPullbackEntryBound.lean, ns QIQTH.PullbackMetric) — Brick-A uniform C0 pullback-entry bound: uniformFlowExp_metric_entry_uniform_bound (g-factor bounded on compact image from J4-62+hg) + uniformFlowPullbackMetric_entry_uniform_bound (exists r0>0 Mg, forall q in K, |v|<=r0, |g-tilde_ij|<=Mg via Cauchy-Schwarz + J4-63 Jacobian). hg = genuine ambient-metric smoothness. Brick-A C0-bounds DONE. Remaining: 2nd/3rd velocity variation -> C3. [AF] std-3.
- **J4-65** (UniformFlowSecondJet.lean) — Brick-A 2nd-order (R1): uniformFlowTube_secondVariation_uniform_bound (exists r0>0 M2j, forall q in K, |v|<=r0, forall a, exists V Zf solving 1st+2nd-var linODEs, |Zf tau|<=M2j.|a|^2 uniform Gronwall). Runs on CLOSED [0,1] via right-within-derivs (sidesteps open-window padding wall). + linODE_inhomog_within_exists_on_Icc engine. R2 (Hessian HasFDerivAt) + R3 (opNorm) firewalled. J4-66 = R2 or 3rd variation → C3. [AF] std-3.
- **J4-66** (UniformFlowSecondFDeriv.lean) — R2 ENABLER: field-agnostic Fréchet first-jet on the doubled field. autonomousLinODE_unique + autonomousFlow_endpoint_hasFDerivAt_window{,_exists} (abstract sigma-windowed Frechet first-jet, CLM via FiniteDimensional) + doubledFlow_endpoint_baseVelocity_hasFDerivAt_exists (specialized to doubledField, all G-regularity discharged). R2 itself firewalled: needs R2-a (base-velocity-perturbed confined doubled uniform-tube supply) + R2-b (strengthen K2 to expose Jacobi endpoint operator) + R2-c (bilinear B2 assembly). GPT-5.5: expMap-C4 transfer can't remove expRho guard. J4-67 = R2-a+R2-b. [AF] std-3.
- **J4-67** (UniformFlowSecondSupply.lean) — R2-a + R2-b (indep-built green). R2-a uniformFlow_doubledEndpoint_baseVelocity_hasFDerivAt (base-velocity-perturbed confined doubled supply fed to J4-66). R2-b uniformFlowExp_fderiv_apply_eq (exposes K2 operator: fderiv(uniformFlowExp q) w b=(J 1).1 via jacobiSol_unique) + uniformFlowExp_fderiv_apply_hasFDerivAt (per-seed Frechet 2nd-jet). FULL R2 (CLM-valued Hessian) firewalled: needs finite-dim basis-eval assembly. J4-68 = that assembly → R2, then R3 + 3rd variation. [AF] std-3.
- **★ J4-68** (UniformFlowHessian.lean) — R2 CLOSED (2nd-order regularity): uniformFlowExp_fderiv_hasFDerivAt (∃B₂ HasFDerivAt(fun w=>fderiv(uniformFlowExp q) w) B₂ v, CLM-valued jet map Frechet-differentiable). Finite-dim assembly via Mathlib ContinuousLinearEquiv.piRing + differentiableAt_pi + R2-b per-seed derivs. Indep build-verified. R3 (uniform Hessian bound) firewalled. Brick-A: C¹✓ C²✓. Next: R3 + 3rd variation → C³. [AF] std-3.
- **J4-69** (UniformFlowHessianBound.lean) — R3 reduction + 2 reusable lemmas (indep build-verified). bilinear_opNorm_le_of_symm_diag_bound (generic: symm B, ‖B a a‖≤M‖a‖² ⟹ ‖B‖≤2M via polarization) + uniformFlowExp_hessian_symm (B₂ symmetric via second_derivative_symmetric) + uniformFlowExp_hessian_opNorm_le_of_diag_bound (hdiag ⟹ ∃M' ‖B₂‖≤M'). R3 NOT fully closed: diagonal bound hdiag carried (needs two-sided doubled 2nd-var supply; R1's Zf is diagonal+within-deriv, hid needs two-sided). J4-70 = that supply ⟹ hdiag ⟹ R3, then 3rd variation → C³. [AF] std-3.
- **★ J4-70** (UniformFlowHessianDiag.lean) — R3 CLOSED UNCONDITIONAL (indep build-verified): uniformFlowExp_hessian_diag_bound + uniformFlowExp_hessian_opNorm_le (∃r₀>0 ∃M' ∀q∈K ∀‖v‖<r₀ ‖B₂(q,v)‖≤M', hyps ONLY hC+IsCompact K). Route T via hid_of_doubled_data, key simplification Zf:=(Vf·).2 ⟹ hZf from doubledField_secondFactor_ode (dissolves within-vs-two-sided tension). Brick-A regularity: C⁰/C¹/C²+bounds ALL ✓. J4-71 = 3rd variation → C³. [AF] std-3.
- **J4-71** (UniformFlowThirdJet.lean) — C³ layer OPENED (W1, indep build-verified): uniformFlowTube_thirdVariation_uniform_bound (∃ V W Z₃ solving 1st/2nd/3rd-var linODEs along the uniform tube, source D³F(V,V,V)+2D²F(V,W)+D²F(W,V), ‖Z₃‖≤M₃j‖a‖³ uniform cubic Grönwall; closed-[0,1] within-derivs; constants over ONE compact ball over K). Remaining C³: W2 per-seed 3rd-jet (hid-analogue one order up) + W3 ‖B₃‖ bound + W4 g̃∈C² assembly. J4-72 = W2. [AF] std-3.
- **J4-72** (UniformFlowThirdFDeriv.lean) — W2 infrastructure (indep build-verified). Route verdict (GPT-5.5): 3rd jet needs the QUADRUPLED field genericDoubled(doubledField), R2-a/b reuse insufficient. Landed: W2-pre DifferentiableOn (from R2-b) + genericDoubled + contDiff/bddOn regularity supply (field-agnostic + instantiated from hC) = the engine inputs for the quadruple-flow supply. W2 HasFDerivAt carried (needs quadruple supply). J4-73 = quadruple supply ⟹ W2. [AF] std-3.
- **J4-73** (QuadrupleFlowSupply.lean) — W2 supply Y1-Y3 + projection (indep build-verified; banked by main loop after agent report-stall): genericDoubled_prod_hasDerivAt + uniformFlow_quadrupleEndpoint_baseVelocity_hasFDerivAt (quadruple family W̃δ=((tube(v+δ),Jf δ),Uf δ) endpoint HasFDerivAt via J4-66 engine + J4-72 regularity) + uniformFlow_quadrupleEndpoint_component_hasFDerivAt (∃L₃ HasFDerivAt(fun δ=>(Uf δ 1).2.1) L₃ 0). W2 residual = Y4 value-id (Uf δ 1).2.1=B₂(v+δ) a b. J4-74 = Y4 ⟹ W2. [AF] std-3.
- **★ J4-74** (UniformFlowThirdJetClose.lean) — W2 CLOSED (indep build-verified): Z1 uniformFlowExp_hessian_value_id (B₂(v) a b = (U 1).2.1 for any Jacobi-J + doubled-linearized-U, via hid_of_doubled_data + jacobiSol_unique + autonomousLinODE_unique) + Z2 uniformFlow_thirdJet_hasFDerivAt (∃L₃ HasFDerivAt(fun w=>B₂(w) a b) L₃ v, via J4-73 component + eventual-eq + recentre). Slot-order a=base-vel dir, b=Jacobi dir, direct. C³ remaining: W3 ‖B₃‖ bound + W4 g̃∈C² assembly. J4-75 = W3. [AF] std-3.
- **J4-75** (UniformFlowThirdBound.lean) — W3 polarization half (indep build-verified): symm_trilinear_polarization (24-fold parallelogram-free identity) + trilinear_opNorm_le_of_symm_diag_bound (‖B‖≤(9/2)M from symmetric diagonal bound), generic/reusable, one-order-up of J4-69. GPT-5.5: per-slot Grönwall route BLOCKED (confinement grows with ‖a‖,‖b‖). W3 residual: P1 diagonal value-id (tripled-flow hid-analogue) + P2 B₃ symmetry (Clairaut). J4-76 = P1+P2 ⟹ W3 (M₃=(9/2)M₃j from W1). [AF] std-3.
- **J4-76** (UniformFlowThirdBoundClose.lean) — D1+P2+conditional-W3 (indep build-verified): uniformFlowExp_hessianMap_differentiableAt (CLM-valued 3rd jet via double piRing lift) + thirdJet_symm23/symm12 (differentiated hessian_symm + Clairaut) + uniformFlowExp_thirdDeriv_opNorm_le_of_diag_bound (hdiag ⟹ ‖B₃‖≤(9/2)M uniform). W3 residual = P1 diagonal value-id (d/ds[(U_s 1).2.1]|₀ ↔ W1 Z₃, discharges hdiag with M=M₃j). J4-77 = P1 ⟹ W3 unconditional. [AF] std-3.
- **J4-77** (UniformFlowThirdDiag.lean) — Q1a diagonal value-id (indep build-verified): uniformFlowExp_thirdDeriv_diag_value_perSeed (B₃(q,v) a a a = L₃ a, via D1 + line-restriction + W2 per-seed + HasDerivAt.unique). W3 residual reduced to ‖L₃ a‖≤M₃j‖a‖³ — needs the Xcmp comparison-field brick (engine L δ=V δ 1 clause re-plumb + packed within-uniqueness + 3 fderiv-applied lemmas; GPT-5.5 no-shortcut). J4-78 = Xcmp ⟹ W3 unconditional. [AF] std-3.

## J4-78 (aa2b8f4b) — ★★ W3 UNCONDITIONAL: C³ LAYER OF BRICK-A(β) CLOSED
`QIQTH/UniformFlowThirdUncond.lean` (ns QIQTH.ExpMap), [AF] std-3, indep build-verified.
The Xcmp comparison-field brick, exactly per the GPT-5.5-confirmed spec (no shortcut existed):
- Reusable applied block lemmas: `genericDoubled_fderiv_fst/snd_apply`,
  `fderiv_fderiv_doubledField_apply` (+`_fst`/`_snd`) — D²(doubledField) applied block via
  the evaluation-commutes-with-fderiv route.
- `autonomousLinODE_within_unique` — within-[0,1] Grönwall uniqueness (reconciles W1's
  within-derivatives vs the engine's two-sided ones).
- `comparisonField_hasDerivWithinAt` — Xcmp τ = ((V τ,W τ),(W τ,Z₃ τ)) solves the
  Φ̃-linearized ODE along ((Y,V),(V,W)); RHS reduces EXACTLY to W1's (V',W',W',Z₃')
  (Src₃ matched up to abel).
- `uniformFlow_quadrupleEndpoint_baseVelocity_hasFDerivAt_withField` — J4-73 engine
  re-plumbed KEEPING ∀δ, L δ = Vf δ 1 and exposing the linearized family+ODE+seed.
- X1 `uniformFlowExp_thirdDeriv_diag_cubic_bound`: B₃ a a a = (Xcmp 1).2.2.1 = (Z₃ 1).1
  via three within-uniqueness pins (Jf 0 = V; Uf 0 = (V,W); Vf a = Xcmp) ⟹
  ‖B₃ a a a‖ ≤ M₃j‖a‖³ (M₃j = W1's constant; r₀ = min r₀_W1 ρ_K).
- X2 = W3 `uniformFlowExp_thirdDeriv_opNorm_le`: with J4-76 polarization, ‖B₃‖ ≤ (9/2)M₃j
  uniform on the common ball — hyps ONLY hC + IsCompact K. The hdiag firewall is a THEOREM.
STATUS: Brick-A(β) regularity climb C⁰/C¹/C² /C³ ALL CLOSED unconditional.
NEXT: J4-79 = W4 (g̃ = Jᵀ(g∘F)J ∈ C² with uniform bounds) → hunif assembly → hcoord →
mechanical wiring → hDuhamel (Rosenberg §3.2.2) → TrueKernelA1Reduced:153.

## J4-79 (270891aa) — W4 differentiability + C⁰ half: g̃ entries C² on the uniform ball
`QIQTH/UniformFlowMetricC2.lean` (ns QIQTH.ExpMap), [AF] std-3, indep build-verified.
- `IsC2At` scalar 2-jet calculus (eventual DifferentiableAt + differentiable fderiv-map;
  const/add/mul/finsetSum closure) — geometry-free, reusable.
- `isC2At_jacobianEntry` (CLM-apply/proj evaluation route + D1 third jet),
  `isC2At_metricFactor` (hg chain rule), entry assembly + both HasFDerivAt layers.
- Capstone `uniformFlowPullbackMetric_c2_uniform`: ∃r₀>0 ∃M ∀q∈K ∀‖v‖<r₀ ∀ij — both
  Fréchet layers exist + |g̃_ij(v)| ≤ M. Hyps ONLY hg+hC+IsCompact K.
FIREWALL (honest, assembly-only): uniform C¹/C² entry opNorm bounds pending — all
sub-bounds exist uniformly (Mg0, Mj, Hessian R3, third W3, EVT ‖Dg‖/‖D²g‖ on the
endpoint tube). J4-79b = IsC2At-with-bounds product lemma ×2 + finite triangle sums.

## J4-79b (5b5f2eb8) — ★★ W4 COMPLETE: Brick-A(β) REGULARITY + BOUNDS CLOSED
`QIQTH/UniformFlowMetricC2Bound.lean`, [AF] std-3, indep build-verified. Discharges the
J4-79 C¹/C² firewall — NOTHING left firewalled in W4:
- `uniformFlowExp_tube_continuous_bound` (EVT on the displacement tube, Q1 generalized);
- `HasC2BoundAt` Leibniz bound calculus (product law A₀B₂+2A₁B₁+A₂B₀);
- `metricFactor_c2Bound` + `jacobianEntry_c2Bound` (Mj/Hessian/W3 feed C⁰/C¹/C²);
- capstone `uniformFlowPullbackMetric_c2_uniform_full`: ∃r₀>0 ∃M ∀q∈K ∀‖v‖<r₀ ∀ij —
  both HasFDerivAt layers + |g̃|≤M + ‖D‖≤M + ‖D²‖≤M. Hyps ONLY hg+hC+IsCompact K.
STATUS: Brick-A(β) fully closed (exp C⁰..C³ + g̃ C⁰..C² uniform over K).
NEXT: J4-80 (in flight) = hunif uniform-B assembler (RecenterReduction:86 consumer);
then hcoord → mechanical wiring → hDuhamel (Rosenberg §3.2.2) → TrueKernelA1Reduced:153.
Gotchas banked: opNorm_add_le for CLM norms; point-free fderiv_mul bridging; clm_comp
const route for L∘h(w); maxSynthPendingDepth 4 for 4-level CLM Norm; standalone ring have.

## J4-80 (a01032c5) — hunif assembler step 1: uniform FORWARD-metric packet
`QIQTH/UniformResidualB.lean`, [AF] std-3, indep build-verified.
`uniformResidual_forwardMetric_packet`: ONE r₀>0 + ONE M, ∀q∈K ∀‖v‖<r₀ ∀ij — g̃ C⁰/C¹/C²
≤ M + IsUnit(fderiv uniformFlowExp) + IsUnit(matToCLM g̃). New genuine hyp hgnd (base
metric nondeg at endpoints).
★ S1 FINDING: the hunif consumer (cutoffResidual_expPullback_hEboundW RecenterCutoffC3:97
via hEboundW_of_uniform_perBasePoint RecenterReduction:86) carries residue mostly on the
INVERSE metric g̃⁻¹ (hgi_ann/hLapChi_ann/hdev); the R4c/R5 chain lives over expMap/expRho
⟹ re-target onto uniformFlowExp is the infrastructure step (J4-81+).
FIREWALL (exact): ∃r₀>0 ∃Kinv ∀q∈K ∀‖v‖<r₀ ‖Ring.inverse(matToCLM g̃)‖≤Kinv.
J4-80b (in flight) = Route B: Neumann ‖J⁻¹‖≤2 + tube-EVT ‖(g∘F)⁻¹‖ + congruence.

## J4-80b (9a18cf32) — ★ uniform g̃⁻¹ bound: the J4-80 firewall DISCHARGED (Route B complete)
`QIQTH/UniformInverseMetric.lean`, [AF] std-3, indep build-verified. Nothing firewalled:
- P1 `uniformFlowExp_common_nondeg_radius_quant` (Grönwall/Neumann tail re-derived KEEPING
  C_D ⟹ ‖(fderiv uniformFlowExp)⁻¹‖ ≤ 2 uniform) + `norm_ringInverse_one_sub_le`.
- P2 `uniformFlowExp_baseMetricInv_uniform_bound` (tube-EVT, Ring.inverse continuous at
  units; genuine hgnd = global metric nondeg).
- P3 `norm_ringInverse_matToCLM_congr_le` (congruence bound cJ·cG·cJ·n²; sup-norm transpose
  handled entrywise — no Cramer/Matrix.inv).
- Capstone `uniformInverseMetric_bound`: uniform IsUnit(matToCLM g̃) + ‖Ring.inverse‖ ≤ Kinv
  + entrywise ≤ Kinv (extraction form matches expPullbackMetricInv). Hyps hg+hC+hK+hgnd.
NEXT: J4-81 (in flight) = consumer-shaped inverse props (hinvT/hgisymm/hgi_ann/Γ̃ bound,
+ hLapChi_ann/hdev if reachable) toward cutoffResidual_expPullback_hEboundW:97.

## J4-81 (11886b69) — ★ consumer-shaped inverse props over uniformFlowExp
`QIQTH/UniformFlowMetricInvProps.lean`, [AF] std-3, indep build-verified.
All RecenterCutoffC3:97 metric-side inputs EXCEPT hdev, uniform over K:
- D1 `uniformFlowPullbackMetricInv` (expPullbackMetricInv convention) + `matToCLM_invMat`
  (entrywise inverse reassembles to Ring.inverse — key device).
- D2 hinvT both orders; D3 hgisymm (transpose uniqueness, genuine hgsymm);
- D4 hgi_ann (ball+annulus) — bundled `uniformFlowPullbackMetricInv_props`;
- D5 `uniformFlowChristoffel_uniform_bound`; D6-hLapChi
  `uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound` (bounds bypass continuity —
  sidesteps the ContinuousOn-annulus wall of the opaque expPullback route).
FIREWALL (exact): hdev ∀ᶠ v in 𝓝 0, |g̃⁻¹(v)−δ| ≤ M·rncRadialSq v — needs uniformFlowExp
RNC jet-at-0 (g̃(0)=δ w/ hframe, ∂g̃(0)=0). J4-82 (in flight) = Route T (per-q weld to
expMap via ODE uniqueness, transfer pd_expPullbackMetricInv_zero) or Route D (direct jets).

## J4-82 (8d2626a1) — ★ hdev DISCHARGED: all metric-side hunif consumer inputs closed
`QIQTH/UniformFlowJetZero.lean`, [AF] std-3, indep build-verified. Route T (GPT-5.5 +
gpt-5.6-sol consult): weld expMap =ᶠ uniformFlowExp near 0 per q (J4-20 bridge) ⟹
EventuallyEq.fderiv_eq ⟹ equal pullback metrics ⟹ Ring.inverse pointwise congruence
(total fn, no nondeg needed). No expPullback hdev producer existed — built:
pd_expPullbackMetricInv_zero_clean + contDiffAt_two_quadratic_decay +
expPullbackMetricInv_dev. Capstone `uniformFlowPullbackMetricInv_dev` = the EXACT
RecenterCutoffC3:97 hdev shape over uniformFlowExp (per-q M; uniform-M upgrade via
Taylor from uniform C² = J4-83 concern if needed). Tricks: nested-CLM topology-diamond
dodge (exact's lenient isDefEq), germ-local pd, hypothesis-clean near-0 inverse identity.
NEXT: J4-83 (in flight) = producer→packet refactor (ResidualEstimateData; consult
architecture) ⟹ per-base-point bound w/ SINGLE B ⟹ RecenterReduction:86 ⟹ hunif.
hDuhamel decomposition (gpt-5.6-sol, bankable order) recorded in loop state: Gaussian
convolution calculus → Levi iterate bounds → ε-truncated identity → delta-family
(Lemma 3.14) → ε→0 → partial sums → series interchange.

## J4-82u + J4-83 (ac38c464) — ★★ uniform-M hdev + producer→packet re-plumb
[AF] std-3, indep build-verified.
J4-82u (UniformFlowJetZero.lean +209 lines): jet-values-only transfer (forward weld +
pd_congr_eventuallyEq ⟹ jet_zero g̃(0)=δ, ∂g̃(0)=0) + Taylor with UNIFORM C² constants ⟹
`uniformFlowPullbackMetricInv_dev_uniform` — hdev with ONE M over K (the consult's design).
J4-83 (UniformResidualPacket.lean, ns HeatResidualBound): census found the producer body
is a thin assembly of TWO already-abstract engines ⟹ re-instantiation not port:
`cutoffResidual_bound_from_packet` (construction-independent, no exp objects) +
`cutoffResidual_uniformFlow_hEboundW` (per-q at uniformFlowPullbackMetric; hsymm+hdev
supplied from uniform machinery, rest carried genuine).
FIREWALL (exact): full uniform hEboundW = UNIFORM NEAR ENGINE (per-q b=ρ/2 + constant in
near_uncutResidual_gaussianWide_ball_C3 / residualN0_local_baseKernelW_slice_C3) + ball-
local producer variant (global ∀y/∀a,b fields vs ball-local uniform lemmas).
J4-84 (in flight) = UniformNearEngine.lean attacking exactly this.

## J4-84 (984e39d9) — ★ near engine UNIFORM: packet refactor + one radius/constant over K
`QIQTH/UniformNearEngine.lean` (ns HeatResidualBound), [AF] std-3, indep build-verified.
Census: per-q source = the radius ρ inside eventually_nhds_zero_ball (constant already
explicit). `near_uncutResidual_gaussianWide_ball_from_packet` (refactor boundary = the
explicit-radius residual bound hRes) + `_viaPacket` satisfiability check (sharper constant,
(√2)ⁿ dropped) + `near_uncutResidual_uniform` (ONE b=ρ_u/2 + ONE C over K from hResU).
FIREWALLS: (F-res) uniform residual bound — term (1) uniform little-o of totalRadialO1_
coeff (uniform C³ Taylor remainder) + term (3) uniform Laplacian L [term (2) already
uniform]. (F-cut) explicit-B cutoff-engine variant — J4-85 in flight.

## J4-85 (bf055099) — ★★ F-cut DISCHARGED: explicit-B cutoff engine + uniform assembly
`QIQTH/UniformCutoffEngine.lean` (ns HeatResidualBound), [AF] std-3, indep build-verified.
B exposed: C + M·Kc2 + 2n²·Kg·Kc1·M·(8/a²). `_explicitB` (packaging-only change) +
`uniformFlowPullbackMetricInv_symm_global` (junk-value trick sheds hgisymm) +
`cutoffResidual_uniformFlow_uniform` (SINGLE (a,b,B) over K; b=min(ρ_u/2,rmin/2), a=b/2;
same-B by fixing constants before ∀q) + `_gaussDdim` (width-2 shape).
Conditional ONLY on hResU = F-res. Gaps to RecenterReduction:86: fixed-t vs ∀τ, q∈K vs
∀q, E-identification (Vmap). J4-86 (F-res: quantitative little-o replacement via
dev_uniform + uniform Laplacian L) in flight.

## J4-86 (6bfd9831) — ★★ F-res REDUCED to hCoeffU: terms 2+3 discharged
`QIQTH/UniformResidualBound.lean` (ns HeatResidualBound), [AF] std-3, indep build-verified.
Split coeffAF·w₀ + radialDeriv(w₀) + coeffDevF; per-q ∀ᶠ little-o replaced by explicit-
radius bounds: `residualQuadratic_pointwise` (32n²MW, consumes dev_uniform) +
`uniformFlowLaplaceBeltrami_w0_near_uniform` (uniform L near 0). `uniformResidual_
gaussian_bound` (exact hResU shape, C=8C_c+32n²MW+L) + `cutoffResidual_uniformFlow_of_
coeffBound` — BOTH conditional ONLY on hCoeffU (uniform O(r²) of totalRadialO1_coeff).
CORRECTED ASSESSMENT (mine, vs agent's C³ claim): hCoeffU needs only the EXISTING C²
layer — Γ̃ linear decay via Γ̃(0)=0 (jet_zero) + MVT with ∂Γ̃ bounded by the second
Fréchet layer + ∂g̃⁻¹=−g̃⁻¹(∂g̃)g̃⁻¹ (differentiate Σg̃⁻¹g̃=δ entrywise). J4-87 in flight.

## Consult record (gpt-5.6-sol, 2026-08-02 ~07:00) — three verdicts for the hunif endgame
1. hCoeffU derivative counting CONFIRMED: C² layer + jet-zero suffice (no C³); ∂Γ̃ from
   ∂(g̃⁻¹)=−g̃⁻¹(∂g̃)g̃⁻¹ + second Fréchet layer; segment MVT needs only differentiability
   + bound (no continuity of ∂Γ̃). Caveat: "second layer" = HasFDerivAt data (the
   derivative FIELD differentiable), which c2_uniform_full provides.
2. τ-uniformity (the ∀τ gap to RecenterReduction:86): quantify the engines over 0<τ(≤T)
   from the start with reusable Gaussian absorption lemmas (r^k·τ^{-m}·e^{−r²/4τ} ≤
   C·e^{−r²/8τ}, annulus variants with r≥a>0); constants come out τ-free on (0,T].
   ⚠ (0,T] does NOT give ∀τ>0 automatically — split at T, separate direct bound for τ≥T
   (elementary at N=0 but must be checked; polynomial τ-corrections can obstruct).
3. E-identification (Vmap gap): define E by the chart residual inside + ZERO outside;
   cutoff support strictly inside the chart domain; three lemmas (chart identification /
   E=0 outside / trivial bound 0≤B·gauss outside). Never apply a partial Vmap outside
   its domain — piecewise extension explicit in the capstone statement.

## J4-87 (c110bcfd) — ★★★ hCoeffU DISCHARGED: uniform cutoff residual UNCONDITIONAL (fixed t)
`QIQTH/UniformCoeffBound.lean` (ns HeatResidualBound), [AF] std-3, indep build-verified.
The C²-suffices assessment HELD (Sol-confirmed); landed route simpler still — MVT one
level down: `pd_linear_decay` (|∂g̃(v)|≤Kpd‖v‖ from jet_zero + fderiv_decay on the
genuine layer-2 HasFDerivAt data) ⟹ `uniformFlowChristoffel_linear_decay` (entrywise, no
inverse calculus) ⟹ `uniformCoeff_bound` (hCoeffU; extra input hw0flat = the SAME gauge
hypothesis as the old chain) ⟹ `cutoffResidual_uniformFlow_unconditional` — the full
single-(a,b,B) uniform residual bound over K. F-res/F-cut/hCoeffU chain (J4-84→87) CLOSED.
Remaining to global hEboundW: τ-quantification + per-base-point E-identification (J4-88
in flight; Sol routes in the consult record above).

## J4-88 (c7b54f78) — ★★ τ-QUANTIFICATION CLOSED: ∀τ>0 with τ-free constants
`QIQTH/UniformTauResidual.lean` (ns HeatResidualBound), [AF] std-3, indep build-verified.
Consumer needs literal ∀τ>0 — delivered. The Mann τ-growth was a packaging artefact
(derivative absorbed directly into gaussDdimWide, (1/τ)G ≤ (8/a²)G_wide). New simpler
explicit-B engine + τ-quantified F-res/near ⟹ `cutoffResidual_uniformFlow_unconditional_
tau` (∃(a,b,B) τ-free, ∀τ>0 ∀q∈K ∀v; same hyps as J4-87).
ONE hunif firewall left: E-IDENTIFICATION (global heatOp g gi H vs recentred cutoff
residual — Laplace–Beltrami pullback naturality under the uniformFlowExp chart; the
arbitrary-center chart wall named in RecenterReduction Step-1). J4-89 (census + core)
in flight.

## J4-89 (59029ce2) — ★ E-identification CENSUS + D²φ-free transport cores
`QIQTH/ResidualChartTransport.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
CENSUS: capstone hEboundW = |heatOp g gi H| ≤ C·baseKernelW (GLOBAL-chart LB; H pinned by
hHdiag); reduction RecenterReduction:86+:101; NO LB-naturality lemma existed; coordinate
naturality is D²φ-dependent. CORES: pd_comp + pullbackInv_trace_contraction (J·g̃⁻¹·Jᵀ=G⁻¹)
+ pd_pd_comp. FIREWALL: D²φ pointwise + Christoffel transformation + assembly + E-id.
J4-90 (in flight): KEY INSIGHT — naturality is a GENERAL C² diffeomorphism computation
(no geodesic input): ∂g̃ product expansion → Christoffel transform (∂J-symmetry from
Mathlib) → abstract laplaceBeltrami_pullback_naturality → instantiate at uniformFlowExp.

## J4-90 (a5d39760) — ★★★ LB PULLBACK NATURALITY: the abstract heart of the E-identification
`QIQTH/PullbackNaturality.lean` (ns HeatResidualBound), [AF] std-3, indep build-verified.
The general-diffeomorphism insight HELD (J4-89 pessimism overturned): naturality is pure
computation for any smooth φ with invertible Jacobian. Chain: pullbackMet + metric-deriv
Leibniz + christoffel-combo (Schwarz cancellations) + `pullback_christoffel_transform`
(CRUX: the RAISED law — contract vs J so J·g̃⁻¹·Jᵀ=g⁻¹ collapses, Dφ⁻¹ never forms) +
CAPSTONE `laplaceBeltrami_pullback_naturality`. FIREWALL: local instantiation at
uniformFlowExp (ContDiffAt-on-ball tower re-run) = J4-91 (in flight).

## J4-91 (7d1af69a) — ★★★ naturality INSTANTIATED at uniformFlowExp: J4-90 firewall broken
`QIQTH/PullbackNaturalityLocal.lean` (817 lines, ns HeatResidualBound), [AF] std-3, indep
verified. NOTHING firewalled. KEY: the three Fréchet layers hold at EVERY ball point ⟹
genuine ContDiffAt 2 (`contDiffAt2_uniformFlowExp`). Tower localized at per-point
regularity; `laplaceBeltrami_uniformFlow_naturality` on the uniform ball with only
genuine far-point hypotheses carried. NEXT: J4-92 (in flight) = the E-witness assembly
(H_w via Vmap/zero-extension → residual transport via naturality → in/out-chart bounds →
hcoord width-margin → RecenterReduction feed ⟹ global hEboundW = hunif core).

## J4-92 (942d236f) — ★★ the E-IDENTIFICATION TRANSPORT
`QIQTH/GlobalResidualWitness.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
`globalCutoffParametrixWitness` H_w (abstract Vmap + per-v left-inverse germ) + W2
`heatOp_globalWitness_eq_recentred_inChart` (heatOp of H_w at φ_q v = the recentred
bracket; reverse naturality + germ-locality) + W3 in-chart bound (single τ-free (a,b,B)).
Carried (Sol-honest): hgerm + witness far-point C² + hcoord + global feed. MY counter-
assessment: Mathlib IFT (ContDiffAt.to_localInverse ⟸ contDiffAt2_uniformFlowExp +
IsUnit fderiv) should discharge hgerm + regularity — J4-93 in flight.

## J4-93 (6da221a0) — ★★★ THE IFT LAYER: inverse-chart regularity DISCHARGED
`QIQTH/UniformFlowLocalInverse.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
Sol's "infrastructure-scale" call REFUTED — Mathlib IFT (ContDiffAt.localInverse /
toOpenPartialHomeomorph) fed by contDiffAt2_uniformFlowExp + common_nondeg_radius:
per-(q,v) local inverse (I1) + SINGLE per-q total `basepointInverseChart` (germ + C² at
every in-ball v; no injectivity-radius lemma needed) + J4-92 antecedents DISCHARGED (I3)
+ `globalWitness_residual_bound_inChart_unconditional` (I4; residue = far-point metric
conditions derivable from global hyps). NEXT: J4-94 (in flight) = hunif closer
(antecedent plumbing + out-of-chart zero-extension [crux: e.symm off-target junk ⟹ maybe
indicator-gated witness] + hcoord + hunif_final).

## Consult record (gpt-5.6-sol, 2026-08-02 ~11:30) — WIDTH-MARGIN verdict for J4-95
Architecture CONFIRMED: three-width chain G₁ → G_{3/2} → G₂ (Gc(τ,v) := gaussDdim(c·τ) v):
1. Polynomial/derivative absorption: τ^{−k}‖v‖^m·G_a ≤ C·τ^{m/2−k}·G_b for 1≤a<b.
2. Annular absorption: r≥r₀ ⟹ τ^{−k}·G_a ≤ C(a,b,k,r₀)·G_b, ∀τ>0 (width diff gives e^{−A/τ}).
3. Chart transfer with width budget: ‖φ_q(v)−q‖ ≤ L‖v‖ ∧ cL² < d ⟹ G_c(τ,v) ≤ C·G_d(τ,φ_q(v)−q);
   c=3/2, d=2, L²≤9/8 gives cL²=27/16<2 — strict room.
Post-hoc conversion from the width-8τ output IMPOSSIBLE (cubic error/τ unbounded) — re-run
from the width-4τ (G₁) primitives FORCED. Lean shape: width-parametric absorption+transfer
lemmas, capstones at c=3/2 (copy-adjust). ⚠ τ-caveat: r²G₁ ≤ Cτ·G_{3/2} carries a τ —
uniform when paired with the 1/τ residual factor; if unpaired use min(Cτ, ρ²).
Final statement stays at width 2 — the hardcoded Levi machinery unchanged.

## J4-94 (e701b5f4) — ★★ H1 discharged + zero-extension core + THE WIDTH FINDING
`QIQTH/GlobalWitnessHunif.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
`globalWitness_residual_bound_inChart_final` (all far-point antecedents discharged — hyps
only geometric+heat) + `heatOp_eq_zero_of_locally_zero` (H2-core) + `metricInv_left_of_
right`. DECISIVE: same-width hcoord PROVED structurally unsatisfiable (τ→0 forces
‖p−q‖≤‖v‖) ⟹ width-margin engine re-run forced (Sol G₁→G_{3/2}→G₂, verdict above).
J4-95 (WidthMarginEngine) in flight. Also firewalled: H2-transfer (φ_q open-map exposure).

## J4-95 (2eb876bc) — ★★★ WIDTH-MARGIN RE-PLUMB COMPLETE: τ→0 obstruction RESOLVED
`QIQTH/WidthMarginEngine.lean` (18 thms, ns HeatResidualBound), [AF] std-3, indep verified.
M1 width-parametric absorptions (single gaussDdim_width_ratio identity; A3 chart transfer
= the unlock) + M2 narrow engine (G_{3/2}, width 6τ; no unpaired r² — τ-caveat moot) +
M3 `globalWitness_residual_bound_chartGaussian` at the CONSUMER width gaussDdim(2τ)(φ_qv−q).
ONE input left: hdisp near-isometry budget — J4-96 (in flight) discharges via retained
Neumann bound + segment MVT + ℓ²-direct summation (dodges the sup-norm n-factor).

## J4-96 (6138f431) — ★★★ hdisp DISCHARGED: consumer-width bound fully unconditional in-chart
`QIQTH/NearIsometryBudget.lean` (ns ExpMap + HeatResidualBound), [AF] std-3, indep verified.
Ball-restatement required (global hdisp false). `uniformFlowExp_zero` (confinement at 0) +
unconditional near-id `‖Dφ−Id‖≤C_D‖v‖` (Grönwall tail re-derivation) + displacement
`‖φv−q−v‖≤C_D‖v‖²` (segment MVT) + `uniformFlowExp_hdisp_ball` (ℓ²-direct, n absorbed) ⟹
CAPSTONE `globalWitness_residual_bound_chartGaussian_final` — hyps only geometric+heat.
NEXT: J4-97 (in flight) = the ∀p assembly (gated witness trichotomy + q-gate +
RecenterReduction feed) ⟹ GLOBAL hEboundW.

## J4-97 (73e238ea) — ★★★ gating machinery + hEboundW reduction to ONE hypothesis
`QIQTH/GlobalHunifAssembly.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
`heatOp_congr_nhds` + `gatedKernel` (q-gate ∘ set-gate; τ-independent hard gate ⟹ exact
time germ) + in/out transfer legs + `gatedKernel_hEboundW_of_trichotomy` — the EXACT
capstone hEboundW primitive, conditional on the single per-p trichotomy htri.
J4-98 (in flight) = htri discharge: chart-openness exposure + gate S=φ_q''(ball r₀'')
with closure⊆V + the 3-LEG variant (in-ball bound / off-closure / χ-collar locally-0).

## J4-98 (b2ba7be1) — ★★★ 3-leg cover: hEboundW reduced to the RADIUS-ORDERING residue
`QIQTH/HunifTrichotomy.lean` (389 lines, ns HeatResidualBound), [AF] std-3, indep verified.
J4-97's 2-leg htri too coarse at the frontier — resolved by the 3-leg cover (in-gate /
off-closure / χ-collar with the ‖W p‖=c pinch, no injectivity, no e.symm agreement).
Unconditional: `basepointChart_exists_strong` (W1) + `chartImage_ball_open_closure` +
cover reductions + collar engine. Conditional on hgood: `gatedWitness_hEboundW` — sole
residue = b < c radius ordering under the τ-free transport radius. J4-99 (in flight) =
b-parametric engine + quantifier hoist ⟹ discharge ⟹ the hEboundW primitive.

## J4-99 (17e7cc9a) — ★★★ τ-uniformity + radius ordering DISCHARGED
`QIQTH/RadiusOrdering.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
R1 engine monotone in b (`_below` variant, ∀ρc); R2 per-q τ-free r₀ hoist (∀f-naturality
+ hoisted transport); R4 `gatedWitness_hEboundW_final` — the circularity broken by
choosing radii BEFORE (a,b). ONE input left: huniformChart = K-uniform IFT source-ball
radius. J4-100 (in flight) = quantitative uniform IFT via ApproximatesLinearOn (exposed
source!) with Id as the linear approximation (near-id + Hessian-Lipschitz uniform data).

## ★★★★ J4-100 (e5b98332) — THE hunif SUMMIT: hEboundW FULLY UNCONDITIONAL
`QIQTH/UniformChartRadius.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
Mathlib ApproximatesLinearOn (source EXPOSED) + near-id MVT ⟹ K-uniform chart radius ⟹
`uniformInverseChart` + huniformChart discharged ⟹ chart-generic capstone copies ⟹
`gatedWitness_hEboundW_unconditional`: ∃ a b B S, ∀τ p q, |heatOp of the gated concrete
witness| ≤ B·baseKernelW 2 0 τ p q — hyps ONLY hg/hC/hK/hgnd/hgsymm/hinvF/hframeK/Θ/u/
hw0smooth/hw0flat. THE hunif/hEboundW TOWER (J4-80…J4-100, 21 bricks, ONE session) IS
COMPLETE. Remaining to a₁=R/6: capstone wiring (hHdiag concrete-parametrix identification
+ hInt/hEzero/hEmeas + hDH/hDConv/hCH/hCConv + RNC jets) + hDuhamel/hInter (last wall).

## J4-101 (2ec8c9a5) — ★★ WIRING CENSUS + concrete van-Vleck hEboundW
`QIQTH/CapstoneWiring.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
CENSUS: gauge inputs carried genuine; hEboundW LANDED (`gatedWitness_hEboundW_vanVleck`
at Θ:=vanVleck g, u:=transportCoeff — the capstone's slot); hHdiag = ORDER-N REBUILD
(N=0 version landed via `gatedWitness_diag_eval_vanVleck`; capstone's hN:1≤N keeps the
t·u₁ term, u₁(0)=R/6 = the extracted coefficient — order-0 witness cannot satisfy);
hInt/hEzero wiring-medium (hEzero needs n≥1); hDuhamel/hInter + conv-regularity = the
LAST WALL. J4-102 (in flight) = order-N rebuild census + N=1 near-residual core.

## J4-102 (771f8248) — ★ order-N rebuild OPENED
`QIQTH/OrderNResidual.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
CENSUS: residual identities already general-N in-repo; ~150 N=0 sites statement-level
(proofs N-agnostic); genuinely new = ONLY the N=1 Gaussian bound. LANDED: N-generic near
packet consumer (+N=1), `parametrixResidual_one_diag_tail` (τ¹ tail = −G·Δw₁(0)·t),
`globalCutoffParametrixWitnessN`. J4-103 (in flight) = the N=1 Gaussian bound (w₁ jets +
four-term C³ estimate; ⚠ large-τ hEboundW-shape question flagged for early Sol consult).

## J4-103 (8cfedba9) — ★★ THE N=1 GAUSSIAN BOUND (the order-N rebuild's genuine new brick)
`QIQTH/ResidualN1GaussianBound.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
`foldedCoeff_shift` rfl ⟹ the N=0 bound reuses verbatim for w₁; `parametrixResidual_one_
split` (R₁ = R₀[u] + H₀[u'] + t·R₀[u'], exact) ⟹ `residualN1_gaussian_bound` (+ ball):
(C₀+W₁+t·C₁)·gaussDdimWide. New genuine inputs = the w₁ jets. LARGE-τ: baseKernelW's α
slot is a τ-margin; capstone α=0 unsatisfiable for N=1 ∀τ; theory needs only τ∈(0,t].
J4-104 (in flight) = restricted-hypothesis capstone census/variant.

## J4-104 (3a10aab9) — ★★★ capstone SHAPE FIX: the N=1 hEboundW obstruction DISSOLVED
`QIQTH/RestrictedEboundW.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
Census: every hEboundW/hInt use is at τ≤t (single site, Ioo 0 t integrals). Route β:
(0,t]-restricted chain mirrors ⟹ `trueKernel_diagonal_a1_eq_R6_residual_restricted`
(hEboundW weakened to ∀τ≤t) + `mixedAlpha_to_alpha0_le` (C(1+T) collapse) +
`capstone_inputs_N1_shape` (the N=1 mixed-α bound ⟹ the restricted capstone's slot).
J4-105 (in flight) = the N=1 tower re-run (T1 uniform bound via split+reuse → T2 narrow
→ T3 abstract-layer re-instantiation → T4 gatedWitnessN1_hEboundW_mixed → T5 N=1 hHdiag).

## J4-105 (7fdc1399) — ★★★ N=1 TOWER RE-RUN: analytic heart + mixed cover + hHdiag
`QIQTH/OrderOneTower.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
T1 `uniformResidualN1_narrow_mixed` ((B₀+B₁τ)·G_{3/2} uniform over K — split + profile-
abstract N=0 engine at u AND u'); T5 `gatedWitnessN1_diag_eval_vanVleck` (hHdiag at N=1!);
T4 mixed cover ⟹ the restricted capstone's hEboundW_le. FIREWALL: the N=1 transport
identity + cutoff engine (geometric leg, mechanical mirrors) = J4-106 (in flight).

## ★★★★ J4-106 (c5bf16b3) — the LAST GEOMETRIC LEG: two hardest capstone inputs CONCRETE at N=1
`QIQTH/OrderOneGeometry.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
Transport mirrors near-verbatim + the affine-in-τ engine trick (no chain re-run) + the
mixed 3-leg cover ⟹ `gatedWitnessN1_hEboundW_le_vanVleck`. With J4-105's hHdiag: the
restricted capstone's hEboundW_le AND hHdiag both concrete. Carried: hCoeffU0/U1 (J4-107
in flight; ∂w₁(0) subtlety), hInt/hEzero/hEmeas, hD*/conv, hDuhamel/hInter, gauge.

## J4-107 (626f5d3d) + ★★★★ J4-108 (b705a605) — coefficient walls CLOSED
J4-107 `CoeffBoundsN1.lean`: hCoeffU0 DISCHARGED (van-Vleck flatness derived from gauge
via the Jacobi/det chain) + hEzero (Iic-uniqueness at τ=0) + K2 verdict (O(r²) hCoeffU1
PROVEN FALSE — 2∂u₁(0)=∂(Tu₀)(0)≠0).
J4-108 `CoeffU1Fix.lean`: the fix fully landed — odd-power absorption r·G ≤ C√τ·G' +
O(r) coefficient bound (no flatness) + √τ≤1+τ GLOBAL fold (better than the planned
ceiling) ⟹ `gatedWitnessN1_hEboundW_le_vanVleck_final`: NO coefficient hypotheses.
STATUS: hEboundW_le + hHdiag both maximally clean at N=1. Remaining: hEmeas/hInt →
conv-regularity (hDH/hDConv/hCH/hCConv) → hDuhamel/hInter (LAST wall) → gauge → assembly
via trueKernel_diagonal_a1_eq_R6_residual_restricted.

## J4-109 (caa2b128) — ★★ hInt via the TIME-CAP producer
`QIQTH/GatedWitnessMeas.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
The ∀τ-mismatch resolved by the time-cap (Sol-confirmed): `timeCap` + causal equality
`iterE_timeCap_eq` ⟹ `iterConvIntegrableW_of_locally_bound_baseMeas` (FULL hInt from the
(0,T]-local family, zero downstream re-plumb) + the concrete hand-off
`gatedWitnessN1_hInt_of_hEmeas`. FIREWALL: hEmeas (joint SM of heatOp H_G — the
parameterized-deriv + choose-chart crux; J4-110 in flight on the joint-measurability
routes: smooth-dependence / closed-graph / Picard iterates; carried-hyp fallback).

## J4-110 (a1656872) — ★★ hEmeas DECOMPOSED; joint-q wall deferred (3rd surfacing)
`QIQTH/GatedWitnessEmeas.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
Direct route WALLS: W1 flow joint-q (Classical.choose, multi-week per Sol) + W2 nested-pd
(deriv_with_param needs joint continuity). LANDED: flow-agnostic E3 field lemmas +
`gatedWitnessN1_hInt_of_kernelContinuity` (hInt from granular {Continuous H_G,
Continuous ∂ⱼH_G, hgiM, hchrM}). The joint-q residue = carried, clearly-labelled.
PIVOT: the hDuhamel campaign (needs no joint-q) — J4-111 conv-regularity in flight.

## J4-111 (ca80bbec) — ★★ the hDuhamel CAMPAIGN OPENER: conv-regularity engine
`QIQTH/HeatConvRegularity.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
C1 integrability + C2 continuity/FTC-upper + C3ε ε-truncated Leibniz (the key brick) +
C4p space-fderiv. Campaign map: B1 hDConv assembly, B2 ContDiff-⊤ induction, B3 concrete
dominations. J4-112 (in flight): D1 |H_G| chart-transfer domination, D2 leviSeries
domination, D3 hDH (explicit diagonal), D4 ⚠ hCH ⊤-vs-C²-chart assessment (load-bearing),
D5 hDConv assembly to the delta-family boundary.

## J4-112 (1bd50402) — ★★★ the C²-WEAKENED FINAL CAPSTONE + hDH
`QIQTH/ConcreteDominations.lean` (ns HeatResidualBound), [AF] std-3, indep verified.
D4 DECISIVE: ⊤-smoothness slots consumed only via ≤2 derivatives AND unsatisfiable for
the C² chart witness ⟹ `trueKernel_diagonal_a1_eq_R6_residual_restricted_C2` = THE FINAL
capstone shape (hCH/hCConv : ContDiffAt ℝ 2 at 0). hDH discharged concretely
(`gatedWitnessN1_hDH`). Firewalled: D1 |H_G| domination, D2 leviSeries domination,
D5 hDConv assembly. J4-113 (D1+D2) in flight.

## J4-113 (46fbfc59) — ★★ D1 witness domination (conditional GateSqControl form)
Additions to `ConcreteDominations.lean`, [AF] std-3, indep verified. Sol packaging verdict:
standalone ∃ not engine-consumable ⟹ the certificate form: `GateSqControl` +
`exists_D1_constants_of_gateSqControl` (|gated H₁| ≤ (A₀+A₁τ)√(3/2)ⁿ·G_{3/2}(p−q) ∀τ>0)
+ `gateSqControl_of_flowBall` (certificate from chart germ + hdisp). J4-114 (in flight) =
the certificate MERGE into the hE chain's ∃S + D2 Levi domination.

## J4-114 (6d27f99c) + J4-115 (85d25db0) — the shared-S package + hDConv→hDelta
J4-114 `GatedWitnessPackage.lean`: the certificate MERGE (gatedWitnessN1_package — ONE
shared S: hEboundW_le ∧ GateSqControl ∧ 0∈S ∧ D1 ∧ W(0,0)=0; .choose-spec re-export) +
leviSeries_dominatedW_le (abstract UNCONDITIONAL Levi domination).
J4-115 `HeatConvDeriv.lean`: hDConv REDUCED to hDelta (Sol: ε-split; the never-evaluated-
limit trick — hasDerivAt_of_tendstoLocallyUniformlyOn with existential D). Remaining D5:
concrete approximants (J4-116 in flight) + Lemma 3.14 (the irreducible singular brick).

## J4-116 BANKED (a3b463be) — 2026-08-02
ConvApproximants.lean [AF std-3, raw 0 @ 9373 jobs]: epsSeq + heatConv_tail_tendsto
(primitive-continuity, no tail estimate) + hDConv_of_delta_epsFamily (never-evaluated-limit
eps-split) + vanVleckGatedWitness + hDConv_gatedWitnessN1_epsFamily = the EXACT capstone
hDConv shape, conditional ONLY on {hFII, hJoint, hDelta}.
IN FLIGHT: J4-117 ConvCarriesDischarge.lean (agent a1e9361b46130abba, restarted post-suspend
2026-08-02 22:43): F1 hFII via D1×Levi dominations + gaussDdim_conv semigroup
(widths (3/2)(u−s)+2s ≥ (3/2)u); F2 hJoint via FTC b-partial + C3eps u-partial +
joint-2D-from-partials; F3 hDConv_gatedWitnessN1_of_delta_final (only deferred family + hDelta).
NEXT: J4-118 = the delta-family brick (Lemma 3.14 ⟹ hDelta, THE singular brick; Sol consult
on Lean shape first), then eps-Duhamel identity + hInter, then hCConv-C2 concrete, then gauge +
final assembly via trueKernel_diagonal_a1_eq_R6_residual_restricted_C2.

## J4-117 BANKED (aa5c3568) — 2026-08-03
ConvCarriesDischarge.lean [AF std-3, raw 0 @ 9401 jobs]: hFII + hJoint GONE from the
capstone hDConv shape. gaussDdim_zero_antitone + heatConvInner_intervalIntegrable_gaussianDom
(hFII domination fully discharged via gaussDdim_conv Chapman-Kolmogorov, constant G_{(3/2)u}(0))
+ heatConvFrozen_hasFDerivAt_of_partials (joint 2-D from hpar/htime/hR, F=H+J+R decomposition)
+ hDConv_(gatedWitnessN1_)of_delta_final. Remaining hDConv carries: hDelta + hMeasFII +
hpar/htime + hR (⟸ joint continuity of inner pairing) + parametric dominations.
NEXT (Sol-consulted 2026-08-03, decomposition CONFIRMED): J4-118 = hBoundary brick =
Lemma 3.14 delta-family: (i) helper tendsto_integral_gaussDdim_smul via NEAR/FAR split
(NOT substitution: mass-1 ∫gaussDdim=1 from gaussianZerothMoment_oneD product + Gaussian
tail→0; Mathlib has NO usable peak-function lemma); (ii) boundary_tendstoUniformlyOn_compact
under hBcont := ContinuousOn (fun (x:ℝ×Point n) => B x.1 x.2 0) (Ioc 0 T ×ˢ univ) via
IsCompact.uniformContinuousOn Heine-Cantor; (iii) hDelta = hDaLim.add hBoundary
(TendstoLocallyUniformlyOn.add), D u := DaLim u + B u 0 0. hDaLim deferred (same singular
integrand as Da). A-side: fixed diagonal ball where A = G·(u₀+τu₁), 4-way split
(main/ε·u₁/off-ball via (3/2)ε-domination tail/mass defect).

## J4-118 BANKED (f8f8ab50) — 2026-08-03
DeltaFamilyBoundary.lean [AF std-3, raw 0 @ 9402 jobs]: mass-one gaussDdim_integral_eq_one
+ THE Lemma-3.14 approximate-identity core tendsto_integral_gaussDdim_smul (NEAR/FAR split;
conditional hmeas + hTail) + tendstoLocallyUniformlyOn_add (Mathlib lacks it — proved) +
hDelta_of_boundary(_shifted) + hDelta_gatedWitnessN1_of_boundary (concrete hDelta feed,
D u = DaLim u + B u 0 0). HONEST: Brick 2 hBoundary (moving-peak concentration) NOT proved —
BOTH factors m-dependent (peak A(ε_m) AND drift B(u−ε_m)); needs the equicontinuous-FAMILY
variant of the approximate identity + Heine–Cantor from hBcont. Carries now: hTail, hBoundary,
hmeas, hDaLim.
NEXT: J4-119 = GaussianTailBoundary.lean: (T1) hTail via 1-D tail × union bound (|z|≥δ ⟹
∃k |z_k|≥δ/√n; ≤ n·tail1D·mass — AVOID n-D change of variables) + (T2) equicontinuous-family
approximate identity (∀η ∃δ ∀ᶠm ∀z∈ball δ, |h m z − c|≤η ⟹ ∫G_{ε_m}h_m → c) + (T3) hBoundary
= Brick 2 via T2 with h m z := u₀ z·B(u−ε_m,z,0), Heine–Cantor on Icc(a/2,T)×closedBall 0 r₀,
4-way split (main/ε·u₁/off-ball (3/2)ε-tail/mass defect).

## J4-119 BANKED (a60bdaa8) — 2026-08-03
GaussianTailBoundary.lean [AF std-3, raw 0 @ 9403 jobs]: T1 hTail UNCONDITIONAL
(gaussDdim_tail_tendsto_zero; explicit n·√2·e^{−δ²/8t}; Pi sup-metric union bound, no √n) +
T1★ tendsto_integral_gaussDdim_smul_of_meas (Lemma 3.14 with hTail gone) + T2 family variant +
T2u tendstoUniformlyOn_integral_gaussDdim_smul_family (parameter-uniform main-term engine).
T3 hBoundary deferred (200+-line 4-way assembly; T2u full-space vs ball-r₀ A-form mismatch
needs an off-ball A-tail bridge).
NEXT: J4-120 = BoundaryAssembly.lean: T3 boundary_tendstoLocallyUniformlyOn (4-way split:
main via T2u + Heine–Cantor; ε·u₁; off-ball (3/2)ε-tail via T1 + gaussDdim diagonal cap;
mass defect via T1) + concrete hDelta_gatedWitnessN1_final (hBoundary killed).
Traps for the agent recorded: indicator_of_notMem, integral_finsetSum, heatKernel1D_pos
arg order, beta-redex show-reduce, (n := n) pinning.

## J4-120 BANKED (52c41399) — 2026-08-03: BRICK 2 hBoundary DISCHARGED
BoundaryAssembly.lean [AF std-3, raw 0 @ 9404 jobs]: boundary_tendstoLocallyUniformlyOn (T3,
full 4-way split via T2u + Heine–Cantor + tails) + hDelta_gatedWitnessN1_final (concrete hDelta,
hBoundary GONE) + peak/evenness/B-sup helpers. hDConv delta-chain closed up to hDaLim.
SOL CONSULT (2026-08-03, J4-121 spec): (1) hDuhamel decomposition: do NOT split ∂_t/Δ_x full
limits (each diverges 1/τ — needs moment cancellation); COMBINE at finite ε: heatConvFrozen a-slot
Leibniz (Brick 2.1 hDa_trunc, regular u−s≥ε) + Δ_x finite-gap interchange (2.2 hLap_trunc) +
E-combination BEFORE ε→0 (2.3 Da m u = LapTrunc m u + Etrunc m u) + hTruncDuhamel (2.4);
limits: Boundary→F PROVEN (delta family), Etrunc→E*F easy (E has NO 1/τ), LapTrunc limit = THE
hard C²_x truncation-tail (carry as hDaLim : Da → Δ_x(H*F)+E*F — the honest analytic carry);
then hDuhamel = pure algebra (hDuhamel_of_derivValue). (2) hInter: integral_tsum on
(volume.restrict (Ioc 0 t)).prod volume + factorial majorant M k = C₀(C₁t)^{k+1}/(k+1)! (Levi
bounds EXIST in repo); helper heatConv_tsum_of_summable_integral_norm; plumbing not hard.
(3) ORDER: J4-121 = hInter FIRST (self-contained, retires capstone input II); then J4-122 =
truncated-Duhamel skeleton (2.1-2.4); then hDaLim formulation with DaLim := Δ_x(H*F)+E*F.
NEXT: J4-121 per Sol statement list (leviLeftTerm, factorial L¹ bound, majorant summable,
integral_tsum helper, instantiation, coefficient normalization, hInter).

## J4-121 CORRECTION — 2026-08-03: hInter was ALREADY CLOSED (4bff8b12, Jul 31)
LeviInterchange.lean (heatConv_leviSeries_interchange) has been in main since Jul 31: hInter
reduced to the standard {hEbound, hEzero, hEmeas, hC, ht} carries via
integral_tsum_of_summable_integral_norm ×2 + iterConvW_bound + gaussDdim_conv +
scaledIterKernelW_summable. Tonight's J4-121 agent verified it green (std-3) — NO new bank.
⚠ don't-under-credit failure repeated: grep QIQTH/ + AxiomAudit BEFORE launching a brick.
Known residue noted by verification: hEbound there is ∀τ>0 unrestricted vs the capstone's
τ≤t-restricted hEboundW_le — reconciliation is a small wiring increment (check RestrictedEboundW
first — may already cover it).
NEXT: J4-122 = truncated-Duhamel skeleton (Sol 2.1-2.4): Ktrunc/Boundary/Etrunc/Da defs +
hDa_trunc (finite-gap a-slot Leibniz) + hLap_trunc (finite-gap Δ_x interchange) +
Da = LapTrunc + Etrunc (E-combination BEFORE ε→0) + hTruncDuhamel.

## J4-122 BANKED (219ee736) — 2026-08-03: hDuhamel REDUCED to hDaLim
TruncatedDuhamel.lean [AF std-3, raw 0 @ 9405 jobs]: the finite-ε skeleton (2.1 hDa_trunc,
2.3 hE_combination ∂_t−Δ_x=E-before-limit, 2.4 truncDuhamel_deriv + heatOp_trunc) +
hDuhamel_of_daLim + hDuhamel_leviSeries_of_daLim (capstone shape VERBATIM). Carries:
hDaLim (THE hard one) + hLap (2.2) + hDerivConv + hBoundaryLim + F2 family.
NEXT: J4-123 = DuhamelLimitWiring.lean: W1 hBoundaryLim ⟸ boundary_tendstoLocallyUniformlyOn
(pointwise, sub_sub_cancel reconcile); W2 Etrunc→E*F (sliver ≤ const·ε, E has NO 1/τ);
W3 hDerivConv ⟸ hDConv chain (hasDerivAt_of_tendstoLocallyUniformlyOn + truncDuhamel_deriv);
W4 hDuhamel_leviSeries_final (conditional ONLY on hDaLim + hLap + F2 + dominations + meas).
THEN: hDaLim deep-dive (Sol consult: tractable vs long-term carry) + hLap + hCH/hCConv-C² +
regularity family + gauge + FINAL ASSEMBLY.

## J4-123 BANKED (92ae55c5) — 2026-08-03: hDuhamel = hDaLimLU + families ONLY
DuhamelLimitWiring.lean [AF std-3, raw 0 @ 9406]: W1 boundaryTrunc_tendsto + W2 etrunc_tendsto
+ truncDuhamel_hasDerivAt + W3 derivConv_tendsto + W4 hDuhamel_(leviSeries_)final (capstone
VERBATIM). ALL soft carries of J4-122 discharged.

## SOL hDaLim ARCHITECTURE (consult 2026-08-03, recorded verbatim intent)
hDaLimLU ⟺ LapTrunc → Δ_x(H*F) (Etrunc part PROVEN). NOT a monolith — split:
- THREE labelled interfaces: hGaugeLap (Δ_g at 0 = Σᵢ∂ᵢ² under hg0/hgi/hΓ/hdg0 gauge — MEDIUM,
  prove early); hParametrixC2Gaussian (small-time H = G·A factorization + A/∂A/∂²A bounds +
  support, from the concrete witness — HARD/wall-ish but extractable); hFLocLip (spatial
  Lipschitz of F on compact positive-time slabs — genuinely NEW input, NOT implied by Gaussian
  domination; carry short-term; discharge later via F = −E − E*F resolvent + E-spatial-difference
  Gaussian bound |∇_zE| ≤ Ct^{-1/2}G_{ct} — avoid termwise Levi differentiation).
- Then PROVE: hGaussianHessianCancellation (∫∂ᵢ²G_τ = 0 second-moment; Lipschitz multiplier
  gains τ^{-1/2} integrable; seed = gaussianSecondMoment_oneD) + sliver estimates j=0,1,2
  (LINEWISE coordinate derivatives, NOT Fréchet Hessian) + finite-ε coordinate differentiation
  + derivative-of-limit ×2 + u-uniformity + gauge-sum assembly.
- Difficulty map: gauge lemma M; moments M; weighted Gaussian deriv estimates H; cancellation H;
  amplitude package H/wall; sliver-2 H; finite-ε 2nd-order H; assembly E-M. Mathlib gaps:
  campaign-specific Gaussian cancellation library needed (no generic PDE theorem).
- Do NOT fully unfold the Levi series (F stays abstract with hFLocLip).
NEXT: J4-124 = hGaugeLap (the normal-coordinate reduction — early, load-bearing, medium) +
Gaussian coordinate-derivative formulas + second-moment identities (seeds exist). Then the
cancellation lemma; then amplitude package; then slivers.

## J4-124 BANKED (18aa16ed) — 2026-08-03: THE CANCELLATION LIBRARY
GaussianHessianCancel.lean [AF std-3, raw 0 @ 9407]: G1 Hessian coefficient + G2 exact
∫∂ᵢ²G = 0 + G3 weighted moments ((15/2)/√t workhorse via the G_{2t} re-route, no 4th moment)
+ G4 gaussian_hessian_cancel (Lipschitz q ⟹ ≤ L·(15/2·n)/√t). All at x=0 (RNC center).
Deferred small: grad-cancel odd analogue + 2√ε corollary → J4-125.
NEXT: J4-125 = SliverEstimates.lean (S0 grad-cancel + rpow sliver corollary; S1/S2 linewise
sliver bounds j=0,1,2 on the FORMAL-derivative integrals — Sliver2 via the 3-term
∂ᵢ²(G·A) expansion + G4 with q := Aamp·F (hqLip carry = the hFLocLip family) + amplitude
interface hyps hAfact/hAampBdd/D1/D2 + derivative-domination tails; identification with
actual derivatives = the LATER finite-ε differentiation brick).

## J4-125 BANKED — 2026-08-03: THE SLIVER ESTIMATES
SliverEstimates.lean [AF std-3, raw 0 @ 9408]: S0a grad-cancel (t-FREE!) + S0b 2√ε family +
S1 j=0 ≤ C·ε + S2 sliver2_bound (3-term Leibniz + G4; Lipschitz carry only on term 1).
Interface carries fixed: hD2Hexpand + M₀/M₁/M₂ + hqLip + hFdom + meas.
NEXT: J4-126 = AmplitudePackage.lean (instantiate D2H/Aamp from vanVleckGatedWitness:
A1 x=0 factorization + the x-derivative layer from the C⁴ chart tower; A2 compactness bounds;
A3 half-concrete fallback = u₀-layer + documented derivative residue). Then finite-ε
differentiation; then hDaLimLU assembly conditional on {hFLocLip, amplitude residue}.

## J4-126 BANKED (a0d5086e) — 2026-08-03: AMPLITUDE PACKAGE + THE CHART FINDING
AmplitudePackage.lean [AF std-3, raw 0 @ 9409]: A0 map (on-gate value = radialCutoff(W z 0)·
G_τ(W z 0)·Θ^{-1/2}(W z 0)·(u₀+u₁τ)(W z 0) — Gaussian argument = CHART IMAGE) +
vanVleckGatedWitness_zero_factor + witnessSecondXDeriv anchor + AmplitudeDerivativeData +
amplitudePackage_sliver_bound. FINDING: literal hAnear NOT satisfied by the witness (chart
argument); reconciliation = new frontier.

## SOL ADAPTER PLAN (consult 2026-08-03 #2): "R2.5" — L¹ KERNEL-REPLACEMENT ADAPTER
Keep ALL proven plain-z interfaces; add the adapter layer:
- B1 chartGauss_l1_sub_plain_tendsto (5/10): ∫|G_τ(W z)−G_τ(z)| → 0 on the active set S,
  hyps = coarse coercivity (c‖z‖²≤‖W z‖² on S — excludes remote zeros; must come from chart
  injectivity/gate) + shrinking-ball near-isometry hasymp (∀δ ∃r); proof = two-stage ε (δ then
  r then τ): inside ball the (1±δ)-width sandwich U−L with exact full-space integral
  (1−δ)^{-n/2}−(1+δ)^{-n/2}; outside = tails via gaussDdim_width_ratio. NO change of variables;
  mass J=1 falls out.
- B2 bounded-multiplier corollary (2/10); B3 repackage amplitude ũ₀/ũ₁ := (cutoff·Θ^{-1/2}·u)∘W
  with ũ₀(0)=1 (3/10); B4 boundary wrapper: I_chart − B(u,0,0) = (I_chart−I_plain) + proven
  (3/10).
- SLIVER-2 (separate, later): S1 exact Gaussian chain-rule Hessian formula (⟨Y,Pᵢ⟩²/4τ² −
  (‖Pᵢ‖²+⟨Y,Qᵢ⟩)/2τ shape) (4/10) + S2 Leibniz normal form (4-5/10) + S3 chart-jet package
  Y=z+O(‖z‖²), Pᵢ=±eᵢ+O(‖z‖), Qᵢ=qᵢ+O(‖z‖) from C⁴ tower (5-6/10) + S4 general weighted-moment
  envelope ∫τ^{-m}‖z‖^k G_{κτ} ≤ Cτ^{k/2−m} (4/10) + S5 quantitative cubic replacement
  |G_τ(Wz)−G_τ(z)| ≤ C‖z‖³/τ·G_{κτ}(z) (7/10) + S6 normal form: canonical Hermite + centerJet
  (do NOT abs the odd ⟨z,qᵢ⟩/2τ term — exact parity cancellation!) + remainder (7/10).
ORDER: B1→B2→B3→B4 (J4-127) then S1..S6.

## J4-127 BANKED (ea2aa854) — 2026-08-03: THE CHART-TO-PLAIN ADAPTER (B1+B2+B3)
ChartGaussAdapter.lean [AF std-3, raw 0 @ 9410]: Gk_scaled + B1 (L¹ replacement, two-stage ε,
no change-of-vars) + B2 (bounded multiplier) + B3 (witness_sub_plain — the concrete witness
minus the SYNTHETIC plain kernel = adapter difference × (ũ₀+τũ₁); the plain kernel satisfies
the literal hAnear!). Carried: B4 assembly + concrete hcoarse/hasymp (J4-128).
NEXT: J4-128 = ChartWrapperConcrete.lean: C1 hcoarse/hasymp discharge from NearIsometryBudget
(|rnsq(Wz)−rnsq z| ≤ 2‖z‖·‖Wz−z‖+‖Wz−z‖² algebra; shrink-or-tails for the full gate);
C2 center values ũ₀ 0 = 1 + bounds; C3 boundary_chart_wrapper_concrete assembly.

## J4-128 BANKED — 2026-08-03: CONCRETE WRAPPER LAYER + THE ISOLATED INPUTS
ChartWrapperConcrete.lean [AF std-3, raw 0 @ 9411]: center values DONE (ũ₀ 0 = 1 = hu₀one!;
chartAmp1_at_zero = the R/6 seed) + concrete B1/B2 + the C3 split scaffold. Isolated inputs:
(1) inverse-chart near-isometry (exp-side→W-side bootstrap, J4-129); (2) base-point
continuity/measurability of z ↦ W₀ z (.choose obstacle); (3) gate-ball containment.
NEXT: J4-129 = InverseChartDisplacement.lean: D1 the bootstrap ‖v₀ ± z‖ ≤ C‖z‖² from
φ_z(v₀) = 0 + exp displacement (SIGN: W z 0 ≈ −z; rnsq is even — fine); D2 hasymp₀/hcoarse₀
in the exact carried shapes; D3 measurability via uniqueness/selection or honest carry;
D4 gate-ball via cf floor; D5 boundary_chart_wrapper_final.

## J4-129 BANKED — 2026-08-03: BLOCKER (1) DOWN — inverse-chart near-isometry PROVEN
InverseChartDisplacement.lean [AF std-3, raw 0 @ 9412]: chartW0_displacement (bootstrap via
ApproximatesLinearOn right-inverse + germ pin; W₀ z ≈ −z) + chartW0_nearIsometry (hcoarse₀
c=1/2 + hasymp₀ exact shapes) + chartW0_l1_sub_plain_of_meas (only hWmeas₀ carried).
Blockers left: (2) base-point flow regularity (labelled hWmeas₀), (3) gate-ball cf floor.
NEXT: J4-130 = ChartJetHessian.lean (S1 exact Gaussian chain-rule Hessian for
x ↦ gaussDdim τ (W z x): G·[⟨V,∂ᵢV⟩²/4τ² − (⟨∂ᵢV,∂ᵢV⟩+⟨V,∂ᵢ²V⟩)/2τ] + S2 Leibniz normal
form toward the S6 canonical-Hermite + centerJet + remainder decomposition of
witnessSecondXDeriv; jet hyps carried, C⁴-satisfiable).

## J4-130 BANKED — 2026-08-03: THE CHART-JET HESSIAN (S1+S2+S3-seed, exact)
ChartJetHessian.lean [AF std-3, raw 0 @ 9413]: gaussComp_pd/pd_pd (exact chart Hessian) +
gaussComp_amp_pd_pd (Leibniz) + gaussComp_amp_center_decomp (canonical Hermite + EXACT odd
centerJet + cross; no estimates). NO commutation carry.
NEXT: J4-131 = GaussianMomentEnvelope.lean (S4 general ∫τ^{-m}‖z‖^k G_{κτ} ≤ Cτ^{k/2−m}
envelope via 1-D moments k=0..4 + S5 quantitative cubic replacement |G_τ(Wz)−G_τ(z)| ≤
C‖z‖³/τ·G_{κτ}(z) via MVT + chartW0_rncRadialSq_error + Gk_scaled; weighted corollary
τ^{(k+1)/2}). Then S3 jet bounds + S6 assembly into sliver2_bound.

## J4-131 BANKED (916c0cde) — 2026-08-03: S4 ENVELOPES + S5 CUBIC REPLACEMENT
GaussianMomentEnvelope.lean [AF std-3, raw 0 @ 9414]: 1-D moments k=0..4 + n-D envelope +
S5b gaussDdim_replace_bound (exact J4-129 hyp shapes) + S5c (√τ)^{k+1} weighted rate.
NEXT: J4-132 = ChartJetBounds.lean (S3: field-slot jets of V := uniformInverseChart z ·:
J1 existence via inverse-function differentiability; J2 center values P=eᵢ at z=0 +
POSSIBLE q_i = 0 under the capstone gauge hΓ(0)=0 — would kill the centerJet at the
assembly point!; J3 quantitative ‖P−eᵢ‖ ≤ C‖z‖, ‖Q‖ ≤ C_Q via fderiv-near-id + Neumann
inversion + BasepointJetModulus). Then S6 assembly.

## J4-132 BANKED — 2026-08-03: CHART JETS — P=eᵢ EXACT; CENTERJET DEAD AT ASSEMBLY POINT
ChartJetBounds.lean [AF std-3, raw 0 @ 9415]: DV₀(0)=Id tower-derived; centerJet contraction
∑(V₀0)ₖQₖ = 0 unconditionally (V₀0=0). Carried: J1b + raw D²V₀(0)=0 + J3 z-moduli.
⚠ S6 nuance: the vanishing is at base 0; the sliver integrand's jets sit at base z — the
centerJet there is O(‖z‖·C_Q/τ)·G ⟹ CRUDELY integrable (τ^{-1/2} rate) given ‖Q(z)‖ ≤ C_Q
(J3 carry) — NO parity argument needed anywhere.
NEXT: J4-133 = SliverAssembly.lean (S6: concrete witnessSecondXDeriv sliver ≤ C√ε — normal
form + Hermite-argument bridge via S5 cubic replacement + jet expansions (J3 labelled) +
centerJet crude + G4 cancellation with hqLip ⟹ the concrete AmplitudeDerivativeData
discharge modulo {hqLip, J3 moduli, J1b, meas}).

## J4-133 BANKED — 2026-08-03: S6 ASSEMBLY (bridges + skeleton)
SliverAssembly.lean [AF std-3, raw 0 @ 9416]: T1' Hermite bridges PROVEN + exp_tail_beats_inv
+ witness_sliver2_assembly ((C₀+C₁)·2√ε + C₂·ε). Carried: hNormalForm + hInner0/1/2 + meas.
NEXT: J4-134 = InnerSliceBounds.lean (discharge hInner0/1/2: I0 via S5b replacement + bridges
+ G4 cancellation (hqLip); I1 crude gradient; I2 mass; I3 witness_sliver2_final composite).

## J4-134 BANKED — 2026-08-03: I1+I2 DISCHARGED + THE COERCIVITY LEVER
InnerSliceBounds.lean [AF std-3, raw 0 @ 9417]: gaussDdim_halfcoer_le + selfmul product +
hInner1/2_discharge (exact assembly shapes, explicit constants). I0 deferred: k=5 moment +
entangled Hermite threading.
NEXT: J4-135 = HessianSliceBound.lean (M5 oneD_absMoment5 (AM-GM from k=4 + even k=6) +
oneD_absMoment6 + I0 hInner0_discharge (E1 replacement worst-term ‖z‖⁵/τ³→τ^{−1/2}; E2
proven bridges; E3 G4 with hqLip) + I3 witness_sliver2_final — the sliver-2 chart program
CLOSED modulo {hNormalForm, hqLip, hco/hYdisp/hJ3/hJ3Q, M₀/₁/₂, hFdom, meas}).
Traps added: ∫ z binder greedy (parenthesize); field_simp mixed τ/√τ (set w := √τ);
gcongr nonneg side-goals; sorryAx grep + ^error: + exit code.

## J4-135 BANKED — 2026-08-03: I0 + THE I3 MILESTONE
HessianSliceBound.lean [AF std-3, raw 0 @ 9418]: moment tower k≤9 complete + T_E3 exact
cancellation @ τ^{−1/2} + polyChartDiff pointwise + hInner0_discharge + witness_sliver2_final
(all three slices in). Carried: hRem (cancellation-free remainder — J4-136 pure integration)
+ hqLip + geometric inputs.
NEXT: J4-136 = RemainderIntegration.lean (hRem discharge: T_E2 via polyChartDiff × moments
k=2..6 with τ₀-absorption; T_E1 via two-term herr (2nC_W‖z‖³+nC_W²‖z‖⁴) × replace-bound ×
moments k≤9; conclusion witness_sliver2_complete — carries only {hNormalForm, hqLip,
hco/hYdisp/hJ3/hJ3Q, M₀/₁/₂, hFdom, meas}).

## J4-136 BANKED — 2026-08-03: hRem DISCHARGED (E2 proven)
RemainderIntegration.lean [AF std-3, raw 0 @ 9419]: tE2_slice_bound (E2 fully proven) +
hRem_discharge (exact shape) + witness_sliver2_complete (hRem gone, hInt0 derived).
NEXT: J4-137 = GaussReplaceSlice.lean (hRemE1: R1 two-term G-diff pointwise bound (mirror
replace_bound with 2nC_W‖z‖³+nC_W²‖z‖⁴); R2 crude polyChart cap; R3 termwise moments
(k,m) ∈ {(5..10,3),(3..6,2)} with oneD_absMoment10 added; R4 hRemE1_discharge +
witness_sliver2_grand + hIntT1/2/3 attempts). After: sliver-2 closed to interface residue ⟹
pivot to finite-ε differentiation + hNormalForm + gauge assembly ⟹ hDaLimLU.

## J4-137 BANKED — 2026-08-03: SLIVER-2 INTEGRATION CLOSED (witness_sliver2_grand)
GaussReplaceSlice.lean [AF std-3, raw 0 @ 9420]: hRemE1 discharged (two-term rnsq-diff +
degree-10 termwise moments); both remainder halves now theorems. Sliver-2 residue =
interface only: {hco/hYdisp/hJ3/hJ3Q, M₀/₁/₂, hFdom, hNormalForm, hqLip, integrabilities}.
NEXT: J4-138 = NormalFormDischarge.lean (N1 hNormalForm_concrete via gaussComp_amp_pd_pd
instantiation for the witness — jets from ChartJetBounds, general-base as J1b/C² carry;
N2 witness_sliver2_concrete for the actual witnessSecondXDeriv; N3 LapTrunc connection via
laplaceBeltrami_at_rnc_center begin). Then finite-ε differentiation + derivative-of-limit +
gauge assembly ⟹ hDaLimLU.

## J4-138 BANKED — 2026-08-03: hNormalForm DISCHARGED (witness_sliver2_concrete)
NormalFormDischarge.lean [AF std-3, raw 0 @ 9421]: pd germ-congruence + hNormalForm_concrete
+ off-gate vanishing + the terminal √ε bound for the ACTUAL witnessSecondXDeriv.
NEXT: J4-139 = LapTruncAssembly.lean (L1 gauge reduction via laplaceBeltrami_at_rnc_center;
L2 finite-gap Δ↔∫ interchange (labelled family OK); L3 the sliver-difference identity +
limit via witness_sliver2_concrete rate √ε_m; L4 hDaLimLU assembly: Da = LapTrunc + Etrunc
(proven) + L3 ⟹ Tendsto Da → Δ_x(H*F)+E*F = THE hDuhamel_of_daLim target — the conditional
hDaLimLU discharge).

## J4-139 BANKED — 2026-08-03: ★ THE CONDITIONAL hDaLimLU DISCHARGE ★
LapTruncAssembly.lean [AF std-3, raw 0 @ 9422]: hDaLim_full (DaTrunc → Δ_g(H*F)+E*F) +
hDuhamel_assembled (heatOp(H*F) = F + E*F end-to-end). The hDaLim carry — THE sole hard
limit the whole Duhamel wall funneled into — is discharged conditional on the explicit
residue: {hgi/hΓ, hInterchange, hLapFull, hII, B/hSliver/hBlim (⟸ sliver-2), 4 proven-lemma
outputs}. NEXT: J4-140 = SliverSumPlumbing.lean (P1 hSliver/hBlim instantiation; P2 thread
the 4 proven lemmas ⟹ hDuhamel_semifinal; P3 begin hInterchange). Then the deep residue +
final assembly.

## J4-140 BANKED — 2026-08-03: hDuhamel_semifinal (ONE theorem, complete grouped residue)
SliverSumPlumbing.lean [AF std-3, raw 0 @ 9423]: all six supplier slots discharged.
Residue groups: GAUGE {hgi,hΓ} · INTERCHANGE {hInterchange,hLapFull,hDa,hLap} ·
INTEGRABILITY · GEOMETRIC-MODULI {hbnd distilled — ε-uniformization small brick} ·
AMPLITUDE · DOMINATION · F2 · MEASURABILITY.
NEXT: J4-141 = SecondOrderInterchange.lean (Q1 first-order differentiation under ∫∫ at the
finite gap; Q2 second-order; Q3 hLapFull improper route; Q4 thread hDa/hLap).

## J4-141 BANKED — 2026-08-03: hInterchange DISCHARGED (the riskiest INTERCHANGE carry)
SecondOrderInterchange.lean [AF std-3, raw 0 @ 9424]: Q1+Q2 second-order under-∫∫ at the
finite gap + hInterchange_discharge VERBATIM. Carried: dominated-engine families
(C4b-satisfiable) + hQ1-nbhd + hpdpdH. NEXT: J4-142 = InterchangeThreading.lean (T1 hDa/hLap
threading via hDa_trunc + hInterchange_discharge ⟹ hEcomb_discharged; T2 hLapFull reduction
(Q2-instances + hLHSlim carry + sliver rate ⟹ uniqueness-of-limits); T3 hDuhamel_penultimate
with the INTERCHANGE group reduced).

## J4-142 BANKED — 2026-08-03: THE INTERCHANGE GROUP CLOSED (hDuhamel_penultimate)
InterchangeThreading.lean [AF std-3, raw 0 @ 9425]: hDa/hLap threaded (Δ↔pd∘pd adapter
PROVEN) + hLapFull reduced (hLHSlim carry + sliver squeeze) + hDuhamel_penultimate.
NEXT: J4-143 = GeometricModuliThreading.lean (G1 hco/hYdisp discharge for the concrete chart
from J4-129 lemmas — domain reconciliation ball-vs-global; G2 hbnd ε-uniformization —
the constants ARE ε-free, extract; G3 thread ⟹ hDuhamel_next). Then deep residue
(hFLocLip/hqLip resolvent; hJ3/J1b base-point bootstrap; hWmeas₀; gate-ball; hLHSlim) +
capstone side (hCH/hCConv-C², F2 family, hFII, gauge) + FINAL ASSEMBLY.

## J4-143 BANKED — 2026-08-03: GEOMETRIC MODULI DISCHARGED (Yext + ε-uniform constant)
GeometricModuliThreading.lean [AF std-3, raw 0 @ 9426]: G1 global hco/hYdisp exact via the
extension trick; G2 hbnd finite-max uniformization. Carried: G3 threading (Pext=eᵢ/Qext=0
design), hGateSub, upstream pinning.
NEXT: J4-144 = LeviLipschitz.lean (F1 E-spatial-difference from gradient carry; F2 the
resolvent Lipschitz F=−E−E*F with (s−r)^{−1/2} integrating to 2√s ⟹ hFLocLip/hqLip in the
sliver-stack shape). Then G3 + hLHSlim + hWmeas₀/gate-ball/J1b + capstone side + FINAL
ASSEMBLY.

## J4-144 BANKED — 2026-08-03: hFLocLip/hqLip DISCHARGED (the resolvent route)
LeviLipschitz.lean [AF std-3, raw 0 @ 9427]: the last genuinely-new analytic input of the
Duhamel residue is closed (segment MVT + 2√s integration + Volterra assembly + the exact
consumer hqLip triple). Carried: hVol/hE1/hSlice + integrabilities + amplitude family.
NEXT: J4-145 = F2FamilyDischarge.lean (R1 htime via the upper-FTC engine; R2 hpar via
hDa_trunc; R3 hR via the mixed-increment route; R4 hFII H*F-pairing mirror; R5 thread).
Then G3 + hLHSlim + hWmeas₀/gate-ball/J1b + hCH/hCConv-C² + gauge + FINAL ASSEMBLY.

## J4-145 BANKED — 2026-08-03: THE F2-REGULARITY GROUP CLOSED
F2FamilyDischarge.lean [AF std-3, raw 0 @ 9428]: hFII + htime + hpar + hR discharged
(the little-o proven; local-continuity FTC route) + hDuhamel_final_of_f2carries.
NEXT: J4-146 = CapstoneStatus.lean (S1 machine-checked supply chain per capstone input;
S2 a1_R6_of_residue — THE ONE THEOREM with exactly the remaining residue as hypotheses;
S3 honest gap doc). Then grind the S2 list.

## J4-146 BANKED — 2026-08-03: ★★ a1_R6_of_residue — THE MACHINE-CHECKED REDUCTION ★★
CapstoneStatus.lean [AF std-3, raw 0 @ 9429]: three capstone slots discharged at the witness
+ a1_R6_of_residue (the a₁=R/6 conclusion conditional on the explicit residue: GATE + GAUGE
+ 7 ANALYTIC slots, each with a landed reduction supplier). Irreducible frontier: joint-q
ODE regularity + loc-unif hDaLimLU. 30 bricks 2026-08-03.
NEXT: J4-147 = SpatialC2.lean (hCH via the C² chart composition; hCConv via the Q1/Q2
engine derivative-continuity). Then hDaLimLU loc-unif upgrade + engine instantiations +
ε-pinning + the joint-q wall assessment.

## J4-147 BANKED — 2026-08-03: hCH DISCHARGED + hCConv REDUCED
SpatialC2.lean [AF std-3, raw 0 @ 9430]: hCH genuinely proven; hCConv 2-layer reduction;
a1_R6_of_residue_hCH_discharged. NEXT: J4-148 = DaLimLocUnif.lean (the hDaLimLU loc-unif
upgrade — K-uniform sliver/Etrunc/LapTrunc constants). Then engine instantiations,
ε-pinning, joint-q assessment, base-point family.

## J4-148 BANKED — 2026-08-03: THE LOC-UNIF UPGRADE (hDaLimLU + hDerivLU discharged)
DaLimLocUnif.lean [AF std-3, raw 0 @ 9431]: U1-U4 all landed; both consumer shapes verbatim.
NOTE: hLHSlim (the Δ_g(frozen)→Δ_g(full) limit) = U2's lapTrunc_tendstoUniformlyOn content
— threadable. NEXT: Sol consult on the JOINT-Q WALL (measurable-selection vs re-construction
routes), then J4-149 per verdict.

## SOL JOINT-Q VERDICT (consult 2026-08-03 #4): ATTACK THE FORWARD FLOW
Routes rated: measurable-selection REJECTED (no jets); outer-envelopes REJECTED; the plan:
Step 0 AUDIT (#print BasepointJetModulus/uniformFlowExp — is the modulus (q,v)-joint or
per-q? what is the flow's construction: ODE/Picard/series/choose?; classify P/Q consumers:
W z 0 only vs moving-base jets); Step 1 the quantitative joint Lipschitz
uniformFlowExp_lipschitzOn_base_field (Grönwall on the phase-space ODE with frozen-q
augmentation, or iterate-limit continuity for Picard/series constructions); Step 2 the
chart transfer ‖W q p − W q' p'‖ ≤ C(‖p−p'‖ + flow-modulus) via the ApproximatesLinearOn
lower-Lipschitz — closes hWmeas₀ + amplitude measurability WITHOUT chart refactor (the
closed-graph route also valid but the quantitative estimate is shorter); Step 3 vertical
jets if the modulus is joint; Step 4 the sliver jets: CHECK the geodesic-reversal bypass
W z 0 = −D_v exp₀(W 0 z)[W 0 z] (fixed-base only — could bypass base-point C² entirely for
the diagonal map!) before the variational-equation C² campaign (HIGH difficulty, limited
Mathlib turnkey support). Restricted-measure note: measurability may need volume.restrict K
or a canonical extension.

## J4-149 BANKED — 2026-08-03: THE JOINT-Q AUDIT + TRANSFER (residue isolated)
FlowJointRegularity.lean [AF std-3, raw 0 @ 9432]: AUDIT: flow = .choose over EXPOSED
geodesic ODE (Grönwall viable); modulus per-v only; reversal infeasible; consumer =
diagonal only. LANDED: antilipschitz + chart_joint_velocity_modulus (residue = base-flow
difference) + hWmeas₀_of_continuousOn. NEXT: J4-150 = GeodesicGronwall.lean (W1 geodesicField
Lipschitz on the confinement compact; W2 two-tube Grönwall comparison; W3 flow difference
≤ e^L‖q−q'‖; W4 hW0 ⟹ hWmeas₀ UNCONDITIONAL).

## J4-150 BANKED — 2026-08-03: ★★ THE C⁰ JOINT-Q WALL CLOSED (geodesic Grönwall) ★★
GeodesicGronwall.lean [AF std-3, raw 0 @ 9433; ns QIQTH.GeodesicGronwall]: the nonlinear
two-solution Grönwall on the exposed geodesic ODE ⟹ base-flow diff ≤ e^L‖q−q'‖ ⟹
z ↦ W z 0 LIPSCHITZ ⟹ hWmeas₀ unconditional (carried: hRI + on-domain). The
4×-surfaced base-point-regularity wall's C⁰/measurability layer is DOWN.
NEXT: J4-151 = ResidueThreading.lean (T1 hRI re-export; T2 hLHSlim ⟸ U2; T3 hVol/hE1/hSlice;
T4 gate-ball; T5 a1_R6_of_residue_v3 refresh).

## J4-151 BANKED — 2026-08-03: THE THREADING SWEEP (hRI/hLHSlim/hVol/hInter GONE)
ResidueThreading.lean [AF std-3, raw 0 @ 9434]: four residue items discharged; gate-ball
derived modulo the cf floor; hWmeas₀'s hRI slot supplied; hInter removed from the capstone
residue. NEXT: J4-152 = EngineInstantiation.lean (the dominated-engine dH/dHH concrete
instantiation + the ε-pinning thread).

## J4-152 BANKED — 2026-08-03: THE ENGINE INSTANTIATION
EngineInstantiation.lean [AF std-3, raw 0 @ 9435]: the concrete dH/dHH kernels + on-gate
formulas + domination + the concrete second-order interchange + the ε-pinning.
NEXT: J4-153 = the final-state documentation census (docs only), then the next residue brick.

## J4-154 BANKED — 2026-08-03: THE AMPLITUDE FAMILY SUPPLIED (F3 top item)
AmplitudeFamilyDischarge.lean [AF std-3, raw 0 @ 9436]: hAmp2 both bases + bounds + the
general-base hWz provider (germ at the image point + right-inverse). NEXT: J4-155 =
CConvLayerDischarge.lean (the hCConv L1 layer + the hdetz-general small lemma).

## J4-155 BANKED — 2026-08-04: hdetz PROVEN + THE hCConv L1 LAYER
CConvLayerDischarge.lean [AF std-3, raw 0 @ 9437]: hdetz (displacement route) +
hConvDeriv_linewise (singular-limit dominated) + the exact L1 shape (assembly carry).
NEXT: J4-156 = EGradDischarge.lean (ASSESS hEgrad third-jet wall first; pivot to the
m-uniform C_R / uniform-in-z / general-base J1b if walled).

## J4-156 BANKED — 2026-08-04: GENERAL-BASE J1b JETS + THE F3 ASSESSMENT
GeneralBaseJets.lean [AF std-3, raw 0 @ 9438]: the second-jet existence at general base
(exact consumed shapes). VERDICTS: hEgrad = 3-5-brick third-jet layer (DEFERRED, honest);
m-uniform C_R = tractable plumbing (J4-157); J1b = done.

## J4-157 BANKED — 2026-08-04: THE m-UNIFORM C_R (the witness→hbnd chain closed)
UniformCRDischarge.lean [AF std-3, raw 0 @ 9439]: the master-gap ∃-hoisting; nothing new
carried. NEXT: J4-158 = PartialsToFDeriv.lean (the classical continuous-partials⟹FDeriv
theorem on Fin n — the identified reusable Mathlib gap; then hAssembly reduced to the
partials' continuity).

## J4-158 BANKED — 2026-08-04: THE CLASSICAL PARTIALS→FDERIV THEOREM
PartialsToFDeriv.lean [AF std-3, raw 0 @ 9440; ns QIQTH.PartialsToFDeriv]: the reusable
Mathlib-gap theorem proven in full + hAssembly closed-to-continuity.
NEXT: J4-159 = the census refresh (J4-154..158 layer into A1_R6_RESIDUE_STATUS.md).

### J4-160 — GcoefContinuity (LANDED 0ac1936d)
The gcoef-continuity carry closed at the abstract + exact-shape level:
`continuousAt_doubleIntegral_of_dominated` (reusable nested dominated engine),
`gcoef_continuity_discharge` (verbatim hcont of hAssembly_reduced), and
`hCConv_L1_final` (linewise + assembly + continuity ⟹ the full L1 ∃-HasFDerivAt
shape). Remaining in this layer: the G2 per-(i,x₀) domination/continuity bundle
for dH := witnessFieldDeriv (labelled; satisfiable from
witnessFieldDeriv_gate_eq/_gate_abs_le) → J4-161. std-3 raw 0. NOT a1=R/6.

### J4-161 — WitnessDerivDomination (LANDED d7e265af)
The G2 concrete bundle for dH := witnessFieldDeriv: hzcont DISCHARGED
(pd-of-C² continuity, exact G3 shape), hzint DISCHARGED (Gaussian envelope
integrable, endpoint null), hzbound DISCHARGED IN SHAPE (x-free dominator
(C₀·Cf)·G_{κ(t−s)}(z); near-regime envelope PROVEN from E2 + the
chart-Gaussian carry). Open in G2: hzmeas/hsmeas/hsbound/hBint → J4-162.
std-3 raw 0. NOT a1=R/6.

### J4-162 — WitnessDerivMeasurability (LANDED b2e9bc63) — L1 LAYER COMPLETE
hsbound + hBint DISCHARGED (constant B = C0·Cf via mass-one Gaussian);
hzmeas/hsmeas in-shape reductions; CAPSTONE g2_bundle_assembled feeds ALL
SEVEN gcoef_continuity_discharge hypotheses at witnessFieldDeriv. The hCConv
L1 continuity chain is now structurally complete, resting on the six-carry
labelled residue {hC2fam, henv, hKmeas, hFmeas, hjoint, hdomS} (each
satisfiable). Next: discharge the carries concretely (J4-163) or the census
tractables. std-3 raw 0. NOT a1=R/6.

### J4-163 — G2CarryDischarge (LANDED 885c88f0)
The six-carry round: gaussDdim_coercivity_envelope (the geometric core —
coercivity ⟹ G_τ(w) ≤ (√2)ⁿ·G_{2τ}(base), τ-free constant) +
witnessFieldDeriv_gate_envelope_coercive (hgauss_env carry gone) +
hdomS_from_uniform + pd_aestronglyMeasurable_of_slice (reusable lever) +
hKmeas_from_witness. L1 residue now {hC2fam (genuine general-centre C²),
henvU instantiation, hWmeas+hWdiff, hjoint, hFmeas}. std-3 raw 0.
NOT a1=R/6.

### J4-164 — HenvUInstantiation (LANDED 32cf3344)
henvU/henv ASSEMBLED (C₀=(Bs·Ba+Bd)·(√2)ⁿ, κ=2; off-gate z∉K kills the
witness ∀x, on-gate = coercive-envelope data via the hGateData dichotomy)
+ concrete capstones hdomS_assembled/hzbound_assembled + the reusable
pd-vanishing levers. Envelope-branch residue = {hGateData('), hFbd}.
L1 residue overall: {hC2fam, hGateData('), hWmeas+hWdiff, hjoint, hFmeas}.
std-3 raw 0. NOT a1=R/6.

### J4-165 — WitnessMeasDeriv (LANDED 95a718e3)
hWmeas/hWdiff round: gated-indicator measurability lever (reusable),
hWmeas exact slot ← {hKm, hSm, hIn}; hWdiff off-gate leg DISCHARGED
unconditionally, on-gate PdiffAt⟹HasDerivAt, exact slot via a.e.-z
dichotomy; CAPSTONE hKmeas_concrete ← {hKm, hSm, hIn, hGateDiff}.
Key structural finding: inner kernel z-enters only through
uniformInverseChart z p (radialCutoff·heatParametrix of the chart), so
hIn = chart z-continuity. L1 residue: {hC2fam, hGateData('),
hKm+hSm+hIn+hGateDiff, hjoint, hFmeas}. std-3 raw 0. NOT a1=R/6.

### J4-166 — GateChartMeasurability (LANDED 1b92d7de)
hKm DISCHARGED (IsCompact.measurableSet); hIn reduced to {hw, hVmapMeas}
via the composition lever (inner slice = (cutoff·parametrix)∘chart;
spatial continuity unconditional in τ); hKmeas_concrete_v2 capstone.
Findings: S free at the capstone (hSm genuine); chart z-continuity
banked only p=0-on-subsets (hVmapMeas honest carry). L1 residue:
{hC2fam, hGateData('), hSm, hw, hVmapMeas, hGateDiff, hjoint, hFmeas}.
std-3 raw 0. NOT a1=R/6.

### J4-167 — FoldedCoeffChartMeas (LANDED fdf89a67)
hw DISCHARGED (Θ^{-1/2} prefactor proven from vanVleck_contDiffAt +
vanVleck_pos; residue {hg, hgpos, hu} — radialTransportSolve smoothness
genuinely unbanked). The restricted-K measurability route (indicator-iff
lever: inner meas on volume.restrict K suffices) + p=0 chart slice
DISCHARGED (chartOrigin_continuousOn at S=K). CAPSTONE hKmeas_concrete_v3
← {hSm, hg, hgpos, hu, hVmapMeasK restricted-K, hGateDiff}. std-3 raw 0.
NOT a1=R/6.

### J4-168 — ChartGeneralPContinuity (LANDED b75dceed)
The p=0 Groenwall GENERALIZES to all reachable p (p = flow endpoint only,
never ODE data): chartP_lipschitz_modulus + chartP_continuousOn +
hVmapMeasK_at_p_of_geom + the honest per-p disjunction
hVmapMeasK_of_geomOrMeas (far p not overclaimed). CAPSTONE
hKmeas_concrete_v4 ← {hSm, hg, hgpos, hu, hChartP, hGateDiff}.
std-3 raw 0. NOT a1=R/6.

### J4-169 — GateSetMeasurability (LANDED 23774e15)
Flow-ball hSm: mem_flowBall_iff_chart (both directions, from the banked
left-/right-inverse identities); K-relative weakening confirmed
architecturally (consumers use only hKm.inter hSm) + 3 re-threaded
levers; flow-ball discharge lemmas; CAPSTONE hKmeas_concrete_v5 ←
{hSmK, hg, hgpos, hu, hChartP, hGateDiff}. std-3 raw 0. NOT a1=R/6.

### J4-170 — OnGateFieldRegularity (LANDED 700d6c39)
The SHARED field-slot regularity core: local-coincidence lever + the
hCH comp tower lifted to general x₀ + on/off-gate C² + PdiffAt levers;
hC2fam_from_chart + hGateDiff_from_chart (the exact consumer slots) +
hGateDiff_hC2fam_shared_core (BOTH from one root). The one remaining
regularity core = chart field-slot C² at general points (banked only at
centre; IFT satisfiability). std-3 raw 0. NOT a1=R/6.

### J4-171 — ChartFieldC2General (LANDED f695250e) — REGULARITY CORE CLOSED
KEY DISCOVERY: the chart is C² at EVERY reachable point already (the
quantitative IFT ran inside the chart construction —
uniformInverseChart_huniformChart). Abstract IFT identification core
(reusable, generic Banach) + concrete no-hypothesis discharge + base-point
non-vacuity witness + hFieldReg/hFieldReg2 families + the FULL
hGateDiff∧hC2fam pipeline from reachable-gate geometry at one δ₀.
std-3 raw 0. NOT a1=R/6.

### J4-172 — ConcreteGateAssembly (LANDED a99862fa)
The concrete flow-ball gate wired end-to-end: openness + left-inverse +
reachability + C² all from the one banked chart spec; the right-inverse
DERIVED on-gate; hKmeas_concrete_v6 ← {hGeomP, hMemNear, hg, hgpos, hu};
hC2fam_concrete_final ← {hMemPt, hg, hgpos, hu}; l1_residue_status =
the machine-checked census reduction. std-3 raw 0. NOT a1=R/6.

### J4-173 — GeomPTransportAssess (LANDED b68e7409) — v6 SUPERSEDED
⚠ HONEST CORRECTION: hKmeas_concrete_v6's hGeomP is unsatisfiable in
general (∀p right-inverse fails beyond the injectivity reach) — v6 is
VACUOUS for general metrics; superseded by hKmeas_concrete_v7 (per-p
geometry-OR-{measurable set + slice measurability} disjunction, the
paired right branch required). hu: radialTransportSolve = explicit
parametric integral; continuity rung PROVEN (radialTransportSolve_-
continuous + transportCoeff_continuous_of_preserve); hu reduced to
{hSolve, hT} operator premises (C^∞-under-integral absent in Mathlib).
std-3 raw 0. NOT a1=R/6.

### J4-174 — TransportOpSmoothness (LANDED 82cf2f3c)
hT FULLY DISCHARGED (laplaceBeltrami + transportOp preserve C^inf from
{hg, hgi, hgpos}); the solve C1 rung + the induction-step identity
d(I_m f) = I_{m+1}(df). STRUCTURAL: top = omega = analytic here — the
ray integral reaches all finite orders + infinity but not omega; hSolve
sharpened to ray-integral analyticity; candidate = infinity-rebase of
the hu chain (J4-175). std-3 raw 0. NOT a1=R/6.

### J4-175 — HuInftyRebase (LANDED 43fba045) — HU CLOSED AT INFINITY
The generic Banach rayIntegral C^inf tower (m->m+1 fderiv bumping,
F-generalized induction) + radialTransportSolve_contDiff_infty (hSolve
at infinity PROVEN) + transportOp infinity mirror + hu_infty_closed
from {hg, hgi, hgpos} ONLY. Audit: no consumer genuinely needs omega;
top->infinity rebases are one-token interface edits. std-3 raw 0.
NOT a1=R/6.

### J4-176 — census refresh (LANDED 6e5c09cd)
Verified addendum in A1_R6_RESIDUE_STATUS.md: J4-160..175 brick table
(every theorem re-read), the honest L1 residue, the v6 correction, the
tractability verdict. hjoint confirmed the last open G2 slot; hu now
DERIVED (not parallel-carried); walls unchanged. NOT a1=R/6.

### J4-177 — JointMeasurability (LANDED 96e938bf)
hjoint (the last open G2 slot) REDUCED: abstract-measure difference-
quotient lever + ae_prod_of_ae_ae (honest MeasurableSet side-condition)
+ gated indicator glue + hjoint_concrete (exact slot). New residue =
hinnerJ ONLY (inner parametrix joint measurability; gaussDdim vanishes
at tau<=0); other carries unify with the census. std-3 raw 0.
NOT a1=R/6.

### J4-178 — InnerKernelJointMeas (LANDED e5117ac0) — HJOINT CLOSES
hinnerJ DISCHARGED (tau<=0 vanishing ladder + direct-Borel global
measurability across tau=0 + the nu-slice product lift) + hjoint_final:
the last G2 slot closes from {hKmeasSet, hSmeasSet, hFjoint, hThetac,
hThetane, huc, hVmapMeas, hWdiffJ} — all unified-or-reducible carries.
std-3 raw 0. NOT a1=R/6.

### J4-179 — CoeffContWdiffLift (LANDED bfd87522)
hThetac/hThetane/huc DISCHARGED from geometry (huc via the infinity
chain — transportOp does not preserve C0, trap confirmed); the
forall-x-first hWdiff reorder variant + the ae_prod hWdiffJ lift
(hMeasSet carried honestly); hjoint_from_geometry_final <-
{hKmeasSet, hSmeasSet, hFjoint, hVmapMeas, hg, hgi, hgpos, hGateDiff',
hMeasSet}. std-3 raw 0. NOT a1=R/6.

### J4-180 — GateDiffWiringMeasSet (LANDED 9119dbd4)
hGateDiff' wired geometry-only (tau-uniformity confirmed; infinity
mirrors — omega never touched) + the rational eps-delta HasDerivAt
characterization + the general measurable-set lever + hMeasSet reduced
to {hSliceCont, hWq, hWa, hDmeas}. CAPSTONE hjoint_fully_geometric <-
{hg, hgi, hgpos, hKmeasSet, hSmeasSet, hFjoint, hVmapMeas, hCover,
hSliceCont, hWq, hWa, hDmeas}. std-3 raw 0. NOT a1=R/6.

### J4-181 — SliceInterfaceInstantiation (LANDED b3d6f181) — L1 PLUMBING EXHAUSTED
The support-condition identity (gated = inner everywhere; jump lands
where the kernel is 0; design b < c) + slice continuity + hSliceCont +
Borel hWq/hWa mirrors + hjoint_instantiated. hDmeas stays the honest
carry (both routes examined and rejected). The L1 plumbing is now
effectively exhausted: residue = satisfiable-by-design geometric/
measurability data + hDmeas + the v7 disjunction + the top->infinity
interface rebases + hGateData envelope. Next: Sol consult on walls +
final assembly. std-3 raw 0. NOT a1=R/6.

### SOL CONSULT (2026-08-04, post-J4-181) — THE ENDGAME PLAN
Verdict: layered assembly with ONE bundled facade (4-5 Prop bundles:
Metric/ChartGate/Source/Derivative/Envelope data; envelope parallel to
L1, rejoining only at the final hCConv constructor). hDmeas: replace
exact deriv-measurability by the MEASURABLE EXPLICIT REPRESENTATIVE D
(the gated E1 formula) + measurable Good = {HasDerivAt slice (D x)}
(the banked rational lever) + ae_prod on Good + uniqueness => deriv
=ae D — no exact-Borel-deriv theorem needed. F2: compact open-tube
lemma (finite subcover min), NOT continuity of the .choose radius —
1-2 bricks IF the chart spec gives joint openness (audit first). F1:
materially easier now — factorize E first, reuse the support-
globalization; 2-3 bricks if chart spec is jointly regular, 4-7 if the
parameter-ODE measurability must be built. hEgrad: 5-7 bricks (jet
pack -> factorization -> differentiate -> r/t G <= C t^{-1/2} G' 
absorption -> cutoff annulus -> assembly). PLAN: J4-182 top->infinity
rebase sweep NOW; 183 facade; 184 measurable-derivative-representative
interface; 185 gated-D instantiation; 186 close hDmeas + full hCConv;
187 generic tube lemma; 188 F2 close; 189 factorized E normal form;
190 inner joint meas of E; 191 F1 close; then the 5-brick hEgrad tail.

### J4-182 — the top->infinity sweep + InftyRebaseCapstone (LANDED a42ab9ad)
6/7 consumer groups already mirror-covered (no churn); hCH_discharge
rebased in place; hCH_discharge_from_geometry + hsrc_from_geometry
(geometry-only). FINDING: the deep a1_R6_of_residue hsrc slot demands
omega — future audit whether that slot's use is omega-genuine.
Sol plan step 1 done. std-3 raw 0. NOT a1=R/6.

### J4-183 — CConvFacade (LANDED 311429cd) — Sol plan step 2
Five verbatim-shaped Prop bundles + shared_chart_consequences +
hCConv_discharged_from_data (the full L1 thread, first-build-green).
HONEST GAP: facade = hCConv_reduction's hfam (L1) verbatim; the C2
residue slot needs L2 hD1 (hEgrad tail) + leviSeries specialization.
J4-184 = flow-ball S-instantiation + measurable-D adapter.
std-3 raw 0. NOT a1=R/6.

### J4-184 — FlowBallInstantiation (LANDED 66da4a2d) — Sol steps 3-4
chartGateData_flowBall (3/7 fields from geometry; carries minimized to
{hSmeasSet-full, hVmapMeas, hChartB, hSliceData}) +
goodProd_hasDerivAt_of_carries + derivativeData_of_rep +
facade_flowBall (the L1 hfam at the concrete gate, c-indexed).
Honest hlin-pointwise vs hDmeas-ae split recorded. std-3 raw 0.
NOT a1=R/6.

### J4-185 — GatedDInstantiation (LANDED a27aa270) — Sol step 5
The gated-D measurable representative: gatedDerivRep (K-indicator of
the E1 form) + the EVERYWHERE identification (three-way dichotomy) +
witnessFieldDeriv joint measurability <- lower-order factor carries +
hDmeas_discharged (the exact bundle field) + the geometry builders.
All six Sol sub-steps landed. std-3 raw 0. NOT a1=R/6.

### J4-186 — CompactTubeLemma (LANDED 80c29340) — F2 OFF THE WALLS LIST
Generic tube lemma banked (via generalized_tube_lemma) + the F2 AUDIT:
F2 was ALREADY DISCHARGED — the chart spec is K-uniform (single delta_0
from the quantitative IFT), and the E-bound gate radius is the uniform
constant c = (b+rho_c)/2 > b > 0. Remaining walls: F1, hEgrad/L2 only.
std-3 raw 0. NOT a1=R/6.

### J4-187 — ErrorKernelFactorization (LANDED e84467c4) — Sol step 9
The E normal form: heatOp_gated_split + residual_eq_gauss_mul_A (the
Gaussian factorization repackaged from banked algebra) +
cutoffError_eq_cutoff_gauss_A_sub_annulus + annulus supports + the F1
measurability feeds (unified factor carries). Serves both F1 and
hEgrad. std-3 raw 0. NOT a1=R/6.

### J4-188 — ErrorKernelJointMeas (LANDED c8ccff2e) — Sol step 10
All six factor carries DISCHARGED from geometry; the full normal form
chi*(G*A) - annulus measurable from geometry + the ONE carry hDH (the
parametrix spatial gradient). F1 slot identified (the triple
StronglyMeasurable, ResidueThreading:316); remaining F1 = hDH + the
W1/W2 q-regularity flow wall. 1/tau^2 blowup honestly documented.
std-3 raw 0. NOT a1=R/6.

### J4-189 — ParametrixGradientMeas (LANDED 62fd1c86)
The gradient identity + hDH DISCHARGED + the E diagonal normal form
measurable from GEOMETRY ALONE. F1 VERDICT: factor axis DONE; the
remaining F1 = the W1/W2 flow q-regularity wall (joint continuity/C1
of H_G across the .choose base-point flow — the honest Sol route-(b)
parameter-ODE wall, recorded not attempted). std-3 raw 0. NOT a1=R/6.

### J4-190 — CompactJetBounds (LANDED 64a3232e) — hEgrad step (i)
The compact-bound levers + JetBoundPack + geometry builder +
pd_poly_eq_sum + the tau^2-cleared amplitude (pole-clearing identity;
the cleared form is a genuine polynomial) + tau^2*|A| <= C on the
compact box. hEgrad slot confirmed = the mixed-third-jet LeviLipschitz
layer (3-5 bricks). std-3 raw 0. NOT a1=R/6.

### J4-191 — GaussianGradAbsorption (LANDED a3b7e0e8) — hEgrad step (iii)
The absorption lever family with explicit factorial constants: 1D core,
general doubling-width, linear/quadratic campaign forms, annulus
sqrt-tau-gain family. Covers exactly the gradient-formula powers.
std-3 raw 0. NOT a1=R/6.

### J4-192 — ChartThirdJet (LANDED 6b7d2894) — the third-jet layer opens
uniformFlowExp C4 DERIVED (the overlap bridge to the exp tower); the
no-conjugate-points invertibility DISSOLVED (Neumann on the uniform
ball); the C4 chart at reachable points; third-jet existence. ZERO new
carries. Next: third-jet compact bounds + parametrix corollary + the
grad-E expansion. std-3 raw 0. NOT a1=R/6.

### J4-193 — ThirdJetBounds (LANDED 839d9385) — all four goals
tau^2*|pd A| <= C (the fderiv-slice route, no symbolic gradient) +
the grad(G*A) skeleton + the field-C3 parametrix + third-derivative
continuity/compact lever + the pd_slice_eq_fderiv bridge. Honest
residue: the gate-uniform third-jet constant (per-base expRho
non-uniformity). std-3 raw 0. NOT a1=R/6.

### J4-194 — GradEAssembly (LANDED dda1e7ca) — the hEgrad machinery COMPLETE
gradGA_bound (|pd(G*A)| <= C*tau^{-5/2}*G_{2tau} from geometry) + the
E-gradient triangle (annulus term exposed). THE ALIGNMENT VERDICT: the
tau-power gap to the tau^{-1/2} slot = the GRADIENT of the already-
carried C4c DeWitt-cancellation wall — NOT a new gap; discharging C4c
makes this composition yield the target verbatim. Remaining honest
frontier: C4c (the genuine Seeley-DeWitt content), W1/W2 flow wall,
annulus-gradient composition, gate-uniform third-jet constant, L2 hD1
threading, the omega-hsrc audit. std-3 raw 0. NOT a1=R/6.

### J4-195 — OmegaHsrcC4cAudit (LANDED 9b4d0d2e) — omega-hsrc REMOVED
Part A: hsrc traced (C1/C0 downcasts only, no analyticity) => the C1
keystone + full infinity re-thread => a1_R6_of_residue_inf (the
top-hsrc carry REMOVED; composes with hsrc_from_geometry). Part B:
the honest C4c correction — the off-diagonal singular heads are
GENUINE curvature (domination not cancellation is the repo route; the
true cancellation = the Jacobi/exp radial ODE Mathlib gap) + the
diagonal singular-free identity. std-3 raw 0. NOT a1=R/6.

### J4-196 — census #3 (LANDED e6844f94)
The definitive residue: hsrc/hCH DISCHARGED from geometry; hEboundW
dischargeable (width-2 domination, GateSqControl from flowBall); the
Levi carries = satisfiable interface assembly; L2 hD1 = the remaining
hCConv gap. Walls re-tiered: Jacobi/exp ODE needed ONLY for the true
off-diagonal value (NOT for hEboundW); W1/W2 flow; L2 hD1; K-uniform
expRho; annulus-grad. Verdict: grind (c)(d)(e)+Levi; Sol-consult
(a)(b). NOT a1=R/6.

### J4-197 — EboundWiringHD1 (LANDED fe70ecb6)
hEboundW discharged into a1_R6_of_residue_inf_v2 (the carry GONE from
the capstone surface; provider defeq + the C*(1+t) reshape) + the
abstract dominated-differentiation lever (the derivative analogue of
the J4-160 engine) + the hD1 assessment (missing = the order-2 gate
envelope + order-2 measurability). std-3 raw 0. NOT a1=R/6.

### J4-198 — SecondDerivEnvelope (LANDED f5b3fe43)
The order-2 gate formula/envelope/coercive + the measurability mirror
+ THE PROVEN VERDICT: the naive hD1 dominator rate (t-s)^{-1} is NOT
interval-integrable (theorem!) while the (t-s)^{-1/2} sliver rate IS
=> hD1 = the sliver-truncation mirror one order up. std-3 raw 0.
NOT a1=R/6.

### J4-199 — HD1SliverRoute (LANDED 3326bc68)
THE MAP IS DIRECT (the banked witness_sliver2 bounds cover the hD1
sliver piece verbatim); the bulk lemma (truncation defeats the wall) +
the uniform-limit-of-derivatives skeleton (the analytic heart of hD1).
Remaining: the concrete wiring + gderiv continuity. std-3 raw 0.
NOT a1=R/6.

### J4-200 — HD1ConcreteWiring (LANDED 79a7abfe)
The hD1-slot verdict (= HasFDerivAt family + D' continuity) + all four
feeds (sliver-rate hBint, gderiv_continuousAt, endpoint convergence,
sqrt-eps vanishing, hD1_reduction). Honest finding: witness_sliver2 is
centre-only — the x-uniform upgrade is the remaining carry. std-3
raw 0. NOT a1=R/6.

### J4-201 — XUniformSliver (LANDED ac30a37a)
ROUTE A: the sliver pinning is interface-only (the F-cap x-uniform,
same constant); the E1 per-slice x-uniform + sliver_rate_hsbound in
the exact consumer shape; NO new carries. Scope: E2/T1-T3 halves next.
std-3 raw 0. NOT a1=R/6.

### J4-202 — XUniformSliverFull (LANDED e6b54406) — HD1 INTERFACE-CLOSED
All halves x-uniform (route A, none resisted); witness_sliver2_xuniform
(the sqrt-eps composite at every x); hD1_from_data — the interface-level
hD1 closure from the unified carries. Remaining: the componentwise CLM
lift + the concrete data threading + the Levi-carries assembly.
std-3 raw 0. NOT a1=R/6.

### J4-203 — LeviCarriesAssembly (LANDED 8a4a793b)
hS0 DISCHARGED (v3 via the strengthened gatedWitnessN1_package);
the honest provider map: the four remaining Levi slots stay carried
(wall-cored bundles: hEmeas=W1/W2, hDelta; hDuhamel = net expansion).
hCH needs hSopen (small extension next). std-3 raw 0. NOT a1=R/6.

### J4-204 — GateOpennessExport (LANDED 4a5bc111)
The openness was hgood's bundled 5th conjunct; the package re-merge
exports it; a1_R6_of_residue_inf_v4 (hCH DISCHARGED; +hgiC/hgpos).
Inner residue: {hInt, hDuhamel, hInter, hDConv, hCConv}. Next: the
Sol walls-consult. std-3 raw 0. NOT a1=R/6.

### SOL CONSULT #3 (2026-08-05, post-J4-204) — THE FINAL PLAN
Phases: (1) LeviSeriesLocalData package [3-5 bricks] -> (2) hInt from
hEmeas+series [1-3] -> (3) the hInter LOCAL rebase [4-7; the global
bound is an API artifact, not load-bearing] -> (4) the hCConv concrete
threading [5-8; pin D/F explicitly, never replace F by an ae-rep in
ContDiffAt goals] -> (5) plain Gaussian approximate identity [3-5] ->
(6) the witness hDelta specialization [4-8] -> (7) hDConv threading
[2-4] -> (8) the TruncatedDuhamelData facade [7-12; package not
reprove] -> (9) final assembly [2-3] -> (10) the BOUNDED hEmeas
attempt [16-26 if the variational jets are accessible: full-initial-
state Groenwall + the product endpoint map Theta(q,v)=(q,Exp_q v) +
the inverse-jet formulas + the Neumann region; 6-8 recon bricks first,
stop if the jets are behind new choices]. FINAL SHAPE:
a1_R6_of_geometry_and_heatOp_qregularity (P : GeometryPackage)
(hQ : HeatOpTripleMeasurableWall P) : a1 = R/6 — pure geometry + ONE
named wall. Honest frontier if hEmeas fails: the q-continuity of the
endpoint-flow velocity jets on the compact good tube. DON'T cite as
frontier: hInter/hCConv/hDelta/the raw Duhamel bundle (engineering).
Total ordinary work ~31-55 bricks.

### J4-205 — LeviSeriesLocalData (LANDED 4eced3e3) — Sol Ph1+Ph2
The shared series package (structure + tsum-measurability + envelope
lemmas + builder + hInt accessor); banked domination reused; the
joint-(s,z) bonus honestly removed (whnf loop, follow-on).
std-3 raw 0. NOT a1=R/6.

### J4-206 — InterchangeLocalRebase (LANDED 6516852b) — Sol Ph3
The Sol verdict confirmed (no load-bearing global use); the local
interchange + global corollary + hInter_from_local_data (the exact v4
slot mod {local bound, hEzero, hEmeas, hglobal}). std-3 raw 0.
NOT a1=R/6.

### J4-207 — CConvConcreteThreading (LANDED 664e46e5) — Sol Ph4
The hCConv threading at the concrete witness + a1_R6_of_residue_inf_v5
(inner carries {hInt, hDuhamel, hInter, hDConv, hCH} + bundles + hD1);
the forall-S provider vacuity-hole soundly rejected. std-3 raw 0.
NOT a1=R/6.

### J4-208 — GaussianApproxIdentity (LANDED 943fd1f3) — Sol Ph5 collapsed
The identity was FULLY BANKED (J4-118/119); the gap was only the
nhdsWithin-0+ filter form (upgraded, no new analysis). The hDelta slot
remains assembled to hBoundary (Brick 2) — audit next. std-3 raw 0.
NOT a1=R/6.

## J4-209 (2026-08-05, 0b179174) — HDConvThreading: the hDConv chain audit + threading + v6 [AF]
Sol final plan Ph7. THE AUDIT: every slot of hDConv_gatedWitnessN1_of_delta_final has a
banked provider — hpar/htime/hR (F2FamilyDischarge J4-145 R1-R3), hDelta
(hDelta_gatedWitnessN1_final J4-120; **hBoundary/Brick-2 moving-peak DISCHARGED inside**
via boundary_tendstoLocallyUniformlyOn), hDaLim→hDaLimLU (hDaLimLU_discharge, DaLimLocUnif
U3). SOLE hard chain residue = **hDaLimLU** (L3/L4 sliver/tail/interchange family:
pdpdH/hInterchange/hLapFull/hII_lo/hII_hi/hSliver/hEbnd/hEcomb + RNC hgi,hΓ). Rest =
satisfiable analytic data (dominations/measurabilities/parametrix family/C3ε engine/
cross-Lipschitz/floor/inner-continuity; hMeasFII deferred base meas).
LANDED: hDConv_from_banked (chain composed at the concrete witness, Da := DaTrunc H F);
a1_R6_of_residue_inf_v6 (= v5 minus black-box hDConv, re-derived internally). Post-v6
walls: hDaLimLU + hD1 (+ Levi/Duhamel interface + facades = data). std-3, budget raw 0.
NOT a₁=R/6. NEXT: Ph8 TruncatedDuhamelData facade.

## J4-210 (2026-08-05, ce18a73c) — TruncatedDuhamelData: the semantic Levi/Duhamel facade [AF]
Sol Ph8. The v5/v6 five-slot cluster {hEboundW_le,hInt,hDuhamel,hInter,hDConv} → four Prop
bundles (Core.hIdentity→hDuhamel; Bulk.hDiff→hDConv; Endpoint.hEbound/hIntegrable→
hEboundW_le/hInt; Interchange.hSeries→hInter). Adapters: hDuhamel_of_truncatedData +
duhamelInterface_of_truncatedData (four bundles → the full 5-conjunction). Providers:
Core ← hDuhamel_leviSeries_of_daLim (rests on hDaLimLU), Interchange ←
heatConv_leviSeries_interchange (DATA residue), Endpoint ←
iterConvIntegrableW_of_bound_baseMeas (hEbound = envelope DATA), Bulk ←
hDConv_from_banked (J4-209). std-3, budget raw 0. NOT a₁=R/6. NEXT: Ph9 CapstoneAssembly.

## J4-211 (2026-08-05, 6dbf022e) — CapstoneAssembly: a1_R6_of_geometry_and_frontier [AF]
Sol Ph9. v6's conclusion; four flat Levi/Duhamel slots → the three J4-210 bundles
(endpoint/core/inter; Bulk omitted — hDConv already internal to v6). Pure composition.
MASTER ENUMERATION: GEOMETRY flat · BANKED bundles (core rests on hDaLimLU) · DATA
(CConv facades, hCH, the hDConv analytic block) · **ONE WALL at capstone level =
hDaLimLU**. ⚠ hD1 caveat: hD1_from_data is scalar-typed vs the CLM-valued Dmap — lift
missing, hD1 NOT fully banked. Rejections (size-based, in-header): local-data threading
+ the _walls stretch re-expose larger ∀τ>0-global residues. std-3, budget raw 0.
NOT a₁=R/6. NEXT: Ph10 recon (hEmeas obligation map + variational-jet shape-match).

## J4-212 (2026-08-05, b23ee9f4) — HEmeasRecon: the hEmeas obligation map + B1 [AF]
Sol Ph10 recon. hEmeas = TWO axes: factor/diagonal (.choose-free) DISCHARGED from
geometry; flow/triple axis single .choose entry = uniformFlowExp (base q enters only via
uniformInverseChart). OBL-4/OBL-6 discharged; OBL-1 (triple hEmeas) reduces via E3e to
OBL-2 (joint C⁰) + OBL-3 (hKp1, joint C¹-in-base). STRETCH: flow_base_continuousOn_of_
gronwall = the FIRST base-slot continuity of the .choose flow (Grönwall Lipschitz
modulus). LADDER: B1✓ → B2 joint weld → B3 inverse chart (OBL-5) → B4 kernel C⁰ (OBL-2)
→ B5 ★WALL = base-point C¹ variational Grönwall (OBL-3) → B6 wrapper
(heatOp_qregularity_of_jointCont certifies content). NAMED WALLS: hDaLimLU + hKp1(B5)
(+ hD1 CLM lift). std-3, budget raw 0. NOT a₁=R/6. NEXT: B2 FlowJointContinuity.

## J4-213 (2026-08-05, 6ac4cf7d) — FlowJointContinuity: B2 joint flow continuity [AF]
hEmeas ladder B2. uniformFlowExp_joint_continuousWithinAt/_continuousOn on K ×ˢ ball 0
ρ_K — triangle weld: W3 base Lipschitz (uniform in w) + velocity slot at fixed q₀
(contDiffAt2.continuousAt). ContinuousWithinAt = honest shape. + B4 seed
uniformFlowExp_smoothFactor_continuousOn. B3 discovered ALREADY BANKED
(ChartGeneralPContinuity.chartP_continuousOn — don't-under-credit vindicated again).
OBL-2 residual gap documented (inverse-chart entry + τ/p slots E3a-E3e + reach).
std-3, budget raw 0. NOT a₁=R/6. NEXT: B4 KernelJointContinuity (OBL-2).

## J4-214 (2026-08-05, cb72f2a9) — KernelJointContinuity: B4 honest verdict [AF]
Global OBL-2 (Continuous over ℝ×Pⁿ×Pⁿ) UNSATISFIABLE — structural edges E-τ0 (diagonal
Gaussian blow-up at τ=0) + E-gate (hard set-gate jumps at ∂K/∂(S q)). Maximal honest:
kernelBase_jointContinuousOn_pos ({τ>0}) + kernelGated_jointContinuousOn_inGate.
hEmeas_of_hKp1 REFUSED (unsatisfiable hyp — firewall held). KEY DISCOVERY: the strong
measurability OBL-2 fed is ALREADY discharged via the Borel route
(InnerKernelJointMeas.hinnerJ_discharged/hjoint_final, globally Borel across τ=0) —
the OBL-2 continuity line RETIRES; whether hKp1 (OBL-3) is needed AT ALL = next audit.
std-3, budget raw 0. NOT a₁=R/6. NEXT: J4-215 HEmeasBorelAudit (may retire hKp1).

## J4-215 (2026-08-05, a74bf64c) — HEmeasBorelAudit: ★ hKp1 RETIRES ★ [AF]
THE DEFINITIVE hEmeas RE-AUDIT. S1 (triple hEmeas) = the one upstream measurability slot
(feeds EndpointData/InterchangeData; S2 via iterE_zmeas). Route A (E3e) needed
hKcont+hKp1 — an ARTEFACT (measurable_deriv_with_param wants joint continuity in the
.choose base). Route B (E3d) = pure Borel algebra; the banked gate-eq machinery (J4-185
first-pd + J4-198 second-pd) feeds it continuity-free. Banked: tripleHEmeas_of_surface
(BorelDischargeSurface = measurabilities ONLY) + 5 more. Residue = ROUTINE G-a (varying
p) / G-b (off-diag Hessian) / G-c (∂_τ rep). WALLS NOW: hDaLimLU + hD1 CLM lift. The
B5 variational Grönwall is OFF the critical path. std-3, budget raw 0. NOT a₁=R/6.
NEXT: G-a GatedDerivRepProduct.

## J4-216 (2026-08-05, 24df6db5) — GatedDerivRepProduct: G-a + G-b diagonal [AF]
Product-coordinate gate-eq extension: gatedDerivRepProd + everywhere-identity +
firstFieldPd_prod_stronglyMeasurable = BorelDischargeSurface conjunct (2) EXACT (rfl
bridge); suppliers = measurabilities only. G-b diagonal (gatedDeriv2RepProd) landed.
Honest gaps: G-b MIXED (needs new gaussComp_amp_pd_pd_mixed normal form) + G-c (∂_τ
gate-eq rep). std-3 all 7, budget raw 0. NOT a₁=R/6. NEXT: G-c GatedTauDerivRep.

## J4-217 (2026-08-05, 47fa4206) — GatedTauDerivRep: G-c + tripleHEmeas_concrete_of_mixed [AF]
τ gate-eq rep. Honest τ≤0: gate τ-independent ⟹ funext-global identity; τ≤0 witness ≡0
on Iic τ ⟹ HasDerivWithinAt.deriv_eq_zero forces deriv=0 (no diagonal case analysis;
junk-deriv at the diagonal is 0 anyway). τ>0: product rule + gaussDdim_heat_eqn.
Conjunct (1) EXACT. ★ STRETCH: tripleHEmeas_concrete_of_mixed — S1-concrete with ONLY
the mixed i≠j Hessian (hP2) carried. Remaining measurability = ONE brick
(gaussComp_amp_pd_pd_mixed). std-3 all 4, budget raw 0. NOT a₁=R/6.
NEXT: J4-218 ChartJetHessianMixed (the LAST measurability brick).

## J4-218 (2026-08-05, 2f894d30) — ChartJetHessianMixed: ★ MEASURABILITY FAMILY CLOSED ★ [AF]
The last measurability brick. gaussComp_amp_pd_pd_mixed DERIVED (mixed second moment
⟨V,Pi⟩⟨V,Pj⟩/(4τ²), no −1/(2τ) off-diagonal; + cross-jet + second-jet + amp-cross);
i=j recovers the diagonal — one general-index form. gatedMixed2RepProd + everywhere
identity + conjunct (3) ∀(i,j) = exact hP2. ★ tripleHEmeas_concrete: S1 DISCHARGED
CONTINUITY-FREE (all 5 conjuncts; residue = genuine measurable-jet suppliers only).
The OBL-2/OBL-3 continuity ladder fully obsoleted by the Borel route. std-3 all 11,
budget raw 0. NOT a₁=R/6. WALLS NOW: hDaLimLU + hD1 CLM lift. NEXT: J4-219 HD1CLMLift.

## J4-219 (2026-08-05, d93785c2) — HD1CLMLift: the hD1 CLM-lift wall CLOSED [AF]
J4-211's caveat resolved: NOT a wrong scalar fact — the gap was pure componentwise→CLM
assembly. contDiffAt_clm_of_scalar_components + hD1_clm_of_scalar_and_rep +
hD1_concrete_from_scalar (c i = proj i) + ★ a1_R6_of_residue_inf_v7 (CLM hD1 binder →
n scalar ContDiffAt facts). Residue = hD1_from_data's own sliver carries per component
(bulk HasFDerivAt/limit, x-uniform hsliver + vanishing, order-2 continuity). WALLS NOW:
hDaLimLU ONLY. std-3 all 4, budget raw 0. NOT a₁=R/6. NEXT: J4-220 DaLimLUWallRecon
(THE FINAL WALL).

## J4-220 (2026-08-05, 0e634bf0) — DaLimLUWallRecon: the final-wall census [AF]
hDaLimLU family census: everything BANKED or DATA except ★ hEbnd (+Be/hEblim) — the
RATED x/u-uniform residual-tail bound (etrunc_tendsto is un-rated). NEW:
sliver_sum_bound_U (the ∀u∈U upgrade; u-free B(e)=∑(D0·2√e+D1·e)→0) +
hDaLimLU_of_sliverData (sliver slots eliminated). LADDER: E2 (peel the tail under
hEdom+hBdom, mirror the sliver peel) + E3 (rate). THE LAST WALL IS ONE BRICK WIDE.
std-3 both, budget raw 0. NOT a₁=R/6. NEXT: J4-221 ETailRateBound (E2).

## J4-221 (2026-08-05, 43cc9bfb) — ETailRateBound: ★★ ALL NAMED WALLS DOWN ★★ [AF]
E2: strip-difference identity proved inline (rfl + Chasles); hEbnd_discharge = MemETail
verbatim (hEdom+hFdom+vanishing; inner_slice_bound via Chapman-Kolmogorov + antitone
cap; Be(e)=(E₀+E₁e)·√(3/2)ⁿ·C_L·gaussDdim aT 0·e, u-free). E3: Be_tendsto_zero.
★ hDaLimLU_from_data: the COMPLETE DaLimLUGoal from pure data — no irreducible open
member remains. Walls arc complete: measurability (cp102) + hD1 lift (cp103) + hDaLimLU
(here). Residue = geometric wiring (pdpdH→Ric) + concrete-witness instantiation.
std-3 all 4, budget raw 0. NOT a₁=R/6. NEXT: J4-222 GrandAssemblyRecon.

## J4-222 (2026-08-05, cd3cf30d) — GrandAssemblyRecon: ★★ a1_R6_assembled ★★ [AF]
The grand assembly. Build-checked trace: DaLimLUGoal DEFEQ to the frontier hDaLimLU slot
(daLimLU_reduces_to_pointwise → core hDaLim); tripleHEmeas_is_hEmeas_slot (Iff.rfl).
★ a1_R6_assembled = geometry_and_frontier + hDaLimLU internally discharged + hD1 via
n-scalar route: WALL-FREE, CLM-FREE, same conclusion. LEAVES: GEOMETRY + CD + DATA;
GENUINE-GAP NONE (pdpdH→Ric not open — htr carries the trace). LADDER R1-R7 ⟹ FINAL
a1_R6_of_geometry (the _heatOp_qregularity shape SUPERSEDED — no q-regularity needed).
std-3 all 3, budget raw 0. NOT a₁=R/6. NEXT: J4-223 AssemblyLadderR1R2.

## J4-223 (2026-08-05, 009a351a) — AssemblyLadderR1R2: R1 landed; R2 size-rejected [AF]
R1: a1_R6_assembled_v2 — opaque bundles GONE (hEmeas ← tripleHEmeas_concrete defeq;
hEzero shared; hEbound ← one new hEboundFull ∀τ>0 binder). HONEST: the geometry
provider is τ≤t-weakened; the builders need ∀τ>0 — carried as DATA. Net +6 binders
(depth over count; no opaque Prop bundle left). R2: ALL THREE size-rejected (no ∀u∈U
producers; 1→~14 / 1→~4+hLHSlim / 1→≥4). std-3, budget raw 0. NOT a₁=R/6.
NEXT: R3 core unbundle (hDaLim free).

## J4-224 (2026-08-05, 46a9759a) — AssemblyLadderR3: v3, the last opaque bundle gone [AF]
Net-neutral: −core +hDerivConv. hDaLim + hBoundaryLim discharged FREE (already-carried
data). hDerivConv size-rejected (≥4 new families) — one clean limit binder. R4
corrected: facades are INPUTS (full unbundle ≈ +15) — partial only. Next genuine
discharges: R1½ suppliers-from-smoothness + R5 hgD1 (size-gated). std-3, raw 0.
NOT a₁=R/6. NEXT: J4-225 R1½+R5.

## J4-225 (2026-08-05, 0efdf6a5) — AssemblyLadderR5: v4 (honest partial) [AF]
hchrMeas −1 FREE (hChr.continuous.measurable); hgiMeas→hgiC deepened. BLOCKS honest:
hcar* (global joint chart Borel + general-gate PdiffAt + Cfield HasDerivAt = new
analysis); hgD1 size-rejected (~30 per-slice carries vs the integrated D0/D1/hbnd).
Three real-analysis items named: hcar* closure / concrete-gcoef sliver / F2+hFII.
std-3, raw 0. NOT a₁=R/6. NEXT: J4-226 ChartJointBorel (hcar* item 1a — Borel NOT
continuity, the unsatisfiability doesn't apply; representative-swap route in reserve).

## J4-226 (2026-08-05, 98cbe58c) — ChartJointBorel: hcar* → ONE hChartRep (v5) [AF]
The chart read: off-gate CONSTANT 0; on-gate .choose that FORGOT E_q.symm ⟹ raw joint
measurability = definitional wall. Discharged the piecewise half
(chartJoint_measurable_of_rep); tripleHEmeas_concrete_v2 = 3 opaque conjuncts → 1
shared hChartRep (∃ measurable representative agreeing on-gate). v5 threaded. The true
content: CONSTRUCT the representative from the flow (Θ jointly cont (B2) + injective
(Neumann) ⟹ Lusin–Souslin). std-3, raw 0. NOT a₁=R/6. NEXT: J4-227 ChartRepConstruction.

## J4-227 (2026-08-05, e7dd1550) — ChartRepConstruction: the Lusin–Souslin layer [AF]
flowInverse_jointMeasurable_regional: Θ ContinuousOn (B2) + InjOn (germ) on
K ×ˢ closedBall 0 ρ ⟹ measurableEmbedding ⟹ global measurable G with ON-IMAGE
agreement. v6 REFUSED (off-image choose_q = junk, unprovable — firewall). DECISIVE
NEXT: do the gate-eq consumers need the RAW chart meas or only gated compositions
(regional G would suffice; radii chain S q vs flow image to verify). std-3, raw 0.
NOT a₁=R/6. NEXT: J4-228 GatedChartMeasAudit.

## J4-228 (2026-08-05, 355fa68b) — GatedChartMeasAudit: ★ GATED-SUFFICIENT ★ [AF]
The decisive audit: raw chart meas enters every consumer only ×amplitude factors that
vanish for ‖W‖≥b ⟹ each rep = its Gc-twin pointwise; twin measurable WITHOUT the raw
chart. Banked: hWG_of_unguarded (guard strictly weaker — non-vacuous), four _v2 reps,
three conjunct capstones _v2, ★ tripleHEmeas_concrete_v3 (chart-meas conjunct
DISCHARGED: regional Gc + hWG). Residues: (1) hWG's geometric fact = general-field-point
right-inverse germ (origin-only banked); (2) the v6 entry-point wrapper. std-3 all 11,
raw 0. NOT a₁=R/6. NEXT: J4-229 RightInverseGeneral (A: the germ; B: the v6 wrapper).

## J4-229 (2026-08-05, 47ad1239) — RightInverseGeneral: ★ v6 — raw chart meas ELIMINATED ★ [AF]
KEY: the concrete S-gate IS the flow image (S z = φ_z '' ball 0 c; on-gate right-inverse
already banked). rightInverse_general (germ + image membership) + hWG_concrete (regional
Gc = a THEOREM) + hWG_of_regional_support (only carry = hImg) + v2' (htriple direct) +
★ v6 (tripleHEmeas ← v3 internal — no raw chart measurability anywhere in the assembly).
Chart residue = ONE geometry fact hImg (guard → image membership; radii c vs ρ next).
Analytic residue unchanged. std-3 all 5, raw 0. NOT a₁=R/6.
NEXT: J4-230 ImageSupportDischarge (the hImg audit → possibly v7).

## J4-230 (2026-08-05, 4ba37791) — ImageSupportDischarge: hImg split + ⚠⚠ CRITICAL FLAG [AF]
S-guard hImg FULLY CLOSED (hWG_gate_concrete: Gc internal, radii-only). Amplitude guard
= modulo hSurj (off-image surjectivity, the named wall) — the Cfield disjunct is a free
field, so no single-fact reduction; v7 honestly not delivered. ⚠⚠ FLAG: the hgate
carriers of tripleHEmeas_concrete(+v3) demand ∀-w S-membership — possibly satisfiable
only at K=∅ ⟹ POTENTIAL VACUITY of the hcar supplier line (J4-218→v6). J4-231 = the
satisfiability audit (the axiom-budget blind-spot pattern) BEFORE crediting further.
std-3 all 6, raw 0. NOT a₁=R/6.

## J4-231 (2026-08-05, 57b1c46f) — HgateSatAudit: ⚠⚠ VACUOUS CONFIRMED + the fix [AF]
The hcar carriers assert S-membership as a CONCLUSION over all field points ⟹
UNSATISFIABLE at the concrete gate unless K=∅ (impossibility proofs banked). Blast
radius: 9 files carry it as an OPEN INPUT — LATENT TRAP, not unsoundness (the v* line
= valid conditionals). Root cause: base-only indicator gating. FIX proved (τ template):
gatedTauRepProdS full-gate + conditional hgate + tauDeriv_prod_stronglyMeasurable_v4
(SATISFIABLE). J4-232 = the field/field² surgery ⟹ tripleHEmeas_concrete_v4 ⟹ v7.
std-3 all 9, raw 0. NOT a₁=R/6.

## J4-232 (2026-08-05, 3a9d1dfc) — GatedRepSFix: ★ THE VACUITY FIX COMPLETE AT S1 ★ [AF]
Field/field² S-re-gating: full-gate reps (bodies byte-identical ⟹ defeq to the gate-eq
RHS) + conditional hgate + hKSmeas + v4 conjuncts (2)(3). HONEST NEW: hOffS/hOffS2 (the
field pd's don't vanish pointwise off S — the radialCutoff-support vanishing carried
explicitly, true at the concrete witness). ★ tripleHEmeas_concrete_v4 = S1 with ALL
hypotheses satisfiable (corrects the vacuous J4-218). Gc/hWG _v5 recipe + v7 re-thread
documented. std-3 all 9, raw 0. NOT a₁=R/6. NEXT: J4-233 AssemblyV7Rethread.

## J4-233 (2026-08-05, 6545456d) — AssemblyV7Rethread: ★ v7 the credited capstone ★ [AF]
a1_R6_assembled_v7 = v2' + htriple ← tripleHEmeas_concrete_v4 internal. Gc route
REMOVED (the chart-side Gc/hWG/germ wall BYPASSED via the v4 raw-conjunct route);
vacuous hcar forms → v4 conditional (+hOffS) + hKSmeas. ALL suppliers satisfiable.
Ladder: 1 concrete-S (MED-LARGE; hKSmeas = product-lift via the banked embedding) →
2 Gc+S opt → 3 facades (LARGE) → 4 hDConv pile (LARGE) → 5 R2 trio (LARGE) → 6
core/envelopes (MED) → 7 a1_R6_of_geometry (MED). std-3, raw 0. NOT a₁=R/6.
NEXT: J4-234 ConcreteGateInstantiation.

## J4-234 (2026-08-05, 8e028690) — ConcreteGateInstantiation: step 1 partial [AF]
hKSmeas_concrete (product-lift via the open-ball Lusin–Souslin embedding, rebuilt
parametrically — no ρ carry) + hchrMeas + hS0 + the discharge bundle. HONEST: the full
v7-restatement FREEZES the kernel (~130-binder choose-heavy defeq — never materialize
the full capstone restatement again); hOffS lives INSIDE the hcar existentials (step 2
= the radialCutoff support-closure brick); hgiMeas = genuine input (no gi regularity
carried). std-3 all 4, raw 0. NOT a₁=R/6. NEXT: J4-235 OffSVanishing.

## J4-235 (2026-08-05, 8bb219e7) — OffSVanishing: step 2 done [AF]
The collar lemma via the CLEAN support-closure route (U = closure(φ''ball b)ᶜ; no
frontier analysis; radii 0<a<b<c<δ₀ honest). hOffS/hOffS2_concrete = the exact
GatedRepSFix v4 conjunct shapes. ★ concreteGate_carriers_discharged_v2 = the running
bundle (5 discharges under one δ₀). Remaining in the hcar existentials: the on-gate C²
jets + the jet-coefficient measurability block. std-3 all 5, raw 0. NOT a₁=R/6.
NEXT: J4-236 OnGateJets (the last hcar content).

## J4-236 (2026-08-05, ee7cfd74) — OnGateJets: the on-gate C² jets (bundle v3) [AF]
The C²-at-gate-points was banked (chartField_contDiffAt_reachable_uniform); centre-only
machinery ported to general p. hcarField hgate FULLY satisfied + hcarTau ∂_τ (amp
affine in τ) ⟹ bundle v3 (7 families, one δ₀). TWO residues to the full supplier
block: (1) hcarField2's GLOBAL-y jet family (over-strong packaging — the J4-231/232
surgery pattern again, neighbourhood-only reshape) + (2) hChartRep (the .choose wall).
std-3 all 7, raw 0. NOT a₁=R/6. NEXT: J4-237 Field2NbhdReshape.

## J4-237 (2026-08-05, 292aca3f) — Field2NbhdReshape: the third quantifier surgery [AF]
The hcarField2 global-y weakened (only 3 funext steps were global → EventuallyEq on the
open gate; j-families ∀y∈S, rest at p). Reshaped identity (rep UNCHANGED) + v5
measurability shapes + the general-p second jet + ★ hcarField2_hgate_concrete
SATISFIED + bundle v4. ⟹ ALL THREE suppliers' jet/gate conjuncts satisfiable at the
concrete gate; ONE obligation left = hChartRep. std-3 all 9, raw 0. NOT a₁=R/6.
NEXT: J4-238 ChartRepFinal (the decision brick).

## J4-238 (2026-08-05, f077945a) — ChartRepFinal: the value half discharged [AF]
The audit: chart LITERAL in the existentials; conjuncts split — (1) raw chart SWAPPABLE
(S-gate Gc, hWG_gate_concrete — pure radii, no surjectivity); (2) amp value + Cfield
SWAPPABLE + DISCHARGED (chartFieldAmpGc/chartTauAmpGc measurable + on-gate swaps);
(3) THE ONE WALL = the chart field-JETS/amp field-pd measurabilities (value-only Gc
exposes no derivative — needs the measurable joint field-derivative of the flow
inverse; the difference-quotient-limit route on the open gate = the attack). hcarTau
in-principle fully value-swappable. std-3 all 5, raw 0. NOT a₁=R/6.
NEXT: J4-239 FlowDerivMeasurable (the last supplier wall).

## J4-239 (2026-08-05, 07a7e15d) — FlowDerivMeasurable: ★ the field-derivative wall broke ★ [AF]
The measurable joint field-derivative of the flow inverse = a THEOREM: indicator
difference-quotient sequences of the Gc value-rep + measurable_of_tendsto_metrizable +
the C² on-gate convergence; the mixed second jet one level up; the _component versions
certify the same witnesses satisfy the hgate HasDerivAt conjuncts. ChartRepFinal
residue (3) discharged. Remaining to the v7 supplier payoff: the chart-VALUE Gc-reshape
(kernel-freeze constrained — lighter assembly) + the amp field-pd composition (inputs
now supplied). std-3 all 5, raw 0. NOT a₁=R/6. NEXT: J4-240 AmpPdComposition.

## J4-240 (2026-08-05, 365e4a93) — AmpPdComposition: ★★ all three residue classes = theorems ★★ [AF]
The amp-pd wall closed (first + mixed second, via the once-proven abstract DQ engine —
the whnf trap: never inline heavy defs into tendsto loops). ★ firstFieldPd_prod_
measurable_Gc = the chart-wall-free conjunct-2 consumer (raw-chart hypothesis
eliminated) + the FINAL supplier bundle. Only shape-work left: the literal ∃-bodies
(kernel-freeze) — SIDESTEP identified: tripleHEmeas_Gc via tripleHEmeas_of_surface →
the v2' htriple slot (no restatement). std-3 all 6, raw 0. NOT a₁=R/6.
NEXT: J4-241 GcConsumerMirror (conjunct-3 + τ mirrors → tripleHEmeas_Gc → v8).

## J4-241 (2026-08-05, 7114200a) — GcConsumerMirror: ★★ the htriple supplier side CLOSED ★★ [AF]
The conjunct-3 + τ mirrors landed; ★ tripleHEmeas_Gc = S1 AS A THEOREM at the concrete
gate (chart-wall-free, satisfiable Gc-carriers; the .choose wall never appears). The
plug type-checks into v2''s htriple slot verbatim (hC := hChr) — v8 = mechanical,
deferred. Remaining piles: (1) the routine concrete Gc-carrier ∃-bundle (banked
piecewise); (2) the v2' ANALYTIC residue (hEboundFull/core/hCH/facades/hDConv/R2/
envelopes) = the genuine curvature analytics. std-3 all 3, raw 0. NOT a₁=R/6.
NEXT: J4-242 EnvelopeCoreDischarge (the analytic ladder opener).

## J4-242 (2026-08-05, 650401bf) — EnvelopeCoreDischarge: the analytic census + core [AF]
v2' still carries core raw (predates R3) — core_of_v2prime_data discharges it from
carried data + ONE hDerivConv limit (hDaLim + hBoundaryLim FREE). CENSUS: NO hard wall
at the conditional level; deepest = hDerivConv's F2 family. hEboundFull ∀τ>0 = genuine
DATA (the amplitude grows linearly — no fixed C; clean fix = relax the consumers to
τ≤t, an edit). ORDERED RESIDUE: dominations → hIlo/hIhi → sliver → R2 → facades →
hgD1 → hEboundFull → hDerivConv. std-3, raw 0. NOT a₁=R/6.
NEXT: J4-243 DerivConvDischarge (the deepest residue).

## J4-243 (2026-08-05, bca9564d) — DerivConvDischarge: ★★ the core limit tower CLOSED ★★ [AF]
The carry census: EVERY leaf of derivConv_tendsto is carried-already by v2' (hderiv ←
F2 trio; hfg ← tail + hFII with the never-threaded hAzero find; hDerivLU ← the carried
loc-unif piles). NEW-DATA: NONE. derivConv_of_data + ★ core_of_v2prime_data_FULL (all
three truncation limits internal — the core slot needs nothing new). NO analytic-limit
residue remains; the frontier = DATA-pile satisfiability at the concrete witness +
facades + geometry. std-3 both, raw 0. NOT a₁=R/6.
NEXT: J4-244 DataPileWitnessAudit (the don't-under-credit sweep).

## J4-244 (2026-08-05, 3caad761) — DataPileWitnessAudit: the N=1 audit + THE MAP [AF]
9 concrete discharges (hCH/hsrc from geometry; hAmeas; hEzeroE; hEboundFull-existential-
gate; hchrMeas; the gate carriers; the time window T:=2t; nb). Anchor = v7. THE
FINAL-DISTANCE MAP: [1]S concrete-S re-thread (incremental) [2]M the F2 inner
(s,z)-meas trio (next; widest unblock) [3]M sliver/hD2Hexpand [4]M CConv [5]M/L W3
gate-compat [6]L W2 Leibniz identity [7]L W1 hAnear SHAPE-WRONG [8]S/M jets+Gc.
std-3 all 9, raw 0. NOT a₁=R/6. NEXT: J4-245 InnerMeasFubini (map [2]).

## J4-245 (2026-08-05, 79b88ae7) — InnerMeasFubini: map [2] DONE [AF]
The F2 inner trio discharged (gated-indicator lever + integral_prod_right' Fubini +
hBcont-fed Levi joint meas; product-ae trap avoided). All four conclusions = the v2'
binder shapes verbatim. f2Pack_concrete = the bundle; carries hInner/hWitDeriv/
hLeviJoint/hContDom (bankable-kind, no wall). std-3 all 9, raw 0. NOT a₁=R/6.
NEXT: J4-246 F2CarryDischarge (the three carries → zero-carry).

## J4-246 (2026-08-05, 14c72940) — F2CarryDischarge2: 2/3 carries discharged [AF]
hInner (← witnessInner_measurable_uncurry section + field-0 chart AEMeas) + hWitDeriv
(← the τ gate-eq rep section, satisfiable Cfield carrier). hContDom = the remaining
carry (the per-window Gaussian dominator brick). f2Pack_concrete_v2 = the pack with
both internal. std-3 all 3, raw 0. NOT a₁=R/6. NEXT: J4-247 ContDomWindow.

## J4-247 (2026-08-05, fff8d7aa) — ContDomWindow: f2Pack v3 (all carries internal) [AF]
gaussDdim_window_le (the compact-window dominator) + hContDom_of_gaussDom +
hContDom_discharged (the honest shape: joint (s,z) continuity is FALSE — the slice
hmeas/hcont carried). f2Pack_concrete_v3 = all three J4-245 carries internal; residue
= v2'-level data. std-3 all 5, raw 0. NOT a₁=R/6. NEXT: J4-248 JetsGcUnification (map [8]).

## J4-248 (2026-08-05, d6891133) — JetsGcUnification: ★★ the htriple slot 100% CONCRETE ★★ [AF]
The three Gc-carriers assembled internal (hcarTau/hcarField/hcarField2 from the banked
jets/twins/agreements; exists_forall_radius min-reconciliation; the opaque-obtain trap
fixed). ★ tripleHEmeas_Gc_concrete = S1 from GEOMETRY + radii + measurability ONLY.
NO missing pieces. Map remaining: [1] the v2' re-thread, [3] sliver, [4] CConv, walls.
std-3 all 5, raw 0. NOT a₁=R/6. NEXT: J4-249 SliverCConvBatch ([3]+[4] recon).

## J4-249 (2026-08-06, 7f1aeaf2) — SliverCConvBatch: sliver = W1 (verdict) [AF]
hD2Hexpand MISMATCH precisely delimited: base-point vs chart-image Gaussian; the ratio
exp(−O(‖z‖⁴)/4τ) unabsorbable with bounded amplitudes ⟹ sliver [3] ≡ hAnear [7] ≡ W1
= the near-isometry campaign (rncRadialSq(W z 0)=‖z‖²+O(‖z‖⁴) + ratio absorption).
Banked: witnessSecondXDeriv_chartImage_expand (the honest starting form). CConv: W4 +
Source = genuine DATA. Frontier: [1] re-thread + W1 campaign + W2/W3/W4. std-3, raw 0.
NOT a₁=R/6. NEXT: the gpt-5.6-sol W1/W2/W3 route consult, then the recommended brick.

## SOL CONSULT #4 (2026-08-06) — THE W1-W4 ROUTE (gpt-5.6-sol, recorded verbatim-gist)
★ DECISIVE: the exact-width amplitude package (hAnear/hD2Hexpand as demanded) is
GENERALLY FALSE — the ratio G_τ(q z)/G_τ(z) → ∞ as τ→0 for any fixed z with
‖q z‖<‖z‖; Gaussian suppression helps after integration, NOT as a pointwise τ-uniform
amplitude bound. DO NOT prove the old forms — build the PARALLEL WIDE package:
G_{λτ}(z) with strict width gap (η-shrunk gate, 1/λ < 1−η ⟹ (‖z‖²/τ)^k·G_τ(q z) ≤
C·G_{λτ}(z)). Chart jets needed: q(0)=0, Dq(0)=I, D²q(0)=0 + CUBIC/quadratic/linear
remainders (‖q−z‖≤C‖z‖³ etc.) — from the flow ODE jets differentiated through the germ
+ ThirdJetBounds (C² alone INSUFFICIENT); htr not needed here. W2: uniform-in-u
majorants, ONE master engine instantiation; ⚠ the raw s⁻¹ endpoint is NOT integrable —
use the banked cancellation/splitting. W3: plumbing (FixedFlowGateData record;
re-instantiate providers at ONE fixed gate; ⚠ integral-domain conclusions need
re-instantiation not restriction). W4: near/annulus/outside trichotomy from the same
width-gap infra (τ^{-m}e^{-a²/cτ} ≤ Cτ^N on the annulus). THE 11-BRICK ORDER:
1 GaussianWidthTransfer → 2 FixedFlowGateData → 3 InverseChartNormalJets →
4 FixedGateProviders → 5 WideWitnessAmplitude → 6 WideSliverBoundary →
7 FixedGateDichotomy → 8 FixedGateSourceSlice → 9 SecondOrderMajorants →
10 SecondOrderInterchangeConcrete → 11 WideA1Assembly (the parallel wide capstone
proving the SAME final proposition).

## J4-250 (2026-08-06, 5511366c) — GaussianWidthTransfer: wide brick 1/11 [AF]
The master width-gap lemmas: gaussDdim_closed; gaussDdim_width_ratio_le (G_τ(w) ≤
(√lam)^n·exp(−c·r²/τ)·G_{lamτ}(z) under the (1−eta)-gate); the series sup
y^k e^{−cy} ≤ k!/c^k; poly_absorb + k=0/1/2 + mixed instances; integrability
re-exports. ⚠ lam not λ. std-3 all 10, raw 0. NOT a₁=R/6.
NEXT: J4-251 InverseChartNormalJets (wide bricks 2+3).

## J4-251 (2026-08-06, e6ce8514) — InverseChartNormalJets: wide bricks 2+3 [AF]
★ The near-isometry WAS BANKED (InverseChartDisplacement.chartW0_nearIsometry — coarse
c=1/2 + sharp (1±δ); the sign W₀ z ≈ −z; no base-side third jets needed). LANDED:
chart_width_gate + the FixedFlowGateData record + .of_geometry + .gate + .poly_absorb
(the wide hAnear/hD2Hexpand shapes ready). std-3 all 4, raw 0. NOT a₁=R/6.
NEXT: J4-252 WideWitnessAmplitude (brick 5).

## J4-252 (2026-08-06, d0d6450f) — WideWitnessAmplitude: wide brick 5 [AF]
The factorization bridge + zeroth_domination (≤ C·G_{lamτ}; off-gate 0) +
zeroth_domination_global (hSupp carried — the one-sided-gate chicken-and-egg honest) +
second_domination (the clean ≤ C·τ⁻¹·G_{lamτ}) + ★ WideAmplitudePackage.of_data.
Carries: hAmp0/hSecondEnv (CompactJetBounds + upper near-isometry = follow-ons)/hSupp.
⚠ GL reserved notation. std-3 all 5, raw 0. NOT a₁=R/6.
NEXT: J4-253 WideSliverBoundary (brick 6).

## J4-253 (2026-08-06, e4be04dc) — WideSliverBoundary: wide brick 6 [AF]
The crude τ⁻¹ route proven DIVERGENT (the √ε comes from the moment structure) — the
moment-aware route carried. wide_sliver_sum_bound(_U) + wide_second_inner_slice_bound
+ gaussDdim_wide_approx_identity(_family). Brick-11 carries: sliver hbnd, boundary-f
continuity, the 7/8 globalization. std-3 all 6, raw 0. NOT a₁=R/6.
NEXT: J4-254 FixedGateDichotomy (brick 7).

## J4-254 (2026-08-06, e9f182f9) — FixedGateDichotomy: wide brick 7 [AF]
annulus_invpow_exp_le (dimension-independent super-poly decay) + the support-based
global dominations (hSupp carry) + global_of_near_far (the trichotomy globaliser).
W4 hGateData carried (the exact-width on-gate envelope = the brick-11-parallel
construction). std-3 all 6, raw 0. NOT a₁=R/6. NEXT: J4-255 SecondOrderMajorants (brick 9).

## J4-255 (2026-08-06, b105c5ba) — SecondOrderMajorants: wide brick 9 [AF]
The W2 engine's bound/hbdd/hbound slots FILLED u-uniformly + non-singularly:
window_inv_le (the truncated-window key — (u−s)⁻¹ ≤ ε_m⁻¹; the ε→0 limit = the closed
sliver/DaLim machinery) + secondBoundConst + the slot theorems. Brick 10 remaining:
the concrete snb-uniform second-order domination + measurability plumbing + threading.
std-3 all 4, raw 0. NOT a₁=R/6. NEXT: J4-256 SecondOrderInterchangeConcrete (brick 10).

## J4-256 (2026-08-06, d63ad309) — SecondOrderInterchangeConcrete: ★ the W2 engine FIRED ★ [AF]
The snb-uniform field-shifted second-order domination (off-gate discharged; hOn carry =
the field-shifted near-isometry, brick-11-parallel) + the hbound discharge + ★
witness_MemInterchange(_majorant) = the verbatim MemInterchange member PRODUCIBLE for
the concrete witness (residual = the named providers hQ1/hFmeas/hFint/hF'meas/hdiff +
hOn/hF). std-3 all 4, raw 0. NOT a₁=R/6. NEXT: J4-257 FixedGateSourceProviders (8+4).

## J4-257 (2026-08-06, 1d5fff26) — FixedGateSourceProviders: wide bricks 8+4 [AF]
The Levi source slice (hFjoint discharged no-carry; hFmeas + hFsum carry; hFbd carried
— the τ-uniform constant is genuine input) + the fixed-gate wide dominations (composed)
+ hEboundFull carried (the W3 wall: the provider picks its own existential gate) +
fixedGateProviders_bundle. ⚠ the monolithic-by-block whnf trap → split lemmas.
std-3 all 5, raw 0. NOT a₁=R/6. NEXT: J4-258 WideA1Assembly (brick 11 — the recon).

## J4-258 (2026-08-06, 0f6f8df2) — WideA1Assembly: ★★ THE WIDE CAMPAIGN COMPLETE ★★ [AF]
Sol #4 confirmed at code level: the exact-width forms appear NOWHERE in the conclusion
chain; the leading term = hParam∘hHeat (width-independent DeWitt cancellation); the
only width-2 hardcoding = one summability call over a width-parametric engine ⟹ the
mechanical swap. ★ wide_a1_R6_of_residue_inf_v5 = the SAME conclusion at ANY κ (the
wide bank feeds at κ:=lam). POST-WIDE MAP: [1] residual assembly (∂_τH−Δ_gH; LARGE)
[2] p=0→(p,q) (MED) [3-4] width adapters (SMALL) [5] CConv instantiation (MED).
std-3 all 3, raw 0. NOT a₁=R/6. NEXT: J4-259 WidthAdapters ([3]+[4]).

## J4-259 (2026-08-06, c720e788) — WidthAdapters: post-wide [3]+[4] done [AF]
The bridge + the wide IterConvIntegrableW producers + the slot glue + the live-bank
end-to-end composition at p=0. The width machinery gates NOTHING. hEboundW_le waits on
[1] (the residual assembly — the heat-equation cancellation) + [2] (p=0→∀(p,q)).
std-3 all 7, raw 0. NOT a₁=R/6. NEXT: J4-260 ResidualAssemblyRecon ([1]).

## J4-260 (2026-08-05, ed953238) — ResidualAssemblyRecon: ★★ THE RESIDUAL WALL CLOSED (κ≥2) ★★ [AF]
THE RECON: the width-2 hEboundW provider's cancellation = the PARAMETRIX-RESIDUAL
IDENTITY (on-gate heatOp witness = parametrixResidualN via htransport; the DeWitt
transport equations bake the τ⁻¹ cancellations in; O(r)/τ → O(1) via odd-power width
absorption r·G_{3/2} ≤ √τ·G_2); the chart-image→base transfer = the 3/2→2 width margin
paying the near-isometry budget ⟹ THE PROVIDER WAS INTRINSICALLY WIDE ALL ALONG, and
already ∀(p,q) (post-wide item [2] NOT needed). ★ baseKernelW_two_le_of_two_le (the
pure width-up transfer, the only new math) + hEboundW_widen + hEboundW_wide_from_geometry
(the capstone slot from geometry at free κ≥2) + wide_a1_R6_of_residue_inf_hEboundW_discharged
(the residual slot INTERNAL; the existential provider-chosen gate sidesteps W3).
REMAINING: [small] hInt at κ; [medium] hCConv/facades; the carries.
std-3 all 4, raw 0. NOT a₁=R/6. NEXT: J4-261 WideHIntDischarge (hInt at κ).

## J4-261 (2026-08-05, 331cd206) — WideHIntDischarge: hInt REDUCED; the affine τ-range mismatch [AF]
iterConvIntegrableW_wide (the abstract slot shape) + hInt_wide_from_geometry (hEzero
DISCHARGED via hEzeroE_concrete, 1≤n) + hInt_wide_of_surface (hEmeas → the
continuity-free BorelDischargeSurface). ★ INTEL: the capstone consumes both residual
slots at ONE C', but the geometric provider gives only τ≤t with AFFINE C·(1+t);
all-τ fixed-C is unobtainable (the prefactor survives width changes) ⟹ the stretch
NOT produced (firewall). Obstruction = τ-range/affine coefficient, NOT the gate.
FIX HYPOTHESIS: a₁=R/6 is a t→0⁺ asymptotic — a small-time truncation (t≤T₀) makes
the constant C·(1+T₀) fixed. std-3 all 3, raw 0. NOT a₁=R/6.
NEXT: J4-262 TruncatedHIntRethread (the small-time truncation).

## J4-262 (2026-08-05, 28051a6b) — TruncatedHIntRethread: ★ THE AFFINE OBSTRUCTION DISSOLVED ★ [AF]
C-ROUTE CONFIRMED: every IterConvIntegrableW consumer touches only the OUTER conclusion
time (WideA1Assembly:131 → RestrictedEboundW, outer-t only) ⟹ the J4-261 all-τ
obstruction was a τ-range artifact. IterConvIntegrableWOn (t≤T₀ family) +
eboundW_affine_to_fixed_trunc (affine C·(1+τ) → fixed C·(1+T₀)) + the truncated
producer + iterConvIntegrableWOn_of_affine_trunc + iterConvW_bound_le_trunc +
leviSeries_summableW_le_trunc (the capstone's exact hInt consumption, drop-in proven) +
levi_converges_from_affine_trunc (END-TO-END: affine geometry bound ⟹ Neumann
convergence on 0<t≤T₀). RESIDUAL: the capstone rethread (hInt binder retype + the
one-line swap) not yet materialized. std-3 all 6, raw 0. NOT a₁=R/6.
NEXT: J4-263 WideA1AssemblyTrunc (the rethreaded capstone + hInt internal).

## J4-263 (2026-08-06, f9ab23ec) — WideA1AssemblyTrunc: ★★ BOTH RESIDUAL SLOTS INTERNAL ★★ [AF]
wide_a1_R6_trunc (the capstone source, exactly 2 edits, conclusion IDENTICAL) +
wide_a1_R6_of_residue_inf_trunc + ★★ wide_a1_R6_both_slots_internal (κ≥2; both
hEboundW_le AND hInt internal — shorter than the J4-260 capstone by the hInt arrow).
Constant finding: NO mismatch — hEboundW_wide_from_geometry's τ≤t bound is at a single
fixed C'' (the affine (1+t) factor is constant at fixed t); both slots fill at the
same C''; the affine route wasn't even needed. HONEST CARRIES: 1≤n · ∀-gate S1
tripleHEmeas (→ tripleHEmeas_of_surface) · base geometry hyps · the inner Levi/Duhamel
arrows hS0/hDuhamel/hInter/hDConv/hCH/hCConv. std-3 all 3, raw 0. NOT a₁=R/6.
NEXT: J4-264 InterfaceArrowCensus (banked-provider census + discharge of the arrows).

## J4-264 (2026-08-06, 62f7bfa8) — InterfaceArrowCensus: the CENSUS; hS0+hCH DISCHARGED [AF]
CENSUS (gate (a,b,S) provider-chosen/existential ⟹ per-S arrows need provider EXPORTS):
hS0 DISCHARGED (gatedWitnessN1_package_open ∘ hEboundW_widen) · hCH DISCHARGED
(hCH_discharge_from_geometry, +hgiC/hgpos) · hDuhamel GENUINE (per-S) · hInter GENUINE
(per-S) · hDConv PARTIAL (per-S + hDaLimLU) · hCConv PARTIAL (per-S + 5 facades) · S1
∀-gate PARTIAL (per-(S,a,b) banked; no ∀-provider). LANDED:
hEboundW_wide_from_geometry_open + wide_a1_R6_interface_discharged (implication shorter
by hS0+hCH; surviving antecedents hDuhamel/hInter/hDConv/hCConv; carries 1≤n + S1
∀-gate + base geometry incl. hgiC/hgpos). ROUTE: provider-side export at the concrete
gated-witness gate (the hS0/hCH pattern). std-3 both, raw 0. NOT a₁=R/6.
NEXT: J4-265 ProviderSideExports (hDuhamel/hInter at the concrete gate).

## J4-265 (2026-08-06, 13077977) — ProviderSideExports: ★ hInter EXPORTED ★ [AF]
The hS0/hCH pattern extended: the per-S hInter interchange identity proven at the
concrete gate (InterchangeLocalRebase.hInter_from_local_data, J4-206) — the crux: the
universal-over-ceiling export gives hEbnd AND hglobal from one source; hEzero via
hEzeroE_concrete; width-2 interchange, width-free hInter ⟹ feeds the κ capstone.
wide_a1_R6_interface_discharged_v2: implication = hDuhamel → hDConv → hCConv → ⟨a₁⟩.
CENSUS: exported hS0/hCH/hInter · surviving hDuhamel (hDaLimLU wall + 3 per-S
truncation-limit facts) / hDConv (analytic residue + hDaLimLU) / hCConv (5 facades).
hDaLimLU = the shared blocker. std-3 both, raw 0. NOT a₁=R/6.
NEXT: J4-266 DaLimLUConcreteDischarge (the shared wall at the concrete gate).

## J4-266 (2026-08-06, c2d284ec) — DaLimLUConcreteDischarge: hDaLimLU partial; Da-limit W1-FREE [AF]
hDaLimLU_concrete = the complete DaLimLUGoal at the concrete N=1 witness (pdpdH :=
witnessSecondXDeriv): hInterchange (witness_MemInterchange) + hEzero discharged;
carried DATA: hgi/hΓ, hLapFull, hII_lo/hII_hi, sliver D0/D1/hbnd (→ amplitudePackage
once AmplitudeDerivativeData built at witnessSecondXDeriv), hEdom, hFdom/hFzero,
hIlo/hIhi, hEcomb. ★★ STRUCTURAL: (1) the Da-limit is W1-FREE (hAnear only in the
boundary pile → hBoundaryLim); (2) the hDuhamel/hDConv export is BLOCKED ON W1
(provider-gate satisfiability of hAnear unestablished — not forced). The wide bank
(J4-250/252/253) is the designed weapon. Capstone carry unchanged. std-3, raw 0.
NOT a₁=R/6. NEXT: J4-267 WideBoundaryLimDischarge (hBoundaryLim via the wide forms).

## J4-267 (2026-08-06, a148f07d) — WideBoundaryLimDischarge: W1 partial (boundedness wide) [AF]
The W1 wall precise: hBoundaryLim's provider consumes hAnear at ONE site (hball_eq);
hAnear FALSE at the concrete witness (chart-image Gaussian). LANDED:
wide_boundary_inner_bound + wide_boundaryTrunc_bound + wide_boundaryTrunc_bound_concrete
(the boundedness member discharged at the concrete gate via the wide bank). BLOCKED:
the limit-value member — needs the CHART-IMAGE APPROXIMATE IDENTITY.

## ★ SOL CONSULT #5 (2026-08-06) — the chart-image approximate identity ARCHITECTURE
Ranked plan (least new work): (1) open-gate SET integral (Layer A: boundary_integral_eq
_gate_integral via off-gate vanishing) → (2) chart change-of-variables on the open gate
(Layer B: chart_gaussian_change_variables via MeasureTheory.integral_image_eq_integral_
abs_det_fderiv_smul applied to W, J=|det DW|>0 on the shrunken gate, use the REAL C¹
chart not the measurable representative for the derivative; set-integrals not global
indicators; boundary: witness must vanish on Sᶜ INCL. the boundary or a.e.) → (3) the
generic SET-VALUED MOVING approximate identity gaussDdim_set_approx_identity_moving:
hyps = Ω ∈ 𝓝 0 + eventual AEStronglyMeasurable on Ω.restrict + eventual uniform bound
+ JOINT local convergence at (0⁺,0) (∀ε∃r: eventually ∀ᵐw, ‖w‖<r→‖g τ w−L‖<ε) — ⚠
pointwise+bound NOT sufficient (the h(w/√τ) spike counterexample); proof = 3ε with the
banked base AI applied to ball-complement indicators + the constant 1 + Ω.indicator
(NOT plain DCT — no fixed dominator). Then q τ w := A τ (V w)·F(t−τ)(V w) 0/J(V w) →
A(0,0)·F(t,0,0)/J(0) = F t 0 0 (normalization CONFIRMED: A(0,0)=J(0)=1 in RNC; obligation
A(0,0)=J(0); √Δ diag = 1; watch only the integration-measure density ρ(0)).
Amplitude hyp needed JOINT: Tendsto A ((𝓝[>]0).prod (𝓝 0)) (𝓝 A(0,0)) — derive from
compact joint continuity if only per-z is banked. Avoid: same-width comparison (=hAnear),
rescaling+DCT (more work), inverse-map |det DV| (unless V-bank stronger).

## J4-268 (2026-08-06, 6858c5fd) — ChartImageApproxIdentity: ★ Layer C landed ★ [AF]
gaussDdim_set_approx_identity_moving (the set-valued MOVING approximate identity; the
JOINT hlocal unweakened; 3ε/concentration NOT DCT) + the reusable subs
(setIntegral_le_one, set_mass_tendsto_one, ballCompl_mass_tendsto_zero,
set_moving_dist_bound). RESIDUAL toward hBoundaryLim: Layer A (gate rewrite), Layer B
(chart change-of-variables), the concrete instantiation. std-3 all 5, raw 0.
NOT a₁=R/6. NEXT: J4-269 ChartGaussianChangeVar (Layer B + A).

## J4-269 (2026-08-06, fe4d230e) — ChartGaussianChangeVar: Layer B abstract [AF]
chart_gaussian_change_variables: ∫_S G_τ(Wz)·B = ∫_{W''S} G_τ·(B∘V/J∘V) from standard
CoV data via the UNCONDITIONAL Mathlib Jacobian formula + on-S J-cancellation; matches
the Layer C consumer shape. Concrete corollary blocked on M1–M4 (within-derivative
field on a gate / InjOn radius / left inverse / uniform det bound) = ONE uniform local
IFT package for uniformInverseChart (bank: Vmap-via-IFT 891c5847, J4-251 near-isometry,
expMap C²). std-3, raw 0. NOT a₁=R/6. NEXT: J4-270 ChartIFTPackage (M1–M4).

## J4-270 (2026-08-06, c8a46fa9) — ChartIFTPackage: ★ M1–M4 ALL PROVEN ★ [AF]
chartIFTPackage (carries only (hC,hK,h0K)): the full CoV bundle on ball 0 ρ for the
base-0 chart — M1 derivative field, M2 InjOn PROVEN (ContDiffAt.toOpenPartialHomeomorph),
M3 left inverse PROVEN, M4 |det|>0; banked centre facts (ChartJetBounds) + the
UniformFlowLocalInverse IFT incantation. + chartImage_mem_nhds (Ω∈𝓝0 glue) +
chart_gaussian_change_variables_concrete (CONCRETE Layer B). ⚠ orientation flag:
base-0 vs base-varying — reconcile at the W1 assembly. RESIDUAL: Layer A + the
moving-integrand trio. std-3 all 3, raw 0. NOT a₁=R/6.
NEXT: J4-271 ChartImageAIConcrete (the A+B+C composition).

## J4-271 (2026-08-06, 90950d2e) — ChartImageAIConcrete: Layer A + conditional A∘B∘C [AF]
★★ ORIENTATION VERDICT: "W₀" is OVERLOADED — the factorization/wide pipeline is
BASE-varying (Wbv: z ↦ uniformInverseChart z 0); the J4-270 package is FIELD-varying;
agree only at 0 ⟹ cannot plug. LANDED: boundary_integral_eq_gate_integral (Layer A
CONCRETE) + boundary_integral_eq_chartImage_integral (A∘B at an abstract Wbv bundle) +
chartImage_approx_identity_conditional (the fixed-f W1 member conditional on: (a) the
Wbv CoV bundle, (b) the JOINT amplitude limit, (c) A₀(0)=1). std-3 all 3, raw 0.
NOT a₁=R/6. NEXT: J4-272 BaseVaryingIFTPackage (gap (a); InverseChartNormalJets is
Wbv-oriented — reuse; UniformFlowLocalInverse.basepointChart_exists — check its chart).

## J4-272 (2026-08-06, f9a607e8) — BaseVaryingIFTPackage: gap (a) → ONE input [AF]
baseVaryingChart_hasFDerivAt_center (UNCONDITIONAL: D Wbv(0) = −id from the banked
displacement bound) + baseVaryingIFTPackage (the full M1–M4 + image-nbhd bundle,
conditional ONLY on hbaseC2 = base-slot ContDiffAt 2 at 0 — the recognized J3 blocker;
M2/M3 proven, M4 det(−id)=(−1)ⁿ). (c) A₀(0)=1 deferred (u₀(0)=1 is a carried DeWitt
input, not a bare lemma). std-3 both, raw 0. NOT a₁=R/6.

## ★ SOL CONSULT #6 (2026-08-06) — hbaseC2 via GEODESIC REVERSAL (ranked #1)
THE IDENTITY: U z 0 = − terminalVelocity 0 (U 0 z) eventually at 0 (reverse the
geodesic from (0, U 0 z) ending at (z, u): start (z, −u) ends at 0 ⟹ left-inverse at
base z gives U z 0 = −u). NEEDS ONLY: (1) the banked FIELD-slot C² of U 0 · (chart at
base 0), (2) fixed-base C² (or C¹ after refactor) of terminalVelocity 0 in the initial
velocity (the velocity projection of the phase flow — MUCH weaker than joint base
dependence; the same ODE machinery as expMap_contDiffOn_four), (3) a reusable
time-reversal lemma (flow 1 p v = (q,u) ⟹ flow 1 q (−u) = (p,−v), by ODE uniqueness),
(4) gate management (4 eventual memberships from continuity+compact-uniform radii).
Transfer: EventuallyEq.contDiffAt_iff / ContDiffAt.congr_of_eventuallyEq. AVOIDS the
.choose coherence AND joint base regularity entirely. ⚠ ALSO: C² is likely OVERKILL —
M1–M4 need only local C¹ (+ the strict derivative at 0 from C¹); consider refactoring
the bundle to hbaseC1/hbaseC1Nhd. Rank 2 = the C¹ refactor; rank 3 = doubled-map IFT
(needs joint C² — the (J)-tower gives pointwise first-order only, NOT joint); rank 4 =
strict+two-point (INSUFFICIENT for M1 — no derivative field); rank 5 = carry hbaseC2
labelled (honest fallback, true of the real exp chart). Mathlib joint C^k ODE-flow
dependence: NOT usable off-the-shelf — don't plan around it.

## J4-273 (2026-08-06, a2ff61a9) — GeodesicReversalRoute: ★★ THE J3 BLOCKER → hT0 ★★ [AF]
The SOL#6 chain ALL LANDED: (R) flipVel algebra + the reversal ODE fact · (REACH)
E z (−u) = q by ODE uniqueness · (RI0) chart0_rightInverse · ★ (I)
baseSlot_eventuallyEq_neg_terminalVel (Wbv =ᶠ −T₀∘(U 0 ·), hyps only hC/hK/K∈𝓝0) ·
(T) the full M1–M4 Wbv bundle gated ONLY on hT0 : ContDiffAt ℝ 2 (terminalVel0) 0 —
a fixed-base velocity-endpoint C² (bank: first Fréchet derivative at 0 + position C⁴;
the velocity slot is one order less). The .choose base-slot coherence is REPLACED by a
standard fixed-base ODE regularity. std-3 all 7, raw 0. NOT a₁=R/6.
NEXT: J4-274 TerminalVelC2 (hT0 — mirror the position-C⁴ tower at the velocity
component to order 2; check if C¹+strict suffices per the rank-2 refactor).

## J4-274 (2026-08-06, 34bd0214) — TerminalVelC2: ★★ hT0 LANDED — THE J3 BLOCKER DEAD ★★ [AF]
Route (a) geodesic homogeneity, NO new tower: terminalVel0 v = fderiv (uniformFlowExp 0)
v [v] (scaleVel algebra + degree-2 homogeneity + the reparametrisation ODE-uniqueness
identity + the diagonal identity) ⟹ terminalVel0_contDiffAt_two (C⁴→C³→C², the "one
order less") ⟹ ★★ baseVaryingIFTPackage_unconditional: the full M1–M4 Wbv bundle from
only (hC, hK, K∈𝓝 0). The .choose/joint-base J3 blocker is REMOVED. std-3 all 5,
raw 0. NOT a₁=R/6. NEXT: J4-275 FixedFChartImageAI (plug the bundle into the
conditional capstone + discharge the Layer-C trio + (b) joint amplitude limit +
(c) A₀(0)=1 labelled).

## J4-275 (2026-08-06, bd42c7e7) — FixedFChartImageAI: ★ THE PLUG — 12 → 5 carries ★ [AF]
chartImage_measurableSet_of_bundle (hΩmeas via Lusin–Souslin) +
chartImage_approx_identity_of_amp ((ρ,V,f') PRODUCED from the J4-274 bundle; M1–M4 +
hΩnhds + hΩmeas discharged). CARRIES (5): hGgate + hSupp + hmeas/hbound/hlocal.
INTEL: the trio needs BASE-SLOT amplitude facts (the amp bank is field-slot; van-Vleck
symmetry = candidate dividend); hSupp radius mismatch (ρ_S vs ρ) → the ball/annulus
split. std-3 both, raw 0. NOT a₁=R/6. NEXT: J4-276 BaseSlotAmplitude (+annulus split).

## J4-276 (2026-08-06, 2474f90c) — BaseSlotAmplitude: the amp wall resolved (route iii) [AF]
The amp factors entirely through Wbv ⟹ base-continuity = the CoV bundle's M1 slot (no
symmetry/reversal needed). baseSlotAmp_continuousOn/_bound/_joint_limit/_centreValue
(A₀ = radialCutoff·vanVleck^{-½}·u₀ at 0; =1 given the labelled RNC normalization).
The J4-275 hbound/hlocal carries reduce to the V/det/f wrapper. std-3 all 4, raw 0.
NOT a₁=R/6. NEXT: J4-277 FixedFTrioDischarge (the v2 capstone), then (B) annulus.

## J4-277 (2026-08-06, 50c1e98b) — FixedFTrioDischarge: hAmpCentre PROVEN; 5 → 4 [AF]
baseChartAmp_centre_eq_one (A₀ = 1 from 0∈K, 0<a<b, det g 0 = 1 — the labelled
normalization now a THEOREM) + chartImage_trio_hmeas (the C3 member discharged via
measurable_extend, no V-continuity) + chartImage_approx_identity_v2 (the fixed-f W1
capstone, FOUR carries: hGgate + hSupp + hbound + hlocal). RESIDUAL: the enriched
partial-homeo bundle (V-continuity + sub-ball images) for hbound/hlocal. ⚠ new trap:
ContinuousOn.comp + ascribed lambda over the .choose chart = whnf blowup. std-3 all 5,
raw 0. NOT a₁=R/6. NEXT: J4-278 EnrichedChartBundle (→ v3 with 2 carries).

## J4-278 (2026-08-06, 839bb1c2) — EnrichedChartBundle: ★★ hbound+hlocal DISCHARGED ★★ [AF]
enrichedChartBundle (ρcap parameter + V-continuity/IsOpen Ω/V 0=0/f'=fderiv/det
exports) + the (W) wrappers + chartImage_approx_identity_v3: the fixed-f W1 capstone
carrying ONLY hGgate + hSupp. The ρ-fit crux solved by capping ρ ≤ ρA. std-3 all 4,
raw 0. NOT a₁=R/6. NEXT: J4-279 GateAnnulusSplit (kill hGgate/hSupp at the concrete
witness → the fixed-f FINAL), then moving-f → hBoundaryLim.

## J4-279 (2026-08-06, 80921877) — GateAnnulusSplit: ★★★ THE FIXED-f AI IS DONE ★★★ [AF]
offBall_integral_tendsto_zero (annulus: wide domination + reparametrized tail) +
hGgate_of_gate_activation + chartImage_approx_identity_final: ∫ Wit τ 0 z·f z → f 0
on 𝓝[>]0 with hGgate/hSupp ELIMINATED; every remaining hypothesis satisfiable (gate
carries ← the openness export; hWslice + the zeroth domination banked). The W1
FIXED-f limit-value member is CLOSED (the near-isometry lower bound wasn't needed —
the domination is base-point). std-3 all 3, raw 0. NOT a₁=R/6.
NEXT: J4-280 MovingFBoundaryLim (the moving-f 3ε step → hBoundaryLim).

## J4-280 (2026-08-06, e7ec469f) — MovingFBoundaryLim: hBoundaryLim W1-free mod hMovingCorr [AF]
SEQ composition + frozenBoundary_tendsto (the frozen 2nd term via the fixed-f AI, no
hAnear) + hBoundaryLim_concrete (conditional on the labelled hMovingCorr; satisfiable
via compact uniform continuity + witness mass + annulus tail). F-facts: hf_meas/hf_bdd
satisfiable-banked; hf_cont unbanked (Levi continuity). NEXT WALL: hDerivConv wants
the LOC-UNIF boundary limit. std-3 all 4, raw 0. NOT a₁=R/6.
NEXT: J4-281 MovingCorrAssembly (Levi joint continuity via M-test + hMovingCorr + hf_cont).

## J4-281 (2026-08-06, 9ae45c09) — MovingCorrAssembly: M-test packaging + mass bound [AF]
The Levi M-test lemmas (z-only + joint + the ContinuousAt-0 hf_cont shape; genuine
data = termwise iterE continuity + summable envelope) + the witness-mass lemmas
(∫|Wit(ε_m)| ≤ CW). hBoundaryLim_unconditional withheld (firewall). ISOLATED RESIDUAL:
(a) termwise iterE joint continuity (parametric convolution continuity) + (b) the
hMovingCorr recombination. std-3 all 5, raw 0. NOT a₁=R/6.
NEXT: J4-282 IterEContinuity (induction: E joint continuity base + heatConv step).

## J4-282 (2026-08-06, 60e6eefc) — IterEContinuity: the moving-limit wall resolved [AF]
heatConv_eq_smul_unitInterval (σ=s·u, unconditional) + the double dominated-continuity
STEP engines + iterE_succ (every k≥1) + iterE_jointContinuousOn (the ALL skeleton =
the M-test hterm feed). RESIDUAL: (R-base) heatOp-witness joint continuity (one
operator past the banked in-gate kernel continuity) + (R-dom) the post-rescale
dominations (from iterConvW_bound, t₁>0). std-3 all 5, raw 0. NOT a₁=R/6.
NEXT: J4-283 HeatOpWitnessContinuity (R-base + R-dom → Levi continuity concrete).

## J4-283 (2026-08-06, 29f53406) — HeatOpWitnessContinuity: (R-base) reduced + (R-dom) pointwise [AF]
The congruence reduction (identity + explicit-F continuity) + the deriv−laplaceBeltrami
parts decomposition + the COMPOSE into the ALL skeleton + the pointwise integrand
dominations. REMAINING: (R-base) = the ∂_τ/Δ-of-heatParametrix continuities on τ>0 +
the hIdent discharge (htransport on a gate ball); (R-dom) = the integral-envelope
construction. std-3 all 5, raw 0. NOT a₁=R/6.
NEXT: J4-284 ParametrixPartsContinuity ((i) ∂_τ + (ii) Δ + (iii) hIdent).

## J4-284 (2026-08-06, cfe6e01a) — ParametrixPartsContinuity: (i) proven; (ii)/(iii) reduced [AF]
The Gaussian + parametrix τ-derivative closed forms + joint continuity ((i) = the
hDcont slot DONE) + the laplaceBeltrami parts reduction ((ii) → hpd1/hpd2) + the gate
transfer ((iii) → the ungated identity) + the COMPOSE (carries only (ii)+(iii)).
⚠ FINDING: no standalone heatOp = parametrixResidualN lemma — buried in CoeffU1Fix
~853; extraction brick needed. std-3 all 7, raw 0. NOT a₁=R/6.
NEXT: J4-285 ParametrixSpatialPartials ((ii) partials + (iii) extraction).

## J4-285 (2026-08-06, 94c5dd59) — ParametrixSpatialPartials: (ii) discharged; (iii) plain [AF]
hpd1 (congruence onto the banked first-partial closed form) + the second-partial closed
form + hpd2 + the Δ-term assembly + heatOp_heatParametrix_eq_residual (DEFINITIONAL,
plain kernel) + heatOpWitness_jointContinuousOn_geometry ((i)+(ii)+(iii) internal;
carries only coefficient regularity + hgi/hChr). RESIDUAL: the gated-witness bridge
(cutoff × chart transport near 0) + the R-dom envelope. std-3 all 7, raw 0.
NOT a₁=R/6. NEXT: J4-286 GatedWitnessHeatOpBridge.

## J4-286 (2026-08-06, 58ac1b61) — GatedWitnessHeatOpBridge: the bridge; chart-composed [AF]
The witness on-gate = radialCutoff·heatParametrix at the CHART IMAGE (not plain). L1
def-collapse + L2a gate strip + L2b cutoff germ + the composed reduction + L3
(E's continuity ← hBcont). THE ONE OPEN INPUT: hBcont = heatOp of heatParametrix∘(W 0 ·)
joint continuity (parametrix jets ∘ the banked field-slot chart C²). std-3 all 5,
raw 0. NOT a₁=R/6. NEXT: J4-287 ChartComposedHeatOp (hBcont via the chain rule).

## J4-287 (2026-08-06, 0ee1c898) — ChartComposedHeatOp: ★★ hBcont DISCHARGED ★★ [AF]
The D1–D6 chain (the banked pd_comp/pd_pd_comp_local chain rules + the chart lift +
the Δ assembly) ⟹ chartComposedHeatOp_jointContinuousOn (= hBcont) +
heatOpGatedWitness_jointContinuousOn_final (E's continuity CONCRETE; carries = the
chart facts hWc2/hWc1cont/hWc2cont + coefficient/geometry/cutoff-germ, all
satisfiable). std-3 all, raw 0. NOT a₁=R/6.
NEXT: J4-288 ChartJetFactsDischarge (the chart facts + start the R-dom envelope).

## J4-288 (2026-08-06, 6fd52c79) — ChartJetFactsDischarge: the chart facts internal [AF]
The generic jet engines (second jets from C² only) + J1–J4 + J5
heatOpGatedWitness_jointContinuousOn_chartFree (carries all g-level: coefficient
regularity + hgi/hChr + gate data + cutoff germ, all satisfiable). std-3 all 7, raw 0.
NOT a₁=R/6. NEXT: J4-289 RDomEnvelope (the integral envelope → the Levi chain).

## J4-289 (2026-08-06, 0645a065) — RDomEnvelope: the dominator side DONE (E1–E3) [AF]
The Chapman–Kolmogorov identity (via the banked gaussDdim_conv_scaled) + the z-peak +
the (s,z)-free u-envelope M·u^{k−1} + its integrability. E4 (measurability) + E5 (the
engine instantiation: per-E bounds + the w-integrability bridge) = the wiring brick.
std-3 all 5, raw 0. NOT a₁=R/6. NEXT: J4-290 IterEEngineWiring.

## J4-290 (2026-08-06, 13fc8ecf) — IterEEngineWiring: W1–W4 DONE [AF]
The per-E bounds threaded + the w-measurability/integrability + the OUTER hbound at
the actual integrand (M·u^{k−1}) + the wired engines (∀k at the concrete E). NO slot
mismatches. Remaining per-level carries: (C-meas) parametric-Fubini u-measurability +
(C-cont) the inner-engine recursion; + the banked concrete providers. std-3 all 7,
raw 0. NOT a₁=R/6. NEXT: J4-291 InnerEngineRecursion (C-meas + C-cont).

## J4-291 (2026-08-06, 9c173d54) — InnerEngineRecursion: C-meas discharged; the map [AF]
The parametric-Fubini u-measurability from hEmeas alone (C-meas GONE) + the inner
engine soundly wired. THE MAP: the genuine walls = (S-dom) p-uniform dominator +
Gap-A (E at second-arg w; the base is the (·,·,0) slice) + Gap-B (iterE at first-arg
w off-ball; the IH is ball-anchored). std-3 all 5, raw 0. NOT a₁=R/6.

## ★ SOL CONSULT #7 (2026-08-06) — the Gap-A/B/S-dom ARCHITECTURE
KEY CORRECTIONS: (1) Gap-A localizes via the FIRST factor's finite-range support —
z∈B_R + gate range b ⟹ the active w-region ⊆ B_{R*}=B(0,R+b); off it E(·,z,w)≡0 for
all z∈B_R (needs the LOCAL zero: Wit ≡ 0 on an OPEN nbhd + heatOp locality, NOT
pointwise; ⚠ the boundary is NOT killable by null-sections under the current engine —
the CRITICAL repo check: is the cutoff's derivative-relevant support STRICTLY inside
the hard gate (closure cutoffSupport ⊆ gateInterior, a zero collar)? If yes NO
discontinuity anywhere and everything glues). (2) Gap-B: the "first factor kills far
w" claim is WRONG for iterE itself (near-diagonal gates propagate); the fix = the IH
QUANTIFIED OVER ALL (t₁,t₂,R) — P k := ∀ t₁ t₂ R, ContinuousOn (iterE k) (Icc ×ˢ
closedBall 0 R); instantiate at (ut₁,ut₂,R*) + compose (s,z)↦(su,w). The base case
globalizes via the zero collar (E(·,·,0) continuous on EVERY ball: banked small-ball
chain + local zero outside the support). (3) S-dom: constant × indicator of B_{R*}
(fixed u; constants may blow up in u — harmless, the outer envelope handles u) —
NOT the Gaussian-product optimization. (4) Gap-A near-region: generalize the J4-285/
287/288 chain to FROZEN base w (refactor the centre facts to ∀q; NO translation
covariance, NO joint-w regularity needed — per-w only; measurability stays with the
banked Fubini). ENDGAME PRE-EMPTS: uniform convergence on the EXACT compact + an
ENLARGED K' for the moving correction + Heine on K' + keep u∈(0,1) a.e. + the
measurability separate. RANKINGS recorded (fixed-base-w chain 1st for A; all-radii
IH 1st for B; indicator dominator 1st for S-dom).

## J4-292 (2026-08-06, cc79e433) — ZeroCollarLocalZero: ★★ THE COLLAR HOLDS ★★ [AF]
(A) the cutoff support strictly inside the gate (c = (b+ρc)/2 > b definitional; the
frontier vanishing was banked) — no re-choice. (B1/B2) local zero via heatOp locality
+ (C) the active-region bounds (R* = R + √(3/2)·b) + (D) the pasting skeleton + the
globalized base case (hEA/hoff carried — the radii/wiring reconciliation is the
residual). std-3 all 9+, raw 0. NOT a₁=R/6.
NEXT: J4-293 FrozenBaseWChain (Gap-A near region per SOL#7).

## J4-293 (2026-08-06, 6f63c6e6) — FrozenBaseWChain: ★★ Gap-A's chain COMPLETE ★★ [AF]
The census: only TWO base-0-specific facts, both re-proven parametric; W w w = 0 ⟹
co-centred at w. F1 (∀-base centre facts) + F3 (the re-centred chart-composed chain) +
F2 (the base-w on-gate reduction) + F4 (heatOpWitness_fixedBase_continuousOn at every
base w, near+off pasted). RESIDUAL: the chart-ball cover (per-w slices → the
origin-centred family). std-3 all 21, raw 0. NOT a₁=R/6.
NEXT: J4-294 GapACoverGapB (the cover + the all-radii IH + S-dom).

## J4-294 (2026-08-06, afc52579) — GapACoverGapB: the cover + the G2 reduction [AF]
The origin-ball Gap-A cover (near paste + far zero, all w) + the time-affine bridge +
iterE_jointContinuousOn_all(_concrete) reduced to ONE carry hcont (sub-walls: the ∀w
active bank, the Gap-B R*-IH localization, the S-dom dominator). std-3 all 5, raw 0.
NOT a₁=R/6. NEXT: J4-295 HcontAssembly (the strong induction + S-dom + the ∀w family).

## J4-295 (2026-08-06, 4e4b0094) — HcontAssembly: ★★ THE INDUCTION CLOSED ★★ [AF]
Index verdict: plain single-step induction. iterE_gapB_comp (Gap-B ← the IH) +
iterE_jointContinuousOn_strong (∀k; carries only hGapA + hSdom, both satisfiable via
the covers) + leviSlice_jointContinuousOn_of_strong (the M-test capstone = hf_cont's
shape). std-3 all 3, raw 0. NOT a₁=R/6.
NEXT: J4-296 GapASdomInstantiation (hGapA/hSdom concrete ⟹ the Levi continuity done).

## J4-296 (2026-08-06, 366c5e36) — GapASdomInstantiation: ★★ Gap-A DISCHARGED ★★ [AF]
THE K-GATE ROUTE: w∈K (near, the frozen bank + the bridge) / w∉K (E ≡ 0 — the base
gate) partitions ALL w; hGapA proved ∀w; the lower near-isometry bound MOOT. The
concrete Levi continuity now carries TWO: hnear (the frozen-bank uniformity) + hSdom
(the indicator dominator, documented build). std-3 all 4, raw 0. NOT a₁=R/6.
NEXT: J4-297 SdomHnearDischarge (the last two carries → hf_cont DONE).

## J4-297 (2026-08-06, 4630d528) — SdomHnearDischarge: ★★ hSdom DISCHARGED + C1 ★★ [AF]
hSdom_concrete (constructive: the K-gate zero localizes to 𝟙_K; the banked bounds
peaked ⟹ M(u)) + hnear_concrete (the Hgeo bundle = the surviving carry; the
chart-domain verdict: hWwcont only used off-active where the collar provides it) +
leviSlice_jointContinuousOn_DONE (FINAL INPUTS: the banked four + hnear(Hgeo) + the
envelope). std-3 all 3, raw 0. NOT a₁=R/6.
NEXT: J4-298 HgeoDischarge (the bundle from the collar geometry → hf_cont DONE).

## J4-298 (2026-08-06, a49cee35) — HgeoDischarge: ★★ hnear via the TWO-COVER ★★ [AF]
⚠ HONESTY CATCH: the J4-297 Hgeo shape was UNSATISFIABLE for far w (the chart is
garbage off ball w ρc) — superseded, not forced. The two-cover fix: V ⊇ closure(S w)
replaces the impossible origin-U; off-gate via the hard-gate zero (no chart); the
collar via the far lemma. hnear_twoCover (the satisfiable H2 bundle) +
leviSlice_jointContinuousOn_FINAL (the banked four + H2 + the envelope). std-3 all 4,
raw 0. NOT a₁=R/6. NEXT: J4-299 H2Instantiation (the fields ∀w∈K → hf_cont DONE).

## J4-299 (2026-08-06, 41a5c174) — H2Instantiation: H2 → I1 + I2 [AF]
The ∃V half discharged (V := ball w ρc via F1); H2_concrete + leviSlice_
jointContinuousOn_CONCRETE (the banked four + hgeo(I1) + hactive(I2) + envelope).
I1 = the gate-into-chart-ball containment (no banked φ-displacement bound; shrink the
gate) · I2 = the transition-annulus continuity (the plateau-only F4 doesn't cover
where the cutoff varies; the product-rule extension of the D-chain). std-3 all 3,
raw 0. NOT a₁=R/6. NEXT: J4-300 TransitionAnnulusCont (I2 + I1).

## J4-300 (2026-08-06, c3ba2080) — TransitionAnnulusCont: T1+T2 banked; T3 deferred [AF]
The Leibniz heatOp(c·B) expansion + the parametrix t-differentiability + the VALUE
joint continuity (new) + the fixed-field Δ_g continuity. T3 (the full-gate assembly ⟹
I2) typechecked once but cut for a ~20-min elaboration blowup — the recipe documented;
the re-land = aggressive top-level splitting. std-3 all 4, raw 0. NOT a₁=R/6.
NEXT: J4-301 FullGateAssembly (the split T3 re-land → I2 → hf_cont mod I1).

## J4-301 (2026-08-06, 835583ea) — FullGateAssembly: ★ the generic T3 core ★ [AF]
The split factor library (A1a–f) + the formula continuity (A3) + A4 (the generic
transition-annulus core — plateau+annulus in one; builds ≤ ~1m17s). A5 (the concrete
capstone) typechecks but ~52min elaboration (the .congr defeq vs .choose-heavy terms);
THE FIX mapped: Vmap-abstract A4 + the one-time syntactic reduction. std-3 all 9,
raw 0. NOT a₁=R/6. NEXT: J4-302 FastA5Fix (the abstract restatement → the capstone).

## J4-302 (2026-08-06, bcec49e6) — FastA5Fix: ★★ the concrete capstone in 55s ★★ [AF]
The scalar-defeq isolation (heatOp_globalCutoff_eq_A4kernel_at, outside ContinuousOn)
+ two syntactic .congr steps ⟹ heatOpWitness_fixedBase_fullGate(_chartFree): E(·,·,w)
continuous on the FULL gate (plateau+annulus), 57× faster. RESIDUAL: F5e/A6 (the
hactive wiring) + the origin-vs-w reconciliation. std-3 all 4, raw 0. NOT a₁=R/6.
NEXT: J4-303 HactiveWiring (→ hf_cont mod I1).

## J4-303 (2026-08-06, f0e4e9ef) — HactiveWiring: hactive's analytic half discharged [AF]
The W1 interior extraction + hactive_of_fullGate + hactive_concrete (the ContinuousOn
derived from the banked capstone) + leviSlice_hf_cont (the Levi 0-slice continuity;
inputs = the banked four + the envelope + hgeo (I1) + hfg (the full-gate + the PURE
GEOMETRIC collar)). The two residuals are pure gate-geometry. std-3 all 5, raw 0.
NOT a₁=R/6. NEXT: J4-304 GateGeometryResiduals (I1 + the collar → hf_cont FINAL).

## J4-304 (2026-08-06, be059a50) — GateGeometryResiduals: ★★ hf_cont CLOSED ★★ [AF]
I1 (the image/displacement route + honest radii) + the collar (the contrapositive via
the left-inverse germ) + leviSlice_hf_cont_FINAL: the Levi 0-slice continuity from
the banked four + the envelope + the per-w bundles (all banked exports + satisfiable
radii). std-3 all 3, raw 0. NOT a₁=R/6.
NEXT: J4-305 BoundaryLimAssembly (Heine + hMovingCorr ⟹ hBoundaryLim ASSEMBLED).

## J4-305 (2026-08-06, f8abc8cf) — BoundaryLimAssembly: hf_cont internal; B1 landed [AF]
heine_timeShift_sup_tendsto (the eventual-uniform Heine sup) + the frozen-slice
hf_cont discharge + hBoundaryLim_ASSEMBLED (hf_cont internal via the FINAL bundle).
RESIDUAL: the hMovingCorr integral recombination (mass × sup + tails + split) + the
hf_meas/hf_bdd feeds. std-3 all 3, raw 0. NOT a₁=R/6.
NEXT: J4-306 MovingCorrRecombination (B2 → hBoundaryLim fully internal).

## J4-306 (2026-08-06, 54dc0f0d) — MovingCorrRecombination: ★★ hBoundaryLim FULLY INTERNAL ★★ [AF]
The m-uniform sequence tails + the on-ball mass×sup + the 3ε assembly (kernel-agnostic)
+ hBoundaryLim_FULLY_INTERNAL (hMovingCorr GONE — proven from B1 + the mass + the
tails; hf_cont internal). The two new satisfiable carries: the window-uniform global
Levi bound (provider named) + the moving-slice measurability (provider named). std-3
all 4, raw 0. NOT a₁=R/6. NEXT: J4-307 EnvelopeWiringLocUnif (the carriers wired +
the loc-unif start).

## J4-307 (2026-08-06, 80d7944b) — EnvelopeWiringLocUnif: ★★★ hBoundaryLim DONE ★★★ [AF]
The window-uniform Levi bound + the moving-slice measurability + the t-UNIFORM Heine
sup (the loc-unif key) + hBoundaryLim_DONE (the two envelope carries collapsed into
ONE banked LeviSeriesLocalData package + a satisfiable floor; NO opaque carry).
std-3 all 4, raw 0. NOT a₁=R/6. NEXT: J4-308 LocUnifDerivConv (→ hDerivConv →
the hDuhamel export).

## J4-308 (2026-08-06, 7629a413) — LocUnifDerivConv: the slot recon + L1/L3 [AF]
The hbdryLU slot named (TendstoLocallyUniformlyOn of BoundaryTrunc → F u 0 0 on U) +
movingCorr_tUniform (the t-uniform 3ε) + hbdryLU_of_movingCorr_frozen (the W1-free
composition). L2 = the residual wall: the t-uniform FROZEN limit (the AI moduli
uniform in u; only f_u's modulus is u-dependent — the t-uniform Heine supplies it).
std-3 both, raw 0. NOT a₁=R/6. NEXT: J4-309 TUniformFrozenAI (L2 → hbdryLU → hDerivConv).

## J4-309 (2026-08-06, 2f1bc07f) — TUniformFrozenAI: ★★ L2 CLOSED ★★ [AF]
The f≡1 mass-one trick (T1, the sole AI reuse) + the Heine u-uniform modulus (T2) +
the 3-piece t-uniform split (T3) + the loc-unif form (T4) + the exact hbdryLUTarget
composition (T5; sole carry = the mechanical hmovLU promotion). FLAG: the
untruncated-gate W1 aspect to examine at the hDerivConv composition. std-3 all 5,
raw 0. NOT a₁=R/6. NEXT: J4-310 HDerivConvComposition.

## J4-310 (2026-08-06, 93255114) — HDerivConvComposition: ★★ THE FIXED-GATE hDerivConv IS W1-FREE ★★ [AF]
hmovLU_concrete (H1, the movingCorr_tUniform loc-unif promotion — no abstract carry)
+ hbdryLU_CONCRETE (H2, the exact hbdryLUTarget from the satisfiable frozen+moving
lists — NO hAnear) + hDerivConv_conditional (H3, derivConv_of_data steps (b)+(c)
replicated with OUR W1-free hbdryLU; carries = the F2 regularity pile + hFII tails +
hDaLimLU) + truncatedDuhamelCore_conditional (H4, the pile composed; the hDaLim-vs-
hDaLimLU bridge = .tendsto_at). THE VERDICT: W1 (hAnear) survives ONLY in the OLD
provider-∃ export path (core_of_v2prime_data_FULL); the fixed-gate chain is clean —
open surface = the F2 pile + the hDaLimLU DATA census, none of it W1. std-3 all 4,
raw 0. NOT a₁=R/6. NEXT: J4-311 the provider-∃ export re-thread through the new Core
(gate-identity check → hDuhamel internal → wide_a1_R6_interface_discharged_v3).

## J4-311 (2026-08-06, 3b2d4a2e) — HDuhamelExportRethread: ★★ THE CAPSTONE hDuhamel SLOT IS A THEOREM ★★ [AF]
X0 GATE-IDENTITY VERDICT: IDENTICAL — the wide capstone's provider-chosen S IS the one
concrete van-Vleck gate (gatedWitnessN1_package_open), the same (S,a,b)/witness the
whole J4-266→310 boundary chain is parameterized by; the J4-265 pattern applies with
no gate mismatch. hDerivConv_AT_GATE (the W1-free composition at the gate) +
truncatedDuhamelCore_AT_GATE (robust) + truncatedDuhamelCore_AT_GATE_FULL (the honest
union census: RNC gauge, MemLapFull, interval-integrabilities, sliver, Gaussian
dominations, MemECombine, the W2 family, F2 pile, hFII, frozen/moving lists, the
single W1-free hBoundaryLim) + hDuhamelSlot_AT_GATE (the EXACT hDuhamel antecedent of
wide_a1_R6_interface_discharged_v2, PROVEN — hDuhamel_of_truncatedData projection).
X3 (the v3 restatement) deferred by design (the ~130-binder kernel-freeze rule); the
per-S fact a v3 would ∃-intro is fully in hand. Surviving capstone arrows: hDConv →
hCConv. NO hAnear anywhere. std-3 all 4, raw 0. NOT a₁=R/6. NEXT: J4-312
HDConvGateThreading (hDConv_from_banked at the same gate → hDConvSlot_AT_GATE).

## J4-312 (2026-08-06, 98a72317) — HDConvGateThreading: ★★ THE CAPSTONE hDConv SLOT IS A THEOREM ★★ [AF]
KEY FINDING: HDConvThreading.hDConv_from_banked is W1-POISONED (route via
hDelta_gatedWitnessN1_final → the hAnear boundary provider) — not honestly usable at
the provider gate. The fix: hDConv_W1free (the DifferentiableAt analog of J4-310's
hDerivConv_conditional — same hDerivLU := tendstoLocallyUniformlyOn_add hDaLimLU
hbdryLU, closed by hDConv_of_deltaFamily) + hDConv_AT_GATE (hDaLimLU/hbdryLU internal
from the banked concretes; census = the FULL union MINUS hBoundaryLim) +
hDConvSlot_AT_GATE (the VERBATIM capstone hDConv antecedent — the slot IS the
DifferentiableAt). NO hAnear. ★ BOTH hDuhamel (J4-311) AND hDConv slots are now
theorems at the concrete gate; the surviving inner capstone arrow = hCConv → ⟨a₁
2-jet⟩. std-3 all 3, raw 0. NOT a₁=R/6. NEXT: J4-313 CConvFacadeGate (the hCConv
five-bundle recon + discharge at the gate → hCConvSlot_AT_GATE).

## J4-313 (2026-08-06, dbe25b5c) — CConvFacadeGate: ★★★ ALL THREE INNER CAPSTONE ARROWS ARE THEOREMS ★★★ [AF]
The hCConv slot = the spatial-C² ContDiffAt of the diagonal heatConv; unfolds via the
banked CConvConcreteThreading.hCConv_concrete_from_data into the FIVE CConvFacade
bundles (B1 metric, B2 chart/gate measurability, B3 source, B4 derivative + explicit
D, B5 envelope) + the hD1 L2 carry. POISONING AUDIT: the C² route is structurally
DISJOINT from the W1/hAnear boundary machinery — NOT W1-poisoned. B1 discharged at
the gate from raw geometry the capstone already carries; hCConvSlot_AT_GATE = the
VERBATIM capstone hCConv antecedent, proven from the honest satisfiable census
(B2–B5 + hD1). With J4-311 (hDuhamel) + J4-312 (hDConv), all three inner arrows now
have AT_GATE slot theorems. REMAINING SURFACE: S1 ∀-gate (tripleHEmeas) · the census
piles (hDaLimLU data, F2, hFII, frozen/moving, B2–B5+hD1) · base geometry + 1≤n ·
the heavy X3 v3-export (the residual provider re-exporting the per-S censuses) · the
final a1_R6_of_geometry assembly. std-3, raw 0. NOT a₁=R/6. NEXT: J4-314
S1TripleHEmeasGate (the S1 ∀-gate recon + discharge).

## J4-314 (2026-08-06, 214c3523) — S1TripleHEmeasGate: ★ THE S1 ∀-GATE RESOLVED (interface artefact CAUGHT) ★ [AF]
tripleHEmeas = a SINGLE joint StronglyMeasurable over (τ,p,q) of heatOp at the
witness. ⚠ STRUCTURAL VERDICT (per feedback_axiom_budget_blind_spot): the capstone's
literal `∀ S a b, tripleHEmeas` antecedent is UNSATISFIABLE — a non-measurable
gate-function falsifies the gatedKernel indicator; an over-general interface artefact
(the provider applies hEmeas at exactly ONE self-chosen gate: the uniformFlowExp
flow-ball with q-varying radius cf q). Banked honest content: tripleHEmeas_flowball_
geometry (∃δ₀, S1 at every constant-radius flow-ball gate in (b,δ₀) — geometry-only
satisfiability witness) + tripleHEmeas_at_measurable_gate (S1 at ANY gate with the
honest hKSmeas + satisfiable field-derivative carriers). Poisoning audit: none.
Shedding the outer hEmeas carry = the constant→varying-radius (cf q) extension + a
strengthened provider internalizing S1. std-3 both, raw 0. NOT a₁=R/6. NEXT: J4-315
VaryingRadiusS1Provider (is the varying gate-set OPEN? → hKSmeas free → carriers →
tripleHEmeas at the provider's exact gate → the strengthened provider).

## J4-315 (2026-08-06, 3c440af9) — VaryingRadiusS1Provider: S1 AT THE VARYING GATE mod Measurable cf [AF]
V0: the provider's cf hides the CONSTANT (b+ρc)/2 behind an opaque Classical.choose;
Route A (joint openness) dead (per-fibre only; K compact). hKSmeas_varying = the
banked constant-radius Lusin–Souslin engine extended to the graph-of-radius domain
D = {(q,v) | q∈K ∧ ‖v‖ < cf q} — joint gate-set measurability at varying radius
REDUCED EXACTLY to Measurable cf (+ reach bound δ₀). tripleHEmeas_at_varying_
flowball_gate = S1 at the provider's exact gate shape, conditional on Measurable cf
+ the three satisfiable base-field carriers. SINGLE NAMED RESIDUE: Measurable cf —
dissolvable by a new provider export exposing the constant radius (no .choose).
std-3 both, raw 0. NOT a₁=R/6. NEXT: J4-316 ConstRadiusGateExport (the constant-
radius package re-export → cf ≡ const measurable → S1 at THE gate).

## J4-316 (2026-08-06, 0ceaea33) — ConstRadiusGateExport: ★★ S1 CONTENT COMPLETE (Measurable cf DISSOLVED) ★★ [AF]
The hgood 7-conjunct bundle in _lin_pkg_open is uniform at the constant c=(b+ρc)/2 —
the .choose never carried per-q content. The full gate package re-exported with the
LITERAL constant gate (…_of_good_CONST + …_le_lin_CONST + gatedWitnessN1_package_
open_CONSTRADIUS) + tripleHEmeas_AT_CONSTRADIUS_GATE (geometry-only; Measurable cf ⟹
measurable_const; c<δ₀ chart-vs-jet reach = honest carried antecedent) +
constRadius_package_and_S1 (the bundled fact for the v3-export). THE S1 STORY
(J4-314→316): unsatisfiable-∀S artefact caught → reduced to Measurable cf → dissolved
at the constant gate. Deleting hEmeas from the capstone = the deliberate v3-export
provider refactor. std-3 all 5, raw 0. NOT a₁=R/6. NEXT: J4-317 OuterCarryRecon (the
COMPLETE classified capstone-antecedent census + discharge of derivable base-geometry
carries via the banked recenter/RNC machinery).

## J4-317 (2026-08-06, bcac67db) — OuterCarryRecon: ★★★ THE DEFINITIVE REMAINING-SURFACE MAP ★★★ [AF]
T0 census of EVERY wide_a1_R6_interface_discharged_v2 antecedent: (i) the three inner
arrows each have banked GATE slots (hDuhamelSlot/hDConvSlot/hCConvSlot, J4-311/312/
313); (ii) S1/hEmeas content complete (J4-316); (iii) the analytic residue (hInter/
hInt/hEbound/hEzero/hS0/hSopen/hCH) is ALL ALREADY INTERNAL in v2 — migrated into
the slot piles; (iv) 4 normalization carries DERIVED (hg0_of_hframeK, hGamma_of_hdg0,
hgi_of_hg0_hinvF/hgi_of_geometry, hgnd_of_hgpos); genuine carries = smoothness/
positivity/symmetry/window data + htr (★ the Ricci-source physics coefficient).
T2 ENDGAME MAP (dependency order):
  R0 — retire the ∀S hEmeas via constRadius_package_and_S1 (interface rethread).
  R1 — compose the three gate slots into v2 (composition, no new math).
  R2 — the slot data piles at the concrete gate (the GENUINE analytic walls):
       hDuhamel's hDaLimLU census (F2/hFII/hBoundaryLim_DONE banked), hDConv's
       diff-under-∫ family, hCConv's 4 facade bundles + hD1.
  R3 — derive htr (RNC 2-jet ⟹ −(2/3)Ric; the K4/van-Vleck 2-jet bank should feed).
std-3 all 5, raw 0. NOT a₁=R/6. NEXT: J4-318 RicciSourceCoeff (R3 recon + derivation).

## J4-318 (2026-08-06, 48fed9db) — RicciSourceCoeff: ★ THE htr ALGEBRA CLOSED (R3 → (†)) ★ [AF]
htr (ProviderSideExports:177) = ∀ c d, ∑_a ∂_c∂_d g_{aa}(0) = -(2/3) Ric c d; the
-(2/3) IS the trace of the classical -(1/3) NC 2-jet (†) ∂_c∂_d g_{ab}(0) =
-(1/3)(R_{acbd}+R_{adbc}). ric_of_lowered + lowered_diag_swap + jet_trace_sum +
ricci_diag_contract ⟹ htr_of_geometry (the capstone binder VERBATIM from hjet=(†) +
hRic + hpair); htr_hypotheses_satisfiable (flat witness, no vacuity);
pd_christoffel_at_zero + riemann_at_zero (the honest bridge to the REAL riemann g gi:
ΓΓ dies at 0, Schwarz cancels). SOLE R3 RESIDUE: (†) the four-index NC 2-jet — the
van-Vleck bank is directional-only (Ric(v,v), 3e36639c). R2 untouched. std-3 all 8,
raw 0. NOT a₁=R/6. NEXT: J4-319 FacadeBundleFields (R2 easiest tranche: the hCConv
B2–B5 per-field census + discharges; the CONSTRADIUS gate may simplify B2).

## J4-319 (2026-08-06, c103f5b5) — FacadeBundleFields: THE hCConv FIELD CENSUS + 5 DISCHARGES [AF]
P0 (corrected — DataPileWitnessAudit Family 7 stale): 18 fields + hD1 = 2 ND + 7 DH
(banked builders: reachableGate_concrete, hKmeas_concrete_v7, leviSource_*_aesm +
LeviSeriesLocalData, hDmeas_discharged, hC2fam_concrete_final, hD1_from_data) +
9 GENUINE WALLS in two clusters: (i) B2 chart-inverse OFF-IMAGE measurability ×4
(hSmeasSet/hVmapMeas/hChartB/hSliceData — flowInverse_jointMeasurable_regional
agrees only on-image) + (ii) B5 on-gate Gaussian dichotomy ×2 (hGateData/hGateData'
= W4), plus hFbd, hlin, hDrep. ⚠ CONSTRADIUS does NOT simplify B2 (off-image walls,
radius-orthogonal). P1: hKmeasSet_field, hCover_field, hFjoint_field + hFmeas_field
(the leviSource engines at the gate's residual kernel verbatim), hcoef_field.
std-3 all 5, raw 0. NOT a₁=R/6. NEXT: gpt-5.6-sol consult on the two wall clusters,
then J4-320 on the Sol-informed easiest wall.

## J4-320 (2026-08-06, a6b8da97) — B2MeasurabilityDissolution: ★ 3 OF 4 B2 WALLS DOWN ★ [AF]
Sol-guided (consult recorded here). Wall 1 hSmeasSet FELL K-restricted (the banked
Lusin–Souslin graph sectioned; raw no-K = honest residue). Walls 2/3 hVmapMeas/
hChartB DISSOLVED at the piecewise chart Wg := if (z,p)∈Γ then G else 0 —
measurability + on-gate C² transfer + satisfiability all proven; ⚠ CConvChartGateData
HARDWIRES uniformInverseChart ⟹ consuming Wg needs a chart-parametric facade
VARIANT (vanVleckGatedWitness unaffected). Wall 4 partial (frontier-collar leg a).
FULL SOL VERDICTS: hFbd LIKELY FALSE AS STATED (s^{-n/2} singular at (0,0); honest
fix = L¹/time-integrable facade variant — the ∀S-artefact pattern again); hlin/hDrep
= joint with the hDConv diff-under-∫ tranche (hasFDerivAt_integral_of_dominated,
affine line map, w-neighborhood domination, no facade cycle); hGateData ×2 = ONE
shared quantitative Gaussian-jet theorem (α chart jets on compact + β scalar Gaussian
absorption lemmas + γ product assembly; ⚠ s-power bookkeeping — 1st deriv costs
s^{-1/2}, 2nd costs s^{-1}). std-3 all 10, raw 0. NOT a₁=R/6. NEXT: J4-321
ChartParamFacadeVariant (the chart-parametric bundle + Wg instantiation +
hCConvSlot_AT_GATE_v2 with the B2 measurability internal).

## J4-321 (2026-08-06, 79e4e336) — ChartParamFacadeVariant: WALLS 2/3 INTERNAL AT Wg [AF]
N0 CORRECTED VERDICT: the witness ITSELF contains uniformInverseChart (via
globalCutoffParametrixWitnessN) and the slice-interface machinery
(hjoint_instantiated/HenvUInstantiation/WitnessDerivMeasurability) hardwires the
chart in statements AND proofs — the consumer is NOT chart-opaque.
CConvChartGateDataW (chart-parametric: 4 chart fields opaque W', 3 chart-free
verbatim) + chartGateDataW_of_Wg (walls 2/3 hVmapMeas/hChartB DISCHARGED INTERNALLY
from MeasurableSet Γ + Measurable G). N2/N3 blocked on the named residue: the
chart-parametric re-derivation of hjoint/henv/g2 (sound, heavy, deferred).
Remaining hCConv surface: hSmeasSet(raw)/hSliceData carries · hFbd (likely-false-as-
stated, L¹ fix) · hlin/hDrep (joint w/ hDConv) · hGateData ×2 (Gaussian-jet) · the
N0 re-thread residue. std-3, raw 0. NOT a₁=R/6. NEXT: J4-322 GaussianJetTheorem
(Sol's α/β/γ; SATISFIABILITY VERDICT FIRST — the s-power bookkeeping).

## J4-322 (2026-08-06, 79b755eb) — GaussianJetTheorem: ★★ hGateData ×2 ADJUDICATED FALSE-AS-STATED ★★ [AF]
THE THIRD FACADE ARTEFACT (after the capstone ∀S and hFbd-likely-false): the B5
on-gate conjunct bounds the log-gradient |∑Wₖ·Pvalₖ/(2(t−s))| by a CONSTANT Bs; the
numerator is s-independent and generically nonzero ⟹ blow-up as s→t⁻ on a positive-
measure interval (∀ᵐ cannot escape); s-power 0 demanded where −1/2 is forced.
PROVEN: gateData_numerator_shape_unsat (satisfiable antecedents — the impossibility
as a Lean theorem, parallel to HgateSatAudit.gate_Sconj_impossible). Brick β BANKED
regardless: gaussian_beats_linear (β1, explicit s^{−1/2}) + gaussian_beats_quadratic
(β2, s⁻¹) + the mul_exp_neg auxiliaries. THE CORRECTED VARIANT (⋆): the
(t−s)^{−1/2}-weighted VALUE-LEVEL domination — s-integrable, sufficient downstream,
scalar core = β1; Ba/Bd conjuncts survive, only Bs is poisoned. std-3 all 7, raw 0.
NOT a₁=R/6. NEXT: Sol consult on the corrected-facade-v2 design (the (⋆) envelope +
L¹ hFbd + the chart-parametric re-thread — one consolidated v2 chain?), then J4-323.

## SOL CONSULT #9 (2026-08-06, post-J4-322) — THE FACADE-v2 DESIGN (14 bricks)
Decisions: (1) surgery = (c)-as-contract: DELETE hGateData/hGateData' (do NOT weaken
the naked quotient — |N/2(t−s)| ≤ Bs(t−s)^{-1/2} is STILL false; the Gaussian must
participate); the new B5 contract = hStar: ∃C≥0,∀x∈u,∀i,∀s∈Ioc 0 t,∀z,
|witnessFieldDeriv| ≤ C·(t−s)^{-1/2}·gaussDdim(2(t−s))z (pointwise uniform — kills
the ∀ᶠ/∀ᵐ reorder duplication); concrete proof via a separate bridge theorem.
(2) hFbd fix = hFpair: IntegrableOn (fun s => (t−s)^{-1/2}·∫ gaussDdim(2(t−s))z·|F s z|)
(Ioc 0 t) — derived from |F s z| ≤ CF·s^γ·G_{cF·s}(z) with γ>−1 (Levi conservative
γ=−1/2; Beta(1/2,1/2) endpoint; iterates improve m(γ₀+1)−1 but the series keeps γ₀).
(3) chart re-thread MERGED into the v2 campaign via a SliceChartData package
(instantiate at uniformInverseChart AND Wg) — separate generic modules, not one
monolith, and NOT patch-after-duplicate. (4) hlin from the BANKED hDConv loc-unif
machinery (hDerivConv_conditional/hDConv_W1free specialized to update x i w) — NO
second dominated-differentiation development; hDrep by definition of D + algebra.
THE 14 BRICKS: 1 Contracts (V2 structures) · 2 GaussianPairing (sourcePair_of_
gaussian_bound, β-integral) · 3 ChartJoint (chart-parametric hjoint copies) · 4
ChartSlices · 5 EnvelopeFromStar (hdomS/henv_v2 NEW from hStar+hFpair) · 6 α₁
ChartComparisonLocal (exp/log identities, no heat asymptotics) · 7 α₂ Uniform
(c·r² ≤ r_x² ≤ C·r² + the log-derivative bound) · 8 WitnessProductRule (at Wg) · 9
WitnessStarConcrete ((⋆) proven: α₂ + β1; β2 NOT here) · 10 LeviSource (γ=−1/2
adapter) · 11 WgInstantiation (the deferred chart residue discharged) · 12
HDerivConv (hlin from banked) · 13 DRepresentation (D def + hDrep + hD1 via sliver;
β2 if needed) · 14 Facade (hCConvSlot_AT_GATE_v2).

## J4-323 (2026-08-06, 746b1ad7) — FACADE-v2 BRICKS 1+2 [AF]
Brick 1 CConvV2Contracts: CConvSourceDataV2 (+hFpair, −hFbd) + CConvWitnessEnvelope-
DataV2 (+hStar, −hGateData ×2) + SliceChartData (chart-parametric survivor package)
+ satisfiability guards. Brick 2 CConvV2GaussianPairing: P1–P5 ALL —
gaussDdim_pairing_integral (one step from the banked gaussDdim_conv!) +
betaPow_integrableOn (γ>−1 split Beta) + sourcePair_of_gaussian_bound (the full
hFpair adapter; sole carry = satisfiable hgMeas). std-3 all, raw 0. NOT a₁=R/6.
NEXT: J4-324 = v2 bricks 5 (EnvelopeFromStar: hdomS/henv_v2 from hStar+hFpair) + 10
(LeviSource: the γ=−1/2 adapter from the banked domination).

## J4-324 (2026-08-06, e2282d90) — FACADE-v2 BRICKS 5+10 [AF]
Brick 5 EnvelopeFromStar: the poisoned constant-dominator replaced by the TRUE
C·(t−s)^{-1/2}·gaussDdim·|F| envelope — pointwise_dom_v2 + envelope_integrable_v2 +
hdomS_v2/henv_v2 (both old filter orders trivial from the pointwise-uniform hStar) +
zslice_integrable_v2. Brick 10 LeviSource: ★ the banked Levi domination has γ=0 (NO
s-singularity — leviSeries_dominatedW_le + baseKernelW_zero_apply = gaussDdim(2τ));
sourceDataV2_concrete = CConvSourceDataV2 for the concrete gate source (carries:
LeviSeriesLocalData + hFsum + hgMeas). v2 DONE: 1,2,5,10 of 14. std-3 all 8, raw 0.
NOT a₁=R/6. NEXT: J4-325 = bricks 6+7 (ChartComparison α₁/α₂ — the two-sided radial
comparison + Jacobian bound feeding brick 9's (⋆) proof).

## J4-325 (2026-08-07, 516a14d1) — FACADE-v2 BRICKS 6+7: ChartComparison α₁/α₂ [AF]
C0: the ½-radial conjunct banked at the centre (chartW0 nearIsometry); the general-x
coercivity = the honest carry (= hmin of witnessFieldDeriv_gate_envelope_coercive);
HgateSatAudit's poison was Bs, never the radial. C1 α₁ re-exports; C2 the two-sided
centre comparison; C3 the compact upper + the Cauchy–Schwarz/Jacobian chain; C4 ★
THE TRANSFER PROVED: √r²_W·τ⁻¹·gaussDdim τ (W z x) ≤ √2·2ⁿ·τ^{-1/2}·gaussDdim(4τ) z
(β1 at the banked c₀=½). Brick-9 inputs named: general-x coercivity, Jacobian L, the
width bookkeeping (4τ vs hStar's 2τ — the wide-variant route). v2 DONE 1,2,5,6,7,10
of 14. std-3 all 13, raw 0. NOT a₁=R/6. NEXT: J4-326 = bricks 8+9 (WitnessStar — the
(⋆) analytic heart, the wide-variant decision).

## J4-326 (2026-08-07, 7fe0ccf2) — FACADE-v2 BRICKS 8+9: ★★★ THE (⋆) HEART IS PROVEN ★★★ [AF]
The bank already had the on-gate product rule (witnessFieldDeriv_gate_eq) — brick 8
a re-export; only the constant-Bs packaging was poisoned. THE WIDTH: the wide
4(t−s) route (c₀=½ banked; c₀=1 unobtainable); the contract stays at 2(t−s), the
concrete witness satisfies the WIDE form. witnessFieldDeriv_starWide_onGate: |wfd| ≤
(½√n·L·√2·2ⁿ·Ba + 2ⁿ·Bd·√t)·τ^{-1/2}·gaussDdim(4τ)z — s-UNIFORM constant; assembly
= product rule + Cauchy–Schwarz + β1 transfer + ampWiden4. hStarWide_concrete (∃C on
Ioo 0 t; off-gate zero; carries hgate + hdata, satisfiable) + the S4 wide legs
(hFpairWide, envelope/pointwise/hdomS Wide, the width-generic pairing). v2 DONE
1,2,5,6,7,8,9,10 of 14. std-3 all 11, raw 0. NOT a₁=R/6. NEXT: J4-327 = bricks 3+4
(the chart-parametric slice-interface copies at SliceChartData).

## J4-327 (2026-08-07, 2d231e47) — FACADE-v2 BRICKS 3+4: ChartInterface [AF]
T0: hjoint's internals copy-with-edits at the opaque chart (only hWjoint consumed);
WitnessDerivMeasurability ALREADY chart-opaque; the dead old-plumbing skipped;
henv_v2Wide = the missing ∀ᵐs→∀ᶠx wide order. gatedWitnessW (Vmap-parametric) + the
rfl bridge + the T1 three-leg interface (sliceInterfaceW_of_data). FINDING: the full
hjoint_fully_geometric capstone also consumes the chart-intrinsic hVmapMeas/hCover —
routed through Wg in brick 11 (banked wg_* theorems). v2 DONE 1–10 of 14; REMAIN
11,12,13,14. std-3 all 11, raw 0. NOT a₁=R/6. NEXT: J4-328 = brick 11
(WgInstantiation: SliceChartData at Wg + the witness-equality bridge + the concrete
three legs with the chart walls INTERNAL).

## J4-328 (2026-08-07, 25991695) — FACADE-v2 BRICK 11: THE Wg BRIDGE IS CLEAN [AF]
U2: globalCutoffParametrixWitnessN evaluates Vmap ONLY at the same on-gate (q,p) —
no collar. wg_agree_onGate + gatedWitnessW_Wg_eq_vanVleckGatedWitness (the function-
level bridge) + the satisfiability certificate + sliceChartData_at_Wg (hWjoint
INTERNAL) + sliceInterface_CONCRETE (the three legs for the concrete witness — the
chart-intrinsic hVmapMeas/hChartB walls INTERNAL) + wg_hCover_leg. THE J4-321
CHART-HARDWIRING RESIDUE IS DISCHARGED. v2 DONE 1–11 of 14. std-3 all 6, raw 0.
NOT a₁=R/6. NEXT: J4-329 = bricks 12+13 (hlin from the banked hDConv machinery via
the affine line map; D + hDrep by definition; hD1 via the banked sliver adapters).

## J4-329 (2026-08-07, 7137acb5) — FACADE-v2 BRICKS 12+13: hlin / D / hDrep / hD1 [AF]
ROUTE VERDICT: the banked hDConv machinery = TIME variable (wrong for hlin); the
SPATIAL linewise diff-under-∫ was ALREADY BANKED (hConvDeriv_linewise) — brick 12 a
re-export. Dmap (the CLM representative) + hDrep_of_def (rfl) + hlin_as_D (the
verbatim field) + hD1_conditional (the named per-coordinate sliver census →
hD1_from_data + the CLM lift). v2 DONE 1–13 of 14. std-3 all, raw 0. NOT a₁=R/6.
NEXT: J4-330 = brick 14 THE FACADE (hCConvSlot_AT_GATE_v2 from the v2 census only).

## J4-330 (2026-08-07, 81581da9) — ★★★ THE 14-BRICK FACADE-v2 CHAIN IS COMPLETE ★★★ [AF]
hCConvSlot_AT_GATE_v2 = the EXACT capstone hCConv antecedent from the v2 census
ONLY, via the unchanged SpatialC2.hCConv_reduction at D := Dmap. KEY RESOLUTION:
hcont derived from hD1's C¹ (gcoef i x = (D x)(single i 1)) — the poisoned
g2_bundle chain bypassed entirely; the old linewise→Fréchet bridge reused.
v1→v2: hGateData ×2 + hFbd DEAD; hAnear absent from the cone. SURVIVING CENSUS:
(a) the open field nbhd; (b) the hlin linewise family (diff-under-∫ carries
dischargeable from hStarWide_concrete/hFpairWide/envelope_integrable_v2Wide + the
chart-opaque measurability bank + sourceDataV2_concrete); (c) the L2 sliver census
(hD1_conditional). THE WHOLE SOL-#9 v2 CAMPAIGN (J4-323→330, bricks 1–14) CLOSED IN
8 BRICKS OF WORK. std-3 all 3, raw 0. NOT a₁=R/6. NEXT: J4-331 = the hDaLimLU DATA
census recon+discharge (the next endgame-map item), then (†), then R0/R1.

## J4-331 (2026-08-07, 8106d1be) — DaLimCensusRecon: THE hDaLimLU CENSUS (NO POISONS) [AF]
Every hDaLimLU_concrete binder classified: gauge + hEcomb DISCHARGED
(memGaugeGi_of_geometry / memGaugeGamma_of_hdg0 / memECombine_of_data); the W2
family BANKED (witness_MemInterchange). ★ SATISFIABILITY AUDIT CLEAN — the three
facade poisons do NOT recur; the Da-limit pile is honest. X2 REMAINDER (dependency
order): 1 hFzero (small) → 2 hFdom (Levi-domination re-export) → 3 hIlo/hi +
hII_lo/hi (pairing+Beta) → 4 hbnd (√ε sliver, hD2Hexpand) → 5 hEdom (width-3/2
narrowing, β-seeded) → 6 hLapFull (the deepest — Laplacian comparison → the F2
C²-limit). std-3 all 3, raw 0. NOT a₁=R/6. NEXT: J4-332 = the easy tranche (1–3).

## J4-332 (2026-08-07, b2b3fc95) — DaLimEasyTranche: Da-LIMIT ITEMS 1–3 DISCHARGED [AF]
hFzero_concrete (iterE/leviSeries vanishing at s≤0) + hFdom_concrete (the
width-MATCHED Levi domination re-export) + the four strip integrabilities
(hIlo/hIhi + hII_lo/hII_hi=MemAdjLo/Hi via pairing_intervalIntegrable — the widths
ADD ⟹ constant peak, no sliver). Carries: LeviSeriesLocalData + two Gaussian
dominations + hmeas, all satisfiable. Remainder: 4 hbnd → 5 hEdom → 6 hLapFull.
std-3 all 9, raw 0. NOT a₁=R/6. NEXT: J4-333 = the hard tranche (hbnd recon +
the hEdom width-parametricity verdict).

## J4-333 (2026-08-07, 5c76a7a2) — DaLimHardTranche: ITEM 4 DONE, ITEM 5 REDUCED [AF]
Item 4 hbnd DISCHARGED (amplitudePackage_sliver_bound; carries = the
AmplitudeDerivativeData bundle (hard field hD2Hexpand) + window relations). Item 5
hEdom — THE WIDTH-ENTRY MAP: width 2 pinned only in the collapsed global-gated
bound; the in-chart M2 engine is ALREADY at width 3/2 per-base; the block = the C4c
global-gated assembly. Delivered: gaussian_beats_power (the ∀k absorption engine) +
hEdom_of_gaussPoly_residual (the honest bridge from the named width-1 residual
hraw). Da-limit remainder: 6 hLapFull + the named residues (hraw, hD2Hexpand).
std-3 all 3, raw 0. NOT a₁=R/6. NEXT: Sol consult on (†)/hLapFull/C4c, then J4-334.

## SOL CONSULT #10 (2026-08-07, post-J4-333) — THE THREE DEEP WALLS
(a) (†) THE NC 2-JET: ⚠ (†) is FALSE for a general 0-jet-gauged metric (arbitrary
symmetric ∂∂g) — the honest statement is (†)-given-hGauss, the Gauss-lemma
contraction hGauss : ∀ i, (fun x => ∑ j, g i j x * x j) =ᶠ[𝓝 0] (fun x => x i)
(the ONE-contraction Christoffel radial identity is TOO STRONG/false; the two-
contraction geodesic identity too weak). BRICKS: A1 NCGaussPd3 (the pd-product
third-derivative-at-0 lemmas — the product rule kills all but the Kronecker hits) ·
A2 NCGaussToCyclicT (differentiate hGauss thrice → T_{ipqr}+T_{iqpr}+T_{irpq}=0;
the FOUR instances combine linearly: 2(A+B+D) = h₁+h₂+h₃−h₄ = 0 ⟹ the cyclic
T-identity) · A3 NCRiemannTwoJet (the cyclic identity + riemann_at_zero + metric/
Schwarz symmetry ⟹ (†) by linear arithmetic on opaque T-atoms) · A4 the labelled-
input facade (hGauss = one more gauge input; satisfiable — normal coordinates
exist; deriving it from the exp tower = a separate ~3-brick Gauss-lemma campaign).
(b) hLHSlim: the SAME cancellation as the banked Laplacian sliver — the heat-eq
rewrite does NOT soften it (the ∂τ sliver = the AI boundary term). BRICKS: B1
LaplaceAtRNCOrigin (Δ_g f 0 = ∑ᵢ∂ᵢ∂ᵢf under the gauge) · B2 the frozen=full−sliver
decomposition adapter (W2 interchange + interval split, identify with the
XUniformSliverFull object) · B3 the Tendsto re-export (const.sub hsliver).
(c) hraw: KEEP LABELLED (per-base M2 does not compactify cheaply: base-uniformity
+ exact width-1 preservation are real infrastructure). BRICKS: C1 the
GlobalGatedRawBound predicate · C2 the consumer adapter · C3 the capstone_with_hraw
facade. The hraw PROOF = a separate later campaign (loc-unif M2 + finite-cover +
cutoff absorption), NOT on the critical path.

## J4-334 (2026-08-07, e38ac3c4) — (†) BRICKS A1+A2: THE pd CALCULUS + THE CYCLIC-T IDENTITY [AF]
A1 NCGaussPd3: pd_coord + pd_coord_mul + pd3_coord_mul (only the Kronecker hits
survive at 0) + pd3_sum. A2 NCGaussToCyclicT: pd_eventuallyEq + T_symm_cd/ab +
cyclicT_gauss + ★ cyclicT_of_hGauss (T_{abcd}+T_{acbd}+T_{bcad} = 0 from the
labelled hGauss gauge input, by linarith on the four cyclic instances). std-3 all,
raw 0. NOT a₁=R/6. NEXT: J4-335 = A3 (metric_secondJet_eq_riemann — the linear
system pins T ⟹ (†)) + A4 (htr_from_hGauss — the R3 wall fully reduced to hGauss).

## J4-335 (2026-08-07, 991ad478) — ★★ (†) IS A THEOREM — THE R3 WALL REDUCED TO hGauss ★★ [AF]
riemann_at_zero_T (the T-atom repackaging, defeq) + the four cyclic Gauss relations
pin F=A ⟹ metric_secondJet_eq_riemann = (†): T g a b c d = −(1/3)(R_{acbd}+R_{adbc})
(linarith on opaque atoms) + riemann_pair_symm_at_zero (discharges hpair) +
★ htr_from_hGauss (the capstone htr from hg/hgsymm/hgiC/hgi0/hdg0/hGauss ALONE).
The previously-opaque (†) residue of J4-318 is now a theorem; the R3 Ricci-source
wall rests on the ONE labelled satisfiable hGauss gauge input. std-3 all 4, raw 0.
NOT a₁=R/6. NEXT: J4-336 = the hLHSlim bricks B1–B3 (+B4 hLapFull_concrete — the
Da-limit census would then close mod the labelled inputs).

## J4-336 (2026-08-07, f7c39139) — FrozenLaplaceSliver: hLHSlim → hPd2conv [AF]
F0: B1 was banked generic; every LapTrunc→full limit is CIRCULAR (assumes hLapFull);
XUniformSliverFull IS x-UNIFORM but crosses the Laplacian difference only through
the full-side interchange — the deep wall stands. hLHSlim_concrete (the exact
binder from the atomic hPd2conv carrier, non-circular) + hLapFull_of_pd2conv.
Labelled inputs now: hGauss, hraw, hD2Hexpand, hPd2conv. std-3 all 4, raw 0.
NOT a₁=R/6. NEXT: J4-337 = the hraw C1–C3 packaging + hDaLimLU_from_labelled (the
whole Da-limit pile as ONE theorem over the labelled-input list).

## J4-337 (2026-08-07, 889ccec7) — ★★★ THE Da-LIMIT PILE = ONE THEOREM ★★★ [AF]
GlobalGatedRawBound (the hraw predicate) + hEdom_of_globalRawBound + the six
sub-assembly groups + hDaLimLU_from_labelled: ALL ~45 hDaLimLU_concrete binders
plumbed through the banked dischargers (J4-331..336). SURVIVING: the geometry/gauge
raw inputs + the W2 family + window data + LeviSeriesLocalData + dominations/
measurabilities + the amplitude bundle (hD2Hexpand) + Fubini reps + THE LABELLED
hraw + hPd2conv. The facade poisons do not recur. std-3 all, raw 0. NOT a₁=R/6.
NEXT: Sol consult on the v3-export architecture (the last heavy composition), then
J4-338 toward a1_R6_from_labelled.

## SOL CONSULT #11 (2026-08-07, post-J4-337) — THE v3-EXPORT ARCHITECTURE (5 bricks)
VERDICT: O2 (O3 fallback) — NEVER consume the v2 ∃ (the destructed S is logically
opaque; witness identity does not survive ∃-elim; O4-post-hoc has the same problem).
Route: grep the capstone's proof for the theorem applied immediately before the
final ∃-intro; export/apply THAT pre-∃ inner theorem at the concrete gate (O2); if
not separately named, a thin trimmed core via the same lower-level lemma (O3). The
v2 capstone stays untouched read-only; v3 = a SIBLING export from the same core.
BRICKS: 1 wide_a1_R6_core_AT_CONSTRADIUS (the thin apply-wrapper core: base + hS1 +
htr + the three slot antecedents → the a₁ 2-jet conclusion; no labelled inputs
here) · 2 the htr adapter (re-export htr_from_hGauss) · 3 the Da-data adapter
(re-export hDaLimLU_from_labelled) · 4 A1R6GateSlots (a shallow Prop structure;
the three slots via refine ⟨?_,?_,?_⟩, each field its own theorem if slow) · 5
a1_R6_from_labelled (the final facade: the shallow side-condition structures
(GeometryRaw/GaugeRaw/WindowSide/DaAnalyticSide/BoundaryCensus/C2CensusV2 — reuse
J4-337-style bundles, explicit args, no mega-record/extends chains) + the FOUR
EXPLICIT labelled inputs (hGauss/hraw/hD2Hexpand/hPd2conv) → ⟨a₁ 2-jet⟩; internally
have-chains: hS1/htr/hDa/slots then exact the core). GUARDRAILS: never restate/
unfold/destruct v2; ≤1 heavy application per brick; exact/apply + typed haves; no
broad simpa/simp_all/convert; the one shared syntactic Gate def everywhere; scalar
equalities in tiny standalone lemmas (change + exact); split any brick >1-2 min.

## J4-338 (2026-08-07, 90882103) — A1R6CoreAtGate: v3 BRICK 1 — THE PRE-∃ CORE (O2) [AF]
K0: O2 — the inner carrier (WideA1AssemblyTrunc.wide_a1_R6_of_residue_inf_trunc) is
PUBLIC. wide_a1_R6_core_AT_CONSTRADIUS = the thin wrapper at the literal constGate:
base + package fields + hS1 (per-gate, replacing ∀-hEmeas) + htr + the three flat
slot antecedents → the a₁ 2-jet; ONE heavy application at native κ=2. v2 untouched.
std-3, raw 0. NOT a₁=R/6. NEXT: J4-339 = v3 bricks 2+3+4 (the htr/Da adapters +
A1R6GateSlots).

## J4-339 (2026-08-07, e6fd4210) — A1R6SlotAdapters: v3 BRICKS 2+3+4 [AF]
L3: the Da thread is DIRECT (DaLimLUGoal abbrev-defeq to the slot consumers — no
adapters). htr_adapter + daLim_for_slots + A1R6GateSlots + a1_R6_slots_AT_GATE
(all three fields wired, one banked producer per field). v3 remains: brick 5 only.
std-3 all 3, raw 0. NOT a₁=R/6. NEXT: J4-340 = a1_R6_from_labelled (THE FINAL
FACADE — the a₁ 2-jet over the four labelled inputs + the satisfiable censuses).

## J4-340 (2026-08-07, 3a67981a) — ★★★★ THE v3 CHAIN IS COMPLETE ★★★★ [AF]
a1_R6_from_labelled = THE CONDITIONAL a₁=R/6 MILESTONE: the a₁ two-jet (heatOp
vanishing + the trueHeatKernel expansion with the GENUINE Ricci scalar
(∑ᵢ ricci)/6 in the O(t) coefficient) at the literal constant-radius gate, from
THE FOUR LABELLED INPUTS (hGauss, hraw, hD2Hexpand, hPd2conv) + the base
geometry/gauge/window raw inputs + the package facts (satisfiability =
constRadius_package_and_S1; hS1 under c<δ₀) + the satisfiable census piles
(Da-limit ~60 / Duhamel-core ~90 with shared binders de-duplicated / F2 + frozen/
moving / CConv-v2 sliver). NO shape residues — the full composition type-checked.
THE SOL-#11 PLAN (bricks 1–5, J4-338/339/340) COMPLETE. std-3, raw 0.
⚠ NOT unconditional a₁=R/6. THE REMAINING SURFACE = the four labelled derivation
campaigns: hGauss (the exp-pullback Gauss lemma, ~3 bricks per SOL #10) · hraw
(loc-unif M2 + finite cover + cutoff absorption) · hD2Hexpand (the Leibniz-Gaussian
derivative layer) · hPd2conv (the full-side diff-under-∫ deep wall) + the census
satisfiability sweeps. NEXT: J4-341 = the hGauss campaign brick 1 (the
first-variation/Gauss-lemma recon).

## J4-341 (2026-08-07, 30d51d70) — GaussLemmaFirstVariation: THE hGauss RADIAL LEG [AF]
R0: the geodesic ODE banked (geodesicField+expTube_spec); metric compat banked
(christoffel_lower); the Jacobi bank has NO symplectic conservation; the energy
identity NEW here. G1a the compat-algebra derivative-zero + G1b the ODE product
rule + G1c ★ geodesic_energy_conservation (the RADIAL Gauss identity on the exp
tube). hGauss remaining: (a) transverse Jacobi conservation (new symplectic) ·
(b) homogeneity (ExpJacobianRescale partial) · (c) coordinate assembly · (d) frame
transport. std-3 all 4, raw 0. NOT a₁=R/6. NEXT: J4-342 = the transverse leg
(GaussLemmaTransverse: d/dt[g(J,γ̇)] = g(J',γ̇) → the Jacobi-ODE second step →
the linear-growth conclusion).

## J4-342 (2026-08-07, c6c5d0fb) — GaussLemmaTransverse: THE hGauss TRANSVERSE LEG [AF]
T1a the covariant-pairing algebra (pure metric_compat, no ½-factors) + the generic
pairing HasDerivAt + T1b (E_J' = the covariant pairing) + T2b (conditional on the
ONE named hvanish — the first-pair antisymmetry contraction) + T3 the linear growth
(double constancy). J abstract; the matrix instantiation later. hGauss remaining:
the hvanish brick → homogeneity → coordinate assembly → frame transport. std-3 all
5, raw 0. NOT a₁=R/6. NEXT: J4-343 = RiemannFirstPairAntisym (hvanish discharged
from the general-point lowered-Riemann antisymmetry).

## J4-343 (2026-08-07, 23ccf3cd) — RiemannFirstPairAntisym: hvanish DISCHARGED [AF]
V1 the general-point lowered-Riemann expansion (½∂∂g + ΓΓg; the gΓΓ pairwise
cancellation + Schwarz) + V2 the first-pair antisymmetry (FULLY, incl. the ΓΓ part)
+ V3 hvanish_from_antisym (the exact hvanish of the transverse leg, given the
satisfiable Jacobi-ODE hJac). The transverse curvature half CLOSED. hGauss
remaining: the Jacobi-ODE instantiation → homogeneity → the coordinate assembly →
the frame transport. std-3 all 4, raw 0. NOT a₁=R/6. NEXT: J4-344 =
GaussLemmaHomogeneity (the Euler homogeneity + the hJac instantiation from the
matrix-Jacobi flow).

## J4-344 (2026-08-07, 5caec8da) — GaussLemmaHomogeneity: EULER + THE COVARIANT BRIDGE [AF]
H1 exp_euler_homogeneity UNCONDITIONAL (D exp_p(v)·v = γ̇_v(1) — the banked rescale
ray facts + chain rule + within-Iic endpoint uniqueness). H2 jacobi_covariant_ode
(the raw variational ODE → the exact hJac covariant shape; the complete Γ/∂Γ
algebra; carries hJODE-banked/hcJ-def/hcJp-product-rule). THE hGAUSS CHAIN IS
ALGEBRAICALLY CLOSED; remaining wiring = the Jacobi instantiation + the coordinate
assembly + the frame transport. std-3 all 3, raw 0. NOT a₁=R/6. NEXT: J4-345 =
GaussLemmaAssembly (the instantiation + the pairing assembly + ∑g̃_ij v^j = v^i).

## J4-345 (2026-08-07, 59b01cc6) — GaussLemmaAssembly: THE FULL GAUSS LEMMA [AF]
gauss_first_variation(_dexp) (the whole chain wired: the initial data + T3 linear
growth + the curvature kill ⟹ g_{exp v}(D exp(v)·w, γ̇(1)) = g_p(w,v)) +
gauss_coordinate_contraction(_gauge) (★ ∑g̃_ij v^j = v^i at the RNC base gauge —
the exact hGauss shape; expPullbackMetric reused). REMAINING (the final hGauss
brick): the flow-data HasDerivAt discharge (via the banked ∃-Φ) + the germ shape +
the frame/capstone transport. std-3 all 4, raw 0. NOT a₁=R/6. NEXT: J4-346 =
GaussLemmaFlowData (F1 the flow data + F2 the concrete contraction + F3 the germ +
F4 the transport-scope verdict incl. the C⁴-vs-C∞ check).

## J4-346 (2026-08-07, a3b8957b) — GaussLemmaFlowData: THE hGauss GERM DELIVERED [AF]
F1 flow_jacobi_field (the named-conjunct ∃-Φ extraction; J(0)=0/Jp(0)=w/hJ1 + the
interior variational system). KEY FINDING: the flow gives within-Icc[0,1]
derivatives vs the assembly's Ioo(-2,2) — the closure = the interior-MVT route
(documented in-header). F2/F3 ★ hGauss_pullback (the =ᶠ germ in the EXACT consumer
binder order; surviving hyp = hgball) + F4 g̃(0)=I proven. F4 VERDICT: the capstone
C∞-of-pullback = the one labelled smoothness residue (C⁴ cap); ∂g̃(0)=0 +
inverse/positivity derivable-with-work. std-3 all 4, raw 0. NOT a₁=R/6. NEXT:
J4-347 = GaussInteriorMVT (E′=W, W′=0 on the interior + the MVT closure ⟹
hgball_concrete ⟹ the hGauss campaign closes mod the C∞ scope note).

## J4-347 (2026-08-07, 1b4db10a) — ★★ THE hGAUSS CAMPAIGN ANALYTICALLY CLOSED ★★ [AF]
THE TOOL: Lagrange's MVT (exists_hasDerivAt_eq_slope) — interior derivatives +
Icc-continuity only; the J4-346 endpoint worry sidestepped. covariant_field_
hasDerivAt (the one new interior product-rule computation) + gauss_interior_
identity (the per-point Gauss identity DERIVED from the flow; the window + the
hJd/hcJd/hcJp carries all discharged) + hgball_concrete + ★ hGauss_pullback_
concrete (the =ᶠ germ with NO Gauss carry; surviving = ordinary geometry hyps +
g_p=I). ONE OF THE FOUR LABELLED INPUTS (hGauss) IS NOW DERIVED for the pullback
route. Residue: the C∞-vs-C⁴ facade scope (labelled) + ∂g̃(0)=0 + inverse/
positivity (derivable). std-3 all 6, raw 0. NOT a₁=R/6. NEXT: J4-348 =
PullbackGeometryLegs (∂g̃(0)=0 + inverse/positivity + the C∞ verdict).

## J4-348 (2026-08-07, 6fe4574b) — PullbackGeometryLegs: NO C∞ WALL; hpd2 THE SOLE RESIDUE [AF]
THE BANKED FINDING: the D²exp jet + ∂g̃(0)=0 were ALREADY BANKED (pd_jacobian_
expMap_zero / pd_expPullbackMetric_at_zero). L2 delivered (isUnit/rightInverse/
det>0 eventually). ★ L3 VERDICT: the correct pullback consumer =
RNCExpansion.heat_a1_of_gauge_c2 (FINITE-ORDER, already instantiated at g̃ via
kappa_eq_one_sixth_expPullback_of_hpd2) — NO C∞-vs-C⁴ wall on this route. THE
SOLE OPEN RESIDUE: the labelled hpd2 (the ∂²g̃(0) radial-contraction identity —
likely a linear consequence of the PROVEN cyclic T-identity at g̃). std-3 all 4,
raw 0. NOT a₁=R/6. NEXT: J4-349 = Hpd2FromCyclic (the cyclic→hpd2 algebra +
potentially κ=1/6 AT THE PULLBACK).

## J4-349 (2026-08-07, ba0dce1f) — Hpd2FromCyclic: THE CYCLIC CROSS-CHECK [AF]
hpd2 = 2A − C = 0; the four-instance cyclic gives 2A + C = 0 — hpd2 needs BOTH
families (A = 0 from the diagonal Gauss cyclic). hpd2_of_cyclicT (unconditional
abstract algebra) + hcd_expPullback (Schwarz at g̃ via Clairaut — discharged) +
hpd2_expPullback_of_cyclic (carries = the two ⊤-blocked satisfiable g̃-cyclics) +
kappa_eq_one_sixth_expPullback_via_cyclic. ⚠ HONESTY: hpd2 was ALREADY
unconditional in-repo (expPullback_hpd2, residFold) and the composed
kappa_eq_one_sixth_expPullback EXISTS — the pullback κ=1/6 was already closed;
J4-341..349 = the INDEPENDENT Gauss-lemma/cyclic derivation + the hGauss labelled
input CLOSED for the pullback route. std-3 all 4, raw 0. NOT a₁=R/6. NEXT:
J4-350 = D2HExpandRecon (the next labelled campaign).

## J4-350 (2026-08-07, 5b680261) — D2HExpandRecon: hD2Hexpand → ONE GERM RESIDUE [AF]
The AmplitudeDerivativeData 24-field census CLEAN (no artefacts — like the Da-limit
pile). The Leibniz–Gaussian layer FULLY discharged (witnessSecondXDeriv_expand_
bridge onto the banked gaussComp_amp_center_decomp; the germ-locality pd lemmas;
the machine-checked flat satisfiability witness). THE ONE WALL: hrep — the germ
factorization G_τ(V·)·A near 0 (the chart-image Gaussian identity / RNC
near-isometry with O(‖z‖⁴) absorption — the AmplitudePackage's flagged hard input).
std-3 all 4, raw 0. NOT a₁=R/6. NEXT: J4-351 = HrepGermFactorization (the germ from
the banked on-gate factorization + openness + the chart-jet center identities).

## J4-351 (2026-08-07, 985c6641) — HrepGermFactorization: THE GERM DISCHARGED + THE hV0 CRUX [AF]
The hrep germ DISCHARGED (the banked on-gate factorization + the open gate).
THE CRUX: hV0 is FALSE at the true chart off-flat (the iff-characterization +
the exact exp((rz−r_{W0})/(4τ)) ratio — bounded ONLY in the √ε sliver ‖z‖~√τ).
The exact-shape hD2Hexpand with uniform amplitude bounds = a flat/diagonal-locus
identity; its consumption lives in the √ε collar. hD2Hexpand_concrete = the
bridge composed with hV0 the isolated per-(τ,z) residue. std-3 all 5, raw 0.
NOT a₁=R/6. NEXT: Sol consult on the hV0 regime re-specification (the 4th
corrected-field case), then J4-352.

## SOL CONSULT #12 (2026-08-07, post-J4-351) — THE hD2Hexpand RE-SPECIFICATION
VERDICT: (c) COLLAR-RESTRICTED with the z-Gaussian conclusion, CONSTRUCTED via the
ratio mechanism of (a). The corrected bundle AmplitudeDerivativeDataOn Regime
(predicate premises, not subtypes; Regime = 0<τ ∧ τ≤τ₀ ∧ ‖z‖≤c√τ ∧ chartDomain z
— intrinsic, ε-free); the true-chart amplitudes = ρ·chartAmp with ρ =
exp((r_z−r_{W0})/(4τ)) and ρ ≤ K = exp(Lc³√τ₀/4) on the regime; the corrected
constants K·M_j. The chart-Gaussian form stays a banked intermediate (NOT the
consumer contract — (b) would cause the largest re-derivation; (a) would force the
consumer to re-uniformize). BRICKS: 1 the corrected bundle + the chart-native
adapter (gauss(W z 0) = ρ·gauss(z) + ρ≤K) · 2 the amplitudePackage_sliver_bound
re-derivation (the hbnd CONCLUSION syntactically UNCHANGED — collar_to_regime
inside; K absorbed into M's; no ρ/K/Regime exposure) · 3 the concrete true-chart
discharge (J4-350's expansion + the ratio rewrite + ρ≤K; β1/β2/gaussian_beats_power
unchanged mod constants; NO product-rule corrections — ρ is x'-free). SAFETY: the
restriction dies inside the sliver-bound proof; hbnd_concrete/hDaLimLU_from_
labelled/a1_R6_from_labelled binder-UNCHANGED.

## J4-352 (2026-08-07, a39246a7) — AmplitudeDataOnCollar: hV0 ELIMINATED (SOL-#12 1+3) [AF]
B1 collarRegime + rhoRatio/collarK (ρ ≤ exp(Lnc³√τ₀/4) on the collar) +
AmplitudeDerivativeDataOn (the regime-conditional corrected bundle, the z-Gaussian
conclusion exact). B2 the ρ-bridge (hV0 → the unconditional ratio; no product-rule
corrections) + hD2HexpandOn_concrete (the true chart; hV0 ELIMINATED; carries =
chart jets + hVP/hPsq/hVQ only). B3 amplitudeDataOn_concrete (the FULL corrected
bundle at the true chart; M_j = K·M_jchart). std-3 all, raw 0. NOT a₁=R/6. NEXT:
J4-353 = SliverBoundOnCollar (Sol brick 2: the sliver-bound re-derivation with the
hbnd conclusion unchanged; the off-collar tail handling).

## J4-353 (2026-08-07, c49249cd) — SliverBoundOnCollar: THE ON-COLLAR LEGS + THE SPLIT VERDICT [AF]
S1: sliver2_bound consumes GLOBALLY (the √ε gain = the full-space Hessian moment
cancellation — fails on sub-domains; every exact-constant global-bundle route
unsatisfiable). The on-collar legs banked (collar_to_regime + the 3-term identity +
the bounds + the integrand identity, hV0-free). ★ THE CARRY TRANSFORMED: hD2Hexpand
CLOSED on the collar; the residue = THE OFF-COLLAR SLIVER REMAINDER (the tail +
the moment split). std-3 all 6, raw 0. NOT a₁=R/6. NEXT: Sol consult on the split
design (the A(0)-moment full-space + Lipschitz-increment architecture), then J4-354.

## SOL CONSULT #13 (2026-08-07, post-J4-353) — THE MATCHED-PAIR SLIVER SPLIT
DECISIVE: the raw on/off-collar split does NOT close — ∫_{off}|H_τ| = a(c)/τ
(τ-independent numerator) ⟹ the truncated constant mode gives poly(c)e^{−κc²}·∫dτ/τ
= LOG-DIVERGENT at the endpoint; gaussian_beats_power only improves the c-constant.
THE FIX: the MATCHED-PAIR architecture — the tail moment T_τ = ∫_{off}H_τ must stay
PAIRED: Brick 1 (on-collar, tail-matched): ‖I_on + A₀·T_τ‖ ≤ B₀/√τ + B₁ (the
A₀-collar-moment = −A₀T_τ by the full-space cancellation; the increment via the
collar hqLip). Brick 2 (off-collar, matched): ‖I_off − A₀·T_τ‖ ≤ B₀'/√τ + B₁' —
compare the chart-native leading term DIRECTLY with H_τ·A₀ via the weighted
|G_τ^chart − G_τ| ≤ C‖z‖³/τ·G_{C'τ} + the amplitude increment; NEVER estimate ρ
alone off-collar (use G_τ·ρ = G_τ^chart). Brick 3 (assembly): the A₀T_τ cancels ⟹
the unchanged hbnd with c-dependent constants absorbed. hqLip: collar-restricted
suffices; Lip(ρ·A_chart) ≤ K·L_chart + M_chart·K·C_r·c²/4 GIVEN the quantitative
cubic-contact gradient estimate ‖∇(r_z − r_{W₀z})‖ ≤ C_r‖z‖² — THE honest carry if
not banked (tangent-isometry + C^{1,1} control; also exactly what Brick 2 needs).

## J4-354 (2026-08-07, 2a7dbc93) — SliverTailMatched: SOL-#13 BRICK 1 COMPLETE [AF]
T1 the EXACT pairing (∫_C H = −T_τ, via the banked full-space moment) + T2 the
increment (≤ L(15n/2)/√τ via the banked √τ-gain moments) + T3 ★ sliver_term1_on_
collar_matched (Sol's exact shape, B₁=0) + T4 the 1/τ tail sanity. The carry: the
collar Lipschitz hq (satisfiable per the Lip(ρ·A_chart) analysis). std-3 all 6,
raw 0. NOT a₁=R/6. NEXT: J4-355 = brick 2 (the off-collar matched domination + the
cubic-contact gradient recon).

## J4-355 (2026-08-07, 0f706a35) — SliverOffCollarMatched: SOL-#13 BRICK 2 [AF]
O1 the weighted comparison (|G^chart−G| ≤ (Ln/4)(√C')ⁿ(‖z‖³/τ)G_{C'τ}; the width
algebra + the shrunk-gate concrete corollary). O2 the difference decomposition.
O3 sliver_term1_off_collar_matched (B₁'=0; the increment PROVEN; the comparison
leg = the named hcomp moment carry). O4 cubic_contact_gradient_bound + THE
VERDICT: needs Db = O(‖z‖) (the derivative-level displacement carry, SHARED with
brick 1's hqLip; not banked). std-3 all 10, raw 0. NOT a₁=R/6. NEXT: J4-356 =
brick 3 (the assembly: A₀T_τ cancels; the hcomp discharge; terms 2/3; ⟹ the
unchanged hbnd ⟹ hD2Hexpand fully closed mod the enumerated carries).

## J4-356 (2026-08-07, 2ba74ad8) — ★★ THE SOL-#13 MATCHED-PAIR CAMPAIGN COMPLETE ★★ [AF]
Terms-2/3 verdict: only term 1 cancels; 2/3 absolute. A1 the term-1 assembly
PROVEN (A₀T_τ cancels exactly). A2 the hcomp discharge machinery + the τ^{3/2}
satisfiability witness. A4 the √ε conclusion (amplitudePackageOn_sliver_bound).
A5 the COMPLETE 5-carry census: hcubic(sat) · hgate · hdisp (THE shared Db=O(‖z‖)
displacement derivative — the one new geometric item) · hjets · hcenter. THE
hD2Hexpand INPUT reduced to the five carries. std-3, raw 0. NOT a₁=R/6. NEXT:
J4-357 = DisplacementDerivative (the hdisp campaign — likely NEARLY BANKED via
the J4-273/274 terminal-velocity machinery: W z 0 = −T₀-form + TerminalVelC2 ⟹
Db = id − DT₀ with DT₀(0)=id ⟹ the C²-modulus Lipschitz).

## J4-357 (2026-08-07, 21ff6a10) — DisplacementDerivative: hdisp RESOLVED [AF]
The dont-undercredit strike: the base-side 1-jet WAS banked (baseVaryingChart_
hasFDerivAt_center ⟹ Db(0)=0) + the C² banked ⟹ displacement_deriv_bound
(UNCONDITIONAL) + cubic_contact_gradient_concrete + the Lip core. THE SLIVER
CENSUS: hdisp resolved; remaining = hcubic(sat)·hgate·hjets·hcenter. std-3 all 4,
raw 0. NOT a₁=R/6. NEXT: J4-358 = CensusSweepOne (the a1_R6_from_labelled
hypothesis piles' concrete instantiation sweep).

## J4-358 (2026-08-07, ced39b3d) — CensusSweepOne: THE CENSUS SWEPT [AF]
7 composed group discharges (gauge/ecombine/source/strip/adj/interchange/
census_lapfull-flagship). THE POST-SWEEP LIST: the four labelled inputs (hGauss
pullback-derived · hraw · hD2Hexpand-in-dataAmp · hPd2conv) + the 4 sliver
carries + the hBoundaryLim pile + the raw geometry/certified package + the
genuine data piles (dataLevi/dominations/W2/§I-J-K). The derivable members drop
for their raw providers. std-3 all 7, raw 0. NOT a₁=R/6. NEXT: J4-359 =
HrawCampaignOne (the width-question verdict + the uniformization recon).

## J4-359 (2026-08-07, c465a2c4) — HrawCampaignOne: THE OPENER VERDICTS + LEGS [AF]
Q1 no collapse (the width-1-with-poly entry stands; its transfer → ambient 4/3 <
3/2). Q2 ★ the constant ALREADY UNIFORM over K (no cover extraction). Q3 the
support = the gate (the far region empty). Legs: the width mono + hEdom_of_
polyfree_width + the off-support zero + gatedRawBound_of_onGate. REMAINING: the
width-1 in-chart pre-collapse form + the two-sided transfer + the polynomial
re-expression. std-3 all 4, raw 0. NOT a₁=R/6. NEXT: J4-360 = HrawChartTransfer.

## J4-360 (2026-08-07, b107f0f1) — HrawChartTransfer: THE TRANSFER + THE BRIDGE [AF]
T1 the two-sided budgets (δ=1/4: r²_z ≤ (4/3)r²_v ∧ r²_v ≤ (5/4)r²_z). T2 the
width-1-with-poly chart→ambient transfer (→ 4/3) + the width-parametric bridge
(w₀ ∈ (0,3/2)). T3: the pre-collapse in-chart form NOT bank-extractable — the
honest hgate carry. T4 the width-parametric predicate + the gate assembly +
hraw_variant_concrete (the capstone). hraw remaining: the pre-collapse extraction
+ the concrete near-isometry + the wiring. std-3 all, raw 0. NOT a₁=R/6. NEXT:
J4-361 = HrawNearIsometryConcrete (the flow-displacement bound + the radial
comparison + the (1/4)-budget on the shrunk gate).

## J4-361 (2026-08-07, b98d8c3c) — HrawNearIsometryConcrete: THE NEAR-ISOMETRY CLOSED [AF]
N1 banked (uniformFlowExp_displacement_bound re-exported). N2 the polarization
(the honest n-cofactors). N3 ★ nearIsometry_concrete (the exact T1 shape, the
explicit shrunk gate; the C_D‖v‖≤1/2 bootstrap). hraw remaining: the pre-collapse
extraction + the wiring. std-3 all 3, raw 0. NOT a₁=R/6. NEXT: J4-362 =
HrawPreCollapse (the extraction + the wiring ⟹ hEdom discharged ⟹ hraw CLOSED).

## J4-362 (2026-08-07, a80bedcf) — HrawPreCollapse: THE QUADRATIC RECONCILIATION [AF]
THE 5TH INTERFACE FINDING: the honest pre-collapse form is width-1 QUADRATIC (the
T2 metric-deviation term); the extra power = A WIDTH (one widening absorbs it) ⟹
the same hEdom. The quadratic bridge + transfer + assembly + ★ hEdom_concrete_final
(the exact hEdom from the honest on-gate width-4/3 quadratic hgate carry). THE hraw
RESIDUE: hgate (satisfiable, named) + the mechanical hEdom-accepting re-thread.
std-3 all, raw 0. NOT a₁=R/6. NEXT: the hPd2conv Sol consult (the v2-route
hypothesis — the s-integral representation may break the J4-336 circularity).

## SOL CONSULT #14 (2026-08-07, post-J4-362) — ★★★ THE hPd2conv DEEP WALL DISSOLVES ★★★
VERDICT: YES — the v2 route breaks the J4-336 circularity. ∂ᵢ∂ᵢ(full conv)(0) =
∂ᵢ[the Dmap coefficient gcoef i](0) — the full-side second derivative is obtained
by differentiating the s-INTEGRAL-REPRESENTED first-derivative coefficient (the
banked hfam_v2/Dmap theorem, the (t−s)^{-1/2}-dominated FIRST interchange), NOT a
full-side second interchange. The hD1 census (hbulkderiv/hbulk_tendsto/hsliver/
hcont) is frozen-side-only + the candidate ⟹ NON-CIRCULAR, and its hbulk_tendsto
at x=0 IS the needed frozen→full convergence. hPd2conv = A COROLLARY of the
already-carried sliver census. THE ONE INTERFACE POINT: the bare ContDiffAt hD1
forgets its derivative = the candidate — re-export the candidate-identification
(pd i (gcoef i) 0 = gderiv i 0) from hD1_from_data's proof (API extraction, not
analysis). THE 3 BRICKS: 1 the full-side bookkeeping (hfam_v2 ⟹ pd(conv) = gcoef
locally; pd² = pd(gcoef) = gderiv(0) via the identification) · 2 the frozen-side
(the proper-integral truncated version; hbulkderiv ⟹ pd²(frozen_m) = gderivₘ(0);
finite bad m irrelevant atTop) · 3 the census convergence (hbulk_tendsto at 0 ⟹
the Tendsto; the √ε sliver as backup). NO new domination needed.

---
## ★★★★ J4-363 (b8fe943b): THE hPd2conv WALL DISSOLVED — ALL FOUR LABELLED INPUTS RESOLVED/DISSOLVED

`QIQTH/Pd2ConvDissolution.lean` (ns `QIQTH.Pd2ConvDissolution`) — the Sol-#14 execution. The last
deep wall of `a1_R6_from_labelled` is a **corollary of the already-carried hD1 sliver census**:
the full-side second derivative = ∂ᵢ(the s-integral-represented Dmap coefficient `gcoef i`)(0) —
the `(t−s)^{−1/2}`-dominated FIRST interchange only, NO full-side second interchange (the
J4-336 circularity broken).

- `pd_of_hasFDerivAt` (B0a) — the HasFDerivAt→pd read-off.
- `pd_germ_eq_of_family` (B0b) — the `hfull_pd1`/`hfrozen_pd1` germ links from an hfam_v2-shape family.
- ★ `gcoef_hasFDerivAt_candidate` (B0c) — the candidate-identification the bare `hD1_from_data`
  ContDiffAt forgets: `HD1SliverRoute.hD1_bulk_sliver_reduction` re-exported at x₀=0 (pure API
  extraction — the inner uniform-limit-of-derivatives step ALREADY installs `gderiv 0`).
- `pd2_at_zero_eq` (B1/B2) — the second-partial read-off, both sides (`pd_congr_of_eventuallyEq` + B0a).
- ★★★ `hPd2conv_from_census` (B3) — the EXACT `hPd2conv` binder of
  `FrozenLaplaceSliver.hLapFull_of_pd2conv` (verified verbatim) from the census only; the
  `hsliver`+`hb` squeeze at 0 IS the frozen→full convergence; CLM-application continuity evaluates
  at eᵢ. The census's `hcont` NOT needed (2-jet only).

**THE FOUR LABELLED INPUTS NOW STAND**: hGauss DERIVED (J4-347) · hD2Hexpand → the sliver
carries (J4-356) · hraw → the hgate carry (J4-362) · hPd2conv → the census corollary (THIS).

All 5 std-3; budget raw 0; wired (QIQTH.lean + AxiomAudit pins). Build 39s agent / green my side.

**HONEST DISTANCE**: a₁=R/6 remains CONDITIONAL. The remaining surface: (1) the hgate carry
(the on-gate width-4/3 quadratic per-base parametrix bound — satisfiable, possibly derivable
from the M2 ingredients); (2) the mechanical hEdom-accepting re-thread of
`hDaLimLU_from_labelled` (the signature names the linear hraw); (3) the 4 sliver carries
(hcubic-sat/hgate/hjets/hcenter) + the L_{A_chart} Lipschitz data; (4) the hfull_pd1/hfrozen_pd1
concrete instantiations (pd_germ_eq_of_family on the carried hfam_v2 / the banked frozen
linewise); (5) the data piles (dataLevi, the dominations, the W2 family, §I/J/K); (6) the
final composition. Est. ~1–3 days.

---
## J4-364 (dcfba0e9): THE hraw LABEL RETIRED — the assembly re-threaded onto the hgate carry

`QIQTH/LabelledRethreadV2.lean` (ns `QIQTH.LabelledRethreadV2`) — the mechanical re-thread.
- `hDaLimLU_from_labelled_v2` — the compiled-source copy of `hDaLimLU_from_labelled` with the
  `{P, hP, hraw}` trio → ONE direct width-3/2 `hEdom` ∃-binder (the exact
  `hEdom_of_globalRawBound` conclusion shape); step (vii) = plain `obtain`. Same `DaLimLUGoal`.
- `hEdom_vanVleck_of_hgate` — the one-delta bridge (`simp only [vanVleckGatedWitness]` head
  rewrite only; nothing touched `uniformInverseChart` internals) feeding
  `HrawPreCollapse.hEdom_concrete_final`.
- ★ `hDaLimLU_from_hgate` — the capstone: the un-dischargeable global width-1 LINEAR `hraw`
  label REPLACED by the honest reachable on-gate width-4/3 QUADRATIC `hgate` carry.

Surviving labelled inputs of the one-theorem assembly: `hgate` (M2-ingredient derivation) ·
`dataAmp.hD2Hexpand` (→ the matched sliver carries, J4-356) · per-`u` `hPd2conv` (→ the census
corollary J4-363; the per-`u` instantiation = J4-365). All 3 std-3; raw 0; build 27s.
NOT a₁ = R/6 (CONDITIONAL). Next: the hPd2conv per-u census instantiation, then the hgate M2 glue.

---
## J4-365 (df27b410): the per-u hPd2conv census instantiation

`QIQTH/Pd2ConvPerU.lean` (ns `QIQTH.Pd2ConvPerU`) — the layer between the J4-363 dissolution and
the J4-364 hgate assembly.
- `hfull_pd1_concrete` — the full-side germ from the banked `CConvV2Facade.hfam_v2` via
  `pd_germ_eq_of_family`; census `gcoef` = the Dmap coefficient = the s-integral
  (`Dmap_apply_single`). Bank sufficed (dont-undercredit paid off again).
- `hfrozen_pd1_from_hQ1` — ★ U0 FINDING: no frozen ∃-`HasFDerivAt` family needed; the banked W2
  `hQ1` pointwise formula on `V ∈ 𝓝 0` IS the germ (`filter_upwards`), `fbulk i m` = the
  truncated s-integral.
- ★ `hPd2conv_perU` — the EXACT per-u binder (viii) of `hDaLimLU_from_hgate`, ∀-intro plumbing
  of `hPd2conv_from_census` over the u-indexed census family + the two germ links.

Residue: U3 = the mechanical census-thread (`hDaLimLU_from_hgate_census`, J4-366) · then the
germ-link carries (hfam_v2's hlin/hD1 + per-u hQ1 threading — hQ1 is ALREADY a binder of the
assembly, so the frozen link may thread for free). All 3 std-3; raw 0; build 28s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-366 (7234f374): the hPd2conv LABEL RETIRED from the assembly — the census-thread

`QIQTH/HgateCensusAssembly.lean` (ns `QIQTH.HgateCensusAssembly`): `hDaLimLU_from_hgate_census`
= the verbatim ~40-binder `hDaLimLU_from_hgate` signature with the atomic per-u `hPd2conv`
binder (viii) replaced by the 14-binder per-u sliver census + germ links (`hPd2conv_perU`'s
block; no collisions); body = one application. Identical `DaLimLUGoal` conclusion.

Assembly's surviving labelled inputs: `hgate` (M2 derivation) · `dataAmp.hD2Hexpand` (→ the
matched sliver carries) · `hfull_pd1`/`hfrozen_pd1` (germ links: frozen → the assembly's OWN
`hQ1` binder, internal discharge = J4-367; full → banked `hfam_v2`, carries not yet assembly
binders, deferred as a lateral trade). std-3; raw 0; build 27s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-367 (7a037a3d): hfrozen_pd1 DISCHARGED INTERNALLY — zero new labels

`QIQTH/FrozenGermInternal.lean`: `fbulkInt` (hQ1's RHS as a semireducible def — hQ1's conclusion
IS the fbulkInt germ definitionally) + `hDaLimLU_from_hgate_census_v2` (fbulk specialized,
hfrozen_pd1 rebuilt internally from the assembly's own hQ1/V/hVopen/hV0). Assembly's surviving
labels: hgate · dataAmp.hD2Hexpand · hfull_pd1 (needs hlin/hD1 first — deferred). std-3; raw 0.

## ★ SOL CONSULT #15 (hgate): THE SIXTH INTERFACE-SHAPE FINDING — hgate as banked is FALSE

Q1 VERDICT: the τ-UNIFORM `hgate` binder (P with no τ-growth) is UNSATISFIABLE for the concrete
N=1 witness — the residual term τ·(Δu₁)·G grows linearly in τ while Q(r²/τ)·G_{4/3} stays
bounded per (p,q). The banked C(1+t) in the width-2 capstone was a GENUINE affine term, not
slack. HONEST SHAPE: `∃ P₀ P₁ ≥ 0, |heatOp …| ≤ (P₀+P₁τ)·(quadPoly(r²/τ))·G_{(4/3)τ}` on-gate;
threads through the width absorption UNCHANGED (E₀:=A·P₀, E₁:=A·P₁ — hEdom_of_quadPoly_
residual_width already emits (E₀+E₁τ); only the E₁=0 hard-coding in the wrappers needs the
affine variant).

Q2 ROUTE (a)+(c-small), 4 bricks: (1) the pure quadratic grading helper grade₂(x)=1+√x+x+x√x+x²
≤ 5·quadPoly(x) (via √x≤1+x, x√x≤x+x²); (2) the raw affine on-gate residual estimate at the
pre-absorption width w₀<4/3 (reuse hCoeffU0_vanVleck + uniformCoeffLinear_bound + the N=1
residual decomposition slice as black boxes; ⚠ |u₁|≤C₁r does NOT bound Δu₁ — reuse the _lin
chain's internal uniform DERIVATIVE bounds; τ⁰ terms → A₀, the τ·Δu₁/cutoff terms → A₁; no τ²);
(3) normalize grades + the NORMALIZED width comparison w₀→4/3 (dimension constant — no bare
G₁≤G_{4/3}!); (4) the thin affine hEdom wrapper. DON'T clone the _lin chain with a width
parameter (route b) — the first irreversible width-2 absorption step poisons everything after.

Q3: publish a COMBINED ∃ (a b C P₀ P₁ S) capstone emitting BOTH the global width-2 arm AND the
narrow on-gate affine arm for the SAME S (never obtain from two independent ∃-producers —
S₁≠S₂). Internally: arbitrary-S narrow theorem under an explicit gate-facts package.

TRAPS: closure≠membership (need closure(S q) ⊆ {χ=1} plateau); the width-algebra sign
(1/(4/3)−1/(3/2)>0); type (4/3 : ℝ) explicitly; choose a,b,S ONCE (no repeated .choose).

CONSEQUENCE: the assembly's hgate binder (hDaLimLU_from_hgate/_census/_census_v2) and
hEdom_concrete_final's hgate need the AFFINE reshape — mechanical re-thread + the 4 new bricks.

---
## J4-368 (8b4b354b): THE 6TH INTERFACE FINDING REPAIRED — the affine hgate (Sol #15 executed, bricks 1+4)

`QIQTH/HgateAffineRepair.lean` (ns `QIQTH.HgateAffineRepair`), 11 decls std-3:
- Brick 1: `grade₂`/`grade_two_le_quadPoly` (≤ 5·quadPoly via √x ≤ 1+x)/`weighted_grade_le`.
- `quadPoly_width_absorb` — the P-INDEPENDENT pointwise absorption extracted standalone from the
  J4-362 chain (Cabs = √(3/2/w₀)ⁿ·(2k₁²+k₁+1)), enabling the clean mul_le_mul affine bridge.
- `AffineGateBound` (the honest satisfiable predicate) → `hEdom_concrete_final_affine`
  (E₀=P₀·Cabs, E₁=P₁·Cabs — genuinely E₁≠0) → `hEdom_vanVleck_of_hgate_affine` →
  `hDaLimLU_from_hgate_affine_census_v2` (the assembly over the affine carry; identical
  DaLimLUGoal; recomposed through the hEdom-accepting layer, not an L-stack copy).

The false τ-uniform hgate chain (J4-362/364/366/367 binders) stays banked but is SUPERSEDED as
the consumer interface. Remaining per Sol #15: brick 2 (the raw affine pre-absorption residual
estimate deriving AffineGateBound from the M2 ingredients — the CoeffU1Fix map first) + brick 3
(w₀→4/3 normalized comparison) + the combined ∃(a b C P₀ P₁ S) capstone. raw 0; build ~48s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-369 (18e99cae): SOL #15 BRICK 2 — the CoeffU1Fix MAP + the raw affine graded estimate

`QIQTH/AffineRawResidual.lean` (ns `QIQTH.AffineRawResidual`), 4 decls std-3.

### THE PHASE-1 MAP (the narrow-route cartography of the _lin chain)
(i) RESIDUAL DECOMPOSITION: `parametrixResidual_N0_O1_isolated_C2` (ResidualN0FiniteReg:297) —
    the three-term raw identity AT WIDTH 1: T1 = (1/τ)G·totalRadialO1_coeff → grade x;
    T2 = (1/τ²)G·((−1/4)Σ(g̃⁻¹−δ)vv)·w₀ → grade x²; T3 = G·Δ_{g̃}w₀ → grade 1.
    N=1: `parametrixResidual_one_split` (ResidualN1GaussianBound:145): R₁ = R₀[u]+H₀[u']+τR₀[u'].
(ii) Δu₁ CARRY: the INDEPENDENT sup-on-compact black box
    `uniformFlowLaplaceBeltrami_w0_near_uniform` (obtained CoeffU1Fix:374) — NOT derived from
    |u₁|≤C₁r. The τ-LINEAR term = the O(r) shifted-profile coefficient's √τ gain
    (CoeffU1Fix:538), not Δu₁.
(iii) FIRST POISONING: the narrow route survives to width 3/2
    (`cutoffResidualN1_uniformFlow_narrow_mixed_below_lin`, CoeffU1Fix:562, (B₀+B₁τ)·G_{3/2});
    the first irreversible width-2 step = `gaussDdim_le_gaussDdim_chart (3/2→2)` at
    CoeffU1Fix:871–874. Pre-871 reusable; the width-2 capstone poisoned.
(iv) GATE FACTS: ∃S from `gatedWitnessN1_hEboundW_le_of_good` (applied CoeffU1Fix:792): radii
    a<b<c<ρc, plateau germs (hchartGerm); off-gate vanishing =
    `HrawCampaignOne.gatedWitness_heatOp_eq_zero_offSupport` (already consumed by the affine chain).

### LANDED
`rawResidualN0_graded_quadPoly_width1` (the promoted slice, 3 per-term graded bounds) ·
`rawResidualN0_graded_quadPoly_width43` (normalized 1→4/3 fold) ·
`tauResidualN0_Or_graded_quadPoly_width1` (the τ-branch: Cc(1+τ)√x·G via √τ≤1+τ, √x≤quadPoly) ·
★ `rawResidualN1_affine_graded_quadPoly_width1` — ∃P₀P₁≥0: |parametrixResidualN 1| ≤
(P₀+P₁τ)·quadPoly(r²/τ)·G_τ at width 1, P₁ = Cc1+n²MdW1/4+L1 ≠ 0 — the inner AffineGateBound
shape. All hypotheses = pointwise instances of banked uniform bounds (no fake carries).

### RESIDUE to AffineGateBound (3 bricks)
(1) the trivial 1→4/3 affine fold; (2) HEAVY: the transport/cutoff promotion — the pre-871
slice (heatOp(gatedKernel…) = radialCutoff·∂ₜH − Δ(radialCutoff·H) + annulus estimates)
re-targeted to width 4/3 chart frame (⚠ 4/3 < 3/2: the 3/2 assembly can NOT be consumed
directly — stop at width 1 and fold); (3) the chart displacement transfer v→(p−q). Then
`hEdom_vanVleck_of_hgate_affine` consumes AffineGateBound directly. raw 0; builds 34–42s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-370 (fdbd0084): the 1→4/3 affine fold + the transport-identity promotion

`QIQTH/AffineGateTransport.lean`: `rawResidualN1_affine_graded_quadPoly_width43` (the chart-frame
inner AffineGateBound shape at 4/3; √(4/3)ⁿ into both affine coefficients) +
`heatOp_globalCutoffWitness_transport` (the pre-871 htransport of CoeffU1Fix:853–868 standalone,
over the honest carries hpt (:831) / hlap (:840–852), both discharged in-bank).

OPEN to AffineGateBound: **(2b)** the annulus width-trade ≤4/3 (bank engine 3/2-only; r≥a>0 ⟹
tradeable — new lemma) · **(3)** the v→(p−q) ambient transfer (width-4/3 near-isometry budget;
banked hdisp is the fixed 3/2→2 pairing — re-parametrize `uniformFlowExp_displacement_bound`,
C_D→0 on small balls; = J4-371). std-3 both; raw 0; build 27s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-371 (a02b23a2): the width-4/3 near-isometry budget — the ball leg, fully DERIVED

`QIQTH/NearIsometry43Budget.lean`: `uniformFlowExp_hdisp43_ball` ((5/4)·rncRadialSq(φ_q v−q) ≤
(4/3)·rncRadialSq v on the ball; the 16/15 reserve; exact mirror of the banked 3/2→2 pairing) +
`uniformFlowExp_gaussDdim_transfer_43` (G_{(5/4)τ}(v) ≤ √(16/15)ⁿ·G_{(4/3)τ}(p−q) via
gaussDdim_le_gaussDdim_chart). NO carries — both derived from hC + IsCompact K. Direction
verdict confirmed: the transfer needs w₀·rncRadialSq(p−q) ≤ (4/3)·rncRadialSq(v) — mirrored.
Remaining to AffineGateBound: the quad transfer (poly leg, J4-372) · (2b) the annulus
width-trade · the on-gate assembly · the combined ∃-capstone. std-3 both; raw 0; build 43s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-372 (51aba6e7): the width-4/3 quad transfer + the ambient affine ball leg

`QIQTH/Transfer43Quad.lean`: `chartTransfer43_quad_from_nearIsometry` (B = (25/16)·√(16/15)ⁿ;
poly leg from the banked TWO-SIDED nearIsometry_concrete J4-361 budget — dont-undercredit) +
`ambientAffine_onBall` (the chart width-1 affine estimate folded 1→5/4 then transferred:
∃P₀P₁ ≥ 0, |parametrixResidualN 1| ≤ (P₀+P₁τ)·quadPoly(r²_z/τ)·G_{(4/3)τ}(z) on the ball —
the BALL LEG of the AffineGateBound precursor). Remaining: the on-gate glue (J4-373:
radialCutoff=1 interior + 2a transport + gatedKernel agreement) · the annulus (2b) · the
combined ∃-capstone. std-3 both; raw 0; build ~30s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-373 (9e373d31): the on-gate glue (2c) + ★ THE PULLBACK-METRIC FINDING

`QIQTH/OnGateGlue.lean` (7 decls std-3): G1 the plateau germ + the transport-RHS =
`parametrixResidualN 1` identification (ANY metric; cutoff through ∂_τ by =1, through Δ by
`laplaceBeltrami_congr_nhds`) · G2 the hpt/hlap discharges standalone (from CoeffU1Fix:831-852) ·
G3 the plateau identities `heatOp(witness) = pullback-residual` — ungated AND gated (the gate
layer = the banked `gatedKernel_heatOp_eq_of_mem_nhds`, GlobalHunifAssembly:138; no S-specific
facts beyond `S q ∈ 𝓝 p`).

★ THE FINDING (composition honestly NOT forced): the transport yields the **PULLBACK-metric**
residual (`uniformFlowPullbackMetric` frame); the J4-372 ball leg bounds the **ORIGINAL-metric**
residual — different objects (different Christoffels). Fix = the pullback-metric affine ball
leg (J4-374): instantiate `rawResidualN1_affine_graded_quadPoly_width1` AT the pullback metric —
its hdev/hcoeff/hlap carries are exactly the pullback-frame uniform bounds the compiled _lin
chain already discharges (hCoeffU0_vanVleck etc. live in the flow frame). Then the annulus (2b),
then the combined ∃-capstone. raw 0; build 24s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-374 (7a881a65): the pullback-metric affine BALL LEG of AffineGateBound

`QIQTH/PullbackAffineBallLeg.lean` (3 decls std-3). P0: the raw affine estimate is GENERIC in
(g,gi) — direct pullback instantiation; carries discharge from the banked flow-frame uniforms;
the transfer legs metric-independent. `pullbackAffine_width1` → `pullbackAffine_onBall` →
★ `gatedHeatOp_pullbackAffine_onBallPlateau` — THE ON-GATE BALL LEG: |heatOp(gated witness)| ≤
(P₀+P₁τ)·quadPoly·G_{(4/3)τ}(ambient) on ball ∩ plateau ∩ gate-interior. Remaining: the
annulus (2b, J4-375) + the ∃-capstone; the banked affine finishers then complete hgate→hEdom.
raw 0; build 29s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-375 (eda5d940): THE ANNULUS (2b) LEG at 4/3 — the 3/2 was NOT irreversible there

`QIQTH/AnnulusAffineLeg.lean` (5 decls std-3). ★ MAP VERDICT: the engine
(`cutoffResidual_narrow_tauUniform_engine`, WidthMarginEngine:529) is width-AGNOSTIC; the
general-(c,d) tail-trade was ALREADY BANKED (`invTpow_gaussDdim_le_width_annulus`,
WidthMarginEngine:142 — τ-free constant, exp(−a²/…τ) beats τ^{−k}); 3/2 is irreversible only
on the plateau (handled by the J4-374 ball leg). LANDED: the 4/3 tail-trade (const (16/a²)^k·k!)
+ the free pure-Gaussian 1→4/3 + the promoted per-term annulus bounds (value/deriv) + ★
`cutoffResidual_annulus43_bound` — the annulus leg in the exact AffineGateBound inner shape,
chart frame, no (1+t) cap, P₁ = the honest near-leg affine carry. Banked per-term suppliers
all in the pullback frame (parametrixCofactor_value/deriv_annulus_tauUniform,
pd_radialCutoff_bound_on_annulus, laplaceBeltrami_radialCutoff…annulus,
uniformFlowPullbackMetricInv_entry_uniform_bound_annulus). Remaining: the ambient v→z transfer
(J4-376; ⚠ width bookkeeping — may need the 5/4 re-instantiation of the annulus bound before
the 5/4→4/3 quad transfer) + the 3-region ∃-capstone (J4-377). raw 0; build 29s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-376 (cca9b5fc): the annulus AMBIENT transfer — all 3 AffineGateBound regions covered

`QIQTH/AnnulusAmbientTransfer.lean` (7 decls std-3). The width bookkeeping resolved via d=5/4
clones (width-agnostic proofs; constants (20/a²)^k·k!, √(5/4)ⁿ) → the 5/4→4/3 ambient transfer
(annulus ⊂ ball via b<r₁) → ★ `gatedHeatOp_affine_onAnnulus` (the shape-match was DEFINITIONAL
at the pullback pair). Regions now: plateau (J4-374) · annulus (THIS) · far (off-support
vanishing, to confirm in the capstone). J4-377 = the 3-region ∃-capstone: region split +
r₁-min + the carry discharges (hpt/hlap/hS/hEnear/hHann/hDHann/uniforms) + coefficient max ⟹
AffineGateBound DERIVED ⟹ the banked finishers ⟹ ★ the hgate label RETIRED. raw 0; build 36s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-377 (499db5f8): the 3-region stitching of AffineGateBound

`QIQTH/AffineGateCapstone.lean` (3 decls std-3): C1 `expPoint_of_mem_closure` (the _of_good
hclos mirror) · C2 `gatedHeatOp_eq_zero_exterior` (the collar b<‖v‖≤c vanishing — NOT empty;
cutoff-zero germ + heatOp locality) · ★ C3 `affineGateBound_of_legs` — given the two UNIFORM
leg bounds, AffineGateBound follows with (max P₀, max P₁); consumes directly into the census_v2
assembly step (vii). C4 honestly deferred: the banked legs are per-(q,v,τ); the residual gap to
an unconditional hgate = THE FLOW-FRAME UNIFORMIZATION (J4-378 — the suppliers are the banked
compact-K uniforms the compiled chain already uses) + the census data piles. raw 0; build 27s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-378 (12bd6525): the flow-frame uniformization — THE PLATEAU LEG UNIFORMIZED

`QIQTH/LegUniformization.lean` (2 decls std-3). THE SUPPLIER MAP: the plateau (P₀,P₁) is fully
ALGEBRAIC in the compact-K uniforms — Md ← uniformFlowPullbackMetricInv_dev_uniform · Cc0 ←
hCoeffU0_vanVleck · L0/L1 ← uniformFlowLaplaceBeltrami_w0_near_uniform (@u, @u') · Cc1 ←
uniformCoeffLinear_bound · W0/W1 q-indep sups · hpt/hlap glue leg-agnostic. LANDED:
`plat_residual_uniform_width43` (single (ρ,P₀,P₁) over K) + ★ `gatedHeatOp_plateau_uniform`
(the hplat_uniform in the EXACT affineGateBound_of_legs binder shape). ANNULUS residue
(J4-379): the τ-affine Kcof/Kder re-fold (mirror the B₀/B₁ step of
cutoffResidualN1_uniformFlow_narrow_mixed_below_lin, CoeffU1Fix:589-626) + the width-5/4-QUAD
hEnear (lift hwidth1, fold 1→5/4); then U4 (both legs + the _of_good choice shell +
hEdom_vanVleck_of_hgate_affine) RETIRES hgate. raw 0; build ~2-3min. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-379 (51e20fcc): THE ANNULUS LEG UNIFORMIZED — both legs uniform over K

`QIQTH/AnnulusUniformization.lean` (3 decls std-3): `width1_residual_uniform` (the hwidth1
lift) + `hEnear_uniform` (1→5/4) + ★ `gatedHeatOp_annulus_uniform` (FULL: six suppliers once,
the τ-affine B₀/B₁ re-fold by ring, the leg-agnostic glue reused — the exact hann binder shape).
BOTH width-4/3 QUAD legs now uniform (plateau cp262 + annulus THIS). A3 blocked structurally:
each leg ∃-chooses its own (a,b); the stitch needs ONE pair. J4-380 = the common-(a,b) shell:
∀-(a,b) leg restatements + the ConstRadiusGateExport hgoodC bundle re-pointed ⟹ AffineGateBound
concrete ⟹ hEdom from geometry ⟹ ★ hgate RETIRED (residual inputs then only smoothness/gauge/
frame + banked hCoeffU0/hCoeffLin1). raw 0; build 37s. NOT a₁ = R/6 (CONDITIONAL).

---
## ★★★★ J4-380 (c0f9708b): THE hgate LABEL RETIRED — hEdom DERIVED FROM GEOMETRY

`QIQTH/CommonGateShell.lean` (4 decls std-3): the ∀-(a,b) leg restatements + ★
`affineGateBound_concrete` (one common (a,b)=(m/8,m/4), the constant-radius gate, the six gate
facts from the chart germ, `affineGateBound_of_legs` applied) + ★★★★ `hEdom_from_geometry` —
the width-3/2 hEdom ∃-shape for the CONCRETE vanVleck gated witness from GEOMETRY ONLY:
smoothness (hg/hC/hw) + gauge (hdg0/hg0) + frame (hframeK/hinvF/hgnd/hgsymm) + compactness
(hK). hCoeffU0/hCoeffLin1 discharged INTERNALLY. NO hgate carry.

**THE SOL-#15 REPAIR ARC (J4-368..380) IS COMPLETE**: the false τ-uniform hgate binder (the 6th
interface-shape finding) → the affine repair (368) → the raw affine graded estimate from the
pre-absorption CoeffU1Fix slice (369) → the folds/transport (370) → the 4/3 near-isometry
budget + quad transfer (371-372) → the on-gate glue + the pullback-metric finding (373-374) →
the annulus at 4/3 (375-376) → the 3-region stitching (377) → the flow-frame uniformization
(378-379) → the common-(a,b) shell + the geometry-only hEdom (THIS). The on-gate carry is
DERIVED, not assumed.

**HONEST DISTANCE**: a₁ = R/6 remains CONDITIONAL. The remaining labelled surface of the
census assembly (hDaLimLU_from_hgate_affine_census_v2): the (a,b)-threading (the assembly
fixes (a,b); the geometry ∃-chooses them — restate ∃-style, J4-381) + the ~40 census carries
(the hQ1/W2 differentiation-under-∫ family, the integrability/measurability piles, the √ε
sliver census incl. dataAmp.hD2Hexpand) + hfull_pd1 + the E-combination carries + the data
piles (dataLevi, the dominations) + the final a₁ composition. raw 0; build 32s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-381 (8229507b): the geometry hEdom threaded into the census assembly

`QIQTH/CensusGeometryThread.lean`: ★ `hDaLimLU_from_geometry_census` — from GEOMETRY ONLY,
∃(a,b,S): (the census (ii)-(ix) minus (vii) at that gate) ⟹ DaLimLUGoal at the vanVleck
witness. NO circularity; the hEdom shapes matched VERBATIM (zero glue); the hEdom step (vii)
is GONE from the labelled surface. THE REMAINING CENSUS INVENTORY (all at the geometry-chosen
gate): (ii) hQ1/hFmeas/hFint/hF'meas/bnd/hbdd/hbound/hdiff (W2) · (iii) aa/haa/hau/hUTle
(arithmetic) · (iv) C/dataLevi · (v) wA/CA/wA2/CA2 + hAdomHeat/hAdom2 + 4 measurabilities ·
(vi) τ₀/dataAmp (hD2Hexpand)/hεaa/hετ₀ · (viii) hPd2conv (banked corollary; per-u
instantiation) · (ix) hDa/hLap/hLapZ/hEZ/hLapS/hES. Next: pile (v)+(iii) (J4-382 — the
dominations from the derived hEdom bound + banked suppliers), then (ix) integrability follows.
raw 0; build 25s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-382 (3d672268): census piles (iii) + (v)-heat discharged

`QIQTH/CensusDominations.lean`: `timeWindow_facts` ((iii) — U=Ioo(T/2)T, aa=T/2) +
`hAdomHeat_from_hEdom` ((v)-heat — wA=3/2, CA=(E₀+E₁T)·√(3/2)ⁿ from the derived hEdom at p=0;
the same E₀/E₁ feed step (vii) and hAdomHeat). HONEST: hAdom2 CARRIED (the banked bound is the
divergent-strip crude τ⁻¹ shape; route = the moment-aware WideSliverBoundary campaign) + the 4
s-slice measurabilities CARRIED (supplied nowhere in-bank; J4-383 = the compositional supplier).
raw 0; build 46s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-383 (d58db818): all 4 census s-slice measurabilities supplied

`QIQTH/SliceMeasurability.lean` (7 decls std-3): the route-(a) continuity discharge on the
banked InnerMeasFubini stack — `sliceMeas_of_jointCont` (the reusable core) + the 4 exact
census binders (hmeasLo/Hi + hmeas2Lo/Hi; the Hi τ→0 endpoint via Ioo_ae_eq_Ioc). Pile (v)'s
measurability residue → TWO joint-continuity atoms (hHeatCont/hSecCont on Ioc 0 T ×ˢ univ;
J4-384 lifts the banked box-continuity towers local-to-global) + the standing hBcont carry.
raw 0; build ~30s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-384 (a027bb4c): the strip joint-continuity atoms via box lifting

`QIQTH/JointContinuityAtoms.lean` (3 decls std-3): `stripContOn_of_boxes` (the unconditional
local-to-global lift, pure topology, f opaque) + `hHeatCont_of_boxes`/`hSecCont_of_boxes`.
Inventory: the banked box towers are conditional (gate-local identity + explicit-formula
continuity) and slice the OPPOSITE slot — pile (v) residual = the box-family carry + hBcont.
raw 0; build 25s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-385 (5b6d0850): census pile (iv) dataLevi REDUCED to two carries

`QIQTH/DataLeviDischarge.lean` (2 decls std-3): all 9 LeviSeriesLocalData fields at the
concrete vanVleck heatOp discharged via the banked builder (iterE measurability · iterConvW
bound · summability · integrability · leviSeries termwise + envelope) + hEzero from geometry.
Surviving: hpkgBound (banked at the literal constGate, J4-316) + hEmeas (banked fixed-gate,
tripleHEmeas_concrete_v4). hBcont does NOT fall out (honest). raw 0; build 25s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-386 (b5fc5dd8): census pile (ix) — the z-leg integrabilities discharged

`QIQTH/ECombinationDischarge.lean` (3 decls std-3). VERDICTS: hDa/hLap NOT definitional (the
census bodies = the banked W2 representation outputs hDa_threaded/hLap_threaded — honest
carries with banked routes). LANDED: `integrable_of_two_gaussDom` (the two-Gaussian product
workhorse via gaussDdim_pair_integrable) + `hEZ_windowed` (hAdomHeat × Levi envelope) +
`hLapZ_from_dom` (the laplaceBeltrami-slice domination; the hAdom2 bridge open per D3).
hES/hLapS = windowed-supplied; the ∀u widening = J4-387. raw 0; build 25s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-387 (bd8965c3): the (ix) s-legs widened to ∀u

`QIQTH/ESLegWidening.lean` (3 decls std-3): `intervalIntegrable_of_deg` (the degenerate case
closed UNCONDITIONALLY — reversed interval ⊆ {s≤0}, Levi vanishes) + `hES_all`/`hLapS_all`
(the exact ∀(m,u) census binders; u>0 case at the ceiling Tc:=u via the every-ceiling carries
hAdomEvery/hLapDomEvery/hFdomEvery — the honest hglobal-style structure; the laplaceBeltrami
slice fed directly). Pile (ix): z-legs (J4-386) + s-legs (THIS) + the hDa/hLap banked-route
carries. J4-388 = the every-ceiling families (hAdomEvery = a thin wrapper over the T-uncapped
hEdom; hFdomEvery = the ∀t hpkgBound re-run). raw 0; build 26s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-388 (6686a7d2): the every-ceiling families + THE F3 UNLOCK

`QIQTH/EveryCeilingFamilies.lean` (6 decls std-3): hAdomEvery from geometry (the uncapped
affine hEdom) · hFdomEvery from the ∀t' hpkgBound (ONE carry, every ceiling) · ★ THE F3
UNLOCK: τ = u−s ≥ εₘ on the pairing interval ⟹ the crude C·τ⁻¹·G second-derivative bank
becomes (C/εₘ)·G — the lower-capped engine v2 + `hLapS_all_capped` end-to-end · 
`hES_hypothesis_light` (hES from geometry + {hEdom, 2 dataLevi carries, hmeas}). Residual
s-leg carries: hEdom/hpkgBound/hEmeas (banked) + the crude hAdom2 bank (now consumable) +
the ∀u hmeas slices (J4-389 — check the J4-383 SliceMeasurability machinery first).
raw 0; build 28s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-389 (f6279d3b): the ∀u hmeas slices discharged

`QIQTH/AllUSliceMeas.lean` (3 decls std-3): the hmeas carries ARE J4-383 instances modulo the
∀u dichotomy (degenerate window ⊆ {s≤0}, Levi vanishes, a.e.-0) + the ceiling Tc:=u +
the full-laplaceBeltrami first factor. `pairingSlice_aesm` (generic) + both instantiations
(exact carry shapes). Carries: hFzero (banked) + hHeatContEvery/hBcontEvery (banked box-glue) +
hLapContEvery (the ONE new atom — J4-390 mirrors hSecCont_of_boxes). raw 0; build 46s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-390 (4fe6901f): the r2 continuity atom CLOSED

`QIQTH/LapContBoxGlue.lean` (3 decls std-3): hLapCont_of_boxes + hLapContEvery_of_boxes (the
exact AllUSliceMeas carry; one Tc-generic box family) + hmeasLapLevi_from_boxes (the hmeas
resting on {box family, hFzero, hBcontEvery} only). Both continuity atoms → the SAME box shape.
raw 0; build 43s. NOT a₁ = R/6 (CONDITIONAL).

## ★ SOL CONSULT #16: THE ENDGAME ASSEMBLY ORDER (recorded 2026-08-07)

Q1 THE DAG (no linear order): geometry → G₀(gate discipline: ONE rcases, all suppliers
gate-generic then specialized; never transport literal-constGate facts through .choose) →
C (the continuity floor: non-Levi boxes → Levi iterates → uniform tail → hBcontEvery) →
D (the W2 package via SecondOrderInterchangeConcrete/witness_MemInterchange as aggregation
points — never pass the 7 carrier fields independently) → B (the hDa/hLap assemblies = wiring
after A/D) → census(ix); E (dataAmp = the matched-sliver wall, DIRECT coefficient path) and
F (per-u hPd2conv: intro u FIRST then construct the census — quantifier trap) parallel;
G₁ (per-gate census: re-run constRadius_package_and_S1 parametrically; derive hEmeas from C) →
hDaLimLU_from_geometry_census → H (a1_R6_from_labelled — one rcases skeleton).
CRITICAL PATH: C, D, E, F, G. A = only via the hDaLimLU branch (interface redesign candidate).
ABSORB (don't expose): the old global hAdom2 field, the individual measurability/W2 fields,
the fixed-gate lifts, the old hraw/hgate/hPd2conv labels.

Q2 THE WALLS: A = GENUINE (the uncapped global hAdom2 shape is generally FALSE — τ⁻¹ at z=0
is intrinsic; the capped (C/ε)·G form is the only valid consequence; the capped route works
IFF every consumer uses τ≥εₘ AND the constant may depend on εₘ at that binder position AND
no limit needs m-uniformity — THE QUANTIFIER TRAP: ∃CA2∀m vs ∀m∃CA2(εₘ); audit
hAdom2→integrability_from_dominations→hII→memLapFull; if hII is whole-interval before the
pairing split ⟹ either refactor memLapFull to assemble from pairing legs OR the moment-aware
WideSliverBoundary campaign is unavoidable — ∫τ⁻¹dτ is not rescued by widening). C(i) standard
C² analysis; C(ii) wiring (promote htransport; no global simp); C(iii) hBcontEvery = the
Weierstrass/M-test route on hmajor/hmajorSum (uniform tail ∀δ∃N∀n≥N∀x∈K — NOT ∀x∃N; term
continuity needed too). D genuine dominated-differentiation. E genuine (matched-sliver jets).
F mixed (hPd2conv_perU banked; the CConv hlin/hD1/hfull_pd1 suppliers genuine).

Q3 THE 6 BRICKS: (1) hAdom2_capped_of_crude ((C/ε)·G from the crude bank; width UNCHANGED) →
(2) the exact hII pairing-leg adapters from the capped bound (THE DECISIVE AUDIT: if the target
needs one constant ∀m, STOP) → (3) memLapFull_from_pairing_dominations (if it compiles without
the full-time hAdom2 ⟹ wall A ELIMINATED by interface weakening; if it bottoms out on the
uncapped whole-interval hII ⟹ the moment-aware campaign precedes D/B) → (4) the non-Levi box
continuity (Θ,u∈C² + htransport promotion) → (5) leviIter continuity by induction (FIXED box
through the induction) → (6) the uniform tail + hBcontEvery (the M-test; identify the tsum
ONCE). Then: the C-measurability package + the D package + the B wiring + E/F + 
geometry_census_at_gate + the one-rcases final assembly.

---
## J4-391 (e1c4b05a): THE DECISIVE AUDIT — wall A REDUCED to {capped-Lo} ∪ {MemAdjHi}

`QIQTH/CappedAdom2Audit.lean` (4 decls std-3). The Sol-#16 brick-1/2/3 verdict:
- LO leg: τ ≥ εₘ ⟹ the capped route WORKS (`hII_lo_from_capped`; per-m constants = the good
  quantifier order; MemAdjLo per-m).
- HI leg: τ ∈ (0,εₘ) ⟹ capped FAILS; but MemAdjHi's ONLY role = the integrability
  prerequisite for `integral_add_adjacent_intervals` (the Hi SIZE dies by the matched-sliver
  √ε cancellation) ⟹ the residue's route = matched-sliver/moment-aware, NOT domination.
- ★ `memLapFull_from_pairing_dominations`: the FULL MemLapFull binder with NO uncapped
  hAdom2 anywhere — carrying only the labelled `hII_hi : MemAdjHi`. The intrinsically-false
  global hAdom2 census field is retired from the interface. J4-392 = hII_hi_from_matchedSliver
  (the [u−εₘ,u] s-profile integrability via cancellation/continuity, not τ⁻¹ domination).
raw 0; build ~30s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-392 (677f77f8): MemAdjHi REDUCED to the τ^{-1/2} moment carry

`QIQTH/MemAdjHiSliver.lean` (3 decls std-3). The τ=0 endpoint is measure-zero (irrelevant).
Route 2 landed: the moment cancellation (∫∂²G=0 ⟹ the signed z-pairing O(1) as τ→0) gives the
τ^{-1/2} profile — integrable, unlike τ⁻¹. `hII_hi_from_sliver` = the full MemAdjHi from the
BANKED hmeas2Hi_slice AESM + ONE satisfiable carry hGpow (m-uniform Cpair — the exact
moment-aware WideSliverBoundary deliverable). Wall A = {capped-Lo (banked)} ∪ {hGpow}.
raw 0; build 26s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-393 (ae955f50): SOL #16 brick 4 — the non-Levi box floor built

`QIQTH/NonLeviBoxContinuity.lean` (10 decls std-3). THE SLOT VERDICT: the banked x-slot heatOp
box machinery does NOT transport to the z-slot (different Laplacian evaluation points); the
scalar/structural pieces are slot-blind and were re-applied correctly. The N1 piece
continuities + N3 (the Δ-slice; metric factors constant at 0; the hpd2 diagonal IS the
witnessSecondXDeriv member) + N2 (the heatOp slice) + the CAP box families (exact carry
shapes) + the STRIP compositions. Carries: Θ/u regularity (satisfiable) + the witness ∂_τ-slice
+ spatial partials. J4-394 = Sol brick 5 (the z-slot leviIter induction, base = N2).
raw 0; build 46s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-394 (fb80a232): SOL brick 5 — the z-slot iterE box induction

`QIQTH/LeviIterBoxInduction.lean` (4 decls std-3). I1: NOT slot-symmetric (different integrand
argument positions) — the generic engine (heatConv_eq_smul_unitInterval + double
continuousOn_of_dominated) allowed a mechanical rebuild. The z-slot outer step + the iterE
step + the FIXED-box induction (base = J4-393 N2) + the ∀τ₀∀R∀k family for the brick-6 M-test.
J4-395 = brick 6: the box-sup of iterKernelW (the genuine step) + the Weierstrass tsum
continuity + the strip lift ⟹ hBcontEvery. raw 0; build 45s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-395 (5ed8af17): SOL brick 6 — hBcontEvery ASSEMBLED; THE C PILE CLOSES

`QIQTH/LeviMTest.lean` (7 decls std-3). M0: the consumers want the x-slot leviSeries p.1 p.2 0
— the BANKED x-slot iterE family serves it (J4-394's z-slot = other consumers). M1 (the
genuine step): the box-uniform majorant (modelCoeff time-monotone + the diagonal-peak/
width-antitone Gaussian sup → the explicit gaussDdim τ₀ 0 prefactor; summable via the banked
scaledModelCoeff_summable). M2: the Weierstrass M-test. M3: the strip + ★ hBcontEvery_of_carries
(verbatim consumer shape). hBcontEvery reduced to {hmajor (banked), htermBoxEvery (residual =
the per-rung W2 carries)}. THE C PILE (the continuity floor) CLOSES. J4-396 = the D pile (W2).
raw 0. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-396 (1371be0f): the D pile — the W2 map + two fields discharged

`QIQTH/W2Package.lean` (3 decls std-3). THE MAP: the census (ii) 8 binders = the
witness_MemInterchange binders; the _majorant sibling discharges bound/hbdd/hbound
INTERNALLY; live demand = {hQ1, hFmeas, hFint, hF'meas, hdiff}. DISCHARGED: w2_hFmeas +
w2_hF'meas (InnerMeasFubini patterns at the field-derivative kernels) + w2_measPack (the
absorption rule). THE FAMILY IDENTITY CONFIRMED: the per-rung Levi carries run on the same
Fubini engine. Residue: hQ1/hFint/hdiff (named banked routes; τ≥εₘ on the truncated window
helps hFint). J4-397 = finish D + fire the reduced-interface MemInterchange. raw 0; build 28s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-397 (baa3300f): THE D PILE FIRES — all 8 census-(ii) binders routed

`QIQTH/W2Finish.lean` (4 decls std-3): w2_hFint (the capped template at the τ≥εₘ floor) +
w2_hdiff (the innerZ re-export; bundled hInnerData) + w2_hQ1 (pd_heatConvFrozen_interchange;
bundled hFrozenData) + ★ memInterchange_at_gate (the verbatim MemInterchange member fired
through witness_MemInterchange). With J4-396: the (ii) block routes entirely to named honest
carries. raw 0; build 29s. NOT a₁ = R/6 (CONDITIONAL).

## ★ SOL CONSULT #17 (recorded 2026-08-07): THE FINAL WALLS + THE E→A→B PATH

THE CRITICAL PATH: E (dataAmp) → A (hGpow) → B (hDa/hLap); F1 + G₁ parallelize; H waits on
B/F/G₁. THE KEY VERDICT: **do NOT start a new second-order moment-cancellation development —
the existing matched-sliver bank IS the hGpow mechanism** (the SliverBoundOnCollar B/√τ shape
is analytically the same pairing after the chart identification; the cancellation ladder:
raw ‖∂²G‖₁ = τ⁻¹ → center-subtraction Lipschitz = τ^{-1/2} → O(1) would need uniform-C² data
that is unnecessary). The DaLimEasyTranche B√εₘ CANNOT be inverted to the pointwise hGpow —
use SliverAssemblyMatched directly.

A-BRICKS: A1 `leviSecondPairing_eq_matchedAssembly` (the target-identification bridge — an
EQUALITY/rewriting brick, all slot conversions HERE, no estimates) → A2
`leviSecondPairing_le_invSqrt` (instantiate SliverBoundOnCollar/TailMatched/OffCollarMatched/
AssemblyMatched; ⚠ fixed collar constants; εₘ ≤ ε*; do NOT use τ≥εₘ — destroys m-uniformity)
→ A3 the hGpow packaging + MemAdjHi + memLapFull closure (no new analysis).

E-BRICKS: E1 the geometry bundle {hcenter + hjets + sliver-hgate} (banked C⁴ + expPullback_hpd2
+ kappa_eq_one_sixth (orient ONCE) + the J4-341..347 Gauss legs; wrappers not new coordinates;
MEDIUM) → E2 {L_A_chart + hcubic-sat} (the genuinely-analytic brick: ONE fixed collar radius,
ONE compact derivative bound, ONE Taylor remainder, r≤1 absorption; L_A_chart from the explicit
A_chart formula NOT from hBcontEvery; HIGH) → E3 the AmplitudeDerivativeData assembly
(factor-by-factor named identities; NO rewriting under integrals; MEDIUM-HIGH elaboration risk).

B: TWO bricks (hDa_census_from_threaded then hLap_census_from_threaded — separate the
debugging surfaces; exact census binder order). F: F1 hlin side-conditions (PARALLEL-SAFE now,
from D+C) → F2 hD1 (HD1SliverRoute; may wait on E3) → F3 hfam_v2 + hfull_pd1 (keep hlin/hD1/
hfull_pd1 as named exports). G₁/H TRAPS: radius-witness coherence (one gate witness across
hpkgBound/hEmeas/hfam_v2 or explicit monotonicity bridges); the existential-constant order
(Cpair BEFORE the m,s binders; no εₘ⁻¹ leakage); strict endpoints (hGpow only on (u−εₘ,u) —
never manufacture τ=0); z-slot verification on every reused C theorem; NO early rcases
(gate-local packages first, ONE rcases at the end); label elimination (no hidden uncapped
hAdom2, no stale fixed-radius packages in context); per-brick audits on E3/A3/B2/F3/H.

THE SEQUENCE: J4-398=E1 · 399=E2 · 400=E3 · 401=A1+A2 · 402=A3+closure · 403=B1 · 404=B2 ·
405=F1 · 406=F2 · 407=F3 · 408=G₁+the one-rcases final assembly. The remaining analytic risk
is CONCENTRATED in J4-399..401; everything after hGpow is interface/gate-discipline work.

---
## J4-398 (6224b3dc): SOL #17 E1 — the amplitude geometry bundle

`QIQTH/AmpGeometryBundle.lean` (7 decls). hcenter LANDED (rhoRatio_center ρ(τ,0)=1 + the
qz0=qc0 anchor) · sliver-hgate LANDED (the collar⊆gate-ball wrappers incl.
not_collarRegime_of_radius) · hjets SHAPED (HjetsShape + hjets_assemble + the honest residual
census: the global ∀x first-jet + general-base hVP/hPsq/hVQ — base-0 banked; general-base =
the J4-156-class residual). E2 HANDOFF: the collar wrappers confine supports;
cubic_gaussian_moment_witness banked; ρ=1 fixes the L_A_chart base; hqLip consumes hdisp.
raw 0; build 30s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-399 (9f295e78): SOL #17 E2 — THE HIGH-RISK BRICK CLEARED

`QIQTH/AmpQuantBundle.lean` (10 decls). Q1 the shared derivative bound · Q2 ★ L_A_chart
(chartAmp_base_lipschitzOn_ball = the named L_g) + Aamp_times_F_lipschitz (the EXACT hqLip
shape) · Q3 ★ the quadratic Taylor remainder + r≤1 absorption + the banked moment re-export ·
the honest censuses {hAmpC1,hLρ,hMA,hLevi} ∪ {hAmpC2,✓,✓}. NO HARD WALL — the one reduction:
the base-varying Φ∘W_bv C¹/C² composition (E3's first job; W_bv C²-at-0 banked). E3 handoff:
M_ρ≤collarK banked (rhoRatio_le_collarK); L_ρ = the K·C_r·c²/4 D2-gradient carry; the wiring
into amplitudeDataOn_concrete → amplitudePackageOn_sliver_bound → hbnd_concrete_v2. raw 0.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-400 (8e202a99): SOL #17 E3 — the dataAmp assembly

`QIQTH/DataAmpAssembly.lean` (11 decls). D1 the Φ∘W_bv BASE-slot composition (hAmpC1/hAmpC2
UNCONDITIONAL at base 0; L_A landed) · D2 all three (M_ρ re-export · ★ L_ρ LANDED (exp of a C²
exponent) · M_A local) · D3 ★ concrete_hqLip_of_carries (the EXACT hqLip field, Lq explicit) ·
D4 the honest census {hMAcollar, hLevi, hiso, hjets, hmeas} + THE HONESTY NOTE: the
unrestricted census-(vi) dataAmp is NOT constructible at the true chart (hV0 false off-flat,
J4-351/356) — the assembleable object is the COLLAR-RESTRICTED AmplitudeDerivativeDataOn
(hD2Hexpand via hD2HexpandOn_concrete; the assembly inverts the J4-356 reduction). A1 handoff:
the concrete amplitudes + collar hD2Hexpand + hqLip feed amplitudePackageOn_sliver_bound;
residual = compactness bookkeeping. raw 0; build 26s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-401 (b30b967a): SOL #17 A1+A2 — the hGpow bridge (the last wall BRIDGED)

`QIQTH/GpowBridge.lean` (8 decls). A1 the equality bridge (the pairing = the matched term-1
collar/off-collar pair + gradient + mass; carries hon/hoff + integrabilities) · A2 the per-τ
K₁τ^{-1/2}+K₀ bound (sliver_term1_full_matched — the banked center-subtraction IS the
τ⁻¹→τ^{-1/2} improvement; NO new moment development per SOL #17) + invSqrt_absorb (ONLY τ≤ε*)
+ ★★★ leviSecondPairing_le_invSqrt (∃Cpair before the m,s binders — the EXACT m-uniform hGpow
shape). Remaining (hGpow_bridge_handoff): the concrete-witness slot instantiation
(hon/hoff/hcomp/hf2bound/hf3bound) + hKnonneg + the s=u endpoint. J4-402 = A3 closure.
raw 0; build ~20s. NOT a₁ = R/6 (CONDITIONAL).

---
## ★★★ J4-402 (cfdf8487): SOL #17 A3 — WALL A CLOSED (modulo enumerated carries)

`QIQTH/GpowClosure.lean` (8 decls). C1 the concrete slots (hon_concrete from
sliverIntegrand_on_collar · hcomp_concrete · the per-(τ,s) inner bound at the witness) · C2
K_nonneg + the m-uniform Cpair · C3 the Ioo→uIoc endpoint upgrade + ★★★
`memLapFull_from_gpow_chain` — the FULL threading (le_invSqrt → hII_hi_from_sliver → MemAdjHi
→ memLapFull_from_pairing_dominations ⟹ MemLapFull; NO uncapped domination anywhere). The
surviving carries enumerated (per-s slots + hgate + hEndpoint + continuity — all satisfiable).
**ALL THE SOL #16/#17 ANALYTIC WALLS ARE NOW BRIDGED/CLOSED.** The remaining surface = the slot
discharges (J4-403) + B (hDa/hLap) + F (per-u census) + G₁ + H. raw 0; build ~50s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-403 (0afb6dca): the wall-A slot discharges + the m-uniform aggregation

`QIQTH/SlotDischarges.lean` (10 decls). S1 SEVEN slots (hqz/hqzmeas/hgate/h0/hf2bound/
hf3bound/hcomp — from the DataAmpAssembly hqLip data, the collar wrappers, rhoRatio_center,
the dominator mechanism, hcomp_concrete) · S2 ★ hinner_window_of_slotBound (THE QUANTIFIER
TRAP RESOLVED: the constants before m,s; hslot over all 0<τ≤τ₀, never over m; no εₘ in K₁/K₀)
· S3 memLapFull_from_slotBound. THE RESIDUAL LIST (machine-checkable): {hslot, hcap
(satisfiable), hEndpoint (measure-zero), hcensus}. raw 0; build 33s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-404 (739fee86): SOL B1+B2 — the (ix) hDa/hLap census wiring

`QIQTH/HDaHLapWiring.lean` (2 decls std-3). B1 (hDa via T1a per-u; the 8 time-Leibniz carriers
honest — the w2 bank is field-side; the maximal honest reduction) + B2 (hLap via T1b: ★
hpdpdH_slice = rfl (α-equal unfold); hInterchange discharged on U by memInterchange_at_gate;
hgi/hΓ from geometry; hpdpdZ/hII_lo → the banked dominations). (ix): hDa/hLap → engines ·
hEZ/hLapZ banked · hES/hLapS windowed (∀u open). J4-405 = F1 + the widening. raw 0; build 26s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-405 (597e0021): SOL #17 F1 + the ∀u-tail widening

`QIQTH/PerUProviders.lean` (5 decls std-3). P1 `hlin_field_concrete` (the facade hlin field at
the concrete pair; hProv = the 7 bundled satisfiable diff-under-∫ legs = the w2_hQ1 hFrozenData
shape on the diagonal window) · P2 the MemInterchange ∀u-tail (★ the degenerate leg
UNCONDITIONAL — both sides collapse to 0 via Levi vanishing; memInterchange_widened).
J4-406 = F2 (hD1 via HD1SliverRoute). raw 0; build 48s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-406 (51dd8e29): SOL #17 F2 — the concrete hD1 fired

`QIQTH/HD1Concrete.lean` (5 decls std-3). The census map: sSet=univ + fbulk=fbulkInt (banked)
+ gcoef definitional + hb/hbulk_tendsto DISCHARGED (the primitive route; the hGint carry) +
the 3 analytic carries (order-2 sliver shapes). ★ THE CORRESPONDENCE CONFIRMED: the hD1
census IS the Pd2ConvPerU per-u census (identical family). ★ hD1_concrete FIRED from
hD1_conditional. J4-407 = F3 (hfam_v2 + hfull_pd1 + the tuple). raw 0. NOT a₁ = R/6
(CONDITIONAL).

---
## J4-407 (c91825c9): SOL #17 F3 — THE F PILE CLOSES

`QIQTH/PerUCensusTuple.lean` (3 decls std-3): hfam_v2_concrete (fired from hlin+hD1) +
hfull_pd1_fired (the exact per-u germ) + ★ hPd2conv_perU_fired (the exact binder (viii);
sSet=univ, hb/hbulk_tendsto discharged, fbulk=fbulkInt). The census plumbing MECHANICALLY
CLOSED through F3. Residual carries: hProv(7) + hGint + hbulkderiv/hsliver/hcont (shared) +
data fields + hfrozen_pd1 (via hQ1; route G₁ through census_v2). raw 0. NOT a₁=R/6 (COND).

## ★ SOL CONSULT #18 (recorded 2026-08-08): THE FINAL ASSEMBLY ARCHITECTURE

THE VERDICT: the capstone path = semantic data → the analytic carriers specialized AT THE
LITERAL constGate → the seven v3 slots → `A1R6SlotAdapters.a1_R6_slots_AT_GATE` → the public
two-jet AT THE LITERAL constGate. Do NOT route through the existential geometry gate; do NOT
wrap a1_R6_from_labelled (its stale linear-hraw binder disqualifies it — callers would have to
supply the old type; keep cp224 as a legacy/regression theorem). The conclusion stays the
EXACT a1_R6_slots_AT_GATE codomain (no existential-gate public shape).

Q2: RE-RUN at the literal constGate (constRadius_package_and_S1 + tripleHEmeas_concrete_v4 +
the parametric census builders) — NEVER eliminate cp264/cp265's ∃ and try to identify the
opaque witnesses with G₀ (transport = gate equalities + dependent-record rewrites = fragile).
Local notation G₀; all coherence definitional.

Q3 THE PUBLIC PACKAGES (the absorption rule): {GeometryFrameData (derives hGauss/G₀/hEdom/S1
internally) · LeviDuhamelConvergenceData (the honest hDuhamel/trio conditional) ·
CollarAmplitudeDataOn (the RESTRICTED object — never unrestricted AmplitudeDerivativeData) ·
GpowSlotData (the A-side; or a derived MemLapFull directly) · TimeLeibnizData (the 8 T1a
carriers + T1b leftovers) · W2FeederData (hProv/hGint/sliver carries; ONE owner per fact) ·
RicciSourceData (temporary-but-honest until ricciSourceData_from_geometry is banked)}.
FORBIDDEN in the final signature: hraw, hgate, a/b/S witnesses, unrestricted
AmplitudeDerivativeData, raw hD2Hexpand/hPd2conv/hGauss, hcap/hEndpoint, gate equalities.

Q4 THE CUT: J4-408 = ConstGateAssemblyData + constGate_assembly_data_from_data (the fixed-gate
G₁/census bridge; copy the hEdom proof one layer earlier if only the ∃-form exists) · J4-409 =
FinalA1SlotsAtConstGate + finalA1Slots_from_data (each field = one exact banked call) ·
J4-410 = the one-line public a1_R6_from_data. TRAPS: the legacy-label audit (#print the
signatures; no hraw/hgate/witness survival), the ∃-elim order (fix G₀ first, rcases once),
restricted-vs-unrestricted amplitude (no silent typeclass/simpa regression), the m-uniform
quantifier order preserved, the gate term syntactically identical everywhere, the final
#print axioms audit.

---
## J4-408 (8a1f2a29): SOL #18 brick 1 — the fixed-gate G₁/census bridge

`QIQTH/ConstGateAssembly.lean` (std-3). THE SLOT AUDIT: a1_R6_slots_AT_GATE = {hDuhamel ←
hDuhamelSlot_AT_GATE (TruncatedDuhamelCore) · hDConv ← hDConv_W1free (hDaLimLU_from_labelled
@ constGate + hbdryLU_CONCRETE) · hCConv ← hCConvSlot_AT_GATE_v2 · htr ← htr_adapter}. THE
hEdom VERDICT: the ∃-witnesses don't defeq-match the constGate — the layer is
hEdom_vanVleck_of_hgate_affine (explicit S,a,b); the constGate IS the census gate shape.
ConstGateAssemblyData: hEdom/hEz/hS1 REAL; hpkgBound/hmemS0/hopenS0 honest carries
(satisfiable via constRadius_package_and_S1). J4-409 = the slots bundle. raw 0; build 27s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-409 (62f391b8): SOL #18 brick 2 — the slots bundle + the firing lemma

`QIQTH/FinalA1Slots.lean` (2 decls std-3). FinalA1SlotsAtConstGate (the 3 verbatim slots + htr
at the concrete Ricci) + finalA1Slots_from_data (the 3 slots ← the ONE A1R6GateSlots package;
htr ← the single hGauss carry) + ★ .fire (the a₁ TWO-JET from {the J4-408 base + this bundle +
base geometry}; the Ricci substitution by defeq). J4-410 = the one-line public capstone +
the final audits. raw 0; build 27s. NOT a₁ = R/6 (CONDITIONAL).

---
# ★★★★★ J4-410 (89cb4df0): THE CAPSTONE — a1_R6_from_data

`QIQTH/A1R6FromData.lean`: **the one-line public capstone** of the a₁=R/6 campaign's
J4-363..410 window. From exactly FOUR semantic input groups — (A) base geometry/gauge,
(B) the ConstGateAssemblyData carries (the AFFINE hgate + v4 measurabilities +
hpkgBound/hmemS0/hopenS0), (C) the ONE A1R6GateSlots package, (D) the single hGauss carry —
THE a₁ TWO-JET at the literal constGate:
`heatOp … = 0 ∧ trueHeatKernel t 0 0 = (heatKernel1D t 0)ⁿ·(1 + ((∑ᵢ ricci g gi i i 0)/6)·t + t²·…)`.
std-3; raw 0; the forbidden-name audits ALL CLEAN.

## THE FINAL HONEST SUMMARY (verbatim from the capstone docstring)
a1_R6_from_data is the maximally-unconditional **CONDITIONAL** a₁ two-jet, NOT an
unconditional a₁ = R/6. What remains genuinely CONDITIONAL:
(a) the A1R6GateSlots censuses (Duhamel ~90-binder + W1-free + L2 sliver) — each satisfiable
    and largely fired by the F-pile bricks, but still binder-shaped;
(b) the ConstGateAssemblyData carries — the affine hgate (DERIVABLE via the J4-368..380 arc's
    hEdom_from_geometry at the ∃-gate, carried explicit-gate here); the v4 measurability
    carriers; hpkgBound/hmemS0/hopenS0 (satisfiable via constRadius_package_and_S1, whose
    ∃-witnesses do not defeq-match a caller-chosen literal gate);
(c) hGauss — DERIVED in-bank (hGauss_pullback_concrete etc.), absorbable later;
(d) THE DEEP CONDITIONALITY NEVER CLAIMED CLOSED — the convergence-trio content inside the
    Duhamel census, and hence the a₁ = R/6 statement itself, remains CONDITIONAL.

## THE WINDOW ARC (J4-363..410, ~48 bricks, all std-3 raw 0)
cp247 all four labelled inputs resolved → cp264 the hgate label RETIRED (the 13-brick Sol #15
affine arc) → cp265-281 the census campaign (the geometry-census master + the pile discharges)
→ cp286 WALL A CLOSED (the moment route) → cp279/289-291 the C/D/E/F piles closed → cp292-294
the Sol #18 three-brick final assembly → THE CAPSTONE. THE GRIND IS PAUSED FOR USER REVIEW.
The natural next targets (user's choice): absorb hGauss into the capstone; the slot-census
firings threaded end-to-end; the constRadius parametric re-run discharging hpkgBound/hmemS0/
hopenS0; the deep Duhamel/convergence campaign.

---
## J4-411 (4ed8b4e6): the hGauss carry ABSORBED (the closing sequence 1/4)

`QIQTH/HGaussAbsorb.lean` (2 decls std-3). THE VERDICT: the banked germ IS the labelled form —
the only gap is the metric identity. `hGauss_concrete` (the instantiation bridge) +
`a1_R6_from_data_v2` (group (D) removed; the one carry = hgPull, the pullback-metric
identification). Next: (2) the constRadius absorption (J4-412) → (3) the slot threading →
(4) the Duhamel campaign. raw 0; build 43s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-412 (7e4dc40f): the (b) package carries ABSORBED (closing 2/4)

`QIQTH/ConstRadiusAbsorb.lean` (std-3). ROUTE (ii): a1_R6_from_data_v3 — hpkgBound/hmemS0/
hopenS0 + the caller (a,b,c,C) REMOVED via the ∃-consumption (the radii are load-bearing; a
parametric version would re-expose hpkgBound). THE HONESTY COST: the ∃-quantified conclusion
+ the ∀-over-gates carriers (strictly stronger supply). Added geometry-only:
hgnd/hinvF/hframeK/hw/hu. J4-413 = the slots threading (slots → the 3 census sub-carriers).
raw 0; build 28s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-413 (c9701e60): the slots threaded (closing 3/4) + ★ THE DUHAMEL CENSUS MAP

`QIQTH/SlotsThreading.lean` (3 decls std-3).

### THE T1 DUHAMEL MAP (the ~90-binder truncatedDuhamelCore_AT_GATE_FULL → 5 blocks)
- **A** hBoundaryLim ← `EnvelopeWiringLocUnif.hBoundaryLim_DONE` (BANKED).
- **B** the hDaLimLU census: the W2 family ← `w2_hQ1`/`w2_hFmeas`/`w2_hF'meas`/`w2_hFint`
  (BANKED); hEdom ← the affine layer (BANKED); the E-combination banked; gauge/nbhds
  geometry-satisfiable. RESIDUES: `hdiff` (the pointwise ∂_w-under-∫₀ᵗ∫ family) + the
  2nd-order interchange `MemLapFull`/`MemAdjLo`/`MemAdjHi` + the sliver D0/D1/hbnd.
- **C** the F2/hFII pile ← `F2FamilyDischarge.{hpar,htime,hR}_discharge` +
  `heatConvInner_intervalIntegrable_H` (BANKED).
- **D** the frozen/moving boundary lists ← `hbdryLU_CONCRETE`'s members (BANKED).

**NET: the Duhamel residual = TWO genuine carries, not 90 binders.** ⚠ DONT-UNDERCREDIT
(J4-414 checks first): the wall-A campaign (memLapFull_from_slotBound / hII_lo_from_capped /
hII_hi_from_sliver) may already cover the interchange legs — then the terminal residue =
{hdiff + the wall-A residual carries (hslot/hGpow-level) + D0/D1/hbnd}.

### T2/T3
`hCConvSlot_threaded` (the L2 census threaded; survivors in `L2Residual`) +
`a1R6GateSlots_threaded` + `a1_R6_from_data_v4` (slots → coreSlots + hDConvSlots + L2Slots).
raw 0; build 31s. NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-414 (9aa6586c): the Duhamel core threaded — the interchange COVERED by wall-A

`QIQTH/DuhamelCoreThreaded.lean` (std-3). THE D1 VERDICT PROVED IN LEAN: all three interchange
legs (MemLapFull/MemAdjLo/MemAdjHi) are covered by the wall-A campaign (memLapFull_from_
slotBound / hII_lo_from_capped / hII_hi_from_sliver — exact shapes, same witness/gate/source/
window/pdpdH). `truncatedDuhamelCore_threaded` = the FULL core with the interchange discharged
internally + the wall-A census; A/C/D carried verbatim (already residual-level). THE TERMINAL
RESIDUAL: hdiff (dominated-derivative candidate — check w2_hdiff coverage) + hslot/hGpow (the
moment wall) + hPd2conv (check hPd2conv_perU_fired coverage) + the satisfiable census. v5
deferred (cosmetic). ⚠ NEW TRAP: private lemmas are NOT pinnable from AxiomAudit (the first
budget run failed on it; public pins only). raw 0; build 30s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-415 (79623afd): hdiff + hPd2conv BOTH COVERED — the terminal surface narrows

`QIQTH/TerminalCoverage.lean` (3 decls std-3). V1: hPd2conv = hPd2conv_perU_fired VERBATIM
(threaded). V2: hdiff = w2_hdiff VERBATIM (threaded; no dominated-derivative derivation
needed). `truncatedDuhamelCore_threaded_v2` absorbs both. ★ THE FINAL TERMINAL LIST: the ONLY
genuinely open analytic input = the moment wall hslot/hGpow (+ the satisfiable data censuses).
⚠ dont-undercredit for J4-416: the GpowBridge/GpowClosure/SlotDischarges results
(leviSecondPairing_le_invSqrt / _inner_bound_concrete / hinner_window_of_slotBound) were
banked J4-401..403 — the moment wall may reduce to the concrete slot-instantiation carries.
raw 0; build 29s. NOT a₁ = R/6 (CONDITIONAL).

---
# ★★★★★ J4-416 (9933aec7): THE CLOSING SEQUENCE COMPLETE

`QIQTH/MomentWallCoverage.lean` (3 decls std-3). M1: the Cpair/hCpair/hGpow trio COVERED —
DERIVED from the core's own hslot/hcap/hEndpoint via the banked J4-401 capstone (the quantifier
trap preserved) + the uIoc upgrade. M2: hslot COVERED verbatim (the J4-403 aggregation + the
J4-402 per-(τ,s) supplier). `truncatedDuhamelCore_threaded_v3`: the trio removed, derived
internally.

## THE ABSOLUTE FINAL CONDITIONAL SURFACE (all satisfiable enumerated data)
1. The slot-instantiation carries (gpow_closure_carries: qc/Ichart/hoff + the integrabilities +
   the Lipschitz/center carries + the Gaussian-moment dominators; slot_discharge_residuals).
2. hInnerData (the z-level diff-under-∫ inputs, ← w2_hdiff).
3. The V1 per-u census (nbP/hProvP/the data fields/hGintP/hbulkderiv/hsliver/hcont/hfrozen_pd1).
4. The carried v2 census (interchange/domination/continuity/gauge/Levi + the √ε sliver).
NO genuinely-open analytic wall remains above the slot-instantiation level.

## THE TWO-DAY ARC (J4-363..416, ~54 bricks, all std-3 raw 0)
The labelled inputs resolved → the hgate retirement (Sol #15, 13 bricks) → the census campaign
→ the walls (A by the moment route; C/D/E/F closed) → the Sol #18 capstone (a1_R6_from_data)
→ the closing (hGauss absorbed · constRadius absorbed · the slots threaded · the Duhamel core
threaded · the terminal coverage · the moment wall covered).

## THE FUTURE TRANCHE (the user's menu)
(a) the concrete slot instantiation at the true witness; (b) the joint-instantiability audit;
(c) the convergence-trio content inside the carried census; (d) the v5 cosmetic bundle.
⚠ a₁ = R/6 remains CONDITIONAL — fully enumerated, not zero. THE GRIND IS PAUSED FOR REVIEW.

---
## J4-417 (2554dbc9): the joint-instantiability AUDIT — the terminal surface CLEAN

`QIQTH/JointInstantiabilityAudit.lean` (8 public decls; 6 pinned). THE TRANCHE-(b) BRICK
(user directive "do it all in the loop" — sequence (b)→(a)→(c)→(d)). The blind spot
(feedback_axiom_budget_blind_spot: budget catches axioms/sorry, NOT unsatisfiable packages)
closed at the reachable level. THE FOUR FINDINGS, ALL CLEAN:
1. **The moment-wall exponent** — hslot demands coeff·τ^(-1/2)+Sconst; the historical
   τ-uniform LINEAR ≤C·τ trap is PROVABLY ABSENT (`audit_hslot_not_linear_trap` /
   `audit_invsqrt_not_linear_trap` — depend on NO axioms at all); the demanded shape is
   satisfiable at the true Levi singularity (`audit_hslot_form_satisfiable`).
2. **The census projectors** — `gpow_closure_carries`/`slot_discharge_residuals` are genuine
   5-/4-fold conjunctions (Iff.rfl): no `:= True` conjunct, no hidden strengthening.
3. **Witness coherence** — `truncatedDuhamelCore_threaded_v3`'s codomain at the literal
   constGate is DEFEQ to `a1_R6_from_data_v4`'s coreSlots binder (`audit_coreSlots_shape`):
   same gate term, same van-Vleck witness, no radius/normalization drift.
4. **The M1 quantifier order** — ∃Cpair ∀(m,s) confirmed by inspection (machine-check
   promotion = J4-419 recommendation).
`joint_instantiability_certificate`: a machine-checked SIMULTANEOUS model of the group-(1)
shapes at one shared sign-correct parameter set. HONEST RESIDUE (not a soundness defect):
groups (2) hInnerData / (3) per-u analytic carries / (4) interchange-domination-Levi carries
need the real kernel — the convergence-trio content, never claimed closed.
Recommended: J4-418 audit_perU_shape (id-transport) + J4-419 quantifier-order extraction.
raw 0; build 84s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-418 (c188c308): findings 3/4 machine-checked + tranche-(a) PHASE 1

`QIQTH/AuditPromotions.lean` (2 decls) + `QIQTH/SlotInstantiationI.lean` (4 decls), all std-3.
**Part A (the audit promotions, both proved, no obstruction):** `audit_perU_shape` — the
threaded core's V1 per-u census binder group is VERBATIM `hPd2conv_perU_fired`'s input
(id-transport; compiles ⟹ shapes match; FINDING 3 machine-checked). `audit_hGpow_quantifier_
order` — the ∃Cpair ∀(m,s) order (Cpair BEFORE m,s = the m-uniformity) extracted standalone
from `hGpow_covered` (FINDING 4 machine-checked). The J4-417 audit is now fully machine-level.
**Part B (phase 1 at the true ρ-scaled chart witness, S-generic):** DISCHARGED: `qc` concrete
(`chartAmp·F`); `h0` centre-match FULL (`center_identity_concrete` ← rhoRatio_center, 0 ∈ K);
`hgate` radius conjunct FULL (c·√τ < r₀; z ∈ K carried). Genuinely new self-contained
instances (dont-undercredit check: the banked `amplitudeDataOn_concrete` + abstract slot
suppliers exist but nothing supplied these slots directly). NOT YET (the phase ledger in-file):
Ichart/hoff (→ J4-419 via SliverAssemblyMatched's off-collar identity), the integrabilities,
hqz/hqc Lipschitz, hcomp, hf2bound/hf3bound Gaussian dominators, AmplitudeDerivativeDataOn.
raw 0; builds 26-48s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-419 (cf7c5b6d): Ichart + hoff DISCHARGED FULLY — phase 2

`QIQTH/SlotInstantiationII.lean` (5 decls std-3). THE FINDING: the phase-1 recommended route
(Ichart := hessCoeff·G^chart·qc + a banked off-collar identity) is NOT realizable — the one
exact banked identity (`hD2Hexpand`) is conditioned ON the collar; no raw off-collar equality
exists in the bank. THE ROUTE TAKEN: the design-intended residual (GpowBridge §A2:
f₁ = Wpair − f₂ − f₃ "equals Ichart off the collar") — with `Ichart := IchartResidual` the
`hoff` identity holds pointwise-everywhere by pure `ring`, verbatim the
leviSecondPairing_inner_bound_concrete binder shape (`hoff_concrete` + the ∃-certificate
`hoff_slot_inhabited`). BONUS: `hIchart_int_concrete` (off-collar integrability) reduced to
the carried hWint/hf2/hf3. `slotInstantiation_phase2` = phase 1 ∧ the new fields.
HONEST NOTE: the chart-native geometric content re-enters at `hcomp` (the comparison leg) —
that is where the real content now sits, not in hoff. Dont-undercredit: the bank threads
Ichart abstractly (bounds only) — genuinely new. REMAINING: hqz/hqc Lipschitz (→ J4-420 via
data.hqLip + concrete_hqLip_of_carries), hcomp, hf2bound/hf3bound dominators, hWint/hf2/hf3.
raw 0; build 46s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-420 (f36cbe65): hqz/hqc + the integrability reductions — phase 3

`QIQTH/SlotInstantiationIII.lean` (9 decls std-3). hqz DISCHARGED-modulo (six factor carries)
via the banked `concrete_hqLip_of_carries` — the exact supplier, verbatim. hqc DISCHARGED-
modulo (four carries) via `collar_product_lipschitz_increment` (the two-factor core; the
three-factor `Aamp_times_F_lipschitz` carries a spurious ρ absent from qc — honest new
wiring). hqzmeas/hqcmeas via `aesm_of_lipBound` (Lipschitz ⟹ continuous ⟹ AESM; no tactics
on .choose-heavy goals). hWint/hf2/hf3 REDUCED to the explicit two-Gaussian product-domination
carries (the hAdom2cap/hFdom census shape) via `gaussDdim_pair_integrable` + `Integrable.mono'`
— confirmed NO banked lemma proves these full-space integrabilities unconditionally.
`hIchart_int_final` promotes the phase-2 off-collar integrability to the witness modulo the
domination carries. `slotInstantiation_phase3` = phase 2 ∧ the new fields.
GROUP-(1) RESIDUE: `hcomp` (THE LOCUS OF THE GEOMETRIC CONTENT → J4-421: IchartResidual −
hessGaussFactor·qc has the chart-native form + ∫_{collarᶜ}‖·‖ ≤ Bcomp/√τ) + hf2bound/hf3bound
(the odd-moment √τ extraction ∫|z_i|/(2τ)·G_τ ≍ τ^{-1/2}; route hf2bound_slot_of_dom +
abs_integral_le_of_dom + the cubic/mass Gaussian-moment family).
raw 0; build 47s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-421 (d0d28ef0): hcomp SPLIT — the geometric content isolated (phase 4) + SOL #19

`QIQTH/SlotInstantiationIV.lean` (4 decls std-3). The comparison leg via the banked
`comparison_leg_of_dom`, four legs split honestly: leg (i) `hcompDiff_int` FULLY DISCHARGED
(wiring: hIchart_int_final − `hessGauss_qc_integrable`; bounded-qc inline from phase-3 sup
carries). Legs (ii)-(iv) hDint/hdom/hmom CARRIED = the genuine geometric content. THE EXACT
OBSTRUCTION ISOLATED: the OFF-collar chart-native identity IchartResidual = hessCoeff·G^chart
·qc — i.e. the off-collar expansion of witnessSecondXDeriv (a van-Vleck jet identity); the
on-collar analogue is banked (sliverIntegrand_on_collar; hD2Hexpand is Regime-conditioned).
Dont-undercredit VERIFIED: the banked sliver machinery threads abstract Ichart /
chartNative_leading_sub_hess_norm_le bounds a DIFFERENT object.

### SOL CONSULT #19 (gpt-5.6-sol, recorded verbatim-in-substance)
RANKING: (A) FIRST — audit hD2Hexpand's Regime dependency: if Regime only selects the witness
branch/supplies chart-true rewrites, extract the UNCONDITIONAL algebraic jet lemma
Wpair = f₂ + f₃ + hessCoeff·G^chart·qc (ordinary chart/τ>0 hypotheses) and get the residual
identity by ring; legs (ii)-(iv) then collapse to the banked chart-native moment bounds. If
Regime proves cutoff constancy/domain membership/ρ-smallness/Taylor-remainder vanishing, the
extension is INVALID and a new geometric lemma is genuinely required. TRAP: never transport
the conditional on-collar equality off-collar because the formulas look algebraic; keep the
ρ-scaled chartArg/normalization/τ≠0 aligned. (B) SECOND — triangle domination D = D_W+D₂+D₃+
D_H; TRAP: the triangle inequality may destroy the cancellation improving τ⁻¹ → τ^{-1/2};
a larger constant CANNOT absorb the wrong power as τ→0; needs uniform off-collar Gaussian
tails in τ/ρ/dim. (C) THIRD — valid scheduling, removes nothing.
hf2bound CONFIRMED: abs_integral_le_of_dom + the absolute coordinate-moment family is sound
m-uniformly IF |z_i|/|z_i|³ moments (NEVER radial ‖z‖ moments — those cost √m or m); do NOT
use odd-moment cancellation (post-|·| the moments are nonzero); the cubic → C/√τ needs the
campaign's τ upper bound, integrability alone does not scale.
raw 0; build 48s. NOT a₁ = R/6 (CONDITIONAL).
