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

---
## ★ J4-422 (c8a84452): hf2bound/hf3bound + THE REGIME JACKPOT — phase 5

`QIQTH/SlotInstantiationV.lean` (12 decls std-3). **Part A:** hf2bound DISCHARGED m-uniformly
by COORDINATE moments (Sol #19 traps respected: |z_i| never radial ‖z‖; no odd-moment
cancellation) — ∫|z_i|·G ≤ (3/2)√τ gives Q = 3M/4 via the EXACT (√τ/τ) = 1/√τ conversion,
NO τ-window needed (the window is only for the Part-B cubic). hf3bound τ-uniform (zeroth
moment). Residual: hfint/hdom per-point carries (satisfiable via hf2/hf3_ptwise_dom_of_
ampBound). **Part B — THE REGIME AUDIT VERDICT = (1) EXTENDS:** hD2Hexpand consumes
Regime = collarRegime at EXACTLY THREE sites (AmplitudeDataOnCollar.lean:426-430: 0<τ, z∈K,
the chart jets); the collar ‖z‖≤c√τ / r₀ / τ≤τ₀ conjuncts are NEVER referenced; the
underlying hD2HexpandOn_concrete (:258-287) takes no collar hypothesis. THE JET LEMMA PROVED:
`ichartResidual_offcollar_form` (IchartResidual = hessGaussFactor·ρ·qc off-collar) +
`ichartResidual_sub_hess_form` (comparison integrand = H·(ρ−1)·qc). THE COLLAPSE WIRED
(`hcomp_collapsed`): the phase-4 legs (ii)-(iv) reduce from three abstract carries about an
unknown IchartResidual to ONE explicit (ρ−1) cubic-form carry + the off-collar jet supply.
GROUP-(1) RESIDUE = terminal geometric wiring only: the (ρ−1)=O(‖z‖³/τ) cubic carry
(→ J4-423 via the near-isometry budget + cubic_gaussian_moment_witness, τ-window REQUIRED
here per Sol trap iii) + the hf2/hf3 per-point hfint/hdom + the jet supply hform + the
factor/domination carries. raw 0; build 49s. NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-423 (86bd4ca6): the cubic carry DISCHARGED — group-(1) ALGEBRA CLOSED (phase 6)

`QIQTH/SlotInstantiationVI.lean` (10 decls std-3). THE POWER COUNT (written as comment, then
PROVED in `comparisonDom_moment`): ∫D = (CρMqc/4τ³)·[∫‖z‖⁵G_τ + 2τ∫‖z‖³G_τ] with the banked
k=5/k=3 moments (`pow_norm_mul_gauss_integral`, `oneD_absMoment3/5`) ⟹ the τ^{5/2} moments ÷
the τ³ prefactor = EXACTLY τ^{-1/2}; Bcomp = CρMqc·n(864√2+1)/2, τ-INDEPENDENT. `hcomp_final`
wires hDint (`comparisonDom_integrable`) + hmom (`setIntegral_le_integral`, D≥0) into
`hcomp_collapsed`. `hf2dom_at_witness`/`hf3dom_at_witness`: the a.e. dominations FULLY
discharged. Sol trap (iii) resolved cleanly: the moment C/√τ is unconditional (closed-form
Gaussian scaling); the τ-window burden sits in the POINTWISE ρ-deviation carry (R1), honestly
carried not re-proved. Dont-undercredit: rhoRatio_le_collarK correctly NOT used (on-collar
only); no banked |ρ−1| scalar bound exists (R1 genuinely open).

### THE GROUP-(1) FINAL RESIDUE — factor/sup/jet-supply carries ONLY (a MILESTONE:
### no slot identity or τ-scaling remains open in group (1))
- R1 `hdom_comp`: pointwise |ρ−1| ≤ Cρ‖z‖³/τ (near-isometry, gate-confined) × Mqc.
- R2 `hform`: the off-collar jet supply (chart jets + open gate at z ∈ K).
- R3 `hcompDiff_int`: the off-collar residual-difference integrability.
- R4 `hf2amp`/`hf3amp`: the amplitude·Levi sup bounds.
- R5 `hf2int`/`hf3int`: the integrand measurability/integrability carries.
⚠ a₁ = R/6 stays CONDITIONAL on the convergence-trio + geometric-wiring stack.
raw 0; build 49s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-424 (05e663c5): R1 PROVED confined + the off-collar S5b map — phase 7

`QIQTH/SlotInstantiationVII.lean` (7 decls std-3). **R1** `rhoRatio_sub_one_bound`:
|ρ−1| ≤ (L·n·collarK/4)·(‖z‖³/τ) on collarRegime — THE EXPONENT BUDGET: ρ = exp θ with
|θ| ≤ L·n·‖z‖³/(4τ) (two-sided `chartW0_rncRadialSq_error` + `rncRadialSq_le_nsq`);
e^{|θ|} ≤ collarK via the collar/window confinement (‖z‖³ ≤ c³τ√τ, √τ ≤ √τ₀); Cρ
τ-INDEPENDENT. THE EXACT OFF-COLLAR FAILURE (recorded for the next brick, honest): at fixed
‖z‖ = r₀ with τ→0 the factor e^{|θ|} DIVERGES — R1 alone cannot supply hcomp_final's
hdom_comp on collarᶜ. THE S5B CLOSURE ROUTE: hessGaussFactor·(ρ−1)·qc =
(z_i²−2τ)/(4τ²)·(G^chart−G_τ)·qc and `gaussDdim_replace_bound` gives
|G^chart−G_τ| ≤ (L'‖z‖³/4τ)·(√2)ⁿ·G_{2τ} GLOBALLY (no exp blow-up) ⟹ comparisonDom2
(width-2τ) + a κ=2 moment lemma → global hdom_comp2 (= J4-425).
**R5** hf2int/hf3int DISCHARGED (Integrable.mono' + compositional measurability from the
banked bundle fields). **R3** DISCHARGED (re-export). **R2** `hform_at_witness` pointwise
(the jet supply = the standing carry). **R4** GENUINELY CARRIED — an off-gate near-isometry
carry would be UNSATISFIABLE; the vacuity was deliberately avoided (the axiom-budget
blind-spot discipline in action). raw 0; build 83s. NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-425 (2228298a): the S5b GLOBAL dominator — GROUP (1) = ENUMERATED
## INPUT CARRIES ONLY (phase 8)

`QIQTH/SlotInstantiationVIII.lean` (8 decls std-3). `hdom_comp2_ptwise` PROVED GLOBALLY
(all z — no collar restriction, no exponent budget) via the exact identity `gauss_ratio_rho`
(hessGaussFactor·(ρ−1)·qc = (z_i²−2τ)/(4τ²)·(G^chart−G_τ)·qc) + the banked
`gaussDdim_replace_bound` (HeatResidualBound / GaussianMomentEnvelope.lean:389 —
|G^chart−G_τ| ≤ (L'‖z‖³/4τ)·(√2)ⁿ·G_{2τ}, the phase-7 exp blow-up ELIMINATED).
`comparisonDom2` (width-2τ) + the κ=2 moment: Bcomp2 = L'(√2)ⁿMqc·n(3328+√2)/4 — the extra
(√2)ⁿ from the coercivity step is LEGITIMATE (n fixed at the witness; the 1/√τ scaling
untouched). `hcomp_final2` = hcomp_collapsed at comparisonDom2 with hDint/hmom/hdom ALL
discharged internally — the phase-6/7 hdom_comp a.e. carry is GONE. Forced honest carries:
herr (ℓ² near-isometry cubic error, ∀z), hmin (coercivity ½r²_z ≤ r²_{Wz}, ∀z), hqcbdd.
Phase 8 = pure assembly of banked machinery (dont-undercredit: the moment tower already
carried the width parameter κ; no new tower needed).

### THE GROUP-(1) FINAL RESIDUE — SIX ENUMERATED INPUT CARRIES (the milestone):
I1 `herr` near-isometry cubic · I2 `hmin` coercivity · I3 the amplitude sups Mqc/M/Sconst ·
I4 `hform` jet supply · I5 `hcompDiff_int` wiring · I6 the .choose measurabilities.
NO open identity, τ-scaling, or domination remains in group (1).
⚠ a₁ = R/6 stays CONDITIONAL (groups (2)/(3)/(4) + the convergence trio + I1-I6).
raw 0; build 55s. NEXT: GROUP (2) hInnerData (J4-426).

---
## J4-426 (f4339d12): GROUP (2) hInnerData — 4/7 conjuncts DISCHARGED (phase 1)

`QIQTH/InnerDataInstantiation.lean` (6 decls std-3). THE GROUP-(2) BINDER MAP: hInnerData =
a 7-conjunct ∃ znb bnd per (m,i,u), a.e.-s, ∀ w∈snb. DISCHARGED: conj-2/4 (z-slice
measurabilities of dH·Lev / dHH·Lev — compositional .mul), conj-5 (Integrable bnd at
bnd := C·G_σ via the banked `envelope_integrable`), conj-7 (★ THE HasDerivAt FAMILY — new
2nd-order off/on-gate line lemmas glued by the gate dichotomy, lifting the banked first-order
`WitnessMeasDeriv.hWdiff_offGate/onGate` pattern one order up; `.mul_const` the Levi factor;
`innerZ_prod_hasDerivAt_witness` = the exact conj-7 shape). `innerData_phase1` trades the
opaque hInnerData for a strictly-lighter reduced core (bare slice measurabilities, a gate
dichotomy, a positive Gaussian width). CARRIED with plans: conj-1 znb (the collar/√ε
line-nbhd), conj-3 (first-kernel base integrability ← gate envelope one order below),
conj-6 (second-kernel Gaussian domination ← `witnessFieldDeriv2_gate_envelope` = E2, J4-427).
Dont-undercredit: the w2_* family CONSUMES hInnerData via innerZ_line_hasDerivAt — this brick
supplies it one level deeper; the first-order pattern was banked and lifted, not re-derived.
raw 0; build 47s. NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-427 (ba80b84a): the E2 envelope — GROUP (2) = ENUMERATED INPUT CARRIES ONLY

`QIQTH/InnerDataEnvelope.lean` (4 decls std-3). `witnessFieldDeriv2_gate_envelope` PROVED
(off-gate dHH = 0 banked `witnessFieldDeriv2_offGate_eq_zero`; on-gate the C₂ sup × the Levi
Gaussian C_L·G_σ) + the first-order sibling `witnessFieldDeriv_gate_envelope_prod`.
conj-6 DISCHARGED (dominator (C₂·C_L)·gaussDdim σ — the exact reduced-core shape);
conj-3 DISCHARGED (Integrable.mono' + first-order envelope + envelope_integrable);
conj-1 DISCHARGED as the carried hznb (NOT univ — the on-gate sup is genuinely local).
`innerData_phase2` = the full hInnerData bundle from gate/amplitude/envelope data.

### THE GROUP-(2) FINAL RESIDUE — 7 NAMED INPUT CARRIES (the milestone):
(a) bare z-slice measurabilities · (b) width σ>0 · (c) C₁ first-order on-gate sup ·
(d) C₂ second-order on-gate sup [NEW, joins the sup family] · (e) C_L Levi Gaussian
domination [groundable by leviSeries_gatedWitnessN1_dominated] · (f) the nbhd znb ·
(g) the per-z gate dichotomy. NO analytic hInnerData conjunct remains.
Dont-undercredit: SecondDerivEnvelope (J4-198) had the E2 3-term bound + the coercive x-free
bound + THE HONEST INTEGRABILITY VERDICT (naive (t−s)⁻¹ dominator NOT interval-integrable;
the (t−s)^{-1/2} sliver route survives — the s-layer must use the √ε truncation); this brick
adds the complementary z-level product dichotomy, abstracting C₂ over the coercive bound.
raw 0; build 49s. NEXT: GROUP (3) the V1 per-u census (J4-428). NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-428 (c8400b27): GROUP (3) = ENUMERATED INPUT CARRIES ONLY (phase 1)

`QIQTH/PerUCensusInstantiation.lean` (2 decls std-3). THE BINDER MAP: sSet/hsOpen/hsnhds,
gcoef, fbulk, bb, hb, hbulk_tendsto, hfull_pd1 — ALREADY FIRED internally by J4-405/406/407
(dont-undercredit honored; nothing re-proved). `hfrozen_pd1` DISCHARGED THIS BRICK: traded
for the lighter hQ1 via the banked `Pd2ConvPerU.hfrozen_pd1_from_hQ1` (J4-365) at
fb := FrozenGermInternal.fbulkInt. `perUCensus_phase1` = the fired census tuple
(= hPd2conv_perU_fired's conclusion) with the residue ENUMERATED: hProv (7-leg linewise
diff-under-∫ — the J4-405 D-feeder legs), the data fields fderivBulk/gderiv/C₀₁₂, hGint
(s-profile interval-integrability — NO banked supplier, grep-confirmed), hbulkderiv (bulk
order-2), hsliver (the √ε tranche), hcont (order-2 continuity), hQ1 (W2 diff-under-∫),
U/hUpos, the nb-triple. **THREE OF THE FOUR TERMINAL GROUPS NOW AT THE ENUMERATED-CARRIES
FLOOR.** raw 0; build 47s. NEXT: GROUP (4) the carried v2 census + the terminal cross-check
(J4-429). NOT a₁ = R/6 (CONDITIONAL).

---
# ★★★ J4-429 (7181fd77): ALL FOUR TERMINAL GROUPS AT THE ENUMERATED-CARRIES FLOOR
# — THE TERMINAL CROSS-CHECK COMPILES

`QIQTH/V2CensusInstantiation.lean` (3 decls std-3). THE GROUP-(4) BINDER MAP (blocks A-F:
boundary/geometry · the wall-A interchange census · the √ε sliver family D0/D1/hbnd · the
domination/mass constants · the F-pile + c-moving family · the Levi cross-Lipschitz).
`hFzero` DISCHARGED internally (← DaLimEasyTranche.hFzero_concrete). **`v2Census_phase1`
transcribes the ENTIRE truncatedDuhamelCore_threaded_v3 binder list verbatim and re-supplies
every binder — IT COMPILES, machine-certifying the completeness of the enumeration: every
binder lands in exactly one of groups (1)/(2)/(3)/(4)/(A)/internally-discharged. NO GAP.**
`terminal_enumeration_check` = the certificate. THE BINDER-LEVEL REDUCTION IS EXHAUSTED.

### SOL CONSULT #20 (gpt-5.6-sol) — THE CONVERGENCE-TRIO ATTACK PLAN (recorded):
RANKED ORDER: 1. (iv) the sup/constant family (after the minimal (vi) bootstrap:
hEdom_from_geometry ⟹ hgate + gate compactness) — pure compactness BUT ⚠ THE .CHOOSE TRAP:
never sup over a pointwise-.choose derivative field; use explicit formulas + ContinuousOn,
or canonical fderiv on an open nbhd, or finite-subcover → choose the CONSTANT not the germ.
herr/hmin are NOT pure compactness (positive minimum needs the near-identity/annulus/affine
3-region split). 2. (iii) THE SLIVER CORE EARLY = the risk gate: u⁻¹ × (√u-vanishing
remainder) ≲ u^{-1/2}; ⚠ endpoint a.e. not forced values; m-uniformity mandatory.
3. (i) diff-under-∫: hasDerivAt_integral_of_dominated_loc_of_lip is the right workhorse;
⚠ THE M-UNIFORMITY RISK: ∀m ∃gₘ WITHOUT summability (∑∫‖gₘ‖ < ∞) is USELESS at the true
kernel; nbhds must not collapse as m→∞; order-2 majorants must be summable. Order: hQ1 →
hProv leg-by-leg → sum 7 dominators → order 2 → hbulkderiv on a bulk cutoff only.
4. (ii) hGint CUTOFF-INDEXED ONLY (∀ε, IntervalIntegrable on [0, t−√ε]) — NEVER full [0,t]
(the naive (t−s)⁻¹ dominator is not integrable; confirmed banked design); ⚠ Bochner
convention: never use integral equality near the endpoint without the Integrable proof.
5. (vi) geometry/gauge (3-region coercivity; positivity before minima). 6. (v) wall-A
instantiation (banked suppliers + Fubini/DCT; ⚠ absolute not conditional integrability).
★ THE SINGLE HIGHEST-RISK ITEM: D1/hbnd — the endpoint order-two cancellation at the true
witness (the one place the route can GENUINELY FAIL if the structural cancellation is weaker
than expected). MITIGATION MANDATE: BEFORE further plumbing, prove the standalone pointwise
lemma extracting the singular leading term + its zero-moment cancellation + an explicit
u^{-1/2} majorant with summable-in-m constants. If it lands, the rest is standard dominated
analysis; if not, no API repairs the route.
raw 0; build 52s. NEXT: J4-430 = the sliver-core risk-gate lemma (Sol's mitigation mandate).
NOT a₁ = R/6 (CONDITIONAL — the floor closes nothing deeper).

---
# ★★★ J4-430 (cda615b1): THE RISK GATE LANDED — the trio campaign's highest-risk
# item is a proved theorem

`QIQTH/SliverRiskGate.lean` (4 decls std-3). THE SOL #20 MANDATE DISCHARGED. THE VERDICT:
**LANDED — the route is sound.** `riskGate_powercount`: |Q| ≤ C·u⁻¹·|rem| with |rem| ≤ B·√u
forces |Q| ≤ (C·B)·u^{-1/2} — the standalone structural lemma at the exact point where the
non-integrable τ⁻¹ order-2 s-dominator becomes the integrable sliver rate; the zero-moment/
center-subtraction cancellation (the banked matched-A₀·T_τ mechanism) supplies the √u
remainder. M-SUMMABILITY: the constants are m-INDEPENDENT — D0/D1 : Fin n → ℝ bound BEFORE
∀m; the entire m-dependence lives in the vanishing 2√(epsSeq m); the wall-A quantifier
discipline (fixed endpoint epsSeq 0, never a per-m cutoff) preserved.
`sliverRiskGate_hbnd` = the BYTE-FOR-BYTE hbnd binder of truncatedDuhamelCore_threaded,
wired via amplitudePackageOn_sliver_bound at ε := epsSeq m. `riskGate_bound_tendsto_zero` +
`sliverRiskGate_certificate` complete the package. Substantially EXTRACTION of banked
machinery (SecondDerivEnvelope §C, SliverAssemblyMatched, GpowBridge.invSqrt_absorb); the
genuinely new content = the isolated structural lemma + the m-independence packaging.
CONSEQUENCE: the remaining sliver work = standard dominated analysis over the satisfiable
hbnd_concrete_v2_carries {hcubic, hgate, hdisp, hjets, hcenter}. raw 0; build 51s.
NEXT: J4-431 = (iv) the sup/constant family (Sol #20 order); then the hcubic discharge.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-431 (95d6ff4f): the sup family — C_L + the amplitude sup GROUNDED;
## the derivative sups on ONE shared wall

`QIQTH/SupConstantFamily.lean` (4 decls std-3). THE SUP LEDGER: **C_L GROUNDED** —
`levi_C_L_grounded` delegates verbatim to the banked `leviSeries_gatedWitnessN1_dominated`
(conditional only on the standing hEmeas carry; the baseKernelW 2 0 = gaussDdim(2τ) bridge
deferred, not an obstruction). **Mqc/M₀chart GROUNDED gate-restricted** —
`chartAmp_center_sup_onCollar` via the banked `BaseSlotAmplitude.baseSlotAmp_bound` (genuine
IsCompact compactness on [0,τ₀]×closedBall; the chartAmp = chartFieldAmp centre bridge by
ring). HONEST MISMATCHES NAMED: the SlotIII ∀τz global shape not reachable from the
compact-ball continuity; the s-uniform product constant stays pointwise (F's Gaussian peak
blows up as s→0). **C₁/C₂/M₁chart/M₂chart OBSTRUCTED — THE SINGLE SHARED WALL:** no banked
joint-in-base continuous derivative field (banked derivative bounds are per-fixed-base or
germ-local); M/Sconst inherit it. THE .CHOOSE TRAP FORCED NOTHING — nothing fabricated.
THE FIX = ONE BRICK: BaseSlotAmpDeriv (the baseSlotAmp_bound analogue one/two derivative
orders up) grounds all four + M/Sconst by the same compactness route (= J4-432).
raw 0; build 52s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-432 (3939e676): the derivative fields IDENTIFIED — the sup wall reduced
## to the J3 atomic carry

`QIQTH/BaseSlotAmpDeriv.lean` (6 decls std-3). The concrete amplitude factors
DEFINITIONALLY: chartFieldAmp τ z = manifoldAmp τ ∘ (W z), W = uniformInverseChart. The
chain rule (HasFDerivAt.comp_hasDerivAt + the banked GeneralBaseJets field jet) yields the
EXPLICIT identification `pd_chartFieldAmp_center_eq`: pd (chartFieldAmp τ z) i 0 =
fderiv(manifoldAmp τ)(Wz0)(fderiv(Wz)(0) eᵢ) — NO .choose germ ever summed (the Sol trap
fully respected). `manifoldAmp_contDiffAt`: C² everywhere, geometry-only.
`baseSlotAmpDeriv1/2_sup_onCollar` ground C₁/M₁chart + C₂/M₂chart by compactness
CONDITIONAL on hcont1/hcont2; M/Sconst follow (banked F Gaussian + rhoRatio_le_collarK).
### THE REDUCTION: the J4-431 wall ("no banked joint-in-base derivative field") is now ONE
### ATOMIC CARRY — ContinuousOn (fun z ↦ fderiv ℝ (uniformInverseChart z) 0) = the chart
### field-slot Jacobian's joint-base continuity = THE RECOGNIZED J3 BLOCKER
(FlowJointRegularity/BasepointFDeriv document it as the carried joint-(q,v) regularity of
uniformFlowExp — a known frontier, not a surprise; the CoV centre-value jet is a DIFFERENT
jet, verified). raw 0; build 93s. NEXT: J4-433 = chartFieldJacobian_continuousOn (the J3
attack — flow smooth-dependence or explicit route; Sol #21 if walled).
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-433 (bcb891d0): the J3 attack — the Jacobian IDENTIFIED by IFT; the blocker
## reduced to the forward-flow jet atom

`QIQTH/ChartFieldJacobian.lean` (4 decls std-3). **THE DIAGNOSIS:** uniformInverseChart is
.choose-built = the LOCAL INVERSE of the geodesic-flow endpoint map uniformFlowExp — route
(c), the IFT. **PROVED:** `fderiv_localLeftInverse_eq_ringInverse` (the abstract IFT-Jacobian
identity, pure Mathlib) + `chartFieldJacobian_eq_ringInverse` (fderiv(W z) 0 =
Ring.inverse(fderiv φ_z (W z 0)), via the banked chartW0_rightInverse + the uniform
nondegeneracy ball) + `chartFieldJacobian_facts_of_small` (the five per-z facts from banked
lemmas). **THE REDUCTION** (`chartFieldJacobian_continuousOn_of_forwardJointCont`): the J3
carry follows unconditionally (ring-inverse continuity at units + the banked
chartOrigin_continuousOn) from ONE geometry-only atom:
  hFwd : ContinuousOn ((z,v) ↦ fderiv ℝ (uniformFlowExp z) v) (U ×ˢ ball 0 δ₀)
— joint smooth dependence of the flow Jacobian on initial data. Mathlib's ODE layer has
Grönwall + Picard–Lindelöf existence but NOT this; the .choose tower exposes no joint fact
(FlowJointRegularity §3) — the recognized J3 residue, honest. hcont2 needs the SECOND-order
forward jet — not discharged, no forced phase3 (no fake net gain). RECOMMENDED DISCHARGE:
the two-solution Grönwall on the Jacobi (first-variation) ODE over the compact confinement
tube = the fderiv-analogue of the banked uniformFlowExp_base_diff_bound (= J4-434).
Dont-undercredit: the decisive machinery (per-z IFT core, right-inverse, nondegeneracy,
value-level base continuity) was all banked; the new content = lifting VALUE → JACOBIAN.
raw 0; build 52s. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-434 (7988134e): the hFwd atom — TERM 2 derived; hbaseJ = the ONE
## spec-exposure carry

`QIQTH/ForwardFlowJet.lean` (4 decls std-3). The banked VALUE-level joint-continuity
triangle (FlowJointContinuity, q₀-anchored: base modulus + velocity continuity) mirrored ONE
DERIVATIVE UP for the operator jet D(q,w) = fderiv(uniformFlowExp q) w. **TERM 2 DERIVED
unconditionally** (`forwardFlowJet_velocityContinuousAt` ← contDiffAt2 +
ContDiffAt.fderiv_right + continuousAt). **TERM 1 = hbaseJ, THE HONEST CARRY** — the first-
jet base modulus (the exact operator analogue of the banked uniformFlowExp_base_diff_bound).
WHY IT CARRIES: the spec tower exposes only ∃L HasFDerivAt (L identified with nothing); the
velocity-Jacobi endpoint operator V is an INTERNAL .choose of uniformFlowExp_hasFDerivAt,
never re-exposed — while the discharge engine (BasepointJetModulus.jacobi_twopoint_diff_bound
+ hunif_of_lipschitz) is ALREADY BANKED and fits. THE RESIDUE IS SPEC-EXPOSURE, NOT ANALYSIS.
`forwardFlowJet_continuousOn_of_baseMod` = the hFwd atom;
`chartFieldJacobian_continuousOn_of_baseMod` = the J3 wiring. phase3 NOT forced (rides on
hbaseJ; hcont2 = the separate 2nd-order carry). raw 0; build 50s.
NEXT: J4-435 = JacobiCLMExposure (re-expose the endpoint Jacobi CLM as a public spec lemma →
feed the banked Grönwall → hFwd + J3 + C₁/M₁chart unconditional). NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-435 (2b8ad6e1): hbaseJ DISCHARGED — hFwd + J3 UNCONDITIONAL

`QIQTH/JacobiCLMExposure.lean` (5 decls std-3). **THE EXPOSURE PROVED:**
`uniformFlowExp_jacobi_spec` re-runs the compiled uniformFlowExp_hasFDerivAt construction
to the full public triple — V δ 0 = (0,δ), the first-variation (Jacobi) ODE
V' = DF(uniformFlowTube q v)·V on [0,1], fderiv = fun δ ↦ (V δ 1).1 — with the base geodesic
exposed CONCRETELY as uniformFlowTube (directly usable by the tube-separation engine).
**THE DISCHARGE:** `uniformFlowExp_fderiv_base_modulus` (strict interior ‖v‖<ρ_K) via
`jacobi_twopoint_diff_bound` with Dcoef = M₂·exp(L_sep)·‖q−q'‖ (the C² field bound × the
banked `uniformTube_twopoint_diff_bound`, J4-150/W2) and Jb = ‖δ‖·exp(K_f) from the ONE
genuinely-new lemma `jacobi_growth_bound` (homogeneous Grönwall). **THE COLLAPSE:**
`forwardFlowJet_continuousOn` (the hFwd atom) + `chartFieldJacobian_continuousOn` (the J3
wiring) BOTH UNCONDITIONAL — the weld re-derived at strict-interior velocities (the boundary
‖v‖ = ρ_K has no differentiability; the open-ball domain is correct, not a gap).
DONT-UNDERCREDIT (the residue was SMALLER than the J4-434 diagnosis): `uniformFlowExp_fderiv_
near_id_quant` had the exposure essentially inline (never extracted); the tube separation
that FlowJointRegularity §1 flagged as "a genuine multi-brick chunk" was ALREADY BANKED.
Net new analysis = one small Grönwall lemma + assembly.
REMAINING: the hcont1 shape wiring (→ J4-436 SupFamilyFirstOrder) + hcont2/C₂ (2nd order).
raw 0; build 76s. NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-436 (c7a71793): hcont1 COMPOSED — C₁/M₁chart GROUNDED (phase 3)

`QIQTH/SupFamilyFirstOrder.lean` (4 decls std-3, first-compile-clean). THE KEY INSIGHT:
manifoldAmp τ = c₀ + τ·c₁ is AFFINE in τ ⟹ its w-Fréchet-derivative field is
fderiv c₀ w + τ•fderiv c₁ w — jointly continuous UNCONDITIONALLY
(`manifoldAmp_fderiv_continuous`; new — BaseSlotAmpDeriv had only per-fixed-τ).
`supFamilyFirstOrder_hcont1`: the EXACT hcont1 shape via pd_chartAmp_center_eq + the CLM
composition (chartOrigin section + the J4-435 unconditional Jacobian + clm_apply at eᵢ).
THE DOMAIN MISMATCH HANDLED HONESTLY: rather than fabricate the U-vs-closedBall
reconciliation, hcont1 takes THREE NAMED banked-reducible geometric facts (hreg/hW0/hJac on
the ball) — the opaque analytic carry is GONE. `baseSlotAmpDeriv1_grounded` + 
`supConstant_phase3`. THE SUP LEDGER v3: C_L ✓ · Mqc/M₀chart ✓ · **C₁/M₁chart ✓** · M
factor-grounded (the s-uniform F peak ∝ s^{-d/2} honestly stays pointwise) ·
C₂/M₂chart/Sconst = GROUNDED-CONDITIONAL on hcont2 with the exact 2nd-order spec stated
(forward 2nd jet joint continuity + the 2nd-order IFT identity + the pd² identification).
raw 0; build 50s. NEXT: J4-437 = the Sol-#20 (i) diff-under-∫ opener (hQ1 first); queued =
the 2nd-order jet chain + hcubic + the small-ball provider. NOT a₁ = R/6 (CONDITIONAL).

---
## J4-437 (2112f7a0): the diff-under-∫ opener — hQ1 PROVED in the census shape

`QIQTH/InnerDiffFamily.lean` (3 decls std-3). THE MAP: the census demands hQ1 per-(u,i,m)
(∃V∈𝓝 0, pd(frozen germ) i y = fbulkInt … y on V); the banked `W2Finish.w2_hQ1` produces the
SAME equality at carrier level (shared V, from the 7-leg hFrozenData → the banked
SecondOrderInterchange engine); fbulkInt is definitionally the truncated primitive — the RHS
matches by delta-reduction (exact unifies). THE GENUINE NEW CONTENT = the shape bridge
(`innerDiff_census_hQ1_of_carrier` / `_of_frozenData`) — that gap was real and unfilled.
`innerDiff_phase1` = the per-u census Tendsto with hQ1 discharged internally.
**THE M-UNIFORMITY VERDICT (Sol #20's trap checked): does NOT bite at hQ1** — V is supplied
m-INDEPENDENT (no nbhd collapse, strictly stronger than demanded); the per-m s-dominators
are admissible (hQ1 is a per-m equality, no series over m); the genuine m-summability burden
lives ONLY in the order-2 sliver carries — and hsliver already meets it
((C₀+C₁)·2√εₘ + C₂εₘ → 0, the J4-430 risk-gate constants). The 7 hFrozenData legs carried
with named suppliers (Fubini engine for the measurabilities, w2_hFint capped-ceiling for the
integrability). raw 0; build 47s. NEXT: J4-438 = FrozenProviderLegs (hFmeas/hF'meas via the
Fubini engine, 7→5). NOT a₁ = R/6 (CONDITIONAL).

---
## J4-438: the hQ1 provider shrunk 7→4 (the Fubini + capped-ceiling legs)

`QIQTH/FrozenProviderLegs.lean` (5 decls std-3). hFmeas/hF'meas DISCHARGED (the banked
`innerIntegral_aesm` Fubini engine on .mul of m-INDEPENDENT joint (s,z) carries — the base-y
analogue of the banked base-0 route). hFint DISCHARGED (the banked
`pairing_intervalIntegrable_lowerCapped` capped-ceiling engine at base y; the degenerate case
via `intervalIntegrable_of_deg`). hdiff NOT wired — HONEST SHAPE MISMATCH (the J4-426 family
is 2nd-order/z-pointwise/base-update-0; the frozen hdiff is 1st-order/∫z/base-y) → J4-439
via `innerZ_line_hasDerivAt`. THE REMAINDER = {snb, bound+hbdd, hbound, hdiff} — the genuine
domination + pointwise-HasDerivAt content. M-UNIFORMITY: the discharged legs use ∀d carries
at d := u−εₘ (m-independent); the window + remainder per-m is ADMISSIBLE (hQ1 = per-m
equality). HONESTLY FLAGGED: the base-y joint carries are ENUMERATED INPUTS (the banked
joint-aesm is field-point-0-only) — no fabrication. raw 0; build 54s.
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-439: the hdiff leg DISCHARGED — the provider 7→3 (base-general engines)

`QIQTH/FrozenHdiffLeg.lean` (4 decls std-3). `frozenLeg_hdiff` fires the banked BASE-GENERAL
engine `innerZ_line_hasDerivAt` per-(s,w) at running base; the innermost z-pointwise
HasDerivAt family discharged internally via the banked base-general FIRST-order gate
dichotomy `hWdiff_offGate/onGate` at `update y i w'` (update_idem/update_self — no new
HasDerivAt engine needed). DONT-UNDERCREDIT CORRECTION recorded: both engines were
base-general (the J4-438 note undersold them). Named carry: the per-(s,w) z-level reduced
core, bundled under the SAME existential snb (window + line-nbhd coupled). THE REMAINDER =
{snb, bound+hbdd+hbound}. THE DOMINATOR PLAN (ledger v2): mirror innerData_pointwise at
base y (C·G_σ via envelope_integrable + a base-y witnessFieldDeriv gate envelope ×
hFdomEvery), then the outer bound via the capped-ceiling ∫z route (already run in
frozenLeg_hFint); the base-y envelope = the honest enumerated input. raw 0; build 77s.
NEXT: J4-440 = FrozenDominatorLegs. NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-440: the hQ1 provider 7→1 — ONE hGateData carry (phase 4)

`QIQTH/FrozenDominatorLegs.lean` (5 decls std-3). Legs (5)/(6) + the z-level reduced core
DISCHARGED. DONT-UNDERCREDIT CORRECTION: the banked `witnessFieldDeriv_gate_envelope_prod`
is ALREADY base-general (arbitrary field point — instantiated at update y i w'; the J4-439
ledger undersold it; only its INPUTS are enumerated). The one genuinely new envelope:
`witnessValue_gate_envelope_prod` (zeroth order, via the new base-general
`vanVleckGatedWitness_offGate_eq_zero`). The core mirrors innerData_reducedCore one order
down (bnd := (C₁·C_L)·gaussDdim σ); the outer bound := const M (the u-capped Gaussian peak)
via the banked capped-ceiling pairing calc; s≤0 killed by hFzero.
**THREAD CONVERGENCE: NOT achieved — the honest base mismatch** (the grounded C₁ lives at
base 0/closedBall; the needed on-gate sup at update y i w'; no fabricated convergence).
**THE PROVIDER LEDGER v3: the frozen hQ1 provider = ONE enumerated base-y gate/amp/envelope
carry `hGateData` per (m,i,u,y)** (snb + the capped dH domination + the a.e.-s gate core:
slice measurabilities, width, C₀/C₁/C_L sups, Levi domination, the gate dichotomy).
raw 0; build 51s. NEXT: J4-441 = SupBaseGeneral (lift the grounded C₁/C₀ to general base —
closing the sup↔diff thread convergence). NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-441: THE THREAD CONVERGENCE CLOSED — the provider core = TWO named atoms

`QIQTH/SupBaseGeneral.lean` (5 decls std-3). THE SIMPLIFICATION CHECK: the cheap local route
REJECTED on the quantifier shape (C₁ is chosen BEFORE ∀ᵐz ∀w'∈znb — must be uniform over the
compact gate; per-fixed-z local boundedness cannot supply it; honest). `supBaseGeneral_C0/C1`
GROUNDED at general field point via the identical compactness route (Icc ×ˢ K; no .choose;
`vanVleckGatedWitness_abs_le` turns the S-gate into a continuous dominator).
`gateData_of_reduced` + `innerDiff_phase5`: the frozen hQ1 provider = ONE reduced carry whose
IRREDUCIBLE CORE = TWO NAMED GEOMETRIC ATOMS — hcont0 (the general-field-point
chartOrigin_continuousOn) + hcont1 (the general-field-point chartFieldJacobian_continuousOn).
BOTH are general-base extensions of lemmas PROVED at the centre — not fresh walls; everything
else is bookkeeping. raw 0; build 57s. NEXT: J4-442 = GeneralFieldContinuity (hcont0 first —
CHECK chartP_continuousOn may already BE it). NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-442: hcont0 DISCHARGED + the hcont1 SMOOTH CORE (phase 6)

`QIQTH/GeneralFieldContinuity.lean` (5 decls std-3). **hcont0 PROVED**: the ungated witness
value factors DEFEQ as profile ∘ (z ↦ W z (update y i w)); `hcont0_of_chartCont` composes the
p-GENERAL `chartP_continuousOn` (dont-undercredit: already p-general — never a fresh wall)
with `parametrixWitnessProfile_continuous` (global; residue = the folded-coefficient
smoothness hw, bookkeeping). **hcont1 SMOOTH CORE BUILT**:
`chartFieldJacobianP_joint_continuousOn` — the JOINT (w',z) continuity of
fderiv(W z)(update y i w') on Icc ×ˢ K, the J4-433/435 chain replayed one field-order more
general (the IFT identity was base-point-general; forwardFlowJet_continuousOn already joint
and unconditional; Ring.inverse at units). NOT WALLED. The TWO remaining hcont1 atoms NAMED:
(i) the general-field UNGATED chain-rule identity (witnessFieldDeriv ↔ the smooth Jacobian;
LEAD: the banked ChartComposedHeatOp.chartComposed_pd_jointContinuousOn keyed at base 0 —
the general-base lift = J4-443) + (ii) the S-gate transparency at the field point.
`gateData_of_reduced2` + `innerDiff_phase6`: **the C₀ witness-value slot FULLY GROUNDED at
the witness.** raw 0; build 78s. NEXT: J4-443 = UngatedChainRule (the last witness-level
geometric atom). NOT a₁ = R/6 (CONDITIONAL).

---
# ★★★ J4-443: hcont1 DISCHARGED — THE FROZEN hQ1 PROVIDER CLOSED AT THE WITNESS LEVEL

`QIQTH/UngatedChainRule.lean` (5 decls std-3). **(a) THE TRANSPARENCY PROVED**: in-gate the
gated witness slice equals the ungated composite on a nbhd (`gatedKernel_apply_of_mem` germ +
the banked `pd_congr_of_eventuallyEq`). **(b) THE CHAIN RULE PROVED**: the composite factors
DEFEQ through the C∞ manifold profile (radialCutoff·heatParametrix — the profile-C¹ "wall"
never existed, it is C∞ free); the base-general banked `pd_comp` gives
witnessFieldDeriv = ∑_c pd prof c (W z p)·pd(W-component) in ONE call.
**(c) `witnessFieldDeriv_jointContinuousOn` = hcont1 EXACTLY** (joint on Icc ×ˢ K; no
boundary weld — the in-gate carry hGate keeps the whole domain in-gate; ContinuousOn.congr
welds onto the smooth sum; the J4-442 smooth core consumed internally).
**THE PROVIDER RESIDUAL** = enumerated bookkeeping + geometry/gate carries
(hW0/hmaps/hunit/hIFT, per-point hWdiff, hGate, hw) — all satisfiable, none deep.
Dont-undercredit: pd_comp was base-general — the 8th brick running where a banked base-0
lemma turned out general. THE DIFF-UNDER-∫ FAMILY'S FIRST ITEM (hQ1 + its full provider) IS
GROUNDED AT THE WITNESS. raw 0; build 54s. NEXT: J4-444 = hGint (Sol (ii); frozenLeg_hFint
did the same shape at base y — may be near-verbatim). NOT a₁ = R/6 (CONDITIONAL).

---
## J4-444: hGint DISCHARGED bulk⊕sliver (census phase 2)

`QIQTH/HGintCutoff.lean` (3 decls std-3). THE FINDING: the census hGint demands the FULL
[0,u] (not the anticipated capped tranche); the field-derivative envelope carries a 1/(2τ)
slope ⟹ near s→u only the singular (u−s)^{-1/2} dominates — per SOL #20 NOT forced.
THE SPLIT: bulk [0,u−εₘ] DISCHARGED (near-verbatim frozenLeg_hFint via
pairing_intervalIntegrable_lowerCapped + gaussDdim_crude_to_capped — the J4-428 "no banked
supplier" verdict was true only for the constant-dominator full route); the endpoint sliver
[u−εₘ,u] CARRIED as hSliver (the irreducible (u−s)^{-1/2} content → J4-445); reassembled by
IntervalIntegrable.trans. New named carries: hFzero/hWFDdomCapped/hFdomEvery/hGintMeas/
hSliver. ⚠ DONT-UNDERCREDIT CONFIRMATION: the census hProv (the DIAGONAL 7-leg provider) is
a DIFFERENT provider from the frozen hQ1 provider closed by J4-437..443 — it stays an honest
carry (ledger notes † ‡). raw 0; build 60s. NEXT: J4-445 = SliverSingularEngine (the
(u−s)^{-1/2} integrable-singularity engine; sliver_rate_intervalIntegrable may BE it).
NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-445: hGint FULLY DISCHARGED — the sliver singular engine (census phase 3)

`QIQTH/SliverSingularEngine.lean` (5 decls std-3). THE ENGINE EXISTED DISTRIBUTED across
three banked files — wired, not re-proved: the sliver-window singular integrability =
`HeatResidualBound.rpow_sub_intervalIntegrable` (SliverEstimates; NOT
sliver_rate_intervalIntegrable, which is fixed-[0,t] — the dont-undercredit check caught the
right engine); the power count = `SliverRiskGate.riskGate_powercount`; assembly =
IntervalIntegrable.mono'. `hSliver_discharged` trades the binder for TWO strictly-lower
satisfiable carries: hProfMeas + hProfFac (|profile| ≤ C·(u−s)⁻¹·|rem| ∧ |rem| ≤ B·√(u−s) —
the 1/(2τ) slope × the coordinate first moment). Endpoint s=u a.e. (ae_ne_point).
`hGint_full_at_witness`: the census hGint FULLY banked (bulk J4-444 ⊕ sliver this brick).
THE GROUP-(3) RESIDUE = enumerated input carries only (U/nb, the diagonal hProv, the order-2
data, hbulkderiv, the √ε hsliver, hcont, hQ1-carrier, + the hGint suppliers).
raw 0; build 51s. NEXT: J4-446 = ProfFacWitness (hProfFac from the banked envelope + moment).
NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-446: hProfFac + hProfMeas DISCHARGED — hGint AT THE CAMPAIGN FLOOR

`QIQTH/ProfFacWitness.lean` (5 decls std-3). `profFac_of_innerRate` — the general m-free
lever, the exact INVERSE of riskGate_powercount: the ∃C B rem factorisation from the single
clean inner-rate carry hProfRate (|profile| ≤ Q·(u−s)^{-1/2}), canonical rem := √(u−s),
(u−s)⁻¹·√(u−s) = (u−s)^{-1/2}, s≤0 by hFzero. `profMeas_at_witness` — the Fubini pattern
window-general (the sliver is a first-class instance; carries = hWFDjoint/hLeviJoint).
`hGint_grounded` + `perUCensus_phase4`. **THE hGint FINAL LEDGER: the sub-chain rests ONLY
on the campaign's standing enumerated families + ONE substantive m-free carry hProfRate**
(the coordinate-first-moment √τ gain — content banked in shape at hf2bound_at_witness).
The J4-428 "NO banked supplier" flag FULLY ELIMINATED. raw 0; build 76s.
NEXT: J4-447 = ProfRateTheorem (hProfRate → a theorem via the coordinate moment).
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-447: hProfRate PROVED — hGint rests on ONE product-moment atom (census phase 5)

`QIQTH/ProfRateTheorem.lean` (4 decls std-3). `profRate_theorem` proves the exact hProfRate
binder at Q := 3M√w/4 — the √τ gain FULLY INTERNAL (absCoord_gaussDdim_integral_le:
∫|z_i|·G_{wτ} ≤ (3/2)√(wτ); √(wτ) = √w·√τ; inv_sqrt_eq_rpow; assembled through
abs_integral_le_of_dom). THE HONEST DESIGN NOTE: `witnessFieldDeriv_gate_abs_le` genuinely
CRUDIFIES the z_i/(2τ) slope into the constant Bs — recovering the un-crudified slope is
real new jet analysis, NOT manufactured; instead `hProdMoment` (the pointwise product-moment
domination, (w,M) s-uniform, m-free) is carried at the IDENTICAL honesty level as the banked
hf2bound family. `hGint_theorem` + `perUCensus_phase5`: the hProfRate integral-rate carry
ELIMINATED; the hGint chain = the standing enumerated families + hProdMoment.
raw 0; build 50s. NEXT: J4-448 = ProdMomentWitness (the un-crudified z_i/(2τ) envelope from
the J4-443 chain rule — the parametrix pd HAS the slope structure). NOT a₁ = R/6.

---
## J4-448: the integrability leg DISCHARGED — hProdPtwise = the ONE irreducible atom

`QIQTH/ProdMomentWitness.lean` (4 decls std-3). The bundled hProdMoment SPLIT into
hProdPtwise + hProdMeas; the Integrable leg derived internally (`integrable_of_prodMoment` ←
the banked power-1 coordinate-moment integrability + Integrable.mono').
★ THE KEY MATHEMATICAL FINDING: the s-uniform POINTWISE collapse of the two-Gaussian product
G_{wA(u−s)}·G_{wF·s} to a single G_{w(u−s)} is GENUINELY FALSE — the harmonic width
σ_h = wA(u−s)·wF·s/(wA(u−s)+wF·s) yields a G_{σ_h} whose peak diverges relative to
G_{w(u−s)} as s→0. The campaign's under-the-integral pairing design is FORCED (verified
against the pairing infra); hProdPtwise is a LEGITIMATE floor atom at the exact
hf2bound-carried-hdom honesty tier, not an oversight. `hGint_final` + `perUCensus_phase6`:
the hGint chain = the standing enumerated families + hProdPtwise ONLY (the integrability
degree of freedom GONE). raw 0; build 49s. NEXT: J4-449 = ProdPtwiseWitness (the refined
dH envelope × a TRUE Levi CAP — WITH the satisfiability gate first per the falsity finding).
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-449: THE GATE RAN — hProdPtwise SATISFIABLE, split into two floor atoms (phase 7)

`QIQTH/ProdPtwiseWitness.lean` (4 decls std-3). **THE GATE VERDICT: SATISFIABLE AS STATED**
via factorization 1 — the refined dH slope-moment envelope (|dH| ≤ CA/(2(u−s))·|z_i|·
G_{wA(u−s)}) × a CONSTANT Levi cap yields EXACTLY the demanded single-Gaussian shape
(w := wA, M := CA·C_L); no G·G product arises — the J4-448 falsity structurally AVOIDED.
**★ THE SOUNDNESS SUBTLETY THE GATE CAUGHT:** the banked leviSeries_gatedWitnessN1_dominated
RHS is a width-2s Gaussian whose peak (8πs)^{-n/2} DIVERGES as s→0 — it canNOT source the
constant cap; but the TRUE Levi factor is O(t^N)-smooth (→0 as s→0), so a genuine finite
s,z-uniform cap EXISTS — carried as the distinct C⁰-regularity atom hLeviCap (correctly NOT
derived from the crude Gaussian). Gate (ii): the refined envelope satisfiable (the J4-443
chain rule; {z_i=0} null). The J4-447 lever fires UNCHANGED. `prodPtwise_at_witness` grounds
the atom to {hDHrefined, hLeviCap}; `hGint_prodPtwise` + `perUCensus_phase7`.
**hGint FINAL: the standing enumerated families + hDHrefined (the sharpened envelope tier) +
hLeviCap (the parametrix-smoothness tier)** — both m-free, satisfiable, strictly lower.
raw 0; build 47s. NEXT: J4-450 = LeviCapWitness (hLeviCap with its own gate: the s→0
extension + compactness). NOT a₁ = R/6 (CONDITIONAL).

---
# ⚠⚠ J4-450 (7fb383f4): THE GATE VERDICT = UNSATISFIABLE — THE POINTWISE SPLIT
# RETRACTED (a soundness finding; the discipline working as designed) + SOL #21

`QIQTH/LeviCapWitness.lean` (1 decl std-3). **THE FINDING:** hLeviCap (the s,z-uniform
CONSTANT Levi cap) is UNSATISFIABLE for general n — the on-diagonal
leviSeries s 0 0 ~ O(s^{N−n/2}) with the fixed witness N=1 (Minakshisundaram): divergent
for n ≥ 3; the J4-449 gate's "O(t^N)-smooth → 0" reasoning OMITTED the (4πt)^{-n/2}
normalization; hFzero + the s→0⁺ peak give a genuine discontinuity at (0,0) — no
compactification. CONSEQUENCE: hProdPtwise itself is NOT a sound s-uniform pointwise atom
at n ≥ 3 (near-diagonal two-Gaussian scaling s^{1−n/2}) — **the J4-447..449 POINTWISE
grounding chain is RETRACTED for general n** (the lemmas remain true conditionals; their
atoms flagged unsatisfiable — exactly the vacuity feedback_axiom_budget_blind_spot exists
to catch). Landed: `leviCap_on_compactBox` (the TRUE positive-time-compact cap; the
constant diverges as δ→0 — the gate boundary explicit). hGint reverts to the J4-446
integral-level surface (hProfRate satisfiable).

### SOL CONSULT #21 (gpt-5.6-sol) — THE INTEGRAL-LEVEL RE-GROUNDING (recorded):
**CONFIRMED with one essential centering condition.** The weighted two-Gaussian pairing:
G_a(z−x)G_b(z−y) = G_{a+b}(x−y)·G_h(z−c), h = ab/(a+b), c the weighted mean;
∫|z_i−x_i|·G_a(z−x)G_b(z−y) ≤ G_{a+b}(x−y)·(κ√h + (a/(a+b))|y_i−x_i|), κ = 3/2 banked.
a+b = wA(u−s)+2s ≥ u·min(wA,2) > 0 BOUNDED (the s→0 danger absorbed by the INTEGRATED
pairing); √h ≤ √a = √(wA)·√τ ⟹ Q·τ^{-1/2} m-free. ⚠ THE CENTERING TRAP: the moment MUST be
|z_i − x_i| RELATIVE TO the dH-Gaussian's center (or the chart recentred so x = 0) — a raw
fixed-coordinate |z_i| with an off-center G_a gives O(τ^{-1}) as s↑u, NOT τ^{-1/2}; adding
|x_i| ≤ diam does NOT close it. THE LEAN ROUTE: one reusable weighted-pairing helper
(∫|(z−x)_i|·G_a(z−x)·G_b(z−y) ≤ G_{a+b}(x−y)·(κ√(ab/(a+b)) + (a/(a+b))·|(y−x)_i|)) via the
product-to-single identity + the triangle around c + translation invariance +
absCoord_gaussDdim_integral_le + gaussDdim_pairing_integral; then hProfRate = abs_integral
+ the two envelopes + the helper + arithmetic. THE ONE GATE TO AUDIT: the refined dH
envelope must supply its moment relative to ITS OWN Gaussian center.
raw 0; build 48s. NEXT: J4-451 = the weighted-pairing helper + the centered hProfRate.
NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-451: THE SOL #21 RE-GROUNDING COMPLETE — the retracted atoms GONE (phase 8)

`QIQTH/WeightedPairingHelper.lean` (9 decls std-3; relaunched post-rate-limit). **THE
CENTERING GATE: VOID** — both the hDHrefined and hFdomEvery Gaussians are centered at 0
(x = y = 0 ⟹ c = 0, the cross term vanishes); no corrected shape needed. **LANDED IN FULL:**
`heatKernel1D_prod_to_single` (the 1-D completed square) + `gaussDdim_prod_to_single`
(the n-D coordinate-wise lift: G_a(z−x)·G_b(z−y) = G_{a+b}(x−y)·G_h(z−c)) +
`weighted_pairing_helper` (the Sol #21 inequality, general centers) + `profRate_integral`
(the EXACT census hProfRate re-grounded: a+b ≥ min(wA,wF)·u BOUNDED — the s→0 peak
divergence ABSORBED UNDER THE INTEGRAL; √h ≤ √(wA·τ); τ⁻¹·√τ = τ^{-1/2}; Q m-free) +
`hGint_regrounded` + `perUCensus_phase8`. **THE RE-GROUNDING LEDGER:** hLeviCap/hProdPtwise/
hProdMoment (the J4-450 retracted atoms) GONE; the hGint chain rests ONLY on the standing
centered census families {hFzero, hWFDdomCapped, hFdomEvery, hGintMeas, hWFDjoint,
hLeviJoint, hDHrefined, hProdMeas}. Dont-undercredit: the pairing INTEGRAL was banked (the
convolution semigroup); the new content = the POINTWISE identity carrying the moment.
raw 0; build 75s. NEXT: J4-452 = DHrefinedWitness (the last substantive carry; its own gate:
the θ-centered parametrix slope vs the 0-centered demanded shape). NOT a₁ = R/6.

---
## J4-452: THE GATE CAUGHT ANOTHER — the two-term hDHrefined₂, the rate SURVIVES (phase 9)

`QIQTH/DHrefinedWitness.lean` (5 decls std-3). **THE VERDICT:** the actual witness slope is
a FULL CONTRACTION ⟨W z p, ∂ᵢW⟩/(2τ) — Cauchy–Schwarz gives a full-norm ‖z‖ moment; the
J4-451 single-coordinate hDHrefined is RETRACTED as unsatisfiable (‖z‖ ≤ |z_i| is false).
**THE CORRECTED SHAPE:** hDHrefined₂ = (CA/(2τ)·‖z‖ + CB)·G_{wA·τ}. **THE MASS-TERM SCALING
SETTLED — NO τ⁻¹:** the mass carries no 1/(2τ); it pairs (gaussDdim_pairing_integral +
antitone) to a bounded τ⁰ = √τ·τ^{-1/2} ≤ √u·τ^{-1/2}, absorbed. The moment: ‖z‖ ≤ ∑|zⱼ| +
the banked centered pairing per coordinate ⟹ n·G_{a+b}(0)·(3/2)√h (Q inflated by n — n
fixed, legitimate). `normPairing_moment` + `profRate_inner_bound₂` + `profRate_integral₂` +
`hGint_regrounded₂` + `perUCensus_phase9`: hProfRate = {hDHrefined₂, hFdomEvery, hProdMeas}.
Dont-undercredit: ALL the moment/pairing/count infrastructure was banked — pure re-assembly.
raw 0; build 57s. NEXT: J4-453 = hProdMeas discharge + the hDHrefined₂ witness derivation
(the contraction-matched shape = the crude envelope's proof pattern one refinement up).
NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-453: THE D₀ GATE RECONCILED — D₀ = 0; the refined envelope PROVED on-gate
## (census phase 10)

`QIQTH/ProdMeasAndEnvelope.lean` (4 decls std-3). **THE CRUX VERDICT: D₀ = 0 at the
witness** — the banked `chartW0_displacement` gives W z 0 = −z + O(‖z‖²): the near-isometry
is PURELY LINEAR, no additive constant; the slope contraction is a pure ‖z‖-moment with the
1/(2τ) ONLY on the moment; the only mass is the amplitude-derivative CB (no 1/(2τ)); even
the quadratic residual pairs as τ⁰. THE J4-452 COUNT STANDS.
`witnessFieldDeriv_refined_gate_envelope`: the exact on-gate two-term bound
(CA/(2τ)·‖z‖ + CB)·G_σ — one refinement up from the crude envelope, via
`slopeContraction_holder` (the ℓ∞–ℓ¹ Hölder surrogate — Point n is Pi-SUP-normed, correctly
NOT Euclidean Cauchy–Schwarz) + the centered near-isometry. Part A: hProdMeas DISCHARGED at
the honest SLICE level (the joint→slice route only gives a.e.-s — caught and routed
correctly). `perUCensus_phase10`. REMAINING: the full ∀z hDHrefined₂ (on-gate + the banked
off-gate vanishing + uniform constant selection = J4-454). raw 0; build 49s.
NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-454: hDHrefined₂ A THEOREM — THE CENSUS hGint CLOSED AT THE WITNESS
## MODULO THE STANDING FAMILIES (census phase 11)

`QIQTH/DHrefinedFull.lean` (3 decls std-3). The constant-selection gate: YES — wA the fixed
width; CA = (sup Mp)·Lz·Ba·C₁, CB = Bd·C₁ (standing amplitude sups × the linear D₀=0
near-isometry slope × the grounded sup family over the compact gate/x-range); no 1/(2τ)
hidden in constants — all s-scaling explicit in the shape. `hDHrefined₂_theorem`: the FULL
∀ᵐz binder consumed by profRate_integral₂ (on-gate = the J4-453 lever × the sups; off-gate =
the banked vanishing + RHS ≥ 0; the dichotomy promotes). `perUCensus_phase11`.
**THE hGint SUB-CHAIN — the J4-428 "NO banked supplier" item — IS CLOSED AT THE WITNESS
modulo the standing Gaussian-envelope families (hOnGate, hFdomEvery) + the satisfiable
measurabilities; every survivor strictly lower-level.** The full hGint arc: J4-444 bulk →
J4-445 sliver engine → J4-446 factorisation → J4-447 rate lever → J4-448/450 the two
retractions caught → J4-451 the Sol #21 re-grounding → J4-452 the two-term correction →
J4-453 D₀=0 + the refined envelope → J4-454 the closure. Dont-undercredit: pure assembly.
raw 0; build 48s. NEXT: J4-455 = Sol-#20 (vi) herr/hmin 3-region coercivity.
NOT a₁ = R/6 (CONDITIONAL).

---
# ⚠⚠ J4-455: THE FOURTH GATE CATCH — the whole-space herr/hmin UNSATISFIABLE
# (machine-certified); the gate-restricted versions PROVED

`QIQTH/HerrHminCoercivity.lean` (5 decls std-3). **THE VERDICT (a THEOREM, not just an
audit):** `uniformInverseChart_off_K` — the chart defaults to 0 off K; hence
`wholeSpace_coercivity_unsatisfiable` — the literal ∀z hmin (½r²_z ≤ r²_{Wz}) is
DEFINITIVELY FALSE at any nonzero z ∉ K (K compact ⟹ such z exist; the ½ is fixed).
herr fails in the small-‖z‖ gap off K. **⚠ CONSEQUENCE:** the group-(1) consumers
hdom_comp2_ptwise/hcomp_final2/slotInstantiation_phase8 (literal ∀z binders) are only
VACUOUSLY dischargeable — they need the gate-vs-far-field re-fire (J4-456): on
collarᶜ ∩ (K∩ball) via comparisonDom2 ← herrHmin_gate; on the far field a decaying
baseKernelW leg (off-gate W z = 0 makes the ρ-factored integrand the WRONG object — a
split, not a scaling gap). **PROVED gate-restricted:** `herr_gate` (≤ L·n·‖z‖³ on K∩ball,
from the banked chartW0_rncRadialSq_error; the sign resolved: W z ≈ −z, rncRadialSq even) +
`hmin_gate` (radius shrunk so L‖z‖ ≤ ½) + `herrHmin_gate`. Dont-undercredit: assembly —
the displacement machinery was banked. raw 0; build 50s. FOUR gate catches to date
(J4-448/450/452/455) — the blind-spot discipline is the campaign's best tool.
NEXT: J4-456 = GateFarFieldSplit (hcomp_final3 + slotInstantiation_phase9).
NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-456: THE REPAIR — hcomp_final3 satisfiable (phase 9); the far field DECAYS

`QIQTH/GateFarFieldSplit.lean` (4 decls std-3). **THE FAR-FIELD AUDIT: DECAYS** — the RAW
comparison integrand off K is f = −z_i/(2τ)·G_τ·A1amp·F − G_τ·A2amp·F (witnessSecondXDeriv
= 0 off K by the gatedKernel base if-else): every term carries G_τ, Gaussian-decaying; the
J4-455 exp-blow-up concern was ONLY the ρ-FACTORED lens (its identity holds only on K).
`hcomp_final3`: collarᶜ = (∩ gate) ⊔ (\ gate) via integral_inter_add_diff; the gate piece
≤ Bcomp2/√τ (`comparison_gate_bound` ← the satisfiable herrHmin_gate); the far field ≤ the
finite carry Bff. `slotInstantiation_phase9` = phase 7 ∧ hcomp_final3 — **the unsatisfiable
∀z binders are GONE; the vacuous phase-8 chain is SUPERSEDED.** The satisfiable carries:
S1 herrHmin_gate · S2 the gate-restricted jets · S3 the Mqc sup · S4 hff/Bff (a
fixed-quantity far-field bound, NOT a false universal — → J4-457 derived from the G_τ
decay) · S5 wiring. Dont-undercredit: comparisonDom2 + the S5b machinery reused verbatim.
raw 0; build 54s. NEXT: J4-457 = FarFieldDecay (Bff derived). NOT a₁ = R/6 (CONDITIONAL).

---
## J4-457: Bff DERIVED (honest O(1/τ)) — the hff carry ELIMINATED (phase 10)

`QIQTH/FarFieldDecay.lean` (5+ decls std-3). THE DOMAIN/TAIL GATE: the far field guarantees
only ‖z‖ > c√τ — the radius SCALES with the Gaussian width (z = √τ·w maps to a
τ-independent tail), so NO fixed-R tail suppression; the controllable structure is the
off-K VANISHING of the witness term (`witnessSecondXDeriv_offGate_eq_zero`), reached via
the satisfiable hKr : K ⊆ ball 0 r (K compact). `farField_decay_bound`: Bff := ∫ farFieldDom
DERIVED — the honest count: gradient O(τ^{-1/2}), mass O(1), **Hessian O(τ⁻¹) DOMINANT** ⟹
Bff = O(1/τ), honestly WORSE than the gate's O(1/√τ) (off K the Hessian stands alone with
no (ρ−1) smallness) — recorded not hidden; hff was a free carry so any finite Bff
discharges it; a downstream-quality concern, not a soundness gap (the absorption → queued).
The far-field sups hA1F/hA2F honestly carried (the data-bundle sups are on-collar-only).
`hcomp_final4` + `slotInstantiation_phase10`. raw 0; build 52s.
NEXT: J4-458 = (v) WALL-A INSTANTIATION (the last Sol-#20 item). NOT a₁ = R/6 (CONDITIONAL).

---
# ★★ J4-458: wall-A INSTANTIATED — ALL SIX SOL-#20 ATTACK ITEMS ADDRESSED

`QIQTH/WallAInstantiation.lean` (5 decls std-3). THE BLOCK-B MAP: hSecCont VERBATIM
(hSecCont_of_boxes — exact Ioc 0 T ×ˢ univ shape); hFdomW BRIDGED (hFdom_concrete,
y:=0/wF:=2/sub_zero); hBcont BRIDGED (the generic stripContOn_of_boxes lift); hmeas2Lo
BRIDGED (the banked hmeas2Lo_slice REDUCES it onto hSecCont/hBcont/hUT/hεU — the V2 map
had it as a carry; dont-undercredit, again); THE TWO GENUINE CARRIES: hInter (the
interchange bundle) + hAdom2cap (the clean 2nd-deriv Gaussian cap — the banked bound is
the crude τ⁻¹ envelope). `wallA_phase1`/`wallA_ledger` produce all six members in the
exact truncatedDuhamelCore_threaded_v3 shapes.
### ★ THE SOL-#20 SCOREBOARD — ALL SIX ADDRESSED:
(i) diff-under-∫ ✓ (hQ1 census-shape + the provider closed) · (ii) hGint ✓ (11 census
phases, closed at the witness) · (iii) the √ε sliver ✓ (the risk gate + the singular
engine) · (iv) sups ✓ (C_L/Mqc/C₁ grounded; C₂ the 2nd-order spec) · (v) wall-A ✓ (THIS
BRICK) · (vi) herr/hmin ✓-as-corrected (the unsatisfiability certified; the gate/far-field
repair in force). The carries are INPUTS not theorems. raw 0; build 81s.
NEXT: J4-459 = WallAThreading (the v3-core call at the witness; block-B → hInter+hAdom2cap).
NOT a₁ = R/6 (CONDITIONAL).

---
## J4-459: the block-B surface THREADED — 6 members → 2 genuine carries

`QIQTH/WallAThreading.lean` (2 decls std-3). `v2Census_phase2` = the v3-core cross-check
with the six block-B binders supplied INTERNALLY from wallA_phase1's inputs (delegating to
the already-transcribed v2Census_phase1; the one mismatch — hFdomW's ∃CF vs the free wF/CF
binders — resolved by obtain + wF := 2, defeq clean). THE BLOCK-B FINAL LEDGER: hInter +
hAdom2cap (the genuine carries) · data/hSecBoxes/hBBoxes (satisfiable envelope/box inputs) ·
hUT/hεU (group-(A) scaffolds); hFdomW/hSecCont/hBcont/hmeas2Lo all internal.
raw 0; build 48s. NEXT: J4-460 = HInterGrounding (hInter — now the single most load-bearing
block-B carry — via the F2/diff-under-∫ piles). NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-460: hInter GROUNDED — hAdom2cap the SOLE remaining block-B carry

`QIQTH/HInterGrounding.lean` (3 decls std-3). THE GATE: PASS — hInter (MemInterchange) is
an abbrev unfolding to EXACTLY the banked `witness_MemInterchange` conclusion (J4-256); the
m-uniformity trap CLEARED (a per-(m,i,u) EQUALITY — per-m dominators admissible); quantifier
order + base-0 centering preserved. `hInter_grounded` (the engine route) +
`hInter_grounded_majorant` (the W2-majorant route — the dominator triple discharged
internally from hOn+hF). `v2Census_phase3` = phase2 with hInter DROPPED and only hdiff
added — phase2 already carried the engine's whole diff-under-∫ family redundantly
(dont-undercredit: hInter was NEVER a raw wall). **BLOCK-B = hAdom2cap ONLY.**
raw 0; build 49s. NEXT: J4-461 = hAdom2cap (the capped-vs-Gaussian shape gate).
NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-461: BLOCK-B CLOSED TO ZERO GENUINE ATOMS

`QIQTH/HAdom2capGrounding.lean` (3 decls std-3). THE GATE: the supplier
`hAdom2_capped_family_of_crude` matches VERBATIM (same kernel witnessSecondXDeriv, same
Gaussian width wA2 — NO bridge, same lower-capped range εₘ ≤ τ ≤ T, per-m CA2c :=
Ccrude·εₘ⁻¹ — ADMISSIBLE because hAdom2cap is per-m; the τ-uniform whole-time version is
generally false). The coercive-E2 candidate REJECTED (wrong kernel, per-point jet data,
width 2τ, 1/τ² in the constants). The bridge input = the banked crude envelope
(WideAmplitudePackage.hSecond + second_global_of_package). `hAdom2cap_grounded` +
`v2Census_phase4`. **BOTH former block-B genuine carries grounded (hInter J4-460 +
hAdom2cap here): THE WALL-A LEG RESTS ON SATISFIABLE ENVELOPE/BOX/SCAFFOLD INPUTS ONLY**
{hcrude, data, hSecBoxes, hBBoxes, hUT, hεU}. Closing block-B closes nothing deeper —
the convergence-trio content lives outside it. Pure assembly. raw 0; build 49s.
NEXT: J4-462 = hdiff (the phase3/4 carry). NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-462: hdiff GROUNDED — ZERO net new carries (phase 5)

`QIQTH/HdiffGrounding.lean` (3 decls std-3). THE GATE: this hdiff = the 2nd-order analogue
(base 0, dH→dHH) of the J4-439 frozen leg — and the chain was PRE-BANKED and stronger:
`W2Finish.w2_hdiff` (J4-397) produces it from hInnerData, which phase4 ALREADY carries
(feeding the W2 route independently). THE DECISIVE OBSERVATION: hdiff collapses onto a
pre-existing carry — `v2Census_phase5` = phase4 MINUS hdiff, NOTHING added (strictly better
than J4-439). `hdiff_grounded` + `hdiff_grounded_reduced` (one level deeper ← hRedCore via
innerData_phase1). Pure wiring — the J4-426 second-order tower + the J4-397 engine were all
banked. raw 0; build 62s. NEXT: J4-463 = InnerDataCensusThread (hInnerData → the reduced
core inside the census, v2Census_phase6). NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-463: hInnerData → the named atomic core (census phase 6)

`QIQTH/InnerDataCensusThread.lean` (1 decl std-3). THE GATE: EXACT VERBATIM MATCH —
innerData_phase2's output = phase5's hInnerData binder (same prefix/conjuncts/indexing/
truncation/centre/kernels). `v2Census_phase6` supplies the bundle internally; the carry =
the strictly-lighter hGateCore (7 named atoms: z-slice measurabilities · σ>0 · C₁ · C₂ ·
C_L · znb · the gate dichotomy). **NO opaque diff-under-∫ bundle survives in the census
surface.** THE SUP CONVERGENCE: AUDITED, DEFERRED — the grounded C₁/C_L theorems live in
the chartAmp/baseKernelW presentation vs the census's witnessFieldDeriv/gaussDdim slots
(base-0 matches; the FUNCTIONAL presentation differs — the bridges = J4-464, honestly
deferred not fabricated). Pure substitution — the surface was one exact-call away.
raw 0; build 74s. NEXT: J4-464 = PresentationBridges. NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-464: the census C₁ slot GROUNDED FROM GEOMETRY (phase 7)

`QIQTH/PresentationBridges.lean` (4 decls std-3). **BRIDGE 2 COMPOSED** via a cleaner
DIRECT route: `witnessFieldDeriv_jointContinuousOn` (J4-443) already bounds the ACTUAL
census object — the feared germ↔chartAmp conversion was UNNECESSARY; the w-slice
restriction + IsCompact.exists_bound on K gives the exact census C₁ slot
(`census_C1_grounded`). **BRIDGE 1**: baseKernelW 2 0 = gaussDdim(2τ) was ALREADY BANKED
(baseKernelW_zero_apply); `census_C_L_grounded` grounds the SHAPE; the slot-wire honestly
blocked — the grounded theorem existentially fixes its own gate S/radii, not injectable for
the census-fixed S (→ J4-465, with the gate-coherence audit). `gateCore_reconstruct` +
`v2Census_phase7` (hGateCore → the 6-conjunct hGateCoreR + the C₁-geometry bundle; C₁
reconstructed internally). raw 0; build 49s. NEXT: J4-465 = CLSlotWire (the gate-coherence
audit + the C_L wire). NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-465: the census C_L slot WIRED — the gate ∃-consumed (phase 8)

`QIQTH/CLSlotWire.lean` (3 decls std-3). THE AUDIT: ∃-CONSUMPTION, NO BLOCKER — the kernels
(vanVleckGatedWitness = gatedKernel) are defeq GIVEN the same S,a,b; the mismatch was purely
∃-S vs ∀-S (no germ/presentation gap). THE HONESTY COST RECORDED: v2Census_phase8's
conclusion is ∃ a b S … (the census gate fixed to the grounded W3 geometry-chosen gate);
the S-dependent slots migrate into the ∃-body — all satisfiable at that S
(hUT/hεU/hEmeas/hGateCoreRR = the surviving labelled inputs). `census_C_L_wired` (σ := 2s)
+ `gateCoreRR_reconstruct` + `v2Census_phase8`. The s-bounds recovered from the existing
hεU/hUT binders — no new carry. raw 0; build 47s. NEXT: J4-466 = Phase9Replumb (the full
analytic stack at the ∃-consumed gate — mechanical). NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-466: THE CAPSTONE CONCLUDED at the ∃-consumed gate — the slot-grounding
## chain (phases 2-9) COMPLETE

`QIQTH/Phase9Replumb.lean` (1 decl std-3). `v2Census_phase9`: obtains (a,b,S) + the
C_L-grounding closure from phase8, feeds the reconstructed hGateCoreR through the FULL
phase-7 analytic stack at that gate ⟹ ∃ a b S, 0<a ∧ a<b ∧ (the stack →
TruncatedDuhamelCore). The at-the-obtained-gate supply pattern (phase8's body dictates it);
the S-independent geometry verbatim; the ~85 S-dependent carries in the ∃-body.
**THE CHAIN: phase 2 (block-B enumerated) → 3 (hInter grounded) → 4 (hAdom2cap) → 5 (hdiff
zero-net) → 6 (hInnerData → the atomic core) → 7 (C₁ grounded from geometry) → 8 (C_L wired,
gate ∃-consumed) → 9 (THE CORE REACHED).** The final census surface = the named satisfiable
carries at the geometry-chosen gate (envelope/amplitude/boxes/scaffold/measurability/gate/
slot/boundary/gauge groups). HONESTY: ∃ over the geometry-chosen gate, not arbitrary S.
raw 0; build 48s. NEXT: J4-467 = hslot (the banked K₁τ^{-1/2} shape may be verbatim).
NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-467: hslot OFF THE CENSUS SURFACE (phase 10)

`QIQTH/HslotGrounding.lean` (3 decls; std-3 + one axiom-FREE projector). THE GATE:
COMPATIBLE, fires VERBATIM — the census hslot binder = EXACTLY the conclusion of the banked
J4-402 `leviSecondPairing_inner_bound_concrete` at F := leviSeries(heatOp …); the supplier
is S-POLYMORPHIC so the ∃-consumed gate instantiates definitionally (exact closes it — the
J4-465 kernels-defeq fact). M-UNIFORMITY: Lc/Bcomp/Q/Sconst bind BEFORE (i,τ,s) — no εₘ
leak. DONT-UNDERCREDIT CLARIFICATION: J4-416's hslot_covered CONSUMES hslot (aggregates it);
the PRODUCER is J4-402 — which is what fires here. `hslot_grounded` + `v2Census_phase10`
(hslot removed; the J4-402 per-(τ,s) slot carries + ampData/qcF/IchartF swapped in — the
already-enumerated campaign surface). raw 0; build 77s.
NEXT: J4-468 = hcap + hEndpoint (both banked-satisfiable). NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-468: hcap + hEndpoint GROUNDED — the moment-wall triple FULLY OFF (phase 11)

`QIQTH/HcapEndpointGrounding.lean` (3 decls std-3 + axiom-free projector). **hcap**: the
per-(m,u,s) window cap COLLAPSES to ONE scalar hτc : epsSeq 0 ≤ τc (s > u−εₘ ⟹ u−s < εₘ ≤
ε₀ via epsSeq_antitone; m-INDEPENDENT — the wall-A fixed-endpoint discipline). **hEndpoint**:
ZERO new residue — from the ALREADY-PRESENT hAzero carry (the τ=0 witness vanishes
identically ⟹ pd_zero_fun ⟹ the integrand is 0 pointwise — the Sol endpoint trap avoided,
nothing forced). `v2Census_phase11`. **THE MOMENT-WALL TRIPLE hslot/hcap/hEndpoint IS NOW
FULLY OFF THE CENSUS SURFACE** (J4-467/468); the residue = the slot-instantiation carries +
the scalar hτc + the unchanged census. raw 0; build 51s.
NEXT: J4-469 = the box census (hSecBoxes/hBBoxes ← the banked box facts).
NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-469: the box families OFF (phase 12)

`QIQTH/BoxCensusGrounding.lean` (4 decls std-3 + axiom-free ledger). **hBBoxes (Levi):
GENUINE WIRE** — the demanded box shape = EXACTLY leviSeries_boxContOn's conclusion, fed
from the already-present phase-11 LeviSeriesLocalData; residue = the per-k termwise box
carry htermBox (strictly lower). **hSecBoxes (witness): HONEST REDUCTION** —
witnessSecondXDeriv is defeq the pd∘pd diagonal at the FIXED centre 0; the J4-442 pd-pd
lead keys the VARYING base of the UNGATED composite (a genuine gate + base-keying mismatch,
no transport) — reduced by defeq to the named atom hpd2diag, NOT discharged.
`v2Census_phase12` = phase11 minus the box families plus {hpd2diag, htermBox}.
raw 0; build 50s. NEXT: J4-470 = hProvP (the diagonal provider). NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-470: the diagonal provider 7 → 4 (phase 13)

`QIQTH/HProvGrounding.lean` (4+ decls std-3 + axiom-free projector). THE LEG MAP: hProvP =
the 7-leg first-order diff-under-∫ bundle at the DIAGONAL window [0,u] (heat-time u, no −εₘ
cap). DISCHARGED: legs 2/4 (Fubini on the window-u joints) + leg 7 (the base-general
innerZ_line_hasDerivAt + the reusable FrozenHdiffLeg family at moving base x). THE HONEST
REMAINDER: snbx + **hFint (THE GENUINE CARRY — the diagonal window reaches the singular
endpoint τ→0; the capped-ceiling engine needs a positive lower cap and does NOT apply)** +
the dominator triple + the z-level core. M-uniformity VACUOUS (no m on the diagonal).
THE J4-444 "diagonal ≠ frozen" claim now EXPLAINED: same engines, window/base-general — the
only genuine obstruction is the singular endpoint blocking the integrability legs.
`v2Census_phase13`. raw 0; build ~50s. NEXT: J4-471 = hFint via the bulk⊕sliver split (the
J4-444/445 hGint pattern at the witness-value order). NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-471: the diagonal hFint DISCHARGED — the trivial route; the split rule
## enforced on the monolithic threading

`QIQTH/HFintDiagGrounding.lean` (2 decls std-3). **THE GATE:** the diagonal kernel is the
witness VALUE (zeroth order, one derivative below the hGint kernel); its envelope
(witnessValue_gate_envelope_prod) carries NO 1/(2τ) slope ⟹ the two-Gaussian pairing peak
is UNIFORM on (0,u) ⟹ the profile is BOUNDED a.e. ⟹ interval-integrable via
Integrable.mono' against the constant — **NO bulk⊕sliver split, no singular engine** (the
J4-444/445 machinery audited and correctly found unnecessary at this order).
`pairing_intervalIntegrable_fullWindow` (the uncapped engine) + `hFint_diag_grounded`
(from {hFzero, hWitDomEvery, hFdomEvery, hFintMeas}). **THE NAMED WALL (the split rule in
action):** the monolithic ~330-hypothesis v2Census_phase14 threading TYPE-CHECKED but
elaborates in ~50-100 min (~125 GB WS) — REMOVED per the <5min rule, recorded verbatim as a
named carry; the restructured lightweight transport = J4-472. The reduced module builds in
29s — the wrap-up discipline vindicated (the agent had burned ~3.5h on the monolith before
the orchestrator nudge). raw 0. NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-472: the phase14 transport at the CORRECT granularity — 26s; the phase
## tower has ZERO downstream consumers

`QIQTH/Phase14Transport.lean` (1 decl std-3). **THE COST ANATOMY (recorded for all future
phase-threading):** phase14 ≟ phase13 in ONE of ~85 binders, but a standalone Core-producing
phase14 must APPLY the phase13 body to all ~85 giant-typed args, whose dependent-binder
substitution recursively defeq-unfolds vanVleckGatedWitness/leviSeries/AmplitudeDerivativeDataOn
— the 50-100min/125GB blow-up is the APPLICATION itself, intrinsic, not removable by
structure-packs. `hRemainderDiag_reconstruct` relocates the integration to the
hRemainderDiag ∃/∧ shape (touches NO 85-binder Π): 26s. **★ THE STRUCTURAL FINDING:**
v2Census_phase14 is referenced NOWHERE downstream — the a₁ capstone consumes the bundled
A1R6GateSlots package and applies the census body EXACTLY ONCE; the phase tower is an
audit/census surface. The deferred monolith is content-free (its correctness was witnessed
by the J4-471 type-check); the right inlining point = the A1R6GateSlots assembly.
raw 0; build 26s module. NEXT: J4-473 = the assembly-point inline (or the honest defer per
the zero-consumer finding). NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-473: htermBox WIRED + hpd2diag consolidated (the box atoms)

`QIQTH/BoxAtomsGrounding.lean` (3 decls; std-3 + axiom-free ledger). **THE GATES:**
(hpd2diag) the transparency hypothesis REFUTED on two independent counts — the gate is
τ-INDEPENDENT (a hard spatial gate; the J4-443 τ-transparency pattern is a category error
here) AND the ungated pd-pd supplier keys the VARYING base vs the demanded fixed centre 0 —
honest consolidation onto the canonical NonLeviBoxContinuity.hpd2 (diagonal j := i).
(htermBox) a GENUINE WIRE — the census atom is the x-slot orientation, EXACTLY produced by
the banked IterEContinuity.iterE_jointContinuousOn per box (NOT the J4-394 z-slot family —
the slot-orientation trap caught by reading the headers, not trusting the queue hint;
LeviMTest's own M0 note documents the x-slot need). `box_atoms_residuals`: hIterBase +
hIterStep replace htermBox; hPd2Full hosts hpd2diag. raw 0; build 47s.
NEXT: J4-474 = the iterE rungs (hIterBase/hIterStep). NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-474: the iterE rungs grounded — the htermBox chain closed to the x-slot
## parts + the rung dominations

`QIQTH/IterRungGrounding.lean` (4 decls; std-3 + axiom-free ledger). **THE GATES:**
(hIterBase) the SLOT GATE — the census base is the x-slot with VARYING Laplacian base p.2;
the banked N2 is the z-slot with the FIXED base 0 (what makes N3's metric factors constants)
— no transport; the N2 ROUTE re-oriented honestly to hDerivX + hLapX. (hIterStep) a GENUINE
WIRE — the banked outer engine produces the succ rung from the per-rung Ioc 0 1 domination
(the IH not needed — a stronger step); hDom honestly carried per rung (the IterEContinuity
R-dom residual, verified against the banked census dominations — different shape).
`htermBox_chain_final`: the whole ∀k family from the deepest carries.
`rung_residuals`: hDerivX · hLapX (VARYING-base — harder than N3) · hDom · hRestBox.
raw 0; build 47s. NEXT: J4-475 = XSlotBaseParts (hDerivX/hLapX with the varying-p.2
metric/Christoffel continuity N3 drops). NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-475: hLapX DISCHARGED — the varying-base metric continuity was FREE

`QIQTH/XSlotBaseParts.lean` (4 decls; std-3 + axiom-free ledger). **THE GATE RESOLUTION:**
unlike N3 (fixed base 0 ⟹ the metric factors are CONSTANTS), the varying-base gi p.2 /
christoffel p.2 vary — but a C² field's continuity is banked: hgiC (the exact
AssemblyLadderR5 binder) + hChr's ContDiff ⊤ give both via .comp continuous_snd. hLapX
demands NO new Laplacian carry — only the geometry inputs + hpd1X/hpd2X (the N3 partial
atoms re-based to p.2). hDerivX = an irreducible ∂_τ LEAF (no metric content; the honest
class N2 also kept). **THE X-SLOT LEDGER: the ENTIRE htermBox census family is grounded to
{hgiC/hChr geometry + the witness-slice leaves hDerivX/hpd1X/hpd2X + hDom +
hPd2Full/hRestBox}.** Honest caveat: NOT geometry-alone — the witness-slice leaves are
genuine (their reduction = the J4-443 parametrix chain-rule machinery, a separate brick).
raw 0; build 47s. NEXT: J4-476 = WitnessSpatialPartialsX (the leaves via the chain rule).
NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-476: the witness-slice leaves — off-gate LANDED, in-gate REDUCED, the
## boundary the honest carry

`QIQTH/WitnessSpatialPartialsX.lean` (10 decls; std-3 + axiom-free projector). THE SLOT
AUDIT: hpd1X is DEFEQ witnessFieldDeriv (an rfl bridge!) but the banked joint-continuity
covers a DIFFERENT parameterization (τ fixed, field along update, z over K) — no transport;
the reduction went through THE GATE DICHOTOMY: off-chart/off-gate ⟹ all three leaves are
IDENTICALLY 0 (banked zeros — DISCHARGED); in-gate ⟹ the ungated C∞ composite (hpd1X, the
J4-443 transparency at z=0) / the banked heatParametrix τ-derivative joint continuity
(hDerivX). THE GATE-BOUNDARY ISSUE honest and real: the τ-independent SPATIAL set-gate at
the varying base can fail on closedBall 0 R — the boundary gluing (hBoundary) = the
irreducible carry at this granularity. The leaves ledger: hOffGate ✓ · hInGate reduced ·
hBoundary carried · hGeom verbatim. raw 0; build 49s.
NEXT: J4-477 = LeafBoxSplice (the single-hBoundary box-family reduction).
NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-477: the leaf splice from ONE hBoundary — ⚠ the all-R census forces the
## GLOBAL-CUTOFF regime (honest scoping)

`QIQTH/LeafBoxSplice.lean` (3 decls; std-3 + axiom-free projector). THE MINIMAL hBoundary:
the small-R/box-inside-gate route (closedBall 0 R ⊆ interior (S 0)) — no gate boundary
crossed; the in-gate reductions apply uniformly via ContinuousOn.congr; hpd2X (NO banked
in-gate lemma existed) assembled from hpd1X_ingate_eq + pd_congr_of_eventuallyEq — no new
analytic wall. **⚠ THE ALL-R AUDIT:** hIterBase_xslot_grounded quantifies over ALL R, so
the ∀R form forces interior (S 0) = univ — this route lands the GLOBAL/CONSTANT-CUTOFF
regime; a genuinely bounded gate needs the strictly-heavier boundary-vanishing route
(smooth piece → 0 at ∂(S 0)) — DEFERRED, documented. THE SPLICE LEDGER: the htermBox chain
= {hGeom ∧ hSmooth (parametrix/composite box regularity) ∧ hBoundary ∧ hDom + hRestBox}.
raw 0; build 49s. NEXT: J4-478 = SmoothCarrierGrounding. NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-478: the smooth carriers — hComposite2 → the chart Hessian; THE THREAD
## CONVERGENCE CONFIRMED

`QIQTH/SmoothCarrierGrounding.lean` (4+ decls; std-3 + axiom-free ledger). All three
hSmooth carriers factor DEFEQ through the C∞ profile (radialCutoff·heatParametrix).
**hParamDeriv FULLY GROUNDED** (the τ-independent cutoff pulls out; the banked
chartComposed_dtau_jointContinuousOn verbatim). **hComposite1 FULLY GROUNDED** (pd_comp +
profPd_composed — 4 banked factors). **hComposite2 honestly REDUCED**: pd_pd_comp_local +
profPdPd_composed (8 banked factors) + the second block carrying hWc2cont = THE CHART
HESSIAN. **★★ THE THREAD CONVERGENCE (audited, confirmed):** hWc2cont is the SAME 2nd-order
chart-jet atom the queued C₂/hcont2 derivative-sup chain needs — the htermBox chain and the
sup chain converge on ONE geometric wall: the second field-jet of the uniform inverse chart
(the J3 2nd-order analogue; FlowJointRegularity/BasepointFDeriv territory). No fresh wall.
Dont-undercredit: the parametrix jets (value/first/second) + the cutoff jets were ALL
banked; only the manifold product rules were new threading. raw 0; build 36s.
NEXT: J4-479 = ChartSecondJet (THE CONVERGENT WALL — the 2nd-order IFT + the forward 2nd
jet, the J4-433/435 chain one order up). NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-479: THE CONVERGENT WALL — the 2nd-order IFT DERIVED; the reduction to
## ONE forward-2nd-jet atom

`QIQTH/ChartSecondJet.lean` (4 decls std-3). **THE STAR: the 2nd-order IFT identity DERIVED
first-try** — pure algebra differentiating the banked ring-inverse identity by the chain
rule (hasFDerivAt_ringInverse outer, fderiv²φ middle, Iφ inner): fderiv(fderiv W)(φ v₀) =
(−mulLeftRight Iφ Iφ) ∘L (fderiv²φ ∘L Iφ); the germ transfer by congr_of_eventuallyEq;
pure Mathlib, no chart internals, no .choose. **THE REDUCTION**
(chartSecondJet_continuousOn_of_forward2): the chart-Hessian base-continuity from ONE named
atom hFwd2 (the forward SECOND jet joint continuity) + the BANKED-UNCONDITIONAL first-order
layer (J4-435 made forwardFlowJet_continuousOn/chartFieldJacobian_continuousOn
unconditional — inherited for free). hFwd2 correctly NOT forced: needs C³ flow regularity
(only C² banked) + the second-variation Grönwall — a genuine multi-brick ODE effort,
deferred per the split rule. NOTED: the two consumers carry DIFFERENT shapes (hWc2cont
pd-iterated over field points vs hcont2 joint over base) — the operator⇄pd bridge is
separate downstream work. raw 0; build 68s.
NEXT: J4-480 = Flow3Regularity (the C³ velocity slot — phase 1 of the hFwd2 effort).
NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-480: C³ was ALREADY BANKED (the C⁴ overlap route) — the hFwd2 velocity
## slot DONE

`QIQTH/Flow3Regularity.lean` (2 decls std-3). THE GATE VERDICT: the direct contDiffAt2
tower is bespoke (three explicit Fréchet layers) and structurally caps at C² — BUT the
tower is NOT capped: `ChartThirdJet.uniformFlowExp_contDiffAt_four` (J4-192!) banks C⁴ via
the unconditional ExpMap C⁴ tower + the ODE-uniqueness overlap bridge.
`contDiffAt3_uniformFlowExp` = .of_le (3≤4), ONE LINE; the price = the reachability guard
‖v‖ < expRho z (the injectivity ball). `forward2_velocitySlot` = the J4-434 TERM-2 pattern
one order up (fderiv_right twice + continuousAt). The J4-479 "only C² banked" claim was
STALE for the regularity half — the dont-undercredit pattern's ~10th strike this campaign.
REMAINING for hFwd2: the base-slot 2nd-variation Grönwall (hbaseJ2) + the K-uniform
reachability radius. raw 0; build 51s. NEXT: J4-481 = SecondVariationModulus (the exposure
+ the Grönwall + the weld — THE CONVERGENT WALL falls if it lands). NOT a₁ = R/6.

---
## ★ J4-481: the 2nd-variation EXPOSED + the component ODE — the hbaseJ2 groundwork

`QIQTH/SecondVariationModulus.lean` (2 decls std-3). **THE EXPOSURE LANDED:**
`uniformFlowExp_secondVar_spec` re-runs the compiled R2-a/b construction KEEPING the
discarded endpoint identification — the full triple (the base Jacobi field Jf0, the DOUBLED
second-variation field Vf along (tube, Jf0), the endpoint identity L₂ δ = (Vf δ 1).2.1) —
the J4-435 exposure one order up; the residue was PURE SPEC-EXPOSURE (the operator was
built in R2-a/J4-67; only _hLeq was discarded). **★ THE KEY NON-OBVIOUS FINDING:** the
naive full-doubled-norm Grönwall FAILS hbaseJ2 — the full norm is dominated by the .1-slot
(∝δ, b-independent), so it cannot deliver the ∝‖b‖ factor the double opNorm requires; the
.2-COMPONENT ODE (the δ·b-bilinear curvature source) is the correct route —
`secondVar_snd_hasDerivAt` LANDED (the inhomogeneous scalar-Jacobi ODE;
linODE_twopoint_diff_bound already accepts inhomogeneous sources). THE WALL DOES NOT FALL
YET: the two-point Grönwall + the double opNorm + the z₀-weld = J4-482. raw 0; build 59s.
NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-482: THE GRÖNWALL LANDED — the wall-felling ODE step

`QIQTH/HbaseJ2Gronwall.lean` (5 decls std-3). **secondVar_snd_twopoint_diff_bound** — the
two-point bound on the .2-component ODE via `linODE_twopoint_diff_bound` with the source
separation from `clm2_apply_telescope` (the pure-CLM trilinear telescope: coefficient +
.1-slot + base-Jacobi parts) — the J4-481 finding honoured. **THE M₃/D²F SEPARATION
LANDED** (`geodesicField_fderiv2_diff_bound` — the M₂ exists_isMaxOn pattern one order up;
dont-undercredit: `contDiff_fderiv2_geodesicField` was ALREADY BANKED in ExpMapContDiff2).
Also: `secondVar_fst_hasDerivAt` (the .1 homogeneous ODE) + `linODE_growth_bound`.
THE WALL HAS NOT FALLEN YET: the concrete instantiation at the two exposures + the
fderiv² = endpoint bridge + the double opNorm → hbaseJ2 (J4-483); the z₀-weld → hFwd2
(J4-484). Pre-banked: the doubled-field fderiv projections, the generic inhomogeneous
engine, the Jacobi bounds — a telescope + Grönwall assembly, not an ODE-existence effort.
raw 0; build 42s. NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-483 (673c7b50): hbaseJ2 DISCHARGED — the base-slot second-jet modulus

`QIQTH/HbaseJ2Assembly.lean` (4 decls std-3). `uniformFlowExp_fderiv2_base_modulus`: ∃Λ₂≥0
uniform over K, ‖fderiv²(uniformFlowExp q)v − fderiv²(uniformFlowExp q')v‖ ≤ Λ₂‖q−q'‖ for
q,q'∈K, ‖v‖<expRho q/q'/ρ_K; Λ₂ = 3M₂²e^{Lsep}e^{4Kf} + M₃e^{Lsep}e^{3Kf}. The J4-482
Grönwall instantiated at the two second-variation exposures via
`secondVar_endpoint_seed_diff_bound` — EVERY hypothesis discharged from banked material (the
tube separation, the compactness maxima Kf/M₂, the D²F M₃ separation, the .1-slot &
base-Jacobi bounds, the inhomogeneous growth). The endpoint bridge
`fderiv2_apply_eq_of_hasFDerivAt` ((apply b)∘fderiv chain rule + uniqueness; C²-at-v from
contDiffAt3 under the reachability guards); the double `opNorm2_le_bound` closes the sup.
Pure instantiate/discharge/bridge/opNorm — the J4-435 first-order template one order up. The
two expRho reachability guards = the price of the C²-at-v bridge, reconciled in the weld.
⚠ NOTE: a sibling VACAREA-1 job now shares the working tree (its VacuumAreaLaw campaign);
banking uses explicit paths only. raw 0; build 38s module.
NEXT: J4-484 = Hfwd2Weld (THE WELD — the wall falls). NOT a₁ = R/6 (CONDITIONAL).

---
## ★★★ J4-484 (c512a563): THE CONVERGENT WALL — a PROVED CHAIN gated by the ONE
## (I1) reachability input

`QIQTH/Hfwd2Weld.lean` (2 decls std-3). `uniformFlowExp_forward2_continuousOn_of_reach` =
THE WELD: the z₀-anchored triangle (the J4-435 first-order weld one order up) —
forward2_velocitySlot (velocity) + uniformFlowExp_fderiv2_base_modulus (base, Lipschitz in
z), abel'd → hFwd2 on K ×ˢ ball 0 uniformFlowRadius; `chartSecondJet_continuousOn_of_reach`
feeds it to chartSecondJet_continuousOn_of_forward2 ⟹ the chart-Hessian base continuity.
**THE ENTIRE SECOND-JET ARCHITECTURE (velocity + base → hFwd2 → chart Hessian) IS NOW A
PROVED CHAIN** — no second-variation ODE / regularity work remains; both the htermBox
(hWc2cont) and the C₂ (hcont2) consumers are served (modulo the operator⇄pd bridge).
**⚠ THE ONE REMAINING GATE (I1):** hReach = ∃ρ>0 ∀q∈K, ρ ≤ expRho q — NOT provable in-repo
(expRho is an irreducible Classical.choose with no banked continuity/lsc/uniform lower
bound; uniformFlowRadius is a separate .choose); this is the repo-WIDE
uniform-injectivity-radius carry (hr_lt across CommonNondegRadius/UniformExpSecondJet/…,
labelled "UNPROVABLE" in UniformFlowNondeg). Carried honestly at the hFwd2 boundary.
Verified std-3 in isolation (lake build QIQTH.Hfwd2Weld green). ⚠ THE WHOLE-LIBRARY BUDGET
SWEEP is transiently RED — blocked by the SIBLING VACAREA-1 job's uncommitted WIP
(VacuumAreaLaw.lean:348 type error + sorries), NOT by this brick; re-run once the sibling's
file goes green. NEXT: J4-485 = ExpRhoLSC (interrogate (I1)). NOT a₁ = R/6 (CONDITIONAL).

---
## J4-485 (b0c7de50): THE (I1) VERDICT = GENUINE GEOMETRIC INPUT

`QIQTH/ExpRhoReachability.lean` (2 decls std-3). THE INTERROGATION of the wall's last gate
hReach (∃ρ>0 ∀q∈K, ρ ≤ expRho q): expRho is Classical.choose of a downward-closed radius set
— an ARBITRARY, non-maximal admissible radius, marked irreducible. The wall needs the swap
∀q∃ρ ↝ ∃ρ∀q over compact K = positive compact inf = lsc of expRho, which GENUINELY FAILS for
a non-maximal .choose (irreducible forbids recovering anything past expRho_pos). The
geometric fact is TRUE-in-principle (injectivity radius of a smooth spray is lsc) but its
discharge needs a maximal-radius RECAST + the injectivity-radius-lsc theorem (ABSENT from
Mathlib) + domination of the separate opaque uniformFlowRadius — not a loop-brick.
**VERDICT: GENUINE INPUT** — hReach joins the a₁ labelled geometric-input list (the
option-(b) precedent), carried until an injectivity-radius-lsc campaign discharges it.
LANDED: the order-swap diagnosis (pointwise reachability is FREE; only the swap is hard) +
the standard-form interface `chartSecondJet_continuousOn_of_uniform_injectivity_radius`.
Dont-undercredit: repo-wide known (UniformFlowNondeg "UNPROVABLE"; CommonNondegRadius "NOT
≤ expRho in general") — this brick audits it to a firm verdict. raw 0 (isolation).
NOTE: the sibling VACAREA job's git-add swept the J4-485 AxiomAudit pins + committed a green
VacuumAreaLaw — the whole-library budget can now run. NOT a₁ = R/6 (CONDITIONAL).

---
## ★★★ THE SECOND-JET / CONVERGENT-WALL ARC COMPLETE (J4-476..485)
The htermBox witness-leaf chain and the C₂ derivative-sup chain were traced to ONE shared
geometric wall (the 2nd field-jet of the uniform inverse chart, J4-478), which was then
felled to a PROVED CHAIN: the 2nd-order IFT (J4-479) · C³ from the banked C⁴ route (J4-480)
· the 2nd-variation exposure + component ODE (J4-481) · the two-point Grönwall (J4-482) ·
the hbaseJ2 assembly (J4-483) · THE WELD → hFwd2 → chartSecondJet (J4-484). The SINGLE
residual gate = (I1) the uniform injectivity radius (J4-485 verdict: genuine geometric
input, repo-wide, joins the a₁ labelled-input list). a₁=R/6 CONDITIONAL.

---
## ★ J4-486 (d0daa045): the operator⇄pd bridge — TWO HONEST FINDINGS on the consumers

`QIQTH/OperatorPdBridge.lean` (3 decls std-3). `pd_pd_component_eq` (THE COORDINATE GATE,
pure Mathlib — the PullbackMetric CLM-contraction pattern one order up) +
`chartSecondJetComponent_continuousOn_of_reach` (the J4-484 operator result in pd-coordinate
form, gated by hReach). **★ FINDING 1:** hWc2cont (SmoothCarrier) is a FALSE TWIN — the
field-Hessian of the SINGLE base-0 chart at a varying FIELD point, NOT a base-varying jet —
ALREADY discharged UNCONDITIONALLY by ChartJetFactsDischarge.hWc2cont_of_contDiffOn_ball
(single-chart C²-on-ball, banked+wired); needs neither (I1) nor this bridge; the J4-478
"convergence" claim OVERSTATED it (an honest correction). **★ FINDING 2:** hcont2
(BaseSlotAmpDeriv C₂) IS genuinely base-varying — its raw-chart 2nd-jet coordinate pd²(W_z·a)
0 is DELIVERED here on the ONE (I1) hReach input; the residue = the manifoldAmp 2nd-deriv +
first-jet + chain-rule assembly (pure bookkeeping, J4-487). raw 0; build 31s module.
NEXT: J4-487 = AmplitudeSecondJet (the 4-block chain-rule ⟹ C₂/M₂chart/Sconst modulo (I1)).
NOT a₁ = R/6 (CONDITIONAL).

---
## ★★ J4-487 (4bb7857f): C₂ GROUNDED MODULO (I1) — the sup family's last slot closed

`QIQTH/AmplitudeSecondJet.lean` (4 decls std-3). Gate (a): `manifoldAmp_fderiv2_continuous`
— the J4-436 affine-in-τ trick ONE ORDER UP (manifoldAmp τ = c₀ + τ·c₁ ⟹ fderiv² =
fderiv²c₀ + τ·fderiv²c₁, each C² ⟹ jointly continuous). Gate (b): the J4-478
`pd_pd_comp_local` 4-block assembly on chartAmp = manifoldAmp ∘ W_z — Hessian/gradient/
first-jet blocks from the amplitude Hessian + banked jets, and the raw-chart SECOND-jet
block = the J4-486 `chartSecondJetComponent` delivery (lifted U → the product box).
`hcont2_of_reach` = the EXACT supConstant_phase3 hcont2 slot (gated by (I1) hReach + the
standing geometric carries); `supConstant_phase4` wires it: **C₂ GROUNDED MODULO (I1)** —
M₀ unconditional ∧ M₁ geometric ∧ M₂ on (I1) + bookkeeping. `pd_pd_scalar_eq` = the scalar
coordinate gate. Dont-undercredit: every ingredient banked (the affine trick,
pd_pd_comp_local, the J4-486 jet) — pure assembly. raw 0 (isolation; ⚠ the sibling was
mid-editing VacuumAreaLaw at commit time). build 33s module. NOT a₁ = R/6 (CONDITIONAL).

---
## ★ J4-488 (6f5b1d1c): 6/7 C₂ carriers COLLAPSED — C₂ on (I1) + one germ residue

`QIQTH/C2CarrierCollapse.lean` (2 decls std-3). `c2_carriers_discharged`: SIX of the seven
supConstant_phase4 geometric carriers on a CONCRETE small ball, FROM THE BANK ALONE (none
needed hReach — all K-uniform without expRho): hUK (K∈𝓝 0), horigin (chartW0_displacement),
hunit (common_nondeg_radius), hreg (chartField_contDiffAt_reachable_uniform +
chartW0_rightInverse), hW0 (chartOrigin_continuousOn), hJac (chartFieldJacobian_continuousOn
+ the ring-inverse identity). `supConstant_phase5`: the sup family from (I1) hReach + the
SINGLE 2nd-order RESIDUE hid2 (the per-z 2nd-order IFT identity / right-inverse germ
φ_z∘W_z = id near 0, a distinct germ sub-brick, J4-489). C₀ unconditional · C₁
geometric-closed · C₂ on (I1)+hid2. The small-ball reconciliation = pure radius bookkeeping
over banked uniform radii (SupFamilyFirstOrder's flagged residual, now discharged). raw 0
(whole-library — the sibling VACAREA-3 committed a green VacuumAreaLaw, unblocking the
sweep). build 32s module. NEXT: J4-489 = Hid2Germ (the right-inverse germ → C₂ on (I1) alone).
NOT a₁ = R/6 (CONDITIONAL).

### J4-489 — Hid2Germ: the last C₂ carrier discharged — THE SUP FAMILY CLOSED ON (I1) ALONE
- **File:** `QIQTH/Hid2Germ.lean` (std-3, 4 public pins).
- **What lands:** `chartRightInverse_germ` (the right-inverse germ φ_z(W_z y)=y near 0) · `chartFDerivInverse_germ` (the per-y fderiv-germ `fderiv W_z y = Ring.inverse(fderiv φ_z (W_z y))`) · `hid2_discharged` (the per-z 2nd-order IFT identity = the `hid2` binder) · `supConstant_phase6` (the sup family supplying ALL SEVEN phase-4 carriers internally from the bank, leaving (I1) `hReach` the SINGLE carried input).
- **The gate / audit verdict:** `hid2`'s crux is `chartSecondJet_eq_of_forward2`'s `hgerm` (the fderiv-germ), which needs the RIGHT-inverse germ. The bank exposed only the LEFT germ (`W_z(φ_z v)=v`) plus the pointwise `φ_z(W_z 0)=0`. The right germ needs a **FRESH strict-IFT invocation but NO NEW INPUT** — re-run Mathlib's strict IFT on the nondegenerate φ_z (`HasStrictFDerivAt` from `contDiffAt2_uniformFlowExp` C² + `uniformFlowExp_common_nondeg_radius` unit, both already used by `c2_carriers_discharged`), then `localInverse_unique` (banked left inverse `=ᶠ` the strict-IFT inverse) ∘ `eventually_right_inverse`. A local diffeo has BOTH germs; the right germ is a THEOREM of the bank.
- **Outcome — C₂ ON (I1) ALONE:** C₀ unconditional · C₁ geometric-closed · C₂ on (I1) `hReach` alone, matching the convergent wall (J4-478). No second-order germ residue survives. **THE SUP FAMILY IS CLOSED ON (I1) ALONE.**
- **Don't-undercredit:** the abstract 2nd-order IFT algebra (`ChartSecondJet`) AND the first-order IFT-Jacobian identity (`ChartFieldJacobian`) were ALREADY banked; this brick supplies only the missing strict-IFT right-inverse germ both consumed. `hid2` was NOT a new input — it reduces to the same nondegeneracy + C² that discharged the other six carriers. Ball-radius bookkeeping reproduced (not reused: the exported ρ lacked the extra smallness margins).
- **Build:** 36s incremental (~56s replay). No sorry/:= True/admit. Import wired `QIQTH.lean:691` after `C2CarrierCollapse`.
- **⚠ a₁=R/6 remains CONDITIONAL** on (I1) `hReach` (the genuine uniform-injectivity-radius geometric input) + the banked convergence trio + the geometric wiring. The sup family being (I1)-closed is a structural milestone, NOT a₁=R/6.

### J4-490 — C2AggregatorPhase6: the (I1)-only C₂ sup family WIRED into the a₁ carry shape
- **File:** `QIQTH/C2AggregatorPhase6.lean` (std-3, 2 public pins). First application of the sup-family phase tower (phase1→6) into the downstream `amplitudeDataOn_concrete` collar carries.
- **What lands:** `collarRegime_mono` (the collar predicate `AmplitudeDataOnCollar` is antitone in the chart radius — pure implication from `‖z‖<r₀`, no analytic content) · `collarSupConstants_of_reach` (the three collar sup-constants — `|chartAmp|≤M₀`, `|−2·pd_i chartAmp|≤M₁`, `|pd_i pd_i chartAmp|≤M₂` — on a COMMON radius `r₀ = min ρ ρ₀ > 0`, from (I1) `hReach` ALONE).
- **The gate:** PASSED. `supConstant_phase6` is a proven std-3 theorem whose sole carried input is (I1) `hReach` (inhabited, not vacuous); the only new ingredient `collarRegime_mono` is a pure implication (no side-condition); the common radius `min ρ ρ₀` is inhabited. No false hypothesis.
- **hid2 removal:** the C₂ sup-constant is now drawn from `supConstant_phase6` (I1-only) rather than `supConstant_phase5` + a separate `hid2`-carry ⟹ the aggregator's downstream hypothesis list carries **no `hid2`**; its C₂ slot is (I1)-conditional. The three delivered bounds match `hM₀chart`/`hM₁chart`/`hM₂chart` verbatim.
- **Transport granularity:** `supConstant_phase6` applied ONCE and destructured; the C₀-on-ρ₀ and C₁/C₂-on-ρ conjuncts re-projected onto `min ρ ρ₀` via `collarRegime_mono`. The ~85-binder `phase4`/`vanVleckGatedWitness`/`leviSeries` Π NOT re-applied — monolith trap avoided, no defeq blow-up.
- **Don't-undercredit:** the entire (I1)-only sup family was already banked in `Hid2Germ.supConstant_phase6`; this brick is a thin adapter — the collar carry shapes already matched the phase-6 conjuncts verbatim.
- **Build:** 27s compile (48s wall). No sorry/:= True/admit. Import wired in `QIQTH.lean` after `Hid2Germ`. Both pins std-3 via direct `lake build` axiom prints. ⚠ Whole-library budget + AxiomAudit build DEFERRED — sibling `VacuumAreaLaw.lean` is mid-edit (VACAREA-5 WIP, broken import); isolation-verified instead. Re-run the full sweep once the sibling greens.
- **⚠ a₁=R/6 remains CONDITIONAL** on (I1) `hReach` + the banked convergence trio + geometric wiring. Routing the (I1)-only C₂ slot into the aggregator is plumbing toward the endpoint, NOT a₁=R/6.

### J4-491 — FarFieldMomentOrder: the far-field moment integral's τ-ORDER made EXPLICIT (O(1/τ))
- **File:** `QIQTH/FarFieldMomentOrder.lean` (std-3, 1 public pin `farFieldDom_integral_le`).
- **What lands:** `∫ farFieldDom τ M1F M2F Mqc z ≤ M1F·n·3/4/√τ + M2F + Mqc·(n+1)/(2τ)` — the far-field dominator's τ-order term-by-term: gradient **O(τ^{-1/2})**, mass **O(1)**, Hessian **O(1/τ) [dominant]**. The whole dominator is genuinely O(1/τ) (τ^{-1/2} < τ^{-1} as τ→0⁺).
- **New vs banked:** the far-field DOMINATION (`‖∫_far f‖ ≤ ∫ farFieldDom`, off-K witness-vanishing) was ALREADY banked (`FarFieldDecay`, J4-457); only the τ-order of `∫ farFieldDom` was recorded in PROSE (the "DOMAIN/TAIL GATE" verdict). This brick turns that prose into a THEOREM by integrating `farFieldDom` explicitly: linearity (`integral_add`/`integral_const_mul`, term-mode to dodge the rw-HOU trap) + the banked width-τ moment envelope `normPow_gauss_tau` (← `oneD_absMoment1/2`) + `gaussDdim_integral_eq_one` + `√τ·√τ=τ`.
- **The gate:** REACHABLE. `M1F/M2F/Mqc ≥ 0` are the SAME satisfiable global amplitude sups `FarFieldDecay.farField_decay_bound` carries (genuine ∀z sups); the moment bounds `∫‖z‖G≤n·(3/2)√τ`, `∫‖z‖²G≤n·2τ`, `∫G=1` are banked+true. No false pointwise inequality, no divergent width, no single-coordinate-vs-contraction trap. (`hM2F` unused — mass term coefficient 1 — harmless linter warning, not vacuity.) Did NOT need Sol.
- **⚠ HONEST DISTANCE — NOT reduced to (I1):** the far field is τ-order-CONTROLLED but by the GLOBAL (off-collar) sups `M1F/M2F/Mqc`, NOT by the (I1)-closed on-collar constants `M₀/M₁/M₂` of J4-490. Off K the witness vanishes ⟹ a pure Gaussian remainder, genuinely DISJOINT from the collar leg. So the far-field τ-order is now explicit; the on-collar leg (which carries the (I1) constants) is the complementary piece still open.
- **Transport granularity:** thin. No sup-family/vanVleck/leviSeries Π re-applied; banked lemmas applied once and destructured.
- **Build:** ~53s module (1m14s total). No sorry/:= True/admit. Import wired in `QIQTH.lean` after `C2AggregatorPhase6`.
- **⚠ a₁=R/6 remains CONDITIONAL** — this pins the far-field moment order; it is not the coefficient value and does not reduce the far field to (I1).

### J4-492 — OnCollarMomentOrder: the on-collar (near-diagonal) moment leg, (I1)-closed
- **File:** `QIQTH/OnCollarMomentOrder.lean` (std-3, 6 public decls). The COMPLEMENT of J4-491's far-field piece.
- **What lands:** `onCollarDom` (the near-diagonal Gaussian-moment envelope `M₀·(1/4τ²)·((‖z‖²+2τ)G_τ) + M₁·(1/2τ)·(‖z‖ G_τ) + M₂·G_τ`, Hessian↔M₀ / gradient↔M₁ / mass↔M₂) · `onCollarDom_eq_farFieldDom` (= `farFieldDom` under the (M₁,M₂,M₀) reorder, a `ring`) · `onCollarDom_nonneg`/`_integrable` · `onCollarDom_integral_le` (full space ≤ `M₁·3n/4/√τ + M₂ + M₀·(n+1)/(2τ)`) · **`onCollarDom_setIntegral_le`** (the same bound over ANY measurable domain A via `setIntegral_le_integral`, nonneg envelope) · **`onCollarMoment_order`** (headline specialisation to `collar(c√τ)`).
- **What it delivers:** the on-collar moment integral is τ-order **O(1/τ)** (dominant Hessian `M₀·(n+1)/(2τ)`; gradient O(τ^{-1/2}); mass O(1)), controlled ENTIRELY by the (I1)-closed collar constants M₀/M₁/M₂ — so the on-collar leg is **(I1)-closed** (unlike the far-field leg, whose sups are the global off-collar ones). Combined with J4-491's far-field O(1/τ), the FULL heat-trace remainder (collar ⊔ far field) is τ-order-controlled: on-collar by (I1) `hReach`, far field by the global Gaussian remainder.
- **The gate:** REACHABLE + correctly CENTERED (moments `‖z‖`,`‖z‖²` relative to the diagonal center 0 of `gaussDdim τ`; the centering trap avoided); M₀/M₁/M₂ = the nonneg (I1)-closed sups of `collarSupConstants_of_reach`; any measurable domain keeps a nonneg integrand ⟹ restriction sound. No vacuity.
- **New vs banked:** the heavy analytic core (full-space Gaussian-moment computation, `normPow_gauss_tau`, `gaussDdim_integral_eq_one`, integrability) was already banked in `FarFieldMomentOrder` and reused VERBATIM (`onCollarDom` is the SAME Gaussian-moment object under the term reorder). Genuinely new: keying the dominator to the on-collar sliver-coefficient structure (so it carries the COLLAR constants) + the domain restriction to the near-diagonal region. Thin adapter; did NOT need Sol.
- **Transport granularity:** no 85-binder Π re-applied; `farFieldDom_integral_le`/`_nonneg`/`_integrable` applied ONCE each + spliced via one `ring` equality + `Integrable.congr`/`setIntegral_le_integral`.
- **Build:** 28s compile (48s wall). No sorry/:= True/admit. Import wired in `QIQTH.lean` after `FarFieldMomentOrder`. All six std-3 via direct `lake build` axiom prints. ⚠ Whole-library budget + AxiomAudit build DEFERRED — sibling `VacuumAreaLaw.lean` is mid-edit (VACAREA-6 WIP, `le_or_lt` unknown-ident at :975); isolation-verified instead. Re-run the full sweep once the sibling greens.
- **⚠ a₁=R/6 remains CONDITIONAL** on (I1) `hReach` + the banked convergence trio + geometric wiring. Both remainder legs are now individually τ-order-closed; the remainder-assembly capstone (collar ⊔ collarᶜ split → full remainder τ-order) is the natural J4-493.

### J4-493 — RemainderAssembly: the remainder-assembly capstone — full heat-trace remainder τ-order = single O(1/τ)
- **File:** `QIQTH/RemainderAssembly.lean` (std-3, 2 public decls).
- **What lands:** `farFieldDom_setIntegral_le` (the far-field mirror of `onCollarDom_setIntegral_le` — the far-field bound over ANY measurable domain) · **CAPSTONE `remainderIntegral_order`**: for a generic integrand `f` with `Integrable f`, dominated pointwise by `onCollarDom` on `collar r₀` AND by `farFieldDom` on `(collar r₀)ᶜ`, `|∫ f| ≤ (M₁·n·3/4/√τ + M₂ + M₀·(n+1)/(2τ)) + (M1F·n·3/4/√τ + M2F + Mqc·(n+1)/(2τ))` — a SINGLE explicit **O(1/τ)** (dominant Hessians `M₀·(n+1)/(2τ)` + `Mqc·(n+1)/(2τ)`; gradients O(τ^{-1/2}); masses O(1)).
- **The gate:** split FAITHFUL + non-vacuous. `integral_add_compl (collar_measurableSet r₀) hInt` gives `∫_collar f + ∫_collarᶜ f = ∫_full f` exactly; both pieces integrable via `Integrable.integrableOn`; the two dominations simultaneously satisfiable by real objects (`sliverIntegrand_on_collar` / `farField_ptwise_bound`) and by `f:=0`. No whole-space-coercivity trap (region-restricted hyps). No false hypothesis.
- **⚠ HONEST — the FAITHFUL PROXY, not yet the concrete aggregator object:** stated for a generic dominated `f`, NOT wired to the concrete integrand `IchartResidual − hessGaussFactor·qc`, because the two legs use disjoint constant families (on-collar M₀/M₁/M₂ (I1)-closed vs far-field M1F/M2F/Mqc global) and the concrete dominations live in separate files (`SliverBoundOnCollar` / `FarFieldDecay`; `hcomp_final4` already wires the far leg). With that proxy the full heat-trace remainder IS τ-order-controlled as one O(1/τ): on-collar by (I1) `hReach`, far field by the global Gaussian remainder.
- **New vs banked:** thin capstone reusing `onCollarDom_setIntegral_le` (J4-492) + `farFieldDom_integral_le`/`_nonneg`/`_integrable` (J4-491) + Mathlib `integral_add_compl`/`norm_integral_le_integral_norm`/`integral_mono_ae`/`setIntegral_le_integral`. Mirrors the `hcomp_final3` split idiom (uses `integral_add_compl` for the exhaustive split vs `integral_inter_add_diff` there). Did NOT need Sol.
- **Transport granularity:** banked lemmas applied once each + a short `calc`; no sup-family Π re-application. Build 28s module (49s total).
- **⚠ a₁=R/6 remains CONDITIONAL.** The remainder τ-order is now assembled; the genuine a₁ wall is BEYOND any τ-order bound: (1) promote the proxy to the concrete integrand (discharge the two dominations for `IchartResidual − hessGaussFactor·qc`; `hcomp_final4` is the far route), then (2) the LEADING-COEFFICIENT extraction (the O(1) constant term surviving the O(1/τ) remainder), then (3) the R/6 identification itself.

### J4-494 — ConcreteRemainderOrder: the concrete-integrand promotion (with a genuine annulus gate-catch)
- **File:** `QIQTH/ConcreteRemainderOrder.lean` (std-3, 2 public decls). Promotes the J4-493 generic proxy to the REAL heat-trace remainder integrand `IchartResidual − hessGaussFactor·(chartAmp·F)`.
- **What lands:** `concreteIntegrand_on_collar_le` (on `collar(c√τ)`, `‖f‖ ≤ onCollarDom τ M₀ 0 0 z`, from the banked on-collar identity `hon_concrete` + `|hessGaussFactor|≤(‖z‖²+2τ)/(4τ²)·G` + the amplitude-diff sup `|Aamp·F−chartAmp·F|≤M₀`) · **CAPSTONE `concreteRemainder_order`**: `|∫ f| ≤ M₀·(n+1)/(2τ) + (Bcomp₂/√τ + far-field O(1/τ))` — a single explicit **O(1/τ)**, NO generic dominated-`f` hypothesis left (only banked satisfiable gate/amplitude/integrability carries).
- **⚠ THE GATE — a genuine unsatisfiability CATCH:** the proxy demands a POINTWISE far domination `|f|≤farFieldDom` on ALL of `(collar r₀)ᶜ`, but the banked far-field pointwise bound holds only OFF K (witness=0), and the on-collar identity only on `collar(c√τ)`; between them the **annulus `{‖z‖>c√τ}∩K`** has the witness present+un-expanded. A two-way pointwise split at one r₀ would force `K = collar r₀` — UNSATISFIABLE (the exact geometric-coincidence trap the gate warned of). So the concrete off-collar leg routes through the banked INTEGRAL-level gate `hcomp_final4` (annulus via `(ρ−1)`+cubic jet, far via off-K Gaussian), carrying an honest `Bcomp₂/√τ = O(1/√τ)` annulus term (still O(1/τ)-dominated) — NOT a false pointwise farFieldDom bound. The concrete integrand IS genuinely integrable (`hfInt`, satisfiable).
- **New vs banked:** NOT pure wiring — the off-collar concrete handling was already banked at integral level in `hcomp_final4`/`hcomp_final3` (annulus + far in one bound); the ONE new brick = the on-collar pure-Hessian pointwise bound `concreteIntegrand_on_collar_le` (missing from the bank). Did NOT need Sol.
- **Transport granularity:** each heavy banked lemma (`hon_concrete`, `hcomp_final4`, `onCollarDom_setIntegral_le`, `farFieldDom_integral_le`) applied EXACTLY once; `data` kept opaque; no 85-binder census Π re-application.
- **Build:** ~29s module (49s total). No sorry/:= True/admit. Import wired in `QIQTH.lean` after `RemainderAssembly`.
- **⚠ a₁=R/6 remains CONDITIONAL.** The concrete remainder is now O(1/τ)-controlled; the genuine a₁ wall is BEYOND: (1) discharge `hcomp_final4`'s remaining carries as (I1)-reachable (esp. `hform_gate` the `(ρ−1)` near-isometry annulus form, and `hAmpDiff`→`collarSupConstants_of_reach`), (2) the LEADING-COEFFICIENT extraction (the O(1) constant surviving the O(1/τ) remainder), (3) the R/6 identification itself.

### Sol consult #22 — the a₁=R/6 ENDGAME recut (after remainder-control complete, J4-494)
The remainder O(1/τ) control is now bookkeeping-complete; the genuine a₁ wall is BEYOND it. Ordered endgame:
0. **Retire the 2 capstone carries** first: (i) ground `hAmpDiff`→(I1) `collarSupConstants` [= J4-495], (ii) derive `hform_gate` from the chart near-isometry/cubic-jet data. Then restate `concreteRemainder_order` with neither exposed (only `hReach` remains).
1. **State the endpoint as a normalized limit:** Θ(τ):=(4πτ)^{n/2}Tr(e^{−τΔ}), target lim_{τ→0⁺}(Θ(τ)−vol M)/τ = ∫_M Scal/6. Local version: (θ_x(τ)−1)/τ → Scal(x)/6. LOCK CONVENTIONS (Laplacian sign, e^{−‖z‖²/4τ} normalization, Lebesgue vs chart-volume measure, which Jacobian/van-Vleck factors sit inside chartAmp) — factors of 2 and signs are easy to misidentify.
2. **⚠ THE q-AUDIT (do immediately, decisive):** rewrite the normalized trace as Θ(τ)=W₀+τW₁+E(τ); record the τ-power q with which the concrete residual enters E(τ). If E(τ)=τ^q∫R with |∫R|≤Cτ^{−1} then E/τ=O(τ^{q−2}): q>2 ⟹ coefficient-negligible (GOOD); q=2 ⟹ only O(1), may ALTER a₁ (need o(τ^{−1}) or explicit subtraction); q<2 ⟹ too weak. **An O(τ^{−1}) bound ALONE cannot select the coefficient** — the q-audit decides whether the remainder subsystem is coefficient-sufficient.
3. **Gaussian-rescaled normal form:** after exp-small gate removal, reduce to ∫ G_τ(z) H_x(z,τ) dz, rescale z=√τ w. (mostly wiring on the banked far-field machinery.)
4. **Generic 2nd-order Gaussian extraction lemma** (representation-independent): for H_x=H₀+τH₁+r with uniform 2nd-order Taylor remainder, (∫G_τ H − H₀(0))/τ → tr(D²H₀(0)) + H₁(0). Moments: ∫G_τ=1, ∫z^iG_τ=0, ∫z^iz^jG_τ=2τδ^{ij}. First deriv vanishes by oddness; quadratic term ½D²H(0)[z,z] contributes τ·tr(D²H(0)).
5. **Coefficient-grade negligibility** E(τ)/τ→0 (NOT mere boundedness) for higher Levi iterates, concrete residual, gate/off-chart, gluing, τ-dependent amplitude remainder.
6. **⚠ THE R/6 SIGN MECHANISM (crucial correction):** in normal coords J_x(z)=√det g = 1 − (1/6)Ric_x(z,z) + o(‖z‖²), i.e. D²J(0)[u,v]=−(1/3)Ric. **√det g ALONE gives −Scal/3·τ, NOT +R/6!** The +R/6 comes from the VAN-VLECK factor u₀=J^{−1/2}=1+(1/12)Ric(z,z)+o ⟹ D²u₀(0)=(1/6)Ric ⟹ tr=Scal/6; then (1/12)Ric_{ij}∫z^iz^jG_τ=(1/12)(2τ)Scal=τScal/6. Do NOT Taylor-expand the volume density alone and call it a₁. The general quadratic term is Ric_{ij}z^iz^j, NOT R‖z‖² (except isotropic/const-curv).
7. **Connect the 2nd jet to the actual first transport/Levi coefficient** — prove which representation `chartAmp·F` realizes (Gaussian contraction of the van-Vleck 2nd jet, OR the diagonal u₁(x,x); equivalent, don't double-count). No potential/endomorphism term for the pure scalar Laplacian.
8. **Globalize + finish by coefficient uniqueness:** uniform integrable bound → pass the limit through ∫_M → apply uniqueness of the normalized 1st-order coefficient.
**THE REAL WALL** = the coefficient-grade diagonal asymptotic (θ_x(τ)−1)/τ→Scal(x)/6, two non-negotiable ingredients: (a) analytic E(τ)/τ→0 after restoring the Duhamel prefactor (needs the q-audit ≥2), (b) geometric D²u₀(0)=(1/6)Ric = the GENERAL (arbitrary-metric) Jacobi-field/determinant second-variation theorem for exp — if VanVleckRadial only proves const-curvature it is NOT sufficient (that general 2-jet is the missing geometric theorem). ⚠ NO new injectivity-radius theorem needed for the LOCAL 2-jet; (I1) is for uniform collars/globalization only. Verdict: a₁=R/6 is NOT yet pure wiring — the E/τ→0 transfer AND the general effective van-Vleck 2-jet must both be built.

### J4-495 — AmpDiffGrounding: hAmpDiff DISCHARGED from (I1) (Sol #22 step 0(i))
- **File:** `QIQTH/AmpDiffGrounding.lean` (std-3, 2 public decls).
- **What lands:** `concreteIntegrand_on_collar_le_atz` (the per-point on-collar bound: given the amp-diff bound at a SINGLE `z ∈ collar(c√τ)`, `‖f z‖ ≤ onCollarDom τ M₀ 0 0 z`) · **CAPSTONE `concreteRemainder_order_reach`** (= `concreteRemainder_order`'s explicit O(1/τ) bound but with `M₀ := (collarK Liso c τ₀ + 1)·Mqc`, NO raw `hAmpDiff`).
- **⚠ THE GATE — a genuine region-mismatch CATCH:** the original `hAmpDiff : ∀ z, …` is stated FULL-SPACE but consumed only ON-collar; for concrete data `Aamp = rhoRatio·chartAmp₀` with `rhoRatio ~ exp(‖z‖²/4τ)` UNBOUNDED off-collar, the full-space `∀ z` sup is UNSATISFIABLE at any finite M₀ — a false binding. So M₀ binds to the (I1)-reachable collar constant `(collarK+1)·Mqc` on the SAME collar region where it is used (`collarK = exp(Liso·n·c³·√τ₀/4) > 0` from `rhoRatio_le_collarK`; `Mqc≥0` banked `hqcbdd`); off-collar is handled by `hcomp_final4`, which never touches the amp-diff sup.
- **What it delivers:** `hAmpDiff` is now DISCHARGED from (I1). Remaining substantive external hyps of the restated capstone: `hiso` (the (I1) near-isometry lower bound feeding `collarK`) + `hform_gate`/`hgate` (the annulus gate carries, unchanged) + the banked amplitude/integrability feeds. `hAampForm : Aamp = rhoRatio·chartAmp₀` is definitionally `rfl` for `amplitudeDataOn_concrete` (satisfiable, non-vacuous).
- **New vs banked:** mostly wiring + one small derivation; no Sol. The per-point bound = triangle: `Aamp·F − chartAmp·F = (rhoRatio−1)·(chartAmp₀·F)`, `|rhoRatio−1| ≤ collarK+1`, `|chartAmp₀·F| ≤ Mqc`. The (I1)-closed `collarK`/`rhoRatio_le_collarK`/`rhoRatio_pos`/`collarRegime` machinery was already banked in `AmplitudeDataOnCollar`.
- **Transport granularity:** capstone takes GENERIC `data` + `hAampForm` (not constructing `amplitudeDataOn_concrete`), so no 85-binder def unfolded; `hcomp_final4` + `rhoRatio_le_collarK` applied once each. Build 32s.
- **⚠ a₁=R/6 remains CONDITIONAL** — remainder-subsystem cleanup (region-matched grounding of a sup), NOT the coefficient value. Per Sol #22: next = discharge `hform_gate` (finishes the remainder subsystem), then the coefficient-facing walls (q-audit ≥2 + the general van-Vleck 2-jet).

### J4-496 — FormGateGrounding: hform_gate DISCHARGED — THE REMAINDER SUBSYSTEM FINISHED (Sol #22 step 0ii)
- **File:** `QIQTH/FormGateGrounding.lean` (std-3, 2 public decls).
- **What lands:** `hform_gate_of_jetSupply` (from a per-annulus-point chart JET SUPPLY `hjets` on EXACTLY `(collar(c√τ))ᶜ ∩ K ∩ {‖z‖<r}` derives the (ρ−1) form `IchartResidual − hessGaussFactor·(chartAmp·F) = hessGaussFactor·((rhoRatio−1)·(chartAmp·F))`) · **CAPSTONE `concreteRemainder_order_reach_form`** (= `concreteRemainder_order_reach`'s explicit O(1/τ) bound but with the raw `hform_gate` carry replaced by `hjets`).
- **The gate:** region-correct + satisfiable. `hjets` demanded on EXACTLY the annulus `hcomp_final4` consumes `hform_gate` on (same region + same `r`), NOT full space (the off-collar exp-blow-up trap J4-495 caught is avoided). The derived `hform_gate` matches the capstone's hypothesis verbatim. No false/vacuous hypothesis.
- **PURE WIRING — no new geometric estimate, no Sol:** the (ρ−1) annulus form was ALREADY a proved banked lemma `SlotInstantiationV.ichartResidual_sub_hess_form`, whose regime audit establishes it is OFF-COLLAR UNCONDITIONAL (no collar/r₀/τ₀ bound in its hyps). `hform_gate_of_jetSupply` is a one-line per-point `intro`/`obtain`/apply wrapper. Grepping the bank first paid off AGAIN — the form was essentially fully banked.
- **What it delivers — REMAINDER SUBSYSTEM FINISHED:** `hform_gate` discharged; NO raw analytic gate carry remains. The remaining substantive external hypotheses are now ONLY genuine geometric inputs — `hiso` ((I1) near-isometry lower bound), `hgate` ((ρ−1) annulus near-isometry: cubic-jet error + lower bound), `hjets` (the chart's actual off-collar jet supply) — plus banked amplitude/integrability feeds. (Honest caveat: `hjets`/`hgate` are genuine off-collar geometric carries, the legitimate geometric residue, NOT derived from `hiso`.)
- **Transport granularity:** `ichartResidual_sub_hess_form` applied once per annulus point + destructured; `concreteRemainder_order_reach` applied once; `data` kept opaque. Build 27s.
- **⚠ a₁=R/6 remains CONDITIONAL.** Remainder subsystem done; the COEFFICIENT walls are all still BEYOND (Sol #22): (a) the q-AUDIT (≥2, decisive next), (b) the Gaussian 0/1/2-moment extraction lemma, (c) the GENERAL arbitrary-metric van-Vleck 2-jet D²u₀(0)=(1/6)Ric. ⚠ IMPORTANT VERDICT: `VanVleckRadial.lean` is CONST-CURVATURE-ONLY (per git log "Constant-curvature: exact radial ODE") — NOT sufficient for the general coefficient; the general van-Vleck 2-jet needs its OWN generalization campaign.

### J4-497 — THE q-AUDIT (Sol #22 step 2) — ⚠⚠ CRITICAL VERDICT: the O(1/τ) remainder is COEFFICIENT-INSUFFICIENT (q ≈ 1 < 2)
- **ANALYTICAL-ONLY — no Lean pin** (correctly: the object whose τ-power would be pinned — the assembled traced Duhamel correction `E(τ)` — is NOT built in the bank; forcing a brick would be dishonest gold-plating). No code changes, nothing committed.
- **THE VERDICT:** q is effectively **q ≈ 1 (with a log endpoint), i.e. q < 2 — INSUFFICIENT.** The proven `|∫_z f| ≤ C/τ` is a FIXED-TIME parametrix-error z-integral bound, NOT an `E(τ)` bound. Under the only sensible assembly (banked `heatConv = ∫₀^τ ds ∫_z …`): the `(4πτ)^{n/2}` normalization supplies NO extra power (f already carries `gaussDdim`'s `(4πτ)^{−n/2}`; the C/τ constants collarK/Mqc/M1F/M2F are all O(1) in τ; normalization used up by `∫gaussDdim=1`); the Duhamel `∫₀^τ ds` supplies exactly ONE power ⟹ `|E| ≤ τ·(C/τ) = O(1)` ⟹ nominal q=1 ⟹ `E(τ)/τ = O(1/τ)` DIVERGENT, not o(τ). If the residual's heat-age is the inner Duhamel variable (`|r(s)|≤C/s`), `∫₀^τ(C/s)ds` LOG-DIVERGES at s=0 (the Sol #13 log-divergence the collar/tail match documents). Both readings < q=2.
- **Sol consulted (gpt-5.6-sol high) — INDEPENDENT AGREEMENT:** "q not yet defined; nominal one-fold Duhamel power q=1 with log endpoint; INSUFFICIENT (below q=2); merely improving O(s⁻¹)→o(s⁻¹) is NOT enough — the assembled traced source must be shown o(1) or O(s^α), α>0." Hierarchy: `r(s)=O(s⁻¹)`→log-div(insufficient); `O(1)`→`O(τ)`(marginal, may alter W₁); `o(1)`→`o(τ)`(negligible); `O(s^α)`→`O(τ^{1+α})`(q=2+α, good).
- **What this means (honest framing correction):** the remainder-control arc (J4-489..496) is a GENUINE τ-order bound and real work, but it does NOT by itself select the a₁ coefficient. The missing piece is NOT a sharper bound on the same object — it is (i) the ASSEMBLY connecting the fixed-time residual bound to `E(τ)` (the ds-convolution + trace normalization on THIS residual, unbuilt), and (ii) a TRANSPORT-CANCELLATION estimate showing the assembled O(1) source is `o(1)`/`O(s^α)` (the `u₀+τu₁` transport eqns must cancel the leading source — extract-not-bound).
- **Banked & real (don't-undercredit):** (a) the exact moment cancellation `hessGaussFactor_integral_zero` (∫hessGaussFactor=0 = the 2τ second-moment minus 2τ·1); (b) the parametrix trace `HeatParametrixTrace.parametrixDiagTraceInt`, `W₀=vol M`, `W₁=(1/6)∫_M R` — BUT `ud_0=1`, `ud_1=R/6` are CARRIED DeWitt-normalization hypotheses, NOT derived; (c) the full O(1/τ) remainder subsystem on genuine geometric inputs. The gap is the assembly + the sharper transport-cancellation source estimate.
- **⚠ CONVENTIONS TO LOCK (Sol #22 step 1) before ANY coefficient work:** (1) TIME identification — which of τ/s/(t−s) is the trace time vs the residual heat-age (currently gaussDdim uses τ, F uses s; heatConv implies ds-convolution but the concrete residual bound is fixed-(τ,s) — UNRESOLVED); (2) the exact Duhamel defect `(∂_t∓Δ)H` sign + convolution order + whether f enters directly or after the Σᵢ direction sum; (3) normalization placement (raw kernel density vs traced; when (4πτ)^{n/2} applied); (4) measure dz vs dvol_g, where √g absorbed, vanVleck^{±1/2} (code uses ^{−1/2}); (5) signs (Δ≥0 with e^{−τΔ}; Ricci/scalar sign for u₁=R/6; e^{−‖z‖²/4τ}).
- **⚠ a₁=R/6 CONDITIONAL — and the q-audit SHARPENS the honest distance: the O(1/τ) remainder subsystem is coefficient-INSUFFICIENT (q≈1). Remainder-control is complete as a τ-order bound but is NOT the coefficient-selecting step. Two non-negotiable remaining ingredients: (I) the transport-cancellation / o(1)-source estimate (the assembled `E(τ)`), (II) the GENERAL arbitrary-metric van-Vleck 2-jet D²u₀(0)=(1/6)Ric (VanVleckRadial const-curv-only).**

### J4-498 — GaussianMomentExtraction: the reusable COEFFICIENT-EXTRACTION tool + a convention card
- **File:** `QIQTH/GaussianMomentExtraction.lean` (namespace `QIQTH.HeatResidualBound`, std-3, 4 public decls + reusable integrability helpers). The coefficient-facing pivot after the q-audit: EXTRACT the leading source, don't bound it.
- **What lands:** `gaussDdim_first_moment_zero` (∫G_t·z_i=0, oddness) · `gaussDdim_second_moment` (∫G_t·z_i z_j = 2t·δ_ij, re-export of banked `gaussianMoment_diag`) · **`quadForm_gauss_second_moment`** (∫G_t·Σ_jk H_jk z_j z_k = 2t·Σ_j H_jj = 2t·tr H) · **`poly2_gauss_extraction`** (∫G_t·(c + Σ b_j z_j + Σ H_jk z_j z_k) = c + 2t·tr H — i.e. **∫G_t·B = B(0) + t·tr(D²B(0)) EXACTLY** for deg-≤2 B ⟹ (∫G_t·B − B(0))/t = tr D²B(0) = ΔB(0), the Laplacian source). Plus public integrability helpers `hk_lin_integrable`/`coord_gaussDdim_integrable`/`coordPair_gaussDdim_integrable`.
- **The gate:** moments CENTERED at 0 (no centering trap); `poly2_gauss_extraction` is an EXACT identity for deg-≤2 B with NO remainder hypothesis (no vacuous Taylor hyp; H/b/c arbitrary, non-vacuous); asserts NO limit (holds ∀t>0, no vacuous filter). No false hypothesis.
- **New vs banked:** banked = M0 (`gaussDdim_mass_one`), M2 (`gaussianMoment_diag`), the 1-D moments, the BOUNDING `gaussian_hessian_cancel` (which discards the coefficient). NEW = the n-D first moment, the 2 integrability helpers, and the 2 EXTRACTION identities that turn the banked `2t·δ` into the actual leading coefficient. Did NOT need Sol; did NOT build the per-coord ∫∂ᵢ²G·B (4th-moment/by-parts) route — the a₁ coefficient needs the TRACE (sum over i), which M2 gives directly, so the 4th moment is unnecessary.
- **What it delivers:** EXTRACTION (an exact coefficient) not a bound — Sol #22 step-4's exact-polynomial core (H₀-quadratic ⇒ tr(D²H₀); constant survives; linear killed). ⚠ DEFERRED: the τH₁ term + the general-smooth-B version `(∫G_τ·B−B(0))/τ → tr(D²B(0))` needs a delta-family limit on a uniform 2nd-order Taylor remainder r=o(τ) — that IS the E(τ) assembly (J4-499).
- **Transport granularity:** no census Π; banked lemmas applied once + destructured; the lemma is GENERIC (plain c/b/H, not census-tied). Build ~30-50s.
- **THE CONVENTION CARD (Sol #22 step 1) — what the code PINS:** (1) TIME: the single width `t` in gaussDdim/heatKernel1D = heat-kernel AGE = trace time; variance/coord = 2t; this flat moment brick is SINGLE-AGE (the campaign's (τ,s) outer-trace vs inner-Duhamel split lives in the residual/Duhamel files, NOT here). (2) LAPLACIAN SIGN: heatKernel1D solves ∂_t G = ∂²_x G (`heatKernel1D_heat_eqn`) ⟹ geometer's Δ=−∂²_x≥0, this is e^{−tΔ} smoothing. (3) EXPONENT: exp(−x²/4t) ⟹ e^{−‖z‖²/4t} ✓. (4) NORMALIZATION: (√(4πt))⁻¹/coord ⟹ (4πt)^{−n/2}, inside gaussDdim (mass-one includes it). (5) MEASURE: dz = Lebesgue; NO √g/van-Vleck here (flat product Gaussian; vanVleck^{−1/2} + dvol_g sit in the curved parametrix files). ⚠ GENUINE AMBIGUITY the code does NOT pin: (a) the τ-vs-s role split (this brick is single-age, cannot resolve it — the E(τ) assembly must fix which age the moment integrates against); (b) the Duhamel defect sign (∂_t∓Δ)H + convolution order (cross-file); (c) the Ricci/scalar sign giving u₁=R/6 (carried/cited, absent here).
- **⚠ a₁=R/6 remains CONDITIONAL** — the reusable coefficient TOOL, not the value; the 1/6 is cited curved geometry. NEXT J4-499 = the E(τ) ASSEMBLY (connect the fixed-(τ,s) residual to the traced Duhamel correction, using `poly2_gauss_extraction` as the direct tr(D²B(0)) input; the assembly must furnish the uniform 2nd-order Taylor remainder r=o(τ) + the delta-limit) — the real gap the q-audit exposed.

### J4-499 — DuhamelSimplexAssembly: the τ/s TIME-ROLE RESOLVED + the ds-assembly last link
- **File:** `QIQTH/DuhamelSimplexAssembly.lean` (namespace `QIQTH.DuhamelAssembly`, std-3, 3 public decls). PART 1 (the resolution) is the primary deliverable; PART 2 (the ds-assembly brick) is the honest last link.
- **★ THE τ/s RESOLUTION (from the code, not inferred):** `heatConv A B t x y := ∫₀^t ds ∫_z A(t−s)x z·B s z y dz ds` (HeatDuhamel.lean:55) ⟹ **t = outer age · s = inner Duhamel source-time ∈[0,t] · the parametrix factor A at the REMAINING age a=t−s · the source B at s.** True kernel `= H + heatConv H F`, `F = leviSeries E`; traced diagonal correction `E_tr(τ) = ∫₀^τ ds ∫_z H(τ−s,x,z)·F(s,z,x)`. The concrete residual `f`'s Gaussian age is the single free `τ` (`gaussDdim τ`), `s` enters ONLY via the source slice `F s z 0` — no `τ−s` inside; a fixed-age Hessian pairing against a source slice. So for `f` to be the Duhamel integrand its age MUST be instantiated at `a=τ−s`, and the proven fixed-age `C/a` bound (dominant `M₀·(n+1)/(2a)`, `Mqc·(n+1)/(2a)`) gives `|E_tr(τ)| ≤ ∫₀^τ C/(τ−s)ds = C·∫₀^τ dσ/σ = +∞` **LOG-DIVERGENT**.
- **⚠ THIS CONFIRMS + SHARPENS the q-audit:** q=1 is the borderline-nonintegrable case; the sup-norm `1/a` bound is genuinely NONintegrable along the Duhamel path (it cannot prove `E_tr=O(τ²)`). It does NOT prove the true correction diverges (a₁ IS finite) — it proves the ABSOLUTE bound is lossy. A sharper slice estimate is genuinely REQUIRED. The correction-order fact `heatConv H F(τ,0,0)=pref·(τ²·cRem)` is currently a CARRIED hypothesis `hCorrHigher` in `TrueKernelA1.trueKernel_diagonal_a1_eq_R6:141` — assumed, not proven. Discharging it IS the open gap.
- **Sol (gpt-5.6-sol high) — critical refinement:** exact Gaussian moment extraction only upgrades **O(1/a)→O(1), NOT O(a)**. The signed Hessian-Gaussian kernel has vanishing 0th/1st moments (`∫∂²_z G_a·P = ∂²_z P(0)`, O(1)) ⟹ the spurious `1/a` cancels, but the surviving **O(1) piece is a TRANSPORT COEFFICIENT** giving an O(τ) correction that CAN shift a₁. To reach O(τ²) the O(1) transport coeff must **CANCEL** (be absorbed into H's transport equation — exactly the van-Vleck 2-jet `D²u₀(0)=(1/6)Ric` content). Minimal correct assembly: post-cancellation `‖R(a,s)‖ ≤ K·(a+s)`; since `a+s=τ` is CONSTANT on the Duhamel simplex, `∫₀^τ ds` yields `‖E_tr(τ)‖ ≤ K·τ²`.
- **PART 2 — the ds-assembly brick (BUILT):** `duhamel_simplex_quadratic_bound` (`(∀s∈Ι 0 τ, ‖r(τ−s) s‖ ≤ K·((τ−s)+s)) → ‖∫₀^τ r(τ−s) s ds‖ ≤ K·τ²`, via `(τ−s)+s=τ` + `intervalIntegral.norm_integral_le_of_norm_le_const`) · `duhamel_simplex_quadratic_bound_pref` (the `pref·(τ²·cRem)` shape matching `hCorrHigher`) · `duhamel_simplex_quadratic_bound_sharp` (satisfiability witness `∫₀^τ((τ−s)+s)ds=τ²`, bound TIGHT with equality). The honest LAST link — CONSUMES the still-open `O(a+s)` slice hyp; does NOT provide it, does NOT dress up the log-divergence (the docstring states the current C/a bound → +∞ explicitly).
- **The gate:** non-vacuous + satisfiable (`_sharp` inhabits the `O(a+s)` hyp with `r a s:=a+s`, `K:=1`, and the bound is SHARP); fixed-τ integral inequality (no vacuous filter); log-divergence NOT dressed up.
- **THE 3 CARRIED HYPS behind a₁=R/6 (in `trueKernel_diagonal_a1_eq_R6`):** `hCorrHigher` (correction O(τ²)), `hEboundW` (C4c off-diagonal residue), `htr` (the DeWitt transport-source normalization = the `−(2/3)Ric` metric-Hessian trace, i.e. `ud_1=R/6`).
- **Build:** std-3 all three; `lake build QIQTH.AxiomAudit` green (no collision — the agent collision-checked). NOT a₁=R/6.
- **⚠ CRITICAL PATH (Sol): NOT another assembly brick (the ds-link is done). It is (1) moment-extraction upgrade of the SLICE bound O(1/a)→O(1) (tractable, uses `poly2_gauss_extraction`, removes the log-divergence), then (2) the TRANSPORT-CANCELLATION = the general van-Vleck 2-jet `D²u₀(0)=(1/6)Ric` (the IRREDUCIBLE a₁=R/6 wall; VanVleckRadial const-curv-only; moment extraction alone provably does NOT close it, O(1)↛O(a)).**

### J4-500 — SliceBoundO1: the SIGNED SLICE bound O(1/a)→O(1) — THE LOG-DIVERGENCE REMOVED (Sol step 1)
- **File:** `QIQTH/SliceBoundO1.lean` (namespace `QIQTH.SliceBoundO1`, std-3, 6 public decls — fresh namespace, collision-checked).
- **CAPSTONE `hessGauss_signed_slice_O1`:** `|∫_z hessGaussFactor_i·(c + Σ b_j z_j + Σ H_jk z_j z_k)| ≤ (32√2+1)·Σ_jk|H_jk|` — the SIGNED slice against a deg-≤2 amplitude is **O(1) uniform as a→0⁺** (NO 1/a, NO 1/√a).
- **Mechanism:** the const part (whose ABSOLUTE bound is ∼c/a = O(1/a)) and the linear part (∼O(1/√a)) VANISH EXACTLY — 0th moment = banked `hessGaussFactor_integral_zero`; 1st moment = `hessGaussFactor_first_moment_zero` (proved here for THIS kernel via product factorization + the odd 1-D integral `oneD_hessW_lin_zero`). The surviving quadratic is bounded by the O(1) mixed second moment `hessAbs_coordSq_le` (`∫|hessGaussFactor|·z_m² ≤ 32√2+1` — the 1/a of the Hessian weight cancels the a of the 2nd moment). Supporting: `oneD_hessW_sq_moment_le` (the 1-D O(1) mixed moment), `hessGaussFactor_coordPair_abs_le`.
- **The gate:** REACHABLE for THIS kernel (0th moment banked; 1st moment proved directly, not a lookalike); SIGNED not absolute (`∫|hessGaussFactor|` genuinely IS O(1/a) — only used inside the `m≠i` factorized product where the `2τ` 2nd moment compensates); Taylor-jet `c/b/H` free (non-vacuous); centered at 0. No false hypothesis. Sol (gpt-5.6-sol high) blessed the route + supplied `|z_j z_k| ≤ (z_j²+z_k²)/2` (drops a factor n).
- **What it delivers:** the LOG-DIVERGENCE is REMOVED (O(1/a)→O(1)). Fed into the Duhamel `∫₀^τ ds` at age a=τ−s: `∫₀^τ O(1) ds = O(τ)` — a MARGINAL q=1 correction, NOT O(τ²). ⚠ HONEST DISTANCE: this is O(1/a)→O(1), NOT O(1/a)→O(a). The surviving O(1) = the amplitude Hessian = the TRANSPORT COEFFICIENT; its cancellation to O(τ²) is the SEPARATE IRREDUCIBLE van-Vleck 2-jet wall D²u₀(0)=(1/6)Ric (VanVleckRadial const-curv-only), the LABELLED next wall — NOT closed here.
- **New vs banked:** reused `hessGaussFactor_integral_zero`, `hk_even_moment_le`, `gaussianSecondMoment_oneD`, `hk_absHess_moment_le`, `hk_mul_sq_pow_integrable`, etc. NEW = the signed 1st-moment vanish, the 1-D + n-D O(1) mixed second moments, and the O(1) signed-slice capstone. No exact 4th moment needed (bounded the quadratic via the mixed 2nd moment).
- **Transport granularity:** no census Π; banked lemmas once + destructured; hessGaussFactor via its definitional product form; amplitude data opaque (generic c/b/H); integrabilities routed through one master n-D lemma. Build ~1min incremental (every iteration <2min).
- **⚠ a₁=R/6 remains CONDITIONAL** — removes the log-divergence but does NOT select the coefficient. CRITICAL PATH now = the IRREDUCIBLE van-Vleck 2-jet wall (the O(1)→O(a) transport-cancellation). NEXT J4-501 = the general arbitrary-metric van-Vleck 2-jet D²u₀(0)=(1/6)Ric campaign: audit exactly what VanVleckRadial proves (const-curv exact radial ODE only — NOT sufficient), survey Mathlib for Jacobi-field/geodesic-deviation/exp-map-Jacobian 2nd-variation infrastructure (likely absent), scope the generalization. Moment extraction provably cannot close it (O(1)↛O(a)).

### J4-501 — VanVleckTwoJet: the van-Vleck amplitude 2-jet D²u₀(0)=+(1/6)Ric (the power-flip layer) + ⚠ AUDIT CORRECTION
- **File:** `QIQTH/VanVleckTwoJet.lean` (std-3, 3 public decls, collision-checked). Reduces the amplitude-Hessian wall to the SINGLE carried metric 2-jet.
- **⚠ AUDIT CORRECTION (don't-undercredit):** `VanVleckRadial.lean` is NOT constant-curvature-only — that git-log title ("Constant-curvature: exact radial ODE") describes a DIFFERENT prior commit. It actually proves the GENERAL arbitrary-metric leading 2-jet of √det g: `sqrtdet_directional_hessian_ricci: ∑vᶜvᵈ∂_c∂_d √det g(0) = −(1/3)Ric(v,v)` under carried `hg`(smooth)/`hg0`(g(0)=δ)/`hdg0`(∂g(0)=0)/`htr`(∑∂∂g_{aa}(0)=−⅔Ric). The repo has a DEEP componentwise geometric infra: `QIQTH.Curvature` (1412 lines: pd/Christoffel/Riemann/Ricci/scalarCurv/Einstein/Bianchi as multivariable calculus) + `QIQTH.RNCExpansion` (the full √det g 2-jet tower: `sqrt_pd_pd`, `sqrtdet_pd_pd=−(1/3)Ric`, `rnc_riemann_hessian` [RNC2 local-inertial], `rnc_htr_of_gauge` [RNC3: derives htr from the normal gauge], + a ContDiffAt `_c2` mirror family). Mathlib: genuinely ABSENT (no Jacobi/exp-Jacobian/RNC/√det-g/abstract-curvature — that's why the repo builds curvature componentwise in a chart).
- **What lands:** `pd_comp_invSqrt` (1st-order chain rule for x↦(√x)⁻¹) · **`invSqrt_pd_pd`** (THE POWER FLIP: `∂_c∂_d(J^{−1/2})(x)=−(1/2)·∂_c∂_d J(x)` for smooth J, J(x)=1, ∂J(x)=0; f'(1)=−1/2, one negative via HasDerivAt.inv) · **`invSqrt_directional_hessian_ricci`** (`∑vᶜvᵈ ∂_c∂_d u₀(0)=+(1/6)Ric(v,v)`) · **`invSqrt_trace_hessian_scal`** (`∑_i ∂_i² u₀(0)=(1/6)Scal`).
- **THE SIGN GATE (explicit, passed):** √det g alone `D²(√det g)(0)=−(1/3)Ric` (banked); power `f(x)=x^{−1/2}`, `f'(1)=−1/2` (the invSqrt_pd_pd factor, one negative); flip `−(1/2)·(−(1/3)Ric)=+(1/6)Ric` (the `ring` close). Did NOT bank −(1/3) (√det g alone) nor +(1/12) (the Taylor coeff = ½·Hessian) — delivers the Hessian CONTRACTION +(1/6). Non-vacuous: `J(z)=1−(1/6)Ric(z,z)` is a globally-smooth inhabitant.
- **Sol (gpt-5.6-sol high):** confirmed the `(√J)⁻¹` representation + the fused first-order rule; rejected Real.rpow (worse API) + rejected composing two localized lemmas (√J not globally ContDiff); smallest sub-brick = `pd_comp_invSqrt`.
- **THE REDUCTION (exactly what⟵what):** van-Vleck amplitude 2-jet `D²u₀(0)=+(1/6)Ric` ⟵ (this file's algebra, on generic smooth positive J with the single carried `hJhess: ∀ c d, pd(pd J d)c 0 = −(1/3)·Ric c d`) ⟵ √det g 2-jet `−(1/3)Ric` (banked `sqrtdet_directional_hessian_ricci`/`sqrtdet_pd_pd` under htr) ⟵ metric 2-jet `htr` (the irreducible geometric theorem, Mathlib-absent, STILL CARRIED; discharged only from the falsifiable normal-gauge condition `rnc_htr_of_gauge`).
- **Transport granularity:** fully GENERIC/algebraic (abstract scalar J + bilinear Ric, no census Π, no g/gi binder tower). 4 lemmas, ~155 lines, 45s compile. Reused `sqrt_pd_pd`'s template + `pd_mul`/`pd_congr`/`PdiffAt_pd`.
- **⚠ a₁=R/6 remains CONDITIONAL** — the amplitude/algebra side of the wall is now reduced-to-one-carried-geometric-input; the metric normal-coord 2-jet (`htr`/`ud_1=R/6`) remains the genuinely open Mathlib-absent geometric input (discharged only from the falsifiable normal-gauge condition). NEXT J4-502 candidates (agent's leverage order): (1) WIRE the reduced amplitude 2-jet → discharge htr/ud_1=R/6 in `trueKernel_diagonal_a1_eq_R6` (bookkeeping, both sides now proven, highest-value+tractable); (2) the TRANSPORT-CANCELLATION linking J4-500's O(1) source to this +(1/6)Ric 2-jet (the true analytic critical path); (3) the metric 2-jet itself stays carried (do NOT attempt from Mathlib — absent).

### J4-502 — A1GaugeDischarge: htr DISCHARGED from the RNC normal-coordinate gauge in the a₁ capstone
- **File:** `QIQTH/A1GaugeDischarge.lean` (std-3, 1 public decl, collision-checked). Reduces the a₁ capstone's carried metric-2-jet input.
- **What lands:** `trueKernel_diagonal_a1_eq_R6_gauged` = `TrueKernelA1.trueKernel_diagonal_a1_eq_R6` with the raw metric-Hessian trace `htr` (`∀ c d, ∑_a ∂_c∂_d g_{aa}(0) = −(2/3)·Ric c d`) + the abstract `Ric` parameter REMOVED, replaced by the falsifiable normal-coordinate gauge `hgauge : ∀ i a b c, ∂_aΓ^i_{bc}(0)+∂_bΓ^i_{ca}(0)+∂_cΓ^i_{ab}(0)=0` (+ the `gi` smoothness/symmetry `rnc_htr_of_gauge` consumes), via `htr := fun c d => rnc_htr_of_gauge …` with `Ric := ricci g gi · · 0`. Conclusion UNCHANGED in force: `(∂_t−Δ)K(t,0,0)=0 ∧ K(t,0,0) = (4πt)^{−d/2}·(1 + ((∑_i ricci g gi i i 0)/6)·t + t²·rem)` — the honest scalar curvature R=∑_i Ric_{ii} over 6.
- **The audit — CLEAN SPLICE + REAL (qualitative) reduction:** `htr` is a plain ordinary hypothesis in the capstone; `rnc_htr_of_gauge` concludes exactly that shape. The corollary applies the capstone ONCE as a BLACK BOX (single term application, no re-elaboration of the ~30-binder internals). Category **(b) MORE-PRIMITIVE than htr → real reduction**: the bare ad-hoc trace identity is replaced by the recognized, falsifiable RNC gauge condition. RNCExpansion certifies `hgauge` is load-bearing (drop it and −(2/3)Ric becomes FALSE) ⟹ NOT cosmetic relabeling. NOT a full discharge either — `hgauge` remains a carried geometric input (Mathlib has no RNC/exp-chart construction to derive it).
- **The gate:** `hgauge` inhabited + non-vacuous (flat Γ≡0 with Ric=0; any curved RNC metric with Ric≠0 — jointly satisfiable by curved metrics); the restated capstone still concludes the real a₁=R/6 (scalar curvature, not a vacuous constant). No trivial/contradiction discharge.
- **What it delivers:** the a₁ capstone's carried metric 2-jet input `htr` → the more-primitive normal-coordinate gauge `hgauge`. A genuine QUALITATIVE reduction of the conditional (raw trace identity → recognized falsifiable geometric gauge), NOT a numerical count drop, NOT elimination.
- **Transport granularity + defeq:** thin black-box corollary, capstone applied once; module build 26s (no census-Π re-application, no defeq blow-up).
- **Don't-undercredit:** the RNC gauge machinery (`rnc_htr_of_gauge`, `pd_christoffel_solve`, `sum_riemann_ii_zero`, RNC1–RNC4) was already banked; this brick wires it into the capstone. `sqrtdet_taylor_coeff_of_gauge` + `heat_a1_of_gauge` already do the analogous gauge-discharge on the amplitude/a₁-assembly side.
- **⚠ THE a₁ CAPSTONE'S CURRENT CARRIED-HYP SET (agent-disclosed, honest):** `hEboundW` (C4c global width-2 off-diagonal parametrix residual — the far-field/off-diagonal residue; its local near-diagonal part IS proved, `residualN0_local_baseKernelW_slice`), `hCorrHigher` (the O(t²) Levi-correction-higher-order-on-diagonal = the transport-cancellation linking J4-500's O(1) source to the +(1/6)Ric 2-jet — the TRUE ANALYTIC CRITICAL PATH), the metric-2-jet/normal-gauge (now `hgauge`), + the analytic carries `hInt` (per-step integrability), `hE`/`hDuhamel`/`hInter` (parametrix-residual/Duhamel/tsum-interchange), `hHdiag`, + heatOp-linearity regularity side conditions.
- **⚠ a₁=R/6 remains CONDITIONAL** — real qualitative reduction of the geometric input, but the normal-gauge condition stays carried (Mathlib-absent). NEXT J4-503 (agent's rec) = `hCorrHigher` (the true critical path, the transport-cancellation O(1)→O(t²)); `hEboundW`'s far-field residue is the harder standalone parallel wall; `hgauge` stays carried (option (b) of the heat-kernel gap plan).

### J4-503 — CorrHigherReduction: hCorrHigher HONESTLY reduced to the per-slice O(a+s) transport estimate (+ a ⚠ COSMETIC-DISCHARGE catch)
- **File:** `QIQTH/CorrHigherReduction.lean` (std-3, 3 public decls, collision-checked).
- **⚠ THE CATCH (audit):** the a₁ capstone's `hCorrHigher` (`heatConv H (leviSeries E) t 0 0 = (heatKernel1D t 0)^n·(t²·cRem)` at a SINGLE fixed t) is TRIVIALLY satisfiable (`cRem := X/(pref·t²)`) — the existing `TrueKernelA1Reduced.corrHigher_witness` discharges it COSMETICALLY, and `_reduced`/`_residual` inherit that cosmetic witness. The genuine O(t²) content (`cRem` BOUNDED as t→0⁺, so the fold does not shift a₁) is a `∀τ` bound `‖heatConv‖≤K·τ²`, NOT the single-t equality.
- **What lands:** `corrHigher_bounded_of_slice` (from the per-slice bound `∀ s∈Ι 0 t, ‖∫_z H(t−s)0z·F s z 0‖ ≤ K·((t−s)+s)` + `t>0`, `pref≠0` delivers the `hCorrHigher` shape WITH the genuine bound `|cRem| ≤ K/|pref|` — the O(t²) boundedness the cosmetic discharge lacks; via the banked `duhamel_simplex_quadratic_bound` + the DEFINITIONAL `heatConv=∫₀^t ds∫_z`) · `slice_bound_inhabited` + `corrHigher_bounded_flat` (satisfiability witnesses, flat F≡0, cRem=0).
- **What hCorrHigher is now reduced to:** exactly the per-slice O(a+s) transport estimate `‖∫_z H(t−s)0z·F s z 0‖ ≤ K·((t−s)+s)` — the isolated carried input.
- **Sol (gpt-5.6-sol high):** the per-slice O(a+s) is SATISFIABLE + SOUND (honest order O(s) — residual lives in the age-s source; O(s)⟹O(a+s); NO intrinsic O(τ²log τ) loss). ⚠ THE EXACT MISSING ESTIMATE: with H₁=G·(u₀+t·u₁) and the first two transport eqns (𝒯u₀=0, (𝒯+1)u₁=Δu₀), the residual factorizes `(∂_t−Δ)H₁ = −t·G·Δu₁ ⟹ E₁ = t·G_t·q, q bounded` — **the extra factor t IS the whole cancellation** (annihilates the surviving O(1) amplitude-Hessian). Then a Levi-series order-preservation lemma (`(t^p G)*(t^q G)=O(t^{p+q+1}G)`) keeps the source O(s·G_s), and the spatial Gaussian convolution `∫_z H(a)·Φ(s) ≤ C·s·G_{a+s}` gives O(s) per slice. ⚠ Sol: diagonal vanishing of the leading amplitude ALONE is insufficient (off-diagonal linear terms leave O(√t)); the FULL off-diagonal factorization E₁=t·G_t·q is required.
- **The gate:** the cosmetic single-t satisfiability was CAUGHT + avoided (my reduction carries the per-slice bound + delivers |cRem|); the carried per-slice hyp is SATISFIABLE not unsatisfiable (proved flat-case + Sol-confirmed genuinely-true, not proof-by-contradiction); non-cosmetic (adds the real |cRem| ≤ K/|pref|).
- **⚠⚠ KEY STRUCTURAL FINDING:** BOTH remaining analytic walls — the genuine O(t²) content of `hCorrHigher` AND `hEboundW` — reduce to the SAME missing object: the Gaussian-weighted residual factorization `E = O(a·G_a)` (good parametrix with N≥1 transport terms) + Levi order-preservation.
- **Transport granularity:** thin assembly over banked `duhamel_simplex_quadratic_bound` + definitional heatConv; no census Π. Build 27s.
- **⚠ a₁=R/6 remains CONDITIONAL** — isolates the gap to the per-slice transport estimate; does NOT close it. NEXT J4-504 = the residual factorization `E₁ = t·G_t·q` (bounded q) from the first transport eqns — concretely `(∂_t−Δ)(G·(u₀+t·u₁)) = −t·G·Δu₁` — + the Levi-series Gaussian order-preservation lemma. This is the genuinely-new estimate; the ds-assembly + bounded-cRem reduction downstream are now banked. Closing it discharges BOTH hCorrHigher (honestly) AND hEboundW.
- **a₁ capstone's current carried set:** RNC/metric data {hg,hg0,hgi,hΓ,hdg0,htr(→hgauge)}, hsrc, hHdiag, **hEboundW** (★ C4c off-diag width-2 residual), hInt, hE, hDuhamel, hInter, hCorrHigher(→per-slice O(a+s), honestly reduced here), heatOp-regularity {hDH,hDConv,hCH,hCConv}.

### J4-504 — ResidualFactorization: the residual factorization E₁=t·G·q — a THEOREM MODULO the two carried transport equations
- **File:** `QIQTH/ResidualFactorization.lean` (std-3, 4 public decls, collision-checked). THE SINGLE MISSING OBJECT that (once hT0/hT1 close) discharges BOTH remaining analytic walls (hCorrHigher's genuine O(t²) AND hEboundW).
- **What lands:** `heatOpFun_mul` (the reusable Leibniz engine `(∂_t−Δ_g)(G·P) = [(∂_t−Δ_g)G]·P + G·[(∂_t−Δ_g)P] − 2Σgⁱʲ∂ᵢG∂ⱼP` — pure calculus) · `crossGrad_lin` (cross-gradient linearity `C(u₀+t·u₁)=C(u₀)+t·C(u₁)`) · **`residual_factorization`** (★ `(∂_t−Δ_g)(gaussDdim·(u₀+t·u₁)) = −t·gaussDdim·Δ_g u₁ = t·G·q`, `q=−Δ_g u₁`, MODULO the two carried POINTWISE equations `hT0` (`𝒢·u₀−2C(u₀)=0` = 𝒯u₀=0) and `hT1` (`t·(𝒢·u₁−2C(u₁))+G·(u₁−Δu₀)=0` = (𝒯+1)u₁=Δu₀)) · **`residual_factorization_flat_witness`** (the flat model g=δ,u₀=1,u₁=0 discharges hT0/hT1 ⟹ E=0 — the SATISFIABILITY witness, hyps jointly INHABITED).
- **Audit (what's banked vs missing):** the `𝒯` transport operator IS defined (`HeatTransportRecursion.transportOp Θ g gi v = Θ^{−1/2}·Δ_g(Θ^{1/2}·v)`, `transportOp_theta_one` → plain Δ_g at the RNC center); the transport eqns are carried DIAGONALLY (`TransportRecursion.udiag_rec: (k+1)·u_{k+1}(x₀)=transportOp(u_k)(x₀)`) — the OFF-diagonal radial ODE `(k+r∂_r)u_k+½(r∂_r logΘ)u_k=𝒯u_{k−1}` is checkpointed STRETCH-#4 (the geodesic-r∂_r wall, Mathlib-absent). The Leibniz identity was banked (`laplaceBeltrami_mul_inf`), + flat-heat `gaussDdim_heat_eqn` + RNC reduction `laplaceBeltrami_at_rnc_center`. `u₀` IS the van-Vleck amplitude (`invSqrt_trace_hessian_scal`). Two prior factorizations banked but insufficient: `residual_eq_gauss_mul_A` (off-diag E=G·A but A carries 1/t,1/t² — no extra t) + `parametrixResidual_telescope_N` (extra tᴺ but ONLY diagonal v=0). What was missing = the OFF-diagonal `E₁=t·G·q` identity + the Leibniz engine — THIS brick.
- **Sol (gpt-5.6-sol high):** confirmed the decomposition + the genuine t, corrected the split allocation to the standard grouping `E = [𝒢·u₀−2C(u₀)] + [t·(𝒢·u₁−2C(u₁))+G·(u₁−Δu₀)] − t·G·Δu₁` so hT0/hT1 map exactly onto the standard transport eqns against the flat Gaussian. Pure algebra = deriv_mul/laplaceBeltrami_mul_inf/∂_tP=u₁/Δ_gP=Δu₀+tΔu₁/term-collection; genuine carried inputs = the two bracket vanishings.
- **The gate:** PASSED. No vacuous hyp (flat witness = genuine full inhabitant proving hT0∧hT1 satisfiable). The extra t is GENUINE (explicit in −t·G·Δu₁, from Δ_g(t·u₁)=t·Δ_g u₁ at order t¹, Sol-confirmed not cosmetically absorbed). ∀t>0,x,u₀,u₁ identity (not single-point). ⚠ Honest caveat: the flat witness satisfies hT1 trivially (u₁=0); the genuine non-triviality of hT0/hT1 at nonzero curvature IS the carried analytic content — reported, not faked.
- **Transport granularity:** the 2 eqns carried as 2 SEPARATE pointwise hyps (matching 𝒯u₀=0 and (𝒯+1)u₁=Δu₀); thin generic engine + `linear_combination` cancellation. Build ~26s, no defeq blowup.
- **⚠ WHAT REMAINS CARRIED/MISSING:** exactly `hT0`/`hT1` for a CURVED metric — the off-diagonal radial-transport ODE (the checkpointed STRETCH-#4 geodesic-r∂_r wall). The factorization is now a theorem AGAINST them; they are NOT banked.
- **⚠ a₁=R/6 remains CONDITIONAL** on deriving hT0/hT1 off-diagonal. This brick isolates the analytic gap to those 2 transport eqns (a theorem-against-them); it does NOT close it. NEXT J4-505 (agent's rec) = derive `hT0` (𝒯u₀=0) as the first tractable slice — feed the flat-Gaussian gradient ∂ᵢG=−(xᵢ/2t)·G into C(u₀) to collapse the cross-gradient to a radial r∂_r u₀ term, turning 𝒯u₀=0 into the homogeneous radial equation the banked van-Vleck u₀=J^{−1/2} satisfies; then hT1 ((𝒯+1)u₁=Δu₀ source) + a Levi order-preservation lemma banking q uniformly bounded.

### J4-505 — TransportEqZero: the k=0 transport equation hT0 REDUCED to the scalar radial input hRad
- **File:** `QIQTH/TransportEqZero.lean` (std-3, 8 public decls, collision-checked).
- **What lands:** `metricRadial` (`R_g(u)=Σᵢⱼ gⁱʲ xᵢ ∂ⱼu`) · **`crossGrad_eq_metricRadial`** ★ (the banked reduction `C(u)=−(1/2t)·G·R_g(u)`, from ONLY the banked flat-Gaussian gradient `∂ᵢG=−(xᵢ/2t)·G` — pure calculus) · **`transportOffDiag_eq_radial`** ★ (`𝒢·u−2C(u)=𝒢·u+(1/t)·G·R_g(u)`) · **`hT0_of_radial`** ★★ (hT0 DISCHARGED from the scalar radial input `hRad: 𝒢·u₀=−(1/t)·G·R_g(u₀)`) · `residual_factorization_of_radial` (the banked factorization with hT0 replaced by hRad) · `metricRadial_eq_radialDeriv_of_gaussLemma` (isolates the Gauss-lemma input `Σᵢgⁱʲxᵢ=xʲ` ⟹ `R_g=radialDeriv`) · `metricRadial_flat_eq_radialDeriv`/`metricRadial_flat_rncRadialSq`/`radialInput_flat_witness`.
- **VERDICT (b) reducible-to-radial-input:** `hT0` collapses EXACTLY to the scalar radial equation `hRad`; closing `hRad` is squarely the STRETCH-#4 wall (Gauss lemma + volume identity), NOT closed here.
- **Sol (gpt-5.6-sol high) CONFIRMED:** the cross-gradient reduction is banked calculus; the exact k=0 equation is NOT derivable from finite RNC jets — at x=0 both `C(u₀)` and `𝒢` vanish so the equation is VACUOUS at the center; it is genuinely uniform-in-v along all radial geodesics. A finite 2-jet CANNOT replace it. Eikonal split: `𝒢u₀−2C(u₀) = (G/4t²)(‖x‖²−Q)u₀ + (G/2t)[(tr g⁻¹−n−A)u₀ + 2R_g(u₀)]`, closed by `Σᵢgⁱʲxᵢ=xʲ` (⟹ Q=‖x‖², R_g=radialDeriv) + `Δ_g(½‖x‖²)=n+r∂_r log√det g`; then `u₀=μ^{−1/2}` makes the amplitude ODE pure chain rule. THE SMALLEST HONEST INPUT = the coordinate GAUSS LEMMA `Σᵢ gⁱʲ xᵢ = xʲ` in RNC (the `RadialDistance` header's explicitly-deferred item, STRETCH-#4, Mathlib-absent).
- **The gate:** PASSED. `radialInput_flat_witness` proves `hRad` for flat metric u₀=1 ∀x ∀t>0 (𝒢=0, R_δ(1)=0) — inhabited/non-vacuous. `metricRadial_flat_rncRadialSq` shows `R_δ(r²)(v)=2r²≠0` for v≠0 = the genuine OFF-center Euler content (NOT the already-banked x=0 diagonal). No cosmetic/single-point discharge; `hRad` is the true off-diagonal identity.
- **Don't-undercredit:** the repo banks extensive radial infra (`RadialTransport` solve operator, `VanVleckTransportRadial`, `ParametrixRadialTransportSplit`, the van-Vleck/Raychaudhuri Jacobi tower). This brick supplies only the missing flat-Gaussian→metric-radial BRIDGE that `ResidualFactorization`'s hT0 needed, and pins the residual to the checkpointed STRETCH-#4 Gauss lemma.
- **Build:** 37s, no census-Π. std-3 all 8.
- **⚠ a₁=R/6 remains CONDITIONAL** — hT0 REDUCED to `hRad` (not discharged outright). WHAT REMAINS CARRIED: `hRad` (closure = the Gauss lemma `Σᵢgⁱʲxᵢ=xʲ` + volume identity `Δ_g(½‖x‖²)=n+r∂_r log√det g`, the one genuinely-geodesic STRETCH-#4 wall) + `hT1` (k=1, untouched). NEXT J4-506 (agent's rec) = `hT1` via the IDENTICAL cross-gradient reduction (fast mechanical mirror — `crossGrad_eq_metricRadial` applies to C(u₁) too, leaving its own radial input), reserving the Gauss-lemma sub-campaign (hRad closure) as the one genuinely-geodesic wall.

### J4-506 — TransportEqOne: the k=1 transport equation hT1 REDUCED to the scalar radial input hRad1 (the mechanical mirror)
- **File:** `QIQTH/TransportEqOne.lean` (std-3, 3 public decls, collision-checked). The fast mechanical mirror of J4-505.
- **What lands:** **`hT1_of_radial1`** (hT1 `t·(𝒢·u₁−2C(u₁))+G·(u₁−Δu₀)=0` discharged from `hRad1 : t·(𝒢·u₁+(1/t)·G·R_g(u₁))+G·(u₁−Δu₀)=0` via `rw [transportOffDiag_eq_radial]` — one line, the generic-in-u banked lemma does the work) · **`residual_factorization_of_radial01`** (the residual factorization = −t·G·Δu₁ MODULO BOTH `{hRad0, hRad1}`; composes `TransportEqZero.hT0_of_radial` + `hT1_of_radial1` into `ResidualFactorization.residual_factorization`) · `radialInput1_flat_witness` (hRad1 inhabited: flat metric u₀=1,u₁=0, ∀x ∀t>0).
- **The rewrite:** `crossGrad_eq_metricRadial` is generic in u ⟹ `C(u₁)=−(1/2t)·G·R_g(u₁)` verbatim; the inner bracket `𝒢·u₁−2C(u₁)` → `𝒢·u₁+(1/t)·G·R_g(u₁)`; the k=1 SOURCE `G·(u₁−Δu₀)` rides along UNTOUCHED (needs NO extra banked identity — it's already an explicit field, no Δu₀ calculus). `hRad1` is the SAME STRETCH-#4 Gauss-lemma family as `hRad0` (under `Σᵢgⁱʲxᵢ=xʲ`, `metricRadial_eq_radialDeriv_of_gaussLemma` generic-in-u turns `R_g(u₁)` into `radialDeriv u₁`). No Sol consult needed (pure mechanical mirror).
- **The gate:** `hRad1` inhabited + non-vacuous (`radialInput1_flat_witness`: flat u₀=1,u₁=0, 𝒢=0 via `laplaceBeltrami_at_rnc_center`+`gaussDdim_heat_eqn`, R_δ(0)=0, source G·(0−Δ_δ1)=0, ∀x ∀t>0); genuine ∀x off-diagonal (carries the full `metricRadial gi u₁ x` double sum), NOT single-point x=0.
- **What it delivers:** hT1 reduced to hRad1 (+ its untouched source). ⚠ Combined with J4-505: **the residual factorization is now a THEOREM MODULO exactly `{hRad0, hRad1}`, BOTH members of the same coordinate-Gauss-lemma family `Σᵢgⁱʲxᵢ=xʲ`.** Closing that single per-coordinate identity collapses both radial equations to eikonal/volume identities.
- **Transport granularity:** per-coefficient (hT0/hT1) level; no census Π; data generic/opaque. Build 28s.
- **Don't-undercredit:** the banked machinery (`transportOffDiag_eq_radial`, `hT0_of_radial`, `metricRadial_eq_radialDeriv_of_gaussLemma`, the flat witnesses) was designed generic in u; J4-506 exploits that, does not re-derive it.
- **⚠ a₁=R/6 remains CONDITIONAL** — isolates the gap further (hT1→hRad1, same family as hRad0); does NOT close it. WHAT STAYS CARRIED: `{hRad0, hRad1}` ⇐ the coordinate GAUSS LEMMA `Σᵢgⁱʲxᵢ=xʲ` + the volume identity `Δ_g(½‖x‖²)=n+r∂_r log√det g`. NEXT J4-507 = THE COORDINATE GAUSS LEMMA `Σᵢ gⁱʲ(x) xᵢ = xʲ` in RNC — the SHARED input closing BOTH hRad0+hRad1. ⚠ AUDIT whether it's derivable from the banked RNC gauge (hgauge/rnc_htr_of_gauge family in RNCExpansion/HeatTransportRecursion) — like htr was in J4-502 — OR the irreducible geodesic wall (STRETCH-#4). If derivable ⟹ HUGE leverage (discharges both radial inputs at once); if not ⟹ the honest single geometric residue that stays carried.

### J4-507 — GaussLemmaGauge: the coordinate GAUSS LEMMA is THE IRREDUCIBLE GEODESIC FLOOR — both radial inputs packaged onto ONE named geometric input
- **File:** `QIQTH/GaussLemmaGauge.lean` (std-3, 6 public decls, collision-checked). ⚠ THE CAMPAIGN IS AT THE GEOMETRIC FLOOR.
- **⚠ VERDICT (c) — irreducible geodesic/exp-map floor; (a) REFUTED:** the coordinate Gauss lemma `∑ᵢ gⁱʲ(x) xᵢ = xʲ` (EXACT, all-orders, ∀x) is NOT derivable from the finite RNC gauge `hgauge` (`∂_(aΓⁱ_bc)(0)=0`, a finite 2-jet at 0). Sol counterexample: `g_ij=(1+ε‖x‖⁴)δ_ij` shares the full 2-jet at 0 (satisfies hgauge, g(0)=δ, ∂g(0)=0) yet `∑_j g_ij x^j=(1+ε‖x‖⁴)x^i≠x^i` off-origin. A finite jet cannot imply an all-orders identity.
- **⚠⚠ DON'T-UNDERCREDIT (major):** the repo is NOT resting on the Gauss lemma as a bare hypothesis — it has a FULL in-Lean geodesic exponential-map machinery, built from scratch (Mathlib has NONE): `ExpMap.lean`/`Geodesic` (geodesicField, expTube, expMap, strict deriv at equilibrium), `GaussLemmaFirstVariation/Transverse/Homogeneity/Assembly/FlowData.lean` (Jacobi fields, energy conservation `g_{exp v}(γ̇,γ̇)=g_p(v,v)`, transverse Jacobi conservation, Euler homogeneity `D exp_p(v)·v=γ̇(1)`, `gauss_coordinate_contraction`, the germ form `hGauss_pullback : ∀ i, (∑_j g̃ x i j·x^j) =ᶠ[𝓝 0] x^i`) — reduced down to a SINGLE labelled tube residue `hgball` (the per-point first-variation Gauss identity), one level DEEPER than a bare axiom. AND there is an a₁=R/6 MAINLINE `A1R6FromLabelled.a1_R6_from_labelled` carrying this SAME content as `hGauss`, feeding `htr` via `NCGaussToCyclicT.cyclicT_of_hGauss`.
- **What lands:** `def CoordGaussGauge gi := ∀ x j, ∑ i, gi x i j·x i = x j` (the single ∀x named floor, inverse-metric form) · `def MetricGaussGauge g := ∀ x i, ∑ j, g x i j·x j = x i` (dual) · `metricRadial_eq_radialDeriv_of_coordGaussGauge` (R_g(u)=r∂_r u ∀u from the one gauge) · **`residual_factorization_of_gauge`** ★★ (the residual E=−t·G·Δ_g u₁ from the ONE named gauge + the two Euler-field radial eqns — BOTH carried radial inputs now rest on ONE recognized hypothesis instead of two ad-hoc metricRadial identities) · `metricGaussGauge_imp_hGaussGerm` (the ∀x metric gauge ⟹ the a₁-mainline germ `hGauss` via `Filter.Eventually.of_forall` — establishing it is the SAME geometric content the mainline carries, differing only metric↔inverse dual + pointwise↔germ).
- **Sol (gpt-5.6-sol high):** confirmed the counterexample (Q1) + Q2 — the cleanest single recognized condition to carry IS the coordinate Gauss lemma itself (equivalently `exp*g|_v(v,·)=g_p(v,·)` the radial gauge, or `Γⁱ_jk(x)xʲxᵏ=0 ∀x`); transverse Jacobi conservation is a proof INGREDIENT not the best downstream hyp. This is the geometric floor given Mathlib's absent exp-map.
- **The gate:** `coordGaussGauge_flat`/`metricGaussGauge_flat` proved for ALL x (genuine ∀x, not vacuous x=0); `coordGaussGauge_flat_rncRadialSq` R_δ(r²)(v)=2r²≠0 v≠0 = genuine off-diagonal Euler content. Inhabited + non-vacuous.
- **Build:** ~27s. std-3 all 6. No census Π.
- **⚠⚠ HONEST ASSESSMENT — THE CAMPAIGN IS AT THE GEOMETRIC FLOOR.** a₁=R/6 now rests on: **(i) recognized geometric inputs Mathlib lacks the exp-map/geodesic infra to derive:** the coordinate Gauss lemma/radial gauge (this brick; partially derived in-repo via the exp-map stack down to `hgball`), the finite RNC gauge `hgauge` (discharges htr), the volume/Laplacian identity `Δ_g(½‖x‖²)=n+r∂_r log√det g` (banked radial ODE exists, wiring open); **(ii) still-reducible analytic carries (NOT floor):** `hCorrHigher`, `hEboundW`-family, the W2 differentiation-under-∫ family, `hraw`/`hPd2conv`/`hD2Hexpand` census piles, and the exp-tube residue `hgball` (reducible to the flow's interior 2nd-order algebra).
- **⚠ a₁=R/6 remains CONDITIONAL** — the honest deliverable is the cleanest single-carried-geometric-input packaging of the Gauss lemma, NOT a derivation. NEXT J4-508 (agent's rec) = (i) close the OTHER geometric leg — the volume/Laplacian identity `Δ_g(½‖x‖²)=n+r∂_r log√det g` via the banked van-Vleck radial ODE (VanVleckRadial), OR (ii) push the exp-tube residue `hgball` (the last genuinely-geodesic sub-lemma between the built exp-map machinery and the germ Gauss lemma).

### J4-508 — AUDIT of the a₁=R/6 MAINLINE a1_R6_from_labelled (audit-only, no brick — the honest current-state map)
- **`a1_R6_from_labelled` (A1R6FromLabelled.lean:90, ~280 binders) — EXACT conclusion:** a conjunction at the literal gate `constGate g gi hChr hK c`, diagonal at origin, for the concrete Duhamel-built true kernel of the GATED witness: (1) `heatOp g gi (trueHeatKernel …) t 0 0 = 0` (heat eqn on diagonal) AND (2) `trueHeatKernel … t 0 0 = (heatKernel1D t 0)^n·(1 + ((∑ᵢ ricci g gi i i 0)/6)·t + t²·(…))`. ⚠ THE t¹ COEFFICIENT IS GENUINELY R/6 = (∑ᵢ ricci)/6 (NOT divided back out — NOT cosmetic); the t² term is a self-referential remainder (a₂ left tautological — honest/standard, only t¹ asserted). R/6 comes from `transportCoeff_vanVleck_one_diag` (u₁(0)=R/6), GENUINELY DERIVED not assumed. std-3.
- **Complete carried-input set:** 4 labelled (`hGauss` = the coordinate Gauss-lemma germ ∀i (∑ⱼ g x i j·xʲ)=ᶠ[𝓝 0] xⁱ, feeds htr via htr_adapter · `hraw` = GlobalGatedRawBound width-1 residual · `hD2Hexpand` = the Leibniz–Gaussian 2nd-deriv expansion inside dataAmp · `hPd2conv` = the frozen→full 2nd-x-deriv interchange limit) + a large census (base geometry/gauge, window data, the constRadius package hpkgBound/hmemS0/hopenS0/hS1, geometry-raw gauge hframeK/hinvF, W2 diff-under-∫, residual floor, Da-limit piles, Duhamel-core ~40 binders, F2/hDConv, frozen/moving envelope, CConv sliver). All std-3, none `:= True`.
- **Relation to the capstone + my chain:** the mainline is a DOWNSTREAM CONSUMER of the capstone family — `a1_R6_from_labelled` → `wide_a1_R6_core_AT_CONSTRADIUS` → `wide_a1_R6_of_residue_inf_trunc` → `wide_trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty` (a wide/residual/C2/∞ variant of `TrueKernelA1.trueKernel_diagonal_a1_eq_R6`). My J4-489→507 chain is a PARALLEL track on the abstract-H `trueKernel_diagonal_a1_eq_R6` (+ _gauged), NOT consumed by the mainline. THE ONE BRIDGE = J4-507's `metricGaussGauge_imp_hGaussGerm`: `MetricGaussGauge g ⟹ hGauss` germ — proving my transport-floor CoordGaussGauge/MetricGaussGauge and the mainline's labelled hGauss are THE SAME geometric content (the coordinate Gauss lemma; metric↔inverse dual, pointwise↔germ). The two tracks meet at exactly ONE recognized geometric input.
- **Minimal carried-input set, classified:** (i) IRREDUCIBLE GEOMETRIC (Mathlib-absent exp-map/geodesic): the coordinate Gauss lemma CoordGaussGauge/MetricGaussGauge (=hGauss; NOT derivable from the finite RNC 2-jet per Sol counterexample g=(1+ε‖x‖⁴)δ — shares the 2-jet at 0 but violates off-origin); the RNC gauge hgauge (∂Γ-cyclic=0, replaces raw htr in _gauged); the volume identity Δ_g(½‖x‖²)=n+r∂_r log√det g; the tube residue hgball (one level below an axiom — the in-Lean exp-map stack reduces the Gauss germ to it). (ii) STILL-REDUCIBLE ANALYTIC: hraw (→width-1 pre-collapse J4-359/360), hD2Hexpand (→germ hrep J4-350; ⚠J4-351 exact bound only on the flat/diagonal/√ε collar — a regime boundary, machine-checked satisfiable, NOT vacuity), hPd2conv, the census families. (iii) ⚠ COSMETIC/VACUOUS: the ONLY documented cosmetic discharge (J4-503 single-t hCorrHigher, cRem:=X/(pref·t²)) is in the ABSTRACT-H route, NOT the mainline (which doesn't carry hCorrHigher directly); it was already caught+replaced. NO NEW cosmetic hypothesis found in a1_R6_from_labelled — the 4 labelled inputs are genuine.
- **⚠⚠ THE KEY HONESTY CAVEAT (satisfiability, not J4-503-cosmetic):** `hframeK : ∀ q ∈ K, g q = δ` (mainline §D). If K has nonempty interior ∋ a neighborhood of 0, then g≡δ there ⟹ Riemann(0)=Ric(0)=0, TRIVIALIZING R/6=0. Nothing requires K∈𝓝 0 (only IsCompact K, 0∈K), so with THIN K (e.g. K={0} ⟹ hframeK reduces to the standard g(0)=δ gauge) the theorem is non-vacuous for curved g. BUT ⚠ NO single CURVED witness (Ric(0)≠0, thin K) satisfying the FULL joint antecedent has been exhibited — ALL exhibited certificates (residueJets_satisfiable, radialInput_flat_witness, residual_factorization_flat_witness, coordGaussGauge_flat, corrHigher_bounded_flat) are FLAT/structural. Not Lean-vacuity, but the milestone's non-vacuity for the CURVED case rests on structural/flat satisfiability, NOT a demonstrated curved instance.
- **Don't-undercredit (what the mainline already achieves):** hGauss is essentially DERIVED for the pullback route (J4-341→348 = a full in-Lean exp-map/geodesic Gauss stack, Mathlib-absent; hGauss_pullback_concrete residue = the single tube identity hgball). The C4c/hEboundW wall is DISCHARGED for the concrete gated witness (constRadius_package_and_S1 PROVES hpkgBound via gatedWitnessN1_package_open_CONSTRADIUS — provable, not assumed; the mainline localizes with the cutoff gated witness, correct since a₁ is near-diagonal-local). The van-Vleck 2-jet D²u₀(0)=+(1/6)Ric is a proved theorem (J4-501). htr discharged to hgauge (J4-502).
- **⚠⚠ HONEST BOTTOM LINE:** a₁=R/6 is CONDITIONAL — reduced (two capstone-anchored tracks) to a SMALL set of recognized geometric inputs Mathlib lacks the exp-map to derive (the Gauss lemma/radial gauge [one level above an axiom via hgball], hgauge, the volume identity) + still-reducible analytic carries (hraw, the hD2Hexpand collar identity, hPd2conv, census), all std-3, NONE `:= True`. No new cosmetic gap; the ONE genuine honesty asterisk = non-vacuity for the CURVED case rests on flat/structural certificates, NO demonstrated curved instance. HIGHEST-VALUE NEXT: (a) discharge the Gauss lemma from the in-Lean exp-map stack via the hgball tube residue (collapses the largest common chunk of both tracks); (b) ⚠ THE ESSENTIAL HONESTY CHECK — exhibit a SINGLE CURVED witness (Ric(0)≠0, thin K) satisfying the full a1_R6_from_labelled antecedent, demonstrating the conditional milestone is non-vacuous for the case that matters.

### J4-509 — ⚠⚠⚠ CURVED-WITNESS NON-VACUITY CHECK: a DEMONSTRATED FLAT-ONLY OBSTRUCTION in the a₁ mainline (audit-only, campaign-critical)
- **THE VERDICT:** `a1_R6_from_labelled`'s antecedent is **NOT curved-satisfiable — it is a FLAT-ONLY (near-vacuous) milestone.** Every metric satisfying the full hypothesis census has `Ric(0)=0`, so the advertised t-coefficient `(∑ᵢ ricci g gi i i 0)/6 = R/6` is identically 0 in EVERY instance where the theorem fires. The milestone never actually asserts a nonzero Ricci coefficient. (NOT a soundness issue — std-3 intact, no sorry, no `:= True`; it is about what the conditional's ANTECEDENT can range over.)
- **THE OBSTRUCTING PAIR = `hframeK ∧ hmassone`** (+ `hg` smoothness + `hdg0` vanishing 1-jet): `hframeK` (Section D): `∀ q∈K, g q=δ` (g flat on ALL of the witness-gate K). `hmassone` (Section J): `Tendsto (fun m => ∫ z, Wit (epsSeq m) 0 z) atTop (𝓝 1)` (the K-gated witness carries unit heat mass as τ→0). The witness is `gatedKernel K S P`, `P`'s leading profile = the genuine Gaussian `gaussDdim`. THE ARGUMENT: a curved metric (some component Hessian `f_ab`≠0) has its δ-agreement set `K` rescale under `z=√t·y` into the measure-zero quadratic null cone `{yᵀHy=0}`; a nondegenerate Gaussian assigns it asymptotic mass 0 ⟹ `hmassone`(→1) is FALSE. So: some Hessian≠0 ⟹ `hmassone` fails (not a satisfier); OR all Hessians=0 ⟹ flat 2-jet ⟹ `ricci(0)=0`. EVERY satisfier has Ric(0)=0. ∎ Thin K (K={0}) satisfies hframeK but then FAILS hmassone (measure-zero region ⟹ mass 0). The mission's hope ("thin K ⟹ non-vacuous for curved") is REFUTED: hmassone silently re-imposes the neighborhood-scale K that hframeK then flattens.
- **Sol (gpt-5.6-sol high) CONFIRMS the obstruction + strengthened it:** mass→1 along an ARBITRARY sequence epsSeq→0 does NOT by itself give Lebesgue density 1 (super-lacunary sequences hide holes) — BUT this does NOT rescue curvature: a nonzero Hessian produces a SCALE-PERSISTENT angular cone at every radius, which a nondegenerate Gaussian detects along EVERY sequence→0 (heat rescaling `t⁻¹f(√t·y)→½yᵀHy`, nonvanishing set full-measure). So ∫_K P→0 regardless of the sequence. No curved escape under standard parametrix semantics; curvature/volume-Jacobian/transport terms enter at O(t) after rescaling, cannot move O(1) mass onto the null cone. Implementation caveats verified: `heatParametrix N Θ u t x = gaussDdim t x·Θ(x)^{−1/2}·∑_{k≤N}u_k(x)t^k` (real Gaussian × smooth amplitude, Θ(0)=1); `g` ContDiff; `ricci` via `pd` (actual partials).
- **Constraint classification:** (A) structural/regularity [hold for any smooth metric — hChr/hK/window/hg/hgsymm/hgiC/hgpos/hinvF/the whole analytic-regularity census/the 4 labelled hGauss/hraw/hD2Hexpand/hPd2conv] — non-constraining. (B) curvature-geometric [hg0, hgi, hΓ, hdg0, hGauss, hframeK] — individually ALL curved-satisfiable in RNC (const-curv model: g(0)=δ, ∂g(0)=0, Γ(0)=0, exact Gauss lemma, Ric(0)=(n−1)κ≠0); hframeK curvature-forcing only WITH (C). (C) analytic bounds + mass [dominations hpkgBound/hAdomHeat/… are curved-satisfiable; **hmassone is THE one analytic hyp INCOMPATIBLE with curved hframeK**]. ⚠ hGauss itself is NOT the obstruction (holds for curved RNC); the obstruction is hframeK∧hmassone.
- **Don't-undercredit:** the mainline theorem, the banked chain, std-3 status are ALL genuine + unaffected — the finding is about the antecedent's range, NOT soundness. J4-507 already flagged the flat-witness concern; J4-509 upgrades it from "witness not yet exhibited" to a DEMONSTRATED OBSTRUCTION and refutes the prior "thin K ⟹ non-vacuous for curved" framing.
- **⚠⚠⚠ HONEST BOTTOM LINE:** the a₁=R/6 milestone `a1_R6_from_labelled` does NOT have real content for the curved case. Honestly describable as "a correct, std-3, conditional heat-trace identity whose hypotheses are jointly realizable ONLY in the flat 2-jet case." It is NOT evidence that the machinery computes R/6 for a curved metric. a₁=R/6 must be reported as CONDITIONAL *AND* EFFECTIVELY FLAT-ONLY (curved-case non-vacuity is not just unproven but OBSTRUCTED under the current hypothesis set).
- **NEXT (J4-509 rec):** (a) THE SUBSTANTIVE FIX — decouple hframeK from the mass region: replace the global `hframeK` (g=δ on the witness gate K) with only the pointwise RNC 2-jet (hg0/hdg0 + a genuine curved ∂²g(0)), which requires REBUILDING `hmassone`/`hDaLimLU_from_labelled` to NOT need g=δ on the mass region — i.e. PROVING the curved van-Vleck parametrix has mass→1 (the actual heat-kernel content: ∫ gaussDdim·Θ^{−1/2}·(1+O(t)) → 1 for curved g). Only after this can a curved witness exist. (b) FORMALIZE THE OBSTRUCTION as a machine-checked lemma `hframeK ∧ hmassone ∧ hg ∧ hdg0 ⟹ ∑ᵢ ricci g gi i i 0 = 0` (via heat-rescaling mass ⟹ flat-2-jet), making the flat-only nature rigorous rather than an audit note.

### J4-510 — CurvedParametrixMass: the curved-parametrix MASS→1 (approximate-identity) — PARTIALLY unblocks the flat-only obstruction
- **File:** `QIQTH/CurvedParametrixMass.lean` (std-3, 6 public decls, collision-checked). Attacks the J4-509 flat-only obstruction (step 1 of the fix).
- **HEADLINE `heatParametrix_setMass_tendsto_one`:** `Tendsto (fun τ => ∫_{w∈Ω} heatParametrix N Θ u τ w) (𝓝[>]0) (𝓝 1)` for Ω∈𝓝 0, Θ(0)=1, u₀(0)=1, ContinuousAt Θ/each u_k at 0, eventual AEStronglyMeasurable + a uniform bound `hbound` — the Gaussian approximate-identity mass→1, holding for CURVED Θ, INDEPENDENT of hframeK. Supporting: `parametrixAmp` (A τ w=(Θ w)^{−1/2}·Σ_{k≤N}u_k(w)τ^k), `parametrixAmp_zero_zero` (A(0,0)=1 PROVED from banked vanVleck_zero/transportCoeff_zero — the L=1 part is proved NOT assumed), `parametrixAmp_continuousAt_zero`, `heatParametrix_eq_gauss_mul_amp`.
- **⚠ THE CURVED CERTIFICATE (satisfiability gate — genuinely curved, NOT flat):** `heatParametrix_setMass_tendsto_one_curved_certificate` instantiates Θ=`curvedTheta w = 1+‖w‖²` (Θ(0)=1, Θ^{−1/2}≤1 bounded) + `flatU` (u₀≡1, u_k≡0) over Ω=univ ⟹ mass→1; `curvedTheta_ne_one (1≤n)` is a PROVED theorem that Θ_curved ≢ 1. So the mass→1 provably holds for a genuinely curved AMPLITUDE. (Honest caveat: certifies a curved amplitude, not yet a curved GEOMETRIC instance with Θ=actual van-Vleck and Ric(0)≠0.)
- **AUDIT of hmassone:** it is a PURE CARRIED HYPOTHESIS in A1R6FromLabelled (Section J:336, threaded verbatim into truncatedDuhamelCore_AT_GATE_FULL/hbdryLU_CONCRETE, NOT proved anywhere; the constRadius certificate produces hpkgBound/hmemS0/hopenS0/hS1, NOT hmassone). So there is NO current discharge that touches hframeK; hframeK is a separate Section-D geometry-raw input fed to hDaLimLU_from_labelled. The J4-509 obstruction is a JOINT-satisfiability fact.
- **Sol (gpt-5.6-sol high):** the lemma is analytically sound + the right shape (endorsed the uniform hbound). It does NOT by itself yield the repo's exact hmassone (stated in the z-variable): converting `∫_z Wit(τ,0,z)dz` needs (a) the Layer-A on-gate factorization + (b) a Layer-B change of variables w=Vmap z with Jacobian J(0)=1 (Sol's V(z)=2z counterexample shows J is genuinely necessary). ⚠ THE GATE DECOUPLES: if K and the S-gate are neighborhoods of 0 and the chart inverse Z is continuous with Z(0)=0, then {w|Z w∈gate} is a FULL neighborhood of 0 — NOT measure-thin/null-cone — so mass→1 survives (mass 0 only for half-space/null-cone gates = exactly what hframeK smuggled). Minimal decoupling: hframeK → pointwise jet normalization (g(0)=δ, ∂g(0)=0) in the core dependency path; hframeK is INDEPENDENTLY load-bearing in hDaLimLU_from_labelled (a separate obstruction this lemma doesn't touch).
- **Don't-undercredit:** built on the banked approximate-identity tower GaussianApproxIdentity.gaussDdim_approx_identity (J4-208) → ChartImageApproxIdentity.gaussDdim_set_approx_identity_moving (J4-268 Layer C), reused not re-proved. Discovered banked Layer-A/B-adjacent infra for the next brick: ErrorKernelFactorization (heatOp_gated_split, residual_eq_gauss_mul_A, cutoffError_…), ErrorKernelJointMeas.heatParametrix_uncurry_measurable_from_geometry, InverseChartDisplacement.chartW0_rncRadialSq_error.
- **Build:** green; std-3 all six; no census Π.
- **⚠ HONEST BOTTOM LINE:** PARTIALLY unblocks — removes ONE of two independent uses of flatness (the 0th-order heat-mass normalization is now an approximate-identity phenomenon NOT requiring g=δ near 0; the fixed-neighborhood gate decouples the mass from the δ-set). Does NOT by itself make a1_R6_from_labelled curved-satisfiable because (i) the repo's hmassone is in the z-variable + still needs the exact gated chart-transfer (Layer A + Layer B Jacobian J(0)=1), and (ii) hframeK is independently fatal in hDaLimLU_from_labelled + the final signature. a₁=R/6 remains CONDITIONAL + effectively flat-only until BOTH clear.
- **NEXT J4-511 (agent's rec):** `gatedKernel_mass_tendsto_one_of_localChart` — the exact hmassone bridge with NO hframeK: assume combined K/S gate ∈ 𝓝 0, cutoff≡1 near 0 in an injective chart region, chart inverse Z with Z(0)=0, a change-of-variables `Measure.map Vmap (volume.restrict D) = (volume.restrict Ω).withDensity J` with J continuous J(0)=1, feed this lemma. Then (CRITICAL PATH) the curved replacement for hframeK inside hDaLimLU_from_labelled — likely the real remaining blocker to a nonzero R/6 instance.

### J4-511 — MassChartBridge: the hmassone CHART-BRIDGE — hmassone DECOUPLED from hframeK (abstract-bridge level)
- **File:** `QIQTH/MassChartBridge.lean` (std-3, 5 public decls, collision-checked). Second piece of the J4-509 flat-only fix.
- **What lands:** `weightedParametrix_setMass_tendsto_one` (the weighted moving-AI: `∫_{w∈Ω} gaussDdim τ w·(parametrixAmp N Θ u τ w·φ w) → 1` for Ω∈𝓝 0, Θ(0)=1, u₀(0)=1, φ ContinuousAt 0 with φ(0)=1; `hlocal` proved 1·1=1 from J4-510's `parametrixAmp_continuousAt_zero`×φ-continuity) · `chartMass_tendsto_one_of_weightedCovar` (abstract `Wit` + `hcov : ∫_z Wit =ᶠ[𝓝[>]0] ∫_{w∈Ω} gaussDdim·(parametrixAmp·φ)` ⟹ z-mass→1, via `Tendsto.congr'`) · **`gatedKernel_mass_tendsto_one_of_localChart`** (composes with `epsSeq→𝓝[>]0` ⟹ the EXACT repo `hmassone` shape `Tendsto (fun m => ∫ z, Wit (epsSeq m) 0 z) atTop (𝓝 1)`) · `chartBridge_curved_certificate` (+ curvedPhi/…).
- **AUDIT:** `hmassone` (A1R6FromLabelled:336) = `Tendsto (fun m => ∫ z, vanVleckGatedWitness … (epsSeq m) 0 z) atTop (𝓝 1)`. `vanVleckGatedWitness` (ConvApproximants:161) = `gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g) (transportCoeff…) (uniformInverseChart g gi hC hK))`; on-gate `Wit τ 0 z = gaussDdim τ (W₀ z)·chartFieldAmp τ z`, `W₀ z = uniformInverseChart g gi z 0`, off-gate 0. Banked: on-gate factorization `witness_zero_eq_gauss_mul_amp` ✅, abstract CoV `chart_gaussian_change_variables` (Mathlib `integral_image_eq_integral_abs_det_fderiv_smul`) ✅, moving-AI `gaussDdim_set_approx_identity_moving` ✅, AND **the full A∘B∘C is ALREADY banked as `ChartImageAIConcrete.chartImage_approx_identity_conditional` (general f; f≡1 ⟹ z-mass→1 on 𝓝[>]0), ALREADY hframeK-free**. MISSING: the concrete base-varying CoV bundle M1–M4 for `W₀=z↦uniformInverseChart…z 0` (only the field-varying `Wfv` bundle is banked) ⟹ J4-511 carries the CoV abstractly (`hcov`) rather than manufacturing the missing bundle.
- **Sol (gpt-5.6-sol high) — Route B:** keep the chart weight `φ=radialCutoff·/(J∘V)` explicit, apply the GENERAL moving-AI to `parametrixAmp·φ`, transport across an EVENTUAL CoV equality via `Tendsto.congr'`. `heatParametrix_setMass_tendsto_one` CANNOT be consumed literally (its integrand is `gaussDdim·parametrixAmp`, φ≢1 on Ω; absorbing φ into Θ' has rpow-sign pitfalls) — Route B reuses J4-510's amplitude lemmas cleanly. Exposing `φ(0)=1` (not proving J(0)=1 from RNC now) is correct honest scoping since the base-varying CoV bundle is the missing brick.
- **⚠ THE GATE (genuinely curved, NO g=δ reintroduced):** `chartBridge_curved_certificate` instantiates a curved Θ=1+‖w‖² (≢1) AND a curved weight φ=curvedPhi=(1+‖w‖²)⁻¹ (`curvedPhi_ne_one` PROVED ≢1), both =1 only at origin, over Ω=univ ⟹ the bridge holds. The bridge references NO metric; sole normalization = φ(0)=1 ∧ Θ(0)=1 ∧ u₀(0)=1, all first-order value-at-origin. φ(0)=1⟺J(0)=1 pointwise, compatible with curved RNC (Sol V(z)=2z ⟹ J genuinely needed, but POINTWISE J(0)=1 does NOT force flatness). Curved-inhabited, no vacuity.
- **Don't-undercredit:** the A∘B∘C composition + both CoV layers + the hframeK-free capstone `chartImage_approx_identity_conditional` already existed; new = (a) the weighted moving-AI reusing J4-510's amplitude facts with explicit φ, (b) the exact atTop/epsSeq hmassone shape, (c) a curved-φ certificate.
- **Build:** green; std-3 all five; no census Π.
- **⚠ HONEST BOTTOM LINE:** hmassone is now DECOUPLED from hframeK at the abstract-bridge level (given a J(0)=1 CoV, z-mass→1 follows from J4-510's curved content with NO flatness, certified curved-satisfiable). This is the 2nd of the 2 mass fix pieces (J4-510 chart-variable, J4-511 z-variable bridge). ⚠ STILL OPEN: (i) the CONCRETE hcov for the base-varying chart W₀ = the M1–M4 CoV bundle (injectivity radius/left inverse/0<|det f'| with |det f'(0)|=1) = the acknowledged MISSING brick, and with it the concrete φ(0)=1; (ii) hframeK is STILL consumed in GlobalRawBoundFacade.hDaLimLU_from_labelled (the Da-limit residual gauge), NOT touched here — remains FATAL to curved-satisfiability until independently weakened. a₁=R/6 remains CONDITIONAL + effectively flat-only.
- **NEXT J4-512 (agent's rec):** build the base-varying IFT/CoV package (M1–M4 for W₀=z↦uniformInverseChart…z 0) on a small ball — injectivity radius, left inverse, 0<|det f'| with |det f'(0)|=1 — discharging `hcov` (+ φ(0)=1) concretely; IN PARALLEL begin the hframeK-weakening of hDaLimLU_from_labelled (the residual-gauge use, the remaining fatal flatness dependence).

### J4-512 — DaLimCurvedGauge: hframeK's OTHER fatal use (in hDaLimLU) DECOUPLED — BOTH fatal hframeK uses now addressed
- **File:** `QIQTH/DaLimCurvedGauge.lean` (std-3, 8 public decls, collision-checked). The critical-path brick.
- **AUDIT (how hframeK is used in hDaLimLU_from_labelled):** consumed at EXACTLY ONE site — `obtain ⟨hgi,hΓ⟩ := gauge_from_geometry g gi hK0 hframeK hinvF hdg0` (line 472), threaded nowhere else. `gauge_from_geometry` uses it only via `memGaugeGi_of_geometry → hgi_of_geometry → hg0_of_hframeK`, and `hg0_of_hframeK` is LITERALLY `hframeK 0 hK0` — i.e. it reads ONLY the 0-jet VALUE g(0)=δ. The two produced members are both pointwise-at-0 (MemGaugeGi gi = gi(0)=δ; MemGaugeGamma = Γ(0)=0, the latter from hdg0 alone). **VERDICT: role (c) VALUE-reducible to the 0-jet g(0)=δ** (NOT convenience, NOT genuinely load-bearing).
- **What lands:** `gauge_from_pointwise` (the curved-compatible drop-in for `gauge_from_geometry`: `MemGaugeGi gi ∧ MemGaugeGamma g gi` from {hg0 (g(0)=δ), hinvF, hdg0 (∂g(0)=0)}, with hK0/hframeK REMOVED, via banked `OuterCarryRecon.hgi_of_hg0_hinvF` + `memGaugeGamma_of_hdg0`) · `memGaugeGi_of_hg0` · `hg0_of_hframeK_relax` (soundness: old hframeK ⟹ new hg0, genuine relaxation) · **`curved_gauge_inhabited`** (the curved satisfiability witness) + `confMetric_{hg0,hinvF,hdg0,second_jet_ne_zero}`.
- **⚠ THE CURVED GATE (adversarial, NOT vacuous):** `curved_gauge_inhabited` exhibits a genuine curved metric `confMetric y a b=(1+(y₀)²)δ_ab` on Point 2 satisfying all three weakened hyps {hg0,hdg0,hinvF} (⟹ both gauge members) WHILE `∂²g₀₀(0)=2≠0` (`confMetric_second_jet_ne_zero`, proved) — precisely the 2nd-jet datum hframeK destroys (hframeK⟹∂²g=0⟹Riemann=0⟹Ric(0)=0). So the decoupled gauge antecedent is genuinely curved-satisfiable, NOT secretly flat.
- **Sol (gpt-5.6-sol high):** agreed the τ→0 concentration collapses the multiplicative normalization to its centre value, so the gauge members need g=δ only at 0; minimal replacement = `hg0 : g(0)=δ`. Confirmed {hg0,hdg0,hinvF} curved-inhabited with Ric(0)≠0 (const-curv RNC 2-jet, Ric_ij(0)=(n−1)κδ_ij). ⚠ CORRECTION he raised: concentration does NOT generally erase HIGHER jets (scaled residuals x^a x^b/τ retain 2nd-jet/curvature — that's how a₁ gets its Ricci); the "value-only" claim is specific to the GAUGE MEMBERS, not the whole residual analysis.
- **NO second obstruction found in the hframeK channel.** Don't-undercredit: the value-based chain (`hgi_of_hg0_hinvF`, `hg0_of_hframeK`, `memGaugeGamma_of_hdg0`) already existed; this is a thin re-composition, credited.
- **Build:** ~47s; std-3 all 8; no census Π.
- **⚠ HONEST BOTTOM LINE:** BOTH identified fatal uses of hframeK are now LOGICALLY addressed — hframeK is value-reducible everywhere it currently feeds a1_R6_from_labelled. BUT hframeK is NOT yet LITERALLY removed: `hDaLimLU_from_labelled` still carries hK0/hframeK in its ~180-binder signature, and a1_R6_from_labelled still calls it with them (I did NOT re-elaborate that capstone Π per the monolith constraint). TWO honest caveats before a curved witness of the FULL antecedent: (i) MECHANICAL (J4-513) = `hDaLimLU_from_labelled_jet` (a copy with the single gauge line swapped to gauge_from_pointwise, hK0/hframeK→hg0) + rethread a1_R6_from_labelled — straight substitution, cost = re-elaborating the big Π; (ii) GENUINE remaining audit surface (Sol-flagged, out of scope here): the OTHER ~180 hDaLimLU hyps may have INDEPENDENT non-hframeK flatness (√det g Hessian=Ricci, van-Vleck 2-jet, exact-Euclidean phase/convolution identities, o(1)/o(τ) rate demands that could kill the surviving curvature term) PLUS the upstream CONSTRUCTORS that currently produce these labelled hyps (a hyp can be curved-compatible while its only existing proof still assumes hframeK). a₁=R/6 remains CONDITIONAL + effectively flat-only.
- **NEXT J4-513:** pair the mainline rethread (mechanical) with a TARGETED AUDIT of the √det g / van-Vleck 2-jet channels (the most likely independent flatness) — determine whether the residual analysis's other hyps + their constructors are curved-compatible or harbor a deeper flat-only dependence.

### J4-513 — AUDIT: the a₁ milestone is ONE-CHANNEL-FLAT (hframeK only, value-reducible) — NO independent second flatness (audit-only)
- **THE VERDICT: ONE-channel-flat.** Adversarial audit of the FULL `a1_R6_from_labelled` antecedent (every binder) + upstream constructors finds EXACTLY ONE flat-forcing hypothesis: `hframeK : ∀ q∈K, g q = δ`. Every other geometry-constraining binder is pointwise-at-0, an RNC-exact identity, an inequality/limit with free constants, or bakes curvature into the witness DEFINITION. Sol concurs: "one demonstrated flatness channel, now value-reducible; no demonstrated second flatness channel." `hframeK` is consumed at EXACTLY ONE site (hDaLimLU_from_labelled → gauge_from_geometry → memGaugeGi_of_geometry ⟹ gi(0)=δ); in a1_R6_from_labelled it's passed ONLY to hDaLimLU (line 387) — truncatedDuhamelCore_AT_GATE_FULL / a1_R6_slots_AT_GATE / wide_a1_R6_core_AT_CONSTRADIUS never receive it. Confirmed single consumer.
- **Per-suspect-channel (all CURVED-COMPATIBLE):** (a) √det g / van-Vleck 2-jet: `vanVleck g=(√det g)⁻¹`, `transportCoeff` are genuine functions of curved g (det carries Hessian(0)=−(1/3)Ric); no binder equates Θ≡1 or ∂²g≡0; the core takes Ric as an ABSTRACT parameter (instantiated `ricci g gi · · 0`); the t²-term sum is over Finset.Ico 2 2 = ∅. (b) Ricci-source (hGauss→htr): `htr_from_hGauss` produces `−(2/3)·ricci g gi c d 0` via `metric_secondJet_eq_riemann` — this is the curvature-CARRYING channel; `hGauss` (RNC radial gauge g_{ij}(x)xʲ=xⁱ) is EXACT for curved RNC (Sol: curvature cancels under radial contraction by Riemann symmetries) — NOT flat-only. (c) exact-Euclidean phase/convolution: hmassone content is curved-true (J4-510); all Gaussian dominations are ≤ with free constants, none forces a coeff to 0. (d) o(τ)/o(√ε) rates: hbnd/hraw are upper bounds with free constants, control the residual not the R/6 term. (e) CONSTRUCTORS: the ONLY flat one is the hframeK chain (memGaugeGi_of_geometry), ALREADY given a curved drop-in (J4-512 gauge_from_pointwise / memGaugeGi_of_hg0); memGaugeGamma_of_hdg0, htr_from_hGauss, the core, the witness are all pointwise/curved. NO flat-only hyp/constructor other than the hframeK chain.
- **Sol (gpt-5.6-sol high):** one-channel-flat; remaining work is a CoV/normalization + analytic-packaging problem — "proof depth, not evidence of multi-channel flatness." Two adversarial CONSTRUCTIBILITY caveats (NOT flatness): (i) gated hmassone Layer-A must prove the TOTAL normalized amplitude at the origin = EXACTLY 1 (J(0)=1 alone insufficient); (ii) the Gaussian-phase trap — `e^{−|V(z)|²/4τ} ≤ C·e^{−|z|²/4τ}` does NOT follow from DV(0)=I alone (if |V(z)|²<|z|² anywhere on the gate no fixed C repairs it); needs the exact Vmap phase / RNC radial-distance equality / a widened Gaussian / a one-sided phase inequality.
- **⚠ KEY CAVEAT:** the J4-512 confMetric=(1+y₀²)δ witness does NOT satisfy hGauss in those coordinates — it certifies the GAUGE SUB-PACKAGE only, NOT the full antecedent. A full curved witness requires a genuine RNC / constant-curvature normal-coordinate model (n≥2), patched to a global smooth metric preserving the curved 2-jet.
- **Audit-only** (no witness/obstruction lemma — a full curved witness of the ~280-binder antecedent is not a <5-min job; no clean sub-witness beyond those already banked). Nothing built/staged.
- **Don't-undercredit:** the repo has diagnosed the hframeK obstruction to a single consumer + given it a curved-certified pointwise replacement (J4-512), has a curved-certified mass content lemma (J4-510), and the Ricci-source + core + witness are all structurally curved. This audit CONFIRMS that work suffices to eliminate the demonstrated flatness — it finds NO hidden deeper wall.
- **⚠ HONEST BOTTOM LINE:** the milestone is ONE-CHANNEL-FLAT — curved a₁ is a MECHANICAL rethread + a concrete CoV bundle away, with two analytic-constructibility RISKS to watch (Layer-A origin-value=1; the Gaussian-phase inequality), NOT new flatness. a₁=R/6 remains CONDITIONAL AND EFFECTIVELY FLAT-ONLY as currently stated (a1_R6_from_labelled still literally carries hframeK). The positive finding is depth-of-obstruction: single-channel, value-reducible, clear (non-trivial) constructive path — NOT a multi-channel wall.
- **SHORTEST PATH to a curved witness of the full antecedent:** (1) RETHREAD a1_R6_from_labelled/hDaLimLU_from_labelled to consume pointwise hg0 (or hgi directly, type already MemGaugeGi gi) via gauge_from_pointwise instead of hframeK [mechanical]; (2) Layer-A on-gate factorization `Wit τ 0 z = gaussDdim τ (Vmap z 0)·amp` with amplitude origin-value EXACTLY 1; (3) Layer-B CoV `w=Vmap z 0` (local injectivity, |det DV(0)|=1, gate exhaustion, negligible tail, uniform-in-τ domination) discharging gated hmassone/hpkgBound/hraw curved — ⚠ CHECK THE GAUSSIAN-PHASE INEQUALITY explicitly; (4) instantiate with a genuine n≥2 RNC/const-curv normal-coordinate metric (NOT confMetric — fails hGauss), patched global.
- **NEXT J4-514 (agent's rec):** build the Layer-A on-gate factorization brick `Wit τ 0 z = gaussDdim τ (Vmap z 0)·amp` — the gateway for both the gated hmassone CoV and the Gaussian-phase check, the smallest independent unit. Defer the full-antecedent curved witness until the RNC model + CoV bundle exist.

### J4-514 — LayerAFactorization: the Layer-A on-gate factorization gateway (origin-value=1, curved-safe)
- **File:** `QIQTH/LayerAFactorization.lean` (std-3, 6 public decls, collision-checked; fresh namespace). The first analytic gateway on J4-513's shortest-path to curved a₁.
- **What lands:** `layerA_on_gate_factorization` (re-export of banked `WideWitnessAmplitude.witness_zero_eq_gauss_mul_amp`: `vanVleckGatedWitness … τ 0 z = gaussDdim τ (uniformInverseChart g gi hC hK z 0)·chartFieldAmp … τ z 0` for z∈K, 0∈S z) · `chartFieldAmp_origin_value` (★ `chartFieldAmp … τ 0 0 = 1 + transportCoeff(transportOp(vanVleck g) g gi) 1 0·τ`, needs 0∈K, 0<a<b, det(g 0)=1) · `chartFieldAmp_origin_zero` (=1 at τ=0) · `chartFieldAmp_origin_tendsto_one` (★ → 1 as τ→0⁺) · **`layerA_witness_origin_factor`** (★★ `vanVleckGatedWitness … τ 0 0 = gaussDdim τ 0·(1 + u₁(0)·τ)`) · `hgdet0_curved_satisfiable` (∃ M, det M=1 ∧ M≠1, n≥2).
- **AUDIT:** the on-gate factorization was fully BANKED (`witness_zero_eq_gauss_mul_amp`); the amplitude-at-0 blocks banked (`chartW0_zero` W₀ 0=0, `vanVleck_zero` Θ(0)=1 from det(g 0)=1, `radialCutoff_eq_one`, `transportCoeff_zero` u₀≡1; `chartAmp0_at_zero`/`chartAmp1_at_zero` precedents). NEW = the assembled scalar origin value `chartFieldAmp … τ 0 0 = 1 + u₁(0)·τ` + its 𝓝[>]0 limit → 1 (the mass-limit normalization). ⚠ ORIGIN-VALUE=1 needs ONLY `det(g 0)=1` + W₀ 0=0 + radialCutoff(0)=1 + u₀(0)=1 — NOT the CoV Jacobian, NOT hframeK. The Jacobian J=|det DW₀| enters only via dz=dw/J in the CoV (Layer-B φ weight), a separate factor from chartFieldAmp.
- **Gaussian-phase check:** Layer-A does NOT need it (Sol-confirmed): at z=0, W₀ 0=0 ⟹ |W₀ 0|²=0=|0|² trivially. The banked `chartW0_rncRadialSq_error` is a TWO-SIDED near-isometry squeeze (`rncRadialSq z − L‖z‖·rncRadialSq z ≤ rncRadialSq(W₀ z) ≤ rncRadialSq z + L‖z‖·rncRadialSq z`, L=2nC_W+3nC_W² on ‖z‖<r₀≤1) = the Layer-B mass-domination input, NOT needed here.
- **Sol (gpt-5.6-sol high):** minimal Layer-A = the banked factorization + `chartFieldAmp … τ 0 0 = 1 + u₁(0)·τ` + the 𝓝[>]0 tendsto → 1; J(0)=1 irrelevant to Layer-A (Layer-B only); the phase comparison is Layer-B/domination only; det(g 0)=1 as the sole normalization + a transvection witness certifies non-flatness.
- **THE GATE:** PASS — origin-value=1 is CURVED, NOT secretly flat: uses only `det(g 0)=1` (an RNC normalization true for all normal-coordinate metrics), never hframeK/g=δ. `hgdet0_curved_satisfiable` exhibits a transvection (det=1, ≠1) ⟹ det-1 strictly weaker than flat-at-origin; with `chartFieldAmp_origin_value` g-generic (no hframeK) the normalization is genuinely curved-inhabited.
- **Don't-undercredit:** the factorization + the amplitude-at-0 pattern (`chartAmp0_at_zero`/`chartAmp1_at_zero`) were banked; new = the combined scalar origin value + its mass-limit tendsto.
- **Build:** green; std-3 all six; no census Π; fresh namespace collision-checked.
- **⚠ a₁=R/6 remains CONDITIONAL + EFFECTIVELY FLAT-ONLY.** Layer-A is a de-risking gateway (NOT the curved witness) — confirms the origin-normalization piece of Sol's constructibility caveat is NOT the obstruction and IS curved-safe. STILL STANDING for the full concrete hcov (Layer-B): the base-varying CoV bundle for W₀ (M1–M4) with the Jacobian J + the weight φ=radialCutoff/J (needs J(0)=1 ⟹ φ(0)=1) + the Gaussian-phase domination inequality from the two-sided `chartW0_rncRadialSq_error`.
- **NEXT J4-515 (agent's rec):** the Layer-B CoV bundle — the base-varying change-of-variables for W₀ (M1–M4) producing the Jacobian J + weight φ=radialCutoff/J, prove J(0)=1 (⟹ φ(0)=1), discharge the Gaussian-phase domination from the two-sided `chartW0_rncRadialSq_error`. That is the concrete content between the banked hcov/φ-interface (MassChartBridge) and a curved-satisfiable mass limit.

### J4-515 — LayerBChangeVars: the Layer-B Gaussian-phase domination MAJORANT (integrability side of hcov)
- **File:** `QIQTH/LayerBChangeVars.lean` (std-3, 3 public decls, collision-checked). The integrability/hbound side condition of the concrete Layer-B CoV.
- **What lands:** `chartW0_radialSq_half_lower` (`∃ r>0, ∀ z∈K, ‖z‖<r → ½·rncRadialSq z ≤ rncRadialSq(uniformInverseChart g gi z 0)`, from the banked TWO-SIDED `chartW0_rncRadialSq_error`) · **`gaussDdim_chartW0_le_wide`** ★ (`∃ r>0, ∀ z∈K, ‖z‖<r → ∀ τ>0, gaussDdim τ (W₀ z) ≤ gaussDdimWide τ z`) · `phase_domination_curved_satisfiable` (the gate).
- **AUDIT (W₀ CoV facts):** BANKED (curved-generic): `chartW0_zero` (W₀ 0=0), `chartW0_displacement` (‖W₀ z+z‖≤C_W‖z‖²), `chartW0_rncRadialSq_error` (two-sided ℓ² near-isometry, explicit L), `chartW0_nearIsometry`. ⚠ MISSING/BLOCKED: the base-point derivative `fderiv (z↦W₀ z)` / Jacobian — `InverseChartDisplacement` FIREWALL blocker (the chart is `.choose`-built, no base-point flow regularity); `chartW0_displacement` is stated only for z∈K (not a full nbhd), so `HasFDerivAt W₀ (−I) 0` does NOT follow ⟹ **M4 `|det DW₀(0)|=1` is BLOCKED**. The field-varying Wfv bundle is a template but does NOT supply the base-varying derivative.
- **Smallest unit + width:** built the phase domination (option ii, since M4 is blocked). `½·rncRadialSq z ≤ rncRadialSq(W₀ z)` on `‖z‖<1/(2(L+1))` ⟹ `exp(−rncRadialSq(W₀z)/4τ) ≤ exp(−rncRadialSq z/8τ)`; `(√(4πτ))⁻ⁿ` prefactors cancel ⟹ C=1, exactly the repo's `gaussDdimWide`. ⚠ WIDTH CHANGES 4τ→8τ (widened Gaussian): a VALID MAJORANT for integrability/hbound/tail/off-diagonal, BUT `∫gaussDdimWide τ = 2^{n/2} ≠ 1` (→ 2^{n/2}·δ₀, not δ₀), so it MUST NOT compute the unit mass — FIREWALLED. MassChartBridge's `hcov` is an EXACT integral EQUALITY (doesn't consume the domination directly); the domination feeds the integrability/hbound side conditions; the exact unit mass comes from un-widened `gaussDdim` after the exact CoV.
- **Sol (gpt-5.6-sol high):** confirmed this is the right smallest unit given the fderiv block; recommended the exact factoring used (half-lower geometric core + Gaussian corollary, L=0-safe phrasing). Confirmed the width distinction verbatim (majorant OK; wrong mass; unit mass needs exact/(1±δ) sharp comparison). Flagged: the origin normalization is `|det DW₀(0)|=1` NOT `det=1` (DW₀(0)=−I fails in ODD dim), M3 must use the ABSOLUTE Jacobian.
- **THE GATE:** holds CURVED — fully g-generic, derived only from the curved-generic banked error, no hframeK/g=δ. `phase_domination_curved_satisfiable` certifies the core inequality is inhabited by a genuinely non-isometric radial distortion W z=(4/5)z (c≠±1) ⟹ doesn't secretly force the isometric/flat W z=±z. Curved-inhabited, not vacuous.
- **Don't-undercredit:** reused the banked chart tower (near-isometry error, displacement) + the existing `gaussDdimWide` absorption machinery; the deliverable plugs into present infra.
- **Build:** green; std-3 all three; no census Π; import wired by the agent.
- **⚠ HONEST BOTTOM LINE:** discharges ONLY the Gaussian/integrability SIDE CONDITION of the concrete hcov (the majorant feeding hbound/tail) — NONE of the exact hcov equality. STILL REMAINING in Layer-B: M1 (injectivity of z↦W₀z), M2 (left inverse + support/cutoff transport), M3 (positive/absolute Jacobian on the domain), M4 (`|det DW₀(0)|=1`, BLOCKED on the unbanked base-point fderiv), the EXACT CoV equality (Jacobian cancellation + domain bookkeeping), and the MassChartBridge assembly. a₁=R/6 remains CONDITIONAL + effectively flat-only.
- **NEXT J4-516 (agent's rec):** attack M4 by first establishing base-point regularity of z↦W₀ z — test whether the mainline gate K can be taken to CONTAIN a neighborhood of 0 so `chartW0_displacement` on a full nbhd yields `HasFDerivAt W₀ (−I) 0` (unblocking `|det DW₀(0)|=1` ⟹ φ(0)=1 structurally); if K cannot, pursue M1 injectivity from the `ApproximatesLinearOn` germ already used in `chartW0_displacement`.

### J4-516 — ChartW0Fderiv: M4 |det DW₀(0)|=1 (standalone) + ⚠ DON'T-UNDERCREDIT: the concrete CoV was ALREADY COMPLETE
- **File:** `QIQTH/ChartW0Fderiv.lean` (std-3, 3 public decls, collision-checked). Standalone extraction of M4.
- **What lands:** `chartW0_hasFDerivAt_zero` (`HasFDerivAt (z↦uniformInverseChart g gi hC hK z 0) (−ContinuousLinearMap.id ℝ (Point n)) 0`, given hK compact + `h0Kmem : K∈𝓝 0`) · `chartW0_fderiv_zero` (`fderiv ℝ W₀ 0 = −id`) · `chartW0_absdet_fderiv_zero` (**M4: `|det(fderiv ℝ W₀ 0)|=1`** = |(-1)ⁿ|).
- **AUDIT:** `chartW0_displacement` (InverseChartDisplacement:91) domain = `∀ z∈K, ‖z‖<r₁` (compact K, not a ball). `uniformInverseChart` (UniformChartRadius:228) is `.choose`-built per base point on K (=0 off K). THE KEY INSIGHT (eventual-near-0): combining the compact-K bound with `K∈𝓝 0` via `filter_upwards` upgrades to `∀ᶠ z in 𝓝 0` ⟹ `‖W₀ z+z‖=o(‖z‖)` ⟹ HasFDerivAt.
- **⚠⚠ DON'T-UNDERCREDIT (the J4-515 "M4 BLOCKED" premise was STALE):** M4 was NEVER blocked. `BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center` (J4-272) already proves `HasFDerivAt W₀ (−id) 0` unconditionally (given K∈𝓝 0) from `chartW0_displacement` + `filter_upwards h0Kmem`; and `|det(fderiv W₀ 0)|=1` is ALREADY a proven conjunct in `EnrichedChartBundle.enrichedChartBundle` (line 123, proof 152–162; AxiomAudit-pinned line 18618). This file just extracts them as standalone directly-consumable lemmas. No new math, no Sol consult, NO WALL.
- **⚠⚠ THE ENTIRE CONCRETE CoV IS ALREADY COMPLETE ON THE MAINLINE:** the J4-272→279 line (BaseVaryingIFTPackage, GeodesicReversalRoute, TerminalVelC2, FixedFChartImageAI, BaseSlotAmplitude, FixedFTrioDischarge, EnrichedChartBundle, GateAnnulusSplit) already built the full M1–M4 base-varying CoV bundle [M1 within-derivative field, M2 InjOn, M3 left-inverse V, M4 positive/unit Jacobian, image-nbhd, ContinuousOn V, the assembled approximate-identity limit — all in `enrichedChartBundle`/`chartImage_approx_identity_v3`], discharged hbound/hlocal, and marked the fixed-f chart-image approximate-identity DONE (J4-279). This reduces the fixed-f carry list to just `hGgate`/`hSupp` (the ball/annulus gate split = obstruction (B)). ⚠ The J4-510→515 Layer-B thread (CurvedParametrixMass/MassChartBridge/LayerAFactorization/LayerBChangeVars) is a REDUNDANT/orphan branch that never checked the J4-272→279 line — a recurring don't-undercredit failure (should have grepped the mainline CoV before building the Layer-B majorant).
- **GATE:** |det(−I)|=1 dimension-only, curved-generic (`chartW0_displacement` g-generic, no hframeK/g=δ); HasFDerivAt from a GENUINE nbhd (K∈𝓝 0), not compact-only-faked.
- **Build:** green (30s); std-3 all three; import wired.
- **⚠ a₁=R/6 remains CONDITIONAL + EFFECTIVELY FLAT-ONLY** — M4 was never the barrier; it changed nothing about a₁'s status. THE ACTUAL REMAINING FRONTIER (per this audit): **obstruction (B)** = the `hGgate`/`hSupp` witness-gate-radius vs CoV-ball ANNULUS SPLIT (the `WideBoundaryLimDischarge`/`GateAnnulusSplit` thread) — the real barrier between the fixed-f approximate-identity (DONE) and the varying-f a₁ assembly. PLUS the mechanical mainline rethread (hframeK→hg0) + a genuine RNC/const-curv curved witness.
- **NEXT J4-517:** do NOT continue the redundant Layer-B majorant branch. Either (a) reconcile/retire LayerBChangeVars against the complete EnrichedChartBundle CoV, or (b) ATTACK obstruction (B) — the hSupp gate-annulus split (WideBoundaryLimDischarge/GateAnnulusSplit), the genuinely-open frontier. RECON-FIRST: re-map the ACTUAL current state of the varying-f a₁ assembly given the CoV is done, BEFORE building (the J4-515 redundancy shows the mainline is further along than the Layer-B chain assumed).

### J4-517 — RECON: the varying-f a₁ assembly map — obstruction (B) is CLOSED; the true frontier = hPd2conv/hraw/iterE + geometric bridges (recon-only, 3rd don't-undercredit correction)
- **THE MAP (mission premise STALE):** both the fixed-f AI AND the varying-f (moving-f) boundary assembly are ALREADY BUILT on the mainline. (a) Fixed-f AI (J4-279, `GateAnnulusSplit.chartImage_approx_identity_final`): PROVEN, `∫ z, Wit(τ,0,z)·f(z) → f(0)` for fixed bounded-meas-cont-at-0 f; `hGgate`/`hSupp` ELIMINATED here. (b) Varying-f boundary: `MovingFBoundaryLim` (J4-280 frozen slice proven) → `MovingCorrRecombination.hBoundaryLim_FULLY_INTERNAL` (J4-306: `hMovingCorr` DISCHARGED, on-ball bounded-mass×uniform-sup + 2 off-ball Gaussian tails + integral_add_compl) → `EnvelopeWiringLocUnif.hBoundaryLim_DONE` (reduces to a single LeviSeriesLocalData package + window-floor). The varying-f boundary member is a THEOREM conditional only on satisfiable joint-continuity data.
- **OBSTRUCTION (B) — CLOSED, not the frontier:** `hGgate : ∀ z∈ball 0 ρ, z∈K ∧ 0∈S z` (on-ball gate activation) + `hSupp : ∀ τ, ∀ z∉ball 0 ρ, vanVleckGatedWitness … τ 0 z = 0` (τ-uniform off-ball vanishing). Both were carries of the FIXED-f `chartImage_approx_identity_v3` (J4-278), DISCHARGED at J4-279: `hGgate`→measure/support bookkeeping (`hGgate_of_gate_activation`, radius cap ρcap=min ρA rS); `hSupp`→NOT a support fact (the concrete witness does NOT vanish off a small ball — its gate is WIDER than the CoV ball, the structural mismatch) but replaced by the Gaussian-tail annulus split `offBall_integral_tendsto_zero` (‖∫_{ballᶜ} Wit·f‖ ≤ C·Cf·∫_{ballᶜ} gaussDdim(λτ)→0). So (B) = measure-bookkeeping + a Gaussian-tail estimate, BOTH already discharged. ⚠ (B) is NOT a carried hyp of `a1_R6_from_labelled` at all (lives only in the fixed-f sub-thread). Closed ~230 increments ago.
- **Sol (gpt-5.6-sol high) — the TRUE remaining distance to CURVED a₁:** (1) MECHANICAL (plumbing): swap hframeK→hg0 (bank exists, DaLimCurvedGauge.gauge_from_pointwise) + thread hBoundaryLim_DONE into a1_R6_from_labelled — both require re-touching the ~280-binder capstone (deferred, ENGINEERING not analysis). (2) ANALYTIC FRONTIER (genuine, 3 obligations): (a) positive-time PARAMETRIC (joint) CONTINUITY of the iterated Levi convolutions `iterE` (dominated convergence interior + Gaussian endpoint + induction + summable envelope; on time bounded away from 0); (b) ⚠ `hPd2conv` (frozen→full 2nd-derivative interchange — likely the HARDEST local piece: 2nd derivs of a narrow Gaussian are L¹-size ~t⁻¹, uniform convergence INSUFFICIENT, needs Taylor subtraction / moment cancellation / IBP); (c) ⚠ `hraw` residual-order — must be DERIVED from the transport/htr cancellation, NOT postulated (else part of the coefficient HIDES there). (3) GEOMETRIC BRIDGES: `htr` (∑∂²g=−(2/3)Ric, RNC 2-jet→Ricci, curved-true, verify sign/index/contraction — sphere sanity check) + `hGauss` (radial Gauss lemma ∑ⱼ g_ij(x)xⱼ=xᵢ, curved-true for genuine RNC metrics; ⚠ NOT from hg0+hdg0 alone; ⚠ the confMetric conformal witness does NOT satisfy hGauss off 0 — need a metric in ACTUAL normal coordinates as the simultaneous witness).
- **⚠⚠ CIRCULARITY-AUDIT RISK (Sol):** `hPd2conv`/`hraw` are NOT harmless labels — they may smuggle the coefficient (like the cosmetic hCorrHigher J4-503 caught, or the flat-only hframeK J4-509 caught). R/6 division of labor: R/6 lives in `transportCoeff` via the first transport recurrence on the van-Vleck-normalized leading term, fed by `htr`; Levi/boundary handle only the remainder. Circularity checks needed: transportCoeff must be VERIFIED to cancel the residual (not just defined); the remainder must be shown o(t) (t·T(t)→0, not merely an exact decomposition); check the volume/measure conjugation convention.
- **Recon-only** (no build): the mission forbids re-elaborating the ~280-binder Π (the swaps require it); the frontier pieces are multi-hour new analysis. The `hframeK→hg0` curved replacement is already banked (J4-512) as a standalone.
- **Don't-undercredit (3rd correction J4-501/516/517):** banked axiom-free std-3: fixed-f AI with hGgate/hSupp discharged (J4-279); the entire moving-f hMovingCorr (J4-306); hBoundaryLim_DONE; the curved hframeK→hg0 (J4-512). The "ball/annulus gate split" this recon set out to attack was closed ~230 increments ago.
- **⚠ HONEST BOTTOM LINE:** a₁=R/6 remains CONDITIONAL — now conditional on **Levi-series regularity (iterE continuity) + the labelled 2nd-derivative/residual inputs (hPd2conv, hraw) + the geometric bridges (htr, hGauss)**, NOT on flatness. It is NOT "obstruction (B) then mechanical rethread + a curved witness" — there are THREE analytic obligations + two geometric bridges, and hraw/hPd2conv carry a genuine circularity-audit risk. Key files: GateAnnulusSplit.lean, MovingFBoundaryLim.lean, MovingCorrRecombination.lean, EnvelopeWiringLocUnif.lean, DaLimCurvedGauge.lean, A1R6FromLabelled.lean, CapstoneStatus.lean, WideBoundaryLimDischarge.lean.
- **NEXT J4-518:** RECON/AUDIT `hPd2conv` and `hraw` at the concrete gate — is each (i) already a banked proven lemma, (ii) reducible to a small frozen-Euclidean 2nd-derivative convolution lemma, or (iii) a HIDDEN conclusion/flat-only/coefficient-smuggling trap (adversarial check on hraw's time-order + hPd2conv's limiting value). The correct next frontier — NOT another gate-split branch.

### J4-518 — AUDIT: hPd2conv is SOUND (discharged); hraw's LINEAR binder is a 2nd FLAT-ONLY channel (coefficient-neutral, fix already banked) — refines the one-channel verdict (audit-only)
- **`hPd2conv` VERDICT: (ii) REDUCIBLE, coefficient-neutral, HONEST — no trap.** Exact statement (A1R6FromLabelled:195, per u∈U, per i, at RNC origin): `Tendsto (fun m => pd(fun y=>pd(fun x=>heatConvFrozen H F u (u−εₘ) x 0) i y) i 0) atTop (𝓝 (pd(fun y=>pd(fun x=>heatConv H F u x 0) i y) i 0))` — a PLAIN INTERCHANGE (lim ∂²frozen = ∂²full), pins NO value/coefficient. DISCHARGED (not carried vacuously): `Pd2ConvDissolution.hPd2conv_from_census` (std-3, J4-363/365), lifted per-u by `Pd2ConvPerU.hPd2conv_perU`. Route reduces the 2nd-deriv interchange to a FIRST-derivative uniform-limit-of-derivatives at the single point 0 (via the carried (t−s)^{−1/2}-dominated first-interchange family `CConvV2Facade.hfam_v2` + frozen linewise `hQ1` + sliver census `hsliver` giving `gcoef`'s Fréchet deriv). ⚠ Sol's t⁻¹ trap check PASSES: the discharge does NOT assume uniform convergence of the narrow-Gaussian SECOND derivatives (the unsound L¹~t⁻¹ route) — it transfers the difficulty to the legitimate first-order `hsliver`. No secret uniform-2nd-derivative assumption.
- **`hraw` VERDICT: (iii) FLAT-ONLY / mis-graded as literally stated — but NOT coefficient-smuggling; curved-valid replacement already built.** Exact statement (GlobalRawBoundFacade:76): `GlobalGatedRawBound g gi H P := ∀ τ>0, ∀ p q, |heatOp g gi H τ p q| ≤ P·((rncRadialSq(p−q)/τ + 1)·gaussDdim τ (p−q))` — LINEAR, width-1, free P≥0 (heatOp on the van-Vleck witness = the N=1 parametrix RESIDUAL). ⚠ The genuine curved residual (campaign self-diagnosed J4-362, `HrawPreCollapse`, via `WidthMarginEngine.uniformResidual_gaussian_bound_tau_narrow`) grades T1+T2−T3 with a QUADRATIC term T2=(1/τ²)·G·⟨(g⁻¹−δ)·v⊗v⟩·w₀ = (r²/τ)²·G (because g⁻¹−δ=O(r²)=curvature × v⊗v=O(r²)). Honest curved residual = `B·(((r²/τ)²+r²/τ+1)·G_τ)`. THE LINEAR binder is curved-UNSATISFIABLE when T2≠0: x²·G ≤ P(x+1)·G fails as x=r²/τ→∞ (Sol confirmed |A|≤0 contradiction); it holds FLAT (g=δ, the T2=0 locus) or only at a wider Gaussian. ⚠ COEFFICIENT-NEUTRAL confirmed: a free-constant upper domination, no diagonal value / asymptotic equality / order condition / R/6. Consumer `DaLimHardTranche.hEdom_of_gaussPoly_residual` → E₀=13P, E₁=0 (pure constant×wider-Gaussian DCT envelope). Switching to the honest QUADRATIC width-4/3 form (`HrawPreCollapse.hEdom_concrete_final`, std-3) yields the IDENTICAL downstream hEdom — constants/widths only, NO coefficient change.
- **Sol (gpt-5.6-sol high):** hPd2conv (ii) reducible/coefficient-neutral, reduction legitimate; hraw (literal linear) (iii) flat-only/vacuity trap as stated, NOT coefficient-smuggling, replaceable by the curved-valid quadratic. R/6 still lives SOLELY in transportCoeff/htr.
- **⚠ REFINES the J4-513 ONE-CHANNEL verdict:** there are actually TWO flat-only binders in `a1_R6_from_labelled` — `hframeK` (J4-509) AND the linear `hraw` (this audit). BOTH are COEFFICIENT-NEUTRAL with BANKED curved-valid replacements (hframeK→`DaLimCurvedGauge.gauge_from_pointwise` J4-512; linear-hraw→`HrawPreCollapse.hEdom_concrete_final` quadratic width-4/3 J4-362). So the capstone as-written is flat-only via ≥2 REPAIRABLE named binders, NOT a deep coefficient hole. J4-513's "hraw curved-compatible" was slightly optimistic — hraw is curved-compatible IN PRINCIPLE (replacement exists) but the binder AS NAMED is flat-only.
- **Don't-undercredit:** hPd2conv fully DISSOLVED (Pd2ConvDissolution+Pd2ConvPerU, J4-363/365, std-3, honesty firewalls + width-2 satisfiability witness); hraw's flat-only defect SELF-DIAGNOSED (J4-362) with the curved-valid quadratic-grading replacement built end-to-end (HrawPreCollapse, 7 std-3 lemmas incl. hEdom_concrete_final). A mature self-critical campaign, not raw postulates.
- **Audit-only** (no build): the refuting content (x²≰P(x+1)) + the curved-valid replacement already exist as std-3 decls; a new refuter risks the sibling race for negligible value.
- **⚠ HONEST BOTTOM LINE:** neither is a coefficient-smuggling trap. hPd2conv is fully honest+discharged. hraw does NOT hide R/6 but its LITERAL capstone binder is flat-only/mis-graded (curved-unsatisfiable when T2≠0) — the honest curved-valid form (quadratic width-4/3 → same hEdom) is already proven; the capstone simply still names the idealized linear one. a₁=R/6 remains CONDITIONAL + EFFECTIVELY FLAT-ONLY — the flatness now traced to TWO specific REPAIRABLE capstone binders (hframeK, linear-hraw), both coefficient-neutral with banked fixes, rather than a deep coefficient hole.
- **NEXT J4-519:** re-wire `a1_R6_from_labelled` to consume the curved-valid QUADRATIC hgate (via `HrawPreCollapse.hEdom_concrete_final`) in place of the flat-only linear `hraw` binder — converts the capstone from "vacuous on curved through hraw" to "curved-satisfiable through hraw", zero coefficient change (constants/widths only). ⚠ AUDIT THE RE-WIRE COST FIRST: can it be a THIN black-box corollary (like J4-502's `trueKernel_diagonal_a1_eq_R6_gauged`) or does it force re-elaborating the ~280-binder Π (expensive, 50-100min)? If thin, build; if expensive, scope. This + the hframeK→hg0 swap + threading hBoundaryLim_DONE are the 3 "mechanical but re-touch the capstone" items.

### J4-519 — A1R6FromLabelledCurved: the CURVED-VALID hraw-channel rewire of the a₁ capstone — ONE of TWO flat-only binders REMOVED (+ MONOLITH FEAR REFUTED)
- **File:** `QIQTH/A1R6FromLabelledCurved.lean` (std-3, capstone-level, collision-checked).
- **What lands:** `a1_R6_from_labelled_curved` = a VERBATIM copy of `a1_R6_from_labelled` with EXACTLY two coupled edits: binder (vii) `hraw : GlobalGatedRawBound g gi H_G P` (LINEAR width-1, flat-only, curved-UNSATISFIABLE when T2≠0) SWAPPED for the curved-valid QUADRATIC on-gate carry `hgate : ∀ τ>0, ∀ q∈K, ∀ p∈closure(constGate … q), |heatOp g gi (vanVleckGatedWitness …) τ p q| ≤ P·(((rncRadialSq(p−q)/τ)²+rncRadialSq(p−q)/τ+1)·gaussDdim(4/3·τ)(p−q))`, and `hDa` routed through `LabelledRethreadV2.hDaLimLU_from_hgate` instead of `hDaLimLU_from_labelled`. SAME conclusion (the a₁ two-jet at the const-radius gate).
- **COST-AUDIT:** the capstone consumes `hraw` at exactly ONE site — passed into `hDaLimLU_from_labelled`; the FIRST `hraw→hEdom` point is inside it (GlobalRawBoundFacade:505, `hEdom_of_globalRawBound … hraw` → the ∃-hEdom object both linear+quadratic routes produce identically); downstream (core/slots/wide) consume `hDa` never `hraw`.
- **⚠⚠ MONOLITH FEAR REFUTED (measured):** the "50-100min/125GB" estimate for the ~280-binder capstone Π was WRONG — the EXISTING capstone elaborates in **79s**, the curved variant in **57.5s** (fresh module build 31s). The capstone re-elaboration is CHEAP (well under the 8-min bound), so route (b) [moderate re-statement] was built; and the OTHER two swaps (hframeK, hBoundaryLim) are ALSO tractable bricks (~1min each), NOT monolith blow-ups.
- **Sol (gpt-5.6-sol high):** no thin capstone-level corollary exists (a theorem body can't be inverted into a hDa-continuation; the linear hraw can't be produced from hgate) — any full-signature curved wrapper forces a fresh full-Π elaboration; the measured 57.5s refutes the MAGNITUDE not the existence.
- **THE GATE (adversarial):** genuinely hraw-FREE — grep confirms NO `hraw`/`GlobalGatedRawBound` in the signature (the 4 hits are all comment/docstring prose, lines 2/5/46/400). The swapped `hgate` carries the `(r²/τ)²` curvature term the true curved residual has (g⁻¹−δ=O(r²)) = the curved-VALID form (J4-362 satisfiable honest grading, curved-inhabited). Coefficient-neutral (R/6 solely in transportCoeff/htr, untouched). NOT a relabel — the flat-only predicate is entirely gone.
- **Don't-undercredit:** the entire curved intermediate machinery (`hDaLimLU_from_labelled_v2` / `hEdom_vanVleck_of_hgate` / `hDaLimLU_from_hgate`) was ALREADY banked in J4-364; this is ONLY the capstone-level wiring.
- **Build:** module 31s fresh, capstone Π 57.5s; std-3; collision-checked (AxiomAudit green, mainline intact); import wired.
- **⚠ HONEST BOTTOM LINE:** the flat-only linear `hraw` binder is now REMOVED at the capstone level (curved-valid quadratic hgate replaces it, coefficient-neutral). Of the 3 capstone flat-only/pending items, **1 removed (hraw); 2 remain**: `hframeK` (still carried verbatim in the curved variant's signature — its banked curved swap `DaLimCurvedGauge.gauge_from_pointwise` J4-512 NOT yet threaded) + `hBoundaryLim` (thread `hBoundaryLim_DONE`). a₁=R/6 stays CONDITIONAL + effectively flat-only (the hframeK thread + hBoundaryLim + iterE/htr/hGauss curved bridges + a genuine RNC curved witness all remain).
- **NEXT J4-520:** thread the banked `gauge_from_pointwise` (J4-512) to remove `hframeK` from the capstone. ⚠ DEEPER swap than hraw: `hframeK` is consumed inside `hDaLimLU_from_*` via `gauge_from_geometry`, so it needs a `hDaLimLU_from_hgate`-analogue that internally uses `gauge_from_pointwise` — build/check that intermediate first, then the capstone Π (likely ~1min given these measurements). ⚠ THE CAPSTONE Π IS CHEAP (~1min) — the three swaps are tractable; a genuinely curved a₁ milestone (all 3 flat-only binders removed) is now a realistic near-term target, THEN iterE continuity + the geometric bridges htr/hGauss + a genuine RNC curved witness.

### J4-520 — A1R6FromLabelledCurvedGauge: the SECOND flat-only binder REMOVED — BOTH hraw + hframeK gone from the a₁ capstone (2 of 3)
- **File:** `QIQTH/A1R6FromLabelledCurvedGauge.lean` (std-3, 3 public decls, collision-checked). Built on J4-519's hraw-free variant.
- **What lands:** `a1_R6_from_labelled_curved_gauge` (byte-identical conclusion to `a1_R6_from_labelled_curved` — the a₁ two-jet at the const-radius gate — with the `hframeK : ∀ q∈K, g q i j = δ` binder REMOVED, hDa routed through `hDaLimLU_from_hgate_gauge` using the already-carried pointwise `hg0`) + two reusable bricks `hDaLimLU_from_labelled_v2_gauge` (R1-gauge) + `hDaLimLU_from_hgate_gauge` (R3-gauge).
- **COST-AUDIT:** `hframeK` entered at EXACTLY ONE place inside R1 (`LabelledRethreadV2.hDaLimLU_from_labelled_v2`): `obtain ⟨hgi,hΓ⟩ := gauge_from_geometry g gi hK0 hframeK hinvF hdg0`, used ONLY as `hframeK 0 hK0` to read g(0)=δ. The hg0-carrying replacement `gauge_from_pointwise` was ALREADY banked (J4-512); the R1/R3 census assembly ALREADY banked (J4-364). J4-520 built the two gauge-variant Da-limit bricks (verbatim R1/R3 copies with the single gauge line swapped to `DaLimCurvedGauge.gauge_from_pointwise g gi hg0 hinvF hdg0`) + the capstone wiring. Module build 33s; monolith fear refuted again (the a₁ facade Π is cheap).
- **THE GATE (adversarial):** genuinely hframeK-FREE — grep confirms every `hframeK`/`∀ q∈K, g q=δ` occurrence is comment/docstring prose ONLY; no such binder in any of the 3 signatures. Carries the pointwise `hg0`/`hinvF`/`hdg0`. Curved-satisfiable: `{hg0,hinvF,hdg0}` curved-inhabited by J4-512's `confMetric` on Point 2 (∂²g₀₀(0)=2≠0). NOT a relabel — the internal gauge sub-assembly genuinely routes through the curved-valid `gauge_from_pointwise` (output type `MemGaugeGi ∧ MemGaugeGamma` identical to `gauge_from_geometry`).
- **Sol:** not consulted — the threading was mechanical, matching the banked J4-512/J4-364 shapes exactly.
- **Don't-undercredit:** `gauge_from_pointwise` + `confMetric` + the R1/R3 census assemblies were all already banked (J4-512/J4-364); J4-520 = capstone wiring + the 2 thin gauge-variant Da-limit bricks.
- **Build:** module 33s; std-3 all three; AxiomAudit green (9798 jobs, no collision).
- **⚠ HONEST BOTTOM LINE:** BOTH flat-only capstone binders are now removed at the capstone level — **2 of 3** (`hraw` via J4-519's hgate, `hframeK` via this J4-520's hg0/gauge_from_pointwise). The capstone is now curved-SATISFIABLE through those two channels, coefficient-neutral (R/6 solely in transportCoeff/htr, untouched). It does NOT derive curved a₁. Remaining carried/labelled: the `hBoundaryLim` thread (thread `hBoundaryLim_DONE`), iterE positive-time continuity, the `htr`/`hGauss` geometric bridges, and a genuine full-census RNC curved witness. a₁=R/6 stays CONDITIONAL + effectively flat-only until those close.
- **NEXT J4-521:** thread the curved swap for `hBoundaryLim` (thread the banked `EnvelopeWiringLocUnif.hBoundaryLim_DONE` — 3 of 3, yielding a genuinely-curved-SIGNATURE a₁ capstone), OR if that has no directly-threadable form, audit which of iterE/htr/hGauss is next-cheapest AND whether a single `confMetric`-style curved witness can simultaneously satisfy the remaining labelled binders to certify the capstone antecedent is curved-inhabited as a WHOLE (the milestone-level non-vacuity the J4-509 obstruction demanded).

### J4-521 — A1R6FromLabelledCurvedBoundary: the 3-of-3 CURVED-SIGNATURE a₁ capstone (hBoundaryLim threaded)
- **File:** `QIQTH/A1R6FromLabelledCurvedBoundary.lean` (std-3, collision-checked). Built on the J4-520 curved_gauge variant.
- **What lands:** `a1_R6_from_labelled_curved_boundary` — identical conclusion to the J4-520 capstone (the a₁ two-jet at the const-radius gate) with the opaque Section-H `hBoundaryLim` binder REMOVED, supplied from the banked `EnvelopeWiringLocUnif.hBoundaryLim_DONE` (instantiated at S:=constGate…, hC:=hChr), and a new Section L carrying the boundary-assembly input list.
- **COST-AUDIT:** SHAPE MATCH EXACT, no bridge — `hBoundaryLim_DONE`'s conclusion is byte-identical to the capstone's `hBoundaryLim` binder (both `Tendsto (fun m => BoundaryTrunc … m t) atTop (𝓝 (leviSeries … t 0 0))`); supplied via `have hBoundaryLim := hBoundaryLim_DONE …`. No boundary-threaded variant pre-existed. In place of the opaque `hBoundaryLim`, the capstone now carries CONCRETE individually-satisfiable data: hEbound/hInt/hEmeas/hbase (van-Vleck heat-envelope), env/hu/hbound (summable Levi tail), hf_meas, hgeoBundle/hfgBundle (RNC exp-chart geometry, QUADRATIC remainder), gate activation rS/hKball/hSact, hWslice, hDomB, window floor ε₀/hε₀/hε₀t/hεbnd. The existing `dataLevi : LeviSeriesLocalData` is REUSED as hBoundaryLim_DONE's hLocal (NOT a new binder); htT:=hUT t htU + hgdet0:=det(g 0)=1 (from hg0) derived internally. Build ~52s standalone / ~62s AxiomAudit (cheap, monolith fear refuted again).
- **THE GATE (adversarial):** PASSES — genuinely reduces the opaque boundary to curved-valid data, no relabel/no reintroduced flatness. The RNC geometry bundles carry the QUADRATIC remainder `‖exp v − q − v‖ ≤ C_Dw·‖v‖²` with C_Dw FREE (curved-valid; flat only forces C_Dw=0); hEbound/hDomB/hInt are Gaussian envelope bounds valid for the curved van-Vleck witness; the reused dataLevi is the curved Levi-window package; hBoundaryLim_DONE's chain (leviSlice_window_uniform_bound + leviSlice_moving_meas + MovingCorrRecombination.hBoundaryLim_FULLY_INTERNAL) carries the honest firewall, no flatness assumption.
- **Don't-undercredit:** hBoundaryLim_DONE + its (E1)/(E2)/(E3) members + hBoundaryLim_FULLY_INTERNAL all already banked (J4-306/307/517); this = capstone supply wiring + 2 internal derivations (htT, hgdet0).
- **Build:** green; std-3; AxiomAudit green (name-collision clean); import + pin wired by the agent.
- **⚠ HONEST BOTTOM LINE:** this IS a **3-of-3 CURVED-SIGNATURE a₁ capstone** — all three flat-only/pending items (hraw J4-519, hframeK J4-520, hBoundaryLim J4-521) resolved from the signature, which now carries ONLY genuine coefficient-neutral curved-valid labelled inputs. ⚠ IT DOES NOT DERIVE A CURVED a₁ COEFFICIENT — R/6 still lives SOLELY in the untouched transportCoeff/htr, and the capstone still carries the labelled hGauss/hgate/hEdom + the joint-continuity data. A curved-SIGNATURE capstone ≠ a DERIVED curved coefficient. THE GENUINE FRONTIER: (1) iterE positive-time continuity (the one residual analytic input feeding hBoundaryLim_DONE, now SURFACED as concrete hbase/hgeoBundle/hfgBundle continuity data rather than an opaque limit); (2) htr/hGauss geometric bridges (turning the labelled Gaussian/transport data into DERIVED curvature); (3) a full RNC curved WITNESS simultaneously discharging the whole antecedent (J4-512 confMetric inhabits the GAUGE channel only; a global witness of all Section A–L binders is not yet assembled). a₁=R/6 remains CONDITIONAL + effectively flat-only until (1)-(3) close.
- **NEXT J4-522 (agent's rec):** attack frontier (1) — the positive-time continuity of iterE/the Levi convolutions (⚠ `IterEContinuity.lean` ALREADY EXISTS as a partial brick — GREP-FIRST, continue/complete it), discharging the hbase/hgeoBundle joint-continuity carries into a genuine derivation; the last analytic input standing between the curved-signature capstone and a boundary member with no continuity assumption.

### J4-522 — HfgRadiusSelection: the iterE-continuity RADIUS-SELECTION sub-gap closed (+ 5th don't-undercredit: iterE STEP + induction already proven)
- **File:** `QIQTH/HfgRadiusSelection.lean` (std-3, 2 public decls, collision-checked).
- **⚠⚠ AUDIT (grep-first, 5th don't-undercredit win):** `IterEContinuity.lean`'s STEP machinery is FULLY PROVEN (`heatConv_eq_smul_unitInterval`, the σ=s·u change of variables → double `continuousOn_of_dominated`; `heatConv_jointContinuousOn_of_dominated`; `iterE_succ_jointContinuousOn_of_dominated`; the ∀k induction `iterE_jointContinuousOn`). The `hbase`/`hfgBundle` joint-continuity carries are ALREADY DERIVED: base 0 via `ChartComposedHeatOp.heatOpGatedWitness_jointContinuousOn_final` (D6) → `ChartJetFactsDischarge.heatOpGatedWitness_jointContinuousOn_chartFree` (J5); moving base w via `FrozenBaseWChain` (J4-293, `heatOpWitness_fixedBase_active_chartFree` + near/off paste). The EXACT residual was a pure RADIUS-SELECTION gap: local continuity banked only for R<ρc (chart C²-region), but `hfgBundle` needs an existential `Rg` with both `Rg<ρc` AND the geometric floor `b+C_Dw·b²<Rg`.
- **What lands:** `exists_fgRadius_of_local_continuousOn` (from local `ContinuousOn F` on `Icc s₁ s₂ ×ˢ closedBall w R` ∀ 0<R<ρc + the EXPOSED margin `b+C_D·b·b<ρc` + a threaded `Geom : Prop` ⟹ `∃ Rg, 0<Rg ∧ ContinuousOn F (Icc s₁ s₂ ×ˢ closedBall w Rg) ∧ Geom ∧ b+C_D·b·b<Rg` at midpoint `Rg=(max 0 (b+C_D·b·b)+ρc)/2`; pure order arithmetic max_lt/linarith) · `witness_exists_fgRadius` (the concrete restatement at the Levi residual `F = fun p => heatOp g gi (vanVleckGatedWitness …) p.1 p.2 w` = the continuity+margin core of `hfgBundle` at base w).
- **THE GATE:** curved-generic (no g=δ/hframeK; F/geometry fully abstract); time bounded away from 0 (only threads the banked 0<t₁ continuity, no t=0 claim, Icc domain inherited); the margin `b+C_Dw·b²<ρc` is an EXPOSED hypothesis (the genuine near-diagonal condition: cutoff scale fits inside chart C²-region), NEVER hidden — ρc/cw independent of Rg so midpoint selection valid, no vacuity.
- **Sol (gpt-5.6-sol high):** picked A (radius selection) over B (hbase ∀R) / C (R-dom). ⚠ Verdict on B: `hbase`'s R≥ρc tail is NOT derivable from current banks — needs a NEW global off-support/local-zero lemma (pointwise witness=0 insufficient; heatOp differentiates in z ⟹ needs local-zero + strict support-separation from the gate boundary; possibly FALSE if the cutoff support isn't separated). So `hbase ∀R` stays a raw carry until that separate lemma lands.
- **Don't-undercredit:** the whole D1–D6/L1–L3 base-0 chain + ChartJetFactsDischarge + FrozenBaseWChain + the IterEContinuity change-of-variables STEP + induction were all already banked; this file adds ONLY the radius-selection plumbing.
- **Build:** green; std-3 both; AxiomAudit green (9800 jobs, collision-checked); import + 2 pins wired by the agent.
- **⚠ HONEST BOTTOM LINE:** closes the RADIUS-SELECTION sub-gap — the `hfgBundle` continuity carry is now a genuine derivation modulo (i) the banked local continuity (FrozenBaseWChain) + (ii) the exposed near-diagonal margin. Does NOT close: the full hfgBundle (still needs hgeoBundle threaded as Geom + the margin proven at the call site), `hbase`'s ∀R>0 tail (needs the new global off-support lemma, Sol's B, possibly false), or the (R-dom) per-rung Gaussian convolution-integral dominations feeding the iterE INDUCTION STEP. A piece of iterE continuity ≠ derived curved a₁. a₁=R/6 remains CONDITIONAL + effectively flat-only.
- **NEXT J4-523:** either (a) the (R-dom) convolution-integral envelope (integrate the banked pointwise `convStepIntegrand_pointwise_bound_gauss` over w to a u-integrable Ioc 0 1 envelope, discharging the STEP's hbnd_int/hbound), or (b) the `hbase` ∀R global off-support lemma Sol sketched (support-separation + local-zero ⟹ heatOp=0 far, pasted with near) — the harder load-bearing one for the unbounded carry. OR pivot to a DIFFERENT frontier piece (htr/hGauss geometric bridges, or the RNC curved witness).

### J4-523 — CurvedRNCGaussWitness: the FIRST genuine curved RNC Gauss witness + the geometric-bridge map (the exp-map "wall" is NOT a wall for the concrete-metric route)
- **File:** `QIQTH/CurvedRNCGaussWitness.lean` (std-3, 6+ public decls, collision-checked).
- **★★ THE WITNESS:** `curvedRNCMetric K x i j := δ_ij − (K/3)(‖x‖²δ_ij − x_i x_j)` — the FIRST field-level curved inhabitant of hGauss. `metricGaussGauge_curvedRNC`: the EXACT ∀x radial Gauss lemma `∑_j g^K_{ij}(x)x^j = x^i` holds EXACTLY (all orders/K/n — the correction tensor `‖x‖²δ_ij − x_i x_j` annihilates x^j). This is the DEFINING RNC property, NOT a confMetric-lookalike (conformal e^{2φ}δ gives e^{2φ}x_i≠x_i). `hGaussGerm_curvedRNC` = the capstone's labelled hGauss germ for a curved metric. `curvedRNCMetric_ricci_trace`: `∑ₐ ∂c∂d g_aa(0) = −(2/3)(n−1)K δcd` (= the htr datum). `curvedRNCMetric_ricci_trace_diag_ne`: ≠0 for K≠0, n≥2 (the gate) ⟹ Ric(0)=(n−1)Kδ≠0. Plus `_symm`/`_zero`/`_contDiff`/`_trace`/`pd_coord`.
- **GEOMETRIC-BRIDGE MAP:** (a) `htr` FULLY DERIVED from the normal gauge (`RNCExpansion.rnc_htr_of_gauge` from {C^∞, gi(0)=δ, ∂g(0)=0, symm, hgauge=∂_{(a}Γ^i_{bc)}(0)=0}; route `∑_ν ∂_cΓ^ν_{νd}=½tr∂∂g=−⅓Ric`) — RESIDUE = carrying `hgauge` (a falsifiable 2-jet condition), not htr. (b) `hGauss` reduced to `hgball` (`GaussLemmaFlowData.hGauss_pullback:240`, the per-point first-variation Gauss identity on ball 0 (expRho p)) = a GENUINE geodesic residue needing the exp-map endpoint (Mathlib-absent) FOR THE ARBITRARY-METRIC pullback construction — BUT ⚠ an EXPLICIT metric (g^K) satisfies MetricGaussGauge DIRECTLY, bypassing exp-maps entirely.
- **⚠⚠ Sol (gpt-5.6-sol high) — the FALSE-DICHOTOMY correction:** geometric residues do NOT force flatness (g^K closes the geometric slice); the exp-map is only needed for the ARBITRARY-metric theorem. The REAL remaining wall for full non-vacuity is the **~250 coupled ANALYTIC binders** (measurability/Levi-integrability/Gaussian-gate), NOT exp-map infrastructure. Sol's traps: g^K global positivity for K>0 (det g^K=(1−(K/3)‖x‖²)^{n−1}, singular at ‖x‖²=3/K) — use K<0 for global or a neighborhood for either sign; curvature Ric(0)=(n−1)Kδ, Scal=n(n−1)K correct with the repo's sign. Sol: MetricGaussGauge should itself IMPLY hgauge (Γ^i_{jk}x^jx^k=0 + Taylor) — a reusable consolidation lemma, not yet built.
- **THE GATE:** PASSED — genuinely Ric(0)≠0 (`curvedRNCMetric_ricci_trace_diag_ne` proves the metric-Hessian trace =−(2/3)(n−1)K≠0 at the FIELD level via actual pd(pd …), = −(2/3)Ric_{00} by htr ⟹ Ric(0)=(n−1)Kδ≠0); in REAL RNC coordinates (exact radial Gauss lemma), NOT a confMetric-lookalike. Banked model metrics (SphereMetric/HyperbolicPlane/sphDdg/confMetric) were all jet-only or fail hGauss — this is the FIRST field-level curved hGauss inhabitant.
- **Don't-undercredit:** the repo had the flat inhabitant (metricGaussGauge_flat), the full Curvature/RNCExpansion tower, rnc_htr_of_gauge, the exp-map/Gauss stack, hGauss_pullback→hgball; J4-523 built ONLY the missing curved FIELD inhabitant + its field-level curvature certificate (reusing pd_rncRadialSq/rncRadialSq_contDiff/coord_contDiff/metricGaussGauge_imp_hGaussGerm).
- **Build:** green; std-3 all; AxiomAudit green (collision-checked); import + 4 pins wired by the agent.
- **⚠⚠ HONEST BOTTOM LINE — the endgame is REFRAMED (positively):** a NON-VACUOUS DERIVED curved a₁ is NOT blocked by an unclosable exp-map residue — that was the wrong worry. The geometric slice is now INHABITED with genuine curvature (g^K, Ric≠0, exact hGauss). The honest separating gap is **analytic instantiation for a concrete curved metric**: g^K (or Sol's uniformly-elliptic rational variant δ − c/(1+‖x‖²)(‖x‖²δ−xx)) must simultaneously satisfy the ~250-binder measurability/Levi/Gaussian-gate antecedent of `a1_R6_from_labelled_curved_boundary` — none of which g^K yet discharges. `htr` derivable (needs an hgauge supply / the MetricGaussGauge→hgauge lemma); `hGauss` DIRECTLY satisfied by g^K (no exp-map). a₁=R/6 remains CONDITIONAL — the gap is analytic instantiation, NOT Mathlib-absent geometry.
- **NEXT J4-524 (Sol's rec):** build the `MetricGaussGauge g → hgauge g` BRIDGE (g_ij x^j=x_i ⟹ Γ^i_{jk}x^jx^k=0 ⟹ ∂_{(a}Γ)(0)=0) — lets g^K DERIVE both htr AND hGauss from the single exact radial gauge, collapsing frontier (2) to one geometric fact + making g^K a SELF-CONTAINED curved geometric witness. Then begin instantiating the lightest analytic binders (hg0/hinvF/hdg0 pointwise gauge) for g^K toward chipping the ~280-binder antecedent.

### J4-524 — GaussGaugeToHgauge: the MetricGaussGauge→hgauge bridge — g^K is now SELF-CONTAINED on the geometric side
- **File:** `QIQTH/GaussGaugeToHgauge.lean` (std-3, 6 public decls, collision-checked).
- **AUDIT:** `hgauge` (consumed by `RNCExpansion.rnc_htr_of_gauge`) = `∀ i a b c, pd (Γ i b c) a 0 + pd (Γ i c a) b 0 + pd (Γ i a b) c 0 = 0` (totally-symmetrized Christoffel derivative). `christoffel g gi μ ν ρ x := ½ ∑_α gi x μ α (∂_ν g_{αρ}+∂_ρ g_{αν}−∂_α g_{νρ})`. Banked: `RNCExpansion.pd_christoffel_origin` (∂_a Γ^ν_{λμ}(0)=½(∂_a∂_λ g_{νμ}+∂_a∂_μ g_{νλ}−∂_a∂_ν g_{λμ})(0), from gi(0)=δ/∂g(0)=0/smooth), `Curvature.pd_comm` (Schwarz). ⚠ Neither A→B nor B→C was banked (`gauss_coordinate_contraction` does NOT exist); the smallest missing link = the metric-Hessian algebra bridging pd_christoffel_origin → hgauge.
- **What lands:** `GaussHessianCyclic g` (the metric-2nd-deriv gauge `∀ i p q r, ∂_q∂_p g_{ir}(0)+∂_r∂_q g_{ip}(0)+∂_p∂_r g_{iq}(0)=0`) · **`hgauge_of_gaussHessianCyclic`** ★ (THE BRIDGE: pure jet algebra — expand each ∂Γ(0) via pd_christoffel_origin, split the 9 Hessian atoms into a positive block =2·GaussHessianCyclic + a negative block killed by 3 more instances + pd_comm + metric symmetry; linarith) · **`curvedRNCMetric_gaussHessianCyclic`** ★ (g^K satisfies it, K≠0, via `curvedRNCMetric_pd_pd`: ∂_q∂_p g^K_{ir}(0)=−(K/3)(2δ_{ir}δ_{pq}−δ_{ip}δ_{rq}−δ_{rp}δ_{iq}); cyclic sum vanishes by δ-algebra) · **`curvedRNCMetric_hgauge`** ★ (the FIRST curved Ric≠0 inhabitant of the Christoffel gauge, from the bridge + flat inverse δ) · **`curvedRNCMetric_htr_from_gauge`** (htr DERIVED from the gauge via rnc_htr_of_gauge: ∑_a ∂_c∂_d g^K_{aa}(0)=−(2/3)·ricci g^K δ c d 0) · **`curvedRNCMetric_ricci_from_gauge`** (Ric(0)=(n−1)Kδ_{dc} pinned from the gauge).
- **THE GATE:** curved-generic (the bridge assumes only RNC conditions g(0)=δ/∂g(0)=0/symm/smooth, never g=δ); `GaussHessianCyclic` proved for g^K with K≠0 all n; output carries genuine Ric(0)=(n−1)Kδ≠0 (K≠0, n≥2). NOT secretly flat.
- **Sol:** NOT consulted (honest deviation) — the route (A→B→C reduces to metric-Hessian algebra; pd_christoffel_origin already banks the ∂Γ(0)→∂∂g step) was clear from the audit + validated by compilation; no new geometric lemma needed (pure Finset/Schwarz algebra).
- **Don't-undercredit:** pd_christoffel_origin/pd_comm/curvedRNCMetric_ricci_trace + the whole Curvature/RNCExpansion pd tower already banked, reused; the witness + its exact radial gauge were J4-523.
- **Build:** green; std-3 all; AxiomAudit green (9802 jobs, collision-checked); import + 5 pins wired by the agent.
- **⚠ HONEST BOTTOM LINE:** g^K is now SELF-CONTAINED on the geometric side — `hgauge` (previously only CARRIED, never proved for a curved metric) is DISCHARGED for g^K, and its htr/Ricci are DERIVED from that gauge. Both geometric bridges (hGauss from J4-523's exact radial gauge; htr from hgauge here) hold for the SAME genuinely-curved witness. ⚠ CAVEAT (no overstatement): this is the ∂∂g→hgauge (curvature-side) HALF. g^K's GaussHessianCyclic is proved by a DIRECT 2nd-derivative computation, NOT yet from MetricGaussGauge itself; the `MetricGaussGauge g → GaussHessianCyclic g` link (triple-differentiating the radial gauge — a heavy 3-factor Leibniz on ∑_j g_{ij}x^j) is SCOPED, not built. And the ~250-binder ANALYTIC instantiation for g^K remains the separating gap. NOT a₁=R/6 (conditional + effectively flat-only).
- **NEXT J4-525:** either (a) the `MetricGaussGauge → GaussHessianCyclic` link (triple-diff of ∑_j g_{ij}(x)x^j=x^i at 0 — closes the geometric chain fully from the single radial gauge), or (b) begin instantiating the LIGHTEST analytic binders (hg0: g^K(0)=δ [curvedRNCMetric_zero banked]; hinvF: g^K·gi=1 at 0; hdg0: ∂g^K(0)=0) for g^K — the analytic side is the TRUE frontier (the ~250-binder measurability/Levi/Gaussian-gate campaign).

### J4-525 — CurvedRNCGaugeBundle: the g^K inverse-metric gauge bundle + the ANALYTIC-BINDER AUDIT (the endgame's honest shape)
- **File:** `QIQTH/CurvedRNCGaugeBundle.lean` (std-3, 5+ public decls, collision-checked). Closes the inverse-metric quadrant of g^K's geometric-gauge half.
- **(A) What lands:** `curvedRNCInv K x i j := (1/(1−(K/3)‖x‖²))·(δ_ij − (K/3)x_i x_j)` (the TRUE Sherman–Morrison inverse) · `curvedRNCInv_zero` (`hgi`: gi(0)=δ) · `curvedRNCInv_contDiff (hK:K≤0)` (`hgiC`: denominator α≥1 never vanishes for K≤0, ContDiff.inv) · **`curvedRNCMetric_hinvF (hK:K≤0)`** (★ the crux: `∑_σ g^K(y) c σ · gi^K(y) σ d = δ` ∀y, via the exact radial Gauss lemma `metricGaussGauge_curvedRNC`) · `curvedRNCMetric_christoffel_zero` (`hΓ`: Γ(0)=0 from ∂g(0)=0) · **`curvedRNC_geomGaugeBundle (hK:K<0)`** (the packaged 9-way conjunction `hg∧hgsymm∧hgiC∧hg0∧hgi∧hΓ∧hdg0∧hGauss∧hinvF`, g:=curvedRNCMetric K, gi:=curvedRNCInv K). NEW = the 4 gi-dependent members (hinvF/hgi/hgiC/hΓ); hinvF the load-bearing novelty. Banked+reused: hg/hgsymm/hg0/hdg0/hGauss (J4-523/524).
- **THE GATE:** genuinely curved — the bundle requires K<0 (keeps Ric(0)=(n−1)Kδ≠0, n≥2). ⚠ `hinvF` handled ∀y (GLOBAL), NOT secretly flat: flat δ EXPLICITLY REJECTED (forces g(y)=δ); `curvedRNCInv` is the TRUE inverse; holds ∀ Point n because K<0 ⟹ α=1−(K/3)‖x‖²≥1>0 never vanishes. Sol confirmed: flat δ genuinely fails hinvF for curved g^K; the true Sherman–Morrison inverse is required; K<0 is the clean GLOBAL move (K>0 ⟹ α=0 on ‖x‖²=3/K, no global inverse). Sol's ‖x‖ sup-vs-Euclidean trap NOT an issue (the Lean def uses rncRadialSq=∑x_i²).
- **⚠⚠ (B) THE ANALYTIC-BINDER AUDIT — the endgame's HONEST SHAPE:** the capstone (`A1R6FromLabelledCurvedBoundary`) has ~130 surface binders (~250 with structures unfolded). Minus the geometric-gauge bundle: **(i) ~40–50 TRIVIAL-for-any-smooth-metric** (Section-A data/window params, window floors, support facts hFzero/hAzero, gate-membership/openness bookkeeping) — g^K being a C^∞ polynomial metric makes these routine. **(ii) ~30–40 GENUINE CURVED HEAT-KERNEL ESTIMATES (the bulk of the difficulty, THE REAL WALL):** ALL the Gaussian dominations (hpkgBound/hAdomHeat/hAdom2/hEdom/hFdom/hAdom/hEbound/hgate — the width-4/3 curved-kernel gate on the ACTUAL heatOp), the Levi machinery (dataLevi/hInt/env-hu-hbound summable envelope), mass normalization (hmass/hmassone), moduli (hmod/hsup), cross-Lipschitz, √ε boundary (D0/D1/hbnd), dataAmp, convergence (hPd2conv/hbulk_tendsto), diff-under-∫ dominations — each a real parametrix/Aronson-style estimate. **(~40 middle) measurability-contingent** (AEStronglyMeasurable/Integrable/ContinuousOn — cheap ONCE kernel continuity is known, + the exp-chart quadratic-remainder bundles hgeoBundle/hfgBundle).
- **Sol:** ~½+ of the proof burden is genuine heat-kernel estimates, ~⅓ cheap bookkeeping, ~¼ local geometry/measurability. ⚠ The K<0 metric's tangential eigenvalue grows like r² (non-uniformly-elliptic GLOBALLY) ⟹ global Euclidean Gaussian bounds need LOCAL COMPACT-STRIP LOCALIZATION.
- **Build:** green; std-3 all; AxiomAudit green (collision-checked); import + 5 pins wired.
- **⚠⚠ HONEST BOTTOM LINE:** the GEOMETRIC-GAUGE HALF is now essentially fully provable for g^K (the 9-member bundle std-3; the ~40–50 type-(i) trivial binders routine). ⚠ BUT a NON-VACUOUS DERIVED curved a₁ is NOT a bounded pile of cheap bricks — it is gated behind the GENUINE CURVED HEAT-KERNEL ESTIMATE WALL: ~30–40 type-(ii) surface binders (the Gaussian dominations of the actual curved heatOp + the Levi machinery + mass/moduli), each a real parametrix estimate, PLUS the non-uniform-ellipticity localization subtlety. One remaining geometric member `hgpos` (det g^K=α^{n−1}>0) is deferred (clean via Matrix.PosDef.det_pos + Cauchy–Schwarz wᵀg^K w≥‖w‖²). a₁=R/6 remains CONDITIONAL + effectively flat-only — the geometric-gauge half is charted+packaged; the coefficient is NOT derived; the curved heat-kernel Gaussian dominations are the real wall (NOT a short brick count).
- **NEXT J4-526:** (a) close `hgpos` for g^K (finishes the geometric-gauge half completely, bounded ~1 file via PosDef/Cauchy–Schwarz) FIRST, then (b) attack the next-lightest genuine-analytic binder `hWslice`/`hWmeas` (base-witness AEStronglyMeasurable — concerns the EXPLICIT gated van-Vleck ansatz smooth×Gaussian×cutoff, NOT the solved kernel/Levi series, so it AVOIDS the parametrix wall). ⚠ hgate bounds the ACTUAL heatOp (a wall), NOT light — Sol's hgate nomination was wrong on lightness.

## J4-526 — hgpos for curved witness g^K (geometric-gauge half COMPLETE) [9d11b74a]
CurvedRNCPosDef.lean (new, std-3, budget raw 0 / 9804 jobs). Closes the LAST
geometric-gauge binder hgpos of the curved capstone antecedent for g^K.
- curvedRNCMetric_quadForm: wᵀg^K(x)w = ‖w‖²+(K/3)(⟨x,w⟩²−‖x‖²‖w‖²) exactly.
- curvedRNCMetric_isHermitian; curvedRNCMetric_posDef (K≤0, via Cauchy–Schwarz
  Finset.sum_mul_sq_le_sq_mul_sq + rncRadialSq_pos); curvedRNCMetric_det_pos
  (PosDef.det_pos); curvedRNCMetric_hgpos : ∀v, 0<det(curvedRNCMetric K v).
- Binder-exact for A1R6FromLabelledCurvedBoundary.a1_R6_from_labelled_curved_boundary
  hgpos. det = α^{n−1}, α=1−(K/3)‖x‖²≥1.
- Satisfiability GATE PASSED: K<0 satisfies hgpos(K≤0) ∧ geomGaugeBundle(K<0) ∧
  Ric(0)=(n−1)Kδ≠0 — genuinely curved, not secretly flat.
- Geometric-gauge half now COMPLETE for g^K: hg/hgsymm/hgiC/hgpos/hg0/hgi/hΓ/
  hdg0/hGauss/hinvF all discharged.
HONEST: a₁=R/6 CONDITIONAL + effectively FLAT-ONLY. Completing the geometric half
≠ deriving the coefficient. Remaining wall = ~30-40 curved heat-kernel Gaussian
dominations (heatOp/Levi: hpkgBound/hAdomHeat/hAdom2/hDomB/dataLevi). Type-(iii)
measurability (hWmeas/hWslice) curvature-independent, reduces via banked generic
lemma vanVleckGatedWitness_slice_aestronglyMeasurable → heatParametrix_uncurry_
measurable_from_geometry. J4-527 = instantiate hWmeas/hWslice for g^K.

## J4-527 — hWmeas/hWslice for curved witness g^K (type-iii measurability) [e3f9f1e1]
CurvedRNCWitnessMeas.lean (new, std-3, budget raw 0 / 9805 jobs). Instantiates the
two curvature-INDEPENDENT measurability binders of the curved capstone for
g^K = curvedRNCMetric K (K<0).
- curvedRNC_hIn_from_geometry: inner order-1 parametrix slice, discharged from
  {curvedRNCMetric_contDiff, curvedRNCInv_contDiff, curvedRNCMetric_hgpos} via
  HuInftyRebase.vanVleck_witnessInner_continuous_ofGeom at C^∞ (never analytic hw)
  + Continuous.comp_aestronglyMeasurable.
- curvedRNC_hWmeas / curvedRNC_hWslice: EXACT hWmeas/hWslice binders (∀τ
  AEStronglyMeasurable of vanVleckGatedWitness for g^K) via banked
  WitnessMeasDeriv.vanVleckGatedWitness_slice_aestronglyMeasurable; MeasurableSet K
  from compactGate_measurableSet.
- Residual carries reduced to two strictly-lighter curvature-independent bookkeeping
  facts: hSm (gate-set preimage measurable), hVmap (base-chart pullback z-ae-meas).
- GATE: K=-1, n≥2 — Ric(0)=(n−1)Kδ≠0 genuinely curved, det g^K>0, non-vacuous.
HONEST: a₁=R/6 CONDITIONAL + effectively FLAT-ONLY. hWmeas/hWslice = type-(iii)
curvature-independent bookkeeping; closing them ≠ deriving the coefficient. Remaining
wall = ~30-40 curved heat-kernel Gaussian dominations (heatOp/Levi), untouched.
J4-528 = discharge hSm + hVmap for g^K (curvature-independent) to make hWmeas
self-contained, OR the FIRST genuine curved Gaussian domination (the crux wall).

## J4-528 — self-contained hWmeas/hWslice for g^K (hSm+hw discharged, hVmap lightened) [97e9ca4d]
CurvedRNCWitnessMeasSC.lean (new, std-3, budget raw 0 / 9806 jobs). Strict reduction
of J4-527's carry surface {hSm(raw), hVmap(full,∀p)} → {hVmapK(restrict,p=0)} + reach
c<δ₀, for g^K = curvedRNCMetric K (K<0).
- gatedKernel_slice_aemeas_ofRestricted_Kguard: reusable K-guard lever — full-volume
  gated slice = (K∩{0∈S}).indicator ⟹ only the K-RESTRICTED gate graph needed
  (banked Lusin–Souslin), never raw off-K set.
- curvedRNC_hWmeas_sc / curvedRNC_hWslice_sc: ∃δ₀>0, ∀c∈(0,δ₀), ∀τ,
  AEStronglyMeasurable of the g^K witness slice — ZERO hSm carry, NO hw carry.
  hSm via ConcreteGateInstantiation.hKSmeas_concrete → B2MeasurabilityDissolution.
  hSmeasSet_Krestricted (p=0); hw via HuInftyRebase.vanVleck_witnessInner_continuous_
  ofGeom fed the C^∞ curved bundle {contDiff g, contDiff gi, hgpos} (⊤/analytic
  unavailable for g^K).
- SOLE remaining carry = hVmapK (single-point p=0, volume.restrict Kset) = the genuine
  curved geometric residue (origin-chart reach exp^{g^K}_z(W_z 0)=0 over Kset), NOT
  bookkeeping. FoldedCoeffChartMeas.hVmapMeasK_zero_of_geom.
- GATE: K<0, Kset∋0, 0<c<δ₀ — Ric(0)=(n−1)Kδ≠0 genuinely curved, det g^K>0, δ₀>0
  range nonempty. Non-vacuous.
HONEST: a₁=R/6 CONDITIONAL + effectively FLAT-ONLY. hSm/hw/hVmap = type-(iii)
curvature-independent (or single-point geometric) measurability bookkeeping; ≠ deriving
the coefficient. Remaining wall = ~30-40 curved heat-kernel Gaussian dominations
(heatOp/Levi), untouched. J4-529 = discharge hVmapK (curved origin-chart reach
exp^{g^K}_z(W_z 0)=0 over Kset via Cartan–Hadamard K<0 globality) → fully carry-free
witness measurability, OR the FIRST genuine curved Gaussian domination (crux wall).

## J4-529 — hVmapK discharged, g^K witness measurability CARRY-FREE [70f467e3]
CurvedRNCChartReach.lean (new, std-3, budget raw 0 / 9807 jobs). Closes the last
measurability carry hVmapK for g^K = curvedRNCMetric K (K<0), leaving only an explicit
geometric reach input.
- hVmapMeasK_zero_of_reach: the three origin side-conditions {hball,hnorm,hRI} of
  FoldedCoeffChartMeas.hVmapMeasK_zero_of_geom collapse to a SINGLE reach input
  ∀z∈K, ∃v, ‖v‖<ρ ∧ exp_z v=0 (banked left-inverse germ uniformInverseChart_
  huniformChart gives W z 0 = v; hRI/hnorm/hball follow, ρ = min of 3 radii).
- curvedRNC_hVmapK_of_reach: the g^K instance = exactly the hVmapK carry.
- curvedRNC_hWmeas_carryFree / curvedRNC_hWslice_carryFree: witness-measurability
  capstone with ZERO measurability carries (∃ρ>0, (reach over Kset) → ∃δ₀>0,
  ∀c∈(0,δ₀), ∀τ AEStronglyMeasurable of the g^K witness slice).
- HONEST residual: the reach is the K-uniform injectivity-radius reachability that
  ExpRhoReachability (J4-485) audited GENUINE-INPUT — substrate exp/expRho are
  arbitrary Classical.choose witnesses (no LSC), so g^K Cartan–Hadamard globality
  is NOT exposed; reach carried, not banked. A GEOMETRY input, not measurability.
- GATE: K<0, n≥2, Kset∋0 — Ric(0)=(n−1)Kδ≠0 curved; reach ∀z∈Kset (uniform ρ over
  compact Kset), no flat/single-point collapse. Non-vacuous.
HONEST: a₁=R/6 CONDITIONAL + effectively FLAT-ONLY. Last curved-geometry measurability
carry closed; ≠ deriving the coefficient. Remaining wall = ~30-40 curved heat-kernel
Gaussian dominations (heatOp/Levi), UNTOUCHED. ★ Witness-measurability track now DONE
(modulo geometric reach). J4-530 = the FIRST genuine curved Gaussian domination (THE
CRUX WALL — e.g. |heatOp g^K τ p q|≤C·gaussDdim(cτ)(p−q), consumed by hEboundFull/
hEdom/hBdom), OR bank a K<0 Cartan–Hadamard reachability lemma (multi-session).

## J4-530 — bounded van-Vleck amplitude factor for curved witness g^K (PARTIAL) [b6a07b91]
CurvedRNCVanVleckBound.lean (new, std-3, budget raw 0 / 9808 jobs). The AMPLITUDE FACTOR
of the FIRST base-witness Gaussian domination, for g^K = curvedRNCMetric K (K≤0).
⚠ AGENT MALFUNCTIONED (repeated non-report 'waiting for build' completions, stopped via
TaskStop); the file's FINAL state (mtime 17:34) is CLEAN — an earlier snapshot showed
sorryAx (mid-edit), but the definitive rebuild confirmed all 5 decls std-3, no sorryAx.
Main verified + banked directly (agent had correctly wired import+pins before dying).
- curvedRNCMetric_det: EXACT van-Vleck det g^K(w)=(1−(K/3)‖w‖²)^(n−1) via rank-one
  Matrix.det_one_add_replicateCol_mul_replicateRow (g^K=α·(1+vecMulVec((K/3/α)w)w),
  α=1−(K/3)‖w‖², α+(K/3)‖w‖²=1).
- curvedRNCMetric_alpha_ge_one/_det_ge_one/_det_le: two-sided det control K≤0
  (1≤det g^K(w)≤(1−(K/3)M)^(n−1) on ‖w‖²≤M) — raw material for Θ^{±1/2}=det^{1/4}.
- curvedRNCMetric_vanVleck_pos/_vanVleck_le_one: bounded factor 0<vanVleck g^K(w)≤1
  for K≤0 (Θ∈(0,1]) — the amplitude input the domination consumes.
HONEST SCOPE: closes ONLY the van-Vleck AMPLITUDE factor Θ∈(0,1]; does NOT close the
full base-witness domination — the Gaussian-PHASE transfer gaussDdim τ(Vmap z 0)≤
C·gaussDdim(λτ)z is an IRREDUCIBLE geometric reach input (not from DV(0)=I, not
cheatable on a compact gate). Only the FIRST of ~30-40 curved heat-kernel Gaussian
dominations. GATE: K<0 genuinely curved (Ric(0)=(n−1)Kδ≠0), det≢1 — not flat kernel.
Non-vacuous. a₁=R/6 CONDITIONAL + effectively FLAT-ONLY — one amplitude factor ≠ the
coefficient. J4-531 = the Gaussian-PHASE transfer (genuinely-geometric core of the
base-witness domination — hard, may need reach input) OR next amplitude/moduli binder.

## J4-531 — full base-witness Gaussian domination #1 for g^K (modulo carried phase+moduli) [8343d8cb]
CurvedRNCBaseWitnessDom.lean (new, std-3, budget raw 0 / 9809 jobs; verified clean via
independent rebuild reading #print axioms — no sorryAx). Assembles the FIRST base-witness
domination |vanVleckGatedWitness g^K … τ 0 z| ≤ C_W·gaussDdim(λτ)z, g^K=curvedRNCMetric K
(K≤0), every ELEMENTARY factor discharged, only 2 geometric factors carried.
- sqrt_inv_rpow_half: ((√d)⁻¹)^(−1/2)=d^(1/4).
- curvedRNCMetric_cutoff_amp_le: radialCutoff a b w·(vanVleck g^K w)^(−1/2) ≤
  ((1−(K/3)b²)^(n−1))^(1/4) — amplitude (J4-530 det bounds) + cutoff∈[0,1].
- curvedRNC_baseWitness_dom: the full domination, C_W=C_amp·C_u·C_φ.
DISCHARGED: amplitude det^(1/4)≤C_amp, radial cutoff≤1. CARRIED (explicit satisfiable):
hMod (|∑ₖuₖ(w)τᵏ|≤C_u; u₀≡1, u₁ smooth on compact gate) + hPhase (gaussDdim τ w ≤
C_φ·gaussDdim(λτ)z, irreducible Gaussian-phase transfer = near-isometry ‖W z 0‖≈‖z‖).
GATE: K<0 curved (Ric(0)=(n−1)Kδ≠0, det≢1), C_amp finite, hMod/hPhase satisfiable-not-
contradictory (hPhase genuine near-isometry NOT vacuous ∀). Non-vacuous. Sol confirmed the
rpow amplitude chain + that det bounds do NOT prove hMod/hPhase (correctly carried), no
K<0 soundness trap. HONEST: a₁=R/6 CONDITIONAL + effectively FLAT-ONLY — domination #1
modulo carried inputs ≠ the coefficient; 1 of ~30-40 heat-kernel dominations.
J4-532 = discharge the MODULI carry hMod for g^K (u₀≡1 + u₁=radialTransportSolve bound on
compact chart-image ⟹ leaves ONLY phase carried) OR begin the phase-transfer via banked
chartW0_rncRadialSq_error near-isometry squeeze.
⚠ J4-530 agent malfunctioned (reporting-loop); verify final on-disk file by clean rebuild
reading #print axioms (sorryAx invisible to text-grep).

## J4-532 — transport-coefficient moduli bound hMod for g^K (domination #1 modulo only phase) [4ab2c792]
CurvedRNCModuliBound.lean (new, std-3, budget raw 0 / 9810 jobs; verified clean by rebuild
reading #print axioms — no sorryAx). Discharges the moduli carry hMod of
curvedRNC_baseWitness_dom for g^K=curvedRNCMetric K (K<0).
curvedRNC_moduli_bound: ∃Cu>0, ∀w∈Wset(compact),∀τ∈[0,τmax], |∑_{k∈range 2}
transportCoeff(transportOp(vanVleck g^K)g^K gi^K)k w·τ^k|≤Cu, Cu=1+|M|·|τmax|. Summand
byte-for-byte the hMod body.
- u₀≡1 via transportCoeff_zero (definitional).
- |u₁|≤M: u₁=transportCoeff T 1 continuous — transportOp(vanVleck g^K)g^K gi^K(fun _↦1)
  is C^∞ (TransportOpSmoothness.transportOp_preserves_contDiff ← curvedRNCMetric_contDiff/
  curvedRNCInv_contDiff/hgpos), ray-integral solve C¹ (radialTransportSolve_contDiff_one)
  ⟹ continuous; IsCompact.exists_bound_of_continuousOn gives M. triangle+mul_le_mul.
HONEST SCOPE: discharges hMod POINTWISE for the reachable (gated) z whose chart-image lands
in compact Wset = the vanVleckGatedWitness support ⟹ domination #1 modulo ONLY hPhase. Does
NOT satisfy the literal unguarded ∀z binder (needs a global range bound on the .choose
uniformInverseChart = pre-catalogued far-reach obstruction in GeomPTransportAssess Part A,
NOT a new gap; agent correctly declined a vacuous ∀z∈Wset corollary — vacuity trap avoided).
GATE: K<0 curved (Ric(0)=(n−1)Kδ≠0), Cu≥1>0 finite, Wset inhabited (closedBall 0 1∋0),
non-vacuous. HONEST: a₁=R/6 CONDITIONAL + effectively FLAT-ONLY — hMod discharged leaves
domination #1 modulo only the phase transfer; 1 of ~30-40; ≠ deriving the coefficient.
J4-533 = the phase-transfer hPhase itself (gaussDdim τ w≤C_φ·gaussDdim(λτ)z for g^K, THE
irreducible geometric reach crux + last carried factor, via banked chartW0_rncRadialSq_error
two-sided near-isometry squeeze) OR domination #2.

## J4-533 — Gaussian-phase transfer hPhase for g^K, base-witness domination #1 complete on reach collar [7bdc2a81]
CurvedRNCPhaseTransfer.lean (2 std-3, budget raw 0 / 9811 jobs; verified clean by rebuild
reading #print axioms — no sorryAx). Discharges the LAST carried factor hPhase of
curvedRNC_baseWitness_dom for g^K=curvedRNCMetric K (K<0), on the reachable collar.
curvedRNC_phase_transfer: ∃r>0,∃Cφ>0,∃lam>0, ∀z∈Kset, ‖z‖<r, ∀τ∈(0,τmax],
gaussDdim τ(uniformInverseChart g^K gi^K hChr hKset z 0) ≤ Cφ·gaussDdim(lam·τ)z, EXPLICIT
Cφ=(√2)ⁿ, lam=2 — binder byte-for-byte the hPhase binder.
- PHASE TRAP handled by the EXACT banked squeeze (NOT DW(0)=I): two-sided near-isometry
  chartW0_rncRadialSq_error → chartW0_radialSq_half_lower gives (1/2)rncRadialSq z ≤
  rncRadialSq(W₀z), fed to exp-free gaussDdim_le_of_norm_ge (near-isometry ⟹ widened
  Gaussian), prefactor bookkept exactly ((√(1/2))⁻ⁿ=(√2)ⁿ). Exp-free route chosen to avoid
  brittle exp-arg matching.
- curvedRNC_phase_transfer_satisfiable: curved-not-flat inhabitation (W z=(4/5)z, c=4/5≠±1)
  — genuine radial contraction, NOT secretly flat W₀z=z.
GATE: K<0 curved (Ric(0)=(n−1)Kδ≠0), residual reach window ‖z‖<r (r>0, Kset∋0) inhabited-
not-vacuous, Cφ/lam finite. HONEST: a₁=R/6 CONDITIONAL + effectively FLAT-ONLY — completes
base-witness domination #1 of ~30-40 (modulo reach collar); full a₁ needs the whole heatOp/
Levi pile + Duhamel assembly; ≠ deriving the coefficient.
★ ALL 4 factors of base-witness domination #1 now closed for g^K: amplitude (J4-530) +
cutoff (J4-531) + moduli hMod (J4-532) + phase hPhase (J4-533). Domination #1 = COMPLETE on
the gated reach collar.
J4-534 = base-witness domination #2 (N=2 parametrix term, Finset.range 3) OR discharge the
reach-collar residual (collar = the trace domain the heatOp assembly integrates over) OR
begin the heatOp/Levi domination pile (per agent rec).

## J4-534 — base-witness domination #1 fully discharged on the reach collar (hDomB/hWDom shape) [547d768e]
CurvedRNCBaseWitnessDomCollar.lean (2 std-3, budget raw 0 / 9812 jobs; verified clean by
rebuild reading #print axioms — no sorryAx). Assembles domination #1 for g^K=curvedRNCMetric K
(K<0) with ZERO abstract carried hypotheses — strictly lighter than J4-531 (carried hMod+hPhase).
curvedRNC_baseWitness_dom_collar: ∃r>0,∃CW>0,∃lam>0, ∀z∈Kset, ‖z‖<r, ∀τ∈(0,τmax],
|vanVleckGatedWitness g^K gi^K hChr hKset S a b τ 0 z| ≤ CW·gaussDdim(lam·τ)z,
CW=((1−(K/3)b²)^(n−1))^(1/4)·Cu·Cφ = EXACTLY the hDomB/hWDom amplitude-witness binder shape.
All 4 factors DISCHARGED inline (no carried analytic hyp): amplitude+cutoff (curvedRNCMetric_
cutoff_amp_le), transport moduli (curvedRNC_moduli_bound over closedBall 0 ρ, chart image
w=uniformInverseChart…z 0 PROVEN contained ‖w‖≤ρ=√(2n r²) from UPPER near-isometry
chartW0_rncRadialSq_error rncRadialSq w≤2 rncRadialSq z), phase (curvedRNC_phase_transfer).
SOLE residual = reach collar ‖z‖<r. curved-not-flat gate via c=4/5≠±1 witness. GATE: K<0
curved (Ric≠0), CW>0 finite, collar inhabited. HONEST: a₁=R/6 CONDITIONAL + effectively
FLAT-ONLY — domination #1 of ~30-40 fully discharged (only reach collar residual); full a₁
needs heatOp/Levi/error pile + Duhamel assembly + coefficient extraction; ≠ the coefficient.
SURVEY: capstone remaining domination binders = hpkgBound/hAdomHeat/hAdom2/hEdom/hFdom (heatOp/
Levi §H), hAdom/hWDom/hDomB (amplitude §I/J/L — hDomB now DISCHARGED), hEbound/hInt (Levi-
convergence §L, genuine G1/G2/G3 local/width/two-point gap = heavy).
J4-535 = recenter to base-point-varying hAdom (∀p q τ, |witness … τ p q|≤(A₀+A₁τ)√(3/2)ⁿ·
gaussDdim(3/2 τ)(p−q) via banked recenter machinery) OR the heatOp defect-kernel hAdomHeat
(witness Laplacian, one lower τ-power, reuse this collar Gaussian).

## J4-535 — base-point-varying hAdom/hWDom recenter for g^K (discharges the capstone binder pair) [9c918610]
CurvedRNCBaseWitnessDomAdom.lean (2 std-3, budget raw 0 / 9813 jobs; verified clean by rebuild
reading #print axioms — no sorryAx). Lifts base-witness domination #1 to the base-point-varying
form the capstone trace integral consumes, g^K=curvedRNCMetric K (K<0).
curvedRNC_baseWitness_dom_adom: given hChr, hKset(compact), 0<a<b, τ0fr>0, carried amplitude-
smoothness hw (∀k ContDiff ℝ ⊤ (foldedCoeff …)), produces ∃A₀ A₁≥0,∃c>0,∃CW lam, BOTH capstone
hAdom (∀τ>0,∀p q, |vanVleckGatedWitness … (constGate … c) … τ p q|≤(A₀+A₁τ)·√(3/2)ⁿ·
gaussDdim((3/2)τ)(p−q)) AND hWDom (∀τ∈(0,τ0fr],∀z, |… τ 0 z|≤CW·gaussDdim(lam·τ)z).
- Banked recenter: ConcreteDominations.exists_D1_constants_of_gateSqControl. vanVleckGatedWitness
  unfolds DEFINITIONALLY (ConvApproximants) to the gated cutoff parametrix ⟹ its D1 conclusion IS
  the hAdom binder for g^K (uniform-flow machinery inherently base-point-varying, no p=0 recenter
  needed). hWDom = frozen p=0 window slice (WidthAdapters.gaussDdim_neg).
- GateSqControl fully discharged: gateSqControl_of_flowBall ← uniformFlowExp_hdisp_ball UNIFORM-
  over-Kset near-isometry + uniformInverseChart_huniformChart chart-inverse germ; c=min r₁(δ₀/2)>0.
- CARRIED (sole residual): amplitude smoothness hw = mainline-standard van-Vleck-coeff regularity
  carried ∀k throughout the codebase (never derived for concrete coeffs), consistent NOT a new gap.
curved-not-flat: c=4/5≠±1 radial contraction. GATE: K<0 (Ric≠0), c/lam=3/2/CW finite, gate
nonempty, hw satisfiable (C^∞). HONEST: a₁=R/6 CONDITIONAL + effectively FLAT-ONLY — discharges
one capstone binder pair (hAdom+hWDom); ≠ the coefficient; heatOp/Levi pile + Duhamel + extraction
remain. J4-536 = heatOp defect-kernel hAdomHeat (|heatOp g^K witness τ 0 z|≤CA·gaussDdim(wA·τ)
(0−z), witness Laplacian one lower τ-power) OR D2 Levi-series bound (|leviSeries (heatOp g gi H_G)
τ p q|≤C_L(T)·baseKernelW 2 0 on (0,T], one-step input hEboundW_le landed) per J4-535 rec.

## J4-536 — heatOp defect-kernel dominations hpkgBound + hAdomHeat for g^K (bypasses Levi gap) [392f30bc]
CurvedRNCHeatOpDomPkg.lean (2 std-3, budget raw 0 / 9814 jobs; verified clean by rebuild
reading #print axioms — no sorryAx). Closes TWO capstone heatOp defect-kernel domination
binders at one gate for g^K=curvedRNCMetric K (K<0), bypassing the hEbound G1/G2/G3 Levi
gap.
curvedRNC_heatOp_dom_pkg: ∃a b C c, 0<a∧a<b∧0≤C∧b<c ∧
  (∀t' τ p q, 0<τ→τ≤t'→ |heatOp g^K gi^K (vanVleckGatedWitness … (constGate … c)a b)τ p q|
    ≤ (C·(1+t'))·baseKernelW 2 0 τ p q)  [hpkgBound §C]
  ∧ (∀τ, 0<τ→τ≤T→ ∀z, |heatOp … τ 0 z|≤(C·(1+T))·gaussDdim(2τ)(0−z))  [hAdomHeat §G].
ROUTE: ConstRadiusGateExport.gatedWitnessN1_hEboundW_le_lin_CONST already gives the CONCRETE
constGate width-2 defect bound in the hpkgBound shape (never instantiated for the curved
metric via the coefficient route — flat _vanVleck_final used the ∃-gate _lin); coefficient
inputs discharge as in _vanVleck_final; gives width-2 DIRECTLY, BYPASSING the hEbound G1/G2/G3
trichotomy. hAdomHeat = p=0 slice for free. CLOSED: hgnd (curvedRNCMetric_det_pos+
isUnit_matToCLM_iff), both amplitude-coeff bounds (hCoeffU0_vanVleck+uniformCoeffLinear_bound),
all gauge/frame (banked curved bundle; hframeK on {0}), the width-2 defect. CARRIED: only
mainline-standard hChr (C^∞) + hw (all-k folded smoothness). hEbound gap NOT touched. GATE:
K<0 curved (Ric(0)=(n−1)Kδ≠0, n≥2), Kset={0} restricts only frame-δ base points (metric curved
everywhere), K<0=global-inverse range α≥1. Non-vacuous. HONEST: a₁=R/6 CONDITIONAL + FLAT-ONLY
— 2 heatOp dominations closed; ≠ the coefficient; hAdom2/hEdom/hFdom/hgate + hEbound/hInt Levi
convergence + Duhamel + extraction remain. J4-537 = hAdom2 (2nd-spatial-deriv amplitude Gaussian
|witnessSecondXDeriv … i τ z|≤CA2·gaussDdim(wA2·τ)(0−z), geometric-route sibling of hAdom J4-535,
light). ⚠ AVOID hFdom/hEbound (G1/G2/G3 gap); hEdom width-3/2<2 is NOT a trivial re-slice of the
width-2 hpkgBound (hard Gaussian-width direction).

## J4-537 — honest τ⁻¹ 2nd-deriv envelope for g^K; ★ clean hAdom2 is FALSE for the curved witness [03a43aa6]
CurvedRNCHeatOpDom2.lean (2 std-3, budget raw 0 / 9815 jobs; verified clean by rebuild
reading #print axioms — no sorryAx). ★★ CRITICAL FINDING: the clean single-constant hAdom2
binder consumed by a1_R6_from_labelled_curved_boundary (|witnessSecondXDeriv …|≤CA2·
gaussDdim(wA2·τ)(0−z)) is GENUINELY FALSE at the concrete van-Vleck witness — the true
envelope carries a τ⁻¹ prefactor blowing up as τ→0 (at z=0 ~τ^(−1−n/2) vs demanded ~τ^(−n/2));
documented in the codebase's own CensusDominations D3 / CappedAdom2Audit; Sol confirmed.
Building the clean binder would be UNSOUND ⟹ the curved-boundary capstone is only flat/
degenerate-satisfiable AT hAdom2; the SOUND route uses the per-m capped hAdom2cap (census)
which consumes the τ⁻¹ form.
This brick delivers the HONEST τ⁻¹ envelope:
- curvedGate: g^K FixedFlowGateData discharged from hChr via InverseChartNormalJets.
  FixedFlowGateData.of_geometry.
- curvedRNC_witnessSecondXDeriv_dom_crude: ∃C>0, ∀τ∈(0,τ₀],∀z∈Kset,‖z‖<r,
  |witnessSecondXDeriv g^K … i τ z|≤C·τ⁻¹·gaussDdim(lam·τ)z, via banked
  WideWitnessAmplitude.WideAmplitudeData.second_domination.
- ..._curved_satisfiable: c=4/5≠±1.
CLOSED: gate geometry (of_geometry from hChr+hKset). CARRIED: hAmp0 (amplitude sup) +
hSecondEnv (chart-image two-term second-jet envelope). ⚠ hSecondEnv is a GENUINE ADDITIONAL
2nd-jet geometric carry (moment-aware three-term normal form, CensusDominations D3) — NOT
reducible to mainline hChr+hw (unlike J4-535's 1st-deriv); inherent to the 2nd derivative.
GATE: K<0 curved (Ric≠0), c=4/5≠±1, carries satisfiable. HONEST: a₁=R/6 CONDITIONAL + FLAT-
ONLY; AND the clean hAdom2 binder of the curved-boundary capstone is FALSE for the curved
witness ⟹ that capstone flat-satisfiable at hAdom2, sound route = capped census hAdom2cap.
hEdom/hFdom/hgate + hEbound/hInt Levi + Duhamel + extraction remain.
J4-538 = hgate (curved gate/affine-repair binder, of_geometry machinery reusable, avoid
hEdom/hFdom/hEbound) OR wire this crude envelope into the per-m capped hAdom2cap for g^K
(the census route that actually consumes the 2nd-deriv bound; clean hAdom2 is a dead-end).

## J4-538 — STRATEGIC ASSESSMENT (no brick): NO curved-satisfiable a₁ trace capstone currently exists
★★ DECISIVE NEGATIVE FINDING (adversarial audit + Sol-confirmed). The a₁ two-jet is produced
ONLY by the trace-capstone chain a1_R6_from_labelled{,_curved,_curved_gauge,_curved_boundary},
which has TWO INDEPENDENT second-x-derivative-domination consumers:
- LEG 1 (Da-limit leg) hDaLimLU_from_labelled / _v2_gauge → DaLimLUGoal: consumes the CLEAN
  single-constant hAdom2 (|witnessSecondXDeriv …|≤CA2·gaussDdim(wA2·τ)(0−z), CA2/wA2 fixed over
  all (0,T]) — A1R6FromLabelled.lean:391, A1R6FromLabelledCurvedGauge.lean:130/322/495.
- LEG 2 (Duhamel-core leg) truncatedDuhamelCore_AT_GATE_FULL → TruncatedDuhamelCore: consumes
  hLapFull : MemLapFull as an external binder.
The a₁ capstone passes clean hAdom2 to LEG 1 AND hLapFull to LEG 2 as INDEPENDENT args
(A1R6FromLabelledCurvedBoundary.lean:452,455).
CAPPED CENSUS ROUTE (hAdom2cap, τ⁻¹-tolerant, lower-capped epsSeq m≤τ≤T; provable from a crude
τ⁻¹ via CappedAdom2Audit.hAdom2_capped_family_of_crude, grounded HAdom2capGrounding.hAdom2cap_
grounded; J4-537's curvedRNC_witnessSecondXDeriv_dom_crude supplies the crude form for g^K) →
manufactures MemLapFull (leg 2's hLapFull) ONLY, via memLapFull_from_pairing_dominations. It
tolerates τ⁻¹ for the LO adjacency leg (hII_lo_from_capped, τ∈[ε_m,u) bounded below) and CARRIES
hII_hi:MemAdjHi as a labelled residual (HI leg [u−ε_m,u] has τ→0, ∫₀^ε τ⁻¹=+∞ un-dischargeable).
⟹ LEG 1 has NO capped variant; it still takes the clean, genuinely-FALSE single-constant hAdom2
(false at g^K for the SAME reason J4-537 documented: true envelope ~τ^(−1−n/2) at z=0 vs demanded
τ^(−n/2)). Wiring J4-537's τ⁻¹ crude via the capped route buys NOTHING at the a₁-two-jet level —
leg 1's independent clean-hAdom2 obligation survives. DECISIVE: there is NO curved-satisfiable a₁
trace capstone at present. To make one: (i) re-plumb LEG 1 (hDaLimLU_from_labelled_v2_gauge's
~45-180-binder census) to consume hAdom2cap + a carried MemAdjHi-style HI residual (structural
analogue of J4-391's MemLapFull work — NEW, LARGE); (ii) leg 2 can accept an externally-supplied
capped hLapFull (Sol: internal building not required). Only LEG 1 is the true blocker.
HONEST: a₁=R/6 CONDITIONAL + effectively FLAT-ONLY — the clean-hAdom2 curved capstone is flat-only
at hAdom2 in BOTH legs (J4-537 leg-2 clean binder; J4-538 leg-1 DaLim clean binder = the
un-eliminated blocker). Capped census = genuine curved path for the MemLapFull leg ONLY. J4-530..537
dominations are genuine reusable lemmas but the target capstone is NOT curved-satisfiable.
J4-539 = SCOPING brick: grep/read hDaLimLU_from_labelled_v2_gauge's internal pairing structure to
confirm its hAdom2 usage factors through the same pairing_intervalIntegrable LO/HI split (so the
capped-LO + carried-HI pattern applies) — if NOT, another high-value negative finding; if YES, build
hDaLimLU_from_labelled_capped (mirror memLapFull_from_pairing_dominations).

## J4-539 — leg-1 (Da-limit) LO-capped integrability sub-assembly: LEG-1 IS CAPPABLE [6813c43a]
DaLimLUCapped.lean (1 std-3, budget raw 0 / 9816 jobs; agent STALLED on stream watchdog after
writing file+import before pin/report — main verified on-disk file builds clean std-3 no-sorryAx
+ wired the pin, per verify-don't-trust discipline). The leg-1 mirror of leg-2's
CappedAdom2Audit.memLapFull_from_pairing_dominations. ★ SCOPE VERDICT (Sol-confirmed): leg-1's
clean hAdom2 factors IDENTICALLY to leg-2 — hDaLimLU_from_labelled consumes uncapped hAdom2 at
EXACTLY ONE site (GlobalRawBoundFacade.integrability_from_dominations), threading into the SAME
DaLimEasyTranche.pairing_intervalIntegrable LO/HI split: LO leg [0,u−ε_m] (τ∈[ε_m,u) bounded below)
CAPPABLE, HI leg [u−ε_m,u] (τ→0, ∫₀^ε τ⁻¹=+∞) carried as MemAdjHi; strip legs ride hAdomHeat (no
blow-up). Past integrability_from_dominations hAdom2 never reappears (no pointwise limit/τ→0/non-
integral estimate reaches the uniform bound).
integrability_from_dominations_capped: drop-in for integrability_from_dominations producing the
identical 4-tuple census (hIlo,hIhi,MemAdjLo,MemAdjHi), but MemAdjLo built INTERNALLY from the
per-m CAPPED hAdom2cap via hII_lo_from_capped (NO uncapped hAdom2) + MemAdjHi carried as hII_hi.
Proof = 4-tuple of banked lemmas. Non-vacuous (hAdom2cap true for curved witness via J4-537 crude→
capped; hII_hi standard residual; no hyp=conclusion). Generic in (g,gi) = interface re-plumbing.
HONEST: a₁=R/6 CONDITIONAL + effectively FLAT-ONLY — establishes leg-1 cappable + delivers the
LO-capped sub-assembly; NOT a₁=R/6; the full capped capstone hDaLimLU_from_labelled_capped
(~45-180-binder monolith) deferred to J4-540; convergence trio + Seeley-DeWitt wiring remain.
J4-540 = build hDaLimLU_from_labelled_capped (the leg-1 capped capstone) swapping
integrability_from_dominations → integrability_from_dominations_capped at line 495; consumes
hAdom2cap + carries MemAdjHi; then the a₁ capstone accepts externally-supplied capped hLapFull
(leg 2, via memLapFull_from_pairing_dominations) + this capped leg 1 ⟹ FIRST curved-satisfiable a₁
capstone (modulo the carried MemAdjHi residuals + convergence trio + geometric wiring). LARGE.

## J4-540 — leg-1 capped chain step 2: memLapFull_from_labelled_capped (MemLapFull from the capped family) [d987f75c]
DaLimLUCappedStep2.lean (1 std-3, budget raw 0 / 9817 jobs; elaborated 27s — no monolith blowup;
verified clean by rebuild reading #print axioms — no sorryAx). The next THIN SPLICE in the leg-1
capped re-plumbing. Routes J4-539's integrability_from_dominations_capped into memLapFull_from_
labelled → MemLapFull WITHOUT the false uncapped hAdom2.
memLapFull_from_labelled_capped: from capped-family inputs (hAdom2cap, strip-leg hAdomHeat/hmeasLo/
hmeasHi, hFdomW/hFzero/hmeas2Lo), carried hII_hi:MemAdjHi, + memLapFull inputs (hgi/hΓ/hInter/D0/D1/
hbnd/hPd2conv) → MemLapFull. Body: obtain ⟨_hIlo,_hIhi,hII_lo,hII_hi'⟩:=integrability_from_
dominations_capped …; exact memLapFull_from_labelled … hII_lo hII_hi' …. Leg-1 mirror of leg-2's
memLapFull_from_pairing_dominations, wired THROUGH the J4-539 brick.
DOWNSTREAM MAP (GlobalRawBoundFacade.hDaLimLU_from_labelled): integrability_from_dominations
(line 496) → 4-tuple → memLapFull_from_labelled (512, MemLapFull) [THIS BRICK CAPS] + hDaLimLU_
concrete (524, all four → DaLimLUGoal) [J4-541 target]. CLOSED: no uncapped hAdom2 on path. CARRIED:
hII_hi:MemAdjHi. Non-vacuous (strip-leg inputs genuine heat-op facts not disguised MemLapFull, Sol-
confirmed; hAdom2cap true for g^K via J4-537). Generic in (g,gi). HONEST: a₁=R/6 CONDITIONAL + FLAT-
ONLY — discharges only the hLapFull sub-goal of leg-1 from the capped family; ≠ the coefficient;
hDaLimLU_concrete still consumes false uncapped hAdom2, + capped leg-2 hLapFull + MemAdjHi residuals
+ convergence trio + Seeley-DeWitt wiring remain.
J4-541 = thread the full capped 4-tuple + this MemLapFull into DaLimLUConcreteDischarge.hDaLimLU_
concrete (line 524) → DaLimLUGoal = hDaLimLU_from_labelled_capped (the ~45-180-binder monolith) —
⚠ SPLICE thin (capped eCombine/source sub-assembly then concrete-gate discharge), NOT whole; check
if hDaLimLU_concrete accepts capped legs without dragging uncapped hAdom2 back in (else report
obstruction).

## J4-541 — capped leg-1 capstone hDaLimLU_from_labelled_capped: false uncapped hAdom2 PURGED from leg-1 [0bff283b]
DaLimLUCappedStep3.lean (1 std-3, budget raw 0 / 9818 jobs; elaborated 34s no monolith blowup;
verified clean by rebuild reading #print axioms — no sorryAx). ★ DECISIVE: hDaLimLU_concrete
(line-524 consumer) needs ONLY the 4-tuple + MemLapFull + gauge/frame as PLAIN binders — NO hAdom2
binder, does NOT re-drag uncapped domination. Full hAdom2 trace in hDaLimLU_from_labelled = EXACTLY
ONE site (line 497, integrability_from_dominations); NO second clean-hAdom2 site in leg-1.
hDaLimLU_from_labelled_capped: DaLimLUGoal g gi (vanVleckGatedWitness …)(leviSeries (heatOp …)) U
— identical conclusion to uncapped. Uncapped body verbatim + single-seam swap: step (v) calls
DaLimLUCapped.integrability_from_dominations_capped (J4-539) with per-m capped hAdom2cap + carried
hII_hi_res:MemAdjHi; unused hmeas2Hi dropped; all else byte-identical. CLOSED: false uncapped
whole-time hAdom2 PURGED from leg-1's Da-limit assembly. CARRIED: hII_hi_res:MemAdjHi (HI-leg
matched-sliver, ∫₀^ε τ⁻¹=+∞). Non-vacuous (hAdom2cap true for g^K J4-537; MemAdjHi genuine
target≠conclusion; strip-leg inputs genuine heat-op facts). Generic in (g,gi). ★★ MILESTONE: leg-1
FULLY re-plumbed off uncapped hAdom2 END-TO-END (capped integrability J4-539 → capped MemLapFull
J4-540 → capped capstone J4-541); the J4-538 blocker DISMANTLED; remaining leg-1 residual = carried
MemAdjHi. HONEST: a₁=R/6 CONDITIONAL + FLAT-ONLY — purges false hAdom2 from leg-1; ≠ the coefficient;
carried MemAdjHi residuals (both legs) + capped leg-2 hLapFull + convergence trio + Seeley-DeWitt
wiring remain.
J4-542 = attack the carried MemAdjHi residual: the moment-aware/matched-sliver discharge of MemAdjHi
for witnessSecondXDeriv (honest HI-leg integrability target, mirror leg-2's matched-sliver campaign)
OR pivot to the leg-2 hLapFull capped capstone so both legs reach the same MemAdjHi residual frontier
before tackling the ∫₀^ε τ⁻¹ sliver.

## J4-542 — leg-1 MemAdjHi HI-leg residual DISCHARGED via banked matched-sliver (moment-cancellation carry) [968c6093]
DaLimLUMemAdjHi.lean (1 std-3, budget raw 0 / 9819 jobs; elaborated 28s; verified clean by rebuild
reading #print axioms — no sorryAx). Discharges the opaque MemAdjHi residual of the capped leg-1
capstone (J4-541) — a cheap wire (already banked), not a wall.
GREP FINDING: MemAdjHi for witnessSecondXDeriv already discharged by MemAdjHiSliver.hII_hi_from_
sliver (returns exactly the hII_hi_res type) — reduces via intervalIntegrable_of_aesm_le (banked
slice-AESM hmeas2Hi_slice + τ^{-1/2} dominator intervalIntegrable_invSqrt_sub, ∫₀^ε τ^{-1/2}=2√ε<∞)
against the moment-improved carry hGpow.
hDaLimLU_from_labelled_capped_memAdjHi: DaLimLUGoal … — same sig as hDaLimLU_from_labelled_capped
MINUS the opaque hII_hi_res:MemAdjHi binder, PLUS honest carries hSecCont/hBcont (continuity/AESM),
Cpair/hCpair (0≤Cpair), hGpow (τ^{-1/2} signed-integral bound). hεU derived in-file.
CLOSED: opaque MemAdjHi binder. CARRIED: hGpow = τ^{-1/2} bound on the SIGNED z-integral of the
2nd-deriv pairing. Genuinely TRUE (∫z ∂²_xG·F=O(1) as τ→0: leading τ⁻¹ cancels vs ∫z ∂²G=0 moment
cancellation; (u−s)^{-1/2}≥ε₀^{-1/2}, Cpair=(sup|∫z…|)·ε₀^{1/2}). STRICTLY WEAKER than the false
τ-uniform pointwise Gaussian bound — NOT the flat hole, NOT vacuous; concrete-kernel constructor
for hGpow OWED (J4-543). Non-vacuous, no carry=conclusion (Sol-confirmed). HONEST: a₁=R/6
CONDITIONAL + FLAT-ONLY — ≠ the coefficient; hGpow constructor + capped leg-2 hLapFull + convergence
trio + Seeley-DeWitt wiring remain.
J4-543 = construct hGpow for the concrete convolved kernel (moment-cancellation lemma |∫z ∂²_xG(u−s)
·F|≤Cpair·(u−s)^{-1/2} from ∫z ∂²G=0 + first-moment Taylor bound on F) — removes the last
substantive HI-leg carry; new file QIQTH/MemAdjHiMomentBound.lean. OR mirror the J4-542 wire on
leg-2's matched-sliver MemAdjHi to cap that leg symmetrically.

## J4-543 — hGpow moment-cancellation constructed from honest geometric amplitude bundle [146820a4]
MemAdjHiMomentBound.lean (2 std-3, budget raw 0 / 9820 jobs; elaborated ~31s; verified clean by
rebuild reading #print axioms — no sorryAx). Constructs the leg-1 hGpow carry (J4-542's last
substantive HI-leg residual) from honest geometric amplitude data — replaces abstract carry with
geometric one.
- slice2_inner_bound: generic per-slice inner bound (exposed hinner core of sliver2_bound):
  |∫z D2H(u−s)·F s z 0|≤(L·(15/2·n)+3/4·M₁·C_F)·(u−s)^(−1/2)+M₂·C_F on Ioo(u−ε)u. 3 terms: Hessian
  cancellation / odd first moment / mass one.
- hGpow_of_amplitudeData: from data:∀i AmplitudeDerivativeData …, K₁/K₀+comparisons, window floor,
  hEndpoint → ∃Cpair≥0 with EXACT hGpow type of MemAdjHiSliver.hII_hi_from_sliver. Route:
  slice2_inner_bound → leviSecondPairing_le_invSqrt → hGpow_uIoc_of_Ioo_zeroEndpoint.
★ ADVERSARIAL FINDING (Sol-confirmed): ∫z ∂²_xG=0 does NOT hold outright for the curved witness —
the exact 2nd-moment cancellation (gaussian_hessian_cancel + gaussian_hessian_moment_zero) hits
only the LEADING flat-Gaussian Hessian; curvature is ABSORBED into the bounded amplitudes
Aamp/A1amp/A2amp (van-Vleck×chart-image×cutoff), carried via the 3-term decomposition hD2Hexpand.
No curvature term dropped — it lives in the carried bundle. Genuinely true, curved-not-flat (Aamp≢1
off-flat), non-vacuous. CLOSED: abstract hGpow now constructible from the geometric bundle.
CARRIED: AmplitudeDerivativeData bundle (esp. hD2Hexpand), K₁/K₀+comparisons, hEndpoint. Generic
in (g,gi); applies K<0. HONEST: a₁=R/6 CONDITIONAL + FLAT-ONLY — REDUCES not closes the wall;
carried hD2Hexpand (chart-Jacobian + C⁴ geometry) + hEndpoint + capped leg-2 hLapFull + convergence
trio + Seeley-DeWitt wiring remain.
J4-544 = (i) discharge hEndpoint by proving witnessSecondXDeriv i 0 z=0 (gaussDdim 0≡0 for n≥1,
heatKernel1D 0 y=0) + (ii) construct a concrete AmplitudeDerivativeData term for the van-Vleck
witness (discharging hD2Hexpand = chart-Jacobian + C⁴ geometric input, the LAST genuine HI-leg
geometry) — new file QIQTH/AmplitudeDerivativeDataConcrete.lean; OR wrapper hDaLimLU_from_
amplitudeData removing DaLimLUMemAdjHi's Cpair/hCpair/hGpow binders; OR mirror capped chain on leg-2.

## J4-544 — leg-1 HI-leg endpoint carries hEndpoint+hAzero discharged; hD2Hexpand scoped to banked collar route [2d8e619f]
AmplitudeDerivativeDataConcrete.lean (6 std-3, budget raw 0 / 9821 jobs; elaborated ~26s; verified
clean by rebuild reading #print axioms — no sorryAx). Discharges the cheap endpoint carries of the
leg-1 HI-leg hGpow pipeline + precisely scopes the remaining curved geometric input.
PART A (endpoint carries DISCHARGED, curvature-independent measure-zero): gatedWitnessN1_eq_zero_of_
nonpos (gated N=1 cutoff witness ≡0 at τ≤0 via gaussDdim vanishing); vanVleckGatedWitness_eq_zero_of_
nonpos (discharges abstract hAzero carry ~10 assembly files); witnessSecondXDeriv_endpoint_zero
(witnessSecondXDeriv i 0 z=0, inner slot zero fn → both pd vanish); hEndpoint_discharged (exact
hGpow_of_amplitudeData hEndpoint binder, UNCONDITIONAL only n≥1); hGpow_of_amplitudeData_noEndpoint
(hEndpoint removed + supplied internally); amplitudeData_concrete_residual_intro (records surviving
hD2Hexpand carry, depends on NO axioms).
PART B (hD2Hexpand = GENUINE WALL, precisely scoped): for curved witness the near-isometry error
ratio bounded ONLY on the collar (off-collar hAampBdd fails). NO banked flat/generic UNRESTRICTED
constructor — but the banked COLLAR variant DOES exist: AmplitudeDataOnCollar.AmplitudeDerivative
DataOn + amplitudeDataOn_concrete discharges hD2HexpandOn from a chart-jet bundle hjets ⟹ remaining
curved geometric input isolates to hjets (chart-jet C⁴/Jacobian).
GATE: PART A curvature-independent endpoint (holds curved g^K K<0 + flat) — NOT curvature-carrying;
curved content entirely in scoped hD2Hexpand (not claimed closed). HONEST: a₁=R/6 CONDITIONAL +
FLAT-ONLY — hEndpoint/hAzero ≠ the coefficient; curved hD2Hexpand (→collar hjets) + capped leg-2
hLapFull + convergence trio + Seeley-DeWitt wiring remain.
J4-545 = thread hGpow_of_amplitudeData_noEndpoint + hAzero discharge (vanVleckGatedWitness_eq_zero_
of_nonpos) into DaLimLUMemAdjHi/MemAdjHiSliver consumers (drop hAzero/hEndpoint binders there) THEN
wire amplitudeDataOn_concrete (collar) into the hGpow pipeline via the collar-regime split,
isolating hjets (chart-jet C⁴/Jacobian) as the single remaining curved geometric input. OR pivot to
leg-2 hLapFull capped chain. OR convergence trio.

## J4-545 — hGpow closure boundary exposed; collar route needs off-collar tail (not just hjets) [393474b1]
HGpowFromCollar.lean (2 std-3, budget raw 0 / 9822 jobs; elaborated ~27s; verified clean by rebuild
reading #print axioms — no sorryAx). Exposes the correct hGpow closure boundary + precisely scopes
the collar-route gap — CORRECTS the cp428 assumption that the collar bundle reduces the leg-1 HI-leg
to hjets alone.
★ FINDING (Sol-confirmed): the collar route does NOT close hGpow with only hjets. hGpow_of_amplitude
Data reaches hGpow in 2 stages: (I) per-slice open-window inner bound (K₁(u−s)^{-1/2}+K₀) from
slice2_inner_bound, whose leading τ^{-1/2} gain is the EXACT FULL-SPACE Hessian moment ∫(z_i²−2τ)/
(4τ²)·G_τ=0 over ALL z; (II) closure. The collar bundle supplies fields only on ‖z‖≤c√τ; off-collar
the ρ-ratio blows up ⟹ collar-constant amplitude bounds LITERALLY FALSE, and truncating the Hessian
moment to the τ-shrinking collar DESTROYS the cancellation. No thin collar composition closes it.
(Machine-recorded: SliverBoundOnCollar.lean J4-353 case (b) — consumption over all Point n with the
Gaussian envelope; surviving carry = off-collar Gaussian tail on ‖z‖>c√τ.)
- hGpow_from_innerWindow: ROUTE-AGNOSTIC closure — from ANY per-slice open-window inner bound
  (K₁(u−s)^{-1/2}+K₀ shape, all-z OR collar+split) + 1≤n → uIoc hGpow, τ=0 endpoint internal from
  hEndpoint_discharged. Faithfully factors stage (II); the stable interface both routes hit. std-3.
- collar_hGpow_residual(+_intro): scoping conjunction = hOnCollar (BANKED amplitudeDataOn_concrete,
  input hjets satisfiable via residueJets_satisfiable J4-350) ∧ hOffCollarTail (corrected off-collar
  Gaussian tail reconstituting the full-space moment). No axioms.
Did NOT build a degenerate hGpow_of_amplitudeDataOn (Sol-warned: hSplitInner already implies hGpow →
bundle not consumed). curved-not-flat (obstruction IS the curvature ρ=exp((r_z−r_{W0})/4τ)≠1).
HONEST: a₁=R/6 CONDITIONAL + FLAT-ONLY — exposes closure boundary + scopes the gap; leg-1 HI-leg
curved input = hjets (on-collar) PLUS hOffCollarTail (off-collar tail), NOT hjets alone; + capped
leg-2 hLapFull + convergence trio + Seeley-DeWitt wiring remain.
J4-546 = build collar_inner_on from AmplitudeDerivativeDataOn (integrate banked sliverIntegrand_on_
collar 3-term identity over the collar) producing the collar-truncated inner integral with the
moment defect EXPLICIT — isolate ∫_{collar}(z_i²−2τ)/(4τ²)G_τ=−∫_{‖z‖>c√τ}(…) as the precise
hOffCollarTail obligation ⟹ turns hOffCollarTail into a concrete Gaussian-tail moment integral
(gaussian_beats_power / exp(−c²/4) territory), the last step before hGpow_from_innerWindow. OR pivot
to leg-2 hLapFull capped chain OR convergence trio.

## J4-546 — concrete exp-suppressed off-collar tail moment (operational closure = banked matched estimate) [07eb9cb8]
OffCollarTailMoment.lean (3 std-3, budget raw 0 / 9823 jobs; ~30s elab; verified clean by rebuild
reading #print axioms — no sorryAx). Sharpens the leg-1 HI-leg off-collar tail moment from crude τ⁻¹
to a concrete exp-in-c² suppressed integral.
- gaussDdim_tail_le_scaled: gaussDdim τ z ≤ √2^n·exp(−R²/(8τ))·gaussDdim(2τ)z on ‖z‖>R (width split).
- tailMoment_expSuppressed_bound: |SliverTailMatched.tailMoment i τ R|≤√2^n·exp(−R²/(8τ))·(2n+1)/(2τ).
- tailMoment_collar_expSuppressed: |tailMoment i τ (c√τ)|≤√2^n·exp(−c²/8)·(2n+1)/(2τ) (τ-indep e^{−c²/8}).
★ HONEST VERDICT (Sol-confirmed): tail machinery largely BANKED (SliverTailMatched J4-354 = Sol#13
matched-pair: tailMoment, collarMoment_eq_neg_tail ∫_collar H=−T_τ, O(τ^{-1/2}) closure sliver_term1_
on_collar_matched); its tailMoment_bound had crude τ⁻¹ + deferred the sharp poly(c)e^{−κc²} — THIS
fills it. BUT for FIXED c the tail is STILL O(τ⁻¹); exp-suppression operational only under growing
collar c=c(τ). ⟹ the OPERATIONAL leg-1 HI-leg term-1 closure is the banked sliver_term1_on_collar_
matched, NOT this bare bound — this brick = sharp-tail quantitative INFRASTRUCTURE not the closure.
GATE: non-vacuous; curvature in the adjacent multiplier A₀=q(0)=Aamp·F(0) via the banked matched
pairing (true corrected tail, Gaussian decay retained, not flat shortcut). HONEST: a₁=R/6 CONDITIONAL
+ FLAT-ONLY — ≠ the coefficient; on-collar hjets + capped leg-2 hLapFull + convergence trio +
Seeley-DeWitt wiring remain.
★ PIVOT DECISION: leg-1 HI-leg consumed J4-542..546 (5 bricks); it is now well-characterized (matched
estimate sliver_term1_on_collar_matched IS the operational closure, banked). PIVOTING to broaden.
J4-547 = mirror the leg-1 capped chain (J4-539..541 pattern) onto LEG-2 hLapFull: the a₁ capstone
takes an EXTERNALLY-supplied capped hLapFull:MemLapFull (Sol J4-538); build/wire it for the curved
witness via CappedAdom2Audit.memLapFull_from_pairing_dominations (the leg-2 capped template) + the
landed curved dominations — the symmetric other leg. OR the convergence trio.

## J4-547 — curved leg-2 hLapFull (cheap wire): BOTH a₁-capstone legs now capped-for-curved [58650593]
Leg2HLapFull.lean (2 std-3, budget raw 0 / 9824 jobs; elaborated 26s; verified clean by rebuild
reading #print axioms — no sorryAx). Supplies the curved leg-2 external MemLapFull binder the a₁
capstone's Duhamel-core leg (truncatedDuhamelCore_AT_GATE_FULL) consumes.
★ KEY: leg-2's hLapFull is the SAME MemLapFull object J4-540 (DaLimLUCappedStep2.memLapFull_from_
labelled_capped) already builds — NOT a distinct instance. Capstone leg-2 binder = J4-540 output at
S:=constGate g gi hChr hK c. Cheap wire.
curved_leg2_hLapFull: exact leg-2 MemLapFull at S:=constGate, threading J4-540; gauge binders (hgi:
MemGaugeGi, hΓ:MemGaugeGamma) discharged internally via gauge_from_geometry from hK0/hframeK/hinvF/
hdg0 (banked curvedRNC_geomGaugeBundle at singleton seed). Carried verbatim from J4-540: hInter,
hAdomHeat (J4-536), per-m CAPPED hAdom2cap (J4-537), hFdomW/hFzero, hmeasLo/hmeasHi/hmeas2Lo, hII_hi:
MemAdjHi, √ε sliver D0/D1/hbnd, hPd2conv. curved_leg2_hLapFull_curved_satisfiable: Ric(0)=(n−1)Kδ≠0.
★★ BOTH LEGS NOW CAPPED-FOR-CURVED: leg 1 = J4-541 hDaLimLU_from_labelled_capped, leg 2 = this brick
via J4-540; both purge the FALSE uncapped whole-time hAdom2. GATE: K<0 curved (Ric≠0 n≥2); hAdom2cap
TRUE off flat (J4-537); MemAdjHi/moment/√ε carries satisfiable, none=conclusion, no :=True. Sol:
grounding only gauge while carrying dominations is sound; no seed hazard. HONEST: a₁=R/6 CONDITIONAL
+ FLAT-ONLY — both legs capped ≠ the coefficient; the capstone still carries MemAdjHi/moment residuals
(both legs) + convergence trio + Seeley-DeWitt geometric wiring.
J4-548 = ASSEMBLE the curved a₁ capstone from BOTH capped legs: instantiate A1R6FromLabelledCurved.
a1_R6_from_labelled_curved at g:=curvedRNCMetric K feeding leg-2 hLapFull from curved_leg2_hLapFull +
leg-1 hDa from J4-541 hDaLimLU_from_labelled_capped — the FIRST genuinely curved-satisfiable a₁
capstone modulo {both-leg MemAdjHi/moment residuals, convergence trio, SDW geometric wiring}. ⚠
MONOLITH: the capstone is a large Π — SPLICE (feed the two legs as the specific binders), do NOT
re-elaborate whole; >5min STOP+split. OR attack the convergence trio.

## J4-548 — ★★ FIRST curved-satisfiable, non-vacuous a₁ two-jet capstone (clean hAdom2 removed) [75567286]
CurvedA1Assembled.lean (2 std-3, budget raw 0 / 9825 jobs; elaborated 26s thin no monolith; verified
clean by rebuild reading #print axioms — no sorryAx; ADVERSARIAL GATE verified independently by main).
The first a₁ two-jet capstone that is NOT flat-only — removes the clean whole-time 2nd-derivative bound
hAdom2 (the sole binder J4-537/538 proved FALSE for g^K=curvedRNCMetric K, K<0), routing BOTH legs
through caller-supplied capped outputs.
curved_a1_R6_assembled: a₁ two-jet at the const-radius gate, conclusion identical to a1_R6_from_
labelled_curved, coefficient (∑ᵢ ricci g gi i i 0)/6. Assembly: htr_adapter (SDW htr from hGauss) +
a1_R6_slots_AT_GATE (3 per-gate slots, feeding LEG 1 hDa + LEG 2 core as EXTERNAL binders) +
wide_a1_R6_core_AT_CONSTRADIUS.
★ ADVERSARIAL GATE (agent + Sol + MAIN read of the statement): GENUINELY CURVED-SATISFIABLE, NON-
VACUOUS. (i) clean hAdom2 (2nd-deriv, false) appears ONLY in header prose, NOT a binder; the hAdom
present is the amplitude-witness domination (TRUE, J4-535), not the 2nd-deriv. (ii) LEG 1 hDa:
DaLimLUGoal ← J4-541; LEG 2 core:TruncatedDuhamelCore ← J4-547 — both inhabited for g^K WITHOUT forcing
Ric=0. (iii) coefficient (∑ᵢ ricci)/6 = n(n−1)K/6 ≠ 0 for g^K; curved_a1_R6_assembled_curved_
satisfiable proves pd(pd(∑ₐ g^K_aa)c)c 0 ≠ 0 (curvedRNCMetric_ricci_trace_diag_ne). (iv) no binder
:=True/vacuous/=conclusion. Sol: SATISFIABLE (hGauss+gauge does NOT force Ric=0), NON-VACUOUS, HONEST.
Binder→supplier: hDa←J4-541, core←J4-547, gauge←J4-525 curvedRNC_geomGaugeBundle, hGauss→htr←
curvedRNCMetric_hgauge, Ric pin←curvedRNCMetric_ricci_from_gauge, hpkgBound←J4-536.
★★ MILESTONE: converts J4-538's "NO curved-satisfiable a₁ capstone exists" into a genuinely curved-
satisfiable, non-vacuous a₁ capstone SHAPE. HONEST: a₁=R/6 CONDITIONAL — the capstone SHAPE with the
flat-forcing binder removed + proven-nonzero curved coefficient; NOT unconditional a₁=R/6. Still
carried: MemAdjHi/matched-sliver moment residuals + convergence trio (inside J4-541/547 suppliers),
SDW geometric wiring (hGauss→htr/hsrc/transportCoeff), hDConv/hCConv analytic census. The legs enter
as BINDERS here; the fully-wired end-to-end curved instantiation (discharging them at g^K) is NEXT.
J4-549 = wire J4-541 hDa + J4-547 core into curved_a1_R6_assembled at g:=curvedRNCMetric K behind a
single curved_a1_R6_fully_wired, shrinking the residual surface to {MemAdjHi/matched-sliver moment,
convergence trio, transportCoeff/SDW}. OR discharge hGauss for g^K (bank the exact RNC Gauss-lemma
=ᶠ[𝓝 0] fact) so htr is supplied-for-curved. OR the convergence trio.

## J4-549 — LEG-1 of the curved a₁ capstone wired at g^K (curved_hDa_at_gate) + residual map [a8d2bdce]
CurvedA1FullyWired.lean (1 std-3, budget raw 0 / 9826 jobs; ~45s elab; verified clean by rebuild
reading #print axioms — no sorryAx; adversarial gate main-verified). Wires LEG 1 of the J4-548
curved-satisfiable a₁ capstone at g^K=curvedRNCMetric κ (κ<0). Honest fragment — full curved_a1_R6_
fully_wired (capstone+both legs) deferred (monolith).
curved_hDa_at_gate: DaLimLUGoal (curvedRNCMetric κ)(curvedRNCInv κ)(vanVleckGatedWitness … (constGate
… c)a b)(leviSeries …) U = exactly the capstone's hDa binder under g/gi/S substitution. Body: J4-541
hDaLimLU_from_labelled_capped at g:=curvedRNCMetric κ, hinvF←curvedRNCMetric_hinvF, hdg0←curvedRNC
Metric_pd_zero discharged.
★ RESIDUAL MAP (carried, classified): geometry/gauge (hChr, hK/hK0, hframeK); analytic-census F2/W2
diff-under-∫ (V/hVopen/hV0/snb/hsnb/hQ1/hFmeas/hFint/hF'meas/bnd/hbdd/hbound/hdiff + window aa/haa/
hau/hUTle); convergence-trio/Levi (C/dataLevi + positivity consts + hAdomHeat + CAPPED hAdom2cap +
hmeasLo/hmeasHi/hmeas2Lo + hPd2conv + E-comb hDa(DaTrunc)/hLap/hLapZ/hEZ/hLapS/hES); MemAdjHi/moment
(hII_hi_res:MemAdjHi); √ε sliver/raw (τ₀/dataAmp/hεaa/hετ₀, P/hP/hraw:GlobalGatedRawBound). No SDW in
leg-1 (lives in capstone hGauss/htr/hsrc).
★ ADVERSARIAL (main+Sol): non-vacuous for g^K. hinvF/hdg0 true-fact/non-circular; residuals jointly
satisfiable, none forces Ric=0. ⚠ hframeK (g=δ on seed) holds for κ<0 only at rncRadialSq=0 ⟹
COLLAPSES seed to K={0} (0∈K) ⟹ TRUE via curvedRNCMetric_zero; geometric-localization residual NOT
unsatisfiable (the a₁ two-jet is a POINTWISE statement at 0). ⚠ CRUCIAL: the new curved capstone
DROPPED the conflicting mass condition (hmassone) that made hframeK force Ric=0 in the OLD flat-only
capstone (J4-509) — so K={0} is now consistent + non-vacuous. Coefficient (∑ᵢricci)/6=n(n−1)κ/6≠0
genuine. HONEST: a₁=R/6 CONDITIONAL — leg-1 wired ≠ unconditional; CAPPED hAdom2cap + MemAdjHi moment
+ convergence trio + Levi/raw/measurability + (deferred capstone) SDW wiring + LEG 2 all owed.
J4-550 = LEG-2 adapter curved_core_at_gate (curved TruncatedDuhamelCore via truncatedDuhamelCore_AT_
GATE_FULL fed by J4-547 curved_leg2_hLapFull, discharge hgi/hΓ via gauge_from_geometry); ⚠ watch
shared binder names D0/D1/hbnd/hII_hi/hFzero (reuse one per). Then J4-551 assembles curved_a1_R6_
fully_wired = curved_hDa_at_gate + curved_core_at_gate → curved_a1_R6_assembled + gauge bundle +
curvedRNCMetric_hgauge + J4-536 hpkgBound, K:={0}. Largest remaining residual after = MemAdjHi/
matched-sliver moment + convergence trio (both legs).

## J4-550 — LEG-2 of the curved a₁ capstone wired at g^K (curved_core_at_gate) + shared-binder map [eb5a2900]
CurvedA1Leg2Core.lean (2 std-3, budget raw 0 / 9827 jobs; ~28-51s elab; verified clean by rebuild
reading #print axioms — no sorryAx; adversarial gate main-verified). Symmetric leg-2 adapter of J4-549.
curved_core_at_gate: TruncatedDuhamelCore (curvedRNCMetric κ)(curvedRNCInv κ)(vanVleckGatedWitness …
(constGate … c)a b) t = byte-for-byte the J4-548 capstone's `core` binder at g:=curvedRNCMetric κ.
Body: discharge hinvF/hdg0; obtain ⟨hgi,hΓ⟩:=gauge_from_geometry; hLapFull:=J4-547 curved_leg2_
hLapFull; exact truncatedDuhamelCore_AT_GATE_FULL (arg order verbatim from A1R6FromLabelledCurved).
DISCHARGED: hgi/hΓ (gauge_from_geometry), hinvF/hdg0, hUpos, leg-2 hFzero, hLapFull (J4-547).
★ SHARED-BINDER MAP (J4-551 assembly, bound once both legs consume): hII_hi:MemAdjHi, D0/D1/hbnd
(√ε sliver), U/T/hUT, hK0, hframeK, hChr, hK, a/b/c, hAdomHeat, CAPPED hAdom2cap, hmeasLo/hmeasHi/
hmeas2Lo, hPd2conv, wA/CA/wA2/CA2c, W2 diff-under-∫ census family, hQ1 — SAME types as J4-549 leg-1.
★ ADVERSARIAL (main-verified): non-vacuous g^K; hgi/hΓ genuinely supplied (not conclusion); residuals
satisfiable K<0 (hframeK→seed {0} RNC-normalization non-vacuous; hAdom2cap CAPPED true J4-537; hII_hi
honest moment target not forcing Ric=0); Ric(0)=(n−1)Kδ≠0 preserved. No forced Ric=0/unsatisfiable.
★★ BOTH LEGS now wired at g^K: leg 1 = J4-549 curved_hDa_at_gate, leg 2 = J4-550 curved_core_at_gate.
HONEST: a₁=R/6 CONDITIONAL — removes hgi/hΓ/hinvF/hdg0 as binders; NOT unconditional; MemAdjHi/moment
+ convergence trio + measurability/window + SDW wiring (transportCoeff/htr) owed.
J4-551 = ASSEMBLE curved_a1_R6_fully_wired: instantiate CurvedA1Assembled.curved_a1_R6_assembled at
g:=curvedRNCMetric κ feeding hDa:=curved_hDa_at_gate (J4-549) + core:=curved_core_at_gate (J4-550),
UNIFYING the shared binders (hII_hi/D0/D1/hbnd, W2 family, hK0/hframeK, numerics). Remaining capstone
externals to supply: Section A/C params, hsrc, LABELLED hGauss (SDW), hpkgBound/hmemS0/hopenS0/hS1,
hbdry, Sections G/H. Result = fully-wired curved-satisfiable a₁ two-jet with only physical/SDW/
convergence residuals. ⚠ MONOLITH: SPLICE (feed the two leg terms), if >5min STOP+split.

## J4-551 — ★★ fully-wired curved a₁ two-jet at g^K (both legs + geometry discharged) + FINAL RESIDUAL MAP [4fbbc1a5]
CurvedA1FullyWiredCapstone.lean (3 std-3, budget raw 0 / 9828 jobs; verified clean by rebuild reading
#print axioms — no sorryAx; ★ADVERSARIAL GATE main-verified independently). The first assembled,
genuinely-curved, std-3, sorry-free a₁ two-jet capstone threading BOTH capped-route legs + geometry
discharge into one theorem, at g^K=curvedRNCMetric κ (κ<0).
- curved_a1_R6_geomWired: curved_a1_R6_assembled at g:=curvedRNCMetric κ with 9 g/gi-geometry binders
  discharged (curvedRNC_geomGaugeBundle J4-525; curvedRNCMetric_det_pos hgpos); hDa/core external.
- curved_a1_R6_fully_wired: + LEG 1 hDa:=curved_hDa_at_gate (J4-549) + LEG 2 core:=curved_core_at_gate
  (J4-550), shared binders unified. Conclusion coefficient (∑ᵢ ricci g^K i i 0)/6.
- curved_a1_R6_fully_wired_curved_satisfiable: Ric(0)≠0.
★ ADVERSARIAL (MAIN-VERIFIED, J4-509-critical): NON-VACUOUS. Clean hAdom2 ABSENT (only capped
hAdom2cap CA2c:ℕ→ℝ). ⚠⚠ hframeK ∧ hmassone do NOT force Ric=0 here (KEY difference from J4-509):
hframeK (∀q∈K, g^K q=δ) → FRAME SEED K={0} (RNC normalization); hmassone (∫z vanVleckGatedWitness …
(constGate … c) … (epsSeq m) 0 z → 1) = the CONSTGATE(c)-mass heat-kernel normalization, a DIFFERENT
set (radius-c ball c>0) from the frame seed {0}. In J4-509 the mass was gated by the SAME K → K
measure-zero forced mass 0≠1 → Ric=0; HERE decoupled → both hold independently → non-vacuous.
Coefficient n(n−1)κ/6≠0. Sol concurs.
★ FINAL RESIDUAL MAP: (MemAdjHi/moment) hII_hi:MemAdjHi + √ε sliver dataAmp/τ₀/D0/D1/hbnd;
(convergence trio) dataLevi + E-comb hDa_ec/hLap/hLapZ/hEZ/hLapS/hES + E₀E₁/hEdom/hIlo/hIhi + hPd2conv
+ hII_lo/hInter/hEcomb + boundary hBoundaryLim/hbdry + frozen/moving (hmass/hmassone/hmod/hsup/hUsub);
(measurability/window) hmeas* + W2 family + capped Gaussian hAdom2cap/hAdomHeat/hFdomW + Section-G F2
census + Section-H hCConv census + gate pkg hpkgBound/hmemS0/hopenS0/hS1 + raw hraw/P + window; (SDW)
ONLY hsrc (hGauss/htr DISCHARGED); (frame) hframeK(→{0})/hChr/hK/hK0.
HONEST: a₁=R/6 CONDITIONAL — holds for g^K GIVEN the residuals above (owed analytic/physical inputs);
coefficient NOT unconditional. J4-551 = honest precisely-scoped statement of exactly what's owed.
J4-552 = attack the MemAdjHi matched-sliver moment residual hII_hi (single shared, most-central,
deepest analytic wall feeding BOTH legs — the √ε adjacency-sliver moment the capped route can't supply
pointwise). 2nd choice = convergence-trio E-combination (DaTrunc/LapTrunc + MemECombine).

## J4-552 — discharge hII_hi:MemAdjHi in the curved a₁ capstone; opaque MemAdjHi binder dropped [a6d8943c]
CurvedA1MemAdjHiWired.lean (2 std-3, budget raw 0 / 9829 jobs; 35s elab; verified clean by rebuild
reading #print axioms — no sorryAx; adversarial main-verified). Discharges the most-central residual
hII_hi:MemAdjHi of curved_a1_R6_fully_wired (J4-551) for g^K via the banked leg-1 HI-leg chain
(J4-542–546), replacing opaque MemAdjHi with concrete inputs.
- curved_hII_hi_at_gate: produces the capstone hII_hi:MemAdjHi by composing the chain (defeq the
  capstone binder, confirmed by exact); no opaque MemAdjHi carried.
- curved_a1_R6_fully_wired_hII: J4-551 capstone with hII_hi binder DROPPED, supplied internally.
CHAIN: (1) hGpow_of_amplitudeData_noEndpoint (hGpow from data+K₁/K₀+window-floor, τ=0 shed via 1≤n);
(2) MemAdjHiSliver.hII_hi_from_sliver (MemAdjHi from hGpow + slice-AESM hmeas2Hi_slice via
intervalIntegrable_of_aesm_le + intervalIntegrable_invSqrt_sub); (3) compose at g^K; (4) feed into
curved_a1_R6_fully_wired.
★ UPDATED RESIDUAL: opaque hII_hi:MemAdjHi → concrete {data:∀i AmplitudeDerivativeData (ONE hard
field hD2Hexpand = chart-jet Leibniz-Gaussian 3-term identity = owed hjets/off-collar geometry) +
K₁/K₀/hK₁bound/hK₀bound + hSecCont/hBcont continuity + window-floor}. NET NEW carry vs J4-551 = ONLY
{K₁/K₀ envelope + hSecCont/hBcont} (dataAmp/T/τ₀/aa/haa/hau/hεaa/hετ₀/hUT already capstone binders).
ADVERSARIAL (main): non-vacuous g^K; conclusion verbatim → coefficient n(n−1)κ/6≠0 carries over;
reduced inputs satisfiable none forcing Ric=0. HONEST: a₁=R/6 CONDITIONAL — SHARPENS the residual
(opaque MemAdjHi → concrete chart-jet+tail+continuity); NOT unconditional; hjets C⁴ + off-collar tail
owed. J4-553 = construct dataAmp from the chart-jet bundle via AmplitudeDataOnCollar.amplitudeDataOn_
concrete (hD2HexpandOn from hjets) + the off-collar corrected tail (OffCollarTailMoment/collar_hGpow_
residual.hOffCollarTail) ⟹ isolate hjets + hOffCollarTail as the two remaining geometric carries. OR
the convergence trio.

## J4-553 — curved collar amplitude data from chart-jets; HI-leg residual → hjets + off-collar tail (vacuity trap avoided) [ebc03bf1]
CurvedA1AmplitudeData.lean (3 std-3, budget raw 0 / 9830 jobs; verified clean by rebuild reading
#print axioms — no sorryAx; adversarial main-verified). Concretizes the HI-leg amplitude carry of the
fully-wired curved a₁ capstone down to the irreducible chart-jet geometry, soundly routing AROUND a
non-constructible whole-space bundle.
★ SOUNDNESS CATCH: the whole-space AmplitudeDerivativeData is NON-CONSTRUCTIBLE for the curved witness
(J4-544 PART B: off-collar ρ blows up ⟹ hAampBdd fails). A collar→whole-space bridge would carry a
plausibly-UNSATISFIABLE (vacuous) hypothesis = the axiom-budget-blind-spot hole. This brick AVOIDS it,
routing the HI-leg via collar bundle + hOffCollarTail into hGpow_from_innerWindow (NO fabricated
whole-space data). Sol-confirmed sound route.
- curved_amplitudeDataOn_at_gate: curved COLLAR AmplitudeDerivativeDataOn (collarRegime r₀ c τ₀) from
  AmplitudeDataOnCollar.amplitudeDataOn_concrete ← hjets — discharges on-collar hD2HexpandOn.
- curved_hII_hi_from_innerWindow: capstone hII_hi:MemAdjHi for g^K via the sound route
  (hGpow_from_innerWindow ← hinner_window ← hOnCollar[banked←hjets] ⊕ hOffCollarTail; τ=0 discharged
  internally; slice-AESM continuity carried).
- curved_amplitudeData_residual(_intro): scoping ledger (no axioms).
★ UPDATED HI-leg RESIDUAL: MemAdjHi ← {slice-AESM continuity} ∪ {hinner_window ← hOnCollar(BANKED←
hjets) ⊕ hOffCollarTail}. OWED: hjets (chart-jet C⁴/Jacobian: 1st/2nd i-jets of uniformInverseChart,
amplitude jets of chartAmp, + 3 center identities ∑V·P=zᵢ / ∑P²=1 / ∑V·Q=0) + hOffCollarTail
(off-collar Gaussian-tail reconstitution). ELIMINATED: τ=0 endpoint + whole-space detour.
ADVERSARIAL (main): non-vacuous g^K, R/6=n(n−1)κ/6≠0; hjets genuinely curved (over uniformInverseChart/
chartAmp of curvedRNCMetric κ, not flat); hinner_window true satisfiable heat-kernel moment estimate.
HONEST: a₁=R/6 CONDITIONAL — SHARPENS the residual (HI-leg amplitude → hjets + hOffCollarTail); NOT
unconditional; hjets C⁴ + hOffCollarTail owed Seeley-DeWitt geometry.
J4-554 = build the chart-jet bundle hjets for curvedRNCMetric κ (1st/2nd i-jets of uniformInverseChart
+ amplitude jets of chartAmp + 3 center identities, from the banked C⁴ tower expMap_contDiffOn_four /
RNC jets / curvedRNCMetric_contDiff) ⟹ collapse hOnCollar to elementary, leaving hOffCollarTail as the
last HI-leg geometric wall. OR attack hOffCollarTail directly. OR pivot to the convergence trio.

## J4-554 — chart-jet bundle hjets for g^K; mostly banked, owed = global ∀x jet + 3 general-base center identities [ffcf7c41]
CurvedChartJets.lean (4 std-3, budget raw 0 / 9831 jobs; 28s elab; verified clean rebuild reading
#print axioms — no sorryAx; adversarial main-verified). Constructs hjets for g^K=curvedRNCMetric κ
(κ<0) that the J4-553 collar amplitude data consumes, with per-field banked-vs-owed census + REWIRE.
- curved_hjets_at_gate: whole hjets bundle at constGate … cg (exact shape) from per-(τ,z)
  AmpGeometryBundle.HjetsShape supplier.
- curved_hjetsShape_of_pieces: HjetsShape at g^K = ⟨…⟩ of 7 parts (AmpGeometryBundle.hjets_assemble).
- curved_amplitudeDataOn_from_hjetsShape: ★ REWIRE — feeds curved_hjets_at_gate into J4-553's
  curved_amplitudeDataOn_at_gate ⟹ hOnCollar chart-jet carry collapsed to the scoped census.
- curved_hjets_residual(_intro): general-base residue ledger (no axioms).
★ PER-FIELD (grep-confirmed vs AmpGeometryBundle census): BANKED = openness+centre-membership, first
i-jet near 0 (chartField_firstJet_nhds_of_contDiffAt), second i-jet at 0 Q (GeneralBaseJets.chartField
_secondJet_general), amplitude jets hA1/hA2 (OnGateJets.ampField_pdiffAt, curved chart C²+det>0),
centre-value-1 (rhoRatio_center), the 3 centre identities ∑V·P=zᵢ/∑P²=1/∑V·Q=0 AT BASE 0. OWED = the
global ∀x first jet (chart C² only near image points) + the 3 centre identities at GENERAL base z
(base-0 banked, general lift owed) = AmpGeometryBundle.hjets_residual_carries curved-labelled.
ADVERSARIAL (main): non-vacuous g^K; discharged fields genuine chart facts; the 3 centre identities
CURVATURE-COMPATIBLE (normal-coordinate/geodesic radial GAUGE g^K satisfies WITH Ric≠0, normalization
not flatness); R/6≠0; banked/owed matches the pre-existing census — NO new soundness surface. HONEST:
a₁=R/6 CONDITIONAL — SHARPENS/wires on-collar chart-jet geometry (opaque hjets → 4-item census, most
banked); NOT unconditional; global ∀x jet + 3 general-base centre identities + hOffCollarTail +
convergence trio + measurability census + hsrc owed.
J4-555 = lift the general-base centre identities hVP/hPsq/hVQ for curvedRNCMetric κ (banked base-0
chartField_firstJet_center / chartField_centerJet_term_vanishes_base0 → general base z via the exact
geodesic radial gauge ∑ⱼ g_ij(x)xʲ=xᵢ, curvedRNCMetric_hgauge/metricGaussGauge_curvedRNC J4-523/524/
525) — highest-leverage remaining chart-jet piece; the global ∀x first jet is the harder C⁴ remainder.
OR hOffCollarTail. OR the convergence trio.

## J4-555 — curved radial-gauge (metric+inverse) + general-base center identities reduced to the pullback bridge [f26f7de8]
CurvedCenterIdentities.lean (6 std-3, budget raw 0 / 9832 jobs; 26s elab; verified clean rebuild
reading #print axioms — no sorryAx; adversarial main+Sol). Closes the metric-side radial gauge for
g^K UNCONDITIONALLY (incl. new inverse-gauge content) + reduces the 3 general-base center identities
to the geodesic pullback bridge ⟹ hjets owed residue shrinks to just the global ∀x first jet.
- curvedRNCMetric_radialGauge: ∑ⱼ g^K_{ij}(y)yʲ=yᵢ (re-export metricGaussGauge_curvedRNC).
- ★ curvedRNCInv_radialGauge (κ≤0): ∑ⱼ gi^K_{ij}(y)yʲ=yᵢ — NEW content from exact Sherman–Morrison
  inverse (per-term split + inv_mul_cancel₀, mirrors curvedRNCMetric_hinvF).
- curved_radialGauge_bundle; curved_centerIdentities_of_gaussPullback (the LIFT: hVP via metric gauge,
  hPsq via g^K(0)=δ, hVQ via metric−inverse gauge = sub_self); curved_centerIdentities_at_gate;
  curved_centerIdentities_discharge_residual (the 3 CENTRE fields of curved_hjets_residual PROVED given
  the bridge ⟹ residue → hGlobalJet).
★ HONEST SCOPING: the 3 center identities did NOT close from radial gauge alone — the .choose-built
uniformInverseChart W_z is controlled only near image points, so its jets P,Q at ambient 0 for GENERAL
base z = unbanked base-point (z-slot) chart regularity = the C⁴ remainder (blocker J3). Lift CONDITIONAL
on the geodesic normal-chart pullback bridge (hpullVP/hpullPsq/hpullVQ), which the radial gauge closes.
ADVERSARIAL (main+Sol): non-vacuous g^K (κ<0, Ric≠0, R/6≠0); CURVATURE-COMPATIBLE — inverse gauge uses
exact (κ/3) cancellation α=1−(κ/3)‖y‖², NOT Ricci-flatness, FAILS for gi:=δ off origin (no flat
shortcut; both gauges consumed, hVQ uses both). HONEST: a₁=R/6 CONDITIONAL — discharges the metric-side
radial gauge unconditionally + reduces center identities to the pullback bridge; NOT unconditional;
global ∀x first jet + hOffCollarTail + convergence trio + measurability census + hsrc remain.
J4-556 = the global ∀x first jet hGlobalJet (base-point z-slot chart regularity of the .choose-built
uniformInverseChart W_z — underpins the pullback bridge; the C⁴/C² remainder, blocker J3) OR
hOffCollarTail OR the convergence trio. ⚠ hGlobalJet = genuine .choose-witness base-point-regularity
frontier (ExpRhoReachability-style GENUINE-INPUT); may be un-bankable from the substrate — scope
honestly.

## J4-556 — CONSOLIDATION + ASSESSMENT (no brick): hGlobalJet verdict + the honest distance-to-unconditional curved a₁
Assessment-only (no file modified; baseline curved_a1_R6_fully_wired confirmed std-3 via existing pins).
★ hGlobalJet VERDICT (Sol-concurred): GENUINE .choose-witness substrate frontier — CARRIED, NOT
bankable from the jet-4 tower. hGlobalJet = the global ∀x first i-jet of uniformInverseChart
(curvedRNCMetric κ), the SOLE surviving member of the chart-jet residue after J4-555 (the 3 centre
identities discharged via the radial-gauge pullback bridge). Substrate chain all Classical.choose:
uniformFlow_tube_exists.choose → uniformFlowExp (regularity exposed only C²/C³ = contDiffAt2/3) →
uniformChart_exists (spec = eventual-left-inverse germ + ContDiffAt ℝ 2 W near image points ONLY) →
uniformInverseChart := (…).choose. (a) UN-BANKABLE from the object as defined (spec frozen at
C²-near-image-points; a pathological choose witness admissible off the collar, no uniform-in-z ambient
∀x). (b) mathematically TRUE (canonical exp_z⁻¹ is C⁴ on the injectivity ball by IFT from the C⁴
forward expMap_contDiffOn_four) but requires a SUBSTRATE REBUILD of uniformChart_exists to expose a
global/higher-order (C⁴, uniform-in-z) spec — a rebuild, not a derivation. THE HONEST TERMINAL for the
chart-jet thread.
★★ CONSOLIDATED RESIDUAL CLASSIFICATION of curved_a1_R6_fully_wired (the honest distance):
(A) IRREDUCIBLE-CARRIED geometric/substrate: hGlobalJet (substrate terminal, hard), hsrc (ContDiff ℝ ∞
transportCoeff SDW source = legit geometric input), hOffCollarTail (off-collar Gaussian tail), setup/
frame data (hframeK→{0}, hChr C∞, hK compact, hK0 0∈K = defining data not "owed").
(B) ANALYTIC-CLOSABLE bookkeeping (mechanical wiring, no new physics): convergence trio (dataLevi/
E-comb hDa_ec/hLap/…/hPd2conv/hInter/hII_lo/hEcomb), boundary (hBoundaryLim/hbdry/hmod/hsup/hmass/
hmassone), measurability/window census (W2/Section-G/Section-H/gate-pkg hpkgBound/hmemS0/hopenS0/hS1/
hmeas*/raw/window), capped Gaussian dominations (hAdom/hAdomHeat/hFdomW/hAdom2cap/hEdom/hFdom). [hII_hi
MemAdjHi already discharged J4-552.]
HONEST: a₁=R/6 for g^K CONDITIONAL on {A∪B}; Class B = large-but-mechanical backlog closable by wiring;
Class A = the genuine residue, hGlobalJet the one substrate-limitation terminal. Coefficient
n(n−1)κ/6≠0 unaffected.
J4-557 = PRIMARY: collar-localization surgery on hGlobalJet — trace what the amplitude machinery
(curved_amplitudeDataOn_from_hjetsShape → AmplitudeDataOnCollar → collar hD2HexpandOn) actually
consumes; if only collar/overlap, REDEFINE the residue to the collar/overlap first-jet (BANKED via
chartField_firstJet_nhds_of_contDiffAt) dropping hGlobalJet as FALSE GENERALITY; else re-tag hGlobalJet
as an explicit LABELLED geometric input (option-b, same honest carry as a₁=R/6). SECONDARY: thinnest
class-B (gate-package hmemS0/hopenS0 for constGate, or hPd2conv if banked-instantiable).

## J4-557 — hGlobalJet was FALSE GENERALITY: collar-localized (dropped); the hard chart-jet terminal removed [c0f43ead]
CurvedChartJetsCollar.lean (8 std-3, budget raw 0 / 9833 jobs; verified clean rebuild reading #print
axioms — no sorryAx; adversarial main-verified). MACHINE-VERIFIED (not argued) that the ambient ∀x
first-jet hGlobalJet (J4-556's sole hard chart-jet substrate frontier) is FALSE GENERALITY — DROPPED.
★ TRACE (machine-verified): hjets first-jet feeds AmplitudeDataOnCollar.hD2HexpandOn_concrete →
witnessSecondXDeriv_expand_bridge_rho → ChartJetHessian.gaussComp_amp_center_decomp → gaussComp_pd_pd.
The ambient ∀x jet hV1 is used at ambient generality in EXACTLY ONE place (the funext writing ∂ᵢ(gauss
Ddim∘V) as a GLOBAL equality); but pd=deriv is a LOCAL germ operator so the outer partial only reads
=ᶠ[𝓝 0] — funext strictly stronger than needed; every other hV1 use is at centre x₀=0. Ambient ∀x =
proof-convenience over-reach, NOT genuine.
- pdiffAt_of_eventuallyEq (germ transfer); gaussComp_pd_pd_nhds / gaussComp_amp_pd_pd_nhds /
  gaussComp_amp_center_decomp_nhds (terminal Leibniz consumer from =ᶠ[𝓝 0], IDENTICAL conclusions to
  the ∀x lemmas; funext → pd_congr_of_eventuallyEq); witnessSecondXDeriv_expand_bridge_rho_nhds /
  hD2HexpandOn_concrete_nhds (whole collar D2 bridge re-plumbed, hGlobalJet dropped, conclusion
  unchanged); curved_collarFirstJet_banked (near-centre jet for g^K BANKED via chartField_firstJet_
  nhds_of_contDiffAt ← ContDiffAt ℝ 2 (W z) 0); curved_hjets_residual_collar(_intro) (refactored residue
  carrying banked hCollarJet in place of hGlobalJet).
★ SOUND (no vacuity): each consumer's _nhds counterpart has IDENTICAL conclusion from the strictly-
weaker =ᶠ[𝓝 0] hyp ⟹ discharges the same goal from a banked hyp, not a silent weakening; ∀ᶠ x in 𝓝 0
strictly weaker than ∀x (not a re-label). ADVERSARIAL: non-vacuous g^K (κ<0, Ric≠0, R/6≠0). HONEST:
a₁=R/6 CONDITIONAL — removes ONE substrate terminal (hGlobalJet), machine-backed; updated chart-jet
residue = banked collar first jet + 3 general-base centre identities (J4-555); NOT unconditional; hsrc,
hOffCollarTail, convergence trio, measurability census remain.
J4-558 = structural field-erasure: replace the ambient ∀x first-jet field in AmpGeometryBundle.HjetsShape
(+ the hjets field of amplitudeDataOn_concrete / curved_amplitudeDataOn_from_hjetsShape) with the
=ᶠ[𝓝 0] form, routing hD2Hexpand through hD2HexpandOn_concrete_nhds — erases hGlobalJet from the LIVE
bundle structures (not just the residue ledger). OR thinnest class-B (gate-package hmemS0/hopenS0,
hPd2conv) OR hOffCollarTail OR hsrc.

## J4-558 — Class-B census member hmemS0 discharged for g^K (gate-centre membership) [ad115a43]
CurvedA1ClassB.lean (2 std-3, budget raw 0 / 9834 jobs; 29s elab; verified clean rebuild #print axioms
no sorryAx). curved_hmemS0_at_gate / _of_lt: (0∈K)→0∈constGate(curvedRNCMetric κ)(curvedRNCInv κ)hChr
hK c 0, via banked ConcreteGateInstantiation.hS0_concrete (φ_0 0=0 via uniformFlowExp_zero; constGate…
c 0 = uniformFlowExp… 0 '' ball 0 c by defeq, pure interface rethread). ★ SIBLINGS NOT THIN: hopenS0/
hS1 need chart-reach smallness c<δ₀ (gatedWitnessN1_hEboundW_le_lin_CONST via uniformInverseChart_
huniformChart) — the capstone binder does not assume c<δ₀, so smallness-gated (⟹ could be discharged by
instantiating the capstone with small gate c<δ₀, a legit base-point choice — deferred). ADVERSARIAL:
non-vacuous g^K (κ<0, Ric≠0), genuine membership fact from banked geometry supplier, R/6 unaffected.
HONEST: a₁=R/6 CONDITIONAL — shrinks Class-B by one binder; hsrc + hOffCollarTail + convergence trio +
hopenS0/hS1(smallness) + measurability census remain.
J4-559 = a measurability census member (hmeasLo/hmeasHi/hmeas2Lo or W2 hFmeas/hWmeas family) via the
banked J4-527/528 machinery (vanVleckGatedWitness_slice_aestronglyMeasurable / heatParametrix_uncurry_
measurable_from_geometry, no smallness needed) OR begin hsrc (ContDiff ℝ ∞ transportCoeff SDW source,
genuine geometric input).

## J4-559 — Class-B measurability member hWmeas discharged for g^K (witness-slice AEStronglyMeasurable) [b4ce38e6]
CurvedA1ClassBMeas.lean (1 std-3, budget raw 0 / 9835 jobs; verified clean rebuild #print axioms no
sorryAx). curved_hWmeas_at_gate (hSm)(hVmap): ∀τ AEStronglyMeasurable (vanVleckGatedWitness (curved
RNCMetric κ)(curvedRNCInv κ) hChr hK (constGate…c)a b τ 0) volume — EXACT capstone hWmeas binder, via
banked CurvedRNCWitnessMeas.curvedRNC_hWmeas (J4-527/528, curved smoothness bundle → WitnessMeasDeriv.
vanVleckGatedWitness_slice_aestronglyMeasurable). CARRIED: {hSm gate-set-preimage MeasurableSet, hVmap
base-chart pullback AEStronglyMeasurable} — curvature-independent bookkeeping, NOT smallness. (carry-free
variant produces ∃δ₀∀c<δ₀ smallness, does NOT match the fixed-c binder.) ADVERSARIAL: non-vacuous g^K
(κ<0, Ric≠0), genuine AEStronglyMeasurable from banked supplier, R/6 unaffected. HONEST: a₁=R/6
CONDITIONAL — shrinks Class-B measurability by one; hsrc + hOffCollarTail + convergence trio + remaining
census (hmeasLo/hmeasHi/hmeas2Lo, W2 family, Section-G hMeasFII/hFmeas_d, smallness-gated hopenS0/hS1)
remain.
J4-560 = next measurability member hMeasFII/hFmeas_d (Section-G base-witness ∫z slice measurability, via
ErrorKernelJointMeas.heatParametrix_uncurry_measurable_from_geometry + Fubini/Bochner) OR the convergence
trio OR hOffCollarTail OR hsrc.

## J4-560 — Class-B census member hopenS0 discharged for g^K (gate-centre openness, modulo gate-smallness) [6786e6b4]
CurvedA1ClassBMeas2.lean (3 std-3, budget raw 0 / 9836 jobs; 29s elab; main verified rebuild #print
axioms no sorryAx). curved_hopenS0_at_gate: ∃c₀>0, ∀c∈(0,c₀), (0∈K → IsOpen (constGate (curvedRNCMetric
κ)(curvedRNCInv κ) hChr hK c 0)), via banked CompactTubeLemma.flowBall_gateRadius_floor (=
ConcreteGateAssembly.reachableGate_concrete). Needs ONLY hChr+hK (thinner than hS1). CARRIED (honest):
gate-smallness 0<c<c₀ (chart reach c<δ₀) as the ∃c₀ antecedent — constrains the gate parameter (capstone
binds c with only b<c, no upper bound), so closable only for small gate c∈(b,c₀), a legit base-point
choice. ADVERSARIAL: non-vacuous g^K (κ<0, Ric≠0), genuine openness fact from banked supplier, R/6
untouched. HONEST: a₁=R/6 CONDITIONAL. ★ CENSUS TALLY: 3 drained (hmemS0/hWmeas/hopenS0), ~12-15 remain
(s-slice ∫z convolutions hmeasLo/hmeasHi/hmeas2Lo, W2 hFmeas/hFint/hF'meas, Section-G hMeasFII/hFmeas_d/
hFint_d/hF'meas_d, leviSeries hffro_meas/hfmov_meas, hInnerCont, hS1, interval-integrabilities) — ~1/5
drained; + hsrc/hOffCollarTail geometric + convergence trio.
J4-561 = hS1 (tripleHEmeas) for g^K via ConstRadiusGateExport.tripleHEmeas_AT_CONSTRADIUS_GATE /
constRadius_package_and_S1 (the const-radius gate package bundling hpkgBound+hmemS0+hopenS0+hS1),
carrying the same c<δ₀ smallness + the curved transport-coeff smoothness hu/hw (the genuine geometric
residue) — pairs naturally with this hopenS0. OR a measurability member OR hOffCollarTail OR hsrc.

## J4-561 — Class-B hS1 (tripleHEmeas) discharged for g^K; const-radius GATE PACKAGE COMPLETE [dc4983d0]
CurvedA1GateS1.lean (2 std-3, budget raw 0 / 9837 jobs; main verified rebuild #print axioms no sorryAx).
curved_hS1_at_gate: ∃δ₀>0, c<δ₀ → HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ)(curvedRNCInv κ)
(vanVleckGatedWitness … (constGate…c)a b) — EXACT capstone hS1 binder, via banked ConstRadiusGateExport.
tripleHEmeas_AT_CONSTRADIUS_GATE (gate match definitional; g/gi geometry from curvedRNCMetric_contDiff/
curvedRNCInv_contDiff/curvedRNCMetric_hgpos + .continuous.measurable shadows, κ<0 via hκ.le). CARRIED
(labelled): (1) transport-coeff smoothness hu:∀k ContDiff ℝ ⊤ (transportCoeff …) = the hsrc-family
geometric input; (2) gate-smallness c<δ₀. ★ CONST-RADIUS GATE PACKAGE COMPLETE for g^K: {hpkgBound
(J4-536), hmemS0 (J4-558), hopenS0 (J4-560), hS1 (this)} all 4 individually discharged (each modulo
honest gate-smallness). ADVERSARIAL: non-vacuous g^K (κ<0, Ric≠0), tripleHEmeas genuine from banked
supplier, hu satisfiable (C^∞ van-Vleck transport recursion), R/6 untouched. HONEST: a₁=R/6 CONDITIONAL
— gate package done; carried hsrc-family hu + hOffCollarTail + convergence trio + remaining measurability
census (hmeasLo/hmeasHi/hmeas2Lo/hMeasFII/hFmeas_d/…) owed. CENSUS: gate package (4) done; measurability
carriers ~10-12 remain.
J4-562 = drain the next measurability carrier (s-slice ∫z convolution hmeasLo/hmeasHi/hmeas2Lo via
SliceMeasurability.hmeas*_slice, OR Section-G hMeasFII/hFmeas_d via heatParametrix_uncurry_measurable_
from_geometry + Fubini) OR bundle the full gate package into curved_constRadius_package_at_gate (needs
~14 curved inputs from curvedRNC_geomGaugeBundle — non-thin) OR hOffCollarTail/hsrc/convergence trio.

## J4-562 (1ef68070) — Class-B s-slice ∫z measurability family for g^K
CurvedA1ClassBMeas3.lean: three measurability census binders of `curved_a1_R6_fully_wired`
instantiated at g^K = curvedRNCMetric κ (κ<0), each a literal application of banked
`SliceMeasurability.{hmeasLo_slice,hmeasHi_slice,hmeas2Lo_slice}` (J4-383):
`curved_hmeasLo_at_gate` (heatOp·leviSeries s-slice AESMeas on uIoc 0 (u−εₘ)),
`curved_hmeasHi_at_gate` (Hi window uIoc (u−εₘ) u), `curved_hmeas2Lo_at_gate`
(witnessSecondXDeriv·leviSeries per-i on uIoc 0 (u−εₘ)) + `_curved_satisfiable`
(Ric(0)≠0, κ≠0∧n≥2). Carries {hUT,hεU,hHeatCont/hSecCont,hBcont} — curvature-independent
window + joint-continuity analytic carries (mirrors J4-559 {hSm,hVmap}). std-3, budget raw 0,
9838 jobs. Adversarial gate verified by main (genuine AESMeas from banked supplier, not True,
not a₁ conclusion; R/6 untouched). MEASURABILITY CENSUS: 4 of ~10-12 drained for g^K
(hWmeas J4-559 + this family). Remaining ~7-8: W2 hFmeas/hFint/hF'meas; Section-G
hMeasFII/hFmeas_d/hFint_d/hF'meas_d; leviSeries hffro_meas/hfmov_meas; hInnerCont (needs
genuine curved bound — deferred). a₁=R/6 CONDITIONAL: residual {hsrc,hOffCollarTail} + Class-B
backlog still owed. J4-563 = W2 diff-under-∫ hFmeas/hF'meas (hunt witnessFieldDeriv-slice supplier).

## J4-563 (33d48c8f) — Class-B W2 diff-under-∫ measurability carriers for g^K
CurvedA1ClassBMeas4.lean: the two W2 (differentiation-under-the-integral) measurability binders
of `curved_a1_R6_fully_wired` at g^K=curvedRNCMetric κ (κ<0): `curved_hFmeas_at_gate`
(witnessFieldDeriv·leviSeries s-slice AESMeas on uIoc 0 (u−εₘ), per m,i,u,w),
`curved_hFpmeas_at_gate` (witnessFieldDeriv2·leviSeries, per m,i,u) — each a literal application
of a banked geometry-generic supplier `hFmeas_slice`/`hFpmeas_slice` (proved via the J4-383
Fubini core SliceMeasurability.sliceMeas_of_jointCont). + `_curved_satisfiable`
(curvedRNCMetric_ricci_trace_diag_ne, κ≠0∧n≥2). Carries {hUT,hεU,hFieldCont/hField2Cont,hBcont}
— curvature-independent window + strip joint-continuity (mirrors J4-562). std-3, budget raw 0,
9839 jobs. Adversarial gate verified by main (genuine AESMeas from banked core, not True, not
a₁ conclusion; R/6 untouched; suppliers proved via sliceMeas_of_jointCont). MEASURABILITY CENSUS:
6 carriers drained for g^K (hWmeas J4-559, hmeasLo/hmeasHi/hmeas2Lo J4-562, hFmeas/hF'meas J4-563).
hFint SCOPED OUT (IntervalIntegrable — needs Gaussian domination, not measurability-thin).
Remaining ~5-6: Section-G hMeasFII/hFmeas_d/hFint_d/hF'meas_d; leviSeries hffro_meas/hfmov_meas;
hInnerCont (DEFER, needs genuine curved bound). + convergence trio + Class-A {hsrc, hOffCollarTail}.
a₁=R/6 CONDITIONAL. J4-564 = Section-G ∫z member hMeasFII/hFmeas_d via
ErrorKernelJointMeas.heatParametrix_uncurry_measurable_from_geometry + Fubini.

## J4-564 (Section-G error-kernel ∫z-slice measurability carrier hMeasFII for g^K)
CurvedA1ClassBMeas5.lean: `hMeasFII_slice` (geometry-generic supplier: s ↦ ∫z vanVleckGatedWitness
g gi … (u−s) 0 z · leviSeries … s z 0 AESMeas on uIoc 0 u, via banked sliceMeas_of_jointCont on
Ioo 0 u + Ioo_ae_eq_Ioc null-endpoint transfer) + `curved_hMeasFII_at_gate` (g^K instance = exact
capstone hMeasFII binder) + `_curved_satisfiable`. First factor = RAW gated witness (error-kernel
numerator), no εₘ floor. Carries {hUT,hU0,hFIICont,hBcont} — curvature-independent. std-3, budget
raw 0, 9840 jobs. Adversarial gate verified by main (supplier proved via sliceMeas_of_jointCont not
axiomatized; genuine AESMeas; R/6 untouched). MEASURABILITY CENSUS: 7 drained for g^K (hWmeas J4-559,
hmeasLo/Hi/hmeas2Lo J4-562, hFmeas/hF'meas J4-563, hMeasFII J4-564). Remaining Section-G: hFmeas_d
(unconstrained shift cc−s — NOT literal banked instance, harder), hF'meas_d (deriv-first-factor,
needs τ-derivative-kernel joint-cont carry). + leviSeries hffro_meas/hfmov_meas; hInnerCont (DEFER,
curved bound); hFint/hFint_d (DEFER, IntervalIntegrable need domination). + trio + Class-A {hsrc,
hOffCollarTail}. a₁=R/6 CONDITIONAL. J4-565 = hF'meas_d (deriv-first-factor supplier from
sliceMeas_of_jointCont with Φ τ z := deriv (fun r => vanVleckGatedWitness … r 0 z) τ + joint-cont carry).

## J4-565 (Section-G error-kernel-DERIVATIVE ∫z-slice measurability carrier hF'meas_d for g^K)
CurvedA1ClassBMeas6.lean: `hFpmeas_d_slice` (geometry-generic supplier: ∀m,u∈U AESMeas
(s ↦ ∫z deriv (fun r => vanVleckGatedWitness g gi … r 0 z) (u−s) · leviSeries … s z 0) on
uIoc 0 (u−εₘ), via banked sliceMeas_of_jointCont with τ-derivative first factor, εₘ-floored Lo
window) + `curved_hFpmeas_d_at_gate` (g^K instance = exact capstone hF'meas_d binder) +
`_curved_satisfiable`. Carries {hUT,hεU,hFIIDerivCont,hBcont} — curvature-independent
(τ-derivative-kernel joint continuity is the owed carry). std-3, budget raw 0, 9841 jobs.
Adversarial gate verified by main (supplier PROVED via sliceMeas_of_jointCont not axiomatized;
genuine AESMeas; R/6 untouched). MEASURABILITY CENSUS: 8 drained for g^K (hWmeas J4-559,
hmeasLo/Hi/hmeas2Lo J4-562, hFmeas/hF'meas J4-563, hMeasFII J4-564, hF'meas_d J4-565). Remaining:
hFmeas_d (raw-witness Section-G, unconstrained shift cc — harder), leviSeries hffro_meas/hfmov_meas.
+ DEFER hInnerCont (curved bound), hFint/hFint_d (IntervalIntegrable need domination). + trio +
Class-A {hsrc, hOffCollarTail}. a₁=R/6 CONDITIONAL. J4-566 = hFmeas_d OR leviSeries hffro_meas/hfmov_meas.

## J4-566 (leviSeries "frozen"/"moving" z-slice measurability carriers hffro_meas/hfmov_meas for g^K)
CurvedA1ClassBMeas7.lean: STRUCTURAL FINDING — hffro_meas/hfmov_meas are POINTWISE-in-z
AEStronglyMeasurable at a fixed time (leviSeries analogue of hWmeas J4-559), NOT ∫z-slices; and
hfmov_meas m u = hffro_meas (u−epsSeq m), so ONE supplier serves both. `leviSlice_meas`
(geometry-generic: ∀u AESMeas (fun z => leviSeries (heatOp g gi W) u z 0) volume, via banked
Continuous.aestronglyMeasurable) + `curved_hffro_meas_at_gate` + `curved_hfmov_meas_at_gate`
(g^K instances = exact capstone binders) + `_curved_satisfiable`. Single carry hLcont (spatial
continuity of Levi slice ∀ time) — curvature-independent, lighter than J4-565. std-3, budget raw 0,
9842 jobs. Adversarial gate verified by main (supplier PROVED via (hLcont u).aestronglyMeasurable
not axiomatized; genuine AESMeas; R/6 untouched). MEASURABILITY CENSUS: 10 drained for g^K (hWmeas
J4-559, hmeasLo/Hi/hmeas2Lo J4-562, hFmeas/hF'meas J4-563, hMeasFII J4-564, hF'meas_d J4-565,
hffro_meas/hfmov_meas J4-566). ONLY hFmeas_d (unconstrained shift cc — needs MapsTo-per-shift or
full-window uIoc+Ioo_ae_eq_Ioc) remains open on the measurability side. + DEFER hInnerCont (curved
bound), hFint/hFint_d (domination). + convergence trio + Class-A {hsrc, hOffCollarTail}. a₁=R/6
CONDITIONAL. J4-567 = hFmeas_d (last measurability carrier) OR PIVOT to domination-integrabilities
hFint/hFint_d (reuse capped J4-530..537 lemmas) OR convergence trio OR hOffCollarTail/hsrc.

## J4-567 (LAST measurability carrier hFmeas_d free-anchor Section-G for g^K — CENSUS COMPLETE)
CurvedA1ClassBMeas8.lean: `curved_hFmeas_d_at_gate` (∀m,u∈U,cc AESMeas (s ↦ ∫z vanVleckGatedWitness
g^K … (cc−s) 0 z · leviSeries … s z 0) on uIoc 0 (u−εₘ) — matches capstone hFmeas_d binder VERBATIM,
FREE anchor cc) + `_curved_satisfiable`. STRUCTURAL FINDING: sliceMeas_of_jointCont CANNOT serve
(cc free ⟹ shift cc−s on positive-measure set with τ≤0; εₘ-floor/null-endpoint trick fails; a
Continuous carry = vacuity trap, witness singular at (0,0)). Banked InnerMeasFubini.hFmeas_concrete
(engine gatedWitnessShift_joint_aesm gated-INDICATOR joint (s,z) lever + leviJoint + Fubini) is the
ONLY surviving route. Carries {hKm,hSm0,hInner,hLeviJoint} = genuine MEASURABILITY (measurable off
null singular set ⟹ AESMeas — honest not continuity; Sol-confirmed). Main verified: at-gate matches
capstone verbatim; hFmeas_concrete + gatedWitnessShift_joint_aesm PROVED theorems (0 axioms in
InnerMeasFubini.lean); carries satisfiable not vacuous; R/6 untouched. std-3, budget raw 0, 9843 jobs.
★★ MEASURABILITY CENSUS COMPLETE for g^K — 11 carriers all discharged (J4-536/558/559/560/561/562/
563/564/565/566/567). RESIDUAL now = HARDER analytic/geometric core: {hsrc (SDW transportCoeff C^∞),
hOffCollarTail (off-collar Gaussian tail)} geometric + {convergence trio, hFint/hFint_d (need genuine
Gaussian DOMINATION), hInnerCont (curved bound)} analytic — NOT more thin measurability bookkeeping.
a₁=R/6 CONDITIONAL. J4-568 PIVOT = hFint/hFint_d domination (reuse capped J4-530..537 lemmas) OR
convergence trio OR hOffCollarTail/hsrc OR honest TERMINAL WRITEUP.

## J4-568 (interval-integrability hFint + hFint_d for g^K via CAPPED Gaussian domination — analytic core PIVOT)
CurvedA1ClassBFint.lean: `pairing_intervalIntegrable_capped` (geometry-generic ENGINE: s ↦ ∫z A(u−s) 0 z
· F s z 0 IntervalIntegrable on [0,u−ε] from ε-FLOORED Gaussian domination of A + (0,Tc] domination of F
+ s-slice measurability; ε-capped variant of banked DaLimEasyTranche.pairing_intervalIntegrable via
gaussDdim_pairing_integral → s-uniform const → Integrable.mono') + `curved_hFint_at_gate`
(A=witnessFieldDeriv, matches capstone hFint) + `curved_hFint_d_at_gate` (A=raw vanVleckGatedWitness,
matches hFint_d) + `_curved_satisfiable`. ★ DOMINATION TRUE FOR g^K: window [0,u−εₘ] samples A only at
τ=u−s≥εₘ ⟹ engine needs only CAPPED per-m bound (εₘ≤τ≤T), genuinely true (τ^{−1/2}≤εₘ^{−1/2} into CA_m,
hAdom2cap mechanism J4-530..537); clean whole-time witnessFieldDeriv bound FALSE (CappedAdom2Audit D3);
raw witness no blow-up. Carries {hAdom capped, hFdom, hFzero, hmeas banked} — IntervalIntegrable engine
DISCHARGED. Main verified: at-gate matches capstone verbatim; hAdom is εₘ-floored (not false clean hAdom2);
engine proved (Integrable.mono'); satisfiable not vacuous; R/6 untouched. std-3, budget raw 0, 9844 jobs.
Agent ~24min/61 tool-uses genuine work. RESIDUAL: hFint/hFint_d off the analytic list (modulo their capped
hAdom carry to be banked). Remaining = {hsrc, hOffCollarTail} geometric + {convergence trio, hInnerCont} +
the capped hAdom sources. a₁=R/6 CONDITIONAL. J4-569 = source capped hAdom (witnessFieldDeriv per-m Gaussian
domination from WideSliverBoundary/witnessFieldDeriv_gate_envelope) OR hInnerCont OR convergence trio.

## J4-569 (source hFint's capped hAdom — bank ε-absorption, scope hcrude residual)
CurvedA1FintAdomSource.lean: `sqrt_crude_to_capped` (PROVED τ^{−1/2} ε-absorption arithmetic;
first-deriv sibling of banked EveryCeilingFamilies.gaussDdim_crude_to_capped: whole-time
Ccrude·(√τ)⁻¹·gaussDdim on (0,Tc] ⟹ capped (Ccrude·(√εₘ)⁻¹)·gaussDdim on [εₘ,Tc] via inv_le_inv₀+
Real.sqrt_le_sqrt) + `curved_hFint_hAdom_at_gate` (EXACT hAdom binder consumed by
CurvedA1ClassBFint.curved_hFint_at_gate, sourced from crude envelope hcrude, CA m = Ccrude·(√(epsSeq m))⁻¹
m-DEPENDENT) + `curved_hFint_at_gate_via_crude` (DEMONSTRATOR: full hFint IntervalIntegrable re-derived
with hAdom slot FILLED — plugs in verbatim) + `_curved_satisfiable`. Main verified: CA m m-dependent
(capped not false-clean); sqrt_crude_to_capped proved (inv_le_inv₀+sqrt_le_sqrt+mul_le_mul); demonstrator
confirms binder match; hcrude satisfiable for g^K (genuine τ^{−1/2} crude bound, banked-shape). std-3,
budget raw 0, 9845 jobs. ★ HONEST PARTIAL: ε-absorption arithmetic BANKED; hcrude (crude first-derivative
envelope) remains CARRIED — no WideAmplitudeData.first_domination exists yet (only zeroth/second;
curvedRNC_witnessSecondXDeriv_dom_crude is the τ^{−1} SECOND-deriv analog). RESIDUAL: {hcrude, hFint_d's
hAdom} domination sources + {hsrc, hOffCollarTail} geometric + {convergence trio, hInnerCont} analytic.
a₁=R/6 CONDITIONAL. J4-570 = source hcrude (build WideAmplitudeData.first_domination = τ^{−1/2}
witnessFieldDeriv curved envelope via WitnessDerivDomination.witnessFieldDeriv_gate_envelope + near-isometry
chart-Gaussian) OR hFint_d's raw-witness hAdom (from banked CurvedRNCBaseWitnessDomAdom, order-0 whole-time).

## J4-570 (FULL-source hFint_d's order-0 hAdom for g^K from banked base-witness domination)
CurvedA1FintDAdomSource.lean: `curved_hFint_d_hAdom_at_gate` (∃ c>0,wA>0,C≥0, ∀m τ epsSeq m≤τ→τ≤T→∀z
|vanVleckGatedWitness g^K…(constGate…c)a b τ 0 z|≤C·gaussDdim(wA·τ)(0−z), obtained from banked
CurvedRNCBaseWitnessDomAdom.curvedRNC_baseWitness_dom_adom frozen-p=0 window conjunct hWDom [CW const]
via rw[zero_sub,gaussDdim_neg]; C=CW m-INDEPENDENT constant, honest for order-0 no blow-up) +
`curved_hFint_d_at_gate_via_source` (DEMONSTRATOR: feeds sourced hAdom into curved_hFint_d_at_gate
(CA:=fun _=>C), chains to full IntervalIntegrable — plugs verbatim) + `_curved_satisfiable`. Carries
ONLY hw (amplitude C^∞ smoothness, hsrc-family). Main verified: ∃ values are the BANKED c/lam/CW (not
vacuous); base bound PROVED; demonstrator confirms match; C m-independent honest (order-0). std-3,
budget raw 0, 9846 jobs. ★ FULL close (cleaner than hFint J4-569 which left hcrude carried) — hFint_d's
hAdom removed from carry pile modulo hw. RESIDUAL: {hcrude (hFint's τ^{−1/2} first-deriv envelope —
still carried), hsrc, hOffCollarTail} + {convergence trio, hInnerCont}. a₁=R/6 CONDITIONAL. J4-571 =
source hcrude (build WideAmplitudeData.first_domination τ^{−1/2} witnessFieldDeriv curved envelope) OR
hInnerCont OR convergence trio.

## J4-571 (source hFint's crude first-derivative envelope hcrude for g^K — width-transfer core + hFar residual)
CurvedA1FintHcrudeSource.lean: `witnessFieldDeriv_wide_crude` (THE MISSING first_domination base-bound,
honest sibling of banked WideAmplitudeData.second_domination one power weaker (√τ)⁻¹ not τ⁻¹, via banked
FixedFlowGateData.poly_absorb 0/1) + `curved_hFint_hcrude_at_gate` (EXACT whole-space hcrude census binder
for g^K, Ccrude·(√τ)⁻¹·gaussDdim(wA·τ)(0−z), glued over 3 z-regions: z∉K→BANKED witnessFieldDeriv_offGate_eq_zero;
z∈K,‖z‖<r→proved §A + carried hFirstEnv; z∈K,‖z‖≥r→carried hFar; τ^{−1/2} prefactor kept) +
`curved_hFint_hAdom_via_hcrude_at_gate` (DEMONSTRATOR: hcrude→J4-569 ε-absorption→per-m capped hAdom,
plugs verbatim) + `_curved_satisfiable`. Main verified: conclusion MATCHES hcrude binder; τ^{−1/2} prefactor
kept every branch (not false clean); off-gate BANKED; carried hFirstEnv+hFar satisfiable geometric envelopes
(banked-shape, true for g^K); poly_absorb PROVED; demonstrator confirms chain. std-3, budget raw 0, 9847 jobs.
★ HONEST PARTIAL: hcrude reduced from opaque carry to {proved width-transfer core + banked off-gate} ⊕
{hFirstEnv (narrow chart-image first-jet) + hFar (far-field annulus — the PRECISE unbanked blocker)}. Both
hFint domination carries now addressed (hAdom order-0 FULL J4-570; hcrude first-deriv PARTIAL J4-571).
a₁=R/6 CONDITIONAL. J4-572 = hFar (far-field annulus envelope, the precise blocker) OR hFirstEnv OR hInnerCont
OR convergence trio.

## J4-572 (source hFint hcrude's far-field annulus envelope hFar for g^K, modulo carried hlam4: 4≤lam)
CurvedA1FintHFarSource.lean: `curved_hFint_hFar_at_gate` (EXACT hFar binder consumed by
curved_hFint_hcrude_at_gate: ∃ Cfar≥0 ∀i τ z∈K ¬(‖z‖<r) |witnessFieldDeriv g^K…i τ 0 z|≤
Cfar·(√τ)⁻¹·gaussDdim(lam·τ)z — on the annulus 0 STILL∈gate ⟹ banked ON-GATE
CConvV2WitnessStar.witnessFieldDeriv_starWide_onGate [Cstar·(√τ)⁻¹·gaussDdim(4τ)z, GLOBAL near-isometry
coercivity ½·rncRadialSq z≤rncRadialSq(W₀ z)] widened gaussDdim(4τ)≤√(lam/4)ⁿ·gaussDdim(lam·τ) via
HeatResidualBound.gaussDdim_le_gaussDdim_chart; (√τ)⁻¹ kept) + `curved_hFint_hcrude_via_hFar_at_gate`
(DEMONSTRATOR: chains hFar+carried hFirstEnv into curved_hFint_hcrude_at_gate → whole-space hcrude
verbatim) + `_curved_satisfiable`. Main verified: conclusion MATCHES hFar binder; on-annulus on-gate
argument sound (0∈gate); base starWide bound PROVED; (√τ)⁻¹ kept; demonstrator confirms chain; R/6
untouched. ⚠ CARRIED hlam4:4≤(curvedGate).lam — NEW width-compat scalar; gate exposes only 1<lam
(near-isometry ∃), 4≤lam OWED (not provable from interface, NOT provably false — larger lam relaxes
1/lam<1-η ⟹ gate-widening admissible). + shared {hSopen,hgate0,hdata}. std-3, budget raw 0, 9848 jobs.
★ hcrude now has ONLY hFirstEnv left on its analytic side (off-gate + on-gate width transfer proved
inside; hFar sourced modulo hlam4). RESIDUAL: {hlam4, hFirstEnv (hcrude's last carrier), hsrc/hw,
hOffCollarTail} + {convergence trio, hInnerCont}. a₁=R/6 CONDITIONAL. J4-573 = hFirstEnv (chart-image
first-jet two-term envelope, sibling of banked witnessSecondXDeriv_chartImage_expand — makes hcrude
fully sourced modulo hlam4) OR hInnerCont OR convergence trio.

## J4-573 (FULL-source hcrude's on-gate chart-image first-jet envelope hFirstEnv for g^K)
CurvedA1FintHFirstEnvSource.lean: `curved_hFint_hFirstEnv_at_gate` (EXACT hFirstEnv binder consumed by
curved_hFint_hcrude_at_gate: ∃A₀ A₁≥0, ∀i τ z∈K ‖z‖<r |witnessFieldDeriv g^K…i τ 0 z|≤
(A₀+A₁·(rncRadialSq z/τ))·(√τ)⁻¹·gaussDdim τ (W₀ z) — from banked EXACT Leibniz
CConvV2WitnessStar.witnessFieldDeriv_productRule + Cauchy–Schwarz CConvV2ChartComparison.numerator_le_radial_mul;
Gaussian gradient √(r²_chart/τ) dominated via √x≤1+x; A₀:=√n·L·Ba/2+Bd·√T, A₁:=√n·L·Ba) +
`curved_hFint_hcrude_via_hFirstEnv_hFar_at_gate` (DEMONSTRATOR: hFirstEnv + J4-572 hFar → hcrude verbatim)
+ `_curved_satisfiable`. ⚠ NEW scalar (hdata bundle): UPPER near-isometry rncRadialSq(W₀ z)≤2·rncRadialSq z
— companion of J4-572's LOWER ½·rncRadialSq z≤rncRadialSq(W₀ z) (two-sided ½r≤r_chart≤2r); satisfiability
audited NOT provably false (z=0→0≤0; flat→r≤2r; true for near-isometry RNC chart). Main verified: conclusion
matches hFirstEnv; (√τ)⁻¹+A₁·(r²/τ) kept; base bounds PROVED (productRule+numerator); new scalar satisfiable;
R/6 untouched. std-3, budget raw 0, 9849 jobs. ★ hcrude now FULLY SOURCED modulo {hlam4, hdata-family}:
3 glued regions = off-gate vanishing (banked) + on-gate two-term hFirstEnv (J4-573) + far-field hFar (J4-572).
RESIDUAL: {hlam4 (4≤lam), hdata-family (2-sided near-isometry + Jacobian/amplitude bounds), hsrc/hw,
hOffCollarTail} + {convergence trio, hInnerCont}. a₁=R/6 CONDITIONAL. J4-574 = discharge hlam4 by gate-widening
(chart_width_gate) OR hInnerCont OR convergence trio.

## J4-574 (discharge hFar's hlam4 at an admissible widened gate curvedGate4 for g^K)
CurvedA1FintHlam4.lean: VERDICT route (a) REJECTED (4≤curvedGate.lam FALSE — lam=1/c+1 can be <4, would
be a false bound); route (b) widened admissible variant. `curvedGate4` (GENUINE FixedFlowGateData:
inherits a,b,r,eta + PROVED hgate VERBATIM from curvedGate; lam:=max 4 (curvedGate).lam; hlam via
le_max_left, hgap via one_div_le_one_div_of_le — enlarging lam RELAXES both constraints; lam = far-field
Gaussian-domination WIDTH not geometric radius, so sound) + `curvedGate4_r`/`curvedGate4_lam` (@[simp]
field ids) + `curved_hlam4_at_gate4`:4≤(curvedGate4).lam (THE DISCHARGE = 4≤max 4 …, le_max_left,
unconditionally true) + `curved_hFint_hFar_general` (J4-572 far-field generalised to arbitrary (r,lam),
4≤lam explicit hyp) + `curved_hFint_hFar_at_gate4` (far-field over curvedGate4, hlam4 REMOVED) +
`_curved_satisfiable`. Main verified: curvedGate4 genuine (all field obligations discharged, no vacuity);
hlam4 discharge genuinely true (not false claim about curvedGate.lam); machinery PROVED; R/6 untouched.
std-3, budget raw 0, 9850 jobs. ★ hlam4 dischargeable at admissible widened gate; mainline
curvedGate→curvedGate4 swap (identical geometry, only lam changes) = mechanical follow-on. RESIDUAL:
{hdata-family (2-sided near-isometry ½r≤r_chart≤2r + Jacobian L + amplitude Ba/Bd), hsrc/hw,
hOffCollarTail} + {convergence trio, hInnerCont}. a₁=R/6 CONDITIONAL. J4-575 = hdata-family (near-isometry
+ jet bounds from RNC chart properties — sole hcrude/far-field residual) OR hInnerCont OR convergence trio.

## J4-575 (source hdata-family near-isometry conjunct near 0 for g^K; depth-verdict on hFar/uniformization)
CurvedA1FintHdata.lean: `curved_hdata_nearIsometry_at_gate` (∃r>0 ∀z∈K ‖z‖<r →
½·rncRadialSq z≤rncRadialSq(W₀ z)≤2·rncRadialSq z — from banked HeatResidualBound.chartW0_rncRadialSq_error
[two-sided |rncRadialSq(W₀ z)−rncRadialSq z|≤L·‖z‖·rncRadialSq z], r shrunk to min r₀ (1/(2(L+1))) ⟹ L‖z‖≤½;
½/2 = genuine near-identity slack, true WITH Ric≠0) + `_curved_satisfiable`. Main verified: proved from banked
error (not axiomatized); ½/2 genuinely true not false-flat bound; R/6 untouched. std-3, budget raw 0, 9851 jobs.
★ DEPTH VERDICT: hFirstEnv near-isometry (upper ‖z‖<r) FULLY sourced (domain+bound match). hFar needs LOWER
coercivity ∀z∈K incl annulus ‖z‖≥r — near-isometry is NEAR-0 ONLY (whole-z form provably FALSE off-K, agent
verified, did NOT ship) = GENUINE new chart-jet geometry, the DEEP residual. Conjuncts (1)/(2) inverse-chart
jet + (3) uniform Ba/Bd/L need compactness-uniformization (medium depth; PdiffAt center banked via
AmplitudeFamilyDischarge.amp_pdiffAt_center). RESIDUAL: {hFar far-field coercivity (deep chart-jet),
hdata(1)/(2)/(3) uniformization (medium), hsrc/hw, hOffCollarTail} + {convergence trio, hInnerCont}. a₁=R/6
CONDITIONAL. J4-576 = conjunct (3) uniform Ba/Bd/L via compactness (banked-thin, tractable) OR hInnerCont OR
convergence trio; hFar far-field coercivity flagged as the geometric wall.

## J4-576 (source hdata conjunct (3) uniform amplitude bounds for g^K via compactness)
CurvedA1FintHdataUniform.lean: `curved_hdata_amp_value_uniform_at_gate` (3a FULLY DISCHARGED no residual:
∃ρ>0 Ba≥0 ∀i τ z∈K ‖z‖<ρ |chartFieldAmp g^K…a b τ z 0|≤Ba — from banked BaseSlotAmplitude.baseSlotAmp_bound
[joint cont on compact [0,T]×ˢclosedBall → IsCompact.exists_bound_of_continuousOn] + curved carries
curvedRNCMetric_contDiff/curvedRNCInv_contDiff[κ≤0]/curvedRNCMetric_hgpos; τ affine, no ε-floor) +
`curved_hdata_amp_deriv_uniform_at_gate_of_cont` (3b THIN: reduced to SINGLE carried hcont = joint (τ,z)-cont
of pd(chartFieldAmp) i 0 on compact box, via IsCompact.exists_bound_of_continuousOn; hcont satisfiable
ContinuousOn carry not yet banked; ∀i Bd = finite max) + `_curved_satisfiable`. Main verified: 3a from banked
machinery no residual; 3b hcont genuine satisfiable carry not vacuous; τ→0 audited (affine, no blow-up);
R/6 untouched. std-3, budget raw 0, 9852 jobs. ★ hdata DEPTH: (3a) amp value BANKED full; (3b) amp deriv →1
continuity carry (medium); remaining (1) inverse-chart field-jet existence + (2) |Pval|≤L (deep), (3b) hcont.
RESIDUAL: {hFar far-field coercivity (GEOMETRIC WALL), hdata (1)/(2) inverse-chart jet [deep] + (3b) hcont
[continuity], hsrc/hw, hOffCollarTail} + {convergence trio, hInnerCont}. a₁=R/6 CONDITIONAL. J4-577 = (3b)
hcont pd-continuity discharge (pd_chartAmp_center route in BaseSlotAmpDeriv, would complete conjunct 3) OR
(1)/(2) inverse-chart field-jet OR hInnerCont OR convergence trio; hFar far-field coercivity = flagged wall.

## J4-577 (discharge hdata (3b)'s hcont pd-continuity for g^K — conjunct (3) analytic core complete)
CurvedA1FintHdataDerivCont.lean: `curved_hdata_amp_deriv_cont_at_gate` (ContinuousOn (pd(chartFieldAmp g^K
… p.1 p.2) i 0) (Icc 0 T ×ˢ closedBall 0 ρ) = exactly J4-576 hcont; DON'T-UNDERCREDIT — joint cont already
banked general-metric via SupFamilyFirstOrder.supFamilyFirstOrder_hcont1 [pd_chartAmp_center_eq +
manifoldAmp_fderiv_continuous + ContinuousOn.clm_apply; old J3 base-point blocker discharged by
JacobiCLMExposure.chartFieldJacobian_continuousOn ← banked forwardFlowJet_continuousOn]; instantiated at
curved carries, chartAmp→chartFieldAmp via chartAmp_eq_chartFieldAmp_fun) + `curved_hdata_amp_deriv_uniform_at_gate`
(the (3b) ∃Bd bound, hcont DISCHARGED, feeds proved cont into J4-576 of_cont; depends only on hreg/hW0/hJac) +
`_curved_satisfiable`. Main verified: conclusion=exact hcont; from PROVED banked supFamilyFirstOrder_hcont1;
carried hreg/hW0/hJac genuine satisfiable inverse-chart regularity (C²+continuous), analytic cont REDUCED to
geometric substrate not lateral; R/6 untouched. std-3, budget raw 0, 9853 jobs. ★ hdata conjunct (3)
analytically COMPLETE (3a banked J4-576, 3b hcont discharged J4-577), rests on hreg/hW0/hJac. RESIDUAL:
{hFar far-field coercivity (GEOMETRIC WALL), hdata (1)/(2) inverse-chart jet + hreg/hW0/hJac reachability-gate
geometric, hsrc/hw, hOffCollarTail} + {convergence trio, hInnerCont}. a₁=R/6 CONDITIONAL. J4-578 = discharge
hreg/hW0/hJac on small-ρ reachability gate (chartFieldJacobian_continuousOn side-conditions + chartField_contDiffAt_reachable_uniform) OR (1)/(2) inverse-chart jet OR hInnerCont OR convergence trio; hFar coercivity = standing wall.

## J4-578 (discharge hreg/hW0/hJac inverse-chart regularity — hdata conjunct (3) fully unconditional for g^K)
CurvedA1FintHdataReg.lean: DON'T-UNDERCREDIT — three regularity carries already banked general-metric via
C2CarrierCollapse.c2_carriers_discharged (chartField_contDiffAt_reachable_uniform[hreg] +
chartOrigin_continuousOn[hW0] + chartFieldJacobian_continuousOn+chartFieldJacobian_eq_ringInverse IFT[hJac];
no metric-positivity). `curved_carriers_at_gate` (∃ρ>0 hreg∧hW0∧hJac exact J4-577 shapes) +
`curved_hreg/hW0/hJac_at_gate` (individually) + `curved_hdata_amp_deriv_uniform_unconditional_at_gate`
(the (3b) Bd bound, hreg/hW0/hJac ALL discharged, feeds J4-577's curved_hdata_amp_deriv_uniform_at_gate;
rests only on hκ:κ≤0 + h0Kmem:K∈𝓝 0) + `curved_carriers_gate_satisfiable` (∃K compact∧K∈𝓝 0 = closedBall 0 1)
+ `_reg_curved_satisfiable`. Main verified: all carries from PROVED c2_carriers_discharged; only new hyp =
reachability gate K∈𝓝 0 (geometric, strictly-weaker, SATISFIABLE not vacuous); R/6 untouched. std-3, budget
raw 0, 9854 jobs. ★ hdata conjunct (3) FULLY UNCONDITIONAL for g^K (modulo satisfiable K∈𝓝 0 gate) — no
hreg/hW0/hJac carried. RESIDUAL: {hFar far-field coercivity (GEOMETRIC WALL), hdata (1)/(2) inverse-chart
jet [C2CarrierCollapse hid2 second-order IFT residue = sole non-collapsing carrier], hsrc/hw, hOffCollarTail}
+ {convergence trio, hInnerCont}. a₁=R/6 CONDITIONAL. J4-579 = conjuncts (1)/(2) inverse-chart jet (hid2
second-order IFT residue) OR hInnerCont OR convergence trio; hFar coercivity = standing wall.

## J4-579 (prove hdata conjuncts (1)/(2) inverse-chart first-jet + |Pval|≤L for g^K)
CurvedA1FintHdataJet.lean: DON'T-UNDERCREDIT — IFT jet already banked. `curved_hdata_jet_at_gate`
(∃ρ>0 ∃L≥0 ∀i τ z∈K ‖z‖<ρ → ∃Pval, (∀k HasDerivAt(fun r=>uniformInverseChart g^K… z (update 0 i r) k)(Pval k)(0 i))
∧(∀k |Pval k|≤L) — the (1)∧(2) bundle; (1) from banked HeatResidualBound.chartField_firstJet_of_contDiffAt
[Pval k:=fderiv(uniformInverseChart… z)0 (Pi.single i 1) k, fed by hreg J4-578]; (2) from hJac J4-578 +
IsCompact.exists_bound_of_continuousOn → uniform L, |DW e k|≤‖DW e‖≤‖DW‖·‖e‖=‖DW‖≤L) +
`curved_hdata_jet_gate_satisfiable` (∃K compact∧K∈𝓝 0=closedBall 0 1) + `_curved_satisfiable`. hid2 NOT
needed (first-order). Main verified: (1)/(2) from PROVED chartField_firstJet_of_contDiffAt+c2_carriers;
only new hyp K∈𝓝 0 satisfiable not vacuous; jet exists+bound true; R/6 untouched. std-3, budget raw 0, 9855
jobs. ★ ALL FOUR hdata conjuncts now hold individually (small-ρ gates): (1)/(2) J4-579, (3) J4-576/577/578,
(4) J4-575. Bundle-level removal awaits ρ/gate reconciliation (assembly bookkeeping) OR hFar needs K small.
RESIDUAL: {hFar far-field LOWER coercivity (GEOMETRIC WALL — the last genuinely-analytic far-field piece),
hsrc/hw, hOffCollarTail} + {convergence trio, hInnerCont} + [hdata bundle ρ-reconciliation bookkeeping].
a₁=R/6 CONDITIONAL. J4-580 = hFar far-field lower coercivity (highest-leverage geometric wall) OR the hdata
bundle ρ-reconciliation (mechanical, closes the leg visibly) OR hInnerCont OR convergence trio.

## J4-580 (assemble hdata bundle + discharge hFirstEnv's hdata on reconciled ρ* ball for g^K)
CurvedA1FintHdataBundle.lean: `curved_hdata_bundle_at_gate` (FULL six-conjunct hdata bundle for g^K κ≤0 on
ONE ball ‖z‖<ρ*=min ρ1(min ρ2(min ρc r4)), single (L,Ba,Bd); combines curved_hdata_jet_at_gate (1/2) +
curved_hdata_amp_value_uniform_at_gate (κ≤0) + curved_hdata_amp_deriv_uniform_at_gate (shared carrier ball) +
curved_hdata_nearIsometry_at_gate (upper); conjunct (3) PdiffAt via manifoldAmp_contDiffAt∘hreg AVOIDS the
analytic ⊤/ω transport-coeff wall; Bd:=∑ⱼBdⱼ ∀i-uniform) + `curved_hFint_hFirstEnv_on_ball` (radius-GENERIC
port, original never uses (curvedGate).r beyond hdata) + `curved_hFint_hFirstEnv_hdata_discharged_at_gate`
(hFirstEnv hdata REMOVED on reconciled ρ* ball) + satisfiability lemmas. Main verified: bundle on HONEST ρ*
ball (proof via min_le); domain NOT over-claimed as full gate ball (doc: no proof ρ*≥(curvedGate).r); from
PROVED siblings + banked manifoldAmp_contDiffAt; R/6 untouched. std-3, budget raw 0, 9856 jobs. ★ hcrude's
on-gate hFirstEnv leg now hdata-FREE for g^K (‖z‖<ρ*, modulo gate-radius alignment + hSopen/hgate0). RESIDUAL:
{hFar far-field LOWER coercivity (GEOMETRIC WALL, hardest), hsrc/hw, hOffCollarTail, hSopen/hgate0, ρ*-vs-gate
alignment} + {convergence trio, hInnerCont}. a₁=R/6 CONDITIONAL. J4-581 = (i) gate-radius alignment (prove
ρ*≥(curvedGate).r or shrink gate to ρ* → full-gate-ball hFirstEnv-hdata-discharged) OR (ii) hFar far-field
coercivity geometric wall OR hInnerCont OR convergence trio.

## J4-581 (hFar far-field coercivity DISCHARGED from the capstone's own hframeK — K⊆{0}, far-field empty)
CurvedA1FintHFarCoercivity.lean: VERDICT route (a) — mainline frame seed K forced to {0}, far-field annulus
never fires (NOT irreducible wall, NOT false whole-z ½). `curvedRNCMetric_frame_forces_origin` (g^K z=δ ⟹ z=0
for κ≠0,n≥2: curvedRNCMetric κ z=δ−(κ/3)(‖z‖²δ−z⊗z) =δ only at origin) + `curved_hFar_coercivity_smallK_at_gate`
(route a general: ∃ρ>0 (K⊆ball) → coercivity, from banked hmin_gate J4-575) + `curved_hFar_coercivity_frameK_at_gate`
(THE discharge: ∀z∈K coercivity from capstone's OWN hframeK ⟹ K⊆{0} ⟹ z=0 ⟹ 0≤nonneg = exactly the
curved_hFint_hFar_general hdata coercivity conjunct) + `_curved_satisfiable`. ★ HONEST: discharge FROM hframeK,
NOT general far-field coercivity (whole-z ½ FALSE = wholeSpace_coercivity_unsatisfiable; uniformInverseChart
compactly-supported, doesn't realize global Cartan–Hadamard inverse). Frame seed K={0} = established RNC-norm
structure; capstone non-vacuity cleared J4-551 (R/6 coeff n(n−1)κ/6≠0; hframeK/hmassone decoupled, hframeK does
NOT force Ric=0 unlike retracted J4-509). Far-field domination trivial on mainline K; on-gate content (z=0) carries
a₁. Main verified: frame_forces_origin geometry correct; discharge sound; no false far-field ½; R/6 untouched. std-3,
budget raw 0, 9857 jobs. ★ THE DEEPEST GEOMETRIC WALL IS NOT AN IRREDUCIBLE ANALYTIC OBSTRUCTION — it's
discharged by the capstone's own frame normalization. RESIDUAL: {hsrc/hw, hOffCollarTail, hSopen/hgate0,
gate-radius/K-alignment wiring} geometric + {convergence trio, hInnerCont} analytic. a₁=R/6 CONDITIONAL. J4-582 =
curvedGate4→mainline substitution to consume discharged hFar into curved_a1_R6_fully_wired OR hInnerCont OR
convergence trio.

## ⚠⚠ J4-582 (VACUITY FINDING — curved_a1_R6_fully_wired is VACUOUS at the genuinely-curved witness)
CurvedA1FarConsumeCheck.lean: adversarial soundness audit (Sol-confirmed gpt-5.6-sol high) of the J4-581
hFar-coercivity-from-hframeK discharge. VERDICT: the fully-wired curved a₁ capstone is VACUOUS at κ≠0,n≥2 —
antecedent bundle {hK0, hframeK, hmassone} JOINTLY UNSATISFIABLE. `frameK_forces_singleton` (hK0+hframeK ⟹
K={0}, since curvedRNCMetric κ=δ only at origin — hframeK≡δ-on-K is FLATNESS) + `witness_baseIntegral_zero`
(∫z vanVleckGatedWitness g^K…(constGate…c)a b τ 0 z=0 ∀τ — K={0} collapses gated-kernel SOURCE slot q∈K to
null singleton) + `hmassone_unsatisfiable` (THE PIN: capstone's OWN hmassone [line 399-400, verified identical:
Tendsto (fun m => ∫z vanVleckGatedWitness…(epsSeq m)0 z) atTop (𝓝 1)] is FALSE — const-0 seq ≠→1). Main
verified: hmassone shape MATCHES capstone binder EXACTLY; hK0/hframeK are capstone binders (lines 79/221/222);
math airtight (source-slot gating). std-3, budget raw 0, 9858 jobs. ★ CORRECTION: J4-548/551 "curved-satisfiable
non-vacuous" was WRONG — `_curved_satisfiable` gate checks only CONCLUSION coeff (Ric≠0), never antecedent
inhabitance = axiom-budget blind spot; "hframeK/hmassone decoupled" was false (hmassone ∫z over K-gated source).
Only frame-escape regime (n=1/κ=0) has Ric=0 ⟹ coeff 0 (flat). ROOT CAUSE: hframeK="g≡δ on ALL K" is FLATNESS
(wrong RNC gauge); should be CENTER-ONLY (g(0)=δ + ∂g(0)=0). ⚠ a₁=R/6 CONDITIONAL — capstone does NOT
non-vacuously establish it at a curved witness. J4-583 = re-architect hframeK to a center-only normal-coordinate
gauge (the substantive fix enabling a non-degenerate curved witness) OR add a joint-inhabitance obligation to
the satisfiability gate; this is now THE crux, ahead of hInnerCont/convergence-trio.

## J4-583 (VERDICT SALVAGEABLE — J4-582 curved vacuity is a removable hframeK-too-strong artefact)
CurvedA1FrameAudit.lean: hframeK-consumer trace (CurvedA1FullyWired/Leg2Core/Leg2HLapFull/Capstone) —
EVERY hframeK consumption is gauge_from_geometry → hg0_of_hframeK:=hframeK 0 hK0 (reads ONLY 0-jet value
g(0)=δ). MAIN independently grep-confirmed: no rw[hframeK], no hframeK q at q≠0, no metric→δ substitution
in the R/6 derivation (AxiomAudit:22995 documents hg0_of_hframeK role). R/6 coeff from Ric(0) of CURVED
metric = center fact. ⟹ J4-582 vacuity caused SOLELY by hframeK neighbourhood strength (∀q∈K⟹K={0}), NOT
flattening. `curved_gauge_from_center` (κ<0: MemGaugeGi∧MemGaugeGamma via banked
DaLimCurvedGauge.gauge_from_pointwise fed by center-only curvedRNCMetric_zero/hinvF/pd_zero — NO
hframeK/hK0) + `curved_frame_salvage_certificate` (gauge members ∧ Ric(0)≠0 = center gauge inhabited by
genuinely curved metric). std-3, budget raw 0, 9859 jobs. ★ VERDICT: curved a₁=R/6 is FIXABLE not
flat-only. SALVAGE PATH J4-584: weaken capstone binder hframeK(∀q∈K g^K q=δ)→hg0(∀i j g^K 0 i j=δ)
[curvedRNCMetric satisfies, doesn't force K={0}, hmassone satisfiable] + rethread 2 gauge_from_geometry→
gauge_from_pointwise. ⚠ curved capstone STILL VACUOUS AS WRITTEN (J4-582); this certifies FIXABILITY only.
a₁=R/6 CONDITIONAL. J4-584 = the rethread (weaken hframeK→hg0 in curved_a1_R6_fully_wired + curved_hDa_at_gate
+ curved_core_at_gate + curved_leg2_hLapFull binders; discharge hg0 via curvedRNCMetric_zero; rethread gauge
sites via curved_gauge_from_center; re-run J4-582 vacuity check to confirm now jointly satisfiable at curved).

## J4-584 (anti-J4-582 NON-VACUITY CERTIFICATE — center-only gauge defeats the curved-capstone vacuity)
CurvedA1CenterGauge.lean: certifies the J4-583 salvage is sound + inhabited by a genuinely-curved metric;
J4-582 structural vacuity mechanism REMOVED. NO in-place capstone/monolith edits (agent correctly declined —
leg-1 hframeK terminates in census monolith DaLimLUCappedStep3:215 gauge site). `half_axis_mem_ball` (½·e₀∈
closedBall 0 1 ∧≠0) + `curved_center_antecedents_nonvacuous` (κ<0,n≥2: ∃K IsCompact∧0∈K∧(∃q∈K q≠0)∧
(MemGaugeGi∧MemGaugeGamma)∧Ric(0)≠0∧¬(∀q∈K g^K q=δ); K=closedBall 0 1; gauge from PROVED curved_gauge_from_center;
¬hframeK via curvedRNCMetric_frame_forces_origin) + `curved_center_gate` (antecedent-inhabitance gate,
contrast coefficient-only gate J4-582 exploited). Main verified: certificate genuine (non-singleton K,
gauge from banked center-only facts, Ric≠0, ¬hframeK); DEFEATS J4-582 (vacuity needed K⊆{0} for source
collapse; here ∃z≠0∈K ⟹ collapse gone ⟹ hmassone obstruction structurally removed). std-3, budget raw 0,
9860 jobs. ⚠ HONEST LIMITS: (1) hmassone NOT in the satisfiable bundle — structural obstruction removed but
hmassone(∫z→1) still carried analytic input; (2) in-place binder rethread STILL OWED (J4-585, touches monolith
gauge site). Shipped curved a₁=R/6 still vacuous-as-written; this certifies fix sound, doesn't apply it. a₁=R/6
CONDITIONAL, non-vacuous only for FLAT tower. J4-585 = in-place rethread: (1) center-gauge VARIANT
hDaLimLU_from_labelled_capped_center in DaLimLUCappedStep3 (rethread the single gauge_from_geometry L215→
gauge_from_pointwise, SPLICE-only census body untouched); (2) mirror Leg2HLapFull.curved_leg2_hLapFull L151
(shallow gauge site); (3) thread hg0:=curvedRNCMetric_zero up through curved_hDa_at_gate/core/capstone dropping
hframeK; (4) re-run curved_center_antecedents_nonvacuous as the weakened-capstone vacuity guard.

## J4-585 (leg-1 center-gauge VARIANT of the DaLimLU monolith site — rethread step 1)
DaLimLUCappedStep3Center.lean: `hDaLimLU_from_labelled_capped_center` — center-only-gauge variant of
DaLimLUCappedStep3.hDaLimLU_from_labelled_capped. Sig IDENTICAL EXCEPT {hK0,hframeK}→hg0:∀i j g 0 i j=δ
(K/hK retained — gated witness uses pervasively; only hK0/hframeK dropped, fed gauge site alone). Conclusion=
SAME DaLimLUGoal (not weakened). Proof=original VERBATIM except ONE gauge line (215): gauge_from_geometry g gi
hK0 hframeK hinvF hdg0 → DaLimCurvedGauge.gauge_from_pointwise g gi hg0 hinvF hdg0 (identical gauge-member
output). ★ Census body is a SEPARATE assembly of already-compiled lemmas (witness_MemInterchange/source_from_leviData/
integrability_from_dominations_capped/memLapFull_from_labelled/eCombine_from_data/hDaLimLU_concrete) taking gauge
members as explicit args — NO inlined census, NO _of_gauge abstraction needed, NO 85-binder re-elaboration
(30s build). Main verified: hg0 binder no hframeK/hK0; gauge site swapped (L190 gauge_from_pointwise); conclusion=
DaLimLUGoal; DaLimLUCappedStep3.lean UNTOUCHED; std-3. hg0 curved-satisfiable via curvedRNCMetric_zero, doesn't
force K={0} ⟹ J4-582 vacuity removed on leg-1. budget raw 0, 9861 jobs. a₁=R/6 non-vacuous only for FLAT tower.
J4-586 = mirror leg-2 (CurvedA1Leg2Core.lean L262 gauge_from_geometry in curved_leg2_hLapFull/MemLapFull → center
variant via gauge_from_pointwise); then J4-587 thread hg0:=curvedRNCMetric_zero up through curved_hDa_at_gate/
curved_core_at_gate/curved_a1_R6_fully_wired dropping hframeK + weakened-capstone vacuity guard.
