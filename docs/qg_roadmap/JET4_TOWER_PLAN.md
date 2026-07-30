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
- J4-6 discharge hfd3 wherever the recenter chain carries it (R3c-1 contDiffOn_expPullbackMetric_three → g̃∈C³ unconditional → the whole recenter conditional set loses hfd3).
Each brick = a green [AF] std-3 mirror. LONG but every rung is reachable. Then a₁=R/6 loses hfd3 (still conditional on the convergence trio + geometric wiring until those land too).

## Progress
- J4-1 ✅ (5e44674e) ExpJet4Rhs.lean: expJet4Rhs (14-term Faà-di-Bruno RHS) + _apply/_continuousOn/_norm_le, mirror expJet3Rhs. [AF] std-3. Confirmed the tower IS a faithful mirror (14 terms = the one-order-up analog of jet-3's 4).
- (parallel) hInter ✅ (4bff8b12) LeviInterchange.lean: heatConv_leviSeries_interchange — the convergence-trio interchange FULLY discharged; NOT a Mathlib gap (integral_tsum_of_summable_integral_norm + built domination). Reduces trueKernel's hInter carry to hEbound/hEzero/hEmeas. Convergence trio now: hDuhamel (via leviSeries_volterra + this hInter) + hCorrHigher remain.
- J4-2a ✅ ExpJet4Fund.lean: expJet4Fund_local (local PL existence, verbatim mirror of expJet3Fund_local). [AF] std-3. NEXT J4-2b = expJet4Field_continuousOn → expJet4Fund_shifted → _glue → expJet4Fund ([0,1] global capstone, mirror expJet3Fund chain ExpMapContDiff3.lean:581-996).
- J4-2c ✅ ExpJet4FundBounds.lean: expJet4Fund_unique + expJet4Fund_value_bound + _value_bound_Icc (mirror expJet3Fund_unique/_value_bound/_value_bound_Icc). J4-3 prereqs (uniqueness pins witness; value_bound_Icc = M₄ a-priori bound) in place. [AF] std-3. NEXT J4-3 = expJet4Val_v_two_pt_diff (two-point Lipschitz analytic HEART, mirror expJet3Val_v_two_pt_diff:4165 — hardest rung, reuses shared expFund_two_pt_diff_Icc; decompose if huge).
