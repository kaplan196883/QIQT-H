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
- J4-1 [NEXT] expJet4Rhs (4th-variation ODE RHS field) + expJet4Rhs_apply + _continuousOn (Icc 0 1) + _norm_le — mirror expJet3Rhs (ExpMapContDiff3.lean:242-375) one order up.
- J4-2 expJet4Fund (fundamental solution): _local + _shifted + _glue + expJet4Fund + _unique + _value_bound + _value_bound_Icc — mirror expJet3Fund chain.
- J4-3 expJet4Val_v_two_pt_diff (analytic heart, two-point Lipschitz ‖R⁴_v(1)−R⁴_w(1)‖≤C‖v−w‖‖h‖‖k‖‖l‖‖m‖) — mirror expJet3Val_v_two_pt_diff.
- J4-4 expJetD4_two_pt_diff — mirror expJetD3_two_pt_diff.
- J4-5 expMap_fderiv3_hasFDerivAt + assemble: fderiv³exp Lipschitz⟹continuous + differentiable ⟹ ContDiffOn 1 (fderiv³exp) = hfd3 ⟹ feed expMap_contDiffOn_four_of_fderiv3_contDiffOn_one (eb8ab4cd) ⟹ expMap_contDiffOn_four UNCONDITIONAL.
- J4-6 discharge hfd3 wherever the recenter chain carries it (R3c-1 contDiffOn_expPullbackMetric_three → g̃∈C³ unconditional → the whole recenter conditional set loses hfd3).
Each brick = a green [AF] std-3 mirror. LONG but every rung is reachable. Then a₁=R/6 loses hfd3 (still conditional on the convergence trio + geometric wiring until those land too).
