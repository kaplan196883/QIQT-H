/-
  CensusLeviFactorDischarge — J4-942: the F-FACTOR half of junction piece (3) of the `hCensusBound`
  (`hCross`) re-audit — the SOLE remaining piece-(3) obligation flagged since J4-939/940/941.

  ROLE.  Across J4-930..J4-941 the literal `hCensusBound` (the `hCross` wall, a sub-carry of
  `hDuhamel`/`hDConv`) was reduced to EXACTLY ONE remaining obligation:

    (a) the F-factor's own ball-local bounded+Lipschitz regularity — for the census weights
        `q₁ = amp·F` and `q₂ = Cfield·F` (`F = leviSeries E`), the abstract factor
        `F0 z := leviSeries E s z 0` must be BOUNDED and pairwise-LIPSCHITZ on a genuine ball, the
        EXACT `(rF, M_F, L_F, hFb, hFl)` bundle carried by
        `CensusHbaseC2Discharge.census_ampF_transported_ratio_regularity_unconditional` (J4-941).

  (obligation (b), `hbaseC2`, was DISCHARGED UNCONDITIONALLY at J4-941.)

  THIS FILE supplies obligation (a) from BANKED Levi machinery.  The banked `LeviLipschitz` file
  already contains BOTH halves of the F-factor regularity, GLOBALLY (hence ball-locally trivially):
    • BOUNDEDNESS — `HeatResidualBound.abs_F_le_diagonal`: from the width-2 `F`-domination `hFdom`,
        `|F s z 0| ≤ C_L · gaussDdim (2s) 0` for EVERY `z` (the Gaussian peak-at-`0` bound).
    • LIPSCHITZ — `HeatResidualBound.resolvent_lipschitz_pointwise` (J4-144): from the Volterra
        identity + the `E`-slice difference `hE1` + the inner-`ζ`-integral slice difference `hSlice`
        (the `(s−r)^{−1/2}`-weighted bound) + integrabilities,
        `|F s z 0 − F s z' 0| ≤ (L_E + K·2√s) · dist z z'` for EVERY `z, z'`.
  Assembling these two GLOBAL bounds gives the ball-local `F0`-bundle J4-941 demands, verbatim; and
  composing with J4-941 discharges the abstract `F0` slot of the transported census integrands
  `q₁ = (amp·F)/|det|` and `q₂ = (Cfield·F)/|det|` down to the CONCRETE `leviSeries E`, carrying ONLY
  the honest `LeviLipschitz` analytic inputs (`hFdom`, the Volterra `hVol`, `hE1`, `hSlice`,
  integrabilities) — which ARE the `{hDuhamel, hDConv, hCConv}`-family analytic carries.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## WHAT IS — AND IS NOT — CLOSED (honest, extreme-stakes; gpt-5.6-sol high adversarially audited).
    • The F-factor obligation (a) is REDUCED to the banked `LeviLipschitz` analytic carries
      (`hFdom`; the Volterra `hVol`; `hE1`; the integrability `hIz`; `hSlice`).  Composed with (b)
      (`hbaseC2`, J4-941) and the concrete amplitude (J4-938), the transported census-integrand
      regularity for the CONCRETE `F = leviSeries E` is supplied carrying ONLY those Levi carries.
    • This does NOT close `hCensusBound`/`hCross`.  ⚠ NO literal single `hCensusBound`/`hCross`
      theorem is assembled here (the 6-piece assembly into the literal statement was never
      monolithized).  Only the LAST flagged regularity INTERFACE obligation (a) is conditionally
      solved.
    • The Levi carries `hFdom`/`hE1`/`hIz`/`hSlice` are INTENDED to come from the
      `Ebound`/`heatConv` analytic family = the `{hDuhamel, hDConv, hCConv}` inputs, but that
      identification is CAMPAIGN BOOKKEEPING, NOT a Lean-proven equality here — this file does NOT
      prove those carries follow from `{hDuhamel, hDConv, hCConv}`.  So it is honest to say the
      F-factor obligation is REDUCED to the Levi analytic carries, but NOT that `hCross` is formally
      subsumed / discharged.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, EXACTLY
      as before.  NOT a new unconditional theorem.

  ## WHAT LANDS.
    • `levi_Ffactor_ball_regularity` — ★★ the F-factor bundle: from the Levi carries, `F0 z := F s z
        0` is bounded (`C_L·gaussDdim (2s) 0`) + pairwise-Lipschitz (`L_E + K·2√s`) on ANY ball
        `rF>0` (the exact abstract-`F0` input of J4-941), via `abs_F_le_diagonal` +
        `resolvent_lipschitz_pointwise`.
    • `census_ampF_leviF_transported_ratio_regularity` — ★★ THE CONCRETE q₁ with F = `leviSeries E`:
        composing the F-factor bundle with J4-941's
        `census_ampF_transported_ratio_regularity_unconditional`, the transported census integrand
        `w ↦ (chartFieldAmp … τ (V w) 0 · leviSeries E s (V w) 0) / |det (fderiv Wbv (V w))|` is
        bounded + pairwise-Lipschitz on an image ball — amplitude concrete, F = `leviSeries E`
        concrete, carrying ONLY the honest Levi analytic inputs.
    • `census_CfieldF_leviF_transported_ratio_regularity` — ★★ the same for q₂ (`censusAmpTauDeriv`).
    • `levi_Ffactor_slot_satisfiable` — non-vacuity: the Levi-carry hypothesis bundle is CONSISTENT
        (the degenerate zero resolvent `E = F = 0` satisfies all five carries at positive constants
        `C_L = K = L_E = 1`, `s = 1`).  (The TEETH-bearing downstream `F0`-slot witness is the banked
        `CensusAmpConcreteRegularity.census_abstractF_slot_satisfiable` — `cos‖·‖`, genuinely varying.)

  ⚠  STILL NOT `a₁ = R/6`.  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.
-/
import Mathlib
import QIQTH.LeviLipschitz
import QIQTH.CensusHbaseC2Discharge
import QIQTH.TrueHeatKernel
import QIQTH.ResidueBound

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.HeatResidualBound QIQTH.TrueHeatKernel QIQTH.ResidueBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.CensusHbaseC2Discharge QIQTH.CensusTauDerivGateSplit
open scoped Topology BigOperators Interval

namespace QIQTH.CensusLeviFactorDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the F-factor bundle from the banked Levi machinery.
    ############################################################################### -/

/-- **★★ `levi_Ffactor_ball_regularity` — the F-factor bounded+Lipschitz bundle.**  From the banked
    `LeviLipschitz` analytic carries (the width-2 `F`-domination `hFdom`; the Volterra identity
    `hVol`; the `E`-slice difference `hE1`; the inner-`ζ`-integral slice difference `hSlice`; the
    integrability `hIz`), the F-factor `F0 z := F s z 0` is bounded (`M_F = C_L·gaussDdim (2s) 0`) AND
    pairwise-Lipschitz (`L_F = L_E + K·2√s`) on ANY ball `rF>0`.  Route: `abs_F_le_diagonal`
    (boundedness, Gaussian peak-at-`0`) + `resolvent_lipschitz_pointwise` (Lipschitz, resolvent
    route), both GLOBAL ⟹ ball-local trivially.  This is the EXACT abstract-`F0` input of J4-941.
    ⚠ NOT `a₁ = R/6`. -/
theorem levi_Ffactor_ball_regularity (E F : ℝ → Point n → Point n → ℝ) (s C_L Kc L_E rF : ℝ)
    (hs : 0 < s) (hrF : 0 < rF) (hC_L : 0 ≤ C_L) (hKc : 0 ≤ Kc) (hL_E : 0 ≤ L_E)
    (hFdom : ∀ z : Point n, |F s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0))
    (hVol : ∀ z : Point n, F s z 0 = - E s z 0 - heatConv E F s z 0)
    (hE1 : ∀ z z' : Point n, |E s z 0 - E s z' 0| ≤ L_E * dist z z')
    (hIz : ∀ z : Point n,
        IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * F r ζ 0) volume 0 s)
    (hSlice : ∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * F r ζ 0) - (∫ ζ, E (s - r) z' ζ * F r ζ 0)|
          ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) :
    ∃ M_F L_F : ℝ, 0 ≤ M_F ∧ 0 ≤ L_F ∧
      (∀ z : Point n, ‖z‖ < rF → |F s z 0| ≤ M_F) ∧
      (∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F s z 0 - F s w 0| ≤ L_F * dist z w) := by
  refine ⟨C_L * gaussDdim (2 * s) (0 : Point n), L_E + Kc * (2 * Real.sqrt s), ?_, ?_, ?_, ?_⟩
  · -- `0 ≤ M_F` via `0 ≤ |F s 0 0| ≤ M_F`.
    exact le_trans (abs_nonneg _) (abs_F_le_diagonal F C_L s hs hC_L hFdom 0)
  · -- `0 ≤ L_F`.
    have hnn : (0 : ℝ) ≤ Kc * (2 * Real.sqrt s) := mul_nonneg hKc (by positivity)
    linarith
  · -- boundedness on the ball (from the GLOBAL diagonal peak bound).
    intro z _
    exact abs_F_le_diagonal F C_L s hs hC_L hFdom z
  · -- pairwise-Lipschitz on the ball (from the GLOBAL resolvent bound).
    intro z w _ _
    exact resolvent_lipschitz_pointwise E F s Kc L_E z w hs hKc
      (hVol z) (hVol w) (hE1 z w) (hIz z) (hIz w) (hSlice z w)

/-! ###############################################################################
    ### §B — CONCRETE compositions: the census integrands with F = `leviSeries E`.
    ############################################################################### -/

/-- **★★ `census_ampF_leviF_transported_ratio_regularity` — THE CONCRETE q₁ with F = `leviSeries E`.**
    Composing the F-factor bundle (§A, for `F := leviSeries E`) with J4-941's
    `census_ampF_transported_ratio_regularity_unconditional`, the transported census integrand
    `w ↦ (chartFieldAmp … τ (V w) 0 · leviSeries E s (V w) 0) / |det (fderiv Wbv (V w))|` is bounded +
    pairwise-Lipschitz on an image ball `ball 0 σ`.  Amplitude concrete (J4-938), F = `leviSeries E`
    concrete — reducing the abstract `F0` slot to the concrete `leviSeries E`, carrying ONLY the
    honest `LeviLipschitz` analytic inputs (`hFdom`/`hVol`/`hE1`/`hIz`/`hSlice`).  ⚠ NOT `a₁ = R/6`. -/
theorem census_ampF_leviF_transported_ratio_regularity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (E : ℝ → Point n → Point n → ℝ) (s C_L Kc L_E rF : ℝ)
    (hs : 0 < s) (hrF : 0 < rF) (hC_L : 0 ≤ C_L) (hKc : 0 ≤ Kc) (hL_E : 0 ≤ L_E)
    (hFdom : ∀ z : Point n, |leviSeries E s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0))
    (hVol : ∀ z : Point n,
        leviSeries E s z 0 = - E s z 0 - heatConv E (leviSeries E) s z 0)
    (hE1 : ∀ z z' : Point n, |E s z 0 - E s z' 0| ≤ L_E * dist z z')
    (hIz : ∀ z : Point n,
        IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) volume 0 s)
    (hSlice : ∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) - (∫ ζ, E (s - r) z' ζ * leviSeries E r ζ 0)|
          ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (M Lc : ℝ), 0 ≤ M ∧ 0 ≤ Lc ∧ V 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (chartFieldAmp g gi hC hK a b τ (V w) 0 * leviSeries E s (V w) 0
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|) ≤ M) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        abs (chartFieldAmp g gi hC hK a b τ (V x) 0 * leviSeries E s (V x) 0
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V x)).det|
            - chartFieldAmp g gi hC hK a b τ (V y) 0 * leviSeries E s (V y) 0
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V y)).det|)
          ≤ Lc * dist x y) := by
  obtain ⟨M_F, L_F, hMFnn, hLFnn, hFb, hFl⟩ :=
    levi_Ffactor_ball_regularity E (leviSeries E) s C_L Kc L_E rF hs hrF hC_L hKc hL_E
      hFdom hVol hE1 hIz hSlice
  exact census_ampF_transported_ratio_regularity_unconditional g gi hC hK a b τ h0Kmem hg hg0 hu
    (fun z => leviSeries E s z 0) rF M_F L_F hrF hMFnn hLFnn hFb hFl

/-- **★★ `census_CfieldF_leviF_transported_ratio_regularity` — THE CONCRETE q₂ with F = `leviSeries
    E`.**  As `census_ampF_leviF_transported_ratio_regularity` but for the `∂_τ`-slope weight
    `censusAmpTauDeriv · leviSeries E`.  ⚠ NOT `a₁ = R/6`. -/
theorem census_CfieldF_leviF_transported_ratio_regularity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (E : ℝ → Point n → Point n → ℝ) (s C_L Kc L_E rF : ℝ)
    (hs : 0 < s) (hrF : 0 < rF) (hC_L : 0 ≤ C_L) (hKc : 0 ≤ Kc) (hL_E : 0 ≤ L_E)
    (hFdom : ∀ z : Point n, |leviSeries E s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0))
    (hVol : ∀ z : Point n,
        leviSeries E s z 0 = - E s z 0 - heatConv E (leviSeries E) s z 0)
    (hE1 : ∀ z z' : Point n, |E s z 0 - E s z' 0| ≤ L_E * dist z z')
    (hIz : ∀ z : Point n,
        IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) volume 0 s)
    (hSlice : ∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
        |(∫ ζ, E (s - r) z ζ * leviSeries E r ζ 0) - (∫ ζ, E (s - r) z' ζ * leviSeries E r ζ 0)|
          ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (M Lc : ℝ), 0 ≤ M ∧ 0 ≤ Lc ∧ V 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (censusAmpTauDeriv g gi hC hK a b (V w) * leviSeries E s (V w) 0
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|) ≤ M) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        abs (censusAmpTauDeriv g gi hC hK a b (V x) * leviSeries E s (V x) 0
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V x)).det|
            - censusAmpTauDeriv g gi hC hK a b (V y) * leviSeries E s (V y) 0
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V y)).det|)
          ≤ Lc * dist x y) := by
  obtain ⟨M_F, L_F, hMFnn, hLFnn, hFb, hFl⟩ :=
    levi_Ffactor_ball_regularity E (leviSeries E) s C_L Kc L_E rF hs hrF hC_L hKc hL_E
      hFdom hVol hE1 hIz hSlice
  exact census_CfieldF_transported_ratio_regularity_unconditional g gi hC hK a b h0Kmem hg hg0 hu
    (fun z => leviSeries E s z 0) rF M_F L_F hrF hMFnn hLFnn hFb hFl

/-! ###############################################################################
    ### §C — non-vacuity: the Levi-carry hypothesis bundle is CONSISTENT.
    ############################################################################### -/

/-- **Non-vacuity of the Levi-carry slot.**  The five `LeviLipschitz` carries of
    `levi_Ffactor_ball_regularity` (`hFdom`, the Volterra `hVol`, `hE1`, `hIz`, `hSlice`) are jointly
    CONSISTENT — satisfiable by the degenerate zero resolvent `E = F = 0` at positive constants
    `C_L = K = L_E = 1`, `s = 1` (`E = 0 ⟹ heatConv E F = 0 ⟹ F = 0` by Volterra; all bounds hold by
    `0 ≤ nonneg`).  This confirms the carried Levi-factor slot is NOT unsatisfiable — no vacuity trap.
    (The TEETH-bearing downstream `F0`-slot witness is the banked
    `CensusAmpConcreteRegularity.census_abstractF_slot_satisfiable`, `cos‖·‖`.)  ⚠ NOT `a₁ = R/6`. -/
theorem levi_Ffactor_slot_satisfiable :
    ∃ (E F : ℝ → Point n → Point n → ℝ) (s C_L Kc L_E : ℝ),
      0 < s ∧ 0 ≤ C_L ∧ 0 ≤ Kc ∧ 0 ≤ L_E ∧
      (∀ z : Point n, |F s z 0| ≤ C_L * gaussDdim (2 * s) (z - 0)) ∧
      (∀ z : Point n, F s z 0 = - E s z 0 - heatConv E F s z 0) ∧
      (∀ z z' : Point n, |E s z 0 - E s z' 0| ≤ L_E * dist z z') ∧
      (∀ z : Point n,
          IntervalIntegrable (fun r => ∫ ζ, E (s - r) z ζ * F r ζ 0) volume 0 s) ∧
      (∀ z z' : Point n, ∀ r ∈ Set.Ioo (0 : ℝ) s,
          |(∫ ζ, E (s - r) z ζ * F r ζ 0) - (∫ ζ, E (s - r) z' ζ * F r ζ 0)|
            ≤ Kc * dist z z' * (s - r) ^ (-(1 : ℝ) / 2)) := by
  refine ⟨fun _ _ _ => 0, fun _ _ _ => 0, 1, 1, 1, 1,
    one_pos, zero_le_one, zero_le_one, zero_le_one, ?_, ?_, ?_, ?_, ?_⟩
  · -- `hFdom`: `|0| ≤ 1 · gaussDdim 2 (z − 0)`.
    intro z
    simpa using gaussDdim_nonneg (2 : ℝ) z
  · -- `hVol`: `0 = −0 − heatConv 0 0 = 0`.
    intro z
    simp [heatConv]
  · -- `hE1`: `|0 − 0| ≤ 1 · dist z z'`.
    intro z z'
    simpa using dist_nonneg
  · -- `hIz`: `IntervalIntegrable (fun r ↦ ∫ ζ, 0·0) volume 0 1`.
    intro z
    simpa using (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 1)
  · -- `hSlice`: `|0 − 0| ≤ 1 · dist z z' · (1 − r)^{−1/2}`.
    intro z z' r hr
    have h1 : (1 : ℝ) - r > 0 := by
      have := hr.2; simpa using sub_pos.mpr this
    have hrp : (0 : ℝ) ≤ ((1 : ℝ) - r) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg h1.le _
    have : (0 : ℝ) ≤ 1 * dist z z' * ((1 : ℝ) - r) ^ (-(1 : ℝ) / 2) := by
      apply mul_nonneg (mul_nonneg zero_le_one dist_nonneg) hrp
    simpa using this

end QIQTH.CensusLeviFactorDischarge

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CensusLeviFactorDischarge
#print axioms levi_Ffactor_ball_regularity
#print axioms census_ampF_leviF_transported_ratio_regularity
#print axioms census_CfieldF_leviF_transported_ratio_regularity
#print axioms levi_Ffactor_slot_satisfiable
end AxiomChecks
