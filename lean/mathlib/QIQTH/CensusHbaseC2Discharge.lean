/-
  CensusHbaseC2Discharge — J4-941: DISCHARGE the `hbaseC2` carry of the census-family regularity
  lemmas, UNCONDITIONALLY.

  ROLE.  Across J4-930..J4-940 the `hCensusBound` (the hCross wall) was reduced to EXACTLY TWO
  remaining obligations:
    (a) the F-factor's ball-local bounded+Lipschitz regularity (the `leviSeries` carry, downstream of
        `Ebound`/`heatConv` — the `{hDuhamel, hDConv, hCConv}`-family input), and
    (b) `hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) 0`  — the base-slot
        `C²` regularity of the base-varying chart `Wbv z := uniformInverseChart g gi hC hK z 0`,
        carried as an explicit HYPOTHESIS by the census-family lemmas of `BaseSlotTransportBallLocal`
        (J4-939) and its dependencies.

  THIS FILE closes obligation (b) AT THE POINT OF USE.  `hbaseC2` is NOT a genuine open obligation:
  it is EXACTLY the unconditional conclusion of `QIQTH.TerminalVelC2.terminalVel0_contDiffAt_two`
  (`hT0`, the base-`0` terminal-velocity `C²`, discharged UNCONDITIONALLY at J4-274 via the geodesic
  homogeneity route) fed through the geodesic-reversal transfer
  `QIQTH.GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt`.  The recent census lemmas simply
  carried it as a hypothesis instead of instantiating the banked discharge.

  ── WHAT LANDS.
    • `wbv_contDiffAt_two` — the STANDALONE UNCONDITIONAL `hbaseC2` object:
          `ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) 0`
      given only the standing geometry `(hC, hK, K ∈ 𝓝 0)`.  A one-composition bridge of two banked
      unconditional results — NO new hypothesis.
    • `census_ampF_transported_ratio_regularity_unconditional`,
      `census_CfieldF_transported_ratio_regularity_unconditional`,
      `transported_ratio_regularity_ballLocal_unconditional` — the census-family transport regularity
      lemmas of `BaseSlotTransportBallLocal` with the `hbaseC2` hypothesis REMOVED (discharged by
      `wbv_contDiffAt_two`).  The only remaining regularity input is the ABSTRACT F-factor
      (`F0`, the honest Levi carry).

  ── HONEST STATUS.  With obligation (b) closed unconditionally, the census-family transport
    regularity lemmas depend ONLY on the abstract F-factor `F0` (obligation (a), the
    `{hDuhamel, hDConv, hCConv}`-family — NOT touched here).  `hCensusBound`/`hCross` therefore remain
    carried through `{hDuhamel, hDConv, hCConv}` alone; `a₁ = R/6` remains CONDITIONAL on
    `{hDuhamel, hDConv, hCConv}`.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  No `sorry`, no new axioms, no
  `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypotheses.  `wbv_contDiffAt_two`
  is a genuine composition of two DIFFERENT banked facts (the terminal-velocity `C²` and the
  reversal transfer); it does not trivially yield the census conclusions (those additionally carry
  the concrete amplitude regularity and the abstract F-factor).  No existing file is edited.
-/
import Mathlib
import QIQTH.TerminalVelC2
import QIQTH.BaseSlotTransportBallLocal

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators

namespace QIQTH.CensusHbaseC2Discharge

open QIQTH.GeodesicReversalRoute QIQTH.TerminalVelC2 QIQTH.BaseSlotTransportBallLocal
open QIQTH.CensusTauDerivGateSplit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The standalone UNCONDITIONAL `hbaseC2`. -/

/-- **★★ `wbv_contDiffAt_two` — the base-slot `C²` of `Wbv`, UNCONDITIONAL (given `K ∈ 𝓝 0`).**
    The base-varying chart `Wbv z := uniformInverseChart g gi hC hK z 0` is `ContDiffAt ℝ 2` at the
    centre `0`.  Composition of two banked UNCONDITIONAL facts:
      • `terminalVel0_contDiffAt_two` (J4-274) — the base-`0` terminal-velocity `C²` (`hT0`), via the
        geodesic homogeneity route (velocity endpoint = differential-of-`exp` on the diagonal); and
      • `hbaseC2_of_terminalVel_contDiffAt` (J4-273) — the geodesic-reversal transfer turning `hT0`
        into the base-slot chart `C²` through the reversal identity `Wbv z = − T₀ (U 0 z)`.
    NO regularity hypothesis beyond the standing geometry.  This is EXACTLY the `hbaseC2` carried as a
    hypothesis by the census-family lemmas.  NOT `a₁ = R/6`. -/
theorem wbv_contDiffAt_two (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n) :=
  hbaseC2_of_terminalVel_contDiffAt g gi hC hK h0Kmem
    (terminalVel0_contDiffAt_two g gi hC hK (mem_of_mem_nhds h0Kmem))

/-! ### UNCONDITIONAL census-family transport regularity (the `hbaseC2` carry discharged). -/

/-- **★★ `transported_ratio_regularity_ballLocal_unconditional`.**  J4-939's ball-local transported
    ratio regularity with the `hbaseC2` hypothesis DISCHARGED by `wbv_contDiffAt_two`.  For ANY weight
    `P` bounded + pairwise-Lipschitz on a base ball, the transported ratio
    `w ↦ P (V w) / |det (fderiv Wbv (V w))|` is bounded + pairwise-Lipschitz on an image ball —
    with NO `hbaseC2` hypothesis.  NOT `a₁ = R/6`. -/
theorem transported_ratio_regularity_ballLocal_unconditional (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (P : Point n → ℝ) (rP M_P L_P : ℝ) (hrP : 0 < rP) (hMP : 0 ≤ M_P) (hLP : 0 ≤ L_P)
    (hPb : ∀ z ∈ Metric.ball (0 : Point n) rP, |P z| ≤ M_P)
    (hPl : ∀ x ∈ Metric.ball (0 : Point n) rP, ∀ y ∈ Metric.ball (0 : Point n) rP,
      |P x - P y| ≤ L_P * dist x y) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (Lc : ℝ), 0 ≤ Lc ∧ V 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (P (V w) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|)
          ≤ M_P / (1 / 2 : ℝ)) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        abs (P (V x) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V x)).det|
            - P (V y) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V y)).det|)
          ≤ Lc * dist x y) :=
  transported_ratio_regularity_ballLocal g gi hC hK h0Kmem
    (wbv_contDiffAt_two g gi hC hK h0Kmem) P rP M_P L_P hrP hMP hLP hPb hPl

/-- **★★ `census_ampF_transported_ratio_regularity_unconditional` — the concrete q₁ transported,
    `hbaseC2` DISCHARGED.**  J4-939's amplitude-half census transport regularity with the `hbaseC2`
    hypothesis removed (via `wbv_contDiffAt_two`).  The transported census integrand
    `w ↦ (chartFieldAmp … τ (V w) 0 · F0 (V w)) / |det (fderiv Wbv (V w))|` is bounded + pairwise-
    Lipschitz on an image ball, with the amplitude factor concrete and ONLY the abstract F-factor
    `F0` carried.  NOT `a₁ = R/6`. -/
theorem census_ampF_transported_ratio_regularity_unconditional (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F0 : Point n → ℝ) (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMFnn : 0 ≤ M_F) (hLFnn : 0 ≤ L_F)
    (hFb : ∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F)
    (hFl : ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (M Lc : ℝ), 0 ≤ M ∧ 0 ≤ Lc ∧ V 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (chartFieldAmp g gi hC hK a b τ (V w) 0 * F0 (V w)
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|) ≤ M) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        abs (chartFieldAmp g gi hC hK a b τ (V x) 0 * F0 (V x)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V x)).det|
            - chartFieldAmp g gi hC hK a b τ (V y) 0 * F0 (V y)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V y)).det|)
          ≤ Lc * dist x y) :=
  census_ampF_transported_ratio_regularity g gi hC hK a b τ h0Kmem
    (wbv_contDiffAt_two g gi hC hK h0Kmem) hg hg0 hu F0 rF M_F L_F hrF hMFnn hLFnn hFb hFl

/-- **★★ `census_CfieldF_transported_ratio_regularity_unconditional` — the concrete q₂ transported,
    `hbaseC2` DISCHARGED.**  As `census_ampF_transported_ratio_regularity_unconditional` but for the
    `∂_τ`-slope weight `censusAmpTauDeriv · F0`.  `hbaseC2` removed via `wbv_contDiffAt_two`.
    NOT `a₁ = R/6`. -/
theorem census_CfieldF_transported_ratio_regularity_unconditional
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F0 : Point n → ℝ) (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMFnn : 0 ≤ M_F) (hLFnn : 0 ≤ L_F)
    (hFb : ∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F)
    (hFl : ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (M Lc : ℝ), 0 ≤ M ∧ 0 ≤ Lc ∧ V 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (censusAmpTauDeriv g gi hC hK a b (V w) * F0 (V w)
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|) ≤ M) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        abs (censusAmpTauDeriv g gi hC hK a b (V x) * F0 (V x)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V x)).det|
            - censusAmpTauDeriv g gi hC hK a b (V y) * F0 (V y)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V y)).det|)
          ≤ Lc * dist x y) :=
  census_CfieldF_transported_ratio_regularity g gi hC hK a b h0Kmem
    (wbv_contDiffAt_two g gi hC hK h0Kmem) hg hg0 hu F0 rF M_F L_F hrF hMFnn hLFnn hFb hFl

end QIQTH.CensusHbaseC2Discharge

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.CensusHbaseC2Discharge
#print axioms wbv_contDiffAt_two
#print axioms transported_ratio_regularity_ballLocal_unconditional
#print axioms census_ampF_transported_ratio_regularity_unconditional
#print axioms census_CfieldF_transported_ratio_regularity_unconditional
end AxiomChecks
