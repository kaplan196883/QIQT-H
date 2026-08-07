/-
  CensusDominations — J4-382: THE CENSUS DOMINATIONS PILE (v) + THE TIME FLOOR (iii).
  Discharging piles (iii) [`aa`/`0<aa`/`aa≤u`/`u≤T`] and part of (v) [`hAdomHeat`, the heat-kernel
  Gaussian domination] of the census antecedent exposed by
  `CensusGeometryThread.hDaLimLU_from_geometry_census` (J4-381).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  SURVIVING census carries (the W2 differentiation-under-∫ family, the Levi envelope, the SECOND-x-
  derivative Gaussian domination `hAdom2`, the four s-slice measurabilities, the amplitude bundle, the
  atomic interchange carrier, and the E-combination facts).  This file discharges only two of the
  cheapest piles.  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO vacuous /
  unsatisfiable hypothesis, NONE equal to (or trivially yielding) the conclusion, NO existing file
  edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS.

  •  (D1) `timeWindow_facts` — THE TIME FLOOR / WINDOW, pile (iii).  For `T > 0` the concrete window
     `U := Set.Ioo (T/2) T` satisfies EXACTLY the (iii) binder shape with `aa := T/2`:
     `0 < T/2 ∧ IsOpen (Ioo (T/2) T) ∧ (∀ u ∈ Ioo (T/2) T, T/2 ≤ u) ∧ (∀ u ∈ Ioo (T/2) T, u ≤ T)`.
     Pure arithmetic — `le_of_lt` on the `Ioo` endpoints.

  •  (D2) `hAdomHeat_from_hEdom` — THE HEAT-KERNEL GAUSSIAN DOMINATION `hAdomHeat`, pile (v), FROM the
     geometry-derived width-3/2 `hEdom` inner body (`CommonGateShell.hEdom_from_geometry`).  Pure
     repackaging AT `p = 0, q = z`: from
         `|heatOp … τ p q| ≤ (E₀ + E₁·τ)·√(3/2)ⁿ·gaussDdim ((3/2)·τ) (p − q)`   (∀ τ>0)
     it derives, for `0 < τ ≤ T`,
         `|heatOp … τ 0 z| ≤ ((E₀ + E₁·T)·√(3/2)ⁿ)·gaussDdim ((3/2)·τ) (0 − z)`,
     i.e. the `hAdomHeat` shape with `wA := 3/2`, `CA := (E₀ + E₁·T)·√(3/2)ⁿ` — the `τ ↦ T` monotone
     absorption of the linear coefficient (needs `E₁ ≥ 0`, `τ ≤ T`) times the nonneg Gaussian.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT REMAINS CARRIED (honest inventory — NOT discharged here).

  •  (D3) `hAdom2` — the SECOND-`x`-derivative Gaussian domination
         `|witnessSecondXDeriv … i τ z| ≤ CA2·gaussDdim (wA2·τ) (0 − z)`   (∀ 0<τ≤T).
     ⚠  NO banked bound of THIS clean `CA2·gaussDdim (wA2·τ)` shape exists at the concrete van-Vleck
     witness.  The only banked second-derivative domination
     (`WideWitnessAmplitude.WideAmplitudePackage.hSecond`, consumed by `WideSliverBoundary`) has the
     CRUDE `C·τ⁻¹·gaussDdim (lam·τ) z` shape — the `τ⁻¹` prefactor blows up as `τ → 0` and does NOT
     collapse into the clean bounded-coefficient form; the two are genuinely different envelopes.  A
     from-scratch derivation is the geometric second-derivative Gaussian estimate (the moment-aware
     three-term normal-form campaign, `WideSliverBoundary`/`SliverSumPlumbing` bricks 7–10), NOT a one-
     brick repackaging.  Therefore `hAdom2` stays an honest CARRIED hypothesis of the census.

  •  (D4) `hmeasLo`/`hmeasHi`/`hmeas2Lo`/`hmeas2Hi` — the four s-slice `AEStronglyMeasurable` facts for
     `fun s => ∫ z, (heatOp | witnessSecondXDeriv) (u−s) 0 z · leviSeries … s z 0` on the restricted
     `volume`.  These are CONSUMED everywhere in the campaign (`DaLimEasyTranche.hIlo/hIhi/hII_lo/
     hII_hi_concrete`, `CensusSweepOne.census_dominations`/`census_adj`) but SUPPLIED nowhere as this
     exact s-slice shape: the campaign carries them as labelled hypotheses.  A compositional discharge
     would need parametric-integral continuity/measurability of the s-slice pairing (a dominated-
     convergence / joint-measurability argument on `.choose`-heavy witness kernels), out of scope for
     this pile brick.  They stay honest CARRIED hypotheses.

  ▸  SATISFIABILITY.  Both landed lemmas are genuine (D1 = an explicit satisfying window; D2 =
     a monotone repackaging of the real geometry-derived bound).  Neither is the census conclusion.
-/
import Mathlib
import QIQTH.ConvApproximants
import QIQTH.TrueHeatKernel
import QIQTH.FlatHeatEquation
import QIQTH.ResidueBound

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.TrueHeatKernel QIQTH.ResidueBound
open QIQTH.HeatResidualBound
open scoped Topology BigOperators

namespace QIQTH.CensusDominations

variable {n : ℕ}

/-! ###############################################################################
    ### (D1) — `timeWindow_facts`: the residual-domination time floor / window (iii).
    ############################################################################### -/

/-- **(D1) — `timeWindow_facts`.**  THE TIME FLOOR / WINDOW, census pile (iii).  For `T > 0` the
    concrete window `U := Set.Ioo (T/2) T` realizes the exact (iii) binder shape with floor `aa := T/2`:
    positivity `0 < T/2`, openness, the floor `∀ u ∈ U, T/2 ≤ u`, and the ceiling `∀ u ∈ U, u ≤ T`.
    Pure arithmetic (`le_of_lt` on the `Ioo` endpoints).  ⚠ NOT `a₁ = R/6`. -/
theorem timeWindow_facts (T : ℝ) (hT : 0 < T) :
    0 < T / 2 ∧ IsOpen (Set.Ioo (T / 2) T)
      ∧ (∀ u ∈ Set.Ioo (T / 2) T, T / 2 ≤ u)
      ∧ (∀ u ∈ Set.Ioo (T / 2) T, u ≤ T) := by
  refine ⟨by linarith, isOpen_Ioo, ?_, ?_⟩
  · intro u hu; exact le_of_lt hu.1
  · intro u hu; exact le_of_lt hu.2

/-! ###############################################################################
    ### (D2) — `hAdomHeat_from_hEdom`: the heat-kernel Gaussian domination (v).
    ############################################################################### -/

/-- **(D2) — `hAdomHeat_from_hEdom`.**  THE HEAT-KERNEL GAUSSIAN DOMINATION `hAdomHeat`, census pile
    (v), repackaged FROM the geometry-derived width-3/2 `hEdom` inner body
    (`CommonGateShell.hEdom_from_geometry`, whose body is exactly the `hEdom` hypothesis here).
    Instantiating `p := 0`, `q := z` and absorbing the linear coefficient `E₀ + E₁·τ ≤ E₀ + E₁·T`
    (via `τ ≤ T`, `E₁ ≥ 0`) against the nonneg Gaussian gives the `hAdomHeat` shape with
    `wA := 3/2`, `CA := (E₀ + E₁·T)·√(3/2)ⁿ`.  ⚠ NOT `a₁ = R/6`. -/
theorem hAdomHeat_from_hEdom (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (E₀ E₁ : ℝ) (hE₁ : 0 ≤ E₁)
    (hEdom : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) :
    ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ z : Point n,
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ 0 z|
        ≤ ((E₀ + E₁ * T) * Real.sqrt (3 / 2) ^ n) * gaussDdim (3 / 2 * τ) (0 - z) := by
  intro τ hτ0 hτT z
  refine le_trans (hEdom τ hτ0 0 z) ?_
  refine mul_le_mul_of_nonneg_right ?_ (gaussDdim_nonneg _ _)
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Real.sqrt_nonneg _) n)
  have hp : E₁ * τ ≤ E₁ * T := mul_le_mul_of_nonneg_left hτT hE₁
  linarith

end QIQTH.CensusDominations

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CensusDominations.timeWindow_facts
#print axioms QIQTH.CensusDominations.hAdomHeat_from_hEdom
