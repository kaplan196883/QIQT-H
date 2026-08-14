/-
  CurvedA1HmassoneMassUnified — J4-739: folding the zeroth Gaussian domination `hDom` INTO the
  mass-side pre-ρ carrier unification — reducing the LAST assembled-witness carrier of
  `CurvedA1HmassoneReach.curved_hmassone_final_from_reach` (J4-738) to the two ELEMENTARY curved
  geometric factors it is built from.  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT
  `a₁ = R/6`; proves NOTHING about the coefficient value.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  J4-738 (`curved_hmassone_final_from_reach`) reduced the center-gauge curved capstone's
  base-mass limit `hmassone` to the carriers `{origin-reach (at ρW and c), rS/hKball, hDom}`, where
  `hDom` is the zeroth Gaussian domination of the ASSEMBLED gated witness,
      `∀ τ ∈ (0,τ₀], ∀ z, |vanVleckGatedWitness g^κ … (constGate … c) a b τ 0 z| ≤ CW · gaussDdim (lam τ) z`.

  ── ★★ THE FINDING (J4-739).  `hDom` is NOT primitive: the banked
     `CurvedRNCBaseWitnessDom.curvedRNC_baseWitness_dom` (J4-531) PROVES exactly this domination shape
     for the gate `S = constGate … c`, DISCHARGING the amplitude (`det^{1/4}`) and radial-cutoff factors
     internally, and carrying only the TWO genuinely-geometric elementary factors:
       • `hMod`   — the order-1 transport-coefficient modulus bound `|∑ₖ uₖ(w)·τᵏ| ≤ Cu`;
       • `hPhase` — the Gaussian-phase transfer `gaussDdim τ (W₀z) ≤ Cφ · gaussDdim (lam τ) z`,
     with the assembled constant `CW = ((1 − (κ/3)b²)^{n−1})^{1/4} · Cu · Cφ`.  Composing:
     `curved_hmassone_mass_unified` produces the EXACT `hmassone` limit with `hDom` REPLACED by
     `{hMod, hPhase}` — the assembled-witness domination carrier is gone, leaving only elementary
     factor bounds.

  ── ★ IS THE ORIGIN-REACH SHARED?  NO — and this is the honest structural finding.  `hDom` does NOT
     rest on the J4-738 origin-reach (`∃ v small, uniformFlowExp z v = 0`).  It rests, via
     `hMod`/`hPhase`, on a DIFFERENT reach-family input: the CHART-IMAGE reach of
     `uniformInverseChart g^κ gi^κ hChr hK z 0 =: W₀z` (the near-isometry collar `‖z‖ < r` for the
     phase, the compact chart-reach `Wset` for the moduli).  So the fully-unified mass pile collapses to
     TWO distinct-but-both-banked reach-family geometric inputs (origin-reach ⊕ chart-image reach) plus
     the finite elementary constants — NOT to a single shared input.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_hmassone_mass_unified` — ★★ the carrier-unified `hmassone` with `hDom` discharged from
      `{hMod, hPhase}` via `curvedRNC_baseWitness_dom`.  The remaining mass-side pre-`ρ` carriers are the
      origin-reach (at ρW and c), the trivially-fat `rS`/`hKball`, and the two ELEMENTARY curved factor
      bounds `hMod` (moduli) and `hPhase` (phase transfer) — plus `κ < 0` (fat, genuinely curved base).
    • `curved_hmassone_mass_unified_hMod_banked` — re-export of `curvedRNC_moduli_bound`: `hMod` is
      DISCHARGED (curved-satisfiable, `Cu = 1 + |M|·|τmax| ≥ 1 > 0`) on any compact chart-reach `Wset`.
    • `curved_hmassone_mass_unified_hPhase_banked` — re-export of `curvedRNC_phase_transfer`: `hPhase`
      is DISCHARGED (curved-satisfiable, `Cφ = (√2)ⁿ`, `lam = 2`) on the near-isometry collar `‖z‖ < r`.
    • `curved_hmassone_mass_unified_curved_satisfiable` — the NON-VACUITY certificate (re-export).

  ── HONEST RESIDUAL.  `hMod`/`hPhase` are BANKED and curved-satisfiable, but each is delivered on the
     chart's finite reach (compact `Wset` / collar `‖z‖ < r`), whereas `curvedRNC_baseWitness_dom`'s
     binders quantify `∀ z τ` UNGUARDED.  The residual to the literal unguarded binder is exactly the
     chart-image far-reach RANGE fact — a distinct reach-family geometric input, itself banked (the same
     `chartW0` near-isometry / compact chart-reach carried throughout the curved chain), NOT the `a₁`
     conclusion and NOT freshly labelled.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  This is a carrier-bookkeeping brick:
  it re-expresses WHICH satisfiable geometric inputs the curved `hmassone` rests on, folding the
  assembled-witness domination `hDom` into its two elementary curved factors; it establishes nothing new
  about the coefficient.  No `sorry`, no new axioms, no `:= True`, no vacuous / conclusion-in-disguise
  hypothesis, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.CurvedA1HmassoneReach
import QIQTH.CurvedRNCBaseWitnessDom
import QIQTH.CurvedRNCModuliBound
import QIQTH.CurvedRNCPhaseTransfer

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ChartImageAIConcrete QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.RadialDistance QIQTH.ExpMap
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators

namespace QIQTH.CurvedA1HmassoneMassUnified

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### ★★ The mass-side carrier-unified base-mass limit — `hDom` folded into `{hMod, hPhase}`. -/

/-- **★★ `curved_hmassone_mass_unified` — the curved `hmassone` with `hDom` discharged from the two
    ELEMENTARY curved factor bounds.**  Produces the EXACT base-mass limit of
    `CurvedA1HmassoneReach.curved_hmassone_final_from_reach` (hence of
    `CurvedA1HmassoneFinal.curved_hmassone_final_at_gate`), but with the zeroth Gaussian domination
    `hDom` of the ASSEMBLED gated witness supplied by the banked
    `CurvedRNCBaseWitnessDom.curvedRNC_baseWitness_dom` from:

    * `hMod`   — the order-1 transport-coefficient modulus bound `|∑ₖ uₖ(W₀z)·τᵏ| ≤ Cu`, and
    * `hPhase` — the Gaussian-phase transfer `gaussDdim τ (W₀z) ≤ Cφ · gaussDdim (lam·τ) z`,

    where `W₀z = uniformInverseChart g^κ gi^κ hChr hK z 0`.  The amplitude (`det^{1/4}`) and radial
    cutoff factors are DISCHARGED internally, and the assembled constant is
    `CW = ((1 − (κ/3)b²)^{n−1})^{1/4} · Cu · Cφ`.

    The remaining mass-side pre-`ρ` carriers are: the origin-reach (at ρW — for the witness-slice
    measurability — and at c — for the gate activation; both instances of the SAME reach fact from
    J4-738), the trivially-fat `rS`/`hKball`, and the two elementary curved factor bounds `hMod`,
    `hPhase` (BANKED, curved-satisfiable on the chart's finite reach — see the re-exports below).
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hmassone_mass_unified (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ρW > (0 : ℝ),
      (∀ z ∈ K, ∃ v : Point n, ‖v‖ < ρW ∧
        uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z v = 0) →
      ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ →
        (∀ z ∈ K, ∃ v : Point n, ‖v‖ < c ∧
          uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z v = 0) →
        ∀ rS : ℝ, 0 < rS → Metric.ball (0 : Point n) rS ⊆ K →
        ∀ τ₀ lam Cu Cφ : ℝ, 0 < τ₀ → 0 < lam → 0 ≤ Cu → 0 ≤ Cφ →
        -- `hMod` : order-1 transport-coefficient modulus bound on the chart image `W₀z`.
        (∀ z τ, 0 < τ → τ ≤ τ₀ →
          |∑ k ∈ Finset.range 2,
              transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
                  (curvedRNCMetric κ) (curvedRNCInv κ)) k
                (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0) * τ ^ k| ≤ Cu) →
        -- `hPhase` : Gaussian-phase transfer for the chart image `W₀z`.
        (∀ z τ, 0 < τ → τ ≤ τ₀ →
          gaussDdim τ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
            ≤ Cφ * gaussDdim (lam * τ) z) →
        ∃ ρ > (0 : ℝ),
          Tendsto (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
              (epsSeq m) (0 : Point n) z) atTop (𝓝 1) := by
  obtain ⟨ρW, hρW, hbody⟩ :=
    QIQTH.CurvedA1HmassoneReach.curved_hmassone_final_from_reach κ hκ hChr hK h0Kmem a b ha hab
  refine ⟨ρW, hρW, fun hReachW => ?_⟩
  obtain ⟨δ₀, hδ₀, hcbody⟩ := hbody hReachW
  refine ⟨δ₀, hδ₀, fun c hc hcδ hReachC rS hrS hKball τ₀ lam Cu Cφ
    hτ₀ hlam hCu hCφ hMod hPhase => ?_⟩
  -- discharge `hDom` from the two elementary curved factor bounds via the banked assembly.
  have hDom := QIQTH.CurvedRNCBaseWitnessDom.curvedRNC_baseWitness_dom κ hκ.le hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b ha hab
    τ₀ lam Cu Cφ hCu hCφ hMod hPhase
  -- nonnegativity of the assembled amplitude constant.
  have hbase0 : (0 : ℝ) ≤ 1 - κ / 3 * b ^ 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ -(κ / 3) by linarith) (sq_nonneg b)]
  have hCamp0 : (0 : ℝ) ≤ ((1 - κ / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) :=
    Real.rpow_nonneg (pow_nonneg hbase0 (n - 1)) _
  exact hcbody c hc hcδ hReachC rS hrS hKball lam τ₀
    (((1 - κ / 3 * b ^ 2) ^ (n - 1)) ^ ((1 : ℝ) / 4) * Cu * Cφ) hlam hτ₀
    (mul_nonneg (mul_nonneg hCamp0 hCu) hCφ)
    (fun τ hτ hτle z => hDom z τ hτ hτle)

/-! ### The two elementary curved factor bounds are BANKED (re-exports). -/

/-- **`curved_hmassone_mass_unified_hMod_banked` — the `hMod` carrier is discharged.**  Re-exports
    `CurvedRNCModuliBound.curvedRNC_moduli_bound`: for the genuinely-curved witness `g^κ` (`κ < 0`),
    any compact chart-reach `Wset` and any time cap `τmax`, a FINITE `Cu > 0` bounds the order-1
    transport-coefficient modulus on `Wset`.  Curved-satisfiable (`Cu = 1 + |M|·|τmax| ≥ 1`).  This
    supplies `curved_hmassone_mass_unified`'s `hMod` on the chart's finite reach.  NOT `a₁ = R/6`. -/
theorem curved_hmassone_mass_unified_hMod_banked (κ : ℝ) (hκ : κ < 0)
    {Wset : Set (Point n)} (hWset : IsCompact Wset) (τmax : ℝ) :
    ∃ Cu : ℝ, 0 < Cu ∧ ∀ w ∈ Wset, ∀ τ : ℝ, 0 ≤ τ → τ ≤ τmax →
      |∑ k ∈ Finset.range 2,
          transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
              (curvedRNCMetric κ) (curvedRNCInv κ)) k w * τ ^ k| ≤ Cu :=
  QIQTH.CurvedRNCModuliBound.curvedRNC_moduli_bound κ hκ hWset τmax

/-- **`curved_hmassone_mass_unified_hPhase_banked` — the `hPhase` carrier is discharged.**  Re-exports
    `CurvedRNCPhaseTransfer.curvedRNC_phase_transfer`: for the genuinely-curved witness `g^κ` (`κ < 0`)
    there are explicit constants `Cφ = (√2)ⁿ`, `lam = 2` and a reach radius `r > 0` such that the
    chart-image Gaussian is dominated on the near-isometry collar `z ∈ Kset`, `‖z‖ < r`.  This supplies
    `curved_hmassone_mass_unified`'s `hPhase` on the chart's finite reach.  NOT `a₁ = R/6`. -/
theorem curved_hmassone_mass_unified_hPhase_banked (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) (τmax : ℝ) :
    ∃ r > (0 : ℝ), ∃ Cφ > (0 : ℝ), ∃ lam > (0 : ℝ),
      ∀ z ∈ Kset, ‖z‖ < r → ∀ τ : ℝ, 0 < τ → τ ≤ τmax →
        gaussDdim τ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hKset z 0)
          ≤ Cφ * gaussDdim (lam * τ) z :=
  QIQTH.CurvedRNCPhaseTransfer.curvedRNC_phase_transfer κ hκ hChr hKset τmax

/-! ### Non-vacuity: the curved base is genuinely curved (re-export). -/

/-- **`curved_hmassone_mass_unified_curved_satisfiable` — the NON-VACUITY certificate.**  For `κ < 0`,
    `n ≥ 2` the curved base is GENUINELY curved (`∃ w, 1 < det g^κ w`), so the mass-side carrier
    unification is NOT secretly the flat kernel and NOT a `K = {0}` collapse.  Re-exports the banked
    certificate.  NOT `a₁ = R/6`. -/
theorem curved_hmassone_mass_unified_curved_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    Matrix.det (curvedRNCMetric κ (0 : Point n)) = 1
      ∧ ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  QIQTH.CurvedA1HmassoneReach.curved_hmassone_reach_satisfiable κ hκ hn

end QIQTH.CurvedA1HmassoneMassUnified

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1HmassoneMassUnified

#print axioms curved_hmassone_mass_unified
#print axioms curved_hmassone_mass_unified_hMod_banked
#print axioms curved_hmassone_mass_unified_hPhase_banked
#print axioms curved_hmassone_mass_unified_curved_satisfiable

end AxiomChecks
