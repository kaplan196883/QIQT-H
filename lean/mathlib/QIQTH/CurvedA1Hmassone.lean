/-
  CurvedA1Hmassone — J4-588: the `hmassone` base-mass limit for the CURVED van-Vleck witness,
  assessed + reduced (the first genuinely-analytic remaining wall on the curved a₁ = R/6 side).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the curved a₁ = R/6 capstone is NON-VACUOUS but CONDITIONAL — J4-587).  The center-gauge
  fully-wired curved capstone `CurvedA1FullyWiredCenter.curved_a1_R6_fully_wired_center` was
  re-established NON-VACUOUSLY at a genuinely-curved witness `g^K = curvedRNCMetric κ` (`κ < 0`,
  `Ric ≠ 0`, `K` a GENUINE compact — NOT the J4-582 collapsed `{0}`).  It still CARRIES a family of
  analytic residuals, of which the base-mass limit
      `hmassone : Tendsto (fun m => ∫ z, Wit (epsSeq m) 0 z) atTop (𝓝 1)`,
      `Wit := vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b`,
  is the heat-kernel UNIT-MASS normalization: the gated van-Vleck parametrix carries unit heat mass
  at field point `0` as time `εₘ ↓ 0`.  J4-582 proved this FALSE for `K = {0}` (the source support
  collapses to a null singleton, `∫ = 0 ≠ 1`); on a GENUINE `K` (the center-gauge capstone) the
  collapse is gone, so `hmassone` becomes a genuine analytic question.

  ── ★★ VERDICT (J4-588): `hmassone` is a DEEP-CARRIED analytic input admitting a THIN REDUCTION. ──
    `hmassone` is EXACTLY the `f ≡ 1` special case of the banked, axiom-free CONDITIONAL W1 limit-value
    capstone `ChartImageAIConcrete.chartImage_approx_identity_conditional`:
        `Tendsto (fun τ => ∫ z, Wit τ 0 z · f z) (𝓝[>]0) (𝓝 (f 0))`.
    At `f ≡ 1`: `f 0 = 1` and `∫ z, Wit τ 0 z · 1 = ∫ z, Wit τ 0 z`, so the capstone delivers the
    `𝓝[>]0`-form base mass → 1; composing with `epsSeq m = 1/(m+1) → 𝓝[>]0` yields the EXACT `atTop`
    `hmassone` shape.  The leading term as `τ ↓ 0` is the flat Gaussian `gaussDdim τ w` (banked mass
    `∫ = 1`); the curved correction is carried by the amplitude center normalization
    `A₀(0) = radialCutoff a b 0 · vanVleck(g^K)(0)^{−1/2} · u₀(0) = 1` (the van-Vleck `Θ(0)=1`,
    `u₀(0)=1`, `cutoff(0)=1` diagonal facts), which is precisely why the total density → 1.

    BUT the capstone is CONDITIONAL on residuals that are NOT banked (Sol-confirmed classification):
      (a) the BASE-VARYING change-of-variables (CoV) bundle M1–M4 for the chart
          `Wbv : z ↦ uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0`
          (derivative field `f'`, injectivity `hinj`, left inverse `V`, positive Jacobian `hJpos`).
          The ONLY banked concrete CoV bundle is for the FIELD-VARYING `Wfv` (base fixed `0`); the
          base-varying package is the acknowledged MISSING brick (`ChartImageAIConcrete` ORIENTATION
          VERDICT), a separate, harder IFT construction.
      (b) the Layer-C moving-integrand facts (`hmeas`/`hbound`/`hlocal`) encoding the curved amplitude
          joint limit `A(τ,z) → 1` + `det`/`f` continuity, plus the chart-image `Ω = Wbv ''(ball 0 ρ)`
          measurability / neighbourhood facts (`hΩmeas`/`hΩnhds`).
    None of (a)/(b) reduces to the one-line banked Gaussian mass fact `∫ gaussDdim τ w = 1`: that fact
    only evaluates the flat limiting integral, not the local invertibility / Jacobian control / gate
    activation / amplitude joint limit that the curved manifold normalization needs.  So `hmassone` is
    a GENUINE carried analytic input — on par with `hsrc`/`hOffCollarTail` — with a thin reduction to
    the named residuals, NOT a thin banked fact.

  ── WHAT LANDS HERE.
    • `curved_hmassone_at_gate` — ★ the THIN REDUCTION.  Instantiates
      `chartImage_approx_identity_conditional` at `g^K = curvedRNCMetric κ`, `f ≡ 1`, then composes with
      `epsSeq → 𝓝[>]0` to produce the EXACT curved capstone `hmassone` shape from the named residuals
      (the base-varying CoV bundle + Layer-C moving-integrand facts).  This DISCHARGES the curved
      capstone's carried `hmassone` MODULO those residuals — i.e. it names precisely what is still owed.
    • `curved_hmassone_gate_forces_nontrivial_K` — ★ the NON-VACUITY guard (anti-J4-582).  For `ρ > 0`,
      `n ≥ 1`, the gate-activation `hGgate` (`ball 0 ρ ⊆ K`) FORCES `K` to contain a nonzero point, so
      `K ≠ {0}`: the reduction's gate is consistent only with a GENUINE `K` (positive-measure source
      support), exactly the center-gauge capstone's regime.  On J4-582's `K = {0}` the gate is
      inconsistent with `ρ > 0` (`ball 0 ρ ⊄ {0}`), so the collapse that killed `hmassone` cannot recur.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  The curved a₁ = R/6 capstone is
  NON-VACUOUS (J4-587) but CONDITIONAL on carried residuals INCLUDING `hmassone`.  This brick determines
  that `hmassone` is a genuine DEEP analytic input (like `hsrc`), reducible to the named base-varying CoV
  bundle + moving-integrand facts (none banked), NOT a thin banked Gaussian fact.  `a₁ = R/6` remains
  CONDITIONAL.  No `sorry`, no new axioms, no `:= True`, no vacuous / conclusion-in-disguise hypothesis
  (every residual is a standard, simultaneously-satisfiable CoV / approximate-identity input, each
  strictly weaker than the `Tendsto` conclusion), no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.ChartImageAIConcrete
import QIQTH.A1R6CoreAtGate
import QIQTH.CurvedRNCGaussWitness
import QIQTH.CurvedRNCGaugeBundle

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.ChartImageAIConcrete QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open scoped Topology

namespace QIQTH.CurvedA1Hmassone

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The thin reduction — the curved capstone's `hmassone` from the named residuals. -/

/-- **★★ J4-588 — `curved_hmassone_at_gate` — the curved base-mass limit `hmassone` REDUCED.**  The
    EXACT `hmassone` shape carried by `CurvedA1FullyWiredCenter.curved_a1_R6_fully_wired_center`,
        `Tendsto (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b (epsSeq m) 0 z) atTop (𝓝 1)`,
    obtained as the `f ≡ 1` special case of the banked conditional W1 capstone
    `ChartImageAIConcrete.chartImage_approx_identity_conditional`, composed with `epsSeq → 𝓝[>]0`.
    CONDITIONAL on the SAME residuals the capstone isolates, here for the CURVED metric `g^K`:
      • the BASE-VARYING CoV bundle M1–M4 for `Wbv : z ↦ uniformInverseChart (curvedRNCMetric κ)
        (curvedRNCInv κ) hChr hK z 0` on `ball 0 ρ` (`hfd`/`hinj`/`hV`/`hJpos`) — the acknowledged
        MISSING brick (ORIENTATION VERDICT);
      • gate-activation `hGgate` (`ball 0 ρ ⊆ K`) + support-in-ball `hSupp`;
      • chart-image `Ω = Wbv ''(ball 0 ρ)` measurability / neighbourhood (`hΩmeas`/`hΩnhds`);
      • the Layer-C moving-integrand facts (`hmeas`/`hbound`/`hlocal`) toward `L = 1`, encoding the
        curved amplitude joint limit `A(τ,z) → 1` (`A₀(0) = 1`) + Jacobian continuity.
    ⚠ This DISCHARGES the carried `hmassone` MODULO those residuals — none banked.  `hmassone` is a
    GENUINE deep analytic input, not a thin banked Gaussian mass fact.  NOT `a₁ = R/6`. -/
theorem curved_hmassone_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ)
    (ρ : ℝ) (V : Point n → Point n) (f' : Point n → (Point n →L[ℝ] Point n))
    (hfd : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      HasFDerivWithinAt
        (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0) (f' z)
        (Metric.ball (0 : Point n) ρ) z)
    (hinj : Set.InjOn
      (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
      (Metric.ball (0 : Point n) ρ))
    (hV : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      V (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0) = z)
    (hJpos : ∀ z ∈ Metric.ball (0 : Point n) ρ, 0 < |(f' z).det|)
    (hGgate : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      z ∈ K ∧ (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z)
    (hSupp : ∀ τ, ∀ z, z ∉ Metric.ball (0 : Point n) ρ →
      vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b τ (0 : Point n) z = 0)
    (hΩmeas : MeasurableSet
      ((fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
        '' (Metric.ball (0 : Point n) ρ)))
    (hΩnhds : (fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
        '' (Metric.ball (0 : Point n) ρ) ∈ 𝓝 (0 : Point n))
    (hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable
        (fun w => chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ (V w) 0
          * (1 : ℝ) / |(f' (V w)).det|)
        (volume.restrict
          ((fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
            '' (Metric.ball (0 : Point n) ρ))))
    (hbound : ∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂(volume.restrict
          ((fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
            '' (Metric.ball (0 : Point n) ρ))),
        ‖chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ (V w) 0
          * (1 : ℝ) / |(f' (V w)).det|‖ ≤ C)
    (hlocal : ∀ ε > 0, ∃ r > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂(volume.restrict
          ((fun z => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
            '' (Metric.ball (0 : Point n) ρ))),
        ‖w‖ < r →
          ‖chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ (V w) 0
            * (1 : ℝ) / |(f' (V w)).det| - (1 : ℝ)‖ < ε) :
    Tendsto (fun m => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
        (epsSeq m) (0 : Point n) z) atTop (𝓝 1) := by
  -- the `f ≡ 1` special case of the banked conditional W1 capstone (`𝓝[>]0` form)
  have hbase := chartImage_approx_identity_conditional
    (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b
    (fun _ => (1 : ℝ)) ρ V f' hfd hinj hV hJpos hGgate hSupp hΩmeas hΩnhds hmeas hbound hlocal
  -- `epsSeq → 𝓝[>]0` (positive, → 0)
  have heps : Tendsto (epsSeq : ℕ → ℝ) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      epsSeq_tendsto (Filter.Eventually.of_forall (fun m => epsSeq_pos m))
  -- compose and clean up `f 0 = 1`, `Wit · 1 = Wit`, `∘ epsSeq`
  have hcomp := hbase.comp heps
  simpa using hcomp

/-! ### The non-vacuity guard — the gate forces a GENUINE `K` (anti-J4-582). -/

/-- **★ J4-588 — `curved_hmassone_gate_forces_nontrivial_K` — the reduction's gate is CURVED-genuine.**
    For `ρ > 0` and `n ≥ 1`, the gate-activation hypothesis `hGgate` of `curved_hmassone_at_gate`
    (`ball 0 ρ ⊆ K`) FORCES `K` to contain a nonzero point, so `K ≠ {0}`.  Hence the reduction's gate is
    consistent ONLY with a GENUINE compact `K` (positive-measure source support) — exactly the
    center-gauge capstone's regime.  Contrast J4-582: there `K = {0}` collapsed the source and killed
    `hmassone` (`∫ = 0 ≠ 1`); here `ρ > 0` is inconsistent with `K = {0}` (`ball 0 ρ ⊄ {0}`), so the
    collapse CANNOT recur.  This certifies `curved_hmassone_at_gate` is NON-VACUOUS on the genuine `K`
    of the center-gauge curved capstone.  ⚠ Does NOT prove `hmassone` (the deep residuals stay owed).
    NOT `a₁ = R/6`. -/
theorem curved_hmassone_gate_forces_nontrivial_K (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ)
    (ρ : ℝ) (hρ : 0 < ρ) (hn : 1 ≤ n)
    (hGgate : ∀ z ∈ Metric.ball (0 : Point n) ρ,
      z ∈ K ∧ (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z) :
    ∃ z : Point n, z ∈ K ∧ z ≠ (0 : Point n) := by
  refine ⟨fun _ => ρ / 2, (hGgate _ ?_).1, ?_⟩
  · -- `fun _ => ρ/2 ∈ ball 0 ρ`
    rw [Metric.mem_ball, dist_pi_lt_iff hρ]
    intro i
    simp only [Pi.zero_apply, Real.dist_eq, sub_zero]
    rw [abs_of_pos (by linarith : (0 : ℝ) < ρ / 2)]
    linarith
  · -- `fun _ => ρ/2 ≠ 0` (evaluate at index `0`, `n ≥ 1`)
    intro h
    have hval := congrFun h ⟨0, by omega⟩
    simp only [Pi.zero_apply] at hval
    linarith

end QIQTH.CurvedA1Hmassone

/-! ### Axiom audit. -/

section AxiomChecks

open QIQTH.CurvedA1Hmassone

#print axioms curved_hmassone_at_gate
#print axioms curved_hmassone_gate_forces_nontrivial_K

end AxiomChecks
