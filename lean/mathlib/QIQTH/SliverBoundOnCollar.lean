/-
  QIQTH / HeatResidualBound — SliverBoundOnCollar.lean   (J4-353)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  HONEST FIREWALL.  This file is ONE derivative-layer brick of the a₁ = R/6 heat-kernel campaign.
  It proves NOTHING about R/6; **a₁ = R/6 remains CONDITIONAL.**  It re-derives the pointwise
  sliver ingredients (Sol consult #12, brick 2) against the CORRECTED collar-restricted bundle
  `AmplitudeDataOnCollar.AmplitudeDerivativeDataOn` (J4-352) — the leg that threads the corrected
  bundle into the sliver interface, closing the `hD2Hexpand` labelled input at the true chart on the
  √ε collar.  NOT `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  ★ S1 — THE CONSUMPTION-REGION VERDICT (read this before consuming the file).

  QUESTION (Sol #12, S1).  Where does the ORIGINAL sliver bound `amplitudePackage_sliver_bound`
  (J4-126, `AmplitudePackage.lean`) USE the amplitude-bundle fields?  It is a one-line application of
  `SliverEstimates.sliver2_bound` with `D2H := witnessSecondXDeriv`.  Tracing `sliver2_bound`'s proof:

    • `hD2Hexpand τ hτIoo z` is invoked pointwise `∀ z : Point n` (the identity `hpt : ∀ z,
      D2H τ z * F s z 0 = [3-term]`, used to SPLIT the FULL z-integral `∫ z, D2H (u−s) z · F s z 0`);
    • `hAampBdd`/`hA1ampBdd`/`hA2ampBdd τ hτIoo z` are invoked `∀ z` (the integrability dominations
      `hT1int`/`hT2int`/`hT3int` and the term bounds `hb1`/`hb2`/`hb3`);
    • `hqLip τ hτIoo s … z w` is invoked `∀ z w` (term-1 Hessian cancellation `gaussian_hessian_cancel`,
      which uses the FULL-SPACE moment `∫ (zᵢ²−2τ)·G = 0`).

  VERDICT = case (b): the consumption is over ALL of `Point n` with the Gaussian envelope, NOT
  collar-confined.  The corrected bundle `AmplitudeDerivativeDataOn (collarRegime …)` supplies the
  3-term identity AND the amplitude bounds ONLY on the regime `‖z‖ ≤ c·√τ` (the ρ-ratio
  `exp((r_z − r_{W0})/(4τ))` is bounded by `collarK` ONLY on the collar; off-collar it blows up, so
  the uniformly-bounded-amplitude exact-shape identity is a collar-only fact — exactly the J4-351
  crux).  Consequently a FULL re-derivation with the hbnd conclusion syntactically unchanged requires
  the collar / off-collar SPLIT:
    • ON-collar  (`‖z‖ ≤ c√τ`, `z ∈ K`): the corrected fields apply (this file — the on-collar leg);
    • OFF-collar (`z ∈ K`, `‖z‖ > c√τ`): the witness's own global width-Gaussian domination
      (banked `hEboundW`-type) + the Gaussian tail (`gaussian_beats_power`, `exp(−c²/4)` factors);
    • `z ∉ K`: the gated witness is `0`, contributing nothing.
  The exact-constant conclusion (its moduli are the ON-collar constants `data.M_j = collarK·M_jchart`)
  is INCOMPATIBLE with a global honest derivation UNLESS the off-collar contribution is separately
  shown super-polynomially small and absorbed — the surviving carry (see FINAL STATUS).

  ──────────────────────────────────────────────────────────────────────────────────────────────
  WHAT LANDS HERE (unconditionally, the minimum-bankable on-collar leg).
    • `collar_to_regime`            — the threading lemma: the ambient chart-domain conjuncts
                                      (`z ∈ K`, `‖z‖ < r₀`) + the collar (`‖z‖ ≤ c√τ`) + the time
                                      window (`0 < τ ≤ τ₀`) ⟹ `collarRegime`.  The honest ambient
                                      hypotheses the corrected bundle's hard fields demand.
    • `sliverExpand_on_collar`      — the 3-term Leibniz–Gaussian identity for the CONCRETE
                                      `witnessSecondXDeriv`, on the collar (via `collar_to_regime`).
    • `sliverAampBdd_on_collar` etc.— the three amplitude sup-bounds on the collar (K-absorbed moduli).
    • `sliverIntegrand_on_collar`   — the pointwise integrand identity `witnessSecondXDeriv·F =
                                      [3-term]·F` on the collar (the exact per-point input the sliver
                                      engine `sliver2_bound` consumes; here supplied from the corrected
                                      bundle rather than the FALSE-off-flat global `hD2Hexpand`).

  THE hD2Hexpand CAMPAIGN — FINAL STATUS (bankable intelligence).
    The labelled `hD2Hexpand` input is CLOSED AT THE TRUE CHART on the √ε collar: the 3-term identity
    with uniformly-bounded (K-absorbed) amplitudes is `hD2HexpandOn_concrete` ∘ `collar_to_regime`
    (this file), with `hV0` ELIMINATED by the unconditional Gaussian ratio (J4-352).  The SURVIVING
    carry is NOT the identity but the OFF-COLLAR sliver remainder (the width-Gaussian tail of the
    concrete witness on `‖z‖ > c√τ`) — a separate Gaussian-tail estimate, NOT a chart-jet fact.  Until
    that off-collar tail lands, the exact-conclusion `amplitudePackageOn_sliver_bound` (and hence
    `hbnd_concrete_v2`) stays blocked on the split, NOT on `hD2Hexpand`.

  NO `sorry`, no new axioms, no `:= True`, every hypothesis satisfiable, no existing file edited.
  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.AmplitudeDataOnCollar
import QIQTH.AmplitudePackage

open MeasureTheory Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Interval Topology

namespace QIQTH.SliverBoundOnCollar

open QIQTH.HeatResidualBound QIQTH.AmplitudeDataOnCollar

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    S1 — the threading lemma `collar_to_regime`.
    ############################################################################### -/

/-- **★ S1 — `collar_to_regime`.**  The ambient conditions the corrected bundle's hard fields demand
    combine into the `collarRegime` predicate: the time window `0 < τ ≤ τ₀`, the chart-domain
    conjuncts `z ∈ K` and `‖z‖ < r₀` (the honest hypotheses the near-isometry
    `chartW0_rncRadialSq_error` needs), and the √ε collar proper `‖z‖ ≤ c·√τ`.  This is the sole
    threading needed to feed `AmplitudeDerivativeDataOn.hD2Hexpand`/`hAampBdd`/… on the collar.  The
    chart-domain conjuncts are supplied by the sliver bound's ambient hypotheses (the `K`-compact base
    region + the small-`τ₀` window), carried honestly.  ⚠ NOT `a₁ = R/6`. -/
theorem collar_to_regime {K : Set (Point n)} (r₀ c τ₀ τ : ℝ) (z : Point n)
    (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀) (hzK : z ∈ K) (hzr : ‖z‖ < r₀)
    (hzc : ‖z‖ ≤ c * Real.sqrt τ) :
    collarRegime (K := K) r₀ c τ₀ τ z :=
  ⟨hτ, hττ₀, hzK, hzr, hzc⟩

/-! ###############################################################################
    S2 (partial — the on-collar leg) — the pointwise sliver ingredients on the collar.
    ############################################################################### -/

/-- **★ S2 — `sliverExpand_on_collar`.**  The Leibniz–Gaussian 3-term identity for the CONCRETE
    second-`x`-derivative `witnessSecondXDeriv` of the `N = 1` van-Vleck gated witness, ON the √ε
    collar, taken from the corrected bundle via `collar_to_regime`.  This is the corrected
    `hD2Hexpand` field's conclusion at a collar point — the exact z-Gaussian shape with the
    (regime-restricted, K-absorbed) amplitudes `data.Aamp/A1amp/A2amp`.  Unlike the FALSE-off-flat
    global `hD2Hexpand` of `AmplitudeDerivativeData`, this holds honestly because `hV0` was eliminated
    by the unconditional Gaussian ratio (J4-352).  ⚠ NOT `a₁ = R/6`. -/
theorem sliverExpand_on_collar (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ : ℝ) (z : Point n) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀) (hzK : z ∈ K) (hzr : ‖z‖ < r₀)
    (hzc : ‖z‖ ≤ c * Real.sqrt τ) :
    witnessSecondXDeriv g gi hC hK S a b i τ z
      = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * data.Aamp τ z
        + z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z
        + gaussDdim τ z * data.A2amp τ z :=
  data.hD2Hexpand (collar_to_regime r₀ c τ₀ τ z hτ hττ₀ hzK hzr hzc)

/-- **★ S2 — `sliverAampBdd_on_collar`.**  The zeroth amplitude sup-bound `|data.Aamp τ z| ≤ data.M₀`
    on the collar (`data.M₀ = collarK·M₀chart`, the K-absorbed modulus).  From the corrected bundle
    via `collar_to_regime` (the ρ-ratio bounded by `collarK` on the collar, `rhoRatio_le_collarK`).
    ⚠ NOT `a₁ = R/6`. -/
theorem sliverAampBdd_on_collar (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ : ℝ) (z : Point n) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀) (hzK : z ∈ K) (hzr : ‖z‖ < r₀)
    (hzc : ‖z‖ ≤ c * Real.sqrt τ) :
    |data.Aamp τ z| ≤ data.M₀ :=
  data.hAampBdd (collar_to_regime r₀ c τ₀ τ z hτ hττ₀ hzK hzr hzc)

/-- **★ S2 — `sliverA1ampBdd_on_collar`.**  The first amplitude sup-bound on the collar
    (`data.M₁ = collarK·M₁chart`).  ⚠ NOT `a₁ = R/6`. -/
theorem sliverA1ampBdd_on_collar (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ : ℝ) (z : Point n) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀) (hzK : z ∈ K) (hzr : ‖z‖ < r₀)
    (hzc : ‖z‖ ≤ c * Real.sqrt τ) :
    |data.A1amp τ z| ≤ data.M₁ :=
  data.hA1ampBdd (collar_to_regime r₀ c τ₀ τ z hτ hττ₀ hzK hzr hzc)

/-- **★ S2 — `sliverA2ampBdd_on_collar`.**  The second amplitude sup-bound on the collar
    (`data.M₂ = collarK·M₂chart`).  ⚠ NOT `a₁ = R/6`. -/
theorem sliverA2ampBdd_on_collar (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ : ℝ) (z : Point n) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀) (hzK : z ∈ K) (hzr : ‖z‖ < r₀)
    (hzc : ‖z‖ ≤ c * Real.sqrt τ) :
    |data.A2amp τ z| ≤ data.M₂ :=
  data.hA2ampBdd (collar_to_regime r₀ c τ₀ τ z hτ hττ₀ hzK hzr hzc)

/-- **★ S2 — `sliverIntegrand_on_collar`.**  The pointwise SLIVER INTEGRAND identity on the collar:
    `witnessSecondXDeriv · F` equals the 3-term product `[hess·G·Aamp + grad·G·A1amp + G·A2amp]·F`.
    This is the EXACT per-point input `SliverEstimates.sliver2_bound` consumes to split the inner
    z-integral (its `hpt : ∀ z, D2H τ z · F s z 0 = …`), here supplied from the corrected collar
    bundle.  The multiplication by `F s z 0` is `congrArg (· * F s z 0)` on `sliverExpand_on_collar`.
    ⚠ NOT `a₁ = R/6`. -/
theorem sliverIntegrand_on_collar (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ : ℝ) (s : ℝ) (z : Point n) (hτ : 0 < τ) (hττ₀ : τ ≤ τ₀) (hzK : z ∈ K) (hzr : ‖z‖ < r₀)
    (hzc : ‖z‖ ≤ c * Real.sqrt τ) :
    witnessSecondXDeriv g gi hC hK S a b i τ z * F s z 0
      = ((z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * data.Aamp τ z
          + z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z
          + gaussDdim τ z * data.A2amp τ z) * F s z 0 := by
  rw [sliverExpand_on_collar g gi hC hK S a b F i T τ₀ r₀ c data τ z hτ hττ₀ hzK hzr hzc]

end QIQTH.SliverBoundOnCollar

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.SliverBoundOnCollar.collar_to_regime
#print axioms QIQTH.SliverBoundOnCollar.sliverExpand_on_collar
#print axioms QIQTH.SliverBoundOnCollar.sliverAampBdd_on_collar
#print axioms QIQTH.SliverBoundOnCollar.sliverA1ampBdd_on_collar
#print axioms QIQTH.SliverBoundOnCollar.sliverA2ampBdd_on_collar
#print axioms QIQTH.SliverBoundOnCollar.sliverIntegrand_on_collar
