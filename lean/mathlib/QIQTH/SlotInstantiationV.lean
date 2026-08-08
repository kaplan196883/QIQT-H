/-
  SlotInstantiationV — J4-422 (Part B, tranche (a) phase 5): (A) the `hf2bound`/`hf3bound`
  Gaussian-moment ABSOLUTE dominators discharged at the phase-1 witness, m-uniformly, via the banked
  absolute COORDINATE-moment family (Sol #19 route); and (B) the REGIME AUDIT of `hD2Hexpand`
  (Sol #19 route A) — the unconditional off-collar chart-native jet identity of `IchartResidual`, with
  the `hcomp` comparison-leg collapse.  Continues `SlotInstantiationI..IV`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  PART A — `hf2bound` / `hf3bound`.  The `leviSecondPairing_inner_bound_concrete` slots
      `hf2bound : |∫ z_i/(2τ)·G_τ·A1amp·F| ≤ Q/√τ`   (gradient, odd-moment √τ extraction),
      `hf3bound : |∫ G_τ·A2amp·F|         ≤ Sconst`   (mass, τ-uniform),
  are discharged at the CONCRETE (phase-1) ρ-scaled chart witness by the route
  `GpowClosure.abs_integral_le_of_dom` + the banked absolute COORDINATE-moment family
  (`coordAbsPow_gauss_integral` + `oneD_absMoment1`, and `gaussDdim_integral_eq_one` for the mass):
    • `hf2` uses the FIRST coordinate moment `∫_z |z_i|·G_τ = ∫_y G_τ(y)·|y|^1 ≤ (3/2)√τ`, so with the
      `1/(2τ)` prefactor the dominator `D := (M/(2τ))·|z_i|·G_τ` integrates to `(3M/4)/√τ` — the odd-moment
      √τ extraction, with `Q = 3M/4` (Sol trap (i): the `z_i` is kept as a COORDINATE moment, NOT the
      radial `‖z‖` moment, which would cost √m and break m-uniformity; Sol trap (ii): no odd-moment
      cancellation is attempted — after `|·|` the coordinate moment is nonzero).
    • `hf3` uses the ZEROTH moment (total Gaussian mass one), so `D := Sconst·G_τ` integrates to `Sconst`
      — τ-uniform, no √τ.
  The prefactor `M`/`Sconst` are the collar-restricted (τ-uniform, m-uniform) amplitude·Levi sup bounds;
  the pointwise dominations `hdom` are CARRIED (they encode gate-confinement — off-gate the gated witness
  vanishes) and are per-point SATISFIABLE where the amplitudes are bounded (`hf2_ptwise_dom_of_ampBound`).
  NO τ-window is needed for hf2/hf3 (the √τ is EXACT from the first moment; the τ-window trap (iii) is for
  the Part-B CUBIC comparison leg, not the first/zeroth moments here).

  PART B — THE REGIME AUDIT (Sol #19 route A).  See the `## THE REGIME AUDIT` block.  VERDICT = (1): the
  `Regime = collarRegime` hypothesis in the `hD2Hexpand` field is used ONLY to select/supply `0 < τ`,
  `z ∈ K`, and the chart jets — NOT to prove cutoff constancy, ρ-smallness, or Taylor-remainder
  vanishing — so the identity `hD2HexpandOn_concrete` (whose own hypotheses contain NO collar / `r₀` /
  `τ₀` bound) EXTENDS OFF-COLLAR.  The jackpot unconditional jet lemma
      `IchartResidual = hessGaussFactor · rhoRatio · qc`   (off collar),
  hence the comparison integrand `IchartResidual − hessGaussFactor·qc = hessGaussFactor·(rhoRatio−1)·qc`,
  is PROVED (`ichartResidual_offcollar_form` / `ichartResidual_sub_hess_form`), collapsing the phase-4
  `hcomp` legs (ii)–(iv) from THREE abstract carries about an unknown `IchartResidual` to ONE explicit
  cubic-form carry (`hcomp_collapsed`).

  NO `sorry`, no `:= True`, no new axioms; std-3.  ⚠ a₁ = R/6 remains CONDITIONAL on the whole
  convergence-trio + geometric-wiring stack.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import QIQTH.SlotInstantiationIV
import QIQTH.GaussianMomentEnvelope
import QIQTH.DeltaFamilyBoundary
import QIQTH.SliverBoundOnCollar

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.AmplitudeDataOnCollar QIQTH.AmpGeometryBundle QIQTH.HrepGermFactorization
open QIQTH.SliverTailMatched
open QIQTH.SlotInstantiationI QIQTH.SlotInstantiationII QIQTH.SlotInstantiationIII
open QIQTH.SlotInstantiationIV
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.SlotInstantiationV

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### PART A, §1 — the coordinate-moment dominators (fully proved, m-uniform).
    ############################################################################### -/

/-- **★ A (hf2 moment) — `hf2_dom_moment`.**  THE ODD-MOMENT √τ EXTRACTION.  The coordinate-first-moment
    dominator `D z := (M/(2τ))·(|z_i|·G_τ(z))` integrates to `(3M/4)/√τ`:
      `∫_z (M/(2τ))·|z_i|·G_τ = (M/(2τ))·(∫_y G_τ(y)·|y|^1) ≤ (M/(2τ))·(3/2)√τ = (3M/4)/√τ`.
    Route: `coordAbsPow_gauss_integral` (`∫_z |z_i|·G = ∫_y G·|y|^1`) + `oneD_absMoment1`
    (`≤ (3/2)√τ`) + the exact `(√τ/τ) = 1/√τ` conversion.  COORDINATE moment only (Sol trap (i)); the
    constant `Q = 3M/4` is m-uniform (no `εₘ`, no √m).  ⚠ NOT `a₁ = R/6`. -/
theorem hf2_dom_moment (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (M : ℝ) (hM : 0 ≤ M) :
    (∫ z : Point n, M / (2 * τ) * (|z i| * gaussDdim τ z)) ≤ (3 * M / 4) / Real.sqrt τ := by
  have hMom : (∫ z : Point n, |z i| * gaussDdim τ z) ≤ 3 / 2 * Real.sqrt τ := by
    have h1 := QIQTH.HeatResidualBound.coordAbsPow_gauss_integral (n := n) τ hτ i 1
    have h2 := QIQTH.HeatResidualBound.oneD_absMoment1 τ hτ
    simp only [pow_one] at h1 h2
    rw [h1]; exact h2
  rw [integral_const_mul]
  have hcoef : (0 : ℝ) ≤ M / (2 * τ) := by positivity
  refine (mul_le_mul_of_nonneg_left hMom hcoef).trans (le_of_eq ?_)
  have hs : Real.sqrt τ ≠ 0 := (Real.sqrt_pos.mpr hτ).ne'
  have hττ : (2 : ℝ) * τ = 2 * (Real.sqrt τ * Real.sqrt τ) := by rw [Real.mul_self_sqrt hτ.le]
  rw [hττ]
  field_simp
  ring

/-- **★ A (hf2 integrability) — `hf2_dom_integrable`.**  The coordinate-first-moment dominator
    `(M/(2τ))·(|z_i|·G_τ)` is integrable (via `coordAbsPow_gauss_integrable` at `k = 1`).
    ⚠ NOT `a₁ = R/6`. -/
theorem hf2_dom_integrable (τ : ℝ) (hτ : 0 < τ) (i : Fin n) (M : ℝ) :
    Integrable (fun z : Point n => M / (2 * τ) * (|z i| * gaussDdim τ z)) volume := by
  simpa using (QIQTH.HeatResidualBound.coordAbsPow_gauss_integrable τ hτ i 1).const_mul (M / (2 * τ))

/-- **★ A (hf3 moment) — `hf3_dom_moment`.**  THE τ-UNIFORM MASS BOUND.  The mass dominator
    `D z := Sconst·G_τ(z)` integrates to `Sconst` (total Gaussian mass one, `gaussDdim_integral_eq_one`):
      `∫_z Sconst·G_τ = Sconst·1 = Sconst`.  τ-uniform (no √τ).  ⚠ NOT `a₁ = R/6`. -/
theorem hf3_dom_moment (τ : ℝ) (hτ : 0 < τ) (Sconst : ℝ) :
    (∫ z : Point n, Sconst * gaussDdim τ z) ≤ Sconst := by
  have h : (∫ z : Point n, Sconst * gaussDdim τ z) = Sconst := by
    rw [integral_const_mul, QIQTH.HeatResidualBound.gaussDdim_integral_eq_one τ hτ, mul_one]
  exact le_of_eq h

/-- **★ A (hf3 integrability) — `hf3_dom_integrable`.**  The mass dominator `Sconst·G_τ` is integrable.
    ⚠ NOT `a₁ = R/6`. -/
theorem hf3_dom_integrable (τ : ℝ) (hτ : 0 < τ) (Sconst : ℝ) :
    Integrable (fun z : Point n => Sconst * gaussDdim τ z) volume :=
  (QIQTH.HeatResidualBound.gaussDdim_integrable τ hτ).const_mul Sconst

/-! ###############################################################################
    ### PART A, §2 — the per-point domination (satisfiability of the `hdom` carry).
    ############################################################################### -/

/-- **★ A (hf2 domination, per-point) — `hf2_ptwise_dom_of_ampBound`.**  Where the amplitude·Levi product
    is bounded, `|data.A1amp τ z · F s z 0| ≤ M`, the term-2 integrand is pointwise dominated by the
    coordinate-first-moment dominator:
      `‖z_i/(2τ)·G_τ·A1amp·F‖ ≤ (M/(2τ))·(|z_i|·G_τ)`.
    This exhibits the `hf2bound` `hdom` carry as SATISFIABLE (per point) from the collar amplitude sup;
    off-gate (where the gated witness vanishes) the LHS is `0`.  ⚠ NOT `a₁ = R/6`. -/
theorem hf2_ptwise_dom_of_ampBound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (M : ℝ) (z : Point n)
    (hamp : |data.A1amp τ z * F s z 0| ≤ M) :
    ‖z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0‖
      ≤ M / (2 * τ) * (|z i| * gaussDdim τ z) := by
  have hG : (0 : ℝ) ≤ gaussDdim τ z := QIQTH.ResidueBound.gaussDdim_nonneg τ z
  have h2τ : (0 : ℝ) < 2 * τ := by positivity
  have key : z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0
      = z i / (2 * τ) * gaussDdim τ z * (data.A1amp τ z * F s z 0) := by ring
  rw [Real.norm_eq_abs, key, abs_mul, abs_mul, abs_div, abs_of_nonneg hG, abs_of_pos h2τ]
  have hnn : (0 : ℝ) ≤ |z i| / (2 * τ) * gaussDdim τ z :=
    mul_nonneg (div_nonneg (abs_nonneg _) h2τ.le) hG
  calc |z i| / (2 * τ) * gaussDdim τ z * |data.A1amp τ z * F s z 0|
      ≤ |z i| / (2 * τ) * gaussDdim τ z * M := mul_le_mul_of_nonneg_left hamp hnn
    _ = M / (2 * τ) * (|z i| * gaussDdim τ z) := by ring

/-- **★ A (hf3 domination, per-point) — `hf3_ptwise_dom_of_ampBound`.**  Where `|data.A2amp τ z · F s z 0|
    ≤ Sconst`, the term-3 integrand is pointwise dominated by the mass dominator:
      `‖G_τ·A2amp·F‖ ≤ Sconst·G_τ`.  ⚠ NOT `a₁ = R/6`. -/
theorem hf3_ptwise_dom_of_ampBound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (Sconst : ℝ) (z : Point n)
    (hamp : |data.A2amp τ z * F s z 0| ≤ Sconst) :
    ‖gaussDdim τ z * data.A2amp τ z * F s z 0‖ ≤ Sconst * gaussDdim τ z := by
  have hG : (0 : ℝ) ≤ gaussDdim τ z := QIQTH.ResidueBound.gaussDdim_nonneg τ z
  have key : gaussDdim τ z * data.A2amp τ z * F s z 0
      = gaussDdim τ z * (data.A2amp τ z * F s z 0) := by ring
  rw [Real.norm_eq_abs, key, abs_mul, abs_of_nonneg hG]
  calc gaussDdim τ z * |data.A2amp τ z * F s z 0|
      ≤ gaussDdim τ z * Sconst := mul_le_mul_of_nonneg_left hamp hG
    _ = Sconst * gaussDdim τ z := by ring

/-! ###############################################################################
    ### PART A, §3 — the discharged `hf2bound` / `hf3bound` slots at the witness.
    ############################################################################### -/

/-- **★★ A (slot `hf2bound`, DISCHARGED) — `hf2bound_at_witness`.**  THE GRADIENT ABSOLUTE SLOT at the
    concrete witness, with the coordinate-first-moment dominator supplied and its moment/integrability
    FULLY discharged (`hf2_dom_moment` / `hf2_dom_integrable`), the two remaining inputs being the
    integrand integrability `hfint` and the pointwise domination `hdom` (the geometric carry, per-point
    satisfiable via `hf2_ptwise_dom_of_ampBound`).  Conclusion in the EXACT `hf2bound` shape of
    `GpowClosure.leviSecondPairing_inner_bound_concrete` with `Q = 3M/4` — m-uniform.  Route:
    `GpowClosure.abs_integral_le_of_dom`.  ⚠ NOT `a₁ = R/6`. -/
theorem hf2bound_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (M : ℝ) (hM : 0 ≤ M)
    (hfint : Integrable
      (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0) volume)
    (hdom : ∀ᵐ z,
      ‖z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0‖
        ≤ M / (2 * τ) * (|z i| * gaussDdim τ z)) :
    |∫ z, z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0| ≤ (3 * M / 4) / Real.sqrt τ :=
  QIQTH.GpowClosure.abs_integral_le_of_dom
    (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0)
    (fun z => M / (2 * τ) * (|z i| * gaussDdim τ z)) ((3 * M / 4) / Real.sqrt τ)
    hfint (hf2_dom_integrable τ hτ i M) hdom (hf2_dom_moment τ hτ i M hM)

/-- **★★ A (slot `hf3bound`, DISCHARGED) — `hf3bound_at_witness`.**  THE MASS ABSOLUTE SLOT at the
    concrete witness, with the mass dominator supplied and its moment/integrability FULLY discharged
    (`hf3_dom_moment` / `hf3_dom_integrable`), leaving `hfint` and the pointwise domination `hdom`
    (satisfiable via `hf3_ptwise_dom_of_ampBound`).  Conclusion in the EXACT `hf3bound` shape with
    `Sconst` — τ-uniform.  Route: `GpowClosure.abs_integral_le_of_dom`.  ⚠ NOT `a₁ = R/6`. -/
theorem hf3bound_at_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (Sconst : ℝ)
    (hfint : Integrable (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0) volume)
    (hdom : ∀ᵐ z,
      ‖gaussDdim τ z * data.A2amp τ z * F s z 0‖ ≤ Sconst * gaussDdim τ z) :
    |∫ z, gaussDdim τ z * data.A2amp τ z * F s z 0| ≤ Sconst :=
  QIQTH.GpowClosure.abs_integral_le_of_dom
    (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0)
    (fun z => Sconst * gaussDdim τ z) Sconst
    hfint (hf3_dom_integrable τ hτ Sconst) hdom (hf3_dom_moment τ hτ Sconst)

/-! ###############################################################################
    ## THE REGIME AUDIT (Sol #19 route A)
    ###############################################################################

  QUESTION.  In the `hD2Hexpand` field of `AmplitudeDataOnCollar.AmplitudeDerivativeDataOn`
  (`Regime : ℝ → Point n → Prop`, instantiated at `Regime = collarRegime (K := K) r₀ c τ₀`), WHERE is the
  `Regime` hypothesis actually consumed, and does the underlying 3-term identity DEPEND on the collar?

  EVIDENCE — the exact `Regime` usage points (file:line).
    • `AmplitudeDataOnCollar.lean:328-332` — the field `hD2Hexpand : ∀ {τ z}, Regime τ z → (3-term id)`
      is the ONLY field carrying the identity.  Its conclusion (the exact z-Gaussian 3-term shape) is
      independent of the collar; the `Regime` premise is the sole gate.
    • `AmplitudeDataOnCollar.lean:426-430` — the CONCRETE discharge (`amplitudeDataOn_concrete.hD2Hexpand`):
          intro τ z hreg
          obtain ⟨hSopen, h0, P, Q, hV1, hP1, hA1, hA2, hVP, hPsq, hVQ⟩ := hjets τ z hreg
          exact hD2HexpandOn_concrete … τ hreg.1 z hreg.2.2.1 hSopen h0 P Q …
      The `Regime = collarRegime` term `hreg` is used at EXACTLY three sites:
        (u1) `hreg.1`      ⟶ supplies `0 < τ`   (collarRegime's 1st conjunct);
        (u2) `hreg.2.2.1`  ⟶ supplies `z ∈ K`   (collarRegime's 3rd conjunct);
        (u3) `hjets τ z hreg` ⟶ supplies the open gate `IsOpen (S z) ∧ 0 ∈ S z` and the chart jets
             `P,Q,hV1,hP1,hA1,hA2,hVP,hPsq,hVQ`.
      The collar radius conjunct `‖z‖ ≤ c√τ` (`hreg.2.2.2.2`), the `r₀` conjunct `‖z‖ < r₀`
      (`hreg.2.2.2.1`), and the window conjunct `τ ≤ τ₀` (`hreg.2.1`) are NEVER referenced.
    • `AmplitudeDataOnCollar.lean:258-287` — the underlying identity `hD2HexpandOn_concrete` ITSELF takes
      hypotheses `hτ : 0 < τ`, `hz : z ∈ K`, `hSopen`, `h0`, and the chart jets — and NO `‖z‖ ≤ c√τ`, NO
      `‖z‖ < r₀`, NO `τ ≤ τ₀`.  So the identity is ALREADY unconditional off the collar.

  VERDICT = CASE (1): THE IDENTITY EXTENDS OFF-COLLAR.  The `Regime` hypothesis is used only to (u1)/(u2)
  select `0 < τ` and `z ∈ K` and (u3) supply the open gate + chart jets — i.e. to select/unfold the
  witness branch and provide rewrites already true on the chart.  It does NOT prove cutoff constancy,
  domain membership beyond `z ∈ K`, ρ-smallness, or Taylor-remainder vanishing.  The collar/`r₀`/`τ₀`
  bounds are used ONLY for the AMPLITUDE SUP-bounds (`hAampBdd`/… via `rhoRatio_le_collarK`), NOT for the
  identity.  Therefore the unconditional jet lemma is IN REACH — proved below as
  `ichartResidual_offcollar_form`, with the `hcomp` collapse wired in `hcomp_collapsed`.

  Sol's trap respected: the off-collar extension keeps the ρ-scaled `chartArg` normalisation (the ρ-ratio
  `rhoRatio` = `G^chart/G` is carried EXACTLY, not dropped), the Gaussian normalisation (`gaussDdim τ z`),
  and the `τ > 0` hypothesis aligned; the identity is an EQUALITY (not an on-collar bound transported
  off-collar).  The only genuinely-off-collar INPUT is the SUPPLY of the chart jets + open gate off the
  collar (a chart-jet fact at base `z`, honest wherever `z ∈ K` with an open gate) — carried as the jet
  hypotheses of the lemmas below, NOT smuggled in. -/

/-! ###############################################################################
    ### PART B, §1 — ★ the unconditional off-collar chart-native jet identity (JACKPOT).
    ############################################################################### -/

/-- **★★★ B (JACKPOT) — `ichartResidual_offcollar_form`.**  THE UNCONDITIONAL OFF-COLLAR CHART-NATIVE
    FORM of the phase-2 residual.  Under the ORDINARY chart hypotheses (`0 < τ`, `z ∈ K`, the open gate,
    the chart jets) — with NO collar `‖z‖ ≤ c√τ`, NO `r₀`, NO `τ₀` bound — the residual
    `IchartResidual = Wpair − f₂ − f₃` has the CHART-NATIVE leading form
        `IchartResidual z = hessGaussFactor i τ z · (rhoRatio τ z · (chartAmp τ z 0 · F s z 0))`,
    i.e. `= H^chart·qc` with `H^chart = (z_i²−2τ)/(4τ²)·G^chart` and `G^chart = ρ·G_τ` the chart-image
    Gaussian, `qc = chartAmp·F`.  This is the OFF-COLLAR identity the phase-4 obstruction note anticipated
    (`SlotInstantiationIV.lean:282-296`) — now an EXACT equality.  Route: the unconditional identity
    `AmplitudeDataOnCollar.hD2HexpandOn_concrete` (the witness expansion), the amplitude-shape carries
    `hA1eq`/`hA2eq` (`rfl` for the concrete bundle), then `ring` — the `f₂`/`f₃` terms cancel exactly.
    ⚠ NOT `a₁ = R/6`. -/
theorem ichartResidual_offcollar_form (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (z : Point n)
    (hz : z ∈ K) (hSopen : IsOpen (S z)) (h0 : (0 : Point n) ∈ S z)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hV1 : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
    (hA2 : PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    (hVP : ∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i)
    (hPsq : ∑ k, P 0 k ^ 2 = 1)
    (hVQ : ∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0)
    (hA1eq : data.A1amp τ z
      = rhoRatio g gi hC hK τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0))
    (hA2eq : data.A2amp τ z
      = rhoRatio g gi hC hK τ z * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0) :
    IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
      = hessGaussFactor i τ z
          * (rhoRatio g gi hC hK τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)) := by
  unfold IchartResidual
  rw [hD2HexpandOn_concrete g gi hC hK S a b i τ hτ z hz hSopen h0
        P Q hV1 hP1 hA1 hA2 hVP hPsq hVQ, hA1eq, hA2eq]
  simp only [hessGaussFactor]
  ring

/-- **★★★ B (comparison integrand, JACKPOT corollary) — `ichartResidual_sub_hess_form`.**  THE
    COMPARISON-LEG INTEGRAND, off collar, in EXACT explicit form:
        `IchartResidual z − hessGaussFactor i τ z · qc z
            = hessGaussFactor i τ z · ((rhoRatio τ z − 1) · qc z)`,   `qc = chartAmp·F`.
    So the `hcomp` comparison integrand is `H·(ρ−1)·qc` — the ρ-deviation-weighted Hessian-Gaussian, the
    exact CUBIC-order object the banked cubic machinery (`cubic_gaussian_moment_witness` /
    `gaussDdim_replace_bound`, `(ρ−1) = O(‖z‖³/τ)`) dominates.  This COLLAPSES the phase-4 `hcomp` legs
    (ii)–(iv) from three abstract carries about an unknown `IchartResidual` to ONE explicit cubic-form
    carry.  Route: `ichartResidual_offcollar_form` + `ring`.  ⚠ NOT `a₁ = R/6`. -/
theorem ichartResidual_sub_hess_form (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (z : Point n)
    (hz : z ∈ K) (hSopen : IsOpen (S z)) (h0 : (0 : Point n) ∈ S z)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hV1 : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
    (hA2 : PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    (hVP : ∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i)
    (hPsq : ∑ k, P 0 k ^ 2 = 1)
    (hVQ : ∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0)
    (hA1eq : data.A1amp τ z
      = rhoRatio g gi hC hK τ z * (-2 * pd (chartAmp g gi hC hK a b τ z) i 0))
    (hA2eq : data.A2amp τ z
      = rhoRatio g gi hC hK τ z * pd (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i 0) :
    IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
      = hessGaussFactor i τ z
          * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)) := by
  rw [ichartResidual_offcollar_form g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ z
        hz hSopen h0 P Q hV1 hP1 hA1 hA2 hVP hPsq hVQ hA1eq hA2eq]
  ring

/-! ###############################################################################
    ### PART B, §2 — the `hcomp` comparison-leg collapse to a single cubic-form carry.
    ############################################################################### -/

/-- **★★★ B (hcomp collapse) — `hcomp_collapsed`.**  THE COMPARISON-LEG BOUND with legs (ii)–(iv)
    COLLAPSED.  Given the off-collar pointwise identity `hform` (the residual comparison integrand equals
    the explicit `H·(ρ−1)·qc` on `(collar (c√τ))ᶜ`, discharged by `ichartResidual_sub_hess_form` wherever
    the chart jets hold — the honest off-collar jet-supply carry) and a SINGLE dominator `D` on that
    explicit form (`hDint`/`hdom`/`hmom`), the exact `hcomp` shape of
    `GpowClosure.leviSecondPairing_inner_bound_concrete` follows:
        `‖∫_{(collar (c√τ))ᶜ} (IchartResidual − hessGaussFactor·qc)‖ ≤ Bcomp/√τ`.
    Route: `setIntegral_congr_fun` (swap the integrand to `H·(ρ−1)·qc`) then
    `norm_integral_le_integral_norm` → `integral_mono_ae` → `hmom`.  The three phase-4 abstract carries
    are now ONE cubic-form carry.  ⚠ NOT `a₁ = R/6`. -/
theorem hcomp_collapsed (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (D : Point n → ℝ) (Bcomp : ℝ)
    (hcompDiff_int : IntegrableOn
      (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      (collar (c * Real.sqrt τ))ᶜ volume)
    (hDint : IntegrableOn D (collar (c * Real.sqrt τ))ᶜ volume)
    (hform : ∀ z ∈ (collar (c * Real.sqrt τ))ᶜ,
      IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0)
        = hessGaussFactor i τ z
            * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))
    (hdom : ∀ᵐ z ∂(volume.restrict (collar (c * Real.sqrt τ))ᶜ),
      ‖hessGaussFactor i τ z
          * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖ ≤ D z)
    (hmom : (∫ z in (collar (c * Real.sqrt τ))ᶜ, D z) ≤ Bcomp / Real.sqrt τ) :
    ‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
        (IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
          - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
      ≤ Bcomp / Real.sqrt τ := by
  have hMeas : MeasurableSet ((collar (c * Real.sqrt τ))ᶜ : Set (Point n)) :=
    (QIQTH.SliverTailMatched.collar_measurableSet _).compl
  have hae : (fun z => IchartResidual g gi hC hK S a b F i T τ₀ r₀ c data τ s z
        - hessGaussFactor i τ z * (chartAmp g gi hC hK a b τ z 0 * F s z 0))
      =ᵐ[volume.restrict (collar (c * Real.sqrt τ))ᶜ]
      (fun z => hessGaussFactor i τ z
        * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0))) :=
    (ae_restrict_iff' hMeas).mpr (ae_of_all _ (fun z hz => hform z hz))
  have hRHSint : IntegrableOn
      (fun z => hessGaussFactor i τ z
        * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0)))
      (collar (c * Real.sqrt τ))ᶜ volume := hcompDiff_int.congr hae
  rw [setIntegral_congr_fun hMeas hform]
  calc ‖∫ z in (collar (c * Real.sqrt τ))ᶜ,
          hessGaussFactor i τ z
            * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖
      ≤ ∫ z in (collar (c * Real.sqrt τ))ᶜ,
          ‖hessGaussFactor i τ z
            * ((rhoRatio g gi hC hK τ z - 1) * (chartAmp g gi hC hK a b τ z 0 * F s z 0))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z in (collar (c * Real.sqrt τ))ᶜ, D z := integral_mono_ae hRHSint.norm hDint hdom
    _ ≤ Bcomp / Real.sqrt τ := hmom

/-! ###############################################################################
    ### PACKAGE — the phase-5 conjunction (phase 4 ∧ the discharged `hf2bound`/`hf3bound`).
    ############################################################################### -/

/-- **★★★ `slotInstantiation_phase5`.**  THE PHASE-5 PACKAGE: the phase-4 group-(1) carries (supplied by
    `SlotInstantiationIV.slotInstantiation_phase4`, held here as `Pphase4`) CONJOINED with the two new
    discharged fields
      • `hf2bound` (`hf2bound_at_witness`, `Q = 3M/4`, m-uniform gradient absolute), AND
      • `hf3bound` (`hf3bound_at_witness`, `Sconst`, τ-uniform mass absolute),
    both in the EXACT shape consumed by `GpowClosure.leviSecondPairing_inner_bound_concrete`.  With this,
    the ONLY remaining group-(1) residue is the `hcomp` comparison-leg carry — now COLLAPSED by Part B to
    the single explicit `H·(ρ−1)·qc` cubic-form dominator (`hcomp_collapsed`) — plus the standing
    integrand-integrability + pointwise-domination carries (per-point satisfiable).  ⚠ NOT `a₁ = R/6`. -/
theorem slotInstantiation_phase5 (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (i : Fin n) (T τ₀ r₀ c : ℝ)
    (data : AmplitudeDerivativeDataOn g gi hC hK S a b F i T τ₀ (collarRegime (K := K) r₀ c τ₀))
    (τ s : ℝ) (hτ : 0 < τ) (M Sconst : ℝ) (hM : 0 ≤ M)
    (Pphase4 : Prop) (hphase4 : Pphase4)
    (hf2int : Integrable
      (fun z => z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0) volume)
    (hf2dom : ∀ᵐ z,
      ‖z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0‖
        ≤ M / (2 * τ) * (|z i| * gaussDdim τ z))
    (hf3int : Integrable (fun z => gaussDdim τ z * data.A2amp τ z * F s z 0) volume)
    (hf3dom : ∀ᵐ z,
      ‖gaussDdim τ z * data.A2amp τ z * F s z 0‖ ≤ Sconst * gaussDdim τ z) :
    Pphase4
    ∧ (|∫ z, z i / (2 * τ) * gaussDdim τ z * data.A1amp τ z * F s z 0| ≤ (3 * M / 4) / Real.sqrt τ)
    ∧ (|∫ z, gaussDdim τ z * data.A2amp τ z * F s z 0| ≤ Sconst) :=
  ⟨hphase4,
   hf2bound_at_witness g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ M hM hf2int hf2dom,
   hf3bound_at_witness g gi hC hK S a b F i T τ₀ r₀ c data τ s hτ Sconst hf3int hf3dom⟩

end QIQTH.SlotInstantiationV

/-! ## Axiom checks — every public declaration is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.SlotInstantiationV
#print axioms hf2_dom_moment
#print axioms hf2_dom_integrable
#print axioms hf3_dom_moment
#print axioms hf3_dom_integrable
#print axioms hf2_ptwise_dom_of_ampBound
#print axioms hf3_ptwise_dom_of_ampBound
#print axioms hf2bound_at_witness
#print axioms hf3bound_at_witness
#print axioms ichartResidual_offcollar_form
#print axioms ichartResidual_sub_hess_form
#print axioms hcomp_collapsed
#print axioms slotInstantiation_phase5
end AxiomChecks

/-! ###############################################################################
    ## PHASE 5 COVERAGE  (J4-422, Part B, tranche (a))
    ###############################################################################

  PART A — `hf2bound` / `hf3bound` (group-(1) Gaussian-moment ABSOLUTE dominators):
    • `hf2bound` — DISCHARGED (`hf2bound_at_witness`) at the concrete witness, in the exact
      `|∫ z_i/(2τ)·G_τ·A1amp·F| ≤ Q/√τ` shape with `Q = 3M/4`, `M`-UNIFORM.  The √τ is the ODD-MOMENT
      extraction from the FIRST COORDINATE moment `∫_z |z_i|·G_τ = ∫_y G_τ|y|^1 ≤ (3/2)√τ`
      (`hf2_dom_moment`, fully proved; Sol trap (i) — coordinate `|z_i|`, NOT radial `‖z‖`, so no √m;
      Sol trap (ii) — no odd-moment cancellation).  NO τ-window needed (the √τ is EXACT).  The dominator
      integrability is fully proved (`hf2_dom_integrable`); the two standing carries are the integrand
      integrability `hfint` and the pointwise domination `hdom` (per-point satisfiable via
      `hf2_ptwise_dom_of_ampBound` from the collar amplitude sup `M`).
    • `hf3bound` — DISCHARGED (`hf3bound_at_witness`), exact `|∫ G_τ·A2amp·F| ≤ Sconst` shape, τ-UNIFORM,
      from the ZEROTH moment (total Gaussian mass one, `hf3_dom_moment`); same two standing carries
      (`hf3_ptwise_dom_of_ampBound`).
    OUTCOME: hf2bound/hf3bound REDUCED-WITH-NAMED-CARRIES — the moment/integrability arithmetic is FULLY
    PROVED and m-uniform (coordinate moments only); the residual is the (per-point satisfiable) domination
    + integrand-integrability, i.e. the amplitude·Levi sup + gate-confinement geometric carry.

  PART B — THE REGIME AUDIT.  VERDICT = (1) EXTENDS OFF-COLLAR (evidence: the `## THE REGIME AUDIT` block;
  usage points `AmplitudeDataOnCollar.lean:328-332`, `:426-430` (u1 `hreg.1`, u2 `hreg.2.2.1`,
  u3 `hjets τ z hreg`), and `:258-287` (the identity's own hypotheses carry NO collar/`r₀`/`τ₀`)).
    • JET LEMMA PROVED: `ichartResidual_offcollar_form` — `IchartResidual = hessGaussFactor·ρ·qc` off
      collar (= `H^chart·qc`), and its corollary `ichartResidual_sub_hess_form` —
      `IchartResidual − hessGaussFactor·qc = hessGaussFactor·(ρ−1)·qc`.
    • HCOMP COLLAPSE WIRED: `hcomp_collapsed` — the phase-4 `hcomp` legs (ii)–(iv) collapse from three
      abstract carries about an unknown `IchartResidual` to ONE explicit `H·(ρ−1)·qc` cubic-form carry
      (`(ρ−1) = O(‖z‖³/τ)` × the banked cubic moment) + the off-collar jet-supply carry `hform`
      (discharged pointwise by `ichartResidual_sub_hess_form` wherever the chart jets hold).

  UPDATED GROUP-(1) RESIDUE (honest; J4-423+):
    • the standing per-point integrand-integrability + pointwise-domination carries of hf2/hf3
      (`hfint`/`hdom`; the amplitude·Levi sup + gate-confinement — a Gaussian-tail/gate estimate, NOT a
      new identity), AND
    • the `hcomp` cubic-form carry now isolated by `hcomp_collapsed` (the `(ρ−1) = O(‖z‖³/τ)` ρ-deviation
      bound + `cubic_gaussian_moment_witness`) AND its off-collar jet-supply `hform`
      (`ichartResidual_sub_hess_form` needs the chart jets + open gate off the collar — a chart-jet fact
      at base `z`, honest wherever `z ∈ K`).
  These are the terminal geometric-wiring carries; the SLOT-INSTANTIATION algebra of group (1) is now
  complete (phases 1–5).  ⚠ a₁ = R/6 remains CONDITIONAL on the whole convergence-trio + geometric-wiring
  stack.
-/
