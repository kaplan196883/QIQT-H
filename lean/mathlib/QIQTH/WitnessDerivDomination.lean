/-
  WitnessDerivDomination — J4-161: the L1 G2-bundle discharge for the CONCRETE first-derivative
  kernel `dH := witnessFieldDeriv` of the gated `N = 1` van-Vleck witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It discharges, for
  the concrete `dH := witnessFieldDeriv`, part of the per-`(i, x₀)` domination/continuity bundle
  that `QIQTH.GcoefContinuity.gcoef_continuity_discharge` (J4-160) consumes — the `hzcont`, `hzint`,
  and the near-regime core of the `hzbound` slots — with the honest analytic inputs carried, never
  the conclusion.

  ── WHAT IS PROVED HERE (axiom-free, no `sorry`).

    STEP 1 — the x-CONTINUITY family (`hzcont`, DISCHARGED).
      • `pd_continuousAt_of_contDiffAt` — ★ THE GENERAL LEVER (reusable).  For any `f` with
          `ContDiffAt ℝ 2 f x₀`, the coordinate partial `x ↦ pd f i x` is `ContinuousAt` at `x₀`
          (near `x₀`, `pd f i = (fderiv f ·)(eᵢ)` by `pd_eq_fderiv`, and `fderiv f` is `C¹`).
          Mirrors `AmplitudeFamilyDischarge.amp_pd_continuousAt_of_contDiffAt`, but generic.
      • `witnessFieldDeriv_continuousAt` — the concrete kernel `x ↦ witnessFieldDeriv i τ x z` is
          `ContinuousAt` at `x₀`, from the FIELD-SLOT `C²` regularity of the gated witness at `x₀`
          (`witnessFieldDeriv i τ x z = pd (fun x' ↦ H_G τ x' z) i x` by definition).
      • `witnessFieldDeriv_mul_const_continuousAt` — the `F s z` glue (constant in `x`).
      • `hzcont_witness` — ★★ the EXACT `hzcont` shape, from the field-slot-`C²` family carry.

    STEP 2 — the near-regime x-FREE Gaussian dominator (near-regime core of `hzbound`).
      • `witnessFieldDeriv_gate_envelope` — ★ the pointwise x-free bound.  Combining E2
          (`witnessFieldDeriv_gate_abs_le` — the on-gate `G_τ(W z p)·(Bs·Ba + Bd)` bound) with the
          carried chart-Gaussian near/far envelope
          `hgauss_env : G_τ(W z p) ≤ C₁·G_σ(z)` (x-FREE RHS; the coercivity/half-coercivity output
          of `InverseChartDisplacement` / `GaussianMomentEnvelope.gaussDdim_replace_bound`-style
          near-isometry), yields `|witnessFieldDeriv i τ p z| ≤ ((Bs·Ba+Bd)·C₁)·G_σ(z)`, with the
          constant and the Gaussian argument BOTH x-free.
      • `hzbound_witness` — the exact `hzbound` shape, assembling the F-weighting on top of the
          carried x-free bare-kernel envelope `henv` plus a scalar sup-bound `|F| ≤ Cf`.

    STEP 3 — the x-FREE envelope integrability (`hzint`, DISCHARGED).
      • `envelope_integrable` — `z ↦ C₀·G_σ(z)` is integrable (`gaussDdim_integrable`).
      • `hzint_witness` — ★★ the EXACT `hzint` shape at width `σ = κ·(t−s)` on `Ι 0 t` (positive a.e.,
          the endpoint `s = t` being null).

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, never the conclusion).
    • STEP 1 carry `hC2fam` — the field-slot `ContDiffAt ℝ 2` family of the gated witness.  This is a
      genuine REGULARITY input (strictly stronger than, and different from, the continuity conclusion);
      satisfiable on the gate exactly as `SpatialC2.hCH_discharge` proves it at the field centre.
    • STEP 2 carry `hgauss_env` — the x-free chart-Gaussian envelope (a pure geometry fact about the
      chart + Gaussian, NOT the derivative kernel); satisfiable from the near-isometry coercivity
      `½·r²_z ≤ r²_{Wz}` (`InverseChartDisplacement`) via Gaussian monotonicity.  The E2 factor
      bounds `Bs`/`Ba`/`Bd` and the gate data `hz`/`hp`/`hJetV`/`hAmp1` are the E1/E2 on-gate carries.
    • STEP 2 carry `henv` — the bare-kernel x-free domination on a nbhd (no `F` factor); GROUNDED in
      `witnessFieldDeriv_gate_envelope` above, NOT the (F-weighted) conclusion.
    • Still OPEN / carried elsewhere: `hzmeas`, `hsmeas`, `hsbound`, `hBint` — the measurability
      halves and the outer s-layer; not addressed here.

  NO `sorry`.  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.EngineInstantiation
import QIQTH.DeltaFamilyBoundary

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.WitnessDerivDomination

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### STEP 1 — the x-continuity family (the `hzcont` slot).
    ############################################################################### -/

/-- **★ STEP 1 — `pd_continuousAt_of_contDiffAt`.**  THE GENERAL LEVER.  For `f : Point n → ℝ` that is
    `ContDiffAt ℝ 2` at `x₀`, the coordinate partial `x ↦ pd f i x` is `ContinuousAt` at `x₀`.  Near
    `x₀` the function is differentiable, so `pd f i = (fderiv f ·)(eᵢ)` (`pd_eq_fderiv`), and `fderiv f`
    is `C¹` (`ContDiffAt.fderiv_right`), hence continuous.  The generic form of
    `AmplitudeFamilyDischarge.amp_pd_continuousAt_of_contDiffAt`.  NOT `a₁ = R/6`. -/
theorem pd_continuousAt_of_contDiffAt (f : Point n → ℝ) (i : Fin n) (x₀ : Point n)
    (hC2 : ContDiffAt ℝ 2 f x₀) :
    ContinuousAt (fun x => pd f i x) x₀ := by
  have hdiff : ∀ᶠ y in 𝓝 x₀, DifferentiableAt ℝ f y := by
    filter_upwards [hC2.eventually (by norm_num)] with y hy using hy.differentiableAt (by norm_num)
  have heq : (fun y => pd f i y) =ᶠ[𝓝 x₀]
      (fun y => (fderiv ℝ f y) (Pi.single i 1)) := by
    filter_upwards [hdiff] with y hy using pd_eq_fderiv f i y hy
  have hfd : ContDiffAt ℝ 1 (fun y => fderiv ℝ f y) x₀ := hC2.fderiv_right (m := 1) (by norm_num)
  have hcontF : ContinuousAt (fun y => (fderiv ℝ f y) (Pi.single i 1)) x₀ :=
    hfd.continuousAt.clm_apply continuousAt_const
  exact hcontF.congr heq.symm

/-- **STEP 1 — `witnessFieldDeriv_continuousAt`.**  The concrete first-derivative kernel
    `x ↦ witnessFieldDeriv i τ x z` is `ContinuousAt` at `x₀`, from the FIELD-SLOT `ContDiffAt ℝ 2`
    regularity of the gated witness at `x₀`.  Since
    `witnessFieldDeriv i τ x z = pd (fun x' ↦ vanVleckGatedWitness … τ x' z) i x` by definition, this is
    `pd_continuousAt_of_contDiffAt` at the witness field slice.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_continuousAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z x₀ : Point n)
    (hC2 : ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) x₀) :
    ContinuousAt (fun x => witnessFieldDeriv g gi hC hK S a b i τ x z) x₀ := by
  show ContinuousAt
    (fun x => pd (fun x' => vanVleckGatedWitness g gi hC hK S a b τ x' z) i x) x₀
  exact pd_continuousAt_of_contDiffAt _ i x₀ hC2

/-- **STEP 1 — `witnessFieldDeriv_mul_const_continuousAt`.**  The `F s z` glue: multiplying the
    (x-continuous) kernel by a constant `c` (the `F s z` factor, constant in the field variable `x`)
    preserves `ContinuousAt`.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_mul_const_continuousAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z x₀ : Point n) (c : ℝ)
    (hcont : ContinuousAt (fun x => witnessFieldDeriv g gi hC hK S a b i τ x z) x₀) :
    ContinuousAt (fun x => witnessFieldDeriv g gi hC hK S a b i τ x z * c) x₀ :=
  hcont.mul continuousAt_const

/-- **★★ STEP 1 — `hzcont_witness`.**  THE EXACT `hzcont` SLOT of
    `GcoefContinuity.gcoef_continuity_discharge`, for the concrete `dH := witnessFieldDeriv` and the
    F-family `F : ℝ → Point n → ℝ`:
      `∀ x₀ ∈ u, ∀ i, ∀ᵐ s, s ∈ Ι 0 t → ∀ᵐ z, ContinuousAt (fun x ↦ witnessFieldDeriv i (t−s) x z · F s z) x₀`,
    produced from the carried FIELD-SLOT `C²` regularity family `hC2fam` (a genuine regularity input,
    satisfiable on the gate exactly as `SpatialC2.hCH_discharge`; NEVER the conclusion).  NOT `a₁ = R/6`. -/
theorem hzcont_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (F : ℝ → Point n → ℝ) (ν : Measure (Point n)) (u : Set (Point n))
    (hC2fam : ∀ x₀ ∈ u, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂ν,
        ContDiffAt ℝ 2 (fun x' => vanVleckGatedWitness g gi hC hK S a b (t - s) x' z) x₀) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ᵐ z ∂ν,
      ContinuousAt
        (fun x => witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z) x₀ := by
  intro x₀ hx₀ i
  filter_upwards [hC2fam x₀ hx₀] with s hs hmem
  filter_upwards [hs hmem] with z hzc
  exact witnessFieldDeriv_mul_const_continuousAt g gi hC hK S a b i (t - s) z x₀ (F s z)
    (witnessFieldDeriv_continuousAt g gi hC hK S a b i (t - s) z x₀ hzc)

/-! ###############################################################################
    ### STEP 2 — the near-regime x-free Gaussian dominator (near-regime core of `hzbound`).
    ############################################################################### -/

/-- **★ STEP 2 — `witnessFieldDeriv_gate_envelope`.**  THE NEAR-REGIME x-FREE POINTWISE BOUND.  From
    E2 (`witnessFieldDeriv_gate_abs_le`, the on-gate `G_τ(W z p)·(Bs·Ba + Bd)` domination) and the
    carried chart-Gaussian envelope `hgauss_env : G_τ(W z p) ≤ C₁·G_σ(z)` (x-FREE RHS — the near/far
    coercivity output; a pure geometry fact about the chart + Gaussian, NOT the derivative kernel),
      `|witnessFieldDeriv i τ p z| ≤ ((Bs·Ba + Bd)·C₁)·G_σ(z)`,
    with the constant `(Bs·Ba + Bd)·C₁` and the Gaussian argument `z` BOTH x-free.  Pure multiplicative
    reduction on E2.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_gate_envelope (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (hτ : 0 < τ)
    (z : Point n) (hz : z ∈ K) (hSopen : IsOpen (S z)) (p : Point n) (hp : p ∈ S z)
    (Pval : Fin n → ℝ)
    (hJetV : ∀ k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update p i s) k) (Pval k) (p i))
    (hAmp1 : PdiffAt (chartFieldAmp g gi hC hK a b τ z) i p)
    (Bs Ba Bd : ℝ)
    (hSc : |(-(∑ k, uniformInverseChart g gi hC hK z p k * Pval k) / (2 * τ))| ≤ Bs)
    (hBa : |chartFieldAmp g gi hC hK a b τ z p| ≤ Ba)
    (hBd : |pd (chartFieldAmp g gi hC hK a b τ z) i p| ≤ Bd)
    (σ C₁ : ℝ)
    (hgauss_env : gaussDdim τ (uniformInverseChart g gi hC hK z p) ≤ C₁ * gaussDdim σ z) :
    |witnessFieldDeriv g gi hC hK S a b i τ p z|
      ≤ ((Bs * Ba + Bd) * C₁) * gaussDdim σ z := by
  have hE2 := witnessFieldDeriv_gate_abs_le g gi hC hK S a b i τ hτ z hz hSopen p hp Pval hJetV
    hAmp1 Bs Ba Bd hSc hBa hBd
  have hBs : 0 ≤ Bs := le_trans (abs_nonneg _) hSc
  have hBa' : 0 ≤ Ba := le_trans (abs_nonneg _) hBa
  have hBd' : 0 ≤ Bd := le_trans (abs_nonneg _) hBd
  have hcoef_nn : 0 ≤ Bs * Ba + Bd := add_nonneg (mul_nonneg hBs hBa') hBd'
  calc |witnessFieldDeriv g gi hC hK S a b i τ p z|
      ≤ gaussDdim τ (uniformInverseChart g gi hC hK z p) * (Bs * Ba + Bd) := hE2
    _ ≤ (C₁ * gaussDdim σ z) * (Bs * Ba + Bd) :=
        mul_le_mul_of_nonneg_right hgauss_env hcoef_nn
    _ = ((Bs * Ba + Bd) * C₁) * gaussDdim σ z := by ring

/-- **STEP 2 — `hzbound_witness`.**  THE EXACT `hzbound` SHAPE, for the concrete `dH := witnessFieldDeriv`
    and F-family `F : ℝ → Point n → ℝ`, with the x-FREE dominator `boundz s z = (C₀·Cf)·G_{κ(t−s)}(z)`.
    Assembles the `F`-weighting (`|F| ≤ Cf`, `hFbd`) on top of the carried bare-kernel x-free envelope
    `henv` (`∀ᶠ x in 𝓝 x₀, ∀ᵐ z, |witnessFieldDeriv i (t−s) x z| ≤ C₀·G_{κ(t−s)}(z)`, GROUNDED in
    `witnessFieldDeriv_gate_envelope`; NOT the F-weighted conclusion).  NOT `a₁ = R/6`. -/
theorem hzbound_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (F : ℝ → Point n → ℝ) (ν : Measure (Point n)) (u : Set (Point n))
    (κ C₀ Cf : ℝ) (hC₀ : 0 ≤ C₀)
    (hFbd : ∀ s z, |F s z| ≤ Cf)
    (henv : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂ν,
          |witnessFieldDeriv g gi hC hK S a b i (t - s) x z| ≤ C₀ * gaussDdim (κ * (t - s)) z) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
      ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂ν,
        ‖witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z‖
          ≤ (C₀ * Cf) * gaussDdim (κ * (t - s)) z := by
  intro x₀ hx₀ i
  filter_upwards [henv x₀ hx₀ i] with s hs hmem
  filter_upwards [hs hmem] with x hx
  filter_upwards [hx] with z hz
  have hGnn : 0 ≤ gaussDdim (κ * (t - s)) z := gaussDdim_nonneg _ _
  rw [Real.norm_eq_abs, abs_mul]
  calc |witnessFieldDeriv g gi hC hK S a b i (t - s) x z| * |F s z|
      ≤ (C₀ * gaussDdim (κ * (t - s)) z) * Cf :=
        mul_le_mul hz (hFbd s z) (abs_nonneg _) (mul_nonneg hC₀ hGnn)
    _ = (C₀ * Cf) * gaussDdim (κ * (t - s)) z := by ring

/-! ###############################################################################
    ### STEP 3 — the x-free envelope integrability (the `hzint` slot).
    ############################################################################### -/

/-- **STEP 3 — `envelope_integrable`.**  The x-free Gaussian envelope `z ↦ C₀·G_σ(z)` is integrable over
    `Point n` for `σ > 0` (from `gaussDdim_integrable`).  NOT `a₁ = R/6`. -/
theorem envelope_integrable (σ : ℝ) (hσ : 0 < σ) (C₀ : ℝ) :
    Integrable (fun z : Point n => C₀ * gaussDdim σ z) volume :=
  (QIQTH.HeatResidualBound.gaussDdim_integrable σ hσ).const_mul C₀

/-- **★★ STEP 3 — `hzint_witness`.**  THE EXACT `hzint` SLOT for the x-free dominator
    `boundz s z = C₀·G_{κ(t−s)}(z)`:  for a.e. `s`, `s ∈ Ι 0 t → Integrable (boundz s) ν=volume`.  The
    width `κ·(t−s)` is positive for every `s ∈ Ι 0 t = Ioc 0 t` with `s ≠ t`, and `{t}` is null, so the
    integrability holds a.e.  NOT `a₁ = R/6`. -/
theorem hzint_witness (κ t : ℝ) (hκ : 0 < κ) (ht : 0 < t) (C₀ : ℝ) :
    ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 t →
      Integrable (fun z : Point n => C₀ * gaussDdim (κ * (t - s)) z) volume := by
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext a; simp
    rw [hset]; exact Real.volume_singleton
  filter_upwards [hae] with s hs hmem
  rw [Set.uIoc_of_le ht.le] at hmem
  have hst : s < t := lt_of_le_of_ne hmem.2 hs
  have hσ : 0 < κ * (t - s) := mul_pos hκ (by linarith)
  exact envelope_integrable (κ * (t - s)) hσ C₀

end QIQTH.WitnessDerivDomination

section AxiomChecks
open QIQTH.WitnessDerivDomination
#print axioms pd_continuousAt_of_contDiffAt
#print axioms witnessFieldDeriv_continuousAt
#print axioms witnessFieldDeriv_mul_const_continuousAt
#print axioms hzcont_witness
#print axioms witnessFieldDeriv_gate_envelope
#print axioms hzbound_witness
#print axioms envelope_integrable
#print axioms hzint_witness
end AxiomChecks
