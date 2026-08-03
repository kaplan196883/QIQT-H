/-
  GcoefContinuity — J4-160: the gcoef-continuity carry of the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It closes ONE
  reduced carry of the `hCConv` L1 layer: the `hcont` slot of
  `QIQTH.PartialsToFDeriv.hAssembly_reduced`, namely the CONTINUITY of the first-derivative
  integral coefficient functions
      `gcoef i x = ∫ s in (0)..t, ∫ z, dH i (t − s) x z · F s z 0`
  (the linewise-derivative value produced by `CConvLayerDischarge.hConvDeriv_linewise`), proven
  under the double integral by two nested dominated-convergence continuity theorems.

  ── WHAT IS PROVED HERE (axiom-free, no `sorry`).
    • G1  `continuousAt_doubleIntegral_of_dominated` — ★ THE ABSTRACT NESTED ENGINE (reusable).
        Continuity at `x₀` of `x ↦ ∫ s in (0)..t, ∫ z, K s x z ∂ν` from:
          (inner, per-s a.e.) x-nbhd ae-measurability + a fixed z-dominator `boundz s` + z-bound
          integrability + per-z x-continuity  ⟹ (via `MeasureTheory.continuousAt_of_dominated`)
          the per-s continuity of `x ↦ ∫ z, K s x z ∂ν`;
          (outer) x-nbhd ae-measurability of `s ↦ ∫ z, K s x z ∂ν` + a fixed s-dominator `B` +
          interval-integrability of `B`  ⟹ (via `intervalIntegral.continuousAt_of_dominated_-
          interval`) the continuity of the whole double integral.
        TWO nested dominated-continuity applications, stated fully parametrically.

    • G3  `gcoef_continuity_discharge` — ★ THE EXACT `hcont` SHAPE.  Specialises G1 to the concrete
        coefficient family `gcoef i x = ∫ s in (0)..t, ∫ z, dH i (t − s) x z · F s z 0` and produces
          `∀ x ∈ u, ∀ i, ContinuousAt (gcoef i) x`
        — verbatim the `hcont` hypothesis of `QIQTH.PartialsToFDeriv.hAssembly_reduced` — from the
        per-`(i, x₀)` domination/continuity bundle that G1 consumes.

  ── WHAT REMAINS CARRIED (G2, each satisfiable, non-vacuous, NEVER the conclusion).
    The per-`(i, x₀)` bundle threaded into G3 is the labelled family the engine consumes.  For the
    concrete `dH := witnessFieldDeriv`:
      • the per-`(s, z)` x-continuity of `K` is satisfiable from the on-gate factorisation
        `EngineInstantiation.witnessFieldDeriv_gate_eq`
        (`G_τ(W z x)·scalar·A(x) + G_τ(W z x)·∂A(x)` — continuous in the field slot via the germ-C²
        chart + `AmplitudeFamilyDischarge`'s C² amplitude);
      • the x-FREE z-dominator is satisfiable from `EngineInstantiation.witnessFieldDeriv_gate_abs_le`
        (the `G_τ(W z x)·(Bs·Ba + Bd)` Gaussian envelope), whose x-dependence in the FIELD slot is
        absorbed on a small ball by the chart's field-slot Lipschitz bound (`ApproximatesLinearOn`)
        plus the two-regime near/far Gaussian half-coercivity split (the `gaussDdim` levers) — a
        `const·G_{cτ}(z-arg)` x-free envelope.
    These are the ENGINE INPUTS (differentiation/continuity-under-∫ domination data), carried, not
    the (global) conclusion.

  NO `sorry`.  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.PartialsToFDeriv

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatDuhamel
open scoped BigOperators Topology Interval

namespace QIQTH.GcoefContinuity

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### G1 — the abstract nested dominated-continuity engine.
    ############################################################################### -/

/-- **★ G1 — `continuousAt_doubleIntegral_of_dominated`.**  Continuity at `x₀` of the double integral
    `x ↦ ∫ s in (0)..t, ∫ z, K s x z ∂ν`, obtained by TWO nested dominated-continuity applications:

    • the INNER `MeasureTheory.continuousAt_of_dominated` gives, for almost every `s ∈ Ι 0 t`, the
      continuity at `x₀` of `x ↦ ∫ z, K s x z ∂ν`, from
        `hzmeas` (x-nbhd ae-measurability of `z ↦ K s x z`),
        `hzbound` (x-nbhd ae z-domination `‖K s x z‖ ≤ boundz s z`),
        `hzint` (integrability of the z-dominator `boundz s`),
        `hzcont` (per-z x-continuity of `x ↦ K s x z`);
    • the OUTER `intervalIntegral.continuousAt_of_dominated_interval` then gives the continuity of the
      whole double integral, from
        `hsmeas` (x-nbhd ae-measurability of `s ↦ ∫ z, K s x z ∂ν`),
        `hsbound` (x-nbhd ae s-domination `‖∫ z, K s x z ∂ν‖ ≤ B s`),
        `hBint` (interval-integrability of the s-dominator `B`),
      with `h_cont` supplied by the inner continuities above.

    Fully parametric in `K`, `B`, `boundz` and the domination/measurability family.  NOT `a₁ = R/6`. -/
theorem continuousAt_doubleIntegral_of_dominated
    {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace Y]
    {ν : Measure Y} (t : ℝ) (x₀ : X)
    (K : ℝ → X → Y → ℝ) (B : ℝ → ℝ) (boundz : ℝ → Y → ℝ)
    (hzmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun z => K s x z) ν)
    (hzbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂ν, ‖K s x z‖ ≤ boundz s z)
    (hzint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → Integrable (boundz s) ν)
    (hzcont : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂ν, ContinuousAt (fun x => K s x z) x₀)
    (hsmeas : ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable (fun s => ∫ z, K s x z ∂ν) (volume.restrict (Set.uIoc 0 t)))
    (hsbound : ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ‖∫ z, K s x z ∂ν‖ ≤ B s)
    (hBint : IntervalIntegrable B volume 0 t) :
    ContinuousAt (fun x => ∫ s in (0)..t, ∫ z, K s x z ∂ν) x₀ := by
  refine intervalIntegral.continuousAt_of_dominated_interval hsmeas hsbound hBint ?_
  -- The outer `h_cont`: for a.e. `s ∈ Ι 0 t`, `x ↦ ∫ z, K s x z ∂ν` is continuous at `x₀`.
  filter_upwards [hzmeas, hzbound, hzint, hzcont] with s hm hb hi hc hs
  exact MeasureTheory.continuousAt_of_dominated (hm hs) (hb hs) (hi hs) (hc hs)

/-! ###############################################################################
    ### G3 — the concrete discharge: the exact `hcont` shape.
    ############################################################################### -/

/-- **★ G3 — `gcoef_continuity_discharge`.**  The `hcont` slot of
    `QIQTH.PartialsToFDeriv.hAssembly_reduced`, PROVEN for the concrete first-derivative coefficient
    family
      `gcoef i x = ∫ s in (0)..t, ∫ z, dH i (t − s) x z · F s z 0`
    (the value returned by `CConvLayerDischarge.hConvDeriv_linewise`).  Specialising G1 with the
    concrete kernel `K s x z = dH i (t − s) x z · F s z 0` (over `ν = volume` on `Point n`), the
    continuity of each `gcoef i` at each `x₀ ∈ u` follows from the per-`(i, x₀)` domination/continuity
    bundle the engine consumes (the G2 family; satisfiable from the E1/E2 banked
    `witnessFieldDeriv_gate_eq` / `witnessFieldDeriv_gate_abs_le` facts, per the header).

    The conclusion is VERBATIM `∀ x ∈ u, ∀ i, ContinuousAt (gcoef i) x`.  NOT `a₁ = R/6`. -/
theorem gcoef_continuity_discharge
    {ι X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace Y]
    {ν : Measure Y} (t : ℝ)
    (dH : ι → ℝ → X → Y → ℝ) (F : ℝ → Y → ℝ)
    (u : Set X)
    (B : ι → X → ℝ → ℝ) (boundz : ι → X → ℝ → Y → ℝ)
    (hzmeas : ∀ x₀ ∈ u, ∀ i : ι, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun z => dH i (t - s) x z * F s z) ν)
    (hzbound : ∀ x₀ ∈ u, ∀ i : ι, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂ν, ‖dH i (t - s) x z * F s z‖ ≤ boundz i x₀ s z)
    (hzint : ∀ x₀ ∈ u, ∀ i : ι, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → Integrable (boundz i x₀ s) ν)
    (hzcont : ∀ x₀ ∈ u, ∀ i : ι, ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂ν, ContinuousAt (fun x => dH i (t - s) x z * F s z) x₀)
    (hsmeas : ∀ x₀ ∈ u, ∀ i : ι, ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable (fun s => ∫ z, dH i (t - s) x z * F s z ∂ν)
          (volume.restrict (Set.uIoc 0 t)))
    (hsbound : ∀ x₀ ∈ u, ∀ i : ι, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ‖∫ z, dH i (t - s) x z * F s z ∂ν‖ ≤ B i x₀ s)
    (hBint : ∀ x₀ ∈ u, ∀ i : ι, IntervalIntegrable (B i x₀) volume 0 t) :
    ∀ x₀ ∈ u, ∀ i : ι,
      ContinuousAt (fun x => ∫ s in (0)..t, ∫ z, dH i (t - s) x z * F s z ∂ν) x₀ := by
  intro x₀ hx₀ i
  exact continuousAt_doubleIntegral_of_dominated t x₀
    (fun s x z => dH i (t - s) x z * F s z) (B i x₀) (boundz i x₀)
    (hzmeas x₀ hx₀ i) (hzbound x₀ hx₀ i) (hzint x₀ hx₀ i) (hzcont x₀ hx₀ i)
    (hsmeas x₀ hx₀ i) (hsbound x₀ hx₀ i) (hBint x₀ hx₀ i)

/-! ###############################################################################
    ### G3+ — the fully-threaded L1 closure (linewise + assembly + continuity all in).
    ############################################################################### -/

/-- **★ G3+ — `hCConv_L1_final`.**  The full L1 `∃`-shape carried by `SpatialC2.hCConv_reduction`,
    threaded HONESTLY from the three closed/reduced inputs on an OPEN field nbhd `u ∋ 0`:
      • `hlin`  — the per-coordinate `HasDerivAt` linewise family (each = `CConvLayerDischarge.-
        hConvDeriv_linewise`), with value `(D x)(Pi.single i 1)`;
      • `hcont` — the coefficient-continuity family, VERBATIM the output of `gcoef_continuity_discharge`
        (this file, G3);
      • `hDrep` — the coordinate representation `D x = ∑ i, gcoef i x • proj i`.
    It composes `PartialsToFDeriv.hAssembly_reduced` (which turns `hpart`/`hcont`/`hDrep` into the
    partials→FDeriv assembly) with `HeatResidualBound.hCConv_L1_of_partialsContinuity` (which turns the
    linewise family + that assembly into the `∃` shape).  The linewise value `(D x)(Pi.single i 1)`
    equals `gcoef i x` via `hDrep` (`hcoord`), so `hpart` follows from `hlin`.  NOT `a₁ = R/6`. -/
theorem hCConv_L1_final {n : ℕ}
    (H F : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (D : Point n → (Point n →L[ℝ] ℝ))
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (gcoef : Fin n → Point n → ℝ)
    (hlin : ∀ x ∈ u, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv H F t (Function.update x i w) 0)
        ((D x) (Pi.single i (1 : ℝ))) (x i))
    (hcont : ∀ x ∈ u, ∀ i : Fin n, ContinuousAt (gcoef i) x)
    (hDrep : ∀ x ∈ u,
      D x = ∑ i : Fin n, gcoef i x • (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ)) :
    ∃ u ∈ 𝓝 (0 : Point n), ∀ x ∈ u,
      HasFDerivAt (fun p => heatConv H F t p 0) (D x) x := by
  -- The coordinate identity `(D x)(Pi.single i 1) = gcoef i x`.
  have hcoord : ∀ x ∈ u, ∀ i : Fin n, (D x) (Pi.single i (1 : ℝ)) = gcoef i x := by
    intro x hx i
    rw [hDrep x hx, ContinuousLinearMap.sum_apply]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  -- The linewise partials with value `gcoef i x` (needed by `hAssembly_reduced`).
  have hpart : ∀ x ∈ u, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv H F t (Function.update x i w) 0) (gcoef i x) (x i) := by
    intro x hx i; rw [← hcoord x hx i]; exact hlin x hx i
  have hu_nhds : u ∈ 𝓝 (0 : Point n) := hu_open.mem_nhds hu0
  exact QIQTH.HeatResidualBound.hCConv_L1_of_partialsContinuity H F t D u hu_nhds hlin
    (QIQTH.PartialsToFDeriv.hAssembly_reduced H F t D u hu_open gcoef hpart hcont hDrep)

end QIQTH.GcoefContinuity

section AxiomChecks
open QIQTH.GcoefContinuity
#print axioms continuousAt_doubleIntegral_of_dominated
#print axioms gcoef_continuity_discharge
#print axioms hCConv_L1_final
end AxiomChecks
