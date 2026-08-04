/-
  EboundWiringHD1 — J4-197: two light bricks of the a₁ = R/6 heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It performs
  two mechanical rewirings of the ALREADY-BANKED `∞`-capstone (`OmegaHsrcC4cAudit.a1_R6_of_residue_inf`):

  PART A — THE `hEboundW` WIRING (a carry removed).
    `a1_R6_of_residue_inf` carries `hEboundW_le` (the width-2 Gaussian domination of the gated van-Vleck
    heat operator) as an abstract HYPOTHESIS.  `CoeffU1Fix.gatedWitnessN1_hEboundW_le_vanVleck_final`
    already PROVES that domination from geometry, delivering `(C·(1+t))·baseKernelW 2 0` (vs the
    capstone's `C·baseKernelW 2 0`).  Since `t` is FIXED in the capstone, `C' := C·(1+t)` is a mere
    constant.
      • `hEboundW_from_geometry` — the provider repackaged into the capstone's EXACT `hEboundW_le`
        shape (with `H = vanVleckGatedWitness …`, constant `C'`).  The trivial `C ↦ C·(1+t)` reshape.
      • `a1_R6_of_residue_inf_v2` — `a1_R6_of_residue_inf` with the `hEboundW_le` carry DISCHARGED
        internally from the provider's geometric inputs; the outer carry list shrinks by one slot.

  PART B — THE L2 `hD1` ABSTRACT LEVER (+ assessment).
    `SpatialC2.hCConv_reduction` reduces the capstone's `hCConv` `C²` slot to
      (L1) a nbhd `HasFDerivAt` family (delivered by the facade), and
      (L2) `hD1 : ContDiffAt ℝ 1 D 0` — the `C¹` regularity of the first-derivative field `D`, whose
           components are the `gcoef` double integrals `gcoef i x = ∫₀ᵗ∫ dH·F`.
    The `hD1` route mirrors the L1 architecture ONE ORDER UP: it needs the SECOND `x`-derivative of the
    heat convolution `= ∫₀ᵗ∫ (∂ₓ dH)·F` under dominated differentiation.  `GcoefContinuity.-
    continuousAt_doubleIntegral_of_dominated` (J4-160) is the two-layer CONTINUITY engine for the same
    double integral; the missing piece for `hD1` is its DERIVATIVE analogue.  This file delivers it:
      • `hasFDerivAt_doubleIntegral_of_dominated` — `x ↦ ∫₀ᵗ∫ K s x z` is `HasFDerivAt` with derivative
        `∫₀ᵗ∫ K' s x z` at `x₀`, from a nested (inner `∫z` / outer `∫s`) domination bundle, composing
        `MeasureTheory.hasFDerivAt_integral_of_dominated_of_fderiv_le` (inner) through
        `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le` (outer).  Fully abstract in
        `K`/`K'`/`boundz`/`B` — the derivative analogue of J4-160's continuity engine.

    ASSESSMENT — what `hD1` still needs, banked vs missing (see the header block above the lever):
      BANKED at order 2:  `EngineInstantiation.witnessFieldDeriv2` (the second gated field-derivative
        kernel `dHH`), `witnessFieldDeriv2_center` (`= witnessSecondXDeriv` at the field centre),
        `witnessFieldDeriv2_offGate_eq_zero` (off-gate vanishing), `AmplitudePackage.sliver2_bound`,
        `NormalFormDischarge.witnessSecondXDeriv_offGate_eq_zero`, plus J4-191's extra Gaussian
        absorption power (`GaussianGradAbsorption`) for the one-order-up envelope.
      MISSING for `hD1`:  the ORDER-2 gate envelope (`witnessFieldDeriv2_gate_abs_le`, the E2-analogue
        one order up — the second-derivative Gaussian domination), the ORDER-2 joint measurability
        (the J4-185 `witnessFieldDeriv_measurable_of_gateEq` pattern applied to `witnessFieldDeriv2`),
        and the dominated-Leibniz application — the LAST piece of which is EXACTLY the abstract lever
        delivered here.

  No conclusion-in-disguise; no vacuous / unsatisfiable hypotheses; NO `sorry`; NO new axioms.
  All mains std-3.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OmegaHsrcC4cAudit
import QIQTH.CoeffU1Fix

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.PullbackMetric
open QIQTH.HeatParametrixAnsatz QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.OmegaHsrcC4cAudit
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.EboundWiringHD1

variable {n : ℕ}

/-! ══════════════════════════════════════════════════════════════════════════════════════════════
    ## PART A — the `hEboundW` wiring (a capstone carry removed).
    ══════════════════════════════════════════════════════════════════════════════════════════════ -/

/-- **★★ J4-197 (A1) — `hEboundW_from_geometry`.**  The `∞`-capstone's EXACT `hEboundW_le` slot
    (width-2 Gaussian domination of the gated van-Vleck heat operator, `H = vanVleckGatedWitness …`),
    delivered from geometry by `CoeffU1Fix.gatedWitnessN1_hEboundW_le_vanVleck_final`.  The provider
    gives `(C·(1+t))·baseKernelW 2 0`; since `t` is FIXED, `C' := C·(1+t)` is a constant — this is the
    only reshape.  The gate parameters `a b` and the gate map `S` are those the provider CHOOSES (via
    the flow-ball `GateSqControl` design), so they are returned existentially.  NOT `a₁ = R/6`. -/
theorem hEboundW_from_geometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ a b C' : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C' ∧ ∃ S : Point n → Set (Point n),
      ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C' * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound⟩ :=
    gatedWitnessN1_hEboundW_le_vanVleck_final g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  refine ⟨a, b, C * (1 + t), ha, hab, mul_nonneg hC0 (by linarith), S, ?_⟩
  intro τ p q hτ hτt
  exact hbound t τ p q hτ hτt

/-- **★★★ J4-197 (A2) — `a1_R6_of_residue_inf_v2`.**  `OmegaHsrcC4cAudit.a1_R6_of_residue_inf` with the
    `hEboundW_le` domination carry DISCHARGED internally from geometry (via
    `gatedWitnessN1_hEboundW_le_vanVleck_final`).  The gate parameters `a b` and gate map `S` are now
    PROVIDER-CHOSEN (existential), and the remaining honest carries — the gate-centre membership `hS0`
    and the Levi/Duhamel interface (`hInt`/`hDuhamel`/`hInter`/`hDConv`) plus the two field-`C²` slots
    (`hCH`/`hCConv`) — are inner hypotheses (satisfiable interface assembly, never the conclusion).
    Relative to `a1_R6_of_residue_inf` the OUTER carry list is shorter by exactly the `hEboundW_le`
    slot.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem a1_R6_of_residue_inf_v2 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ a b C' : ℝ, ∃ S : Point n → Set (Point n),
      0 < a ∧ a < b ∧ 0 ≤ C' ∧
      ((0 : Point n) ∈ S 0 →
        IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) 2 0 C' →
        (heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
            = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
              + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
                  (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0) →
        (heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
            = ∑' k : ℕ, heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
                (fun τ p q => (-1 : ℝ) ^ (k + 1)
                  * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) τ p q)
                t 0 0) →
        DifferentiableAt ℝ (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t →
        ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n) →
        ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
            (0 : Point n) →
        heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))) t 0 0 = 0
        ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
            = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
              * (1 + ((∑ i, Ric i i) / 6) * t
                  + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                              transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                                * t ^ (k - 2))
                            + heatConv (vanVleckGatedWitness g gi hChr hK S a b)
                                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
                                t 0 0
                                / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound⟩ :=
    gatedWitnessN1_hEboundW_le_vanVleck_final g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  refine ⟨a, b, C * (1 + t), S, ha, hab, mul_nonneg hC0 (by linarith), ?_⟩
  intro hS0 hInt hDuhamel hInter hDConv hCH hCConv
  have hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
        ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro τ p q hτ hτt
    exact hbound t τ p q hτ hτt
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  exact a1_R6_of_residue_inf g gi Ric t ht (C * (1 + t)) (mul_nonneg hC0 (by linarith))
    hChr hK S a b ha hab hK0 hS0 (vanVleckGatedWitness g gi hChr hK S a b) rfl
    hg hg0' hgi hΓ hdg0 htr hsrc hEboundW_le hInt hDuhamel hInter hDConv hCH hCConv

/-! ══════════════════════════════════════════════════════════════════════════════════════════════
    ## PART B — the L2 `hD1` abstract dominated-differentiation lever.
    ══════════════════════════════════════════════════════════════════════════════════════════════ -/

/-- **★★ J4-197 (B1) — `hasFDerivAt_doubleIntegral_of_dominated`.**  The DERIVATIVE analogue of
    `GcoefContinuity.continuousAt_doubleIntegral_of_dominated` (J4-160): the double integral
      `x ↦ ∫ s in (0)..t, ∫ z, K s x z ∂ν`
    is `HasFDerivAt` at `x₀` with derivative `∫ s in (0)..t, ∫ z, K' s x₀ z ∂ν`, obtained by TWO
    nested dominated-differentiation applications on an OPEN field neighbourhood `sSet ∋ x₀`:

    • the INNER `MeasureTheory.hasFDerivAt_integral_of_dominated_of_fderiv_le` gives, for a.e.
      `s ∈ Ι 0 t` and every `x ∈ sSet`, the `HasFDerivAt` at `x` of `x ↦ ∫ z, K s x z ∂ν` with
      derivative `∫ z, K' s x z ∂ν`, from
        `hKint`   (per-`x` `z`-integrability of `K s x`),
        `hKmeas`  (per-`x` `z`-ae-measurability of `K s x`),
        `hK'meas` (per-`x` `z`-ae-measurability of `K' s x`),
        `hK'bound`(`x`-uniform `z`-ae domination `‖K' s x z‖ ≤ boundz s z`),
        `hboundz_int` (integrability of the `z`-dominator `boundz s`),
        `hKdiff`  (the per-`z` `x`-`HasFDerivAt` of `x ↦ K s x z` with derivative `K' s x z`);
    • the OUTER `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le` then differentiates
      under `∫ s`, with `h_diff` supplied by the inner family and
        `hGmeas`  (`x`-nbhd `s`-ae-measurability of the inner integral),
        `hGint`   (interval-integrability of the base inner integral `∫ z, K · x₀ z`),
        `hG'meas` (`s`-ae-measurability of the base inner derivative `∫ z, K' · x₀ z`),
        `hG'bound`(`x`-uniform `s`-ae domination `‖∫ z, K' s x z ∂ν‖ ≤ B s`),
        `hBint`   (interval-integrability of the `s`-dominator `B`).

    Fully parametric in `K`, `K'`, `boundz`, `B`.  THIS is the last piece the L2 `hD1` needs: the
    dominated-Leibniz application to the already-built `gcoef` double integrals (its `K := ∂ₓ(dH)·F`,
    `K' :=` the second gated field derivative, `∂ₓ²(dH)·F`).  NOT `a₁ = R/6`. -/
theorem hasFDerivAt_doubleIntegral_of_dominated
    {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [MeasurableSpace Y] {ν : Measure Y}
    (t : ℝ) (x₀ : H) {sSet : Set H} (hsOpen : IsOpen sSet) (hx₀ : x₀ ∈ sSet)
    (K : ℝ → H → Y → ℝ) (K' : ℝ → H → Y → (H →L[ℝ] ℝ))
    (boundz : ℝ → Y → ℝ) (B : ℝ → ℝ)
    (hKint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ x ∈ sSet, Integrable (fun z => K s x z) ν)
    (hKmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ x ∈ sSet, AEStronglyMeasurable (fun z => K s x z) ν)
    (hK'meas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ x ∈ sSet, AEStronglyMeasurable (fun z => K' s x z) ν)
    (hK'bound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂ν, ∀ x ∈ sSet, ‖K' s x z‖ ≤ boundz s z)
    (hboundz_int : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → Integrable (boundz s) ν)
    (hKdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂ν, ∀ x ∈ sSet, HasFDerivAt (fun x => K s x z) (K' s x z) x)
    (hGmeas : ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable (fun s => ∫ z, K s x z ∂ν) (volume.restrict (Set.uIoc 0 t)))
    (hGint : IntervalIntegrable (fun s => ∫ z, K s x₀ z ∂ν) volume 0 t)
    (hG'meas : AEStronglyMeasurable (fun s => ∫ z, K' s x₀ z ∂ν) (volume.restrict (Set.uIoc 0 t)))
    (hG'bound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ x ∈ sSet, ‖∫ z, K' s x z ∂ν‖ ≤ B s)
    (hBint : IntervalIntegrable B volume 0 t) :
    HasFDerivAt (fun x => ∫ s in (0)..t, ∫ z, K s x z ∂ν)
      (∫ s in (0)..t, ∫ z, K' s x₀ z ∂ν) x₀ := by
  -- INNER LAYER: per-`s` differentiation under `∫ z`, uniform over the open field nbhd `sSet`.
  have hinner : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ x ∈ sSet,
      HasFDerivAt (fun x => ∫ z, K s x z ∂ν) (∫ z, K' s x z ∂ν) x := by
    filter_upwards [hKint, hKmeas, hK'meas, hK'bound, hboundz_int, hKdiff]
      with s h1 h2 h3 h4 h5 h6 hsmem x₁ hx₁
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun x z => K s x z) (F' := fun x z => K' s x z) (bound := boundz s)
      (hsOpen.mem_nhds hx₁)
      (Filter.eventually_of_mem (hsOpen.mem_nhds hx₁) (fun x hx => h2 hsmem x hx))
      (h1 hsmem x₁ hx₁)
      (h3 hsmem x₁ hx₁)
      (h4 hsmem)
      (h5 hsmem)
      (h6 hsmem)
  -- OUTER LAYER: differentiation under `∫ s`, the inner family as the `h_diff` bundle.
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x s => ∫ z, K s x z ∂ν) (F' := fun x s => ∫ z, K' s x z ∂ν) (bound := B)
    (hsOpen.mem_nhds hx₀) hGmeas hGint hG'meas hG'bound hBint hinner

end QIQTH.EboundWiringHD1

section AxiomChecks
open QIQTH.EboundWiringHD1
#print axioms hEboundW_from_geometry
#print axioms a1_R6_of_residue_inf_v2
#print axioms hasFDerivAt_doubleIntegral_of_dominated
end AxiomChecks
