/-
  HD1CLMLift — J4-219: the SCALAR → CLM lift of the `hD1` `C¹` slot of the a₁ = R/6 campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is ONE brick
  of the `a₁ = R/6` heat-kernel campaign: it closes the type mismatch J4-211 flagged between the banked
  SCALAR provider `XUniformSliverFull.hD1_from_data` (which proves `ContDiffAt ℝ 1 gfull 0` for a
  SCALAR field `gfull : H → ℝ`) and the capstone's `hD1` slot, which asks for
  `ContDiffAt ℝ 1 D 0` at the CLM-VALUED derivative field `D : Point n → (Point n →L[ℝ] ℝ)`
  (`CConvConcreteThreading.a1_R6_of_residue_inf_v5`, binder `hD1`; `CConvFacade.CConvDerivativeData`
  field `hDrep`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE HONEST MISMATCH DIAGNOSIS (asked by the ledger).

    • The SLOT wants: `hD1 : ContDiffAt ℝ 1 D (0 : Point n)` with `D : Point n → (Point n →L[ℝ] ℝ)`,
      and the bundle constrains `D` by
        `hDrep : ∀ x ∈ u, D x = ∑ i : Fin n, (gcoef i x) • (ContinuousLinearMap.proj i)`,
      where `gcoef i x = ∫ s in 0..t, ∫ z, witnessFieldDeriv … i (t−s) x z * F s z ∂volume`.
    • The PROVIDER gives (per COMPONENT): `hD1_from_data : ContDiffAt ℝ 1 gfull 0` for a SCALAR
      `gfull : H → ℝ`.  Applied at `gfull := gcoef i` it delivers `ContDiffAt ℝ 1 (gcoef i) 0` for each
      coordinate `i`.
    • So the mismatch is NOT a wrong scalar fact — it is exactly a componentwise → CLM ASSEMBLY: from
      `∀ i, ContDiffAt ℝ 1 (gcoef i) 0` and the representation `hDrep` (valid on a nbhd `u ∋ 0`), obtain
      `ContDiffAt ℝ 1 D 0`.  `hD1_reduction` (the ℝ-generic `ContDiffAt 1` assembler) is even already
      polymorphic in the target `F`; the ONLY missing step is the scalar-jets → CLM combination.

  ## WHAT LANDS (this file, ns `QIQTH.HD1CLMLift`).
    • `contDiffAt_clm_of_scalar_components` — ★ THE GENERIC LIFT.  A finite linear combination
      `x ↦ ∑ i ∈ s, gcoef i x • c i` of scalar `Cᵏ`-at-a-point coefficients (`gcoef i`) with CONSTANT
      vector weights `c i` is `Cᵏ`-at-a-point.  Fed by Mathlib `ContDiffAt.sum` + `ContDiffAt.smul`
      + `contDiffAt_const`.
    • `hD1_clm_of_scalar_and_rep` — ★★ THE GENERIC THREADING.  From per-coordinate scalar `ContDiffAt k`
      + a representation `D =ᶠ[𝓝 x₀] (∑ i, gcoef i • c i)` (via `hDrep` on `u ∈ 𝓝 x₀`), obtain
      `ContDiffAt k D x₀`, using `ContDiffAt.congr_of_eventuallyEq`.
    • `hD1_concrete_from_scalar` — ★★ THE CONCRETE THREADING.  The capstone's `hD1` slot
      (`ContDiffAt ℝ 1 D 0`) from the derivative bundle `CConvDerivativeData` (its `hDrep`) + the
      per-coordinate scalar jets (each = the `hD1_from_data` conclusion at `gfull := gcoef i`).
    • `a1_R6_of_residue_inf_v7` — ★★★ THE STRETCH.  `a1_R6_of_residue_inf_v5` with the single CLM-valued
      `hD1` binder REPLACED by the family of per-coordinate SCALAR jets `hgD1`; the CLM lift is
      re-derived in-place by `hD1_concrete_from_scalar`.  This shrinks the capstone surface from a
      CLM-typed regularity black box down to `n` scalar `ContDiffAt ℝ 1` facts, each of which is exactly
      what `XUniformSliverFull.hD1_from_data` produces.

  ## HONEST RESIDUE AFTER THIS BRICK.
    `hD1` is now reduced to `∀ i : Fin n, ContDiffAt ℝ 1 (gcoef i) 0` — the scalar per-component jets.
    Each is the conclusion of `XUniformSliverFull.hD1_from_data`; what remains open is precisely
    `hD1_from_data`'s OWN carry list (bulk derivatives, bulk pointwise convergence, the x-uniform sliver
    dist-bound, its vanishing, and the order-2 derivative-field continuity), applied at
    `gfull := gcoef i`.  No CLM-lift gap remains.

  Every hypothesis is satisfiable, non-vacuous, and never equal to the conclusion.  NO `sorry`.
  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CConvConcreteThreading

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound QIQTH.OmegaHsrcC4cAudit QIQTH.InftyRebaseCapstone
open QIQTH.CConvFacade QIQTH.GateOpennessExport QIQTH.CConvConcreteThreading
open scoped BigOperators Topology ContDiff Interval

namespace QIQTH.HD1CLMLift

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### 1. THE GENERIC LIFT — scalar `Cᵏ`-jets ⟹ CLM/vector `Cᵏ`-jet.
    ############################################################################### -/

/-- **★ J4-219 — `contDiffAt_clm_of_scalar_components`.**  A finite linear combination
    `x ↦ ∑ i ∈ s, gcoef i x • c i` of scalar coefficients `gcoef i : H → ℝ`, each `Cᵏ` at `x₀`, with
    CONSTANT vector weights `c i : F` (e.g. `c i = ContinuousLinearMap.proj i` so the target is the
    CLM space `Point n →L[ℝ] ℝ`), is itself `Cᵏ` at `x₀`.  This is the whole content of the scalar
    coordinate-jet → CLM-valued datum lift: `ContDiffAt.smul` (scalar × constant) then `ContDiffAt.sum`
    (finite sum).  NOT `a₁ = R/6`. -/
theorem contDiffAt_clm_of_scalar_components
    {H F ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Finset ι) (k : WithTop ℕ∞)
    (gcoef : ι → H → ℝ) (c : ι → F) (x₀ : H)
    (hg : ∀ i ∈ s, ContDiffAt ℝ k (gcoef i) x₀) :
    ContDiffAt ℝ k (fun x => ∑ i ∈ s, gcoef i x • c i) x₀ :=
  ContDiffAt.sum fun i hi => (hg i hi).smul contDiffAt_const

/-! ###############################################################################
    ### 2. THE GENERIC THREADING — scalar jets + representation ⟹ CLM `hD1`.
    ############################################################################### -/

/-- **★★ J4-219 — `hD1_clm_of_scalar_and_rep`.**  From per-coordinate scalar `Cᵏ`-jets `hg` and a
    representation `D x = ∑ i ∈ s, gcoef i x • c i` valid on a neighbourhood `u ∋ x₀` (`hDrep` + `hu`),
    conclude `ContDiffAt ℝ k D x₀`.  The representation is turned into `D =ᶠ[𝓝 x₀] (∑ i, gcoef i • c i)`
    and fed to `ContDiffAt.congr_of_eventuallyEq` on top of the generic lift (item 1).  This is the
    ℝ-generic engine behind the CLM-valued `hD1` slot; the target `F` is arbitrary.  NOT `a₁ = R/6`. -/
theorem hD1_clm_of_scalar_and_rep
    {H F ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (s : Finset ι) (k : WithTop ℕ∞)
    (D : H → F) (gcoef : ι → H → ℝ) (c : ι → F) (x₀ : H)
    {u : Set H} (hu : u ∈ 𝓝 x₀)
    (hDrep : ∀ x ∈ u, D x = ∑ i ∈ s, gcoef i x • c i)
    (hg : ∀ i ∈ s, ContDiffAt ℝ k (gcoef i) x₀) :
    ContDiffAt ℝ k D x₀ := by
  refine (contDiffAt_clm_of_scalar_components s k gcoef c x₀ hg).congr_of_eventuallyEq ?_
  filter_upwards [hu] with x hx using hDrep x hx

/-! ###############################################################################
    ### 3. THE CONCRETE THREADING — the capstone's `hD1` from the deriv bundle.
    ############################################################################### -/

/-- **★★ J4-219 — `hD1_concrete_from_scalar`.**  The capstone's `hD1` slot
    `ContDiffAt ℝ 1 D (0 : Point n)` from the derivative bundle `CConvDerivativeData` (whose `hDrep`
    pins `D = ∑ i, gcoef i • proj i` on the nbhd `u`) plus the per-coordinate scalar jets
      `hg i : ContDiffAt ℝ 1 (fun x => ∫ s in 0..t, ∫ z, witnessFieldDeriv … i (t−s) x z * F s z) 0`,
    each of which is EXACTLY the conclusion of `XUniformSliverFull.hD1_from_data` at
    `gfull := gcoef i`.  Instance of the generic threading (item 2) at `s = Finset.univ`,
    `c i = ContinuousLinearMap.proj i`.  NOT `a₁ = R/6`. -/
theorem hD1_concrete_from_scalar
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (F : ℝ → Point n → ℝ) (Hk Fconv : ℝ → Point n → Point n → ℝ)
    (D : Point n → (Point n →L[ℝ] ℝ))
    (deriv : CConvDerivativeData g gi hChr hK S a b t u F Hk Fconv D)
    (hg : ∀ i : Fin n, ContDiffAt ℝ 1
        (fun x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z * F s z
            ∂(volume : Measure (Point n))) (0 : Point n)) :
    ContDiffAt ℝ 1 D (0 : Point n) :=
  hD1_clm_of_scalar_and_rep Finset.univ 1 D
    (fun i x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z * F s z
        ∂(volume : Measure (Point n)))
    (fun i => (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ))
    (0 : Point n) (hu_open.mem_nhds hu0) deriv.hDrep (fun i _ => hg i)

/-! ###############################################################################
    ### 4. THE STRETCH — `a1_R6_of_residue_inf_v5` with `hD1` replaced by scalar jets.
    ############################################################################### -/

/-- **★★★ J4-219 — `a1_R6_of_residue_inf_v7`.**  `CConvConcreteThreading.a1_R6_of_residue_inf_v5` with
    the single CLM-valued regularity binder `hD1 : ContDiffAt ℝ 1 D 0` REPLACED by the family of
    per-coordinate SCALAR jets
      `hgD1 i : ContDiffAt ℝ 1 (fun x => ∫ s in 0..t, ∫ z, witnessFieldDeriv … i (t−s) x z * F s z) 0`.
    The CLM lift is re-derived in place by `hD1_concrete_from_scalar`, then `v5` is invoked.  This is
    the capstone surface after the CLM-lift brick: the `hD1` black box is now `n` scalar `ContDiffAt ℝ 1`
    facts, each = a `XUniformSliverFull.hD1_from_data` conclusion.  Every other hypothesis is `v5`'s
    verbatim.  NOT `a₁ = R/6`. -/
theorem a1_R6_of_residue_inf_v7 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) 2 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
        = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
          + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0)
    (hInter : heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
            (fun τ p q => (-1 : ℝ) ^ (k + 1)
              * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) τ p q)
            t 0 0)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t)
    (hCH : ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n))
    (u : Set (Point n)) (hu_open : IsOpen u) (hu0 : (0 : Point n) ∈ u)
    (Bs Ba Bd Cf : ℝ) (D : Point n → (Point n →L[ℝ] ℝ))
    (metric : CConvMetricData g gi)
    (chart : CConvChartGateData g gi hChr hK S a b t u)
    (source : CConvSourceData
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) t Cf)
    (deriv : CConvDerivativeData g gi hChr hK S a b t u
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      D)
    (env : CConvEnvelopeData g gi hChr hK S a b t u Bs Ba Bd)
    -- ★ the CLM-valued `hD1` binder, REPLACED by the family of per-coordinate SCALAR jets.
    (hgD1 : ∀ i : Fin n, ContDiffAt ℝ 1
        (fun x => ∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hChr hK S a b i (t - s) x z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0
            ∂(volume : Measure (Point n))) (0 : Point n)) :
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
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- re-derive the CLM-valued `hD1` from the per-coordinate scalar jets.
  have hD1 : ContDiffAt ℝ 1 D (0 : Point n) :=
    hD1_concrete_from_scalar g gi hChr hK S a b t u hu_open hu0
      (fun s z => leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      D deriv hgD1
  -- feed `v5` with `hD1` now discharged.
  exact a1_R6_of_residue_inf_v5 g gi Ric t ht C hCnn hChr hK S a b ha hab hK0 hS0
    hg hg0 hgi hΓ hdg0 htr hsrc hEboundW_le hInt hDuhamel hInter hDConv hCH
    u hu_open hu0 Bs Ba Bd Cf D metric chart source deriv env hD1

end QIQTH.HD1CLMLift

section AxiomChecks
open QIQTH.HD1CLMLift
#print axioms contDiffAt_clm_of_scalar_components
#print axioms hD1_clm_of_scalar_and_rep
#print axioms hD1_concrete_from_scalar
#print axioms a1_R6_of_residue_inf_v7
end AxiomChecks
