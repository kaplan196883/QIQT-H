/-
  SpatialC2 — J4-147: discharging the `hCH` (and reducing `hCConv`) spatial-`C²` residue slots of
  the banked final-reduction `CapstoneStatus.a1_R6_of_residue`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`.  It is ONE brick of the a₁ = R/6 campaign: it removes
  the `hCH` slot (`ContDiffAt ℝ 2 (fun p ↦ H_G t p 0) 0`) from the residue of `a1_R6_of_residue` by
  GENUINELY PROVING it, and it REDUCES the `hCConv` slot
  (`ContDiffAt ℝ 2 (fun p ↦ heatConv H_G (leviSeries …) t p 0) 0`) to two honest, still-open analytic
  layers (a nbhd `HasFDerivAt` family = the first spatial derivative under `∫∫`, dominated by the
  `τ^{−1/2}·G` domination family; and the `C¹` regularity of that derivative map = the singular
  second-derivative content that the proven Laplacian-sliver machinery computes at the center).  No
  new analysis of the singular convolution is done here; the hard content becomes carried hypotheses.

  ── C1 (LANDED) — `hCH_discharge`.  `ContDiffAt ℝ 2 (fun p ↦ H_G t p 0) 0`, GENUINELY PROVED.
     Route:  the on-gate germ factorisation
       `(fun p ↦ H_G t p 0) =ᶠ[𝓝 0] (fun p ↦ radialCutoff a b (W₀ p)
            · (gaussDdim t (W₀ p) · vanVleck g (W₀ p)^{−1/2} · (u₀(W₀ p) + u₁(W₀ p)·t)))`
     (from `AmplitudePackage.vanVleckGatedWitness_gate_apply` at BASE `q = 0`, on the OPEN gate `S 0`),
     where `W₀ = uniformInverseChart g gi hChr hK 0` is the BASE-0 field chart, `C²` at the field
     centre (`ChartJetBounds.chartField_contDiffAt_center`, UNCONDITIONAL given `0 ∈ K`).  Each factor
     is `ContDiffAt ℝ 2` at `0`:  `W₀` (chart), `gaussDdim t ∘ W₀` (`gaussDdim_contDiff`),
     `radialCutoff ∘ W₀` (`radialCutoff_contDiff`), `vanVleck g ∘ W₀` (`vanVleck_contDiffAt`, with
     `det g(0) = 1 > 0` from the RNC gauge), its `−1/2` rpow (`rpow_const_of_ne`, `vanVleck g 0 = 1 ≠ 0`
     via `vanVleck_zero` + `W₀ 0 = 0`), and `u_k ∘ W₀` (carried transport-coefficient smoothness `hu`,
     the honest `hsrc`-style carry).  Products via `ContDiffAt.mul`; transfer via
     `ContDiffAt.congr_of_eventuallyEq`.

  ── C2 (REDUCED) — `hCConv_reduction`.  `ContDiffAt ℝ 2 (fun p ↦ heatConv H_G F t p 0) 0` from the
     two carried layers via `contDiffAt_succ_iff_hasFDerivAt` (`2 = 1 + 1`).  Honest structure, no
     singular analysis performed here.

  ── C3 (THREADED) — `a1_R6_of_residue_hCH_discharged`.  `a1_R6_of_residue` with the `hCH` slot GONE
     (supplied by C1) and the `hCConv` slot REPLACED by C2's two analytic layers.

  Carried hypotheses are satisfiable, non-vacuous, and never equal to the conclusion.  NO `sorry`.
  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CapstoneStatus
import QIQTH.NormalFormDischarge
import QIQTH.ChartJetBounds
import QIQTH.AmplitudePackage

open MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.ParametrixFunction QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.VanVleck
open QIQTH.HeatTransportRecursion QIQTH.RadialDistance QIQTH.VanVleckCancellation QIQTH.HeatParametrixOrder
open QIQTH.GaussianWidthTolerant QIQTH.RNCDecay QIQTH.ResidueBound QIQTH.PullbackMetric
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### C1 — `hCH_discharge`: the spatial-`C²` of the witness diagonal slice, GENUINELY PROVED. -/

/-- **★★★ J4-147 (C1) — `hCH_discharge`.**  The capstone's `hCH` slot for the concrete `N = 1` gated
    van-Vleck witness `H_G := vanVleckGatedWitness g gi hChr hK S a b`, GENUINELY PROVED:
      `ContDiffAt ℝ 2 (fun p ↦ H_G t p 0) 0`.
    The field slot `p` is regular through the BASE-0 chart `W₀ = uniformInverseChart g gi hChr hK 0`,
    whose field-center `C²` is `ChartJetBounds.chartField_contDiffAt_center`.  Genuine carries:
    `0 ∈ K`, `0 ∈ S 0`, `IsOpen (S 0)` (gate is a nbhd of the center), the metric smoothness `hg`, the
    RNC gauge `g(0) = δ` (`hg0`, giving `det g(0) = 1 > 0` and `vanVleck g 0 = 1`), and the transport-
    coefficient smoothness `hu` (the honest `hsrc`-style carry — `u_0 ≡ 1` is trivial, `u_1` rides the
    radial-transport solver).  NOT `a₁ = R/6`. -/
theorem hCH_discharge (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0) (hSopen : IsOpen (S 0))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n) := by
  -- the BASE-0 field chart and its center facts.
  set W := uniformInverseChart g gi hChr hK 0 with hWdef
  have hW2 : ContDiffAt ℝ 2 W (0 : Point n) := chartField_contDiffAt_center g gi hChr hK hK0
  have hW0 : W (0 : Point n) = 0 := chartField_centerValue_base0 g gi hChr hK hK0
  -- RNC gauge:  det g(0) = 1  ⟹  vanVleck g 0 = 1 > 0.
  have hgmat : (fun i j => g 0 i j) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    funext i j; exact hg0 i j
  have hdet0 : Matrix.det (g 0) = 1 := by
    rw [show (g 0) = (1 : Matrix (Fin n) (Fin n) ℝ) from hgmat, Matrix.det_one]
  have hvv0 : vanVleck g 0 = 1 := vanVleck_zero g hdet0
  -- the target factored form.
  set F : Point n → ℝ := fun p =>
    radialCutoff a b (W p)
      * (gaussDdim t (W p) * vanVleck g (W p) ^ (-(1 : ℝ) / 2)
          * (transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)
            + transportCoeff (transportOp (vanVleck g) g gi) 1 (W p) * t)) with hFdef
  -- germ equality on the OPEN gate `S 0`.
  have heq : (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) =ᶠ[𝓝 (0 : Point n)] F := by
    refine eventually_nhds_iff.mpr ⟨S 0, ?_, hSopen, hS0⟩
    intro x' hx'
    show vanVleckGatedWitness g gi hChr hK S a b t x' 0 = F x'
    rw [vanVleckGatedWitness_gate_apply g gi hChr hK S a b t hK0 hx']
  -- each factor is `ContDiffAt ℝ 2` at `0`.
  have hcut : ContDiffAt ℝ 2 (fun p => radialCutoff a b (W p)) (0 : Point n) :=
    ((radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)).comp 0 hW2
  have hgauss : ContDiffAt ℝ 2 (fun p => gaussDdim t (W p)) (0 : Point n) :=
    ((gaussDdim_contDiff t).contDiffAt.of_le le_top).comp 0 hW2
  -- van-Vleck smoothness at `W 0`  (`det g(W 0) = det g(0) = 1 > 0`).
  have hdetW : 0 < Matrix.det (g (W (0 : Point n))) := by rw [hW0, hdet0]; norm_num
  have hvv : ContDiffAt ℝ 2 (fun p => vanVleck g (W p)) (0 : Point n) :=
    (vanVleck_contDiffAt g hg (W (0 : Point n)) hdetW (k := 2)).comp 0 hW2
  -- its `−1/2` rpow branch  (`vanVleck g (W 0) = 1 ≠ 0`).
  have hne : (fun p => vanVleck g (W p)) (0 : Point n) ≠ 0 := by
    show vanVleck g (W (0 : Point n)) ≠ 0
    rw [hW0, hvv0]; norm_num
  have hrpow : ContDiffAt ℝ 2 (fun p => vanVleck g (W p) ^ (-(1 : ℝ) / 2)) (0 : Point n) :=
    hvv.rpow_const_of_ne hne
  -- the two transport coefficients through the chart (`hu` now at `∞`; downcast `2 ≤ ∞`).
  have h2inf : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
    have h := (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    simpa using h
  have hu0 : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)) (0 : Point n) :=
    (((hu 0).contDiffAt).of_le h2inf).comp 0 hW2
  have hu1 : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 1 (W p)) (0 : Point n) :=
    (((hu 1).contDiffAt).of_le h2inf).comp 0 hW2
  -- assemble the amplitude and the product.
  have hsum : ContDiffAt ℝ 2
      (fun p => transportCoeff (transportOp (vanVleck g) g gi) 0 (W p)
        + transportCoeff (transportOp (vanVleck g) g gi) 1 (W p) * t) (0 : Point n) :=
    hu0.add (hu1.mul contDiffAt_const)
  have hF : ContDiffAt ℝ 2 F (0 : Point n) := hcut.mul ((hgauss.mul hrpow).mul hsum)
  exact hF.congr_of_eventuallyEq heq

/-! ### C2 — `hCConv_reduction`: honest reduction of the spatial-`C²` convolution slot. -/

/-- **★★ J4-147 (C2) — `hCConv_reduction`.**  The capstone's `hCConv` slot for the concrete witness,
    HONESTLY REDUCED to two still-open analytic layers via `contDiffAt_succ_iff_hasFDerivAt`
    (`2 = 1 + 1`):
      (L1) a nbhd `HasFDerivAt` family `hfam` — the FIRST spatial derivative of the space-time
           convolution under the `∫₀ᵗ ∫` sign, which is dominated-integrable (`|∂ₚH| ~ τ^{−1/2}G`,
           `∫₀ᵗ τ^{−1/2} = 2√t`); the derivative map is `D`;
      (L2) `hD1 : ContDiffAt ℝ 1 D 0` — the `C¹` regularity of that derivative map, whose OWN
           derivative is the SINGULAR second-derivative content (`~ τ^{−1}G`, not absolutely
           integrable) that the proven Laplacian-sliver / cancellation machinery computes at the
           center `x = 0`.
    No singular convolution analysis is performed here — the honest structure only.  `H`, `F`, `t`
    are free (the reduction is generic in the convolution kernels).  NOT `a₁ = R/6`. -/
theorem hCConv_reduction
    (H : ℝ → Point n → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (D : Point n → (Point n →L[ℝ] ℝ))
    (hfam : ∃ u ∈ 𝓝 (0 : Point n),
      ∀ x ∈ u, HasFDerivAt (fun p => heatConv H F t p 0) (D x) x)
    (hD1 : ContDiffAt ℝ 1 D (0 : Point n)) :
    ContDiffAt ℝ 2 (fun p => heatConv H F t p 0) (0 : Point n) := by
  have h2 : (2 : WithTop ℕ∞) = ((1 : ℕ) : WithTop ℕ∞) + 1 := by norm_num
  rw [h2]
  exact contDiffAt_succ_iff_hasFDerivAt.mpr ⟨D, hfam, hD1⟩

/-! ### C3 — thread C1 (+ C2's reduction) into the final reduction. -/

/-- **★★★ J4-147 (C3) — `a1_R6_of_residue_hCH_discharged`.**  The banked final reduction
    `a1_R6_of_residue`, with the `hCH` slot GENUINELY DISCHARGED by C1 (`hCH_discharge`) and the
    `hCConv` slot REPLACED by C2's two honest analytic layers (`hConvDeriv`, `hConvD1`).  The residue
    shrinks by one full slot (`hCH` removed) and refactors `hCConv` into its C¹-plus-singular-second
    structure.  New carries relative to `a1_R6_of_residue`: `hSopen` (gate openness at the center) and
    `hu` (transport-coefficient smoothness) — both satisfiable, non-vacuous, never the conclusion.
    ⚠ STILL NOT `a₁ = R/6`; the GAUGE + remaining ANALYTIC residue (incl. the two `hCConv` layers) is
    carried. -/
theorem a1_R6_of_residue_hCH_discharged
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hSopen : IsOpen (S 0))
    (H : ℝ → Point n → Point n → ℝ)
    (hHeq : H = vanVleckGatedWitness g gi hChr hK S a b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi H τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi H) 2 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries (heatOp g gi H)) u p q) t 0 0
        = leviSeries (heatOp g gi H) t 0 0
          + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0)
    (hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi H)
            (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries (heatOp g gi H)) u 0 0) t)
    -- the two honest `hCConv` layers (replacing the single `hCConv` slot).
    (D : Point n → (Point n →L[ℝ] ℝ))
    (hConvDeriv : ∃ u ∈ 𝓝 (0 : Point n),
      ∀ x ∈ u, HasFDerivAt (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) (D x) x)
    (hConvD1 : ContDiffAt ℝ 1 D (0 : Point n)) :
    heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
    ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- C1: discharge `hCH` from the germ/chart tower.
  have hCH : ContDiffAt ℝ 2 (fun p => H t p 0) (0 : Point n) := by
    rw [hHeq]
    exact hCH_discharge g gi hChr hK S a b t hK0 hS0 hSopen hg hg0
      (fun k => (hu k).of_le le_top)
  -- C2: reduce `hCConv` from the two analytic layers.
  have hCConv : ContDiffAt ℝ 2
      (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) (0 : Point n) :=
    hCConv_reduction H (leviSeries (heatOp g gi H)) t D hConvDeriv hConvD1
  exact a1_R6_of_residue g gi Ric t ht C hCnn hChr hK S a b ha hab hK0 hS0 H hHeq
    hg hg0 hgi hΓ hdg0 htr hsrc hEboundW_le hInt hDuhamel hInter hDConv hCH hCConv

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms hCH_discharge
#print axioms hCConv_reduction
#print axioms a1_R6_of_residue_hCH_discharged
end AxiomChecks
