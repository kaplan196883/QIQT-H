/-
  UniformResidualPacket — J4-83 (the CONSTRUCTION-INDEPENDENT cutoff-residual producer).

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## Why this file exists — the hunif re-plumb.

  The per-base-point cutoff-residual producer `cutoffResidual_expPullback_hEboundW`
  (`RecenterCutoffC3.lean:97`) is stated OVER the OPAQUE `expPullbackMetric g₀ gi₀ hC p` and consumes a
  long list of q-centered geometric data whose constants (`M`, `W`, `L`, `Kg`, `Kc2`, the radius `b`) are
  HIDDEN per-base-point behind `expRho`-derived Taylor remainders.  Transferring that producer's FINAL
  bound across the `uniformFlowExp`-vs-`expMap` weld cannot make those hidden per-`q` constants uniform.

  The fix (GPT-5.6 architecture verdict) is to REFACTOR the producer into a CONSTRUCTION-INDEPENDENT
  lemma parametrized by an explicit CONSTANT/JET packet over an ABSTRACT metric `g̃`/`g̃⁻¹`, then
  instantiate the packet ONCE with the uniform-flow constants.  This file delivers that abstract producer.

  ## Landed here (green, DERIVED; no `sorry`, no new axioms, NO `expRho`, no vacuous hypotheses).

  `cutoffResidual_bound_from_packet` — over ANY metric field `g̃ = g` and inverse field `g̃⁻¹ = gi`
  (`Point n → Fin n → Fin n → ℝ`) and heat profiles `Θ`, `u`, from
    * the RNC near-JET packet at `0` (the exact hypotheses of the abstract near engine
      `near_uncutResidual_gaussianWide_ball_C3`: `C²` regularity of `g̃`/`g̃⁻¹`/`Γ̃`, `C³` of the folded
      cofactor, the value/first-jet gauge data `g̃(0)=δ`, `∂g̃(0)=0`, `Γ̃(0)=0`, `g̃⁻¹(0)=δ`,
      `∂g̃⁻¹(0)=0`, cyclic gauge, van-Vleck `∂²w₀ = −⅓Ric+…`, symmetry, nondegeneracy `g̃⁻¹·g̃=δ`,
      and the analytic near-bounds `hdev`/`hw0bd`/`hlap` with constants `M`/`W`/`L`);
    * the cutoff/annulus packet (`hw0smooth` global cofactor smoothness, `hgisymm` inverse symmetry,
      the annulus bounds `hgi_ann` for `|g̃⁻¹|` and `hLapChi_ann` for `|Δ_g̃χ|`),
  produces the FULL per-base-point width-2 cutoff-residual Gaussian bound
    `∃ a b, 0<a ∧ a<b ∧ ∃ B ≥ 0, ∀ v, |χ·∂ₜH − Δ_g̃(χ·H)| ≤ B·gaussDdimWide t v`  (χ = radialCutoff a b),
  by chaining the two EXISTING abstract engines: the near engine
  `near_uncutResidual_gaussianWide_ball_C3` (`NearResidualC3.lean`) supplies `hEnear` (fixing the outer
  radius `b`), and the finite-regularity cutoff engine `cutoffResidual_global_gaussianWide_bound_C2`
  (`CutoffResidualFiniteReg.lean`, already fully abstract over the metric) supplies the global bound.

  This is EXACTLY `cutoffResidual_expPullback_hEboundW`'s proof with `expPullbackMetric`/`expPullbackMetricInv`
  replaced by abstract fields and the near-jet discharges lifted to packet fields.  It has NO reference to
  `expMap`/`expRho`/`expPullbackMetric`, so it can be instantiated at `uniformFlowPullbackMetric` (whose
  uniform-over-`K` constants are supplied by the Brick-A/J4-80/81/82 uniform lemmas) — the S4 step.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.NearResidualC3
import QIQTH.CutoffResidualFiniteReg
import QIQTH.RecenterConnectC3c
import QIQTH.ParametrixHAnnulusBounds
import QIQTH.CutoffAnnulusBounds
import QIQTH.UniformFlowMetricInvProps
import QIQTH.UniformFlowJetZero

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.HeatParametrixAnsatz
open QIQTH.HeatParametrixOrder QIQTH.GaussianWidthTolerant
open QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 4

/-- **★ J4-83 — THE CONSTRUCTION-INDEPENDENT CUTOFF RESIDUAL WIDTH-2 GAUSSIAN BOUND (from a packet).**

For ANY abstract metric field `g` with inverse field `gi` (`= g̃`/`g̃⁻¹`) and heat profiles `Θ`/`u`, given
the RNC near-jet packet at `0` (the exact hypotheses of `near_uncutResidual_gaussianWide_ball_C3`) plus
the cutoff/annulus packet (`hw0smooth`, `hgisymm`, `hgi_ann`, `hLapChi_ann`), the cutoff-parametrix
heat-operator residual is globally dominated by a constant times the width-2 Gaussian on a nonempty
annulus `0 < a < b`:

  `∃ a b, 0<a ∧ a<b ∧ ∃ B ≥ 0, ∀ v, |χ(v)·∂ₜH v − Δ_g(χ·H) v| ≤ B·gaussDdimWide t v`  (χ = radialCutoff a b).

Chains the abstract near engine `near_uncutResidual_gaussianWide_ball_C3` (⟹ `hEnear`, fixing `b`) with
the abstract finite-regularity cutoff engine `cutoffResidual_global_gaussianWide_bound_C2`.  This IS
`cutoffResidual_expPullback_hEboundW` with the concrete pullback objects abstracted to fields — no
`expMap`/`expRho`/`expPullbackMetric`, so instantiable at `uniformFlowPullbackMetric`.  NOT `a₁ = R/6`. -/
theorem cutoffResidual_bound_from_packet
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    -- near-jet packet (verbatim hypotheses of `near_uncutResidual_gaussianWide_ball_C3`)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgiC : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hCd : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hw0hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - ((1 / 3) * ricci g gi a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
            * foldedCoeff Θ u 0 0)
    {t : ℝ} (ht : 0 < t) (M W L : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L)
    -- cutoff / annulus packet
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hgisymm : ∀ w i j, gi w i j = gi w j i)
    (hgi_ann : ∀ (a b : ℝ), ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (w : Point n) (i j : Fin n),
        a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |gi w i j| ≤ Kg)
    (hLapChi_ann : ∀ (a b : ℝ), ∃ Kc2 : ℝ, 0 ≤ Kc2 ∧ ∀ w : Point n,
        a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |laplaceBeltrami g gi (radialCutoff a b) w| ≤ Kc2) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) t
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * heatParametrix 0 Θ u t y) v|
        ≤ B * gaussDdimWide t v := by
  classical
  -- (1) `hEnear` from the ABSTRACT near engine; this FIXES the outer radius `b`.
  obtain ⟨b, hb0, hEnear⟩ :=
    near_uncutResidual_gaussianWide_ball_C3 g gi Θ u hg hgiC hCd hw0 hg0 hgi0 hdg0 hdgi0 hΓ0
      hsymm hinv hgauge hw0flat hw0hessRicci ht M W L hM hW hdev hw0bd hlap
  -- (2) `a := b/2` gives a nonempty annulus `0 < a < b`.
  set a : ℝ := b / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def]; linarith
  -- The near constant `C` and its nonnegativity.
  set C : ℝ := (1 + 32 * (n : ℝ) ^ 2 * M * W + L) * Real.sqrt 2 ^ n with hC_def
  have hL : (0 : ℝ) ≤ L := by
    obtain ⟨v0, hv0⟩ := hlap.exists
    exact le_trans (abs_nonneg _) hv0
  have hCnn : 0 ≤ C := by
    rw [hC_def]
    have h32 : (0 : ℝ) ≤ 32 * (n : ℝ) ^ 2 * M * W :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hM) hW
    exact mul_nonneg (by linarith) (by positivity)
  -- (3) The concrete parametrix `H = heatParametrix 0 Θ u t = gaussDdim t · (foldedCoeff Θ u 0)`.
  have hHeq : (heatParametrix 0 Θ u t : Point n → ℝ)
      = fun y => gaussDdim t y * foldedCoeff Θ u 0 y := by
    funext x
    rw [heatParametrix_folded]
    simp
  have hHeqw : ∀ w : Point n,
      heatParametrix 0 Θ u t w = gaussDdim t w * foldedCoeff Θ u 0 w := fun w => congrFun hHeq w
  -- `H` is smooth, hence `ContDiffAt ℝ 2`.
  have hH : ContDiff ℝ (⊤ : WithTop ℕ∞) (heatParametrix 0 Θ u t) := by
    rw [hHeq]
    exact (gaussDdim_contDiff t).mul hw0smooth
  have hH2 : ∀ w : Point n, ContDiffAt ℝ 2 (heatParametrix 0 Θ u t) w :=
    fun w => (hH.contDiffAt).of_le le_top
  -- (4) Annulus derivative bounds `hHann`/`hDHann` via `parametrixH_annulus_bounds`.
  obtain ⟨Mann, hMann0, hHann', hDHann'⟩ :=
    parametrixH_annulus_bounds t ht a b hb0 (foldedCoeff Θ u 0)
      hw0smooth.continuous
      (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) hw0smooth i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) hw0smooth j).continuous)
  have hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |heatParametrix 0 Θ u t w| ≤ Mann * gaussDdim t w := by
    intro w h1 h2
    rw [hHeqw w]
    exact hHann' w h1 h2
  have hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (heatParametrix 0 Θ u t) j w| ≤ Mann * (1 / t) * gaussDdim t w := by
    intro w j h1 h2
    rw [hHeq]
    exact hDHann' w j h1 h2
  -- (5) Metric / cutoff annulus bounds.
  obtain ⟨Kg, hKg, hgibd⟩ := hgi_ann a b
  obtain ⟨Kc1, hKc1, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a b
  obtain ⟨Kc2, hKc2, hLapChi⟩ := hLapChi_ann a b
  -- (6) Assemble the finite-regularity engine at `g`/`gi`.
  obtain ⟨B, hBnn, hBd⟩ :=
    cutoffResidual_global_gaussianWide_bound_C2
      g gi
      (heatParametrix 0 Θ u t)
      (fun x => deriv (fun s => heatParametrix 0 Θ u s x) t)
      a b t ha hab ht hH2 hgisymm
      C hCnn hEnear Mann hMann0 hHann hDHann
      Kg Kc1 Kc2 hKg hKc1 hKc2 hgibd hDchi hLapChi
  exact ⟨a, b, ha, hab, B, hBnn, fun v => hBd v⟩

/-- **★ J4-83 (S4) — the per-base-point cutoff residual bound over `uniformFlowExp`, via the packet.**

Instantiation of the construction-independent producer `cutoffResidual_bound_from_packet` at the
uniform-flow pullback metric `g̃ = uniformFlowPullbackMetric g gi hC hK q` and its genuine inverse
`g̃⁻¹ = uniformFlowPullbackMetricInv g gi hC hK q`, for a base point `q ∈ K`.  This demonstrates that the
abstract packet composes over the `uniformFlowExp` objects, and it draws two metric-side packet fields
DIRECTLY from the landed uniform machinery:

  * `hsymm` (`g̃` symmetric ∀y)      ← `uniformFlowPullbackMetric_symm` (uniform, needs only `hgsymm`);
  * `hdev`  (`g̃⁻¹ = δ + O(r²)`, constant `M`) ← J4-82 `uniformFlowPullbackMetricInv_dev` (the weld
      transfer of the `expMap`-side Taylor bound — this wires the uniform inverse-deviation into the
      residual).

The remaining packet fields are CARRIED as GENUINE q-centered geometric/regularity inputs (the same
residue the `expPullback` producer carries): the RNC near-jet at `0` (`C²` regularity of `g̃`/`g̃⁻¹`/`Γ̃`,
`C³` cofactor, value/first-jet gauge `g̃(0)=δ`/`∂g̃(0)=0`/`Γ̃(0)=0`/`g̃⁻¹(0)=δ`/`∂g̃⁻¹(0)=0`, cyclic
gauge, van-Vleck `∂²w₀=−⅓Ric+…`), the global nondegeneracy `hinv`/`hgisymm`, and the annulus data
`hgi_ann`/`hLapChi_ann` + `hw0smooth`.  NO `expRho` in the statement.  NOT `a₁ = R/6`. -/
theorem cutoffResidual_uniformFlow_hEboundW
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg_reg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (q : Point n) (hq : q ∈ K)
    (hframe : ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    -- CARRIED near-jet packet over `g̃`/`g̃⁻¹`.
    (hgjet : ∀ a b, ContDiffAt ℝ 2
      (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) 0)
    (hgiC : ∀ i j, ContDiffAt ℝ 2
      (fun y => uniformFlowPullbackMetricInv g gi hC hK q y i j) 0)
    (hCd : ∀ a b c, ContDiffAt ℝ 2
      (fun y => christoffel (uniformFlowPullbackMetric g gi hC hK q)
        (uniformFlowPullbackMetricInv g gi hC hK q) a b c y) 0)
    (hw0 : ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0)
    (hg0 : ∀ i j, uniformFlowPullbackMetric g gi hC hK q 0 i j
        = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, uniformFlowPullbackMetricInv g gi hC hK q (0 : Point n) i j
        = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => uniformFlowPullbackMetricInv g gi hC hK q y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel (uniformFlowPullbackMetric g gi hC hK q)
        (uniformFlowPullbackMetricInv g gi hC hK q) k i j (0 : Point n) = 0)
    (hinv : ∀ y i j, (∑ σ, uniformFlowPullbackMetricInv g gi hC hK q y i σ
        * uniformFlowPullbackMetric g gi hC hK q y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c,
        pd (fun y => christoffel (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) i b c y) a 0
        + pd (fun y => christoffel (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) i c a y) b 0
        + pd (fun y => christoffel (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) i a b y) c 0 = 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hw0hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - ((1 / 3) * ricci (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel (uniformFlowPullbackMetric g gi hC hK q)
                              (uniformFlowPullbackMetricInv g gi hC hK q) a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel (uniformFlowPullbackMetric g gi hC hK q)
                              (uniformFlowPullbackMetricInv g gi hC hK q) b i i y) a 0)))
            * foldedCoeff Θ u 0 0)
    {t : ℝ} (ht : 0 < t) (W L : ℝ) (hW : 0 ≤ W)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
        (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v| ≤ L)
    -- CARRIED cutoff / annulus packet.
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hgisymm : ∀ w i j, uniformFlowPullbackMetricInv g gi hC hK q w i j
        = uniformFlowPullbackMetricInv g gi hC hK q w j i)
    (hgi_ann : ∀ (a b : ℝ), ∃ Kg : ℝ, 0 ≤ Kg ∧ ∀ (w : Point n) (i j : Fin n),
        a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |uniformFlowPullbackMetricInv g gi hC hK q w i j| ≤ Kg)
    (hLapChi_ann : ∀ (a b : ℝ), ∃ Kc2 : ℝ, 0 ≤ Kc2 ∧ ∀ w : Point n,
        a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) (radialCutoff a b) w| ≤ Kc2) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) t
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u t y) v|
        ≤ B * gaussDdimWide t v := by
  -- `hdev` (with its constant `M`) from J4-82; `hsymm` from the uniform symmetry lemma.
  obtain ⟨M, hM0, hdev⟩ :=
    uniformFlowPullbackMetricInv_dev g gi hC hK hg_reg hgsymm hinvF q hq hframe
  exact cutoffResidual_bound_from_packet
    (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q) Θ u
    hgjet hgiC hCd hw0 hg0 hgi0 hdg0 hdgi0 hΓ0
    (fun y a b => uniformFlowPullbackMetric_symm g gi hC hK hgsymm q y a b)
    hinv hgauge hw0flat hw0hessRicci
    ht M W L hM0 hW hdev hw0bd hlap
    hw0smooth hgisymm hgi_ann hLapChi_ann

end QIQTH.HeatResidualBound
