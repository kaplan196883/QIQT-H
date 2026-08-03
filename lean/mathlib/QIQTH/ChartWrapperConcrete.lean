/-
  ChartWrapperConcrete — J4-128: the concrete chart wrapper for the L¹ Gaussian kernel-replacement
  adapter — center values DISCHARGED, near-isometry ISOLATED, boundary-wrapper reduction SCAFFOLDED.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS BRICK IS.

  `ChartGaussAdapter` (J4-127) proved the PARAMETRIC L¹ kernel-replacement adapter (`B1`
  `chartGauss_l1_sub_plain_tendsto`, `B2` `chartGauss_l1_mul_bdd_tendsto`) for an ABSTRACT chart
  `W : Point n → Point n` and active set `S`, constrained by the two near-isometry facts `hcoarse`
  (coarse lower bound) and `hasymp` (asymptotic two-sided squeeze), plus base measurability `hWmeas`.
  This file specializes that adapter to the CONCRETE chart map
      `W₀ z := uniformInverseChart g gi hC hK z 0`
  (the normal coordinate of the origin seen from base point `z`, the Gaussian argument produced by
  `AmplitudePackage.vanVleckGatedWitness_zero_factor`), and discharges what is genuinely
  dischargeable while isolating — as explicit, honest, labelled hypotheses — the ONE recognized
  geometric BLOCKER.

  ## WHAT LANDS (this file, UNCONDITIONALLY — the center-value layer, C2(i)).
    * `chartW0_zero`        — `W₀ 0 = uniformInverseChart g gi hC hK 0 0 = 0` (given `0 ∈ K`): the
        germ value of the left-inverse chart at `v = 0`, through `uniformFlowExp_zero`.
    * `chartAmp0_at_zero`   — `ũ₀ 0 = chartAmp0 … 0 = 1`: the leading amplitude center value the
        proven boundary interface (`BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`, hypothesis
        `hu₀one : u₀ 0 = 1`) demands, discharged from the DeWitt normalization
        (`radialCutoff = 1` at the centre, `Θ(0) = 1`, `u₀ ≡ 1`).
    * `chartAmp1_at_zero`   — `ũ₁ 0 = chartAmp1 … 0 = u₁(0) = transportCoeff … 1 0` (the R/6 seed).

  ## WHAT IS ISOLATED (C1 — the concrete adapter, CONDITIONAL on the labelled BLOCKER).
    * `chartGauss_concrete_sub_plain_tendsto` / `chartGauss_concrete_mul_bdd_tendsto` — B1/B2 with
        `W := W₀`, so the abstract near-isometry hypotheses become the CONCRETE chart facts
          `hcoarse₀ : ∃ c>0, ∀ z∈S, c·‖z‖² ≤ ‖W₀ z‖²`   and
          `hasymp₀  : ∀ δ∈(0,1) ∃ r>0, ∀ z∈S, ‖z‖²<r² → (1−δ)‖z‖² ≤ ‖W₀ z‖² ≤ (1+δ)‖z‖²`,
        i.e. the chart near-isometry `rncRadialSq (W₀ z) = ‖z‖² + O(‖z‖⁴)` demanded verbatim.

  ## WHAT IS SCAFFOLDED (C3 — the on-gate reduction, provable; the wrapper CARRIED).
    * `witness_mul_split_on_gate` — on the gate (`z ∈ K`, `0 ∈ S z`), the tested concrete witness
        splits EXACTLY as the plain synthetic kernel plus the adapter difference,
          `H_G·B = (G_τ(z)·(ũ₀+τũ₁))·B  +  (G_τ(W₀ z) − G_τ(z))·(ũ₀+τũ₁)·B`,
        the three-way shape the boundary wrapper consumes (plain term → the proven boundary theorem;
        adapter term → B2).  Pure algebra off the difference-reduction `witness_sub_plain` — no
        analysis, no blocker.

  ⚠ HONEST FIREWALL / THE BLOCKER (bankable intelligence, per the `AmplitudePackage` header).
    Assembling the full `boundary_chart_wrapper_concrete`
        `TendstoLocallyUniformlyOn (fun m u => ∫ z, H_G (εₘ) 0 z · B (u−εₘ) z 0) (fun u => B u 0 0)`
    from `boundary_tendstoLocallyUniformlyOn` (applied to the plain synthetic kernel `P τ z =
    G_τ(z)·(ũ₀ z + τ·ũ₁ z)`) + the B2 adapter difference requires THREE geometric inputs that live in
    the BASE POINT `z` of the concrete chart `W₀ z = uniformInverseChart … z 0` and are NOT derivable
    from the current tower (they are the recognized blocker `‖W₀ z‖ = d_g(z,0) ≠ ‖z‖` off-flat):
      (1) the chart NEAR-ISOMETRY `hcoarse₀`/`hasymp₀` (`rncRadialSq (W₀ z) = ‖z‖²+O(‖z‖⁴)`) — the
          quantitative inverse-function control of `W₀` (the tower carries only the EXP-side
          displacement `‖φ_q v − q − v‖ ≤ C_D‖v‖²`, `NearIsometryBudget`, not the inverse side);
      (2) BASE-POINT continuity + measurability of `z ↦ chartAmp0/chartAmp1 z` and of
          `z ↦ gaussDdim τ (W₀ z)` (the `.choose`-built chart carries no base-point regularity);
      (3) a uniform gate-ball containment `∃ ρ>0, ball 0 ρ ⊆ {z : 0 ∈ S z}` (so the off-gate
          discrepancy `∫_{gateᶜ} P·B` is a Gaussian tail → 0).
    Each is a GENUINE geometric fact of the honest chart (satisfiable, non-vacuous, never the goal);
    each is exactly the geometric step the campaign must discharge to convert `hAnear` for `H_G`.  The
    center-value layer (C2(i)), the concrete adapter specialization (C1), and the on-gate reduction
    (C3 scaffold) land here; the full wrapper is CARRIED pending (1)–(3).
    NO `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  Reusable BRICK;
    NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartGaussAdapter
import QIQTH.UniformChartRadius
import QIQTH.NearIsometryBudget

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### C2(i) — the center values of the concrete chart amplitude. -/

/-- **`chartW0_zero` — the concrete chart fixes the origin.**  At base point `q = 0 ∈ K`, the
    K-uniform inverse chart maps the origin to the origin: `uniformInverseChart g gi hC hK 0 0 = 0`.
    This is the germ value of the left-inverse chart at `v = 0`, read through
    `uniformFlowExp g gi hC hK 0 0 = 0` (`uniformFlowExp_zero`). -/
theorem chartW0_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K) :
    uniformInverseChart g gi hC hK 0 0 = 0 := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨hgermC2, _⟩ := hspec 0 h0K
  obtain ⟨hgerm, _⟩ := hgermC2 0 (by rw [norm_zero]; exact hδ₀)
  have h := hgerm.eq_of_nhds
  simp only [uniformFlowExp_zero g gi hC hK 0 h0K] at h
  exact h

/-- **★ C2(i) — `chartAmp0_at_zero`: `ũ₀ 0 = 1`.**  The `τ`-free leading amplitude of the concrete
    van-Vleck witness has center value `1`, exactly the `hu₀one : u₀ 0 = 1` input of the proven
    boundary interface `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`.  Chain: `W₀ 0 = 0`
    (`chartW0_zero`) sends every factor to the centre, where `radialCutoff a b 0 = 1`
    (`radialCutoff_eq_one`, `rncRadialSq 0 = 0 ≤ a²`), `Θ(0)^{−1/2} = 1^{−1/2} = 1` (`vanVleck_zero`,
    given `det g(0) = 1`), and `u₀(0) = 1` (`transportCoeff_zero`, `u₀ ≡ 1`). -/
theorem chartAmp0_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1) :
    chartAmp0 g gi hC hK a b (0 : Point n) = 1 := by
  have hW : uniformInverseChart g gi hC hK 0 0 = 0 := chartW0_zero g gi hC hK h0K
  simp only [chartAmp0, hW]
  rw [radialCutoff_eq_one ha hab (by rw [rncRadialSq_zero]; positivity),
    vanVleck_zero g hgdet0]
  rw [transportCoeff_zero]
  simp [Real.one_rpow]

/-- **C2(i) — `chartAmp1_at_zero`: `ũ₁ 0 = u₁(0)`.**  The `τ`-linear amplitude of the concrete
    van-Vleck witness has center value the raw first DeWitt coefficient
    `transportCoeff (transportOp (vanVleck g) g gi) 1 0` (the `R/6` seed): `W₀ 0 = 0` sends the outer
    `radialCutoff·Θ^{−1/2}` factors to `1·1`, leaving `u₁(0)`. -/
theorem chartAmp1_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0K : (0 : Point n) ∈ K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1) :
    chartAmp1 g gi hC hK a b (0 : Point n)
      = transportCoeff (transportOp (vanVleck g) g gi) 1 0 := by
  have hW : uniformInverseChart g gi hC hK 0 0 = 0 := chartW0_zero g gi hC hK h0K
  simp only [chartAmp1, hW]
  rw [radialCutoff_eq_one ha hab (by rw [rncRadialSq_zero]; positivity),
    vanVleck_zero g hgdet0]
  simp [Real.one_rpow]

/-! ### C1 — the concrete chart specialization of the L¹ kernel-replacement adapter.

    B1/B2 (`ChartGaussAdapter`) are PARAMETRIC in `W`.  Here `W := W₀ = fun z => uniformInverseChart
    g gi hC hK z 0` is the concrete Gaussian argument, so the abstract near-isometry hypotheses become
    the CONCRETE chart near-isometry facts, isolated verbatim as the labelled inputs `hcoarse₀`,
    `hasymp₀`, `hWmeas₀` (each a genuine fact of the honest inverse chart — the BLOCKER `rncRadialSq
    (W₀ z) = ‖z‖² + O(‖z‖⁴)`). -/

/-- **★ C1 — the concrete L¹ kernel replacement.**  With the Gaussian argument `W₀ z =
    uniformInverseChart g gi hC hK z 0`, under the CONCRETE chart near-isometry (`hcoarse₀` coarse
    lower bound, `hasymp₀` two-sided squeeze) and base measurability `hWmeas₀`, the chart-image
    Gaussian and the plain Gaussian are L¹-close as `τ → 0⁺`.  Direct specialization of
    `chartGauss_l1_sub_plain_tendsto` (B1). -/
theorem chartGauss_concrete_sub_plain_tendsto (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (S : Set (Point n)) (hS : MeasurableSet S)
    (hWmeas₀ : ∀ τ : ℝ, AEStronglyMeasurable
      (fun z : Point n => gaussDdim τ (uniformInverseChart g gi hC hK z 0)) (volume.restrict S))
    (hcoarse₀ : ∃ c > 0, ∀ z ∈ S,
      c * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (hasymp₀ : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ r > 0, ∀ z ∈ S, rncRadialSq z < r ^ 2 →
        (1 - δ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)
        ∧ rncRadialSq (uniformInverseChart g gi hC hK z 0) ≤ (1 + δ) * rncRadialSq z) :
    Tendsto (fun τ => ∫ z in S,
        |gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z|)
      (𝓝[>] (0:ℝ)) (𝓝 0) :=
  chartGauss_l1_sub_plain_tendsto S hS (fun z => uniformInverseChart g gi hC hK z 0)
    hWmeas₀ hcoarse₀ hasymp₀

/-- **★ C1 — the concrete bounded-multiplier replacement.**  The concrete L¹ kernel difference tested
    against any eventually-uniformly-bounded family `F τ` still vanishes as `τ → 0⁺` — the multiplier
    shape produced by `witness_sub_plain` (`F τ z = (ũ₀+τũ₁)·B(u−τ) z 0`).  Direct specialization of
    `chartGauss_l1_mul_bdd_tendsto` (B2). -/
theorem chartGauss_concrete_mul_bdd_tendsto (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (S : Set (Point n)) (hS : MeasurableSet S)
    (hWmeas₀ : ∀ τ : ℝ, AEStronglyMeasurable
      (fun z : Point n => gaussDdim τ (uniformInverseChart g gi hC hK z 0)) (volume.restrict S))
    (hcoarse₀ : ∃ c > 0, ∀ z ∈ S,
      c * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (hasymp₀ : ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ r > 0, ∀ z ∈ S, rncRadialSq z < r ^ 2 →
        (1 - δ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0)
        ∧ rncRadialSq (uniformInverseChart g gi hC hK z 0) ≤ (1 + δ) * rncRadialSq z)
    (F : ℝ → Point n → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hFmeas : ∀ τ : ℝ, AEStronglyMeasurable (fun z : Point n => F τ z) (volume.restrict S))
    (hFbd : ∀ᶠ τ in 𝓝[>] (0:ℝ), ∀ z ∈ S, |F τ z| ≤ M) :
    Tendsto (fun τ => ∫ z in S,
        (gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z) * F τ z)
      (𝓝[>] (0:ℝ)) (𝓝 0) :=
  chartGauss_l1_mul_bdd_tendsto S hS (fun z => uniformInverseChart g gi hC hK z 0)
    hWmeas₀ hcoarse₀ hasymp₀ F M hM hFmeas hFbd

/-! ### C3 — the on-gate reduction scaffold for the boundary wrapper.

    The full `boundary_chart_wrapper_concrete` is CARRIED (see the header BLOCKER (1)–(3)).  What is
    provable here — the ALGEBRAIC content the wrapper is assembled from — is the three-way split of the
    tested concrete witness on the gate. -/

/-- **★ C3 (scaffold) — `witness_mul_split_on_gate`.**  On the gate (`z ∈ K`, `0 ∈ S z`) the tested
    concrete witness splits EXACTLY into the tested PLAIN synthetic kernel `P τ z = G_τ(z)·(ũ₀+τũ₁)`
    (whose `hAnear` shape the proven `boundary_tendstoLocallyUniformlyOn` consumes verbatim with
    `u₀ := chartAmp0`, `u₁ := chartAmp1`) plus the tested ADAPTER difference `(G_τ(W₀ z) − G_τ(z))·
    (ũ₀+τũ₁)` (which B2 / `chartGauss_concrete_mul_bdd_tendsto` sends to `0`).  This is the exact
    integrand-level shape the boundary wrapper is assembled from.  Pure algebra off `witness_sub_plain`
    — no analysis, no blocker.  Holds for an arbitrary tested factor `Bz` (`= B (u−τ) z 0`). -/
theorem witness_mul_split_on_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (τ : ℝ) {z : Point n} (hz : z ∈ K) (h0 : (0 : Point n) ∈ S z) (Bz : ℝ) :
    vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * Bz
      = (gaussDdim τ z * (chartAmp0 g gi hC hK a b z + τ * chartAmp1 g gi hC hK a b z)) * Bz
        + ((gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z)
            * (chartAmp0 g gi hC hK a b z + τ * chartAmp1 g gi hC hK a b z)) * Bz := by
  have hsub := witness_sub_plain g gi hC hK S a b τ hz h0
  have hval : vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z
      = gaussDdim τ z * (chartAmp0 g gi hC hK a b z + τ * chartAmp1 g gi hC hK a b z)
        + (gaussDdim τ (uniformInverseChart g gi hC hK z 0) - gaussDdim τ z)
          * (chartAmp0 g gi hC hK a b z + τ * chartAmp1 g gi hC hK a b z) := by
    linarith [hsub]
  rw [hval]; ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.chartW0_zero
#print axioms QIQTH.HeatResidualBound.chartAmp0_at_zero
#print axioms QIQTH.HeatResidualBound.chartAmp1_at_zero
#print axioms QIQTH.HeatResidualBound.chartGauss_concrete_sub_plain_tendsto
#print axioms QIQTH.HeatResidualBound.chartGauss_concrete_mul_bdd_tendsto
#print axioms QIQTH.HeatResidualBound.witness_mul_split_on_gate
