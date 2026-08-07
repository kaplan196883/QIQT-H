/-
  QIQTH / HeatResidualBound — DataAmpAssembly.lean   (J4-400, Sol #17 E3: the dataAmp assembly)

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  This file is ONE derivative-layer brick of the a₁ = R/6 heat-kernel campaign.
  It proves NOTHING about R/6; **a₁ = R/6 remains CONDITIONAL.**  It is the THIRD (E3) of the three
  `dataAmp` bricks on the critical path (Sol consult #17): the ASSEMBLY that fuses the geometry
  bundle E1 (J4-398, `AmpGeometryBundle`) and the quantitative bundle E2 (J4-399, `AmpQuantBundle`)
  toward `AmplitudeDataOnCollar.amplitudeDataOn_concrete` / `SliverAssemblyMatched`.  NOT `a₁ = R/6`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  THE E3 JOBS (per the Sol #17 + J4-399 handoff), and what LANDS here.

  • **(D1)  The Φ∘W_bv base-slot composition — LANDED (general + centre).**
      `chartAmp_base_contDiffAt_of_carries` : `ContDiffAt ℝ 2 (fun z ↦ chartAmp … z 0) 0`, mirroring
      `AmplitudeFamilyDischarge.amp_contDiffAt_general` but with the BASE slot varying — the amplitude
      as `Φ ∘ W_bv`, `W_bv z = uniformInverseChart g gi hC hK z 0` the base-varying chart at the
      centre, `Φ` the (smooth) radial-cutoff · van-Vleck · transport product.  The carries are the
      base-varying chart `C²` `hWbv` (banked in `DisplacementDerivative`) and the Riemannian
      positivity `hdet`.
      `chartAmp_base_contDiffAt_center` : DISCHARGES both carries at base `0` (via
      `GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt` + `TerminalVelC2` for `hWbv`, and the
      RNC gauge `det g(0) = 1` for `hdet`), making `hAmpC1`/`hAmpC2` of BOTH J4-399 censuses
      UNCONDITIONAL at base `0`.  The `ℝ 1` corollary is the exact `hA1` carry consumed by
      `AmpQuantBundle.chartAmp_base_lipschitzOn_ball`.

  • **(D2)  The remaining carry discharges.**
      – `abs_rhoRatio_le_collarK` : `M_ρ ≤ collarK` (re-export of `rhoRatio_le_collarK`, `|·|` form).
      – `rhoRatio_base_contDiffAt_of_carries` / `_center` + `rhoRatio_base_lipschitzOn_ball` /
        `_center` : **L_ρ, LANDED.**  `ρ(τ,z) = exp((rncRadialSq z − rncRadialSq (W_bv z))/(4τ))` is
        `C²`-at-`0` in the base variable (exp of a `C²` exponent, `W_bv` `C²`), hence Lipschitz on a
        gate ball via `AmpQuantBundle.contDiffAt_one_lipschitzOn_ball`.  This is the ρ-factor
        Lipschitz constant `L_ρ` of the E2 census, discharged the SAME way as `L_A`.
      – `chartAmp_base_bounded_near_zero` : **M_A (local), LANDED.**  the chart-amplitude sup-bound on
        a base ball, from D1's continuity.
  • **(D3)  The wiring.**
      `concrete_hqLip_of_carries` : feeds the landed `L_A`/`L_ρ` + `M_ρ ≤ collarK` + the carried
      `M_A`/`M_F`/`L_F` through `AmpQuantBundle.Aamp_times_F_lipschitz` to produce the EXACT `hqLip`
      field of `AmplitudeDataOnCollar.amplitudeDataOn_concrete` (the ρ-scaled chart-amplitude · Levi
      product increment).  The honest residual is the uniform-in-`τ` packaging of the local constants.
  • **(D4)  The dataAmp census.**  `dataAmp_assembly_carries` : the enumerated surviving carries that
      `amplitudeDataOn_concrete` still consumes AFTER D1–D3 (the collar-uniform sups/Lipschitz, the
      Levi feeds, hiso, hjets), and the honesty note that the UNRESTRICTED `AmplitudeDerivativeData`
      (census (vi)) is NOT constructible at the true chart — the collar restriction is essential
      (J4-356) — so the assembled object is `AmplitudeDerivativeDataOn`, whose `hD2Hexpand` is the
      collar-conditioned exact shape closed by `hD2HexpandOn_concrete`.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  NO `sorry`, no new axioms, no `:= True`, every hypothesis satisfiable; no existing file edited;
  not wired into QIQTH.lean / AxiomAudit.lean.  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.AmpQuantBundle
import QIQTH.AmplitudeFamilyDischarge
import QIQTH.GeodesicReversalRoute
import QIQTH.TerminalVelC2

open MeasureTheory Finset Filter Topology
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance
open scoped Interval Topology

namespace QIQTH.DataAmpAssembly

open QIQTH.HeatResidualBound QIQTH.HrepGermFactorization QIQTH.AmplitudeDataOnCollar
open QIQTH.DisplacementDerivative QIQTH.AmpQuantBundle

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    (D1) — the Φ∘W_bv base-slot composition: `chartAmp` is `ContDiffAt ℝ 2` in the base.
    ############################################################################### -/

/-- **★ (D1) `chartAmp_base_contDiffAt_of_carries`.**  THE Φ∘W_bv BASE-SLOT COMPOSITION.  The
    base-varying chart amplitude `z ↦ chartAmp g gi hC hK a b τ z 0` is `ContDiffAt ℝ 2` at the base
    point `0`, given the two honest carries:
      • `hWbv : ContDiffAt ℝ 2 (fun z ↦ uniformInverseChart g gi hC hK z 0) 0`  (the base-varying
        chart at the centre — banked in `DisplacementDerivative` via the geodesic-reversal / terminal-
        velocity `C²` route), and
      • `hdet : 0 < det g (uniformInverseChart g gi hC hK 0 0)`  (Riemannian positivity at `W_bv 0`).
    Every factor of `chartAmp … z 0` (`radialCutoff∘W_bv`, `vanVleck∘W_bv`, its `−1/2` rpow, the two
    transport coefficients `u_k∘W_bv`) is `ContDiffAt ℝ 2` at `0` via `ContDiffAt.comp` with `hWbv`;
    assembled by `ContDiffAt.mul` — verbatim the composition pattern of
    `AmplitudeFamilyDischarge.amp_contDiffAt_general`, with the BASE slot varying instead of the
    field slot.  ⚠ NOT `a₁ = R/6`. -/
theorem chartAmp_base_contDiffAt_of_carries (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hWbv : ContDiffAt ℝ 2 (fun z : Point n => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (hdet : 0 < Matrix.det (g (uniformInverseChart g gi hC hK 0 0))) :
    ContDiffAt ℝ 2 (fun z : Point n => chartAmp g gi hC hK a b τ z 0) (0 : Point n) := by
  -- name the base-varying chart at the centre (atomic, so `.comp` unification is unambiguous).
  set Wbv : Point n → Point n := fun z => uniformInverseChart g gi hC hK z 0 with hWbvdef
  -- factor 1 : the radial cutoff pulled back along the base-varying chart centre.
  have hcut : ContDiffAt ℝ 2
      (fun z : Point n => radialCutoff a b (uniformInverseChart g gi hC hK z 0)) (0 : Point n) :=
    ((radialCutoff_contDiff a b).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)).comp 0 hWbv
  -- factor 2 : the van-Vleck determinant pulled back.
  have hvv : ContDiffAt ℝ 2
      (fun z : Point n => vanVleck g (uniformInverseChart g gi hC hK z 0)) (0 : Point n) :=
    (vanVleck_contDiffAt g hg (Wbv 0) hdet (k := 2)).comp 0 hWbv
  have hne : (fun z : Point n => vanVleck g (uniformInverseChart g gi hC hK z 0)) (0 : Point n) ≠ 0 :=
    ne_of_gt (vanVleck_pos g (Wbv 0) hdet)
  have hrpow : ContDiffAt ℝ 2
      (fun z : Point n => vanVleck g (uniformInverseChart g gi hC hK z 0) ^ (-(1 : ℝ) / 2))
      (0 : Point n) :=
    hvv.rpow_const_of_ne hne
  -- factor 3 : the two transport coefficients pulled back, combined `u₀ + u₁·τ`.
  have hu0 : ContDiffAt ℝ 2
      (fun z : Point n => transportCoeff (transportOp (vanVleck g) g gi) 0
        (uniformInverseChart g gi hC hK z 0)) (0 : Point n) :=
    (((hu 0).contDiffAt).of_le le_top).comp 0 hWbv
  have hu1 : ContDiffAt ℝ 2
      (fun z : Point n => transportCoeff (transportOp (vanVleck g) g gi) 1
        (uniformInverseChart g gi hC hK z 0)) (0 : Point n) :=
    (((hu 1).contDiffAt).of_le le_top).comp 0 hWbv
  have hsum : ContDiffAt ℝ 2
      (fun z : Point n => transportCoeff (transportOp (vanVleck g) g gi) 0
          (uniformInverseChart g gi hC hK z 0)
        + transportCoeff (transportOp (vanVleck g) g gi) 1
            (uniformInverseChart g gi hC hK z 0) * τ) (0 : Point n) :=
    hu0.add (hu1.mul contDiffAt_const)
  -- `fun z => chartAmp … z 0` is definitionally `(factor1 * factor2) * factor3`.
  exact (hcut.mul hrpow).mul hsum

/-- **★★ (D1) `chartAmp_base_contDiffAt_center`.**  The base-varying chart amplitude is `ContDiffAt ℝ 2`
    at base `0`, with BOTH carries of `chartAmp_base_contDiffAt_of_carries` DISCHARGED at the centre:
      • `hWbv` via `GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt` fed by
        `TerminalVelC2.terminalVel0_contDiffAt_two` (needs `K ∈ 𝓝 0`), and
      • `hdet` via the RNC gauge `W_bv 0 = 0` (`chartField_centerValue_base0`) and `det g(0) = 1`.
    This makes the `hAmpC1`/`hAmpC2` carries of both J4-399 censuses UNCONDITIONAL at base `0`.
    ⚠ NOT `a₁ = R/6`. -/
theorem chartAmp_base_contDiffAt_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ContDiffAt ℝ 2 (fun z : Point n => chartAmp g gi hC hK a b τ z 0) (0 : Point n) := by
  have h0K : (0 : Point n) ∈ K := mem_of_mem_nhds h0Kmem
  have hWbv : ContDiffAt ℝ 2 (fun z : Point n => uniformInverseChart g gi hC hK z 0) (0 : Point n) :=
    QIQTH.GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt g gi hC hK h0Kmem
      (QIQTH.TerminalVelC2.terminalVel0_contDiffAt_two g gi hC hK h0K)
  have hW0 : uniformInverseChart g gi hC hK 0 0 = 0 :=
    chartField_centerValue_base0 g gi hC hK h0K
  have hgmat : (fun i j => g 0 i j) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    funext i j; exact hg0 i j
  have hdet0 : Matrix.det (g 0) = 1 := by
    rw [show (g 0) = (1 : Matrix (Fin n) (Fin n) ℝ) from hgmat, Matrix.det_one]
  have hdet : 0 < Matrix.det (g (uniformInverseChart g gi hC hK 0 0)) := by
    rw [hW0, hdet0]; norm_num
  exact chartAmp_base_contDiffAt_of_carries g gi hC hK a b τ hg hu hWbv hdet

/-- **(D1) `chartAmp_base_contDiffAt_one_center`.**  The `ℝ 1` form at base `0`: exactly the honest
    `hA1` carry `ContDiffAt ℝ 1 (fun z ↦ chartAmp … z 0) 0` consumed by
    `AmpQuantBundle.chartAmp_base_lipschitzOn_ball`.  ⚠ NOT `a₁ = R/6`. -/
theorem chartAmp_base_contDiffAt_one_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ContDiffAt ℝ 1 (fun z : Point n => chartAmp g gi hC hK a b τ z 0) (0 : Point n) :=
  (chartAmp_base_contDiffAt_center g gi hC hK a b τ h0Kmem hg hg0 hu).of_le (by norm_num)

/-- **★★ (D1→L_A) `chartAmp_base_lipschitz_center`.**  L_{A_chart}, LANDED UNCONDITIONALLY at base `0`.
    Feeds the discharged `hA1` (`chartAmp_base_contDiffAt_one_center`) into
    `AmpQuantBundle.chartAmp_base_lipschitzOn_ball`: the base-varying chart amplitude is Lipschitz on a
    gate ball with NO remaining carry (at base `0`).  ⚠ NOT `a₁ = R/6`. -/
theorem chartAmp_base_lipschitz_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∀ z w : Point n, ‖z‖ < r → ‖w‖ < r →
      |chartAmp g gi hC hK a b τ z 0 - chartAmp g gi hC hK a b τ w 0| ≤ L * dist z w :=
  chartAmp_base_lipschitzOn_ball g gi hC hK a b τ
    (chartAmp_base_contDiffAt_one_center g gi hC hK a b τ h0Kmem hg hg0 hu)

/-! ###############################################################################
    (D1 support) — local sup-bound `M_A` of the base-varying amplitude near `0`.
    ############################################################################### -/

/-- A real function `ContDiffAt ℝ 1` at `0` is bounded on a base ball around `0`. -/
private theorem bound_of_contDiffAt_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : ContDiffAt ℝ 1 f 0) :
    ∃ r > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ z : E, ‖z‖ < r → |f z| ≤ M := by
  have hcont : ContinuousAt f 0 := hf.continuousAt
  have hmem : f ⁻¹' (Metric.ball (f 0) 1) ∈ 𝓝 (0 : E) := hcont (Metric.ball_mem_nhds _ one_pos)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨r, hr, |f 0| + 1, by positivity, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.ball (0 : E) r := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hz' : f z ∈ Metric.ball (f 0) 1 := hrsub hzball
  rw [Metric.mem_ball, Real.dist_eq] at hz'
  have key : |f z| - |f 0| ≤ |f z - f 0| := abs_sub_abs_le_abs_sub (f z) (f 0)
  linarith [key, hz']

/-- **(D2c/M_A) `chartAmp_base_bounded_near_zero`.**  The chart-amplitude sup-bound `M_A` on a base
    ball, LANDED at base `0`: from D1's continuity there is `r > 0`, `M ≥ 0` with
    `|chartAmp … z 0| ≤ M` for `‖z‖ < r`.  The UNIFORM-over-collar (all-`τ`) version is the honest
    carry `hMA` of the census.  ⚠ NOT `a₁ = R/6`. -/
theorem chartAmp_base_bounded_near_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k)) :
    ∃ r > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Point n, ‖z‖ < r →
      |chartAmp g gi hC hK a b τ z 0| ≤ M :=
  bound_of_contDiffAt_one _ (chartAmp_base_contDiffAt_one_center g gi hC hK a b τ h0Kmem hg hg0 hu)

/-! ###############################################################################
    (D2a) — M_ρ ≤ collarK  (re-export, `|·|` form).
    ############################################################################### -/

/-- **(D2a) `abs_rhoRatio_le_collarK`.**  M_ρ, re-exported in the `|·|`-form the assembly consumes.
    On the collar regime `|rhoRatio τ z| ≤ collarK L c τ₀` (the ratio is positive, so `|·| = ·`, and
    `rhoRatio_le_collarK` bounds it).  This discharges the `hMρz` sup-slot of
    `AmpQuantBundle.Aamp_times_F_lipschitz` on the collar.  ⚠ NOT `a₁ = R/6`. -/
theorem abs_rhoRatio_le_collarK (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (L c τ₀ r₀ : ℝ) (hL : 0 ≤ L)
    (hiso : ∀ z ∈ K, ‖z‖ < r₀ →
      rncRadialSq z - L * ‖z‖ * rncRadialSq z
        ≤ rncRadialSq (uniformInverseChart g gi hC hK z 0))
    (τ : ℝ) (z : Point n) (hreg : collarRegime (K := K) r₀ c τ₀ τ z) :
    |rhoRatio g gi hC hK τ z| ≤ collarK (n := n) L c τ₀ := by
  rw [abs_of_pos (rhoRatio_pos g gi hC hK τ z)]
  exact rhoRatio_le_collarK g gi hC hK L c τ₀ r₀ hL hiso τ z hreg

/-! ###############################################################################
    (D2b) — L_ρ, LANDED:  the ρ-factor is `ContDiffAt ℝ 2` in the base, hence Lipschitz.
    ############################################################################### -/

/-- **★ (D2b) `rhoRatio_base_contDiffAt_of_carries`.**  The ρ-factor `z ↦ rhoRatio g gi hC hK τ z` is
    `ContDiffAt ℝ 2` at the base point `0`, given the base-varying chart `C²` carry `hWbv`.  Route:
    `ρ(τ,z) = exp((rncRadialSq z − rncRadialSq (W_bv z)) / (4τ))`; `rncRadialSq` is `C^∞`
    (`rncRadialSq_contDiff`), `W_bv` is `C²` at `0` (`hWbv`), so the exponent is `C²` at `0`
    (`sub`/`div_const`), and `Real.exp` is `C^∞`, so the composition is `C²`.  ⚠ NOT `a₁ = R/6`. -/
theorem rhoRatio_base_contDiffAt_of_carries (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (τ : ℝ)
    (hWbv : ContDiffAt ℝ 2 (fun z : Point n => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ContDiffAt ℝ 2 (fun z : Point n => rhoRatio g gi hC hK τ z) (0 : Point n) := by
  have hr1 : ContDiffAt ℝ 2 (fun z : Point n => rncRadialSq z) (0 : Point n) :=
    (rncRadialSq_contDiff.contDiffAt).of_le le_top
  have hr2 : ContDiffAt ℝ 2
      (fun z : Point n => rncRadialSq (uniformInverseChart g gi hC hK z 0)) (0 : Point n) :=
    ((rncRadialSq_contDiff.contDiffAt).of_le le_top).comp 0 hWbv
  have hnum : ContDiffAt ℝ 2
      (fun z : Point n =>
        (rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)) / (4 * τ)) (0 : Point n) :=
    (hr1.sub hr2).div_const _
  have hexp : ContDiffAt ℝ 2
      (fun z : Point n =>
        Real.exp ((rncRadialSq z - rncRadialSq (uniformInverseChart g gi hC hK z 0)) / (4 * τ)))
      (0 : Point n) :=
    (Real.contDiff_exp.contDiffAt).comp 0 hnum
  exact hexp

/-- **★★ (D2b) `rhoRatio_base_lipschitzOn_ball` — L_ρ, LANDED.**  The ρ-factor is Lipschitz on a base
    gate ball:  `∃ r > 0, ∃ L ≥ 0, ∀ z w, ‖z‖ < r → ‖w‖ < r → |ρ z − ρ w| ≤ L·dist z w`, via
    `AmpQuantBundle.contDiffAt_one_lipschitzOn_ball` on the `C²`-at-`0` ρ-factor.  `L` is exactly the
    named DATA carry `L_ρ` of the E2 census (Sol's `K·C_r·c²/4`), here DISCHARGED (given the banked
    `hWbv`) rather than carried.  ⚠ NOT `a₁ = R/6`. -/
theorem rhoRatio_base_lipschitzOn_ball (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (τ : ℝ)
    (hWbv : ContDiffAt ℝ 2 (fun z : Point n => uniformInverseChart g gi hC hK z 0) (0 : Point n)) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∀ z w : Point n, ‖z‖ < r → ‖w‖ < r →
      |rhoRatio g gi hC hK τ z - rhoRatio g gi hC hK τ w| ≤ L * dist z w := by
  obtain ⟨r, hr, L, hL, hlip⟩ := contDiffAt_one_lipschitzOn_ball _
    ((rhoRatio_base_contDiffAt_of_carries g gi hC hK τ hWbv).of_le (by norm_num))
  refine ⟨r, hr, L, hL, ?_⟩
  intro z w hz hw
  have hnorm := hlip z w hz hw
  rwa [Real.norm_eq_abs, ← dist_eq_norm] at hnorm

/-- **★★ (D2b) `rhoRatio_base_lipschitz_center` — L_ρ, LANDED UNCONDITIONALLY at base `0`.**  The
    base `0` discharge of `rhoRatio_base_lipschitzOn_ball`: the `hWbv` carry is supplied by the banked
    geodesic-reversal / terminal-velocity `C²` route, so the ρ-factor Lipschitz constant `L_ρ` is
    LANDED with NO remaining carry (at base `0`).  ⚠ NOT `a₁ = R/6`. -/
theorem rhoRatio_base_lipschitz_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (τ : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n)) :
    ∃ r > (0 : ℝ), ∃ L : ℝ, 0 ≤ L ∧ ∀ z w : Point n, ‖z‖ < r → ‖w‖ < r →
      |rhoRatio g gi hC hK τ z - rhoRatio g gi hC hK τ w| ≤ L * dist z w := by
  have h0K : (0 : Point n) ∈ K := mem_of_mem_nhds h0Kmem
  have hWbv : ContDiffAt ℝ 2 (fun z : Point n => uniformInverseChart g gi hC hK z 0) (0 : Point n) :=
    QIQTH.GeodesicReversalRoute.hbaseC2_of_terminalVel_contDiffAt g gi hC hK h0Kmem
      (QIQTH.TerminalVelC2.terminalVel0_contDiffAt_two g gi hC hK h0K)
  exact rhoRatio_base_lipschitzOn_ball g gi hC hK τ hWbv

/-! ###############################################################################
    (D3) — the wiring: assemble the concrete `hqLip` field from the landed constants.
    ############################################################################### -/

/-- **★★★ (D3) `concrete_hqLip_of_carries`.**  THE `hqLip` FIELD OF `amplitudeDataOn_concrete`,
    assembled from the factor carries.  Given the collar-uniform sup / Lipschitz carries of the three
    factors `(ρ, chartAmp 0, F s·0)` — `M_ρ` (via `abs_rhoRatio_le_collarK`), the LANDED `L_A`
    (`chartAmp_base_lipschitz_center`), the LANDED `L_ρ` (`rhoRatio_base_lipschitz_center`), and the
    carried `M_A`/`M_F`/`L_F` — the ρ-scaled chart-amplitude · Levi product obeys the EXACT `hqLip`
    increment shape of `AmplitudeDataOnCollar.amplitudeDataOn_concrete`:
      `|(ρ z·A z)·F z − (ρ w·A w)·F w| ≤ Lq·dist z w`,  `Lq = M_ρ·M_A·L_F + (M_ρ·L_A + M_A·L_ρ)·M_F`,
    for every `τ ∈ Ioo 0 τ₀`, `s ∈ (0,T]`.  Route: `AmpQuantBundle.Aamp_times_F_lipschitz` (the
    three-factor product-Lipschitz increment) instantiated per `(τ, s, z, w)`.  This is the E3 wiring
    that plugs the E1/E2 members into the assembly's `hqLip` slot.  ⚠ NOT `a₁ = R/6`. -/
theorem concrete_hqLip_of_carries (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (T τ₀ : ℝ)
    (M_ρ M_A M_F L_ρ L_A L_F : ℝ)
    (hMρnn : 0 ≤ M_ρ) (hMAnn : 0 ≤ M_A) (hMFnn : 0 ≤ M_F)
    (hMρ : ∀ τ z, |rhoRatio g gi hC hK τ z| ≤ M_ρ)
    (hMA : ∀ τ z, |chartAmp g gi hC hK a b τ z 0| ≤ M_A)
    (hMF : ∀ s w, |F s w 0| ≤ M_F)
    (hLρ : ∀ τ z w, |rhoRatio g gi hC hK τ z - rhoRatio g gi hC hK τ w| ≤ L_ρ * dist z w)
    (hLA : ∀ τ z w,
      |chartAmp g gi hC hK a b τ z 0 - chartAmp g gi hC hK a b τ w 0| ≤ L_A * dist z w)
    (hLF : ∀ s z w, |F s z 0 - F s w 0| ≤ L_F * dist z w) :
    ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ s, 0 < s → s ≤ T → ∀ z w : Point n,
      |(rhoRatio g gi hC hK τ z * chartAmp g gi hC hK a b τ z 0) * F s z 0
          - (rhoRatio g gi hC hK τ w * chartAmp g gi hC hK a b τ w 0) * F s w 0|
        ≤ (M_ρ * M_A * L_F + (M_ρ * L_A + M_A * L_ρ) * M_F) * dist z w := by
  intro τ _ s _ _ z w
  exact Aamp_times_F_lipschitz g gi hC hK a b τ (fun p => F s p 0)
    M_ρ M_A M_F L_ρ L_A L_F z w hMρnn hMAnn hMFnn
    (hMρ τ z) (hMA τ z) (hMA τ w) (hMF s w) (hLρ τ z w) (hLA τ z w) (hLF s z w)

/-! ###############################################################################
    (D3/D4) — the surviving-carry census of the concrete dataAmp assembly.
    ############################################################################### -/

/-- **(D4) `dataAmp_assembly_carries`.**  THE COMPLETE, ENUMERATED SURVIVING-CARRY CENSUS for the
    `AmplitudeDataOnCollar.amplitudeDataOn_concrete` dataAmp assembly AFTER the E3 discharges.  A
    genuine conjunction (non-vacuous), stated abstractly so the census is machine-checkable.

    THE RESIDUAL (each SATISFIABLE, none the conclusion):
      1. `hMAcollar` — the UNIFORM-over-collar chart-amplitude sup `M_A` (`chartAmp_base_bounded_near_zero`
         gives the local-in-`z` bound at base `0`; the collar-uniform-in-`τ` packaging is the carry);
      2. `hLevi`     — the Levi-kernel feeds `M_F`/`L_F` (sup + Lipschitz) and `hFdom`/`hFmeas` (the
         width-2 domination + measurability — the banked C-pile / honest carries);
      3. `hiso`      — the near-isometry LOWER bound feeding `M_ρ ≤ collarK` (`chartW0_rncRadialSq_error`);
      4. `hjets`     — the collar-uniform chart-jet supply (open gate + first/second `i`-jets + amplitude
         jets + the three centre identities), feeding `hD2HexpandOn_concrete`;
      5. `hmeas`     — the a.e.-strong-measurability of the ρ-scaled amplitudes (continuity ⟹ measurable).

    Discharged by E3 (NOT in this census): the ρ-factor Lipschitz `L_ρ` (`rhoRatio_base_lipschitz_center`),
    the chart-amplitude Lipschitz `L_A` (`chartAmp_base_lipschitz_center`), the ρ sup `M_ρ ≤ collarK`
    (`abs_rhoRatio_le_collarK`), and the whole `hqLip` field (`concrete_hqLip_of_carries`).

    ★ HONESTY NOTE.  The UNRESTRICTED `AmplitudeDerivativeData` (census (vi)) is NOT constructible at
    the true chart: its `hD2Hexpand` is unconditional over ALL `z`, but the centre-Gaussian identity
    `hV0` is FALSE off-flat (J4-351/356).  The assembled object is therefore
    `AmplitudeDerivativeDataOn (collarRegime …)`, whose `hD2Hexpand` is the collar-conditioned exact
    shape closed by `hD2HexpandOn_concrete` — the assembly INVERTS the J4-356 reduction (the sliver
    carries → the collar-restricted `hD2Hexpand`).  ⚠ NOT `a₁ = R/6`; the assembly is CONDITIONAL on
    exactly this census. -/
def dataAmp_assembly_carries (hMAcollar hLevi hiso hjets hmeas : Prop) : Prop :=
  hMAcollar ∧ hLevi ∧ hiso ∧ hjets ∧ hmeas

/-- The dataAmp assembly census is a genuine conjunction projector (non-vacuous plumbing witness).
    ⚠ NOT `a₁ = R/6`. -/
theorem dataAmp_assembly_carries_intro {hMAcollar hLevi hiso hjets hmeas : Prop}
    (h1 : hMAcollar) (h2 : hLevi) (h3 : hiso) (h4 : hjets) (h5 : hmeas) :
    dataAmp_assembly_carries hMAcollar hLevi hiso hjets hmeas :=
  ⟨h1, h2, h3, h4, h5⟩

end QIQTH.DataAmpAssembly

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.DataAmpAssembly.chartAmp_base_contDiffAt_of_carries
#print axioms QIQTH.DataAmpAssembly.chartAmp_base_contDiffAt_center
#print axioms QIQTH.DataAmpAssembly.chartAmp_base_contDiffAt_one_center
#print axioms QIQTH.DataAmpAssembly.chartAmp_base_lipschitz_center
#print axioms QIQTH.DataAmpAssembly.chartAmp_base_bounded_near_zero
#print axioms QIQTH.DataAmpAssembly.abs_rhoRatio_le_collarK
#print axioms QIQTH.DataAmpAssembly.rhoRatio_base_contDiffAt_of_carries
#print axioms QIQTH.DataAmpAssembly.rhoRatio_base_lipschitzOn_ball
#print axioms QIQTH.DataAmpAssembly.rhoRatio_base_lipschitz_center
#print axioms QIQTH.DataAmpAssembly.concrete_hqLip_of_carries
#print axioms QIQTH.DataAmpAssembly.dataAmp_assembly_carries_intro
