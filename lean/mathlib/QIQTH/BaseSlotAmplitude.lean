/-
  BaseSlotAmplitude — J4-276: the BASE-SLOT amplitude facts for the fixed-`f` chart-image
  approximate identity (`QIQTH.FixedFChartImageAI.chartImage_approx_identity_of_amp`, J4-275).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the W1 wall of the a₁ = R/6 campaign).  The J4-275 plug carries a Layer-C moving-integrand
  trio (`hmeas`/`hbound`/`hlocal`) for
      `g τ w := chartFieldAmp … τ (V w) 0 · f (V w) / |(f' (V w)).det|`.
  The τ-uniform bound (`hbound`) and the joint `(τ,w) → (0⁺,0)` limit (`hlocal`) reduce to BASE-SLOT
  amplitude facts about `z ↦ chartFieldAmp … τ z 0` (BASE `z` varying, field slot pinned at `0`),
  jointly in `τ`.  The ENTIRE banked amplitude bank (`AmplitudeFamilyDischarge.amp_bound_*`,
  `amp_contDiffAt_*`) is FIELD-slot (`p ↦ chartFieldAmp … z p` at fixed base `z`), so the base-slot
  facts were NOT banked (obstruction (A) of the J4-276 mission).

  ── OBSTRUCTION (A) — THE BASE-SLOT AMPLITUDE WALL, resolved here by route (iii) [DIRECT].
  Read off the definition (`QIQTH.HeatResidualBound.chartFieldAmp`):
      `chartFieldAmp g gi hC hK a b τ z x'`
        `= radialCutoff a b (W z x')`
        `  · (vanVleck g (W z x') ^ (-½) · (u₀ (W z x') + u₁ (W z x') · τ))`,
  with `W z x' := uniformInverseChart g gi hC hK z x'` and `u_k := transportCoeff (transportOp …) k`.
  At the FIELD centre `x' = 0` the base-slot value
      `chartFieldAmp … τ z 0 = radialCutoff a b (Wbv z) · (vanVleck g (Wbv z) ^ (-½) · (u₀(Wbv z)+u₁(Wbv z)·τ))`
  runs entirely through the BASE-VARYING chart `Wbv z := uniformInverseChart g gi hC hK z 0`.  The
  amplitude is therefore MANIFESTLY continuous in the base through banked ingredient continuities —
  `radialCutoff_contDiff`, `vanVleck_continuous` (+ `vanVleck_ne_zero` for the `^(-½)` `rpow`), and
  `huc_discharged` for the transport coefficients — PROVIDED `Wbv` is continuous in the base.  And
  `Wbv` continuity in the base is EXACTLY the M1 slot of the J4-274 base-varying CoV bundle
  (`baseVaryingIFTPackage_unconditional` gives `HasFDerivWithinAt Wbv (f' z) (ball 0 ρ) z`, hence
  `ContinuousOn Wbv (ball 0 ρ)`).  This is the same base-varying obstruction the CoV bundle solved for
  the GAUSSIAN argument, now used for the AMPLITUDE argument.

  ── WHAT LANDS HERE (honest composition; NO amplitude-regularity carry beyond the geometry).
    • `baseSlotAmp_continuousOn` — ★ the JOINT `(τ, z)` continuity of the base-slot amplitude on
        `s ×ˢ U`, CONDITIONAL only on `ContinuousOn Wbv U` (route (iii)); each factor composes the
        banked ingredient continuities with `Wbv ∘ snd`.
    • `baseSlotAmp_bound` — ★★ the τ-uniform sup-bound: from the standing geometry `(hC, hK, K ∈ 𝓝 0)`
        plus `{hg, hgi, hgpos}`, there EXIST a base radius `ρ` and a constant `CA` such that
        `∀ τ ∈ [0, τ₀], ∀ z ∈ closedBall 0 ρ, |chartFieldAmp … τ z 0| ≤ CA`.  Route: obtain the
        J4-274 bundle → `ContinuousOn Wbv (ball 0 ρ_b)` → joint continuity on the COMPACT
        `[0,τ₀] ×ˢ closedBall 0 (ρ_b/2)` → `IsCompact.exists_bound_of_continuousOn`.  DISCHARGES the
        base-slot content of the `hbound` carry.
    • `baseSlotAmp_joint_limit` — ★★ the joint `(τ, z) → (0⁺, 0)` limit: from the same geometry there
        EXISTS `ρ` with
          `Tendsto (fun p => chartFieldAmp … p.1 p.2 0) ((𝓝[>]0) ×ˢ 𝓝 0) (𝓝 (chartFieldAmp … 0 0 0))`,
        the explicit limit value `A₀ = chartFieldAmp … 0 0 0`.  Route: joint continuity on
        `univ ×ˢ ball 0 ρ`, `ContinuousWithinAt` at `(0,0)`, and `(𝓝[>]0) ×ˢ 𝓝 0 ≤ 𝓝[univ×ˢball](0,0)`.
        DISCHARGES the base-slot content of the `hlocal` carry (before the `V`/`f`/`det` wrapper).
    • `baseSlotAmp_centreValue` — the explicit coincidence-limit value:
        `chartFieldAmp … 0 0 0 = radialCutoff a b 0 · (vanVleck g 0 ^ (-½) · u₀ 0)` (using
        `Wbv 0 = 0`, `chartField_centerValue_base0`).  This exhibits `A₀` as the genuine on-diagonal
        amplitude (`= 1` once the RNC normalisation `radialCutoff a b 0 = 1`, `vanVleck g 0 = 1`,
        `u₀ 0 = 1` is supplied — the labelled `hAmpCentre` normalisation, carried, NOT proved here).

  ── HONEST RESIDUAL (what is NOT done here).
    • The FULL J4-275 trio discharge (composing these base-slot facts with the CoV inverse `V`, the
      Jacobian `|det f'(V w)|`, and the sampled `f (V w)` into `hbound`/`hlocal` on `Ω`) is NOT
      performed: it needs `V`-continuity/`V w → 0`, `|det f'(V w)| → 1`, and `f` continuous at `0`
      layered on top.  These base-slot facts are the AMPLITUDE ingredient of that composition.
    • Obstruction (B) — the `hSupp` gate-vs-CoV radius mismatch (the ball/annulus split) — is a
      SEPARATE thread and is not addressed here.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  These are analytic composition
  bricks (base-slot continuity ⟹ compact bound + limit).  No `sorry` (prose only), no new axioms, no
  `:= True`, no vacuous / unsatisfiable / conclusion-in-disguise hypotheses: `{hg, hgi, hgpos}` are
  the standing Riemannian-metric regularity/positivity carries (satisfiable — the RNC metric `δ` has
  them), each strictly weaker than the continuity/bound/limit conclusions.  No existing file is edited.
-/
import Mathlib
import QIQTH.TerminalVelC2
import QIQTH.AmplitudeFamilyDischarge
import QIQTH.CoeffContWdiffLift

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open QIQTH.VanVleck QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.TerminalVelC2
open scoped Topology

namespace QIQTH.BaseSlotAmplitude

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### Route (iii) — the joint `(τ, z)` continuity of the base-slot amplitude. -/

/-- **★ `baseSlotAmp_continuousOn` — joint base-slot amplitude continuity.**  On `s ×ˢ U`, the
    base-slot amplitude `(τ, z) ↦ chartFieldAmp … τ z 0` is continuous, CONDITIONAL only on the
    base-varying chart being continuous on `U` (`hWbv`).  Every factor —
    `radialCutoff ∘ Wbv`, `(vanVleck ∘ Wbv)^(-½)` (nonvanishing branch), `u₀ ∘ Wbv`, `u₁ ∘ Wbv` — is
    the composition of a banked GLOBAL continuity (`radialCutoff_contDiff`, `vanVleck_continuous` +
    `vanVleck_ne_zero`, `huc_discharged`) with `Wbv ∘ snd`; the linear-in-`τ` transport term uses
    `fst`.  This is route (iii) of the base-slot amplitude wall.  NOT `a₁ = R/6`. -/
theorem baseSlotAmp_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b : ℝ) (s : Set ℝ) {U : Set (Point n)}
    (hWbv : ContinuousOn (fun z => uniformInverseChart g gi hC hK z 0) U) :
    ContinuousOn (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b p.1 p.2 0) (s ×ˢ U) := by
  -- `Wbv ∘ snd` continuous on the product.
  have hWsnd : ContinuousOn
      (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 0) (s ×ˢ U) :=
    hWbv.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  -- radialCutoff ∘ Wbv.
  have hcut : ContinuousOn
      (fun p : ℝ × Point n => radialCutoff a b (uniformInverseChart g gi hC hK p.2 0)) (s ×ˢ U) :=
    (radialCutoff_contDiff a b).continuous.comp_continuousOn hWsnd
  -- (vanVleck ∘ Wbv)^(-½), continuous since vanVleck never vanishes.
  have hVVc : Continuous (fun v : Point n => vanVleck g v ^ (-(1 : ℝ) / 2)) :=
    (QIQTH.CoeffContWdiffLift.vanVleck_continuous g hg hgpos).rpow_const
      (fun v => Or.inl (QIQTH.CoeffContWdiffLift.vanVleck_ne_zero g hgpos v))
  have hvv : ContinuousOn
      (fun p : ℝ × Point n =>
        vanVleck g (uniformInverseChart g gi hC hK p.2 0) ^ (-(1 : ℝ) / 2)) (s ×ˢ U) :=
    hVVc.comp_continuousOn hWsnd
  -- transport coefficients ∘ Wbv.
  have huc := QIQTH.CoeffContWdiffLift.huc_discharged g gi hg hgi hgpos
  have hu0 : ContinuousOn
      (fun p : ℝ × Point n => transportCoeff (transportOp (vanVleck g) g gi) 0
        (uniformInverseChart g gi hC hK p.2 0)) (s ×ˢ U) :=
    (huc 0).comp_continuousOn hWsnd
  have hu1 : ContinuousOn
      (fun p : ℝ × Point n => transportCoeff (transportOp (vanVleck g) g gi) 1
        (uniformInverseChart g gi hC hK p.2 0)) (s ×ˢ U) :=
    (huc 1).comp_continuousOn hWsnd
  have hsum : ContinuousOn
      (fun p : ℝ × Point n =>
        transportCoeff (transportOp (vanVleck g) g gi) 0 (uniformInverseChart g gi hC hK p.2 0)
        + transportCoeff (transportOp (vanVleck g) g gi) 1
            (uniformInverseChart g gi hC hK p.2 0) * p.1) (s ×ˢ U) :=
    hu0.add (hu1.mul continuous_fst.continuousOn)
  have hcomb : ContinuousOn
      (fun p : ℝ × Point n =>
        radialCutoff a b (uniformInverseChart g gi hC hK p.2 0)
          * (vanVleck g (uniformInverseChart g gi hC hK p.2 0) ^ (-(1 : ℝ) / 2)
            * (transportCoeff (transportOp (vanVleck g) g gi) 0
                  (uniformInverseChart g gi hC hK p.2 0)
              + transportCoeff (transportOp (vanVleck g) g gi) 1
                  (uniformInverseChart g gi hC hK p.2 0) * p.1))) (s ×ˢ U) :=
    hcut.mul (hvv.mul hsum)
  simpa only [chartFieldAmp] using hcomb

/-! ### The τ-uniform sup-bound (obstruction (A), `hbound` content). -/

/-- **★★ `baseSlotAmp_bound` — the τ-uniform base-slot amplitude sup-bound.**  From only the standing
    geometry `(hC, hK, K ∈ 𝓝 0)` and the metric carries `{hg, hgi, hgpos}`, there exist a base radius
    `ρ > 0` and a constant `CA` with
      `∀ τ ∈ [0, τ₀], ∀ z ∈ closedBall 0 ρ, |chartFieldAmp … τ z 0| ≤ CA`.
    Route: the J4-274 base-varying CoV bundle → `ContinuousOn Wbv (ball 0 ρ_b)` (from `hfd`) → joint
    continuity (`baseSlotAmp_continuousOn`) on the COMPACT `[0,τ₀] ×ˢ closedBall 0 (ρ_b/2)` →
    `IsCompact.exists_bound_of_continuousOn`.  This discharges the base-slot content of the J4-275
    `hbound` carry.  NOT `a₁ = R/6`. -/
theorem baseSlotAmp_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b τ₀ : ℝ) :
    ∃ ρ > (0 : ℝ), ∃ CA : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) τ₀,
      ∀ z ∈ Metric.closedBall (0 : Point n) ρ,
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ CA := by
  obtain ⟨ρ, hρ, V, f', _hballmeas, hfd, hinj, hV, hJpos, hΩnhds⟩ :=
    baseVaryingIFTPackage_unconditional g gi hC hK h0Kmem
  have hcont : ContinuousOn (fun z => uniformInverseChart g gi hC hK z 0)
      (Metric.ball (0 : Point n) ρ) := fun z hz => (hfd z hz).continuousWithinAt
  have hprod := baseSlotAmp_continuousOn g gi hC hK hg hgi hgpos a b (Set.Icc (0 : ℝ) τ₀) hcont
  have hsub : Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) (ρ / 2)
      ⊆ Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.ball (0 : Point n) ρ :=
    fun p hp => ⟨hp.1, Metric.closedBall_subset_ball (by linarith) hp.2⟩
  have hcompact : IsCompact
      (Set.Icc (0 : ℝ) τ₀ ×ˢ Metric.closedBall (0 : Point n) (ρ / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨CA, hCA⟩ := hcompact.exists_bound_of_continuousOn (hprod.mono hsub)
  refine ⟨ρ / 2, by linarith, CA, fun τ hτ z hz => ?_⟩
  have hbd := hCA (τ, z) ⟨hτ, hz⟩
  simpa only [Real.norm_eq_abs] using hbd

/-! ### The joint `(τ, z) → (0⁺, 0)` limit (obstruction (A), `hlocal` content). -/

/-- **★★ `baseSlotAmp_joint_limit` — the joint base-slot amplitude limit.**  From the standing
    geometry `(hC, hK, K ∈ 𝓝 0)` and `{hg, hgi, hgpos}`, there exists a base radius `ρ > 0` with
      `Tendsto (fun p => chartFieldAmp … p.1 p.2 0) ((𝓝[>]0) ×ˢ 𝓝 0) (𝓝 (chartFieldAmp … 0 0 0))`,
    i.e. the base-slot amplitude converges to the explicit on-diagonal value `A₀ = chartFieldAmp … 0 0 0`
    as `(τ, z) → (0⁺, 0)`.  Route: joint continuity (`baseSlotAmp_continuousOn`) on `univ ×ˢ ball 0 ρ`,
    read as `ContinuousWithinAt` at `(0,0)`, then `(𝓝[>]0) ×ˢ 𝓝 0 ≤ 𝓝[univ ×ˢ ball 0 ρ] (0,0)`
    (`nhdsWithin_prod_eq`, `ball ∈ 𝓝 0`).  This discharges the base-slot content of the J4-275
    `hlocal` carry (before the `V`/`f`/`det` wrapper).  NOT `a₁ = R/6`. -/
theorem baseSlotAmp_joint_limit (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (a b : ℝ) :
    ∃ ρ > (0 : ℝ),
      Tendsto (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b p.1 p.2 0)
        ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝 (0 : Point n)))
        (𝓝 (chartFieldAmp g gi hC hK a b 0 0 0)) := by
  obtain ⟨ρ, hρ, V, f', _hballmeas, hfd, hinj, hV, hJpos, hΩnhds⟩ :=
    baseVaryingIFTPackage_unconditional g gi hC hK h0Kmem
  have hcont : ContinuousOn (fun z => uniformInverseChart g gi hC hK z 0)
      (Metric.ball (0 : Point n) ρ) := fun z hz => (hfd z hz).continuousWithinAt
  have hprod := baseSlotAmp_continuousOn g gi hC hK hg hgi hgpos a b Set.univ hcont
  have h0ball : (0 : Point n) ∈ Metric.ball (0 : Point n) ρ := Metric.mem_ball_self hρ
  have hcwa : ContinuousWithinAt
      (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b p.1 p.2 0)
      (Set.univ ×ˢ Metric.ball (0 : Point n) ρ) (0, 0) :=
    hprod (0, 0) ⟨Set.mem_univ _, h0ball⟩
  have htend : Tendsto
      (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b p.1 p.2 0)
      (𝓝[Set.univ ×ˢ Metric.ball (0 : Point n) ρ] (0, 0))
      (𝓝 (chartFieldAmp g gi hC hK a b 0 0 0)) := hcwa
  refine ⟨ρ, hρ, htend.mono_left ?_⟩
  rw [nhdsWithin_prod_eq, nhdsWithin_univ,
    nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds (0 : Point n) hρ)]
  exact Filter.prod_mono nhdsWithin_le_nhds le_rfl

/-! ### The explicit on-diagonal limit value `A₀`. -/

/-- **`baseSlotAmp_centreValue` — the explicit coincidence-limit amplitude value.**  Using
    `Wbv 0 = 0` (`chartField_centerValue_base0`, unconditional given `0 ∈ K`), the joint-limit value
    `A₀ = chartFieldAmp … 0 0 0` evaluates to
      `radialCutoff a b 0 · (vanVleck g 0 ^ (-½) · u₀ 0)`,
    the genuine on-diagonal amplitude.  (It equals `1` once the RNC normalisation
    `radialCutoff a b 0 = 1`, `vanVleck g 0 = 1`, `u₀ 0 = 1` is supplied — the labelled `hAmpCentre`
    normalisation, CARRIED not proved here.)  NOT `a₁ = R/6`. -/
theorem baseSlotAmp_centreValue (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K) (a b : ℝ) :
    chartFieldAmp g gi hC hK a b 0 0 0
      = radialCutoff a b (0 : Point n)
        * (vanVleck g (0 : Point n) ^ (-(1 : ℝ) / 2)
            * transportCoeff (transportOp (vanVleck g) g gi) 0 (0 : Point n)) := by
  have hW0 : uniformInverseChart g gi hC hK 0 0 = 0 :=
    chartField_centerValue_base0 g gi hC hK hK0
  simp only [chartFieldAmp, hW0]
  ring

end QIQTH.BaseSlotAmplitude

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.BaseSlotAmplitude
#print axioms baseSlotAmp_continuousOn
#print axioms baseSlotAmp_bound
#print axioms baseSlotAmp_joint_limit
#print axioms baseSlotAmp_centreValue
end AxiomChecks
