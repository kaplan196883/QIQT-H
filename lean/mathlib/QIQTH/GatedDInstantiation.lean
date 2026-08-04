/-
  GatedDInstantiation — J4-185: the MEASURABLE EXPLICIT REPRESENTATIVE of the concrete
  first-derivative van-Vleck witness kernel `witnessFieldDeriv`, discharging the `hDmeas` slot of the
  Sol endgame plan (2026-08-04, step 5).  ONE brick of the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a pure
  measurability plumbing brick.  It builds a MEASURABLE EXPLICIT REPRESENTATIVE `gatedDerivRep` for
  the concrete first field-derivative kernel `dH := witnessFieldDeriv`, and uses the gate-eq
  DICHOTOMY (E1 of `EngineInstantiation`) to prove that the raw derivative kernel EQUALS this
  explicit representative EVERYWHERE — thereby reducing the joint `(s,z)`-measurability `hDmeas` of
  the derivative kernel (the genuine `pd`-content that the `measurable_deriv_with_param` route cannot
  reach across `∂K`, per J4-181's firewall) to strictly LOWER-order, satisfiable, non-vacuous
  carries: the Borel chart-in-`z` measurability, the first-JET field measurability, and the amplitude
  / amplitude-`pd` measurability, plus the on-gate jet/openness data.  Never a conclusion; no
  vacuous / unsatisfiable hypotheses; NO `sorry`; NO new axioms.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ── THE REPRESENTATIVE (`gatedDerivRep`) — the E1-formula, `z ∈ K`-indicator gated.

    On `z ∈ K` (base gate) the E1 on-gate formula (`witnessFieldDeriv_gate_eq`) gives the closed
    form `G·(scalar)·A + G·(∂ᵢA)` with `G := gaussDdim τ (W z x)`, `A := chartFieldAmp`,
    `scalar := −(∑ₖ (W z x)ₖ·Pₖ)/(2τ)`; off `K` the derivative kernel VANISHES
    (`witnessFieldDeriv_offGate_eq_zero`).  `gatedDerivRep` is EXACTLY this closed form times the
    `z ∈ K` indicator (`Set.indicator (Prod.snd ⁻¹' K) …`), carrying the first-jet field `Pfield`.

    • `gatedDerivRep` — the def.
    • `gatedDerivRep_measurable` — ★ its joint `(s,z)`-Borel measurability, from
        `{hKmeasSet, hChartMeas, hPmeas, hAmpMeas, hAmpDerivMeas}` (the `gaussDdim` joint-measurable
        envelope `gaussDdim_uncurry_measurable` + `Measurable.indicator` glue).  NOT `a₁ = R/6`.

  ── THE VANISHING + IDENTITY.

    • `witnessFieldDeriv_eq_zero_of_nonpos` — for `τ ≤ 0` (and `0 < n`) the whole gated witness slot
        vanishes (`heatParametrix` kills the inner kernel), so the derivative kernel is `0`.
    • `witnessFieldDeriv_eq_gatedDerivRep` — ★ the EVERYWHERE identity `witnessFieldDeriv = gatedDerivRep`
        via the three-way dichotomy `{z ∉ K → 0=0}`, `{z ∈ K, τ ≤ 0 → 0 = G·(…) with G = 0}`,
        `{z ∈ K, τ > 0 → E1 formula}`.  NOT `a₁ = R/6`.

  ── STEPS 1+2 CAPSTONE.

    • `witnessFieldDeriv_measurable_of_gateEq` — ★★ the joint `(s,z)`-measurability of the raw
        first-derivative kernel `(s,z) ↦ witnessFieldDeriv … i (t−s) x z`, via the identity +
        `gatedDerivRep_measurable`.  THE genuine `hDmeas` content, reduced to the unified carries.
        NOT `a₁ = R/6`.

  ── STEPS 3–6 WIRING.

    • `hDmeas_discharged` — ★★ the EXACT `CConvDerivativeData.hDmeas` field shape
        (`∀ x₀ ∈ u₀, ∀ i, ∀ᶠ x, Measurable (fun p ↦ witnessFieldDeriv … i (t−p.1) x p.2)`), from the
        `∀ᶠ x`-first bundled carry `hData`.  NOT `a₁ = R/6`.
    • `hMeasSet_from_geometry` — step 3: the good-set `MeasurableSet` from
        `GateDiffWiringMeasSet.measurableSet_hasDerivAt_of_continuous_slices`, sourcing `hDmeas` from
        geometry.
    • `goodProd_from_geometry` — steps 4–5: the PRODUCT-a.e. `HasDerivAt` good-set object from
        `FlowBallInstantiation.goodProd_hasDerivAt_of_carries`, sourcing `hDmeas` from geometry.
    • `derivativeData_from_geometry` — step 6: the full `CConvDerivativeData` bundle, `hDmeas` from
        geometry, `hlin`/`hDrep` taken as inputs (the J4-184 split: `hlin` rides the C²-regularity
        chain, not the measurability chain).  NOT `a₁ = R/6`.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hChartMeas` — the Borel chart-in-`z` measurability at the fixed field point (Borel analogue of
      J4-178's `hVmapMeas`).
    • `hPmeas` — the first-JET field `Pfield` measurability (strictly lower-order than the witness
      derivative).
    • `hAmpMeas` / `hAmpDerivMeas` — the (non-singular) amplitude and its field-`pd` measurability
      (the amplitude has NO Gaussian singularity — a strictly simpler derivative than the witness).
    • the on-gate jet/openness data `hgate` (the same on-gate content as the envelope `hGateData`).
    • `hKmeasSet` — `MeasurableSet K` (compactness); `0 < n` — the `n`-dimensional heat-kernel story.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.FlowBallInstantiation

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixOrder QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.OnGateFieldRegularity QIQTH.HeatDuhamel
open QIQTH.InnerKernelJointMeas QIQTH.GateDiffWiringMeasSet
open QIQTH.SliceInterfaceInstantiation QIQTH.CConvFacade QIQTH.FlowBallInstantiation
open scoped Interval Topology BigOperators ContDiff

namespace QIQTH.GatedDInstantiation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE MEASURABLE EXPLICIT REPRESENTATIVE `gatedDerivRep`.
    ############################################################################### -/

/-- **`gatedDerivRep` — the measurable explicit representative of `witnessFieldDeriv`.**  For a fixed
    field point `x` and a carried first-jet field `Pfield : z ↦ Pval`, the `z ∈ K`-indicator of the
    E1 on-gate closed form (`witnessFieldDeriv_gate_eq`):
      `p ↦ 𝟙_{p.2 ∈ K}·( G·(scalar)·A + G·(∂ᵢA) )`,   `G := gaussDdim (t−p.1) (W p.2 x)`,
    `A := chartFieldAmp (t−p.1) p.2 x`, `scalar := −(∑ₖ (W p.2 x)ₖ·Pfield p.2 ₖ)/(2(t−p.1))`,
    `W := uniformInverseChart g gi hC hK`.  The `dH := witnessFieldDeriv` will be shown to EQUAL this
    everywhere (`witnessFieldDeriv_eq_gatedDerivRep`), so its joint `(s,z)`-measurability rides the
    (manifestly measurable) representative.  NOT `a₁ = R/6`. -/
noncomputable def gatedDerivRep (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (t : ℝ) (x : Point n)
    (Pfield : Point n → Fin n → ℝ) : ℝ × Point n → ℝ :=
  Set.indicator (Prod.snd ⁻¹' K)
    (fun p : ℝ × Point n =>
      gaussDdim (t - p.1) (uniformInverseChart g gi hC hK p.2 x)
          * (-(∑ k, uniformInverseChart g gi hC hK p.2 x k * Pfield p.2 k) / (2 * (t - p.1)))
          * chartFieldAmp g gi hC hK a b (t - p.1) p.2 x
        + gaussDdim (t - p.1) (uniformInverseChart g gi hC hK p.2 x)
          * pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x)

/-- **★ `gatedDerivRep_measurable`.**  The joint `(s,z)`-Borel measurability of the explicit
    representative, from: `hKmeasSet` (`MeasurableSet K` ⟹ the `Prod.snd ⁻¹' K` indicator set is
    measurable), `hChartMeas` (Borel chart-in-`z`), `hPmeas` (first-jet field), `hAmpMeas` /
    `hAmpDerivMeas` (amplitude + its `pd`).  The `gaussDdim` envelope is jointly measurable via
    `gaussDdim_uncurry_measurable` composed with `(s,z) ↦ (t−s, W p.2 x)`.  NOT `a₁ = R/6`. -/
theorem gatedDerivRep_measurable (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (t : ℝ) (x : Point n)
    (Pfield : Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 x))
    (hPmeas : ∀ k, Measurable (fun p : ℝ × Point n => Pfield p.2 k))
    (hAmpMeas : Measurable
      (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b (t - p.1) p.2 x))
    (hAmpDerivMeas : Measurable
      (fun p : ℝ × Point n => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x)) :
    Measurable (gatedDerivRep g gi hC hK a b i t x Pfield) := by
  unfold gatedDerivRep
  have hG : Measurable
      (fun p : ℝ × Point n => gaussDdim (t - p.1) (uniformInverseChart g gi hC hK p.2 x)) :=
    gaussDdim_uncurry_measurable.comp ((measurable_const.sub measurable_fst).prodMk hChartMeas)
  have hSum : Measurable
      (fun p : ℝ × Point n =>
        ∑ k, uniformInverseChart g gi hC hK p.2 x k * Pfield p.2 k) := by
    refine Finset.measurable_sum Finset.univ (fun k _ => ?_)
    exact ((measurable_pi_apply k).comp hChartMeas).mul (hPmeas k)
  have hSc : Measurable
      (fun p : ℝ × Point n =>
        -(∑ k, uniformInverseChart g gi hC hK p.2 x k * Pfield p.2 k) / (2 * (t - p.1))) :=
    hSum.neg.div (measurable_const.mul (measurable_const.sub measurable_fst))
  refine Measurable.indicator ?_ (measurable_snd hKmeasSet)
  exact ((hG.mul hSc).mul hAmpMeas).add (hG.mul hAmpDerivMeas)

/-! ###############################################################################
    ### THE VANISHING (τ ≤ 0) AND THE EVERYWHERE IDENTITY.
    ############################################################################### -/

/-- **`witnessFieldDeriv_eq_zero_of_nonpos`.**  For `τ ≤ 0` (and `0 < n`) the gated witness slot is
    identically `0` (the `heatParametrix` factor vanishes, `heatParametrix_eq_zero_of_nonpos`), so its
    field `pd` — the first-derivative kernel — is `0`.  This is the leg that makes the representative
    identity hold EVERYWHERE (not merely on `{τ > 0}`).  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_eq_zero_of_nonpos (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (p z : Point n) (hτ : τ ≤ 0) :
    witnessFieldDeriv g gi hC hK S a b i τ p z = 0 := by
  have hzero : ∀ x' : Point n, vanVleckGatedWitness g gi hC hK S a b τ x' z = 0 := by
    intro x'
    have hH : globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b
        (uniformInverseChart g gi hC hK) τ x' z = 0 := by
      unfold globalCutoffParametrixWitnessN
      rw [heatParametrix_eq_zero_of_nonpos hn 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) τ _ hτ, mul_zero]
    rw [vanVleckGatedWitness]
    by_cases hz : z ∈ K
    · by_cases hx : x' ∈ S z
      · rw [gatedKernel_apply_of_mem K S _ τ hz hx]; exact hH
      · exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inr hx)
    · exact gatedKernel_apply_of_notMem K S _ τ x' z (Or.inl hz)
  unfold witnessFieldDeriv
  simp only [hzero]
  exact pd_const 0 i p

/-- **★ `witnessFieldDeriv_eq_gatedDerivRep` — THE EVERYWHERE IDENTITY.**  The raw first-derivative
    kernel EQUALS the explicit representative at every `p = (s,z)`, via the three-way dichotomy:
      • `z ∉ K` — both sides `0` (`witnessFieldDeriv_offGate_eq_zero`, `Set.indicator_of_notMem`);
      • `z ∈ K`, `τ = t−s ≤ 0` — LHS `0` (`witnessFieldDeriv_eq_zero_of_nonpos`), RHS `0` because the
        shared `gaussDdim (t−s)` factor vanishes (`gaussDdim_eq_zero_of_nonpos`);
      • `z ∈ K`, `τ > 0` — the E1 on-gate formula (`witnessFieldDeriv_gate_eq`), using the on-gate
        jet/openness data `hgate`.
    NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_eq_gatedDerivRep (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (x : Point n) (Pfield : Point n → Fin n → ℝ)
    (hgate : ∀ p : ℝ × Point n, p.2 ∈ K → 0 < t - p.1 →
        IsOpen (S p.2) ∧ x ∈ S p.2 ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK p.2 (Function.update x i s) k)
          (Pfield p.2 k) (x i)) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x) :
    ∀ p : ℝ × Point n,
      witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2
        = gatedDerivRep g gi hC hK a b i t x Pfield p := by
  intro p
  simp only [gatedDerivRep]
  by_cases hzK : p.2 ∈ K
  · rw [Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' K from hzK)]
    by_cases hτ : 0 < t - p.1
    · obtain ⟨hSopen, hxS, hjet, hamp⟩ := hgate p hzK hτ
      exact witnessFieldDeriv_gate_eq g gi hC hK S a b i (t - p.1) hτ p.2 hzK hSopen x hxS
        (Pfield p.2) hjet hamp
    · rw [not_lt] at hτ
      rw [witnessFieldDeriv_eq_zero_of_nonpos hn g gi hC hK S a b i (t - p.1) x p.2 hτ,
          gaussDdim_eq_zero_of_nonpos hn (t - p.1) (uniformInverseChart g gi hC hK p.2 x) hτ]
      ring
  · rw [Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' K from hzK)]
    exact witnessFieldDeriv_offGate_eq_zero g gi hC hK S a b i (t - p.1) x p.2 hzK

/-! ###############################################################################
    ### STEPS 1+2 — the raw derivative-kernel measurability via the gate-eq route.
    ############################################################################### -/

/-- **★★ `witnessFieldDeriv_measurable_of_gateEq` — STEPS 1+2, the genuine `hDmeas` content.**  The
    joint `(s,z)`-Borel measurability of the raw concrete first-derivative van-Vleck witness kernel
    `(s,z) ↦ witnessFieldDeriv … i (t−s) x z` at a fixed field point `x`, obtained by rewriting it —
    via the everywhere identity (`witnessFieldDeriv_eq_gatedDerivRep`) — as the manifestly measurable
    explicit representative `gatedDerivRep` (`gatedDerivRep_measurable`).  This is the honest
    reduction of the derivative-kernel measurability (the `pd`-content beyond the
    `measurable_deriv_with_param` reach) to the unified factor carries.  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_measurable_of_gateEq (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (x : Point n) (Pfield : Point n → Fin n → ℝ)
    (hKmeasSet : MeasurableSet K)
    (hChartMeas : Measurable (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 x))
    (hPmeas : ∀ k, Measurable (fun p : ℝ × Point n => Pfield p.2 k))
    (hAmpMeas : Measurable
      (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b (t - p.1) p.2 x))
    (hAmpDerivMeas : Measurable
      (fun p : ℝ × Point n => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x))
    (hgate : ∀ p : ℝ × Point n, p.2 ∈ K → 0 < t - p.1 →
        IsOpen (S p.2) ∧ x ∈ S p.2 ∧
        (∀ k, HasDerivAt
          (fun s : ℝ => uniformInverseChart g gi hC hK p.2 (Function.update x i s) k)
          (Pfield p.2 k) (x i)) ∧
        PdiffAt (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x) :
    Measurable (fun p : ℝ × Point n =>
      witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) := by
  have hrw : (fun p : ℝ × Point n => witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2)
      = gatedDerivRep g gi hC hK a b i t x Pfield := by
    funext p
    exact witnessFieldDeriv_eq_gatedDerivRep hn g gi hC hK S a b i t x Pfield hgate p
  rw [hrw]
  exact gatedDerivRep_measurable g gi hC hK a b i t x Pfield hKmeasSet hChartMeas hPmeas
    hAmpMeas hAmpDerivMeas

/-! ###############################################################################
    ### STEP 6 — the `∀ᶠ x`-first `CConvDerivativeData.hDmeas` field shape.
    ############################################################################### -/

/-- **★★ `hDmeas_discharged` — THE `CConvDerivativeData.hDmeas` FIELD.**  The exact `hDmeas` slot
    shape consumed by `SliceInterfaceInstantiation.hjoint_instantiated` /
    `CConvFacade.CConvDerivativeData`
      `∀ x₀ ∈ u₀, ∀ i, ∀ᶠ x in 𝓝 x₀, Measurable (fun p ↦ witnessFieldDeriv … i (t−p.1) x p.2)`,
    produced from `hKmeasSet` and the `∀ᶠ x`-first bundled carry `hData` (which supplies, per `x`, a
    first-jet field `Pfield` together with the chart / jet / amplitude / amplitude-`pd`
    measurabilities and the on-gate jet/openness data).  Each fibre is closed by
    `witnessFieldDeriv_measurable_of_gateEq`.  NOT `a₁ = R/6`. -/
theorem hDmeas_discharged (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ)
    (u₀ : Set (Point n))
    (hKmeasSet : MeasurableSet K)
    (hData : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∃ Pfield : Point n → Fin n → ℝ,
          Measurable (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 x)
          ∧ (∀ k, Measurable (fun p : ℝ × Point n => Pfield p.2 k))
          ∧ Measurable
              (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b (t - p.1) p.2 x)
          ∧ Measurable
              (fun p : ℝ × Point n => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x)
          ∧ (∀ p : ℝ × Point n, p.2 ∈ K → 0 < t - p.1 →
              IsOpen (S p.2) ∧ x ∈ S p.2 ∧
              (∀ k, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK p.2 (Function.update x i s) k)
                (Pfield p.2 k) (x i)) ∧
              PdiffAt (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x)) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      Measurable (fun p : ℝ × Point n =>
        witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) := by
  intro x₀ hx₀ i
  filter_upwards [hData x₀ hx₀ i] with x hx
  obtain ⟨Pfield, hChartMeas, hPmeas, hAmpMeas, hAmpDerivMeas, hgate⟩ := hx
  exact witnessFieldDeriv_measurable_of_gateEq hn g gi hC hK S a b i t x Pfield hKmeasSet
    hChartMeas hPmeas hAmpMeas hAmpDerivMeas hgate

/-! ###############################################################################
    ### STEPS 3–5 — feeding the discharged `hDmeas` into the banked good-set consumers.
    ############################################################################### -/

/-- **★ `hMeasSet_from_geometry` — STEP 3.**  The `HasDerivAt`-property good-set measurability of
    `GateDiffWiringMeasSet.hMeasSet_of_sliceCont`, now sourcing its `hDmeas` slot from the geometry
    via `hDmeas_discharged` (the other three slots `hSliceCont` / `hWq` / `hWa` are the banked slice /
    interface carries of J4-181).  NOT `a₁ = R/6`. -/
theorem hMeasSet_from_geometry (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ)
    (ν : Measure (Point n)) (u₀ : Set (Point n))
    (hSliceCont : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ p : ℝ × Point n, Continuous
          (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2))
    (hWq : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ q : ℚ,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1)
            (Function.update x i (x i + (q : ℝ))) p.2))
    (hWa : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i (x i)) p.2))
    (hKmeasSet : MeasurableSet K)
    (hData : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∃ Pfield : Point n → Fin n → ℝ,
          Measurable (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 x)
          ∧ (∀ k, Measurable (fun p : ℝ × Point n => Pfield p.2 k))
          ∧ Measurable
              (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b (t - p.1) p.2 x)
          ∧ Measurable
              (fun p : ℝ × Point n => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x)
          ∧ (∀ p : ℝ × Point n, p.2 ∈ K → 0 < t - p.1 →
              IsOpen (S p.2) ∧ x ∈ S p.2 ∧
              (∀ k, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK p.2 (Function.update x i s) k)
                (Pfield p.2 k) (x i)) ∧
              PdiffAt (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x)) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      MeasurableSet {p : ℝ × Point n |
        HasDerivAt
          (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
          (witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) (x i)} :=
  hMeasSet_of_sliceCont g gi hC hK S a b t ν u₀ hSliceCont hWq hWa
    (hDmeas_discharged hn g gi hC hK S a b t u₀ hKmeasSet hData)

/-- **★ `goodProd_from_geometry` — STEPS 4–5.**  The PRODUCT-a.e. `HasDerivAt` good-set object of
    `FlowBallInstantiation.goodProd_hasDerivAt_of_carries`, sourcing its `hDmeas` slot from geometry
    via `hDmeas_discharged`.  The iterated-a.e. `HasDerivAt` carry `hAeAe` (step 4, from the
    C²-regularity chain) is taken as input.  NOT `a₁ = R/6`. -/
theorem goodProd_from_geometry (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b t : ℝ)
    (ν : Measure (Point n)) [SFinite ν] (u₀ : Set (Point n))
    (hSliceCont : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ p : ℝ × Point n, Continuous
          (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2))
    (hWq : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ q : ℚ,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1)
            (Function.update x i (x i + (q : ℝ))) p.2))
    (hWa : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        Measurable (fun p : ℝ × Point n =>
          vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i (x i)) p.2))
    (hKmeasSet : MeasurableSet K)
    (hData : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∃ Pfield : Point n → Fin n → ℝ,
          Measurable (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 x)
          ∧ (∀ k, Measurable (fun p : ℝ × Point n => Pfield p.2 k))
          ∧ Measurable
              (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b (t - p.1) p.2 x)
          ∧ Measurable
              (fun p : ℝ × Point n => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x)
          ∧ (∀ p : ℝ × Point n, p.2 ∈ K → 0 < t - p.1 →
              IsOpen (S p.2) ∧ x ∈ S p.2 ∧
              (∀ k, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK p.2 (Function.update x i s) k)
                (Pfield p.2 k) (x i)) ∧
              PdiffAt (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x))
    (hAeAe : ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 t)), ∀ᵐ z ∂ν,
          HasDerivAt
            (fun w => vanVleckGatedWitness g gi hC hK S a b (t - s) (Function.update x i w) z)
            (witnessFieldDeriv g gi hC hK S a b i (t - s) x z) (x i)) :
    ∀ x₀ ∈ u₀, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      ∀ᵐ p ∂((volume.restrict (Set.uIoc 0 t)).prod ν),
        HasDerivAt
          (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
          (witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) (x i) :=
  goodProd_hasDerivAt_of_carries g gi hC hK S a b t ν u₀ hSliceCont hWq hWa
    (hDmeas_discharged hn g gi hC hK S a b t u₀ hKmeasSet hData) hAeAe

/-! ###############################################################################
    ### STEP 6 (full) — the `CConvDerivativeData` bundle, `hDmeas` from geometry.
    ############################################################################### -/

/-- **★★ `derivativeData_from_geometry` — STEP 6, the full derivative-data bundle.**  Builds
    `CConvFacade.CConvDerivativeData` with its `hDmeas` field discharged from the geometry
    (`hDmeas_discharged`) rather than carried whole; `hlin` (∀ x ∈ u, POINTWISE-everywhere) and
    `hDrep` are taken as inputs — the honest J4-184 split: `hlin` rides the C²-regularity chain, NOT
    the joint-measurability chain.  NOT `a₁ = R/6`. -/
theorem derivativeData_from_geometry (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b t : ℝ) (u : Set (Point n)) (F : ℝ → Point n → ℝ)
    (H Fconv : ℝ → Point n → Point n → ℝ) (D : Point n → (Point n →L[ℝ] ℝ))
    (hKmeasSet : MeasurableSet K)
    (hData : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∃ Pfield : Point n → Fin n → ℝ,
          Measurable (fun p : ℝ × Point n => uniformInverseChart g gi hC hK p.2 x)
          ∧ (∀ k, Measurable (fun p : ℝ × Point n => Pfield p.2 k))
          ∧ Measurable
              (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b (t - p.1) p.2 x)
          ∧ Measurable
              (fun p : ℝ × Point n => pd (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x)
          ∧ (∀ p : ℝ × Point n, p.2 ∈ K → 0 < t - p.1 →
              IsOpen (S p.2) ∧ x ∈ S p.2 ∧
              (∀ k, HasDerivAt
                (fun s : ℝ => uniformInverseChart g gi hC hK p.2 (Function.update x i s) k)
                (Pfield p.2 k) (x i)) ∧
              PdiffAt (chartFieldAmp g gi hC hK a b (t - p.1) p.2) i x))
    (hlin : ∀ x ∈ u, ∀ i : Fin n,
        HasDerivAt (fun w => heatConv H Fconv t (Function.update x i w) 0)
          ((D x) (Pi.single i (1 : ℝ))) (x i))
    (hDrep : ∀ x ∈ u,
        D x = ∑ i : Fin n,
          (∫ s in (0:ℝ)..t, ∫ z, witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z
            ∂(volume : Measure (Point n))) • (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ)) :
    CConvDerivativeData g gi hC hK S a b t u F H Fconv D :=
  { hDmeas := hDmeas_discharged hn g gi hC hK S a b t u hKmeasSet hData
    hlin := hlin
    hDrep := hDrep }

end QIQTH.GatedDInstantiation

section AxiomChecks
open QIQTH.GatedDInstantiation
#print axioms gatedDerivRep_measurable
#print axioms witnessFieldDeriv_eq_zero_of_nonpos
#print axioms witnessFieldDeriv_eq_gatedDerivRep
#print axioms witnessFieldDeriv_measurable_of_gateEq
#print axioms hDmeas_discharged
#print axioms hMeasSet_from_geometry
#print axioms goodProd_from_geometry
#print axioms derivativeData_from_geometry
end AxiomChecks
