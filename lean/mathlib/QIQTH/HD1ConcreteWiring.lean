/-
  HD1ConcreteWiring — J4-200: the CONCRETE WIRING of the `hD1` `C¹` slot of the a₁ = R/6 campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It wires the
  J4-199 bulk+sliver skeleton (`HD1SliverRoute`) and the J4-198 order-2 envelope/measurability
  (`SecondDerivEnvelope`) and the J4-160 nested dominated-continuity engine (`GcoefContinuity`) into
  the FOUR concrete ingredients the `hD1 : ContDiffAt ℝ 1 D 0` slot of `SpatialC2.hCConv_reduction`
  demands, plus the top-level assembly that turns those ingredients INTO `ContDiffAt ℝ 1 D 0`.
  No new singular-convolution analysis is done; the hard content is imported, not reproved.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE hD1-SLOT RE-EXAMINATION VERDICT (asked by the ledger).

  `SpatialC2.hCConv_reduction` splits the `C²` convolution slot into
    (L1) `hfam` — a nbhd `HasFDerivAt` family for `p ↦ heatConv H F t p 0` with derivative field
         `D : Point n → (Point n →L[ℝ] ℝ)` (delivered by the L1 chain / `GcoefContinuity.hCConv_L1_final`),
    (L2) `hD1 : ContDiffAt ℝ 1 D 0`.
  Unfolding `contDiffAt_succ_iff_hasFDerivAt` at `1 = 0 + 1` (Mathlib), `ContDiffAt ℝ 1 D 0` is
  EXACTLY:  ∃ `D'` (the SECOND-derivative field, `Point n → (Point n →L[ℝ] Point n →L[ℝ] ℝ)`), and a
  nbhd `u ∋ 0` with
      • `∀ w ∈ u, HasFDerivAt D (D' w) w`   — `D` DIFFERENTIABLE near `0`  (the J4-199 route:
        `HD1SliverRoute.hD1_bulk_sliver_reduction` gives `HasFDerivAt` of each SCALAR gcoef component
        `gcoef i = ∫₀ᵗ∫z dH·F` with derivative the order-2 field `gderiv i = ∫₀ᵗ∫z dHH·F`; assembling
        the components lifts this to the CLM-valued `D`), PLUS
      • `ContinuousOn D' u`                — `D'` CONTINUOUS near `0`  (the J4-160 engine
        `GcoefContinuity.continuousAt_doubleIntegral_of_dominated` at the ORDER-2 kernel, whose
        `hBint` slot survives ONLY at the sliver rate `(t−s)^{−1/2}`, per J4-198 §C).
  So `hD1` genuinely needs BOTH the second-order differentiation of the convolution (J4-199) AND the
  continuity of that second-derivative field (J4-160).  BOTH feeds are now available; this file
  packages the four concrete ingredients + the assembly.  The `ContDiffAt 1` characterization used is
  `contDiffAt_succ_iff_hasFDerivAt` (mid) + `contDiffAt_zero` (bottom), exactly the
  `PullbackNaturalityLocal` pattern.

  ## THE `witness_sliver2_grand` UNIFORMITY FINDING (asked by the ledger).
  The banked `GaussReplaceSlice.witness_sliver2_grand` / `HessianSliceBound.witness_sliver2_final`
  bound is `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z 0| ≤ (C₀+C₁)·2√ε + C₂·ε`.  The `F s z 0` has the
  field point PINNED TO THE CENTRE `0`, and the kernel `D2H` carries a SINGLE directional index `i`.  So
  the banked sliver bound is **CENTRE-ONLY and per-component (scalar)** — it controls
  `(gderiv i 0 − fderivBulk i ε 0)`, NOT the `x`-uniform CLM distance the reduction's `hsliver` slot
  wants over an `x`-ball.  The honest carry for `hD1_bulk_sliver_reduction` is therefore the
  `x`-uniform version (the same proof re-run at each field point `x`, or `sSet` restricted to `{0}`);
  what this file banks from the sliver bound is the SCALE-FREE, always-true `√ε → 0` VANISHING of its
  right-hand side (`sliver_bound_tendsto_zero`), which is precisely the `hb : Tendsto b l (𝓝 0)` input
  that `HD1SliverRoute.tendstoUniformlyOn_of_dist_le_bound` consumes.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (this file, ns `QIQTH.HD1ConcreteWiring`).

    • `sliver_rate_const_intervalIntegrable` — the scaled sliver rate `s ↦ C·(t−s)^{−1/2}` is
      interval-integrable on `(0,t)` (`SecondDerivEnvelope.sliver_rate_intervalIntegrable` · `const_mul`);
      the `hBint` feed for the order-2 continuity engine.
    • `gderiv_continuousAt` — ★ (GOAL 4) the J4-160 engine
      (`GcoefContinuity.continuousAt_doubleIntegral_of_dominated`) at the ORDER-2 kernel `K'` with the
      `hBint` slot DISCHARGED concretely by the sliver rate — the continuity of the order-2 field
      `gderiv = ∫₀ᵗ∫z dHH·F` that `ContinuousOn D' u` needs.
    • `bulk_tendsto_of_primitive` — ★ (GOAL 2) the BULK pointwise convergence `∫₀^{t−ε} G → ∫₀ᵗ G` as
      `ε → 0⁺`, via Mathlib's endpoint primitive-continuity
      (`intervalIntegral.continuousOn_primitive_interval'`) composed with `ε ↦ t − ε → t⁻`; the
      `hbulk_tendsto` feed of `HD1SliverRoute.hD1_bulk_sliver_reduction` (with `G = s ↦ ∫z dH·F`).
    • `sliver_bound_tendsto_zero` — ★ (GOAL 3) the `√ε → 0` vanishing of the `witness_sliver2_grand`
      right-hand side `(C₀+C₁)·2√ε + C₂·ε`; the `hb` feed of `tendstoUniformlyOn_of_dist_le_bound`.
    • `hD1_reduction` — ★★ (GOALS 1 assembly) the TOP-LEVEL: `ContDiffAt ℝ 1 D 0` from the two unified
      carries {`D` differentiable near `0` with derivative field `D'`} + {`D'` `ContinuousOn` a nbhd},
      via `contDiffAt_succ_iff_hasFDerivAt` + `contDiffAt_zero`.  This is the analytic skeleton that
      closes `hD1` once the four ingredients above are threaded (first carry ← J4-199 lifted
      componentwise; second carry ← `gderiv_continuousAt`).

  ## THE UNIFIED CARRY LIST (what `hD1` is reduced to).
    (i)  a second-derivative field `D'` with `∀ w ∈ u, HasFDerivAt D (D' w) w` on a nbhd `u ∋ 0`
         — the componentwise lift of `hD1_bulk_sliver_reduction`, needing the CENTRE→`x`-uniform
         sliver bound (see finding above) and the bulk derivatives `gcoef_bulk_hasFDerivAt`;
    (ii) `ContinuousOn D' u` — from `gderiv_continuousAt`, needing the order-2 envelope/measurability
         (J4-198) + the sliver-rate domination `hsbound` (the cancellation, an honest labelled carry).
  No other geometric data is introduced here beyond what the L1 chain already carries.

  Every hypothesis is satisfiable, non-vacuous, and never equal to the conclusion.  NO `sorry`.
  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HD1SliverRoute
import QIQTH.GcoefContinuity

open MeasureTheory Filter Set
open scoped Topology Interval ContDiff

namespace QIQTH.HD1ConcreteWiring

set_option maxHeartbeats 1600000

/-! ══════════════════════════════════════════════════════════════════════════════════════════════
    ## GOAL 4 — `gderiv` continuity via the J4-160 engine at the order-2 sliver rate.
    ══════════════════════════════════════════════════════════════════════════════════════════════ -/

/-- **J4-200 — `sliver_rate_const_intervalIntegrable`.**  The scaled sliver rate
    `s ↦ C·(t−s)^{−1/2}` is interval-integrable on `(0,t)`: the banked
    `SecondDerivEnvelope.sliver_rate_intervalIntegrable` (`∫₀ᵗ(t−s)^{−1/2} = 2√t`) times the constant
    `C` (`IntervalIntegrable.const_mul`).  This is the ONLY admissible outer `s`-dominator rate for the
    ORDER-2 kernel (J4-198 §C: the honest `(t−s)^{−1}` is NOT interval-integrable), so it is the
    concrete `hBint` feed of `gderiv_continuousAt`.  NOT `a₁ = R/6`. -/
theorem sliver_rate_const_intervalIntegrable (t C : ℝ) :
    IntervalIntegrable (fun s : ℝ => C * (t - s) ^ (-(1 : ℝ) / 2)) volume 0 t :=
  (QIQTH.SecondDerivEnvelope.sliver_rate_intervalIntegrable t).const_mul C

/-- **★ J4-200 (GOAL 4) — `gderiv_continuousAt`.**  Continuity at `x₀` of the ORDER-2 double integral
    `x ↦ ∫ s in (0)..t, ∫ z, K' s x z ∂ν` — the `gderiv = ∫₀ᵗ∫z dHH·F` second-derivative field whose
    continuity is the `ContinuousOn D' u` half of `hD1` — obtained from the J4-160 nested
    dominated-continuity engine (`GcoefContinuity.continuousAt_doubleIntegral_of_dominated`) with the
    outer `s`-dominator FIXED to the sliver rate `B := s ↦ C·(t−s)^{−1/2}`, whose interval-integrability
    (`hBint`) is DISCHARGED here by `sliver_rate_const_intervalIntegrable`.  The inner
    measurability/domination/continuity slots and the outer `hsbound` (`‖∫z K'‖ ≤ C·(t−s)^{−1/2}`, which
    holds via the Gaussian cancellation — an honest labelled carry) are consumed verbatim.  This is the
    order-2 specialisation of the L1-continuity discharge one order up.  NOT `a₁ = R/6`. -/
theorem gderiv_continuousAt
    {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace Y]
    {ν : Measure Y} (t C : ℝ) (x₀ : X)
    (K' : ℝ → X → Y → ℝ) (boundz : ℝ → Y → ℝ)
    (hzmeas : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun z => K' s x z) ν)
    (hzbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂ν, ‖K' s x z‖ ≤ boundz s z)
    (hzint : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → Integrable (boundz s) ν)
    (hzcont : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t →
        ∀ᵐ z ∂ν, ContinuousAt (fun x => K' s x z) x₀)
    (hsmeas : ∀ᶠ x in 𝓝 x₀,
        AEStronglyMeasurable (fun s => ∫ z, K' s x z ∂ν) (volume.restrict (Set.uIoc 0 t)))
    (hsbound : ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ‖∫ z, K' s x z ∂ν‖ ≤ C * (t - s) ^ (-(1 : ℝ) / 2)) :
    ContinuousAt (fun x => ∫ s in (0)..t, ∫ z, K' s x z ∂ν) x₀ :=
  QIQTH.GcoefContinuity.continuousAt_doubleIntegral_of_dominated t x₀ K'
    (fun s => C * (t - s) ^ (-(1 : ℝ) / 2)) boundz
    hzmeas hzbound hzint hzcont hsmeas hsbound
    (sliver_rate_const_intervalIntegrable t C)

/-! ══════════════════════════════════════════════════════════════════════════════════════════════
    ## GOAL 2 — the BULK pointwise convergence `∫₀^{t−ε} → ∫₀ᵗ` via endpoint primitive-continuity.
    ══════════════════════════════════════════════════════════════════════════════════════════════ -/

/-- **★ J4-200 (GOAL 2) — `bulk_tendsto_of_primitive`.**  The BULK pointwise convergence of the FIRST
    integral: for an interval-integrable `G` on `(0,t)` (`t > 0`),
      `∫ s in (0)..(t−ε), G s  →  ∫ s in (0)..t, G s`   as  `ε → 0⁺`.
    Via Mathlib's endpoint primitive-continuity `intervalIntegral.continuousOn_primitive_interval'`
    (the primitive `u ↦ ∫₀ᵘ G` is continuous on `[[0,t]]`) evaluated at the RIGHT endpoint `t`, composed
    with `ε ↦ t − ε` tending to `t` within `[[0,t]]` from `𝓝[>] 0`.  For the `hD1` application
    `G = s ↦ ∫z dH·F` (the gcoef integrand) and this is the `hbulk_tendsto` slot of
    `HD1SliverRoute.hD1_bulk_sliver_reduction` at each field point (`fbulk ε x → gfull x`).  NOT
    `a₁ = R/6`. -/
theorem bulk_tendsto_of_primitive (G : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hGint : IntervalIntegrable G volume 0 t) :
    Filter.Tendsto (fun ε : ℝ => ∫ s in (0 : ℝ)..(t - ε), G s) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ s in (0 : ℝ)..t, G s)) := by
  -- the primitive is continuous within `[[0,t]]` at the right endpoint `t`.
  have hcont : ContinuousWithinAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, G s) (Set.uIcc 0 t) t :=
    (intervalIntegral.continuousOn_primitive_interval' hGint Set.left_mem_uIcc) t Set.right_mem_uIcc
  -- `ε ↦ t − ε` tends to `t` within `[[0,t]]` from `𝓝[>] 0`.
  have hmap : Filter.Tendsto (fun ε : ℝ => t - ε) (𝓝[>] (0 : ℝ)) (𝓝[Set.uIcc 0 t] t) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Filter.Tendsto (fun ε : ℝ => t - ε) (𝓝 (0 : ℝ)) (𝓝 t) := by
        have hd : Filter.Tendsto (fun ε : ℝ => t - ε) (𝓝 (0 : ℝ)) (𝓝 (t - 0)) :=
          Filter.Tendsto.sub tendsto_const_nhds tendsto_id
        simpa using hd
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iic_mem_nhds ht)] with ε hε hεt
      rw [Set.mem_Ioi] at hε
      rw [Set.mem_Iic] at hεt
      rw [Set.uIcc_of_le ht.le, Set.mem_Icc]
      exact ⟨by linarith, by linarith⟩
  exact hcont.tendsto.comp hmap

/-! ══════════════════════════════════════════════════════════════════════════════════════════════
    ## GOAL 3 — the `√ε → 0` vanishing of the `witness_sliver2_grand` right-hand side.
    ══════════════════════════════════════════════════════════════════════════════════════════════ -/

/-- **★ J4-200 (GOAL 3) — `sliver_bound_tendsto_zero`.**  The `witness_sliver2_grand` /
    `witness_sliver2_final` right-hand side `ε ↦ (C₀+C₁)·2√ε + C₂·ε` tends to `0` as `ε → 0⁺` (`√` is
    continuous, `√0 = 0`).  This is EXACTLY the `hb : Tendsto b l (𝓝 0)` input consumed by
    `HD1SliverRoute.tendstoUniformlyOn_of_dist_le_bound` (and hence by `hD1_bulk_sliver_reduction`) to
    turn the banked CENTRE-only sliver bound into the uniform derivative convergence of the classical
    uniform-limit-of-derivatives theorem.  Scale-free and always true, so it is a clean bankable feed
    (the CENTRE→`x`-uniform upgrade of the bound itself stays the honest carry, see header).  NOT
    `a₁ = R/6`. -/
theorem sliver_bound_tendsto_zero (C₀ C₁ C₂ : ℝ) :
    Filter.Tendsto (fun ε : ℝ => (C₀ + C₁) * (2 * Real.sqrt ε) + C₂ * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hb : Filter.Tendsto (fun ε : ℝ => (C₀ + C₁) * (2 * Real.sqrt ε) + C₂ * ε)
      (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => (C₀ + C₁) * (2 * Real.sqrt ε) + C₂ * ε) :=
      (continuous_const.mul (continuous_const.mul Real.continuous_sqrt)).add
        (continuous_const.mul continuous_id)
    have := hcont.tendsto (0 : ℝ)
    simpa using this
  exact hb.mono_left nhdsWithin_le_nhds

/-! ══════════════════════════════════════════════════════════════════════════════════════════════
    ## GOALS 1 (assembly) — the TOP-LEVEL `ContDiffAt ℝ 1 D 0` reduction.
    ══════════════════════════════════════════════════════════════════════════════════════════════ -/

/-- **★★ J4-200 — `hD1_reduction`.**  THE top-level `hD1` assembly: `ContDiffAt ℝ 1 D 0` (the exact
    slot `SpatialC2.hCConv_reduction` demands) from the TWO unified carries on a nbhd `u ∋ 0`:
      • `hderiv : ∀ x ∈ u, HasFDerivAt D (D' x) x` — `D` differentiable near `0` with SECOND-derivative
        field `D'` (delivered by the J4-199 route `HD1SliverRoute.hD1_bulk_sliver_reduction` lifted from
        the scalar gcoef components to the CLM-valued `D`);
      • `hcont : ContinuousOn D' u` — `D'` continuous near `0` (delivered by `gderiv_continuousAt`, the
        J4-160 engine at the order-2 sliver rate).
    Via `contDiffAt_succ_iff_hasFDerivAt` (`1 = 0 + 1`) for the differentiable-with-`D'` layer and
    `contDiffAt_zero` for the continuity layer — the exact `PullbackNaturalityLocal` pattern.  Fully
    generic in the normed target `F` (instantiated at `F = Point n →L[ℝ] ℝ` for the CLM-valued `D`).
    This closes the `hD1` architecture down to the two enumerated carries.  NOT `a₁ = R/6`. -/
theorem hD1_reduction
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : H → F) (D' : H → (H →L[ℝ] F))
    {u : Set H} (hu : u ∈ 𝓝 (0 : H))
    (hderiv : ∀ x ∈ u, HasFDerivAt D (D' x) x)
    (hcont : ContinuousOn D' u) :
    ContDiffAt ℝ 1 D (0 : H) := by
  have h1 : (1 : WithTop ℕ∞) = ((0 : ℕ) : WithTop ℕ∞) + 1 := by norm_num
  rw [h1]
  refine contDiffAt_succ_iff_hasFDerivAt.mpr ⟨D', ⟨u, hu, hderiv⟩, ?_⟩
  exact contDiffAt_zero.mpr ⟨u, hu, hcont⟩

end QIQTH.HD1ConcreteWiring

section AxiomChecks
open QIQTH.HD1ConcreteWiring
#print axioms sliver_rate_const_intervalIntegrable
#print axioms gderiv_continuousAt
#print axioms bulk_tendsto_of_primitive
#print axioms sliver_bound_tendsto_zero
#print axioms hD1_reduction
end AxiomChecks
