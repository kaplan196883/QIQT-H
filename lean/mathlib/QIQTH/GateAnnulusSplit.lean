/-
  GateAnnulusSplit — J4-279: killing `hGgate` + `hSupp` at the CONCRETE witness (the fixed-`f` FINAL).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT (the W1 wall of the a₁ = R/6 campaign).  `QIQTH.EnrichedChartBundle.chartImage_approx_
  identity_v3` (J4-278) is the fixed-`f` chart-image approximate identity carrying ONLY two structural
  inputs beyond the standing satisfiable ones (for the produced `(ρ, V, f')`):
    • `hGgate` — `∀ z ∈ ball 0 ρ, z ∈ K ∧ (0 : Point n) ∈ S z`  (the on-gate factorisation is active on
      the produced ball, so `witness_zero_eq_gauss_mul_amp` applies pointwise on `ball 0 ρ`);
    • `hSupp`  — `∀ τ, ∀ z ∉ ball 0 ρ, vanVleckGatedWitness … τ 0 z = 0`  (τ-uniform vanishing of the
      witness OFF the produced ball).

  This file ELIMINATES BOTH at the concrete van-Vleck witness, replacing them by genuinely-remaining,
  simultaneously-satisfiable gate facts, and lands the fixed-`f` FINAL approximate identity.

  ── THE TWO ELIMINATIONS.

    (i) `hGgate`.  The witness gate `S` is provider-chosen (existential); `v3` takes `S` as a PARAMETER
        and `ρ` is produced INTERNALLY through a radius CAP `ρcap` fed to `enrichedChartBundle`.  So we
        cap `ρcap := min ρA rS` at an EXTERNAL gate radius `rS`, giving `ρ ≤ rS`; then `hGgate` on the
        produced `ball 0 ρ ⊆ ball 0 rS` is discharged from two HONEST carries at `rS`:
          • `hKball : ball 0 rS ⊆ K`      (satisfiable — `K ∈ 𝓝 0`);
          • `hSact  : ∀ z ∈ ball 0 rS, (0 : Point n) ∈ S z`  (the gate-activation fact; at the concrete
            gate `gatedWitnessN1_package_open` exports `0 ∈ K → 0 ∈ S 0` and `0 ∈ K → IsOpen (S 0)`,
            and `IsOpen (S 0)` with `0 ∈ S 0` supplies a ball around `0` — the base-slice activation).
        NO cap enlargement is needed downstream: `ρ ≤ ρA` still holds (`min ρA rS ≤ ρA`), so the
        amplitude sup-bound / Jacobian route of `v3` is untouched.

    (ii) `hSupp` — THE ANNULUS SPLIT.  The concrete witness does NOT vanish off a SMALL ball in general
        (its gate is wider than the CoV ball).  Instead of demanding vanishing we SPLIT
            `∫ z, Wit τ 0 z · f z = ∫_{ball 0 ρ} + ∫_{(ball 0 ρ)ᶜ}`
        and show the OFF-ball part → 0.  The zeroth WIDE domination
        (`WideWitnessAmplitude.WideAmplitudeData.zeroth_domination_global`) gives, τ-uniformly for
        `0 < τ ≤ τ₀`, `|Wit τ 0 z| ≤ C · gaussDdim (lam·τ) z` for ALL `z` (a base-point Gaussian, the
        near-isometry already baked in).  With `|f| ≤ Cf`,
            ‖∫_{(ball 0 ρ)ᶜ} Wit · f‖ ≤ C·Cf · ∫_{(ball 0 ρ)ᶜ} gaussDdim (lam·τ) → 0,
        the width-scaled Gaussian tail (`ChartImageApproxIdentity.gaussDdim_ballCompl_mass_tendsto_zero`
        reparametrised through `τ ↦ lam·τ`).  The ON-ball part → `f 0` by the same Layer-A∘B∘C route as
        `v3` (factorisation on the ball, no vanishing needed).  The two pieces recombine via
        `integral_add_compl` (integrability of `Wit · f` from the global domination + the carried
        witness-slice measurability).

  ── WHAT LANDS HERE (honest; the ★ is the FINAL).
    • `offBall_integral_tendsto_zero` — ★ (Asplit) the STANDALONE off-ball-vanishing limit for any
      zeroth-wide-dominated kernel slice `H`.  Pure domination + Gaussian-tail squeeze.
    • `hGgate_of_gate_activation` — ★ (G) the `hGgate` reduction: from `hKball`/`hSact` at `rS` and
      `ρ ≤ rS`, the on-ball gate activation.
    • `chartImage_approx_identity_final` — ★★ THE FIXED-`f` FINAL.  `v3` with `hGgate`/`hSupp` REMOVED,
      replaced by the honest carries: the two gate-activation facts `{hKball, hSact}` at an external
      radius `rS`, the witness-slice measurability `hWslice`, and the zeroth wide domination `hDom`
      (`lam, τ₀, C`).  Conclusion (unconditional in the produced `ρ`):
          `Tendsto (fun τ => ∫ z, Wit τ 0 z · f z) (𝓝[>]0) (𝓝 (f 0))`.

  ── THE FINAL HYPOTHESIS LIST of `chartImage_approx_identity_final` (all satisfiable, none the
     conclusion):  standing geometry `(hC, hK, K ∈ 𝓝 0)`, metric carries `{hg, hgi, hgpos}`, gauge
     `det g 0 = 1`, `0 < a < b`, `f` measurable + globally bounded + continuous at `0`;
     PLUS the gate carries `{rS > 0, hKball, hSact}`, the witness-slice measurability `hWslice`, and the
     zeroth wide domination `hDom` (with `0 < lam`, `0 < τ₀`, `0 ≤ C`).  `hGgate` and `hSupp` are GONE.

  ⚠ HONEST FIREWALL.  NOT `a₁ = R/6`; proves NOTHING about `R/6`.  These are analytic composition
  bricks (a gate-activation reduction + a Gaussian-tail annulus split + the fixed-`f` recombination).
  No `sorry` (prose only), no new axioms, no `:= True`, no vacuous / unsatisfiable / conclusion-in-
  disguise hypotheses: the gate carries are satisfiable at the concrete gate via the openness exports;
  the domination is the banked `zeroth_domination_global`; the witness-slice measurability is the
  banked `vanVleckGatedWitness_slice_aestronglyMeasurable`.  The residual (moving-`f` step) is a
  SEPARATE later brick — untouched.  No existing file is edited.
-/
import Mathlib
import QIQTH.EnrichedChartBundle
import QIQTH.WideWitnessAmplitude
import QIQTH.ChartImageApproxIdentity

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ResidueBound
open scoped Topology

namespace QIQTH.GateAnnulusSplit

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### (Asplit) — the standalone off-ball-vanishing limit. -/

/-- **★ (Asplit) `offBall_integral_tendsto_zero` — THE OFF-BALL VANISHING LIMIT.**  For a kernel slice
    `H : ℝ → Point n → ℝ` wide-dominated at the zeroth order (`|H τ z| ≤ C · gaussDdim (lam·τ) z` for
    `0 < τ ≤ τ₀`, ALL `z`) and a globally bounded `f` (`|f z| ≤ Cf`), the OFF-ball pairing vanishes:
        `Tendsto (fun τ => ∫ z in (ball 0 ρ)ᶜ, H τ z · f z) (𝓝[>]0) (𝓝 0)`.
    Route: `‖∫_{(ball 0 ρ)ᶜ} H · f‖ ≤ ∫_{(ball 0 ρ)ᶜ} ‖H·f‖ ≤ C·Cf·∫_{(ball 0 ρ)ᶜ} gaussDdim (lam·τ)`,
    the last factor tending to `0` by the width-`(lam·τ)` Gaussian tail (the fixed-ball tail lemma
    reparametrised through `τ ↦ lam·τ`, which preserves `𝓝[>]0` for `lam > 0`); squeeze.  NOT
    `a₁ = R/6`. -/
theorem offBall_integral_tendsto_zero
    (H : ℝ → Point n → ℝ) (f : Point n → ℝ) (ρ lam CW Cf τ₀ : ℝ)
    (hρ : 0 < ρ) (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hfb : ∀ z, |f z| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |H τ z| ≤ CW * gaussDdim (lam * τ) z) :
    Tendsto (fun τ => ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, H τ z * f z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- Width reparametrisation: `τ ↦ lam·τ` preserves `𝓝[>]0`.
  have hc : Tendsto (fun τ : ℝ => lam * τ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun τ : ℝ => lam * τ) (𝓝 (0 : ℝ)) (𝓝 (lam * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hscale : Tendsto (fun τ : ℝ => lam * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact Set.mem_Ioi.mpr (mul_pos hlam (Set.mem_Ioi.mp hτ))
  -- The width-`(lam·τ)` Gaussian tail off the fixed ball tends to `0`.
  have htail : Tendsto
      (fun τ => ∫ w in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (lam * τ) w)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (QIQTH.ChartImageApproxIdentity.gaussDdim_ballCompl_mass_tendsto_zero (n := n) ρ hρ).comp hscale
  have hub : Tendsto
      (fun τ => CW * Cf * ∫ w in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (lam * τ) w)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := htail.const_mul (CW * Cf)
    simpa using h
  -- Eventual `τ ≤ τ₀`.
  have hcap : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ≤ τ₀ := by
    have hIio : Set.Iio τ₀ ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds hτ₀)
    filter_upwards [hIio] with τ hτ
    exact le_of_lt hτ
  -- Squeeze.
  refine squeeze_zero_norm' ?_ hub
  filter_upwards [self_mem_nhdsWithin, hcap] with τ hτpos hττ₀
  have hτp : 0 < τ := Set.mem_Ioi.mp hτpos
  have hgint : IntegrableOn (fun z : Point n => CW * Cf * gaussDdim (lam * τ) z)
      (Metric.ball (0 : Point n) ρ)ᶜ volume :=
    ((QIQTH.HeatResidualBound.gaussDdim_integrable (lam * τ) (mul_pos hlam hτp)).const_mul
      (CW * Cf)).integrableOn
  calc ‖∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, H τ z * f z‖
      ≤ ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, ‖H τ z * f z‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, CW * Cf * gaussDdim (lam * τ) z := by
        refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hgint ?_
        refine ae_of_all _ (fun z => ?_)
        simp only [Real.norm_eq_abs, abs_mul]
        have h1 := hDom τ hτp hττ₀ z
        have h2 := hfb z
        have hg0 := gaussDdim_nonneg (lam * τ) z
        have hstep : |H τ z| * |f z| ≤ (CW * gaussDdim (lam * τ) z) * Cf :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCW hg0)
        calc |H τ z| * |f z| ≤ (CW * gaussDdim (lam * τ) z) * Cf := hstep
          _ = CW * Cf * gaussDdim (lam * τ) z := by ring
    _ = CW * Cf * ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ, gaussDdim (lam * τ) z := by
        rw [integral_const_mul]

/-! ### (G) — the `hGgate` reduction from external gate-activation facts. -/

/-- **★ (G) `hGgate_of_gate_activation` — THE `hGgate` REDUCTION.**  If the ball of radius `rS` sits
    inside `K` and the gate is active there (`0 ∈ S z` for `z ∈ ball 0 rS`), then for any smaller
    radius `ρ ≤ rS` the `v3` gate-activation predicate holds on `ball 0 ρ`.  This is what a `ρcap ≤ rS`
    cap buys, discharging `hGgate` from the honest external carries.  NOT `a₁ = R/6`. -/
theorem hGgate_of_gate_activation (S : Point n → Set (Point n)) {K : Set (Point n)}
    (ρ rS : ℝ) (hρrS : ρ ≤ rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ S z) :
    ∀ z ∈ Metric.ball (0 : Point n) ρ, z ∈ K ∧ (0 : Point n) ∈ S z := by
  intro z hz
  have hzrS : z ∈ Metric.ball (0 : Point n) rS := Metric.ball_subset_ball hρrS hz
  exact ⟨hKball hzrS, hSact z hzrS⟩

/-! ### (F) — the fixed-`f` FINAL approximate identity. -/

/-- **★★ `chartImage_approx_identity_final` — THE FIXED-`f` FINAL.**  `chartImage_approx_identity_v3`
    with BOTH structural carries eliminated.  From the standing geometry `(hC, hK, K ∈ 𝓝 0)`, the metric
    carries `{hg, hgi, hgpos}`, the gauge `det g 0 = 1`, `0 < a < b`, and `f` measurable + globally
    bounded + continuous at `0`, PLUS
      • the gate carries at an external radius `rS`  (`0 < rS`, `ball 0 rS ⊆ K`, `∀ z ∈ ball 0 rS,
        0 ∈ S z`)  — discharge `hGgate` (obstruction (i)), satisfiable via the openness exports;
      • the witness-slice measurability `hWslice`  — for the split's integrability;
      • the zeroth wide domination `hDom` (`0 < lam`, `0 < τ₀`, `0 ≤ C`)  — the annulus split
        (obstruction (ii)), satisfiable via `zeroth_domination_global` —
    there EXISTS a CoV radius `ρ > 0` such that the boundary witness sampled against `f` concentrates
    at `f 0`:
        `Tendsto (fun τ => ∫ z, Wit τ 0 z · f z) (𝓝[>]0) (𝓝 (f 0))`.
    NO `hGgate`, NO `hSupp`.

    ROUTE.  Cap the enriched bundle at `min ρA rS` (`ρ ≤ ρA` keeps the amplitude/Jacobian route;
    `ρ ≤ rS` discharges `hGgate` via `hGgate_of_gate_activation`).  Rebuild `hbound`/`hlocal`/`hmeas`
    exactly as `v3`, get the Layer-C moving approximate identity `base`; the ON-ball limit is
    `base.congr'` through the on-gate factorisation + chart change of variables; the OFF-ball limit is
    `offBall_integral_tendsto_zero` at the concrete witness; recombine per `τ` via `integral_add_compl`
    (integrability from the global domination + `hWslice`).  ⚠ NOT `a₁ = R/6`. -/
theorem chartImage_approx_identity_final
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1)
    (f : Point n → ℝ) (hf_meas : Measurable f)
    (hf_bdd : ∃ Cf : ℝ, ∀ x, |f x| ≤ Cf)
    (hf_cont : ContinuousAt f 0)
    -- gate-activation carries (discharge `hGgate`):
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ S z)
    -- witness-slice measurability (for the split's integrability):
    (hWslice : ∀ τ : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z) volume)
    -- zeroth wide domination (discharge `hSupp` by the annulus split):
    (lam τ₀ CW : ℝ) (hlam : 0 < lam) (hτ₀ : 0 < τ₀) (hCW : 0 ≤ CW)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z) :
    ∃ ρ > (0 : ℝ),
      Tendsto (fun τ => ∫ z, vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
        (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
  have h0K : (0 : Point n) ∈ K := mem_of_mem_nhds h0Kmem
  obtain ⟨Cf, hCf⟩ := hf_bdd
  have hCf0 : (0 : ℝ) ≤ Cf := le_trans (abs_nonneg _) (hCf 0)
  -- Amplitude sup-bound with a radius `ρA`.
  obtain ⟨ρA, hρA, CA, hCA⟩ :=
    QIQTH.BaseSlotAmplitude.baseSlotAmp_bound g gi hC hK h0Kmem hg hgi hgpos a b 1
  -- Enriched bundle capped at `min ρA rS`.
  have hρcap : 0 < min ρA rS := lt_min hρA hrS
  obtain ⟨ρ, hρ, hρcaple, V, f', _hballmeas, hfd, hinj, hV, hJpos, hΩnhds,
      hVcont, _hΩopen, hV0, hf'eq, hdetlb, hdetcont, hdetval⟩ :=
    QIQTH.EnrichedChartBundle.enrichedChartBundle g gi hC hK h0Kmem (min ρA rS) hρcap
  have hρρA : ρ ≤ ρA := le_trans hρcaple (min_le_left _ _)
  have hρrS : ρ ≤ rS := le_trans hρcaple (min_le_right _ _)
  refine ⟨ρ, hρ, ?_⟩
  -- (i) discharge `hGgate` on the produced ball.
  have hGgate : ∀ z ∈ Metric.ball (0 : Point n) ρ, z ∈ K ∧ (0 : Point n) ∈ S z :=
    hGgate_of_gate_activation S ρ rS hρrS hKball hSact
  -- Chart-image measurability, `V`-maps, `0 ∈ Ω`, inverse limits (verbatim `v3`).
  have hΩmeas : MeasurableSet
      ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ)) :=
    QIQTH.FixedFChartImageAI.chartImage_measurableSet_of_bundle g gi hC hK ρ f' hfd hinj
  have hmeas :=
    QIQTH.FixedFTrioDischarge.chartImage_trio_hmeas g gi hC hK hg hgi hgpos a b f hf_meas ρ V f'
      hfd hinj hV
  have hVmaps : ∀ w ∈ (fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ,
      V w ∈ Metric.ball (0 : Point n) ρ := by
    intro w hw; obtain ⟨z, hz, rfl⟩ := hw; rw [hV z hz]; exact hz
  have h0Ω : (0 : Point n) ∈
      (fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ :=
    ⟨0, Metric.mem_ball_self hρ, uniformInverseChart_zero g gi hC hK h0K⟩
  have hVto0 := QIQTH.EnrichedChartBundle.bundleV_tendsto_zero V
    ((fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ)
    hVcont h0Ω hV0
  have hdet1 := QIQTH.EnrichedChartBundle.bundleDet_tendsto_one g gi hC hK ρ V f'
    hVmaps hf'eq hVto0 hdetcont hdetval
  -- `hbound` (verbatim `v3`, `hρcaple` → `hρρA`).
  have hbound : ∃ C, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂(volume.restrict
          ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))),
        ‖chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|‖ ≤ C := by
    have hCA0 : (0 : ℝ) ≤ CA :=
      le_trans (abs_nonneg _)
        (hCA 0 ⟨le_refl 0, zero_le_one⟩ 0 (Metric.mem_closedBall_self hρA.le))
    have hτicc : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 := by
      have hIio : Set.Iio (1 : ℝ) ∈ 𝓝[>] (0 : ℝ) :=
        nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
      filter_upwards [self_mem_nhdsWithin, hIio] with τ hτpos hτlt
      exact ⟨le_of_lt hτpos, le_of_lt hτlt⟩
    refine ⟨2 * CA * Cf, ?_⟩
    filter_upwards [hτicc] with τ hτ
    refine (ae_restrict_iff' hΩmeas).mpr (Filter.Eventually.of_forall (fun w => ?_))
    intro hwΩ
    have hVwball : V w ∈ Metric.ball (0 : Point n) ρ := hVmaps w hwΩ
    have hVwcball : V w ∈ Metric.closedBall (0 : Point n) ρA :=
      (Metric.ball_subset_closedBall.trans
        (Metric.closedBall_subset_closedBall hρρA)) hVwball
    have hampb : |chartFieldAmp g gi hC hK a b τ (V w) 0| ≤ CA := hCA τ hτ (V w) hVwcball
    have hfb : |f (V w)| ≤ Cf := hCf (V w)
    have hdetb : (1 : ℝ) / 2 < |(f' (V w)).det| := hdetlb (V w) hVwball
    have hdetpos : (0 : ℝ) < |(f' (V w)).det| := lt_trans (by norm_num) hdetb
    have h1 : |chartFieldAmp g gi hC hK a b τ (V w) 0| * |f (V w)| ≤ CA * Cf :=
      mul_le_mul hampb hfb (abs_nonneg _) hCA0
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_abs, div_le_iff₀ hdetpos]
    nlinarith [h1, hdetb, mul_nonneg hCA0 hCf0]
  -- `hlocal` (verbatim `v3`).
  have hlocal : ∀ ε > 0, ∃ r > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂(volume.restrict
          ((fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ))),
        ‖w‖ < r →
          ‖chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det| - f 0‖ < ε := by
    obtain ⟨_ρ0, _hρ0, hAjoint⟩ :=
      QIQTH.BaseSlotAmplitude.baseSlotAmp_joint_limit g gi hC hK h0Kmem hg hgi hgpos a b
    have hA0 : chartFieldAmp g gi hC hK a b 0 0 0 = 1 :=
      QIQTH.FixedFTrioDischarge.baseChartAmp_centre_eq_one g gi hC hK h0K a b ha hab hgdet0
    have hGto : Tendsto (fun p : ℝ × Point n =>
        chartFieldAmp g gi hC hK a b p.1 (V p.2) 0 * f (V p.2) / |(f' (V p.2)).det|)
        ((𝓝[>] (0 : ℝ)) ×ˢ
          (𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
            (0 : Point n)))
        (𝓝 (f 0)) := by
      have hamp : Tendsto
          (fun p : ℝ × Point n => chartFieldAmp g gi hC hK a b p.1 (V p.2) 0)
          ((𝓝[>] (0 : ℝ)) ×ˢ
            (𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
              (0 : Point n)))
          (𝓝 1) := by
        have h := hAjoint.comp (tendsto_id.prodMap hVto0)
        rw [hA0] at h
        exact h
      have hfV : Tendsto (fun p : ℝ × Point n => f (V p.2))
          ((𝓝[>] (0 : ℝ)) ×ˢ
            (𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
              (0 : Point n)))
          (𝓝 (f 0)) :=
        ((hf_cont.tendsto).comp hVto0).comp tendsto_snd
      have hdetV : Tendsto (fun p : ℝ × Point n => |(f' (V p.2)).det|)
          ((𝓝[>] (0 : ℝ)) ×ˢ
            (𝓝[(fun z => uniformInverseChart g gi hC hK z 0) '' Metric.ball (0 : Point n) ρ]
              (0 : Point n)))
          (𝓝 1) := hdet1.comp tendsto_snd
      have hmul := (hamp.mul hfV).div hdetV one_ne_zero
      rw [one_mul, div_one] at hmul
      exact hmul
    intro ε hε
    have hnhd : Metric.ball (f 0) ε ∈ 𝓝 (f 0) := Metric.ball_mem_nhds _ hε
    have hpre := hGto.eventually hnhd
    rw [eventually_prod_iff] at hpre
    obtain ⟨pa, hpa, pb, hpb, hcomb⟩ := hpre
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hpb
    obtain ⟨r, hr, hrsub⟩ := hpb
    refine ⟨r, hr, ?_⟩
    filter_upwards [hpa] with τ hτpa
    refine (ae_restrict_iff' hΩmeas).mpr (Filter.Eventually.of_forall (fun w => ?_))
    intro hwΩ hwr
    have hwpb : pb w := hrsub ⟨mem_ball_zero_iff.mpr hwr, hwΩ⟩
    have hin : chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|
        ∈ Metric.ball (f 0) ε := hcomb hτpa hwpb
    rw [Metric.mem_ball, Real.dist_eq] at hin
    rw [Real.norm_eq_abs]
    exact hin
  -- Layer C: the moving approximate identity over `Ω`.
  have base := QIQTH.ChartImageApproxIdentity.gaussDdim_set_approx_identity_moving
    (n := n) hΩmeas hΩnhds hmeas hbound hlocal
  -- The ON-ball slice equation (factorisation on the ball + chart change of variables).
  have heqBall : ∀ τ : ℝ,
      (∫ z in Metric.ball (0 : Point n) ρ,
          vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
        = ∫ w in (fun z => uniformInverseChart g gi hC hK z 0) '' (Metric.ball (0 : Point n) ρ),
            gaussDdim τ w
              * (chartFieldAmp g gi hC hK a b τ (V w) 0 * f (V w) / |(f' (V w)).det|) := by
    intro τ
    have hfac : (∫ z in Metric.ball (0 : Point n) ρ,
          vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
        = ∫ z in Metric.ball (0 : Point n) ρ,
            gaussDdim τ (uniformInverseChart g gi hC hK z 0)
              * (chartFieldAmp g gi hC hK a b τ z 0 * f z) := by
      refine setIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
      obtain ⟨hzK, h0S⟩ := hGgate z hz
      rw [QIQTH.WideWitnessAmplitude.witness_zero_eq_gauss_mul_amp g gi hC hK S a b τ hzK h0S]
      ring
    rw [hfac]
    exact QIQTH.ChartGaussianChangeVar.chart_gaussian_change_variables
      τ (Metric.ball (0 : Point n) ρ) (fun z => uniformInverseChart g gi hC hK z 0) V f'
      (fun z => |(f' z).det|) (fun z => chartFieldAmp g gi hC hK a b τ z 0 * f z)
      measurableSet_ball hfd hinj hV (fun _ _ => rfl) hJpos
  have hOn : Tendsto (fun τ => ∫ z in Metric.ball (0 : Point n) ρ,
      vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
      (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
    base.congr' (Filter.Eventually.of_forall (fun τ => (heqBall τ).symm))
  -- (ii) the OFF-ball limit at the concrete witness.
  have hOff : Tendsto (fun τ => ∫ z in (Metric.ball (0 : Point n) ρ)ᶜ,
      vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    offBall_integral_tendsto_zero
      (fun τ z => vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z) f
      ρ lam CW Cf τ₀ hρ hlam hCW hτ₀ hCf hDom
  -- Per-`τ` recombination via `integral_add_compl` (integrability from global domination + `hWslice`).
  have hsplitEv : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
      (∫ z in Metric.ball (0 : Point n) ρ,
          vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
        + (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ,
            vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
        = ∫ z, vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z := by
    have hcap : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ ≤ τ₀ := by
      have hIio : Set.Iio τ₀ ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds hτ₀)
      filter_upwards [hIio] with τ hτ
      exact le_of_lt hτ
    filter_upwards [self_mem_nhdsWithin, hcap] with τ hτpos hττ₀
    have hτp : 0 < τ := Set.mem_Ioi.mp hτpos
    have hInt : Integrable
        (fun z => vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z) volume := by
      refine Integrable.mono'
        ((QIQTH.HeatResidualBound.gaussDdim_integrable (lam * τ) (mul_pos hlam hτp)).const_mul
          (CW * Cf))
        ((hWslice τ).mul hf_meas.aestronglyMeasurable)
        (ae_of_all _ (fun z => ?_))
      simp only [Real.norm_eq_abs, abs_mul]
      have h1 := hDom τ hτp hττ₀ z
      have h2 := hCf z
      have hg0 := gaussDdim_nonneg (lam * τ) z
      have hstep : |vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z| * |f z|
          ≤ (CW * gaussDdim (lam * τ) z) * Cf :=
        mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCW hg0)
      calc |vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z| * |f z|
          ≤ (CW * gaussDdim (lam * τ) z) * Cf := hstep
        _ = CW * Cf * gaussDdim (lam * τ) z := by ring
    exact integral_add_compl measurableSet_ball hInt
  -- Recombine.
  have hfin : Tendsto (fun τ =>
      (∫ z in Metric.ball (0 : Point n) ρ,
          vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z)
        + (∫ z in (Metric.ball (0 : Point n) ρ)ᶜ,
            vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z * f z))
      (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
    have h := hOn.add hOff
    rwa [add_zero] at h
  exact hfin.congr' hsplitEv

end QIQTH.GateAnnulusSplit

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.GateAnnulusSplit
#print axioms offBall_integral_tendsto_zero
#print axioms hGgate_of_gate_activation
#print axioms chartImage_approx_identity_final
end AxiomChecks
