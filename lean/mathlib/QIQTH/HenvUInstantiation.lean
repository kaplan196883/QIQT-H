/-
  HenvUInstantiation — J4-164: assembling the x-UNIFORM bare Gaussian envelope family `henvU`
  (and the `∀ᵐ s → ∀ᶠ x` variant `henv`) consumed by the L1 G2-bundle discharge for the concrete
  first-derivative kernel `dH := witnessFieldDeriv` of the gated `N = 1` van-Vleck witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It ASSEMBLES the
  x-uniform bare-kernel Gaussian envelope families that `G2CarryDischarge.hdomS_from_uniform` (carry
  `henvU`) and `WitnessDerivDomination.hzbound_witness` (carry `henv`) consume, from two honest,
  strictly-lighter ingredients: (i) the x-free on-gate coercive Gaussian bound
  `G2CarryDischarge.witnessFieldDeriv_gate_envelope_coercive`, and (ii) the off-gate identical
  vanishing `EngineInstantiation.witnessFieldDeriv_offGate_eq_zero` (`z ∉ K ⟹ dH ≡ 0` for ALL `x`).
  Never the conclusion.

  ── WHAT IS PROVED HERE (axiom-free, no `sorry`).

    ● THE OFF-GATE `pd`-VANISHING LEVER (clean standalone, reusable).
      • `pd_eq_zero_of_line_eventuallyEq_zero` — if the `i`-th coordinate line
          `w ↦ f (update x i w)` is `=ᶠ[𝓝 (x i)] 0`, then `pd f i x = 0` (`pd` is the line `deriv`;
          `Filter.EventuallyEq.deriv_eq` + `deriv_const`).  A neighbourhood-vanishing, not a
          point-vanishing, lever — the honest requirement for an x-DERIVATIVE.
      • `pd_eq_zero_of_eventuallyEq_zero` — the full-neighbourhood corollary: `f =ᶠ[𝓝 x] 0 ⟹
          pd f i x = 0` (pull the germ back along the continuous line map `w ↦ update x i w`, which
          sends `x i ↦ x`).

    ● THE x-UNIFORM ENVELOPE ASSEMBLY (real assembly for `henvU` / `henv`).
      • `henvU_assembled` — ★ THE `∀ᶠ x → ∀ᵐ s → ∀ᵐ z` ENVELOPE.  From an x-uniform on-gate/off-gate
          DICHOTOMY carry `hGateData` (for a.e. `z`, EITHER `z ∉ K`, OR the full per-`(x,z)` gate +
          jet + amplitude-bound + chart-coercivity data of `witnessFieldDeriv_gate_envelope_coercive`
          holds with the fixed sup-bounds `Bs`/`Ba`/`Bd`), the exact `henvU` slot of
          `hdomS_from_uniform` (constant `C₀ = (Bs·Ba+Bd)·(√2)ⁿ`, width `κ·(t−s)` with `κ = 2`)
          follows: off-gate the kernel is `0 ≤` the envelope, on-gate the coercive bound gives it.
          The width positivity `t − s > 0` uses `s ∈ Ι 0 t` (`s ≤ t`) a.e.-refined by `s ≠ t` (`{t}`
          null).
      • `henv_assembled` — the `∀ᵐ s → ∀ᶠ x → ∀ᵐ z` variant (the exact `henv` slot of
          `hzbound_witness`), from the correspondingly-ordered dichotomy carry `hGateData'`.  The two
          orders are genuinely distinct (no free Fubini swap), so each is assembled from its own
          honest carry.

    ● THE CAPSTONE COMPOSITIONS.
      • `hdomS_assembled` — feeds `henvU_assembled` through `hdomS_from_uniform` to produce the exact
          `hdomS` slot of the G2 bundle (F-weighted, `‖dH·F‖ ≤ (C₀·Cf)·G_{2(t−s)}(z)`), reducing the
          L1 residue on this leg to `{hGateData, hFbd}`.
      • `hzbound_assembled` — feeds `henv_assembled` through `hzbound_witness` to produce the exact
          `hzbound` slot (same dominator), reducing that leg to `{hGateData', hFbd}`.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hGateData` / `hGateData'` — the x-uniform on-gate/off-gate DICHOTOMY families.  SATISFIABLE:
        · the off-gate disjunct `z ∉ K` is a real set membership (kills the witness for ALL `x`);
        · the on-gate disjunct bundles EXACTLY the hypotheses `witnessFieldDeriv_gate_envelope_coercive`
          consumes — the gate `z ∈ K ∧ IsOpen (S z) ∧ x ∈ S z`, the field jet `hJetV` (banked at the
          assembly centre via `EngineInstantiation`/`chartField_firstJet_center`), the amplitude
          `PdiffAt` `hAmp1`, the fixed factor sup-bounds `Bs`/`Ba`/`Bd` (E2 data), and the chart
          COERCIVITY `½·r²_z ≤ r²_{W z x}`.  The coercivity is banked base-uniformly at FIELD POINT
          `0` (`InverseChartDisplacement.chartW0_nearIsometry`, `c = 1/2`, `∀ z ∈ K ∩ ball 0 r`); it
          is NOT ball-uniform in the FIELD point `x` as banked (banked only at `x = 0`), so the
          field-uniform coercivity is carried inside the dichotomy (satisfiable exactly at the
          assembly centre `x₀ = 0`, extended over the field neighbourhood).  NON-VACUOUS (the on-gate
          disjunct is inhabited on the gate) and NEVER the conclusion (the conclusion is the ENVELOPE
          BOUND, not the gate data).
    • `hcoef : 0 ≤ Bs·Ba+Bd` — the off-gate nonnegativity of the constant factor; trivially
        satisfiable (`Bs`/`Ba`/`Bd` are sup-norms).
    • `hFbd : |F| ≤ Cf` — the scalar `F`-sup-bound, a property of the source term.

  NO `sorry`.  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.G2CarryDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.WitnessDerivDomination QIQTH.G2CarryDischarge
open scoped Interval Topology BigOperators

namespace QIQTH.HenvUInstantiation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### THE OFF-GATE `pd`-VANISHING LEVER (clean standalone, reusable).
    ############################################################################### -/

/-- **★ `pd_eq_zero_of_line_eventuallyEq_zero`.**  THE `pd`-VANISHING LEVER.  If the `i`-th coordinate
    line `w ↦ f (Function.update x i w)` is `=ᶠ[𝓝 (x i)] 0` (vanishes on a NEIGHBOURHOOD of `x i`, not
    just at the point), then the coordinate partial `pd f i x = 0`.  `pd` is exactly the line `deriv`
    (`pd f i x = deriv (fun w ↦ f (update x i w)) (x i)`), so `Filter.EventuallyEq.deriv_eq` transfers
    to `deriv 0 = 0`.  The honest lever for an x-DERIVATIVE vanishing (point-vanishing is not enough).
    NOT `a₁ = R/6`. -/
theorem pd_eq_zero_of_line_eventuallyEq_zero (f : Point n → ℝ) (i : Fin n) (x : Point n)
    (hf : (fun w => f (Function.update x i w)) =ᶠ[𝓝 (x i)] (fun _ => (0 : ℝ))) :
    pd f i x = 0 := by
  simp only [pd]
  rw [hf.deriv_eq, deriv_const]

/-- **`pd_eq_zero_of_eventuallyEq_zero`.**  The full-neighbourhood corollary of the lever: if `f`
    vanishes on a neighbourhood of `x` in `Point n` (`f =ᶠ[𝓝 x] 0`), then `pd f i x = 0`.  The germ is
    pulled back along the continuous coordinate-line map `w ↦ Function.update x i w`, which sends
    `x i ↦ Function.update x i (x i) = x`.  NOT `a₁ = R/6`. -/
theorem pd_eq_zero_of_eventuallyEq_zero (f : Point n → ℝ) (i : Fin n) (x : Point n)
    (hf : f =ᶠ[𝓝 x] (fun _ => (0 : ℝ))) :
    pd f i x = 0 := by
  refine pd_eq_zero_of_line_eventuallyEq_zero f i x ?_
  have htend : Tendsto (fun w : ℝ => Function.update x i w) (𝓝 (x i)) (𝓝 x) := by
    have hc := ((hasDerivAt_update x i (x i)).continuousAt).tendsto
    rwa [Function.update_eq_self] at hc
  exact htend.eventually hf

/-! ###############################################################################
    ### THE x-UNIFORM ENVELOPE ASSEMBLY (real assembly for `henvU` / `henv`).
    ############################################################################### -/

/-- **★ `henvU_assembled`.**  THE `∀ᶠ x → ∀ᵐ s → ∀ᵐ z` x-UNIFORM BARE ENVELOPE — the exact `henvU`
    slot of `G2CarryDischarge.hdomS_from_uniform`, with constant `C₀ = (Bs·Ba+Bd)·(√2)ⁿ` and width
    `2·(t−s)` (`κ = 2`).  Assembled from the x-uniform on-gate/off-gate DICHOTOMY carry `hGateData`:
    for a.e. `z`, EITHER `z ∉ K` (the witness is identically `0` in the field slot, so `dH ≡ 0 ≤`
    envelope, via `witnessFieldDeriv_offGate_eq_zero`), OR the full per-`(x,z)` gate/jet/amplitude/
    coercivity data of `witnessFieldDeriv_gate_envelope_coercive` holds with the fixed sup-bounds
    `Bs`/`Ba`/`Bd` (giving the on-gate coercive envelope).  Width positivity `t − s > 0` from
    `s ∈ Ι 0 t` (`s ≤ t`) refined a.e. by `s ≠ t` (`{t}` is null).  NOT `a₁ = R/6`. -/
theorem henvU_assembled (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ht : 0 < t) (u : Set (Point n)) (Bs Ba Bd : ℝ) (hcoef : 0 ≤ Bs * Ba + Bd)
    (hGateData : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂(volume : Measure ℝ),
        s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∉ K ∨
          (∃ Pval : Fin n → ℝ,
            z ∈ K ∧ IsOpen (S z) ∧ x ∈ S z ∧
            (∀ k, HasDerivAt
              (fun r : ℝ => uniformInverseChart g gi hC hK z (Function.update x i r) k) (Pval k)
              (x i)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i x ∧
            |(-(∑ k, uniformInverseChart g gi hC hK z x k * Pval k) / (2 * (t - s)))| ≤ Bs ∧
            |chartFieldAmp g gi hC hK a b (t - s) z x| ≤ Ba ∧
            |pd (chartFieldAmp g gi hC hK a b (t - s) z) i x| ≤ Bd ∧
            (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z x))) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂(volume : Measure ℝ),
      s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
        |witnessFieldDeriv g gi hC hK S a b i (t - s) x z|
          ≤ ((Bs * Ba + Bd) * (Real.sqrt 2) ^ n) * gaussDdim (2 * (t - s)) z := by
  intro x₀ hx₀ i
  have hane : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext a; simp
    rw [hset]; exact Real.volume_singleton
  filter_upwards [hGateData x₀ hx₀ i] with x hx
  filter_upwards [hx, hane] with s hs hsne hmem
  have hmem' := hmem
  rw [Set.uIoc_of_le ht.le] at hmem'
  have hst : s < t := lt_of_le_of_ne hmem'.2 hsne
  have hτ : 0 < t - s := by linarith
  filter_upwards [hs hmem] with z hdich
  rcases hdich with hznk | ⟨Pval, hz, hSopen, hp, hJetV, hAmp1, hSc, hBa, hBd, hmin⟩
  · -- off gate: the witness is identically `0` in the field slot, so `dH = 0 ≤` envelope.
    rw [witnessFieldDeriv_offGate_eq_zero g gi hC hK S a b i (t - s) x z hznk, abs_zero]
    have hGnn : 0 ≤ gaussDdim (2 * (t - s)) z := gaussDdim_nonneg _ _
    exact mul_nonneg (mul_nonneg hcoef (pow_nonneg (Real.sqrt_nonneg 2) n)) hGnn
  · -- on gate: the coercive Gaussian bound.
    exact witnessFieldDeriv_gate_envelope_coercive g gi hC hK S a b i (t - s) hτ z hz hSopen x hp
      Pval hJetV hAmp1 Bs Ba Bd hSc hBa hBd hmin

/-- **`henv_assembled`.**  THE `∀ᵐ s → ∀ᶠ x → ∀ᵐ z` variant — the exact `henv` slot of
    `WitnessDerivDomination.hzbound_witness` (same constant/width), assembled from the
    correspondingly-ordered on-gate/off-gate dichotomy carry `hGateData'`.  The `∀ᶠ x → ∀ᵐ s` and
    `∀ᵐ s → ∀ᶠ x` orders are genuinely distinct (no free Fubini swap), so each variant is assembled
    from its own honest carry.  NOT `a₁ = R/6`. -/
theorem henv_assembled (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ht : 0 < t) (u : Set (Point n)) (Bs Ba Bd : ℝ) (hcoef : 0 ≤ Bs * Ba + Bd)
    (hGateData' : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂(volume : Measure ℝ),
        s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∉ K ∨
          (∃ Pval : Fin n → ℝ,
            z ∈ K ∧ IsOpen (S z) ∧ x ∈ S z ∧
            (∀ k, HasDerivAt
              (fun r : ℝ => uniformInverseChart g gi hC hK z (Function.update x i r) k) (Pval k)
              (x i)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i x ∧
            |(-(∑ k, uniformInverseChart g gi hC hK z x k * Pval k) / (2 * (t - s)))| ≤ Bs ∧
            |chartFieldAmp g gi hC hK a b (t - s) z x| ≤ Ba ∧
            |pd (chartFieldAmp g gi hC hK a b (t - s) z) i x| ≤ Bd ∧
            (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z x))) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 t →
      ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
        |witnessFieldDeriv g gi hC hK S a b i (t - s) x z|
          ≤ ((Bs * Ba + Bd) * (Real.sqrt 2) ^ n) * gaussDdim (2 * (t - s)) z := by
  intro x₀ hx₀ i
  have hane : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
    rw [ae_iff]
    have hset : {a : ℝ | ¬ a ≠ t} = {t} := by ext a; simp
    rw [hset]; exact Real.volume_singleton
  filter_upwards [hGateData' x₀ hx₀ i, hane] with s hs hsne hmem
  have hmem' := hmem
  rw [Set.uIoc_of_le ht.le] at hmem'
  have hst : s < t := lt_of_le_of_ne hmem'.2 hsne
  have hτ : 0 < t - s := by linarith
  filter_upwards [hs hmem] with x hx
  filter_upwards [hx] with z hdich
  rcases hdich with hznk | ⟨Pval, hz, hSopen, hp, hJetV, hAmp1, hSc, hBa, hBd, hmin⟩
  · rw [witnessFieldDeriv_offGate_eq_zero g gi hC hK S a b i (t - s) x z hznk, abs_zero]
    have hGnn : 0 ≤ gaussDdim (2 * (t - s)) z := gaussDdim_nonneg _ _
    exact mul_nonneg (mul_nonneg hcoef (pow_nonneg (Real.sqrt_nonneg 2) n)) hGnn
  · exact witnessFieldDeriv_gate_envelope_coercive g gi hC hK S a b i (t - s) hτ z hz hSopen x hp
      Pval hJetV hAmp1 Bs Ba Bd hSc hBa hBd hmin

/-! ###############################################################################
    ### THE CAPSTONE COMPOSITIONS — concrete `hdomS` / `hzbound`.
    ############################################################################### -/

/-- **★ `hdomS_assembled`.**  THE CONCRETE `hdomS` SLOT of the G2 bundle for `dH := witnessFieldDeriv`,
    obtained by feeding `henvU_assembled` (κ = 2, C₀ = (Bs·Ba+Bd)·(√2)ⁿ) through
    `G2CarryDischarge.hdomS_from_uniform` with the scalar `F`-sup-bound `hFbd`.  The `hdomS` leg is
    thereby reduced to `{hGateData, hFbd}` — the x-uniform dichotomy + the source-term bound.  NOT
    `a₁ = R/6`. -/
theorem hdomS_assembled (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ht : 0 < t) (F : ℝ → Point n → ℝ) (u : Set (Point n))
    (Bs Ba Bd Cf : ℝ) (hcoef : 0 ≤ Bs * Ba + Bd)
    (hFbd : ∀ s z, |F s z| ≤ Cf)
    (hGateData : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂(volume : Measure ℝ),
        s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∉ K ∨
          (∃ Pval : Fin n → ℝ,
            z ∈ K ∧ IsOpen (S z) ∧ x ∈ S z ∧
            (∀ k, HasDerivAt
              (fun r : ℝ => uniformInverseChart g gi hC hK z (Function.update x i r) k) (Pval k)
              (x i)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i x ∧
            |(-(∑ k, uniformInverseChart g gi hC hK z x k * Pval k) / (2 * (t - s)))| ≤ Bs ∧
            |chartFieldAmp g gi hC hK a b (t - s) z x| ≤ Ba ∧
            |pd (chartFieldAmp g gi hC hK a b (t - s) z) i x| ≤ Bd ∧
            (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z x))) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ᵐ s ∂(volume : Measure ℝ),
      s ∈ Set.uIoc 0 t → ∀ᵐ z ∂(volume : Measure (Point n)),
        ‖witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z‖
          ≤ (((Bs * Ba + Bd) * (Real.sqrt 2) ^ n) * Cf) * gaussDdim (2 * (t - s)) z :=
  hdomS_from_uniform g gi hC hK S a b t F u 2 ((Bs * Ba + Bd) * (Real.sqrt 2) ^ n) Cf
    (mul_nonneg hcoef (pow_nonneg (Real.sqrt_nonneg 2) n)) hFbd
    (henvU_assembled g gi hC hK S a b t ht u Bs Ba Bd hcoef hGateData)

/-- **`hzbound_assembled`.**  THE CONCRETE `hzbound` SLOT for `dH := witnessFieldDeriv`, obtained by
    feeding `henv_assembled` through `WitnessDerivDomination.hzbound_witness` with the scalar
    `F`-sup-bound `hFbd`.  The `hzbound` leg is thereby reduced to `{hGateData', hFbd}`.  NOT
    `a₁ = R/6`. -/
theorem hzbound_assembled (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (ht : 0 < t) (F : ℝ → Point n → ℝ) (u : Set (Point n))
    (Bs Ba Bd Cf : ℝ) (hcoef : 0 ≤ Bs * Ba + Bd)
    (hFbd : ∀ s z, |F s z| ≤ Cf)
    (hGateData' : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂(volume : Measure ℝ),
        s ∈ Set.uIoc 0 t → ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          z ∉ K ∨
          (∃ Pval : Fin n → ℝ,
            z ∈ K ∧ IsOpen (S z) ∧ x ∈ S z ∧
            (∀ k, HasDerivAt
              (fun r : ℝ => uniformInverseChart g gi hC hK z (Function.update x i r) k) (Pval k)
              (x i)) ∧
            PdiffAt (chartFieldAmp g gi hC hK a b (t - s) z) i x ∧
            |(-(∑ k, uniformInverseChart g gi hC hK z x k * Pval k) / (2 * (t - s)))| ≤ Bs ∧
            |chartFieldAmp g gi hC hK a b (t - s) z x| ≤ Ba ∧
            |pd (chartFieldAmp g gi hC hK a b (t - s) z) i x| ≤ Bd ∧
            (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (uniformInverseChart g gi hC hK z x))) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.uIoc 0 t →
      ∀ᶠ x in 𝓝 x₀, ∀ᵐ z ∂(volume : Measure (Point n)),
        ‖witnessFieldDeriv g gi hC hK S a b i (t - s) x z * F s z‖
          ≤ (((Bs * Ba + Bd) * (Real.sqrt 2) ^ n) * Cf) * gaussDdim (2 * (t - s)) z :=
  hzbound_witness g gi hC hK S a b t F volume u 2 ((Bs * Ba + Bd) * (Real.sqrt 2) ^ n) Cf
    (mul_nonneg hcoef (pow_nonneg (Real.sqrt_nonneg 2) n)) hFbd
    (henv_assembled g gi hC hK S a b t ht u Bs Ba Bd hcoef hGateData')

end QIQTH.HenvUInstantiation

section AxiomChecks
open QIQTH.HenvUInstantiation
#print axioms pd_eq_zero_of_line_eventuallyEq_zero
#print axioms pd_eq_zero_of_eventuallyEq_zero
#print axioms henvU_assembled
#print axioms henv_assembled
#print axioms hdomS_assembled
#print axioms hzbound_assembled
end AxiomChecks
