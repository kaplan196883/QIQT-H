/-
  BFGaussianEnvelopeClosed — J4-868: the GAUSSIAN-PEAK verdict for the field-Hessian envelope `BF`,
  closing the "compact-gate supremum" loop of `hFd` AND resolving the `uniform-in-z` subtlety that the
  step-4 target `BF s z ≤ C·gaussDdim (t−s) z` hides.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL on {hDuhamel, hDConv, hCConv}.  This brick takes the concrete per-entry
  chart-Gaussian field-Hessian envelope to the compact-gate supremum via the banked Gaussian-PEAK bound
  (`BoundaryAssembly.gaussDdim_le_diagonal`) and the J4-865/866 gate-compactness reductions, and it
  proves — rigorously — the exact `uniform-in-z` NO-GO that the naive step-4 target `BF ≤ C·gaussDdim z`
  runs into.  No `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, none equal
  to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE `uniform-in-z` FINDING (the subtlety the mission flagged as a vacuity trap).

  The per-entry pointwise envelopes (`SecondDerivEnvelope.witnessFieldDeriv2_gate_abs_le`, diagonal, and
  `WitnessMixedHessianMagnitudeBound.witnessMixed_gate_abs_le`, off-diagonal) carry the Gaussian factor
  `gaussDdim τ (uniformInverseChart z p)` at the FIELD point `p`.  The gate confines `p ∈ S z`, so the
  chart coordinate `uniformInverseChart z p` ranges over a BOUNDED ball INDEPENDENT of the base `z`.
  Hence the ONLY `z`-uniform bound on this Gaussian factor is its PEAK `gaussDdim τ 0` — a constant that
  does **NOT decay in `z`**.  The compact-gate supremum therefore delivers a bound of the shape
    `BF s z ≤ gaussDdim (t−s) 0 · (compact-gate polynomial sup)`
  whose Gaussian part is the `z`-uniform PEAK, NOT a `z`-decaying `gaussDdim (t−s) z`.

  `bf_no_uniform_gaussian_decay` PROVES that this peak CANNOT be upgraded to `C·gaussDdim (t−s) z` with
  any `z`-uniform constant `C`: the exact peak/point ratio is
    `gaussDdim t 0 = exp((∑ₖ (v k)²)/(4t)) · gaussDdim t v`   (`gaussDdim_peak_ratio`),
  and the prefactor `exp((∑ₖ (v k)²)/(4t)) → ∞` as `‖v‖ → ∞` (and as `t → 0⁺`).  So for any `C` there is
  a base point `z` with `C·gaussDdim (t−s) z < gaussDdim (t−s) 0` — the `z`-decaying uniform envelope is
  UNAVAILABLE.  This is precisely the vacuity trap gpt-5.6-sol flagged: had we asserted `BF ≤ C·gaussDdim
  (t−s) z` with uniform `C`, the hypothesis would have been UNSATISFIABLE at large `z`.  We do NOT assert
  it.  CONSEQUENCE: the `z`-mass `hzmass` (`∫z BL·BF ≤ C·(t−s)⁻¹`) must route through the COMPACT BASE
  SUPPORT of `BL·BF` (`HZMassIntegrabilityAttempt.productEnvelope_support_subset_K`, J4-867) — a
  pointwise-on-`K` estimate — NOT a naive `z`-decaying product envelope.

  ## WHAT LANDS (ns `QIQTH.BFGaussianEnvelopeClosed`).
    • `gaussDdim_peak_ratio` — ★ the EXACT peak/point ratio identity quantifying the blow-up.
    • `fieldHessian_peak_dominator_of_chart_dominator` — ★ the PEAK step: a chart-Gaussian entrywise
      dominator `gaussDdim τ (W z x)·Poly x` on the gate closure is `≤` the `z`-uniform-peak dominator
      `gaussDdim τ 0·Poly x` (via `gaussDdim_le_diagonal`, `Poly ≥ 0`).
    • `witnessFieldHessian_hFd_of_peak_dominator` — ★★★ the POSITIVE `hFd` `⨆`-reduction via J4-866,
      instantiated with the CONCRETE `z`-uniform-peak Gaussian dominator: `hFd` holds once the gate
      closure is compact and the field-Hessian is dominated on it by `gaussDdim (t−s) 0·Poly` with `Poly`
      continuous and `≥ 0`.  (Shows `hbdd` is dischargeable with a dominator whose GAUSSIAN factor is the
      `z`-uniform peak — no `z`-decay needed for `hbdd`, reinforcing the no-go.)
    • `bf_no_uniform_gaussian_decay` — ★★ the `uniform-in-z` NO-GO (the flagged subtlety), PROVED.
    • non-vacuity witnesses (empty gate; the peak ratio at `v = 0`).

  ⚠ HONEST RESIDUAL.  `hFd`'s `hbdd` is now reduced to the concrete peak dominator (boundary domination
  still carried, the J4-866 case-(b) residual); `hzmass` remains the deep wall, now KNOWN (via the no-go)
  to require the compact-base-support route, not a `z`-decaying envelope.  A full
  `MixedDirectionsFieldHessianEnvelope` instance additionally needs `hLevi`/`hkint`/`hbint`.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ChartJetXUniformBoundClosed
import QIQTH.HZMassIntegrabilityAttempt
import QIQTH.BoundaryAssembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.FlowJointContinuity
open QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.ChartJetXUniformBound QIQTH.ChartJetXUniformBoundClosed
open scoped Topology BigOperators

namespace QIQTH.BFGaussianEnvelopeClosed

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the EXACT Gaussian peak/point ratio (quantifies the `z`-blow-up).
    ############################################################################### -/

/-- **★ §A — `gaussDdim_peak_ratio`.**  The EXACT ratio of the peak `gaussDdim t 0` to the point value
    `gaussDdim t v`:
      `gaussDdim t 0 = Real.exp ((∑ₖ (v k)²)/(4t)) · gaussDdim t v`   (`0 < t`).
    Since `gaussDdim t w = (√(4πt))⁻ⁿ · exp(−(∑ (w k)²)/(4t))`, dividing the `w = 0` value by the
    `w = v` value leaves exactly `exp((∑ (v k)²)/(4t))`.  This prefactor `→ ∞` as `‖v‖ → ∞` (and as
    `t → 0⁺`), which is the analytic content of the `uniform-in-z` no-go below.  NOT `a₁ = R/6`. -/
theorem gaussDdim_peak_ratio {t : ℝ} (ht : 0 < t) (v : Point n) :
    gaussDdim t (0 : Point n)
      = Real.exp ((∑ k, (v k) ^ 2) / (4 * t)) * gaussDdim t v := by
  -- normal form `gaussDdim t w = (∏ (√)⁻¹) · exp(−(∑ (w k)²)/(4t))`.
  have key : ∀ w : Point n, gaussDdim t w
      = (∏ _k : Fin n, (Real.sqrt (4 * Real.pi * t))⁻¹)
          * Real.exp (-(∑ k, (w k) ^ 2) / (4 * t)) := by
    intro w
    simp only [gaussDdim, heatKernel1D]
    rw [Finset.prod_mul_distrib, ← Real.exp_sum]
    congr 1
    rw [← Finset.sum_neg_distrib, ← Finset.sum_div]
  rw [key v, key (0 : Point n)]
  have h0 : (∑ k, ((0 : Point n) k) ^ 2) = 0 := by simp
  rw [h0]
  have hexp0 : Real.exp (-(0 : ℝ) / (4 * t)) = 1 := by norm_num
  rw [hexp0, mul_one]
  -- `A = exp(S/4t) · (A · exp(−S/4t))` since `exp(S/4t)·exp(−S/4t) = 1`.
  set A := (∏ _k : Fin n, (Real.sqrt (4 * Real.pi * t))⁻¹) with hA
  set S := (∑ k, (v k) ^ 2) with hS
  have hcollapse : Real.exp (S / (4 * t)) * (A * Real.exp (-S / (4 * t))) = A := by
    rw [← mul_assoc, mul_comm (Real.exp (S / (4 * t))) A, mul_assoc, ← Real.exp_add,
        show S / (4 * t) + -S / (4 * t) = 0 by ring, Real.exp_zero, mul_one]
  rw [hcollapse]

/-! ###############################################################################
    ### §B — the PEAK step on the concrete chart-Gaussian entrywise dominator.
    ############################################################################### -/

/-- **★ §B — `fieldHessian_peak_dominator_of_chart_dominator`.**  The PEAK step: if on the gate closure
    the field-Hessian norm is dominated by the concrete CHART-Gaussian envelope
    `gaussDdim τ (uniformInverseChart z x) · Poly x` (the shape the diagonal + mixed per-entry envelopes
    produce through the CLM combinator, with `Poly` the entrywise polynomial), and `Poly ≥ 0`, then it is
    ALSO dominated by the `z`-uniform-PEAK envelope `gaussDdim τ 0 · Poly x` — via the pointwise peak
    bound `gaussDdim τ (W z x) ≤ gaussDdim τ 0` (`BoundaryAssembly.gaussDdim_le_diagonal`).  The Gaussian
    factor thereby becomes a `z`-uniform CONSTANT.  NOT `a₁ = R/6`. -/
theorem fieldHessian_peak_dominator_of_chart_dominator (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) {τ : ℝ} (hτ : 0 < τ) (z : Point n) (Poly : Point n → ℝ)
    (hPolynn : ∀ x, 0 ≤ Poly x)
    (hchart : ∀ x ∈ closure (S z),
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖
          ≤ gaussDdim τ (uniformInverseChart g gi hC hK z x) * Poly x) :
    ∀ x ∈ closure (S z),
      ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i τ y z) x‖
        ≤ gaussDdim τ (0 : Point n) * Poly x := by
  intro x hx
  refine le_trans (hchart x hx) ?_
  exact mul_le_mul_of_nonneg_right
    (gaussDdim_le_diagonal hτ (uniformInverseChart g gi hC hK z x)) (hPolynn x)

/-! ###############################################################################
    ### §C — the POSITIVE `hFd` reduction with the `z`-uniform-peak dominator.
    ############################################################################### -/

/-- **★★★ §C — `witnessFieldHessian_hFd_of_peak_dominator`.**  The EXACT `hFd` field of
    `MixedDirectionsFieldHessianEnvelope`, with the EXPLICIT envelope
    `BF s z := ⨆ x, ‖fderiv (y ↦ witnessFieldDeriv … (t−s) y z) x‖`, discharged a.e. from the two
    gate-geometry inputs, the dominator taken in the CONCRETE `z`-uniform-PEAK form:
      • `hcpt`  — a.e. `z`, the gate closure `closure (S z)` is COMPACT (concrete gate ⟹
                  `ChartJetXUniformBound.concreteGate_closure_isCompact`);
      • `hpeak` — a.e. `z`, there is a CONTINUOUS `Poly ≥ 0` with the field-Hessian norm `≤ gaussDdim
                  (t−s) 0 · Poly x` on `closure (S z)`.
    The dominator `x ↦ gaussDdim (t−s) 0 · Poly x` is continuous (constant Gaussian peak × continuous
    `Poly`), so `hbdd` follows from `bddAbove_fieldHessian_of_continuous_dominator` and the J4-866
    `⨆`-reduction fires.  KEY: the Gaussian factor here is the `z`-uniform PEAK, so `hbdd` needs NO
    `z`-decay — consistent with the no-go `bf_no_uniform_gaussian_decay`.  NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_hFd_of_peak_dominator (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ)
    (hcpt : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, IsCompact (closure (S z)))
    (hpeak : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∃ Poly : Point n → ℝ, Continuous Poly ∧
          ∀ x ∈ closure (S z),
            ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
              ≤ gaussDdim (t - s) (0 : Point n) * Poly x) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
          ≤ ⨆ x' : Point n,
              ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x'‖ := by
  refine witnessFieldHessian_hFd_ciSup_of_bddAbove g gi hC hK S a b i t m ?_
  filter_upwards [hcpt, hpeak] with s hcpts hpeaks hsUioc
  filter_upwards [hcpts hsUioc, hpeaks hsUioc] with z hzc hzp
  obtain ⟨Poly, hPolyC, hPolydom⟩ := hzp
  exact bddAbove_fieldHessian_of_continuous_dominator g gi hC hK S a b i (t - s) z
    (fun x => gaussDdim (t - s) (0 : Point n) * Poly x) hzc
    (continuous_const.mul hPolyC) hPolydom

/-! ###############################################################################
    ### §D — the `uniform-in-z` NO-GO (the flagged vacuity trap, PROVED).
    ############################################################################### -/

/-- **★★ §D — `bf_no_uniform_gaussian_decay`.**  THE `uniform-in-z` NO-GO.  For `n ≥ 1` and `0 < t`, the
    Gaussian PEAK `gaussDdim t 0` (the only `z`-uniform bound the compact-gate route yields for the
    field-Hessian's Gaussian factor) is NOT `≤ C·gaussDdim t z` uniformly in `z`: for EVERY `C`, there is
    a base point `z` with
      `C · gaussDdim t z < gaussDdim t 0`.
    Route: `gaussDdim_peak_ratio` gives `gaussDdim t 0 = exp((∑ (z k)²)/(4t))·gaussDdim t z`; choosing a
    single-coordinate `z` with `∑ (z k)² = 4t·(|C|+1)` makes the prefactor `exp(|C|+1) ≥ |C|+2 > C`,
    while `gaussDdim t z > 0`.  So the step-4 target `BF s z ≤ C·gaussDdim (t−s) z` with `z`-uniform `C`
    is UNAVAILABLE — asserting it would be an UNSATISFIABLE (vacuity-trap) hypothesis at large `z`.  The
    `z`-mass must instead use the compact base support of `BL·BF` (J4-867).  NOT `a₁ = R/6`. -/
theorem bf_no_uniform_gaussian_decay (hn : 0 < n) {t : ℝ} (ht : 0 < t) (C : ℝ) :
    ∃ z : Point n, C * gaussDdim t z < gaussDdim t (0 : Point n) := by
  set i0 : Fin n := ⟨0, hn⟩ with hi0
  set S₀ : ℝ := 4 * t * (|C| + 1) with hS0
  have hS0nn : 0 ≤ S₀ := by
    have : 0 ≤ |C| + 1 := by positivity
    positivity
  set r : ℝ := Real.sqrt S₀ with hr
  set z : Point n := Function.update (0 : Point n) i0 r with hz
  refine ⟨z, ?_⟩
  -- `∑ (z k)² = r² = S₀`.
  have hsum : (∑ k, (z k) ^ 2) = S₀ := by
    rw [hz]
    rw [Finset.sum_eq_single_of_mem i0 (Finset.mem_univ i0)]
    · rw [Function.update_self]
      rw [hr, Real.sq_sqrt hS0nn]
    · intro k _ hk
      rw [Function.update_of_ne hk]
      simp
  -- the ratio identity at `v = z`.
  have hratio : gaussDdim t (0 : Point n)
      = Real.exp (S₀ / (4 * t)) * gaussDdim t z := by
    rw [gaussDdim_peak_ratio ht z, hsum]
  -- the prefactor `exp(S₀/4t) = exp(|C|+1) > C`.
  have hexparg : S₀ / (4 * t) = |C| + 1 := by
    rw [hS0]; field_simp
  have hCexp : C < Real.exp (S₀ / (4 * t)) := by
    rw [hexparg]
    have h1 : |C| + 1 + 1 ≤ Real.exp (|C| + 1) := Real.add_one_le_exp (|C| + 1)
    have h2 : C ≤ |C| := le_abs_self C
    linarith
  have hgpos : 0 < gaussDdim t z := QIQTH.LeviSeries.gaussDdim_pos t ht z
  calc C * gaussDdim t z
      < Real.exp (S₀ / (4 * t)) * gaussDdim t z :=
        mul_lt_mul_of_pos_right hCexp hgpos
    _ = gaussDdim t (0 : Point n) := hratio.symm

/-! ###############################################################################
    ### §E — NON-VACUITY.
    ############################################################################### -/

/-- **Non-vacuity of the peak-ratio.**  At `v = 0` the ratio is `exp 0 = 1`, so `gaussDdim t 0 =
    gaussDdim t 0` — a genuine (degenerate) instance; the prefactor is genuinely `> 1` for `v ≠ 0`
    (positive `∑ (v k)²`), which is what drives the no-go.  No unsatisfiable antecedent. -/
theorem gaussDdim_peak_ratio_at_zero {t : ℝ} (ht : 0 < t) :
    gaussDdim t (0 : Point n)
      = Real.exp ((∑ _k : Fin n, ((0 : Point n) _k) ^ 2) / (4 * t)) * gaussDdim t (0 : Point n) := by
  exact gaussDdim_peak_ratio (n := n) ht (0 : Point n)

/-- **Non-vacuity of the peak `hFd` reduction.**  At the empty gate `S := fun _ => ∅` the two inputs of
    `witnessFieldHessian_hFd_of_peak_dominator` are inhabited (`closure ∅ = ∅` compact; `Poly := 0`
    continuous with the domination vacuous over `∅`), so the `hFd` `⨆`-reduction fires.  (The stronger
    NON-EMPTY non-vacuity is `ChartJetXUniformBound.concreteGate_closure_isCompact`.)  No J4-548/847-style
    unsatisfiable antecedent. -/
theorem hFd_peak_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (i : Fin n) (t : ℝ) (m : ℕ) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y =>
            witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x‖
          ≤ ⨆ x' : Point n,
              ‖fderiv ℝ (fun y =>
                witnessFieldDeriv g gi hC hK (fun _ => (∅ : Set (Point n))) a b i (t - s) y z) x'‖ := by
  refine witnessFieldHessian_hFd_of_peak_dominator g gi hC hK (fun _ => ∅) a b i t m ?_ ?_
  · filter_upwards with s _; filter_upwards with z
    rw [closure_empty]; exact isCompact_empty
  · filter_upwards with s _; filter_upwards with z
    refine ⟨fun _ => 0, continuous_const, ?_⟩
    rw [closure_empty]; intro x hx; exact absurd hx (Set.notMem_empty x)

end QIQTH.BFGaussianEnvelopeClosed

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.BFGaussianEnvelopeClosed
#print axioms gaussDdim_peak_ratio
#print axioms fieldHessian_peak_dominator_of_chart_dominator
#print axioms witnessFieldHessian_hFd_of_peak_dominator
#print axioms bf_no_uniform_gaussian_decay
#print axioms gaussDdim_peak_ratio_at_zero
#print axioms hFd_peak_nonvacuous
end AxiomChecks
