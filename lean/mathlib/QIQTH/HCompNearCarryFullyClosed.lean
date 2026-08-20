/-
  HCompNearCarryFullyClosed — Plan v9 (`tranquil-stargazing-fox.md`, Task B STEP 4c part (ii)):
  the two genuinely-new analytic bricks that the NEAR carry `nb` of
  `VanVleckGatedSpatialSymmetry.hcomp` needs beyond J4-879's concrete-`W` identification —
    • ITEM (iii) — the EVENNESS LINK  `G_τ(U z x₀) = G_τ(T_{x₀}(U x₀ z))`, connecting the
      witness base-slot Gaussian to the `T_{x₀}` chart-replacement that J4-879 bounds; and
    • ITEM (iv) — the GENERALIZED (`1/τ^p`-prefactor) SLIVER ESTIMATE, the improper-power sliver
      integral that folds each mixed-normal-form term's OWN singular prefactor `‖v‖^m/τ^p` into
      J4-879's cubic cancellation and STILL nets `O(√ε)`, INCLUDING the two MARGINAL rate terms
      (`1a`, `p=2,m=2` and `1b`, `p=1,m=0`) whose sliver integrand is genuinely singular (`τ^{-1/2}`).

  Both were pre-validated (zero discrepancies) by the bounded sympy feasibility check
  `docs/qg_roadmap/rnc_sympy/hcomp_near_carry_final_feasibility.py`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## ITEM (iii) — the evenness link.  `gaussDdim` is EVEN (`heatKernel1D` depends on its space arg
  only through `x²`), so `gaussDdim τ (-v) = gaussDdim τ v` (`gaussDdim_neg`).  Composing with the
  banked generic-base reversal identity (J4-858, `baseSlot_eventuallyEq_neg_terminalVel_at`,
  `U z x₀ =ᶠ[𝓝 x₀] − T_{x₀}(U x₀ z)`) gives the eventual equality
      `(fun z => gaussDdim τ (U z x₀)) =ᶠ[𝓝 x₀] (fun z => gaussDdim τ (T_{x₀}(U x₀ z)))`
  (`gaussDdim_reversal_link`) — radius-free pure algebra, exactly the (iii) link.

  ## ITEM (iv) — the generalized prefactor sliver estimate.  The mixed normal form
  (`ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed`) has, per term, a singular scalar prefactor
  `‖v‖^m/τ^p`.  Folding it into J4-879's fixed-`τ` cubic cancellation
  (`HeatResidualBound.weighted_chart_replace_bound`, `∫_{ball 0 R} ‖z‖^k·|G_τ(Wz)−G_τ(z)| ≤
  Cshape·(√τ)^{k+1}`, `k := m`) gives a sliver integrand dominated by `C·τ^{(k+1)/2 − p}`.  The
  GENUINE new content is the improper-power sliver integral
      `‖∫ s in (t−ε)..t, f(s)‖ ≤ C·ε^{(k+3)/2 − p}/((k+3)/2 − p)`   whenever `(k+1)/2 − p > −1`,
  proved unconditionally (`sliver_power_dominated_integral_le`) via `integral_rpow` + the reversal
  substitution — VALID EVEN when the dominating exponent `(k+1)/2 − p` is negative (the marginal
  terms `1a`/`1b`, exponent `−1/2`, integrand `τ^{-1/2}`), which the constant-bound route of J4-861's
  template CANNOT reach.  `terminalVelAt_prefactor_sliver_bound` instantiates this at the CONCRETE
  reversal near-isometry `T_{x₀}` with its J4-879 near-isometry data, delivering — with HONEST,
  fully-tracked constants (`Cpre·Cshape`) — the matched rate `ε^{(k+3)/2 − p}` for EVERY `(m,p)`:
      `1a` (m=2,p=2)→`ε^{1/2}`, `1b` (m=0,p=1)→`ε^{1/2}` (the two MARGINAL, zero rate-margin),
      `1b′/2/3` (m=1,p=1)→`ε^1`, `4` (m=0,p=0)→`ε^{3/2}` (comfortable) — all `≥ √ε` = `hcomp`'s target.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It builds
  items (iii) and (iv) of the mixed-normal-form connection for `hcomp`'s NEAR carry.  It does NOT, by
  itself, discharge `nb` in full: the remaining items are (i) the wiring of the concrete `kPrime`
  component `∫_{ball x ρ} (kPrime … x z)(eⱼ)` through the mixed normal form (the multi-increment
  "chart-surface" thread, J4-787→794…, which converges on the joint-`C²`-chart wall) and (ii) the
  base↔field change of variables.  And even a FULLY discharged `nb` does NOT close `hcomp`, because the
  near/far split's FAR carry `fb` depends on the STILL-OPEN `hzmass` deep Gaussian z-mass wall of the
  `MixedDirectionsFieldHessianEnvelope` thread.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.TerminalVelAtCubicRemainder
import QIQTH.HCompNearCarryConcreteDischarge
import QIQTH.HCompNearCarryAssembly
import QIQTH.GaussianMomentEnvelope

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1
open QIQTH.GeodesicReversalRouteAtPoint QIQTH.TerminalVelAtCubicRemainder
open scoped Topology Interval BigOperators

namespace QIQTH.HCompNearCarryFullyClosed

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — ITEM (iii): the EVENNESS LINK.
    ############################################################################### -/

/-- **`heatKernel1D_neg`.**  The 1-D heat kernel is EVEN: `G_t(−x) = G_t(x)`, because it depends on its
    space argument only through `x²` (`heatKernel1D t x = (√(4πt))⁻¹·exp(−x²/(4t))`).  NOT `a₁ = R/6`. -/
theorem heatKernel1D_neg (t x : ℝ) : heatKernel1D t (-x) = heatKernel1D t x := by
  rw [heatKernel1D, heatKernel1D, neg_sq]

/-- **`gaussDdim_neg`.**  The `d`-dimensional flat Gaussian is EVEN: `G_τ(−v) = G_τ(v)`, factor-by-factor
    from `heatKernel1D_neg` (`(−v) k = −(v k)`).  ITEM (iii)'s pure-algebra core.  NOT `a₁ = R/6`. -/
theorem gaussDdim_neg (τ : ℝ) (v : Point n) : gaussDdim τ (-v) = gaussDdim τ v := by
  simp only [gaussDdim]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Pi.neg_apply, heatKernel1D_neg]

/-- **★ `gaussDdim_reversal_link` — ITEM (iii), THE EVENNESS LINK.**  Composing `gaussDdim`'s evenness
    with the banked generic-base reversal identity (J4-858, `baseSlot_eventuallyEq_neg_terminalVel_at`),
        `(fun z => gaussDdim τ (uniformInverseChart g gi hC hK z x₀))`
          `=ᶠ[𝓝 x₀]`
        `(fun z => gaussDdim τ (terminalVelAt g gi hC hK x₀ (uniformInverseChart g gi hC hK x₀ z)))`.
    This connects the witness base-slot Gaussian `G_τ(U z x₀)` to the `T_{x₀}` chart-replacement Gaussian
    that J4-879 (`terminalVelAt_chartReplace_sliver_bound`) bounds.  NOT `a₁ = R/6`. -/
theorem gaussDdim_reversal_link (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀Kmem : K ∈ 𝓝 x₀) (τ : ℝ) :
    (fun z => gaussDdim τ (uniformInverseChart g gi hC hK z x₀))
      =ᶠ[𝓝 x₀]
      (fun z => gaussDdim τ
        (terminalVelAt g gi hC hK x₀ (uniformInverseChart g gi hC hK x₀ z))) := by
  have hrev := baseSlot_eventuallyEq_neg_terminalVel_at g gi hC hK hx₀Kmem
  filter_upwards [hrev] with z hz
  show gaussDdim τ (uniformInverseChart g gi hC hK z x₀)
      = gaussDdim τ (terminalVelAt g gi hC hK x₀ (uniformInverseChart g gi hC hK x₀ z))
  rw [hz, gaussDdim_neg]

/-! ###############################################################################
    ### §2 — ITEM (iv), abstract core: the improper-power sliver integral.
    ###
    ### This is the GENUINE new analysis — VALID for a NEGATIVE dominating exponent `q`
    ### (the marginal terms), where J4-861's constant-bound template route is unavailable.
    ############################################################################### -/

/-- **★★ `sliver_power_dominated_integral_le` — the improper-power sliver integral bound.**  For any
    `f : ℝ → ℝ` whose norm is dominated a.e. on the sliver `(t−ε, t]` by a REAL power `C·(t−s)^q`
    (`rpow`, `q > −1`, so possibly SINGULAR at `s = t` when `q < 0`),
        `‖∫ s in (t−ε)..t, f s‖ ≤ C · ε^{q+1} / (q+1)`.
    Route: `intervalIntegral.norm_integral_le_of_norm_le` against the dominating power (interval-
    integrable by `intervalIntegrable_rpow'` + `comp_sub_left`), then the exact sliver integral
    `∫ s in (t−ε)..t, (t−s)^q = ∫ x in 0..ε, x^q = ε^{q+1}/(q+1)` (`integral_comp_sub_left` +
    `integral_rpow`).  UNCONDITIONAL, no integrability of `f`.  This is the marginal-term engine.
    NOT `a₁ = R/6`. -/
theorem sliver_power_dominated_integral_le (ε : ℝ) (hε : 0 < ε) (t : ℝ)
    (C q : ℝ) (hC : 0 ≤ C) (hq : -1 < q) (f : ℝ → ℝ)
    (hdom : ∀ᵐ s : ℝ ∂volume, s ∈ Set.Ioc (t - ε) t → ‖f s‖ ≤ C * (t - s) ^ q) :
    ‖∫ s in (t - ε)..t, f s‖ ≤ C * ε ^ (q + 1) / (q + 1) := by
  have hab : t - ε ≤ t := by linarith
  -- the dominating function `g s = C·(t−s)^q` is interval-integrable on `(t−ε, t)`.
  have hg : IntervalIntegrable (fun s : ℝ => C * (t - s) ^ q) volume (t - ε) t := by
    have h0 : IntervalIntegrable (fun x : ℝ => x ^ q) volume 0 ε :=
      intervalIntegral.intervalIntegrable_rpow' hq
    have h1 : IntervalIntegrable (fun x : ℝ => (t - x) ^ q) volume (t - 0) (t - ε) :=
      h0.comp_sub_left t
    rw [sub_zero] at h1
    exact (h1.symm).const_mul C
  -- the exact value of the dominating sliver integral.
  have hval : ∫ s in (t - ε)..t, C * (t - s) ^ q = C * ε ^ (q + 1) / (q + 1) := by
    rw [intervalIntegral.integral_const_mul]
    have hcomp := intervalIntegral.integral_comp_sub_left (a := t - ε) (b := t)
      (fun x : ℝ => x ^ q) t
    have e1 : t - t = 0 := by ring
    have e2 : t - (t - ε) = ε := by ring
    rw [e1, e2] at hcomp
    rw [hcomp, integral_rpow (Or.inl hq), Real.zero_rpow (by linarith : q + 1 ≠ 0)]
    ring
  -- combine: `‖∫ f‖ ≤ ∫ g = C·ε^{q+1}/(q+1)`.
  have hle := intervalIntegral.norm_integral_le_of_norm_le hab hdom hg
  rwa [hval] at hle

/-! ###############################################################################
    ### §3 — ITEM (iv), concrete: the reversal near-isometry prefactor sliver rate.
    ############################################################################### -/

/-- **`sqrt_pow_mul_rpow_neg`.**  The rpow bookkeeping folding a `1/τ^p` prefactor into the
    `(√τ)^{k+1}` cubic-cancellation moment: for `τ > 0`,
        `(√τ)^{k+1} · τ^{−p} = τ^{(k+1)/2 − p}`   (`rpow`).
    NOT `a₁ = R/6`. -/
theorem sqrt_pow_mul_rpow_neg (τ : ℝ) (hτ : 0 < τ) (k : ℕ) (p : ℝ) :
    (Real.sqrt τ) ^ (k + 1) * τ ^ (-p) = τ ^ (((k : ℝ) + 1) / 2 - p) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (τ ^ (1 / 2 : ℝ)) (k + 1),
      ← Real.rpow_mul hτ.le, ← Real.rpow_add hτ]
  congr 1
  push_cast
  ring

/-- **★★★ `terminalVelAt_prefactor_sliver_bound` — ITEM (iv), CONCRETE, WITH THE MARGINAL TERMS.**  The
    matched prefactor sliver rate for the CONCRETE reversal near-isometry `T_{x₀} = terminalVelAt g gi
    hC hK x₀`.  For any weight power `k` (`= m`, the mixed-normal-form term's `‖v‖`-power) and prefactor
    power `p` satisfying the convergence condition `(k+1)/2 − p > −1` (⇔ `k+3 > 2p`, the exact
    per-term finiteness bound of the sympy check), and a prefactor constant `Cpre ≥ 0`:
        `‖∫ s in (t−ε)..t, Cpre·(t−s)^{−p}·(∫_{ball 0 R} ‖z‖^k·|G_{t−s}(T z)−G_{t−s}(z)|) ds‖`
          `≤ (Cpre·Cshape) · ε^{(k+1)/2 − p + 1} / ((k+1)/2 − p + 1)`,
    i.e. rate `ε^{(k+3)/2 − p}`, with `Cshape := (L'/4)·(√2)^n·(n·ck3·(√2)^{k+3})` (`L'` = J4-879's
    concrete radial-error constant).  Applies UNIFORMLY to all five mixed-normal-form terms:
      `1a` (k=2,p=2): rate `ε^{1/2}` (MARGINAL, singular `τ^{-1/2}` integrand);
      `1b` (k=0,p=1): rate `ε^{1/2}` (MARGINAL, singular `τ^{-1/2}` integrand);
      `1b′/2/3` (k=1,p=1): rate `ε^{1}`;  `4` (k=0,p=0): rate `ε^{3/2}`.
    All `≥ √ε`, `hcomp`'s target — with HONEST, explicit constants (`Cpre·Cshape`) tracked through,
    even for the zero-margin marginal terms.  Obtained by folding J4-879's fixed-`τ` cubic cancellation
    (`weighted_chart_replace_bound` + `terminalVelAt_nearIsometry_data`) into the improper-power sliver
    engine `sliver_power_dominated_integral_le`.  Carries the generic Gaussian facts `hWint`/`hmom`.
    NOT `a₁ = R/6`. -/
theorem terminalVelAt_prefactor_sliver_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) {x₀ : Point n} (hx₀K : x₀ ∈ K)
    (k : ℕ) (p : ℝ) (hp : -1 < ((k : ℝ) + 1) / 2 - p)
    (Cpre : ℝ) (hCpre : 0 ≤ Cpre)
    (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ck3 : ℝ) (hck3 : 0 ≤ ck3) :
    ∃ R > (0 : ℝ), ∃ L' ≥ (0 : ℝ),
      (∀ (_hWint : ∀ τ : ℝ, 0 < τ → τ ≤ ε →
          IntegrableOn (fun z : Point n =>
              ‖z‖ ^ k * |gaussDdim τ (terminalVelAt g gi hC hK x₀ z) - gaussDdim τ z|)
            (Metric.ball 0 R) volume)
        (_hmom : ∀ τ : ℝ, 0 < τ → τ ≤ ε →
          ∫ y : ℝ, heatKernel1D (2 * τ) y * |y| ^ (k + 3)
            ≤ ck3 * (Real.sqrt (2 * τ)) ^ (k + 3)),
        ‖∫ s in (t - ε)..t,
            Cpre * (t - s) ^ (-p) *
              ∫ z in Metric.ball (0 : Point n) R,
                ‖z‖ ^ k * |gaussDdim (t - s) (terminalVelAt g gi hC hK x₀ z)
                    - gaussDdim (t - s) z|‖
          ≤ (Cpre * (L' / 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3))))
              * ε ^ (((k : ℝ) + 1) / 2 - p + 1) / (((k : ℝ) + 1) / 2 - p + 1)) := by
  obtain ⟨R, hR, L', hL', herr, hmin⟩ :=
    QIQTH.HCompNearCarryConcreteDischarge.terminalVelAt_nearIsometry_data g gi hC hK hx₀K
  refine ⟨R, hR, L', hL', ?_⟩
  intro hWint hmom
  set T : Point n → Point n := terminalVelAt g gi hC hK x₀ with hT
  set Cshape : ℝ := L' / 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3))
    with hCshape
  have hCshape_nn : 0 ≤ Cshape := by rw [hCshape]; positivity
  set q : ℝ := ((k : ℝ) + 1) / 2 - p with hq
  -- the sliver integrand.
  set f : ℝ → ℝ := fun s => Cpre * (t - s) ^ (-p) *
      ∫ z in Metric.ball (0 : Point n) R,
        ‖z‖ ^ k * |gaussDdim (t - s) (T z) - gaussDdim (t - s) z| with hf
  -- a.e. domination by `(Cpre·Cshape)·(t−s)^q`.
  have hdom : ∀ᵐ s : ℝ ∂volume, s ∈ Set.Ioc (t - ε) t →
      ‖f s‖ ≤ (Cpre * Cshape) * (t - s) ^ q := by
    have hne : ∀ᵐ s : ℝ ∂volume, s ≠ t := by
      rw [ae_iff]
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, Real.volume_singleton]
    filter_upwards [hne] with s hsne hmem
    obtain ⟨hs1, hs2⟩ := hmem
    have hs2' : s < t := lt_of_le_of_ne hs2 hsne
    have hτpos : 0 < t - s := by linarith
    have hτε : t - s ≤ ε := by linarith
    set τ : ℝ := t - s with hτdef
    -- the ball moment integral `Φ` is nonnegative and `≤ Cshape·(√τ)^{k+1}`.
    set Φ : ℝ := ∫ z in Metric.ball (0 : Point n) R,
        ‖z‖ ^ k * |gaussDdim τ (T z) - gaussDdim τ z| with hΦdef
    have hΦnn : 0 ≤ Φ := by
      rw [hΦdef]
      apply setIntegral_nonneg measurableSet_ball
      intro z _; positivity
    have hΦle : Φ ≤ Cshape * (Real.sqrt τ) ^ (k + 1) := by
      rw [hΦdef, hCshape]
      exact weighted_chart_replace_bound k τ hτpos T R L' hL' herr hmin
        (hWint τ hτpos hτε) ck3 hck3 (hmom τ hτpos hτε)
    -- the prefactor `τ^{−p}` is positive.
    have hpref_pos : (0 : ℝ) < τ ^ (-p) := Real.rpow_pos_of_pos hτpos (-p)
    -- assemble the pointwise bound.
    have hfval : f s = Cpre * τ ^ (-p) * Φ := by rw [hf, hΦdef, hτdef]
    have hfnn : 0 ≤ f s := by
      rw [hfval]; exact mul_nonneg (mul_nonneg hCpre hpref_pos.le) hΦnn
    rw [Real.norm_of_nonneg hfnn, hfval]
    calc Cpre * τ ^ (-p) * Φ
        ≤ Cpre * τ ^ (-p) * (Cshape * (Real.sqrt τ) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left hΦle (mul_nonneg hCpre hpref_pos.le)
      _ = (Cpre * Cshape) * ((Real.sqrt τ) ^ (k + 1) * τ ^ (-p)) := by ring
      _ = (Cpre * Cshape) * τ ^ q := by
          rw [sqrt_pow_mul_rpow_neg τ hτpos k p, hq]
  -- convergence exponent `q > −1`.
  have hqgt : -1 < q := by rw [hq]; exact hp
  have hCC_nn : 0 ≤ Cpre * Cshape := mul_nonneg hCpre hCshape_nn
  -- apply the improper-power sliver engine.
  have hmain := sliver_power_dominated_integral_le ε hε t (Cpre * Cshape) q hCC_nn hqgt f hdom
  -- rewrite the conclusion into the stated constant / exponent shape.
  rw [hf] at hmain
  have hqp1 : q + 1 = ((k : ℝ) + 1) / 2 - p + 1 := by rw [hq]
  rw [hqp1] at hmain
  -- fold `Cshape` back to its explicit form and reassociate the constant.
  calc ‖∫ s in (t - ε)..t,
          Cpre * (t - s) ^ (-p) *
            ∫ z in Metric.ball (0 : Point n) R,
              ‖z‖ ^ k * |gaussDdim (t - s) (T z) - gaussDdim (t - s) z|‖
      ≤ (Cpre * Cshape) * ε ^ (((k : ℝ) + 1) / 2 - p + 1) / (((k : ℝ) + 1) / 2 - p + 1) := hmain
    _ = (Cpre * (L' / 4 * (Real.sqrt 2) ^ n * ((n : ℝ) * ck3 * (Real.sqrt 2) ^ (k + 3))))
          * ε ^ (((k : ℝ) + 1) / 2 - p + 1) / (((k : ℝ) + 1) / 2 - p + 1) := by
        rw [hCshape]

end QIQTH.HCompNearCarryFullyClosed

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryFullyClosed
#print axioms heatKernel1D_neg
#print axioms gaussDdim_neg
#print axioms gaussDdim_reversal_link
#print axioms sliver_power_dominated_integral_le
#print axioms sqrt_pow_mul_rpow_neg
#print axioms terminalVelAt_prefactor_sliver_bound
end AxiomChecks
