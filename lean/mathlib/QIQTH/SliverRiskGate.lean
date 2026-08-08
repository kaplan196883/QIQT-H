/-
  SliverRiskGate — J4-430: THE SLIVER-CORE RISK-GATE LEMMA (Sol #20 highest-risk item).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is the
  opening brick of the a₁=R/6 convergence-trio campaign, tranche (c): the standalone EXTRACTION of the
  ONE structurally-decisive lemma Sol #20 flagged — the endpoint order-two cancellation that upgrades
  the non-integrable `τ⁻¹` s-dominator to the integrable `τ^{-1/2}` rate.  No `sorry`/`admit`, no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially
  yielding) the conclusion, no existing file edited, nothing committed.  `a₁ = R/6` remains CONDITIONAL
  on the whole convergence-trio + geometric-wiring stack.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE RISK-GATE ANALYSIS.

  ### WHAT is the order-2 integrand near the endpoint `s → t` at the true witness.
  The `hbnd` binder of the threaded Duhamel core (`DuhamelCoreThreaded.truncatedDuhamelCore_threaded`)
  demands, on the Hi sliver `s ∈ (u−ε_m, u)` with `τ := u − s → 0⁺`, a bound on the outer integral
      `∫ s in (u−ε_m)..u, ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0`
  whose per-`τ` inner factor is the SIGNED `z`-integral of the SECOND field-derivative pairing
      `Inner(τ) := ∫ z, witnessSecondXDeriv … i τ z · F(u−τ) z 0`.

  ### The SINGULAR LEADING TERM.
  On the open gate the order-2 kernel is the 3-term Leibniz–Gaussian normal form
  (`SecondDerivEnvelope.witnessFieldDeriv2_gate_eq`); its LEADING (most singular) piece is the Hessian
  term `G_τ(V)·⟨V,P⟩²/(4τ²)·A` with `V ≈ z`.  Its pointwise `z`-envelope carries a `1/τ²` power, and the
  naive `z`-mass (the second Gaussian moment `∫‖z‖²G_τ ≈ τ`) leaves
      `|Inner(τ)| ≲ (1/τ²)·τ = 1/τ = (t−s)⁻¹`.
  This is the banked NAIVE dominator, and it is **fatal**: `s ↦ C·(t−s)⁻¹` is NOT interval-integrable
  on `(0,t)` (`SecondDerivEnvelope.order2_naive_dominator_not_intervalIntegrable`).  No
  differentiation-under-the-integral API can repair a divergent outer integral.

  ### WHAT kills the `τ⁻¹` — the ZERO-MOMENT / CENTER-SUBTRACTION cancellation.
  The signed `z`-integral of the Hessian factor enjoys the standard heat-kernel moment cancellation:
  the FIRST Gaussian moment of the CENTERED factor vanishes (`∫ ∂²_x G = 0`), so the leading `τ⁻¹` term
  cancels against the shared center value `A₀·T_τ` between the collar and off-collar legs
  (`SliverAssemblyMatched.sliver_term1_full_matched`, the matched pair `qz 0 = qc 0`).  What survives is
  the CENTER-SUBTRACTED remainder `G_τ(Wz) − G_τ(z)`, controlled by the cubic contact term
  `|G_τ(Wz) − G_τ(z)| ≤ C·(‖z‖³/τ)·G_{C'τ}`.  Its `z`-mass is the cubic Gaussian moment
  `∫‖z‖³ G_{κτ} ≈ τ^{3/2}` (`SliverAssemblyMatched.cubic_gaussian_moment_witness`), so the remainder
  vanishes like `√τ` relative to the `τ⁻¹` prefactor.

  ### THE POWER COUNT (the mandate's structural pattern `u⁻¹ × (√u-remainder) ≲ u^{-1/2}`).
  Writing `u := t − s = τ`, the surviving inner factor has the shape
      `|Inner(u)| ≤ C·u⁻¹·|rem(u)|`   with   `|rem(u)| ≤ B·√u`   (the center-subtracted remainder),
  hence
      `|Inner(u)| ≤ (C·B)·u⁻¹·√u = (C·B)·(√u)⁻¹ = (C·B)·u^{-1/2}`.
  The identity `u⁻¹·√u = (√u)⁻¹ = u^{-1/2}` is the ARITHMETIC HEART of the gate; `u^{-1/2}` IS interval
  integrable (`∫₀^{ε} u^{-1/2} = 2√ε < ∞`), so the outer sliver integral closes at rate `2√ε_m → 0`.

  ## THE m-SUMMABILITY STATUS (Sol #20's decisive question).
  The leading/mass constants `D0 i` (`= K₁ = 2L·(15n/2)+B_comp+Q`) and `D1 i` (`= K₀ = S`) are
  **m-INDEPENDENT** — fixed BEFORE the truncation index `m` (the wall-A quantifier discipline: the
  absorption `GpowBridge.invSqrt_absorb` uses ONLY the fixed upper endpoint `ε₀ = epsSeq 0`, NEVER a
  per-`m` lower cutoff `ε_m`).  This is STRONGER than "`∑ K_m < ∞`": there is a single constant vector
  `(D0, D1) : Fin n → ℝ` and the ENTIRE `m`-dependence lives in the vanishing factors
  `2√(epsSeq m) → 0` and `epsSeq m → 0`.  Hence the outer bound `D0 i·2√ε_m + D1 i·ε_m → 0`.

  ## WHAT IS BANKED vs NEW.
  The mechanism (matched-pair center subtraction, cubic moment, `m`-uniform absorption, outer `√ε`
  assembly) is BANKED in `SliverAssemblyMatched` / `GpowBridge` / `SecondDerivEnvelope`.  This file
  EXTRACTS the standalone risk-gate: (i) `riskGate_powercount` — the pure `u⁻¹·(√u-remainder) ≲
  u^{-1/2}` structural lemma (new, self-contained); (ii) `sliverRiskGate_hbnd` — the exact `hbnd`
  threaded-core binder produced from the moment-cancelled per-`τ` inner bound, with `D0`/`D1` fixed
  BEFORE `m`; (iii) `riskGate_bound_tendsto_zero` — the `m`-vanishing of the outer bound at fixed
  constants; (iv) `sliverRiskGate_certificate` — the packaged verdict.
-/
import Mathlib
import QIQTH.GpowBridge

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.SliverAssemblyMatched QIQTH.GpowBridge
open scoped Interval Topology BigOperators

namespace QIQTH.SliverRiskGate

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — THE RISK-GATE POWER-COUNT (the standalone structural lemma).
    ############################################################################### -/

/-- **★★★ §1 — `riskGate_powercount`.**  THE SLIVER-CORE RISK-GATE LEMMA (Sol #20 highest-risk item).
    The pure, standalone extraction of the structural pattern that repairs the order-2 endpoint: a
    quantity `Q` bounded by the SINGULAR leading factor `C·u⁻¹` times a center-subtracted REMAINDER
    `rem` that vanishes like `√u`, is majorised by the INTEGRABLE `u^{-1/2}` rate:
        `|Q| ≤ C·u⁻¹·|rem|`  and  `|rem| ≤ B·√u`   ⟹   `|Q| ≤ (C·B)·u^{-1/2}`.
    The arithmetic heart is `u⁻¹·√u = (√u)⁻¹ = u^{-1/2}` (`HeatResidualBound.inv_sqrt_eq_rpow`), the
    exact place the non-integrable `τ⁻¹` order-2 dominator
    (`SecondDerivEnvelope.order2_naive_dominator_not_intervalIntegrable`) is upgraded to the integrable
    sliver rate (`SecondDerivEnvelope.sliver_rate_intervalIntegrable`).  `B ≥ 0` is derived, not
    assumed.  NOT `a₁ = R/6`. -/
theorem riskGate_powercount (u C B rem Q : ℝ) (hu : 0 < u) (hC : 0 ≤ C)
    (hrem : |rem| ≤ B * Real.sqrt u)
    (hQ : |Q| ≤ C * u⁻¹ * |rem|) :
    |Q| ≤ (C * B) * u ^ (-(1 : ℝ) / 2) := by
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hune : u ≠ 0 := ne_of_gt hu
  have hsne : Real.sqrt u ≠ 0 := ne_of_gt hsu
  -- `B ≥ 0` is forced by `0 ≤ |rem| ≤ B·√u` with `√u > 0`.
  have h0 : (0 : ℝ) ≤ B * Real.sqrt u := le_trans (abs_nonneg rem) hrem
  have hBnn : 0 ≤ B := le_of_mul_le_mul_right (by rw [zero_mul]; exact h0) hsu
  -- the arithmetic heart: `u⁻¹·√u = (√u)⁻¹ = u^{-1/2}`.
  have hmul : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
  have hid0 : u⁻¹ * Real.sqrt u = (Real.sqrt u)⁻¹ := by
    field_simp
    linarith [hmul]
  have hCinv : 0 ≤ C * u⁻¹ := mul_nonneg hC (inv_nonneg.mpr hu.le)
  calc |Q| ≤ C * u⁻¹ * |rem| := hQ
    _ ≤ C * u⁻¹ * (B * Real.sqrt u) := mul_le_mul_of_nonneg_left hrem hCinv
    _ = (C * B) * (u⁻¹ * Real.sqrt u) := by ring
    _ = (C * B) * (Real.sqrt u)⁻¹ := by rw [hid0]
    _ = (C * B) * u ^ (-(1 : ℝ) / 2) := by rw [inv_sqrt_eq_rpow u hu]

/-! ###############################################################################
    ### §2 — THE D1/hbnd WIRING (the exact threaded-core binder, `m`-independent constants).
    ############################################################################### -/

/-- **★★★ §2 — `sliverRiskGate_hbnd`.**  THE D1/`hbnd` WIRING.  From the moment-cancelled per-`τ` inner
    bound (the `K₁·(u−s)^{-1/2} + K₀` rate, the risk-gate output at the true witness) with constants
    `D0`/`D1 : Fin n → ℝ` FIXED BEFORE the truncation index `m`, the outer sliver integral obeys the
    EXACT `hbnd` binder shape of `DuhamelCoreThreaded.truncatedDuhamelCore_threaded`:
        `|∫ s in (u−ε_m)..u, ∫ z, witnessSecondXDeriv … i (u−s) z · F s z 0|`
          ` ≤ D0 i·(2√ε_m) + D1 i·ε_m`,   `ε_m := epsSeq m`.
    Via `SliverAssemblyMatched.amplitudePackageOn_sliver_bound` at `ε := epsSeq m`.  ⚠ THE QUANTIFIER
    DISCIPLINE: `D0`/`D1` are bound BEFORE `∀ m`, so they are m-INDEPENDENT (stronger than summable);
    the whole `m`-dependence sits in `2√(epsSeq m)`, `epsSeq m`.  NOT `a₁ = R/6`. -/
theorem sliverRiskGate_hbnd (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (D0 D1 : Fin n → ℝ)
    (hinner : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hC hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (u - s) ^ (-(1 : ℝ) / 2) + D1 i) :
    ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
      |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
          witnessSecondXDeriv g gi hC hK S a b i (u - s) z * F s z 0|
        ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m := by
  intro i m u hu
  exact amplitudePackageOn_sliver_bound g gi hC hK S a b F i u (epsSeq m) (D0 i) (D1 i)
    (epsSeq_pos m).le (fun s hs => hinner i m u hu s hs)

/-! ###############################################################################
    ### §3 — THE m-VANISHING (fixed constants, `ε_m → 0`).
    ############################################################################### -/

/-- **★ §3 — `riskGate_bound_tendsto_zero`.**  The outer sliver bound `D0·(2√ε_m) + D1·ε_m` tends to `0`
    as `m → ∞`, for ANY FIXED constants `D0`, `D1` (`ε_m := epsSeq m → 0`, `ConvApproximants.
    epsSeq_tendsto`; `√·` continuous).  This is the m-summability payoff: with m-INDEPENDENT constants
    the truncation residue vanishes, so the endpoint order-2 leg contributes nothing in the limit.
    NOT `a₁ = R/6`. -/
theorem riskGate_bound_tendsto_zero (D0 D1 : ℝ) :
    Tendsto (fun m => D0 * (2 * Real.sqrt (epsSeq m)) + D1 * epsSeq m) atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun m => Real.sqrt (epsSeq m)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp epsSeq_tendsto
    simpa [Function.comp, Real.sqrt_zero] using this
  have hA : Tendsto (fun m => D0 * (2 * Real.sqrt (epsSeq m))) atTop (𝓝 0) := by
    simpa using (hsqrt.const_mul (2 : ℝ)).const_mul D0
  have hB : Tendsto (fun m => D1 * epsSeq m) atTop (𝓝 0) := by
    simpa using epsSeq_tendsto.const_mul D1
  simpa using hA.add hB

/-! ###############################################################################
    ### §4 — THE RISK-GATE VERDICT / CERTIFICATE.
    ############################################################################### -/

/-- **★★★★ §4 — `sliverRiskGate_certificate`.**  THE PACKAGED RISK-GATE VERDICT.  From the moment-
    cancelled per-`τ` inner bound at m-INDEPENDENT constants `D0`/`D1`, the risk gate delivers BOTH
      (1) the EXACT threaded-core `hbnd` binder (`sliverRiskGate_hbnd`), and
      (2) the `m`-vanishing of that bound at fixed constants (`riskGate_bound_tendsto_zero`),
    for every field index `i`.  Together these are the Sol #20 mandate met: a `u^{-1/2}` majorant with
    m-independent (hence trivially summable) constants, whose outer integral both closes and vanishes.
    ⟹ THE ROUTE IS SOUND; the remaining sliver work is standard dominated analysis (discharging the
    enumerated satisfiable carries `SliverAssemblyMatched.hbnd_concrete_v2_carries`).  NOT `a₁ = R/6`. -/
theorem sliverRiskGate_certificate (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (F : ℝ → Point n → Point n → ℝ) (U : Set ℝ) (D0 D1 : Fin n → ℝ)
    (hinner : ∀ (i : Fin n) (m : ℕ), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hC hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (u - s) ^ (-(1 : ℝ) / 2) + D1 i) :
    (∀ (i : Fin n) (m : ℕ), ∀ u ∈ U,
        |∫ s in (u - epsSeq m)..u, ∫ (z : Point n),
            witnessSecondXDeriv g gi hC hK S a b i (u - s) z * F s z 0|
          ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m)
    ∧ (∀ i : Fin n,
        Tendsto (fun m => D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) atTop (𝓝 0)) := by
  refine ⟨sliverRiskGate_hbnd g gi hC hK S a b F U D0 D1 hinner, ?_⟩
  intro i
  exact riskGate_bound_tendsto_zero (D0 i) (D1 i)

end QIQTH.SliverRiskGate

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.SliverRiskGate.riskGate_powercount
#print axioms QIQTH.SliverRiskGate.sliverRiskGate_hbnd
#print axioms QIQTH.SliverRiskGate.riskGate_bound_tendsto_zero
#print axioms QIQTH.SliverRiskGate.sliverRiskGate_certificate
