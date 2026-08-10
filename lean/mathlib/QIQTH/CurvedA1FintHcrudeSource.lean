/-
  CurvedA1FintHcrudeSource — J4-571: SOURCING `hFint`'s crude first-derivative envelope `hcrude`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  This file turns the `hcrude` carrier consumed by
  `CurvedA1FintAdomSource.curved_hFint_hAdom_at_gate` (the τ^(−1/2) whole-time crude FIRST-derivative
  envelope for `g^K = curvedRNCMetric κ`) from a whole opaque carry into

      {  PROVED width-transfer  `witnessFieldDeriv_wide_crude`  (the honest first-derivative sibling of
         `WideWitnessAmplitude.WideAmplitudeData.second_domination`, one power weaker — `(√τ)⁻¹` not
         `τ⁻¹`) — the missing `first_domination` base-bound  }
      ⊕ {  BANKED off-gate vanishing  `witnessFieldDeriv_offGate_eq_zero`  (`z ∉ K` ⟹ `wfd = 0`)  }
      ⊕ {  CARRIED far-field annulus envelope `hFar`  (`z ∈ K`, `‖z‖ ≥ r`) — the precisely-scoped
         residual/blocker (the geometric far-field first-jet content, NOT yet banked)  }
      ⊕ {  the chart-image first-jet two-term envelope `hFirstEnv`  (satisfiable — the magnitude form of
         the first-jet Leibniz expansion; the honest `√(r²/τ)` prefactor is dominated by the integer
         two-term shape via `√x ≤ 1 + x`; NOT the conclusion — the conclusion is the WIDE
         `gaussDdim (lam·τ) z`, the genuine content being the width transfer)  }.

  It does NOT make `a₁ = R/6` unconditional: `hFar`, `hFirstEnv`, the `hFint_d` sibling's `hAdom`,
  `hsrc`, `hOffCollarTail`, the convergence trio, and `hInnerCont` all remain owed.

  ── THE SATISFIABILITY CORE (why the `τ^(−1/2)`-prefactor envelope is TRUE while the clean one is FALSE).
  The census `hFint` binder demands a whole-time first-derivative Gaussian domination.  The genuine
  first spatial derivative of the chart-image Gaussian brings down a factor `~ ‖W‖/(2τ)`, i.e. the true
  envelope carries a `√(rncRadialSq z / τ)·(√τ)⁻¹ = ‖W‖/τ` prefactor — a `τ^(−1/2)` blow-up as `τ → 0`
  at the chart image.  KEEPING the `(√τ)⁻¹` prefactor the envelope is TRUE (and one power weaker than
  the banked SECOND-derivative crude `τ⁻¹` envelope `CurvedRNCHeatOpDom2.curvedRNC_witnessSecondXDeriv_dom_crude`);
  DROPPING it (a single `m`-free clean constant) would be FALSE.  The `(√τ)⁻¹` prefactor is kept
  verbatim throughout.  For `κ < 0 ⊂ κ ≠ 0`, `n ≥ 2` the witness is genuinely curved
  (`curvedRNCMetric_ricci_trace_diag_ne`), so this is NOT secretly flat.

  NOT `a₁ = R/6`.
-/
import QIQTH.CurvedA1FintAdomSource
import QIQTH.CurvedRNCHeatOpDom2
import QIQTH.WidthAdapters

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.InverseChartNormalJets QIQTH.WideWitnessAmplitude
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCGaussWitness QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCHeatOpDom2 QIQTH.WidthAdapters QIQTH.CurvedA1FintAdomSource
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1FintHcrudeSource

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### (A) — THE FIRST-DERIVATIVE WIDE TRANSFER (the missing `first_domination` base-bound).
    ############################################################################### -/

/-- **★★★ J4-571 — `witnessFieldDeriv_wide_crude`.**  THE FIRST-DERIVATIVE WIDE `(√τ)⁻¹` GAUSSIAN
    DOMINATION — the honest sibling of `WideWitnessAmplitude.WideAmplitudeData.second_domination`, one
    power weaker (`(√τ)⁻¹` instead of `τ⁻¹`), and the base-bound that fills the previously-missing
    `first_domination` slot.  For a fixed gate record `D`, a gate function `S`, a line `i`, cutoffs
    `a b`, a time cap `τ₀`, and the CHART-IMAGE first-jet two-term envelope `hFirstEnv`
    `≤ (A₀ + A₁·(r²(z)/τ))·(√τ)⁻¹·gaussDdim τ (W₀ z)`, there is an explicit `C > 0` with, uniformly over
    `0 < τ ≤ τ₀` and every gate base point `z ∈ K`, `‖z‖ < D.r`,

        `|witnessFieldDeriv … i τ 0 z| ≤ C · (√τ)⁻¹ · gaussDdim (D.lam·τ) z`.

    Route (verbatim the `second_domination` argument with `τ⁻¹ ↦ (√τ)⁻¹`): the two-term chart-image
    envelope, then the fixed-gate width transfer `D.poly_absorb 0` (constant piece) and `D.poly_absorb 1`
    (the `r²(z)/τ` piece absorbs against the width gap), both scaled by `(√τ)⁻¹ ≥ 0`.

    ⚠ This is the `(√τ)⁻¹` envelope, NOT a clean single-constant whole-time bound (which is FALSE at the
    concrete witness — the `(√τ)⁻¹` prefactor blows up as `τ → 0`).  NOT `a₁ = R/6`. -/
theorem witnessFieldDeriv_wide_crude {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K}
    (D : FixedFlowGateData g gi hC hK) (S : Point n → Set (Point n)) (i : Fin n)
    (a b : ℝ) (τ₀ A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hFirstEnv : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |witnessFieldDeriv g gi hC hK S a b i τ (0 : Point n) z|
          ≤ (A₀ + A₁ * (rncRadialSq z / τ)) * (Real.sqrt τ)⁻¹
              * gaussDdim τ (uniformInverseChart g gi hC hK z 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
      |witnessFieldDeriv g gi hC hK S a b i τ (0 : Point n) z|
        ≤ C * (Real.sqrt τ)⁻¹ * gaussDdim (D.lam * τ) z := by
  obtain ⟨C₀, hC₀0, habs0⟩ := D.poly_absorb 0
  obtain ⟨C₁, hC₁0, habs1⟩ := D.poly_absorb 1
  refine ⟨A₀ * C₀ + A₁ * C₁ + 1,
    by nlinarith [mul_nonneg hA₀ hC₀0.le, mul_nonneg hA₁ hC₁0.le], ?_⟩
  intro τ hτ hτ0 z hz hzr
  have henv := hFirstEnv τ hτ hτ0 z hz hzr
  have hgW0 : gaussDdim τ (uniformInverseChart g gi hC hK z 0)
      ≤ C₀ * gaussDdim (D.lam * τ) z := by simpa using habs0 τ hτ z hz hzr
  have hgW1 : rncRadialSq z / τ * gaussDdim τ (uniformInverseChart g gi hC hK z 0)
      ≤ C₁ * gaussDdim (D.lam * τ) z := by
    simpa only [pow_one] using habs1 τ hτ z hz hzr
  have hGLnn : 0 ≤ gaussDdim (D.lam * τ) z := gaussDdim_nonneg _ _
  have hti : 0 ≤ (Real.sqrt τ)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg τ)
  set Gw := gaussDdim τ (uniformInverseChart g gi hC hK z 0) with hGwdef
  set Gl := gaussDdim (D.lam * τ) z with hGldef
  set rz := rncRadialSq z with hrzdef
  set st := (Real.sqrt τ)⁻¹ with hstdef
  have hdist : (A₀ + A₁ * (rz / τ)) * st * Gw
      = st * (A₀ * Gw) + st * (A₁ * (rz / τ * Gw)) := by ring
  have h1 : st * (A₀ * Gw) ≤ st * (A₀ * (C₀ * Gl)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgW0 hA₀) hti
  have h2 : st * (A₁ * (rz / τ * Gw)) ≤ st * (A₁ * (C₁ * Gl)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgW1 hA₁) hti
  have htiGL : 0 ≤ st * Gl := mul_nonneg hti hGLnn
  calc |witnessFieldDeriv g gi hC hK S a b i τ (0 : Point n) z|
      ≤ (A₀ + A₁ * (rz / τ)) * st * Gw := henv
    _ = st * (A₀ * Gw) + st * (A₁ * (rz / τ * Gw)) := hdist
    _ ≤ st * (A₀ * (C₀ * Gl)) + st * (A₁ * (C₁ * Gl)) := add_le_add h1 h2
    _ ≤ (A₀ * C₀ + A₁ * C₁ + 1) * st * Gl := by nlinarith [htiGL]

/-! ###############################################################################
    ### (B) — THE EXACT `hcrude` BINDER FOR `g^K` (whole-space, at the constant-radius gate).
    ############################################################################### -/

/-- **★★★ J4-571 — `curved_hFint_hcrude_at_gate`.**  THE EXACT whole-space `hcrude` census binder
    consumed by `CurvedA1FintAdomSource.curved_hFint_hAdom_at_gate`, at the genuinely-curved witness
    `g^K = curvedRNCMetric κ`, produced by GLUING three pieces over the three `z`-regions:

      • `z ∉ K`               — BANKED off-gate vanishing `witnessFieldDeriv_offGate_eq_zero` (`wfd = 0`);
      • `z ∈ K`, `‖z‖ < r`    — the PROVED first-derivative wide transfer (§A, inline) from `hFirstEnv`;
      • `z ∈ K`, `‖z‖ ≥ r`    — the CARRIED far-field annulus envelope `hFar` (the precisely-scoped
                                residual — the geometric far-field first-jet content, NOT yet banked).

    Output constant `Ccrude := Cwide + Cfar` (`Cwide := A₀·C₀ + A₁·C₁ + 1` the width-transfer constant),
    window `wA := (curvedGate κ hChr hK).lam`; the Gaussian argument `0 − z` is matched to the base
    point `z` via `gaussDdim_neg`.  ⚠ The `(√τ)⁻¹` prefactor is kept VERBATIM (dropping it is the FALSE
    clean bound).  NOT `a₁ = R/6`. -/
theorem curved_hFint_hcrude_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (T A₀ A₁ Cfar : ℝ)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hCfar : 0 ≤ Cfar)
    (hFirstEnv : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K,
        ‖z‖ < (curvedGate κ hChr hK).r →
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ (A₀ + A₁ * (rncRadialSq z / τ)) * (Real.sqrt τ)⁻¹
              * gaussDdim τ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0))
    (hFar : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n, z ∈ K →
        ¬ (‖z‖ < (curvedGate κ hChr hK).r) →
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ Cfar * (Real.sqrt τ)⁻¹ * gaussDdim ((curvedGate κ hChr hK).lam * τ) z) :
    ∃ Ccrude wA : ℝ, 0 ≤ Ccrude ∧ 0 < wA ∧
      ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ Ccrude * (Real.sqrt τ)⁻¹ * gaussDdim (wA * τ) (0 - z) := by
  obtain ⟨C₀, hC₀0, habs0⟩ := (curvedGate κ hChr hK).poly_absorb 0
  obtain ⟨C₁, hC₁0, habs1⟩ := (curvedGate κ hChr hK).poly_absorb 1
  have hlam0 : 0 < (curvedGate κ hChr hK).lam :=
    lt_trans zero_lt_one (curvedGate κ hChr hK).hlam
  have hCwide0 : 0 ≤ A₀ * C₀ + A₁ * C₁ + 1 := by
    nlinarith [mul_nonneg hA₀ hC₀0.le, mul_nonneg hA₁ hC₁0.le]
  refine ⟨(A₀ * C₀ + A₁ * C₁ + 1) + Cfar, (curvedGate κ hChr hK).lam,
    by linarith, hlam0, ?_⟩
  intro i τ hτ hτT z
  -- Match the Gaussian argument `0 − z` to the base point `z` (`gaussDdim` is even).
  rw [zero_sub, gaussDdim_neg]
  have hti : 0 ≤ (Real.sqrt τ)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg τ)
  have hGnn : 0 ≤ gaussDdim ((curvedGate κ hChr hK).lam * τ) z := gaussDdim_nonneg _ _
  have htiGL : 0 ≤ (Real.sqrt τ)⁻¹ * gaussDdim ((curvedGate κ hChr hK).lam * τ) z :=
    mul_nonneg hti hGnn
  by_cases hzK : z ∈ K
  · by_cases hzr : ‖z‖ < (curvedGate κ hChr hK).r
    · -- ON-GATE: the proved first-derivative wide transfer (inline §A).
      have henv := hFirstEnv i τ hτ hτT z hzK hzr
      have hgW0 : gaussDdim τ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
          ≤ C₀ * gaussDdim ((curvedGate κ hChr hK).lam * τ) z := by
        simpa using habs0 τ hτ z hzK hzr
      have hgW1 : rncRadialSq z / τ
            * gaussDdim τ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
          ≤ C₁ * gaussDdim ((curvedGate κ hChr hK).lam * τ) z := by
        simpa only [pow_one] using habs1 τ hτ z hzK hzr
      set Gw := gaussDdim τ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
        with hGwdef
      set Gl := gaussDdim ((curvedGate κ hChr hK).lam * τ) z with hGldef
      set rz := rncRadialSq z with hrzdef
      set st := (Real.sqrt τ)⁻¹ with hstdef
      have h1 : st * (A₀ * Gw) ≤ st * (A₀ * (C₀ * Gl)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgW0 hA₀) hti
      have h2 : st * (A₁ * (rz / τ * Gw)) ≤ st * (A₁ * (C₁ * Gl)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgW1 hA₁) hti
      calc |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ (A₀ + A₁ * (rz / τ)) * st * Gw := henv
        _ = st * (A₀ * Gw) + st * (A₁ * (rz / τ * Gw)) := by ring
        _ ≤ st * (A₀ * (C₀ * Gl)) + st * (A₁ * (C₁ * Gl)) := add_le_add h1 h2
        _ ≤ ((A₀ * C₀ + A₁ * C₁ + 1) + Cfar) * st * Gl := by nlinarith [htiGL, hCfar]
    · -- ANNULUS (`z ∈ K`, `‖z‖ ≥ r`): the carried far-field envelope.
      have hf := hFar i τ hτ hτT z hzK hzr
      calc |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ Cfar * (Real.sqrt τ)⁻¹ * gaussDdim ((curvedGate κ hChr hK).lam * τ) z := hf
        _ ≤ ((A₀ * C₀ + A₁ * C₁ + 1) + Cfar) * (Real.sqrt τ)⁻¹
              * gaussDdim ((curvedGate κ hChr hK).lam * τ) z := by nlinarith [htiGL, hCwide0]
  · -- OFF-GATE (`z ∉ K`): the BANKED vanishing kills the witness.
    have hz0 : witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z = 0 :=
      witnessFieldDeriv_offGate_eq_zero (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z hzK
    rw [hz0, abs_zero]
    have hCc0 : 0 ≤ (A₀ * C₀ + A₁ * C₁ + 1) + Cfar := by linarith
    exact mul_nonneg (mul_nonneg hCc0 hti) hGnn

/-! ###############################################################################
    ### (C) — DEMONSTRATOR: `hcrude` plugs into the capped `hAdom` VERBATIM.
    ############################################################################### -/

/-- **★★ J4-571 (demonstrator) — `curved_hFint_hAdom_via_hcrude_at_gate`.**  The sourced `hcrude`
    (§B) fed into `CurvedA1FintAdomSource.curved_hFint_hAdom_at_gate` (the J4-569 ε-absorption
    arithmetic), producing the exact per-`m` CAPPED first-derivative Gaussian `hAdom` the `hFint`
    census consumes — proving the sourced binder plugs into the downstream carrier VERBATIM.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFint_hAdom_via_hcrude_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (T A₀ A₁ Cfar : ℝ)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hCfar : 0 ≤ Cfar)
    (hFirstEnv : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K,
        ‖z‖ < (curvedGate κ hChr hK).r →
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ (A₀ + A₁ * (rncRadialSq z / τ)) * (Real.sqrt τ)⁻¹
              * gaussDdim τ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0))
    (hFar : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n, z ∈ K →
        ¬ (‖z‖ < (curvedGate κ hChr hK).r) →
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ Cfar * (Real.sqrt τ)⁻¹ * gaussDdim ((curvedGate κ hChr hK).lam * τ) z) :
    ∃ (Ccrude wA : ℝ),
      ∀ (m : ℕ) (i : Fin n) (τ : ℝ), epsSeq m ≤ τ → τ ≤ T → ∀ z : Point n,
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ (Ccrude * (Real.sqrt (epsSeq m))⁻¹) * gaussDdim (wA * τ) (0 - z) := by
  obtain ⟨Ccrude, wA, hCc0, _hwA0, hc⟩ :=
    curved_hFint_hcrude_at_gate κ hChr hK a b c T A₀ A₁ Cfar hA₀ hA₁ hCfar hFirstEnv hFar
  exact ⟨Ccrude, wA,
    curved_hFint_hAdom_at_gate κ hChr hK a b c T wA Ccrude hCc0 hc⟩

/-! ###############################################################################
    ### (D) — the CURVED (not-secretly-flat) satisfiability GATE.
    ############################################################################### -/

/-- **★ J4-571 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the sourced `hcrude`
    binder is discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`; and the
    `(√τ)⁻¹` prefactor is what makes the whole-time envelope TRUE (dropping it gives the FALSE clean
    bound).  NOT `a₁ = R/6`. -/
theorem curved_hFint_hcrude_at_gate_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1FintHcrudeSource

section AxiomChecks
open QIQTH.CurvedA1FintHcrudeSource
#print axioms witnessFieldDeriv_wide_crude
#print axioms curved_hFint_hcrude_at_gate
#print axioms curved_hFint_hAdom_via_hcrude_at_gate
#print axioms curved_hFint_hcrude_at_gate_curved_satisfiable
end AxiomChecks
