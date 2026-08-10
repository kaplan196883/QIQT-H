/-
  CurvedA1FintHFarSource — J4-572: SOURCING `hcrude`'s FAR-FIELD ANNULUS first-derivative
  envelope `hFar` (the precisely-carried blocker of J4-571).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`.  J4-571 (`CurvedA1FintHcrudeSource.curved_hFint_hcrude_at_gate`)
  reduced the whole-space crude first-derivative envelope `hcrude` (consumed by
  `CurvedA1FintAdomSource.curved_hFint_hAdom_at_gate`) to three glued regions:

      • `z ∉ K`               — BANKED off-gate vanishing `witnessFieldDeriv_offGate_eq_zero`;
      • `z ∈ K`, `‖z‖ < r`    — the PROVED first-derivative wide transfer from `hFirstEnv`;
      • `z ∈ K`, `‖z‖ ≥ r`    — the CARRIED far-field annulus envelope `hFar`  (the residual/blocker).

  THIS file turns `hFar` — the far-field annulus first-derivative envelope

      `∀ i τ, 0 < τ → τ ≤ T → ∀ z ∈ K, ¬(‖z‖ < r) →
          |witnessFieldDeriv g^K … (constGate … c) a b i τ 0 z|
            ≤ Cfar · (√τ)⁻¹ · gaussDdim (lam·τ) z`

  from a WHOLE-CARRY into a THEOREM, discharged from the PROVED banked whole-`z` first-derivative
  `(⋆)`-WIDE Gaussian domination `CConvV2WitnessStar.witnessFieldDeriv_starWide_onGate` (width `4τ`,
  prefactor `τ^{−1/2} = (√τ)⁻¹`) plus a single genuinely-new SCALAR width-compatibility residual.

  ── THE SATISFIABILITY CORE (why the far-field envelope is TRUE for `g^K`).  On the annulus `z ∈ K`,
  `‖z‖ ≥ r`, the field point `x = 0` STILL lies in the gate (`0 ∈ constGate … c z`, the shared-centre
  gate activation), so the ON-GATE product-rule bound applies — NOT off-gate vanishing.  The banked
  `witnessFieldDeriv_starWide_onGate` delivers, for EVERY `z ∈ K` (annulus included), the genuine
  `(√τ)⁻¹`-prefactor Gaussian envelope at the DOUBLED-DOUBLED width `4τ`, via the GLOBAL near-isometry
  coercivity `½·rncRadialSq z ≤ rncRadialSq (W₀ z)` (which holds for ALL `z ∈ K`, unlike the on-gate
  `poly_absorb` radial gate that is confined to `‖z‖ < r`).  Away from the gate centre the base-point
  Gaussian `gaussDdim (4τ) z` genuinely DECAYS as `‖z‖` grows, dominating any fixed first-jet growth.
  The remaining step — widening `gaussDdim (4τ) z ≤ √(lam/4)ⁿ · gaussDdim (lam·τ) z` — is the free
  pure-Gaussian width upgrade `HeatResidualBound.gaussDdim_le_gaussDdim_chart` (`c = 4 ≤ d = lam`,
  `v = w = z`), TRUE exactly when `4 ≤ lam`.  The `(√τ)⁻¹` prefactor is kept VERBATIM (dropping it is
  the FALSE clean bound).  For `κ < 0 ⊂ κ ≠ 0`, `n ≥ 2` the witness is genuinely curved
  (`curvedRNCMetric_ricci_trace_diag_ne`), so this is NOT secretly flat.

  ── WHAT IS PROVED (axiom-free, no `sorry`).
    •  `curved_hFint_hFar_at_gate` — THE EXACT `hFar` binder consumed by `curved_hFint_hcrude_at_gate`,
       produced (existentially in the constant `Cfar := Cstar·√(lam/4)ⁿ`) from the banked
       `witnessFieldDeriv_starWide_onGate` + the width-upgrade `gaussDdim_le_gaussDdim_chart`.
    •  `curved_hFint_hcrude_via_hFar_at_gate` — the demonstrator: the sourced `hFar` (+ still-carried
       `hFirstEnv`) chained into `curved_hFint_hcrude_at_gate`, producing the whole-space `hcrude`.
    •  `curved_hFint_hFar_at_gate_curved_satisfiable` — the CURVED (not-secretly-flat) gate.

  ── THE CARRIED RESIDUAL (scoped precisely).  Each satisfiable, none the conclusion:
    •  `hlam4 : 4 ≤ (curvedGate κ hChr hK).lam` — the genuinely-NEW scalar width-compatibility (the
       banked star-wide bound is at width `4τ`; the census `hcrude` demands the gate width `lam·τ`).
       The gate `lam` is pinned by `chart_width_gate`; `4 ≤ lam` is the ONE new scalar owed here.
    •  `hSopen`/`hgate0` — gate openness + the shared-centre activation `0 ∈ constGate … c z` (the SAME
       on-gate carries as `chartImage_approx_identity_final`'s `hSact`).
    •  `hdata` — the per-`(i,τ,z)` inverse-chart Jacobian column bound `L`, amplitude value/derivative
       bounds `Ba`/`Bd`, and the GLOBAL near-isometry coercivity — the survivors of the falsified
       `hGateData` (identical to `hStarWide_concrete`'s carry).

  It does NOT make `a₁ = R/6` unconditional: `hFirstEnv`, `hsrc`, `hOffCollarTail`, the convergence
  trio, and `hInnerCont` all remain owed.  NOT `a₁ = R/6`.
-/
import QIQTH.CurvedA1FintHcrudeSource
import QIQTH.CConvV2WitnessStar

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.InverseChartNormalJets QIQTH.WideWitnessAmplitude
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCGaussWitness QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCHeatOpDom2 QIQTH.WidthAdapters QIQTH.CurvedA1FintAdomSource
open QIQTH.CConvV2WitnessStar QIQTH.CurvedA1FintHcrudeSource
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1FintHFarSource

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ###############################################################################
    ### (A) — THE FAR-FIELD ANNULUS `hFar` BINDER FOR `g^K`, sourced from `starWide`.
    ############################################################################### -/

/-- **★★★ J4-572 — `curved_hFint_hFar_at_gate`.**  THE EXACT far-field annulus first-derivative envelope
    `hFar` consumed by `CurvedA1FintHcrudeSource.curved_hFint_hcrude_at_gate`, at the genuinely-curved
    witness `g^K = curvedRNCMetric κ`, SOURCED from the PROVED banked whole-`z` first-derivative
    `(⋆)`-WIDE Gaussian domination `CConvV2WitnessStar.witnessFieldDeriv_starWide_onGate` (width `4τ`,
    prefactor `τ^{−1/2} = (√τ)⁻¹`), widened to the gate width `lam·τ` by the free pure-Gaussian upgrade
    `gaussDdim_le_gaussDdim_chart` (`4 ≤ lam`).  For the produced `Cfar := Cstar·√(lam/4)ⁿ ≥ 0`,

    `∀ i τ, 0 < τ → τ ≤ T → ∀ z ∈ K, ¬(‖z‖ < r) →
        |witnessFieldDeriv g^K … (constGate … c) a b i τ 0 z| ≤ Cfar·(√τ)⁻¹·gaussDdim (lam·τ) z`.

    The far-field envelope is TRUE because on the annulus the field point `0` STILL lies in the gate
    (`hgate0`), so the ON-GATE product-rule bound applies via the GLOBAL near-isometry `hdata` (NOT
    off-gate vanishing); away from the centre the base Gaussian `gaussDdim (4τ) z` decays.  ⚠ The
    `(√τ)⁻¹` prefactor is kept VERBATIM.  NOT `a₁ = R/6`. -/
theorem curved_hFint_hFar_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (T L Ba Bd : ℝ)
    (hL : 0 ≤ L) (hBa0 : 0 ≤ Ba) (hBd0 : 0 ≤ Bd)
    (hlam4 : 4 ≤ (curvedGate κ hChr hK).lam)
    (hSopen : ∀ z ∈ K, IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z))
    (hgate0 : ∀ z ∈ K, (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z)
    (hdata : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K,
      ∃ Pval : Fin n → ℝ,
        (∀ k, HasDerivAt
          (fun r : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
              (Function.update (0 : Point n) i r) k) (Pval k) ((0 : Point n) i))
        ∧ (∀ k, |Pval k| ≤ L)
        ∧ PdiffAt (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)
        ∧ |chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n)| ≤ Ba
        ∧ |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd
        ∧ (1 / 2 : ℝ) * rncRadialSq z
            ≤ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)) :
    ∃ Cfar : ℝ, 0 ≤ Cfar ∧
      ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n, z ∈ K →
        ¬ (‖z‖ < (curvedGate κ hChr hK).r) →
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ Cfar * (Real.sqrt τ)⁻¹ * gaussDdim ((curvedGate κ hChr hK).lam * τ) z := by
  set lam := (curvedGate κ hChr hK).lam with hlamdef
  have hlam0 : 0 < lam := by linarith
  -- the `s`-uniform star-wide constant (width `4τ`, prefactor `τ^{−1/2}`).
  set Cstar : ℝ :=
    Real.sqrt (n : ℝ) * L / 2 * (Real.sqrt 2 * (2 : ℝ) ^ n) * Ba + (2 : ℝ) ^ n * Bd * Real.sqrt T
    with hCstardef
  have hCstar_nn : 0 ≤ Cstar := by
    have h0 : 0 ≤ Real.sqrt (n : ℝ) * L / 2 * (Real.sqrt 2 * (2 : ℝ) ^ n) * Ba :=
      mul_nonneg (mul_nonneg
        (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) (by norm_num)) (by positivity)) hBa0
    have h1 : 0 ≤ (2 : ℝ) ^ n * Bd * Real.sqrt T :=
      mul_nonneg (mul_nonneg (by positivity) hBd0) (Real.sqrt_nonneg _)
    rw [hCstardef]; linarith
  -- the free pure-Gaussian width-upgrade normalizer `√(lam/4)ⁿ`.
  set Cw : ℝ := Real.sqrt (lam / 4) ^ n with hCwdef
  have hCw_nn : 0 ≤ Cw := by rw [hCwdef]; positivity
  refine ⟨Cstar * Cw, mul_nonneg hCstar_nn hCw_nn, ?_⟩
  intro i τ hτ hτT z hzK _hann
  -- the per-point banked star-wide data on the annulus (field point `0 ∈ gate`, global near-isometry).
  obtain ⟨Pval, hJetV, hJac, hAmp1, hBa, hBd, hmin⟩ := hdata i τ hτ hτT z hzK
  -- the banked `(⋆)`-WIDE on-gate first-derivative bound at width `4τ`.
  have hstar := witnessFieldDeriv_starWide_onGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i T τ hτ hτT z hzK
    (hSopen z hzK) (0 : Point n) (hgate0 z hzK) Pval hJetV hAmp1 L Ba Bd hL hJac hBa hBd hmin
  -- convert the rpow prefactor `τ^{−1/2}` into `(√τ)⁻¹`, folding `Cstar`.
  rw [← hCstardef, ← sqrtInv_eq_rpow τ hτ.le] at hstar
  -- the free width upgrade `gaussDdim (4τ) z ≤ Cw · gaussDdim (lam·τ) z`  (`4 ≤ lam`).
  have hnn : 0 ≤ rncRadialSq z := rncRadialSq_nonneg z
  have hwid : gaussDdim (4 * τ) z ≤ Cw * gaussDdim (lam * τ) z := by
    have h := gaussDdim_le_gaussDdim_chart (n := n) (c := 4) (d := lam)
      (by norm_num) hlam0 hτ (v := z) (w := z)
      (by have := mul_le_mul_of_nonneg_right hlam4 hnn; linarith)
    simpa only [hCwdef] using h
  -- combine: keep the `(√τ)⁻¹` prefactor verbatim, widen the Gaussian.
  have hst : 0 ≤ (Real.sqrt τ)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg τ)
  have hCst_st : 0 ≤ Cstar * (Real.sqrt τ)⁻¹ := mul_nonneg hCstar_nn hst
  calc |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
      ≤ Cstar * (Real.sqrt τ)⁻¹ * gaussDdim (4 * τ) z := hstar
    _ ≤ Cstar * (Real.sqrt τ)⁻¹ * (Cw * gaussDdim (lam * τ) z) :=
        mul_le_mul_of_nonneg_left hwid hCst_st
    _ = Cstar * Cw * (Real.sqrt τ)⁻¹ * gaussDdim (lam * τ) z := by ring

/-! ###############################################################################
    ### (B) — DEMONSTRATOR: the sourced `hFar` plugs into `hcrude` VERBATIM.
    ############################################################################### -/

/-- **★★ J4-572 (demonstrator) — `curved_hFint_hcrude_via_hFar_at_gate`.**  The sourced far-field
    annulus envelope `hFar` (§A) chained (together with the STILL-CARRIED chart-image first-jet
    envelope `hFirstEnv`) into `CurvedA1FintHcrudeSource.curved_hFint_hcrude_at_gate`, producing the
    exact WHOLE-SPACE crude first-derivative `hcrude` census binder — proving the sourced `hFar` plugs
    into the downstream carrier VERBATIM.  ⚠ Only `hFirstEnv` remains carried on the `hcrude` reduction
    (the off-gate vanishing and the on-gate width transfer are already PROVED inside
    `curved_hFint_hcrude_at_gate`).  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFint_hcrude_via_hFar_at_gate (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (T A₀ A₁ L Ba Bd : ℝ)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hL : 0 ≤ L) (hBa0 : 0 ≤ Ba) (hBd0 : 0 ≤ Bd)
    (hlam4 : 4 ≤ (curvedGate κ hChr hK).lam)
    (hSopen : ∀ z ∈ K, IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z))
    (hgate0 : ∀ z ∈ K, (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z)
    (hdata : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K,
      ∃ Pval : Fin n → ℝ,
        (∀ k, HasDerivAt
          (fun r : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
              (Function.update (0 : Point n) i r) k) (Pval k) ((0 : Point n) i))
        ∧ (∀ k, |Pval k| ≤ L)
        ∧ PdiffAt (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)
        ∧ |chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n)| ≤ Ba
        ∧ |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd
        ∧ (1 / 2 : ℝ) * rncRadialSq z
            ≤ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0))
    (hFirstEnv : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K,
        ‖z‖ < (curvedGate κ hChr hK).r →
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ (A₀ + A₁ * (rncRadialSq z / τ)) * (Real.sqrt τ)⁻¹
              * gaussDdim τ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)) :
    ∃ Ccrude wA : ℝ, 0 ≤ Ccrude ∧ 0 < wA ∧
      ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z : Point n,
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ Ccrude * (Real.sqrt τ)⁻¹ * gaussDdim (wA * τ) (0 - z) := by
  obtain ⟨Cfar, hCfar, hFar⟩ :=
    curved_hFint_hFar_at_gate κ hChr hK a b c T L Ba Bd hL hBa0 hBd0 hlam4 hSopen hgate0 hdata
  exact curved_hFint_hcrude_at_gate κ hChr hK a b c T A₀ A₁ Cfar hA₀ hA₁ hCfar hFirstEnv hFar

/-! ###############################################################################
    ### (C) — the CURVED (not-secretly-flat) satisfiability GATE.
    ############################################################################### -/

/-- **★ J4-572 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `g^K = curvedRNCMetric κ` is nonzero, so the sourced `hFar`
    binder is discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`; and the
    `(√τ)⁻¹` prefactor is what makes the far-field envelope TRUE (dropping it gives the FALSE clean
    bound).  NOT `a₁ = R/6`. -/
theorem curved_hFint_hFar_at_gate_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1FintHFarSource

section AxiomChecks
open QIQTH.CurvedA1FintHFarSource
#print axioms curved_hFint_hFar_at_gate
#print axioms curved_hFint_hcrude_via_hFar_at_gate
#print axioms curved_hFint_hFar_at_gate_curved_satisfiable
end AxiomChecks
