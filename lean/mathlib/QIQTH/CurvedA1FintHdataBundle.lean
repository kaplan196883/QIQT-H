/-
  CurvedA1FintHdataBundle — J4-580: ρ-RECONCILING the four sibling `hdata` gates into a SINGLE
  bundle for the genuinely-curved witness `g^K = curvedRNCMetric κ` (κ ≤ 0), and feeding it into a
  radius-generic port of `curved_hFint_hFirstEnv_at_gate` to REMOVE the `hdata` hypothesis (on the
  reconciled ρ*-ball).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  No
  `sorry`, no `:= True`, no new axioms, no vacuous / unsatisfiable hypotheses, no conclusion in
  disguise.  std-3 only.  No existing file is edited.

  ## CONTEXT — the `hdata` bundle consumed by `curved_hFint_hFirstEnv_at_gate`.
  `CurvedA1FintHFirstEnvSource.curved_hFint_hFirstEnv_at_gate` (~108-119) carries a per-`(i,τ,z)`
  bundle `hdata`, a conjunction of SIX conjuncts on the FULL gate ball `‖z‖ < (curvedGate κ hChr hK).r`
  with a single `(L, Ba, Bd)` triple:
    (1) `∀ k, HasDerivAt (fun r ↦ uniformInverseChart g^K … z (update 0 i r) k) (Pval k) ((0:Point n) i)`;
    (2) `∀ k, |Pval k| ≤ L`;
    (3) `PdiffAt (chartFieldAmp g^K … a b τ z) i 0`;
    (4) `|chartFieldAmp g^K … a b τ z 0| ≤ Ba`;
    (5) `|pd (chartFieldAmp g^K … a b τ z) i 0| ≤ Bd`;
    (6) `rncRadialSq (uniformInverseChart g^K … z 0) ≤ 2·rncRadialSq z`  (UPPER near-isometry).

  ## WHAT THIS BRICK FINDS (DON'T-UNDERCREDIT).  Each conjunct is ALREADY banked on its own small-ρ
  gate for `g^K`:
    • (1)/(2)  `CurvedA1FintHdataJet.curved_hdata_jet_at_gate`  — `∃ ρ>0, ∃ L≥0, …` on `‖z‖<ρ`.
    • (4)      `CurvedA1FintHdataUniform.curved_hdata_amp_value_uniform_at_gate` — `∃ ρ>0, ∃ Ba≥0, …`.
    • (5)      `CurvedA1FintHdataDerivCont.curved_hdata_amp_deriv_uniform_at_gate` (per `i`, on the
               carrier ball) — `∃ Bd≥0, …`; the `∀ i`-uniform `Bd := ∑ⱼ Bdⱼ` by finite sum.
    • (6)      `CurvedA1FintHdata.curved_hdata_nearIsometry_at_gate` — `∃ r>0, …` (both sides).
    • (3)      `PdiffAt` at general base `z` is obtained WITHOUT the analytic (`ω`, `⊤`) transport-
               coefficient wall: `chartFieldAmp … z = manifoldAmp … ∘ (uniformInverseChart … z)`
               (DEFEQ), `manifoldAmp` is `C²` everywhere (`BaseSlotAmpDeriv.manifoldAmp_contDiffAt`,
               which needs ONLY `hg`/`hgi`/`hgpos` — it invokes `hu_infty_closed` internally at `∞`,
               NOT `⊤`), and the inverse chart is `C²` at `0` (`hreg` from `curved_carriers_at_gate`);
               the composition is `C²`, hence `C¹`, hence `PdiffAt` (`PdiffAt_of_contDiffAt`).

  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `curved_hdata_bundle_at_gate` — ★★★ the FULL six-conjunct `hdata` bundle for `g^K` on the ONE
      reconciled ball `‖z‖ < ρ*`, `ρ* := min` of the four sibling radii and the carrier radius, with a
      single `(L, Ba, Bd)` triple.  Side-condition: the SATISFIABLE reachability gate `K ∈ 𝓝 0`.
    • `curved_hFint_hFirstEnv_on_ball` — ★★ the radius-GENERIC port of `curved_hFint_hFirstEnv_at_gate`:
      the on-ball first-jet two-term envelope for an ARBITRARY radius `r` (the original proof never uses
      any special property of `(curvedGate κ hChr hK).r` beyond feeding it to `hdata`).
    • `curved_hFint_hFirstEnv_hdata_discharged_at_gate` — ★★★ the `hFirstEnv` envelope with `hdata`
      REMOVED, on the reconciled `‖z‖ < ρ*` ball (bundle fed into the radius-generic port).  Still
      carries the gate `hSopen`/`hgate0` (openness + shared-centre activation) — those are NOT `hdata`.
    • `curved_hdata_bundle_gate_satisfiable` / `curved_hdata_bundle_curved_satisfiable` — the
      SATISFIABLE reachability gate + the CURVED (not-secretly-flat) gate.

  ## PRECISE DEPTH VERDICT — DOMAIN HONESTY.
    • The four siblings each expose their OWN radius `ρⱼ`; the reconciliation takes `ρ* := min(ρ₁,…,ρ₄,ρc)`
      and RESTRICTS each conjunct (monotone: `‖z‖<ρ* → ‖z‖<ρⱼ`).  The bundle GENUINELY holds on `‖z‖<ρ*`.
    • ⚠ GATE-RADIUS RESIDUAL.  `curved_hFint_hFirstEnv_at_gate` HARD-CODES its domain as the FULL gate
      ball `‖z‖ < (curvedGate κ hChr hK).r`, and there is NO proof that `ρ* ≥ (curvedGate).r`.  So the
      `hdata` hypothesis of the VERBATIM `curved_hFint_hFirstEnv_at_gate` (full gate ball) CANNOT be
      supplied from the ρ*-ball bundle.  The honest discharge is on the SMALLER `‖z‖<ρ*` ball, obtained
      via the radius-generic port `curved_hFint_hFirstEnv_on_ball`.  Aligning `ρ*` to the gate radius
      (shrinking `(curvedGate).r` to `ρ*`, or proving `ρ* ≥ (curvedGate).r`) is the remaining assembly
      residual — a GEOMETRIC reconciliation, NOT a new analytic wall.

  ⚠  a₁ = R/6 remains CONDITIONAL.  Assembling the `hdata` bundle does NOT make it unconditional — the
  hFar far-field lower coercivity (geometric wall), `hsrc`, `hOffCollarTail`, the convergence trio,
  `hInnerCont`, the gate `hSopen`/`hgate0` carries, AND the gate-radius alignment residual all remain owed.
-/
import QIQTH.CurvedA1FintHFirstEnvSource
import QIQTH.CurvedA1FintHdataJet
import QIQTH.CurvedA1FintHdataUniform
import QIQTH.CurvedA1FintHdata

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.InverseChartNormalJets QIQTH.WideWitnessAmplitude
open QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCGaussWitness QIQTH.A1R6CoreAtGate
open QIQTH.CurvedRNCHeatOpDom2 QIQTH.WidthAdapters QIQTH.CurvedA1FintAdomSource
open QIQTH.CConvV2WitnessStar QIQTH.CConvV2ChartComparison
open QIQTH.CurvedA1FintHcrudeSource QIQTH.CurvedA1FintHFarSource
open QIQTH.CurvedA1FintHdataJet QIQTH.CurvedA1FintHdataUniform
open QIQTH.CurvedA1FintHdataDerivCont QIQTH.CurvedA1FintHdataReg
open QIQTH.CurvedA1FintHdata QIQTH.CurvedRNCPosDef QIQTH.BaseSlotAmpDeriv
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1FintHdataBundle

set_option maxHeartbeats 3200000

variable {n : ℕ}

/-! ###############################################################################
    ### ★★★ THE RECONCILED `hdata` BUNDLE — all six conjuncts on ONE ball for `g^K`.
    ############################################################################### -/

/-- **★★★ J4-580 — `curved_hdata_bundle_at_gate`.**  The FULL six-conjunct `hdata` bundle consumed by
    `CurvedA1FintHFirstEnvSource.curved_hFint_hFirstEnv_at_gate`, for the genuinely-curved witness
    `g^K = curvedRNCMetric κ` (`κ ≤ 0`), reconciled onto ONE ball `‖z‖ < ρ*` with a single `(L,Ba,Bd)`
    triple.  Assembled from the four PROVED siblings (`curved_hdata_jet_at_gate`,
    `curved_hdata_amp_value_uniform_at_gate`, `curved_hdata_amp_deriv_uniform_at_gate`,
    `curved_hdata_nearIsometry_at_gate`) plus the `PdiffAt` conjunct via
    `manifoldAmp_contDiffAt ∘ hreg`.  `ρ* := min` of the sibling radii + carrier radius; `Bd := ∑ⱼ Bdⱼ`
    the finite-`max`-over-`Fin n` uniformizer.  Side-condition: the SATISFIABLE reachability gate
    `K ∈ 𝓝 0`.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hdata_bundle_at_gate (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) (a b T : ℝ) :
    ∃ ρ > (0 : ℝ), ∃ L Ba Bd : ℝ, 0 ≤ L ∧ 0 ≤ Ba ∧ 0 ≤ Bd ∧
      ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K, ‖z‖ < ρ →
        ∃ Pval : Fin n → ℝ,
          (∀ k, HasDerivAt
            (fun r : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
                (Function.update (0 : Point n) i r) k) (Pval k) ((0 : Point n) i))
          ∧ (∀ k, |Pval k| ≤ L)
          ∧ PdiffAt (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)
          ∧ |chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n)| ≤ Ba
          ∧ |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd
          ∧ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
              ≤ 2 * rncRadialSq z := by
  -- the three inverse-chart regularity carriers on ONE ball (`ρc`).
  obtain ⟨ρc, hρc, hreg, hW0, hJac⟩ := curved_carriers_at_gate κ hChr hK h0Kmem
  -- conjuncts (1)/(2): the inverse-chart first jet + column bound `L`.
  obtain ⟨ρ1, hρ1, L, hL, hjet⟩ := curved_hdata_jet_at_gate κ hChr hK h0Kmem T
  -- conjunct (4): the uniform amplitude value bound `Ba`.
  obtain ⟨ρ2, hρ2, Ba, hBa0, hampval⟩ :=
    curved_hdata_amp_value_uniform_at_gate κ hκ hChr hK h0Kmem a b T
  -- conjunct (5): the uniform amplitude derivative bound, per `i`, on the SAME carrier ball `ρc`.
  have hBdi : ∀ i : Fin n, ∃ Bd : ℝ, 0 ≤ Bd ∧
      ∀ (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K, ‖z‖ < ρc →
        |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd :=
    fun i => curved_hdata_amp_deriv_uniform_at_gate κ hκ hChr hK a b T i ρc hρc hreg hW0 hJac
  choose Bdf hBdf0 hBdf using hBdi
  set Bd := ∑ j, Bdf j with hBddef
  have hBd0 : 0 ≤ Bd := Finset.sum_nonneg (fun j _ => hBdf0 j)
  have hBdi_le : ∀ i : Fin n, Bdf i ≤ Bd :=
    fun i => Finset.single_le_sum (fun j _ => hBdf0 j) (Finset.mem_univ i)
  -- conjunct (6): the two-sided near-isometry (UPPER side used).
  obtain ⟨r4, hr4, hnear⟩ := curved_hdata_nearIsometry_at_gate κ hChr hK
  -- geometry carriers for conjunct (3) `PdiffAt` (no `⊤`/`ω` transport wall).
  have hgC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => curvedRNCMetric κ y a b) :=
    fun a b => curvedRNCMetric_contDiff κ a b
  have hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y : Point n => curvedRNCInv κ y a b) :=
    fun a b => curvedRNCInv_contDiff κ hκ a b
  have hgpos : ∀ v : Point n, 0 < Matrix.det (curvedRNCMetric κ v) := curvedRNCMetric_hgpos κ hκ
  -- reconcile the radii: `ρ* := min ρ1 (min ρ2 (min ρc r4))`.
  refine ⟨min ρ1 (min ρ2 (min ρc r4)), lt_min hρ1 (lt_min hρ2 (lt_min hρc hr4)),
    L, Ba, Bd, hL, hBa0, hBd0, ?_⟩
  intro i τ hτ hτT z hzK hzρ
  -- sub-radius facts (monotone restriction).
  have hz1 : ‖z‖ < ρ1 := lt_of_lt_of_le hzρ (min_le_left _ _)
  have hz2 : ‖z‖ < ρ2 := lt_of_lt_of_le hzρ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hzc : ‖z‖ < ρc :=
    lt_of_lt_of_le hzρ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hz4 : ‖z‖ < r4 :=
    lt_of_lt_of_le hzρ (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- (1)/(2): the jet column.
  obtain ⟨Pval, hderiv, hPval_le⟩ := hjet i τ hτ hτT z hzK hz1
  refine ⟨Pval, hderiv, hPval_le, ?_, ?_, ?_, ?_⟩
  · -- (3): `PdiffAt` via `manifoldAmp_contDiffAt ∘ hreg` (DEFEQ composition).
    have hzmem : z ∈ Metric.closedBall (0 : Point n) ρc := mem_closedBall_zero_iff.mpr hzc.le
    have hM : ContDiffAt ℝ 2 (manifoldAmp (curvedRNCMetric κ) (curvedRNCInv κ) a b τ)
        (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0) :=
      manifoldAmp_contDiffAt (curvedRNCMetric κ) (curvedRNCInv κ) hgC hgiC hgpos a b τ
        (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
    have hcomp : ContDiffAt ℝ 2
        (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) (0 : Point n) :=
      hM.comp (0 : Point n) (hreg z hzmem)
    exact QIQTH.LaplaceBeltrami.PdiffAt_of_contDiffAt _ i 0 (hcomp.of_le (by norm_num))
  · -- (4): amplitude value.
    exact hampval i τ hτ hτT z hzK hz2
  · -- (5): amplitude derivative, lifted to the uniform `Bd`.
    exact le_trans (hBdf i τ hτ hτT z hzK hzc) (hBdi_le i)
  · -- (6): UPPER near-isometry.
    exact (hnear z hzK hz4).2

/-! ###############################################################################
    ### ★★ THE RADIUS-GENERIC PORT of `curved_hFint_hFirstEnv_at_gate`.
    ############################################################################### -/

/-- **★★ J4-580 — `curved_hFint_hFirstEnv_on_ball`.**  The radius-GENERIC port of
    `CurvedA1FintHFirstEnvSource.curved_hFint_hFirstEnv_at_gate`: the on-ball chart-image first-jet
    two-term envelope for an ARBITRARY radius `r`.  The original proof never uses any property of
    `(curvedGate κ hChr hK).r` beyond passing it to `hdata`, so it ports VERBATIM with `r` a free
    parameter.  ⚠ The `(√τ)⁻¹` prefactor is kept VERBATIM (dropping it is the FALSE bound).
    NOT `a₁ = R/6`. -/
theorem curved_hFint_hFirstEnv_on_ball (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (T L Ba Bd : ℝ)
    (hL : 0 ≤ L) (hBa0 : 0 ≤ Ba) (hBd0 : 0 ≤ Bd) (r : ℝ)
    (hSopen : ∀ z ∈ K, IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z))
    (hgate0 : ∀ z ∈ K, (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z)
    (hdata : ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K, ‖z‖ < r →
      ∃ Pval : Fin n → ℝ,
        (∀ k, HasDerivAt
          (fun r : ℝ => uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z
              (Function.update (0 : Point n) i r) k) (Pval k) ((0 : Point n) i))
        ∧ (∀ k, |Pval k| ≤ L)
        ∧ PdiffAt (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)
        ∧ |chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n)| ≤ Ba
        ∧ |pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)| ≤ Bd
        ∧ rncRadialSq (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0)
            ≤ 2 * rncRadialSq z) :
    ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
      ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K, ‖z‖ < r →
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ (A₀ + A₁ * (rncRadialSq z / τ)) * (Real.sqrt τ)⁻¹
              * gaussDdim τ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0) := by
  refine ⟨Real.sqrt (n : ℝ) * L / 2 * Ba + Bd * Real.sqrt T, Real.sqrt (n : ℝ) * L * Ba, ?_, ?_, ?_⟩
  · have h1 : 0 ≤ Real.sqrt (n : ℝ) * L / 2 * Ba :=
      mul_nonneg (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) (by norm_num)) hBa0
    have h2 : 0 ≤ Bd * Real.sqrt T := mul_nonneg hBd0 (Real.sqrt_nonneg _)
    linarith
  · exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) hBa0
  · intro i τ hτ hτT z hzK hzr
    obtain ⟨Pval, hJetV, hJac, hAmp1, hBa, hBd, hUpper⟩ := hdata i τ hτ hτT z hzK hzr
    rw [witnessFieldDeriv_productRule (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
          (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ hτ z hzK
          (hSopen z hzK) (0 : Point n) (hgate0 z hzK) Pval hJetV hAmp1]
    set W := uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 with hWdef
    set G := gaussDdim τ W with hGdef
    set A := chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z (0 : Point n) with hAdef
    set dA := pd (chartFieldAmp (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK a b τ z) i (0 : Point n)
      with hdAdef
    set st := (Real.sqrt τ)⁻¹ with hstdef
    have hτpos : (0 : ℝ) < 2 * τ := by linarith
    have hGnn : 0 ≤ G := gaussDdim_nonneg _ _
    have hst : 0 ≤ st := inv_nonneg.mpr (Real.sqrt_nonneg τ)
    have hBa' : 0 ≤ Ba := le_trans (abs_nonneg _) hBa
    have hBd' : 0 ≤ Bd := le_trans (abs_nonneg _) hBd
    have hnum : |∑ k, W k * Pval k| ≤ Real.sqrt (rncRadialSq W) * (Real.sqrt (n : ℝ) * L) :=
      numerator_le_radial_mul W Pval L hL hJac
    have habs_sc : |(-(∑ k, W k * Pval k) / (2 * τ))| = |∑ k, W k * Pval k| / (2 * τ) := by
      rw [abs_div, abs_neg, abs_of_pos hτpos]
    have hkey : Real.sqrt (rncRadialSq W) * τ⁻¹ ≤ (1 + rncRadialSq W / τ) * st := by
      have hy : (0 : ℝ) ≤ rncRadialSq W / τ := div_nonneg (rncRadialSq_nonneg W) hτ.le
      have hsq : Real.sqrt (rncRadialSq W / τ) ≤ 1 + rncRadialSq W / τ := by
        have h := Real.sqrt_le_sqrt
          (show rncRadialSq W / τ ≤ (1 + rncRadialSq W / τ) ^ 2 by
            nlinarith [sq_nonneg (rncRadialSq W / τ), hy])
        rwa [Real.sqrt_sq (by linarith)] at h
      have heq : Real.sqrt (rncRadialSq W / τ) = Real.sqrt (rncRadialSq W) * st := by
        rw [hstdef, div_eq_mul_inv, Real.sqrt_mul (rncRadialSq_nonneg W), Real.sqrt_inv]
      have hst2 : st * st = τ⁻¹ := by rw [hstdef, ← mul_inv, Real.mul_self_sqrt hτ.le]
      calc Real.sqrt (rncRadialSq W) * τ⁻¹
          = Real.sqrt (rncRadialSq W) * (st * st) := by rw [hst2]
        _ = (Real.sqrt (rncRadialSq W) * st) * st := by ring
        _ = Real.sqrt (rncRadialSq W / τ) * st := by rw [heq]
        _ ≤ (1 + rncRadialSq W / τ) * st := mul_le_mul_of_nonneg_right hsq hst
    have hone : (1 : ℝ) ≤ Real.sqrt T * st := by
      rw [hstdef, ← div_eq_mul_inv, one_le_div (Real.sqrt_pos.mpr hτ)]
      exact Real.sqrt_le_sqrt hτT
    have h1 : |∑ k, W k * Pval k| / (2 * τ) * |A|
        ≤ (Real.sqrt (n : ℝ) * L / 2 * Ba) * st
            + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ) * st := by
      have hinv0 : 0 ≤ (2 * τ)⁻¹ := inv_nonneg.mpr hτpos.le
      have hMnn : 0 ≤ Real.sqrt (n : ℝ) * L * Ba / 2 :=
        div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hL) hBa0) (by norm_num)
      calc |∑ k, W k * Pval k| / (2 * τ) * |A|
          = |∑ k, W k * Pval k| * (2 * τ)⁻¹ * |A| := by rw [div_eq_mul_inv]
        _ ≤ (Real.sqrt (rncRadialSq W) * (Real.sqrt (n : ℝ) * L)) * (2 * τ)⁻¹ * Ba := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hnum hinv0) hBa (abs_nonneg _) ?_
            exact mul_nonneg
              (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hL)) hinv0
        _ = (Real.sqrt (n : ℝ) * L * Ba / 2) * (Real.sqrt (rncRadialSq W) * τ⁻¹) := by
            rw [mul_inv]; ring
        _ ≤ (Real.sqrt (n : ℝ) * L * Ba / 2) * ((1 + rncRadialSq W / τ) * st) :=
            mul_le_mul_of_nonneg_left hkey hMnn
        _ ≤ (Real.sqrt (n : ℝ) * L * Ba / 2) * ((1 + 2 * rncRadialSq z / τ) * st) := by
            refine mul_le_mul_of_nonneg_left ?_ hMnn
            refine mul_le_mul_of_nonneg_right ?_ hst
            have hbridge : rncRadialSq W / τ ≤ 2 * rncRadialSq z / τ := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right hUpper (inv_nonneg.mpr hτ.le)
            linarith
        _ = (Real.sqrt (n : ℝ) * L / 2 * Ba) * st
              + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ) * st := by ring
    have hd : |dA| ≤ Bd * Real.sqrt T * st := by
      calc |dA| ≤ Bd := hBd
        _ ≤ Bd * (Real.sqrt T * st) := le_mul_of_one_le_right hBd' hone
        _ = Bd * Real.sqrt T * st := by ring
    have hpre : |(-(∑ k, W k * Pval k) / (2 * τ))| * |A| + |dA|
        ≤ ((Real.sqrt (n : ℝ) * L / 2 * Ba + Bd * Real.sqrt T)
            + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ)) * st := by
      rw [habs_sc]
      calc |∑ k, W k * Pval k| / (2 * τ) * |A| + |dA|
          ≤ ((Real.sqrt (n : ℝ) * L / 2 * Ba) * st
                + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ) * st)
              + Bd * Real.sqrt T * st := add_le_add h1 hd
        _ = ((Real.sqrt (n : ℝ) * L / 2 * Ba + Bd * Real.sqrt T)
              + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ)) * st := by ring
    have eqL : |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A|
        = G * |(-(∑ k, W k * Pval k) / (2 * τ))| * |A| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hGnn]
    have eqR : |G * dA| = G * |dA| := by rw [abs_mul, abs_of_nonneg hGnn]
    calc |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A + G * dA|
        ≤ |G * (-(∑ k, W k * Pval k) / (2 * τ)) * A| + |G * dA| := abs_add_le _ _
      _ = G * |(-(∑ k, W k * Pval k) / (2 * τ))| * |A| + G * |dA| := by rw [eqL, eqR]
      _ = G * (|(-(∑ k, W k * Pval k) / (2 * τ))| * |A| + |dA|) := by ring
      _ ≤ G * (((Real.sqrt (n : ℝ) * L / 2 * Ba + Bd * Real.sqrt T)
            + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ)) * st) :=
          mul_le_mul_of_nonneg_left hpre hGnn
      _ = ((Real.sqrt (n : ℝ) * L / 2 * Ba + Bd * Real.sqrt T)
            + (Real.sqrt (n : ℝ) * L * Ba) * (rncRadialSq z / τ)) * st * G := by ring

/-! ###############################################################################
    ### ★★★ THE `hFirstEnv` ENVELOPE with `hdata` DISCHARGED (on the reconciled ρ*-ball).
    ############################################################################### -/

/-- **★★★ J4-580 — `curved_hFint_hFirstEnv_hdata_discharged_at_gate`.**  The on-ball first-jet
    two-term `hFirstEnv` envelope for `g^K = curvedRNCMetric κ` (`κ ≤ 0`) with the `hdata` hypothesis
    REMOVED — discharged from the reconciled bundle `curved_hdata_bundle_at_gate` fed into the
    radius-generic port `curved_hFint_hFirstEnv_on_ball`.  Holds on the reconciled ball `‖z‖ < ρ*`
    (⚠ NOT the full gate ball `(curvedGate κ hChr hK).r`: the ρ*-vs-gate-radius alignment is the
    remaining geometric residual — see the file header).  Still carries the gate `hSopen`/`hgate0`
    (NOT `hdata`).  Side-condition: the SATISFIABLE reachability gate `K ∈ 𝓝 0`.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hFint_hFirstEnv_hdata_discharged_at_gate (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n)) (a b c T : ℝ)
    (hSopen : ∀ z ∈ K, IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z))
    (hgate0 : ∀ z ∈ K, (0 : Point n) ∈ constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c z) :
    ∃ ρ > (0 : ℝ), ∃ A₀ A₁ : ℝ, 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
      ∀ (i : Fin n) (τ : ℝ), 0 < τ → τ ≤ T → ∀ z ∈ K, ‖z‖ < ρ →
        |witnessFieldDeriv (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK c) a b i τ (0 : Point n) z|
          ≤ (A₀ + A₁ * (rncRadialSq z / τ)) * (Real.sqrt τ)⁻¹
              * gaussDdim τ (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0) := by
  obtain ⟨ρ, hρ, L, Ba, Bd, hL, hBa0, hBd0, hbundle⟩ :=
    curved_hdata_bundle_at_gate κ hκ hChr hK h0Kmem a b T
  obtain ⟨A₀, A₁, hA₀, hA₁, henv⟩ :=
    curved_hFint_hFirstEnv_on_ball κ hChr hK a b c T L Ba Bd hL hBa0 hBd0 ρ hSopen hgate0 hbundle
  exact ⟨ρ, hρ, A₀, A₁, hA₀, hA₁, henv⟩

/-! ###############################################################################
    ### the SATISFIABILITY gates.
    ############################################################################### -/

/-- **★ J4-580 (reachability-gate satisfiability).**  The side-condition `K ∈ 𝓝 0` is achievable:
    `closedBall 0 1` is a compact neighbourhood of the base point `0`.  NON-VACUOUS.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_hdata_bundle_gate_satisfiable :
    ∃ K : Set (Point n), IsCompact K ∧ K ∈ 𝓝 (0 : Point n) :=
  ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩

/-- **★ J4-580 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  For `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0) = n(n−1)κ`) of `g^K = curvedRNCMetric κ` is nonzero, so the assembled
    bundle is discharged at a genuinely curved witness (`κ < 0 ⊂ κ ≠ 0`), NOT the flat `δ`.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_hdata_bundle_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedA1FintHdataBundle

section AxiomChecks
open QIQTH.CurvedA1FintHdataBundle
#print axioms curved_hdata_bundle_at_gate
#print axioms curved_hFint_hFirstEnv_on_ball
#print axioms curved_hFint_hFirstEnv_hdata_discharged_at_gate
#print axioms curved_hdata_bundle_gate_satisfiable
#print axioms curved_hdata_bundle_curved_satisfiable
end AxiomChecks
