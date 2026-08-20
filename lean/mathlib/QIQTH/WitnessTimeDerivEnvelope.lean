/-
  WitnessTimeDerivEnvelope — the CRUDE TIME-DERIVATIVE Gaussian envelope `hAcrude`, DISCHARGED to the
  zeroth-amplitude carries (the `WideAmplitudeData.second_domination` class) via the EXACT `∂_τ` closed form.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a pure
  ANALYSIS-INFRASTRUCTURE brick.  It discharges the GEOMETRIC CORE of the crude time-derivative Gaussian
  envelope `hAcrude`
      `|deriv (fun r => vanVleckGatedWitness … r 0 z) τ| ≤ C · τ⁻¹ · gaussDdim (wL·τ) z`
  (the doubly-load-bearing carry of `DerivDomLowerCapped.derivDom_boundD_of_crude` (J4-911, `boundD`) and
  `HZDataFromCrudeEnv.hZslice_of_crudeEnv` (J4-916, `hZ`)) DIRECTLY from the banked EXACT `∂_τ` closed form
  `GatedTauDerivRep.witnessTauDeriv_eq_gatedTauRepProd` (which J4-915 revealed to be explicit and
  unconditional), reducing it to the SAME zeroth-order amplitude sup-bounds `{|chartFieldAmp| ≤ M,
  |Cfield| ≤ M'}` already carried (as `hAmp0`) by the accepted `WideWitnessAmplitude.WideAmplitudeData`
  zeroth / second dominations.  No `sorry` (header prose excepted), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypothesis (satisfiability EXHIBITED below at a nonempty singleton gate), none
  equal to (or trivially yielding) the conclusion, no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE CLOSED FORM (banked, `gatedTauRepProd`).  On the gate the witness time-derivative is EXACTLY
      `∂_τ Wit = (∑ᵢ ((vᵢ²/(4τ²)) − 1/(2τ)))·gaussDdim τ(v)·A(τ)  +  gaussDdim τ(v)·Cfield`,
  `v = uniformInverseChart z 0` (the chart image), `A = chartFieldAmp` (AFFINE in τ), `Cfield = ∂_τ A`
  (constant in τ).  Taking magnitudes and triangulating the coefficient
      `|∑ᵢ(vᵢ²/4τ² − 1/2τ)| ≤ rncRadialSq v/(4τ²) + n/(2τ)`
  gives three pieces, each of worst rate `τ⁻¹` (the SECOND-spatial-derivative rate, via `∂_τ G = ΔG`):

  ## THE ABSORPTION CHAIN (all banked).
    •  Piece 1 (`rncRadialSq v/(4τ²)·G·A`): the CHART-IMAGE radial polynomial `rncRadialSq v/τ` is absorbed
       into a wider CHART-IMAGE Gaussian by the SELF-application of `GaussianWidthTransfer.gaussDdim_poly_absorb`
       at FIXED gap `(η,lam)=(1/2,4)` with `w := z := v` (gate `(1−1/2)·rncRadialSq v ≤ rncRadialSq v`
       holds since `1/2 ≤ 1`), then transferred to the BASE Gaussian by `FixedFlowGateData.poly_absorb 0`
       at the scaled width `4τ`.  Lands at width `4·lam·τ`, rate `τ⁻¹`.
    •  Pieces 2/3 (`n/(2τ)·G·A`, `G·Cfield`): `FixedFlowGateData.poly_absorb 0` (base transfer at width τ),
       then `HrawCampaignOne.gaussDdim_width_mono` widens `lam·τ ↦ 4·lam·τ`.  Piece 3 (rate `τ⁰`) gets its
       `τ⁻¹` from `1 ≤ τ₀·τ⁻¹` on `τ ≤ τ₀`.
    All three land at the common width `4·lam·τ`, giving `wL = 4·lam`.

  ⚠  STILL NOT `a₁ = R/6`.  The remaining carries `hAmp0`/`hCfield` (zeroth amplitude / slope sup-bounds on
  the compact gate) are the SAME `WideAmplitudeData.hAmp0` class already accepted; `a₁ = R/6` remains
  CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.  Wiring this into the LIVE `boundD`/`hZ` census consumers
  (global-`z` extension + `τ`-cap alignment) is a downstream step, not done here.
-/
import Mathlib
import QIQTH.GatedTauDerivRep
import QIQTH.OnGateJets
import QIQTH.InverseChartNormalJets
import QIQTH.HrawCampaignOne
import QIQTH.WideWitnessAmplitude

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound QIQTH.InnerKernelJointMeas
open QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.GaussianWidthTransfer QIQTH.InverseChartNormalJets
open QIQTH.GatedTauDerivRep QIQTH.OnGateJets
open QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion
open scoped Topology BigOperators ContDiff

namespace QIQTH.WitnessTimeDerivEnvelope

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ###############################################################################
    ### §A — the coefficient magnitude bound (pure `Finset` triangle inequality).
    ############################################################################### -/

/-- **★ `tauCoeff_abs_bound`.**  The `∂_τ`-closed-form scalar coefficient is triangulated:
        `|∑ᵢ ((vᵢ²/(4τ²)) − 1/(2τ))| ≤ rncRadialSq v/(4τ²) + n/(2τ)`   (for `τ > 0`).
    Pure `Finset.abs_sum_le_sum_abs` + per-term `|a − b| ≤ a + b` (both nonneg).  NOT `a₁ = R/6`. -/
theorem tauCoeff_abs_bound (v : Point n) {τ : ℝ} (hτ : 0 < τ) :
    |∑ i, ((v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))|
      ≤ rncRadialSq v / (4 * τ ^ 2) + (n : ℝ) / (2 * τ) := by
  have hsum1 : ∑ i : Fin n, (v i) ^ 2 / (4 * τ ^ 2) = rncRadialSq v / (4 * τ ^ 2) := by
    simp only [rncRadialSq]; rw [← Finset.sum_div]
  have hsum2 : ∑ _i : Fin n, (1 : ℝ) / (2 * τ) = (n : ℝ) / (2 * τ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  calc |∑ i, ((v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))|
      ≤ ∑ i, |(v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ((v i) ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h1 : 0 ≤ (v i) ^ 2 / (4 * τ ^ 2) := by positivity
        have h2 : 0 ≤ (1 : ℝ) / (2 * τ) := by
          apply div_nonneg (by norm_num); linarith
        rw [abs_le]; exact ⟨by nlinarith [h1, h2], by nlinarith [h1, h2]⟩
    _ = rncRadialSq v / (4 * τ ^ 2) + (n : ℝ) / (2 * τ) := by
        rw [Finset.sum_add_distrib, hsum1, hsum2]

/-! ###############################################################################
    ### §B — the concrete on-gate `∂_τ` domination (the `hAcrude` shape on the gate ball).
    ############################################################################### -/

/-- **★★★ `witnessTimeDeriv_domination` — THE CRUDE TIME-DERIVATIVE ENVELOPE, on the gate ball.**  For the
    concrete gated van-Vleck witness `Wit := vanVleckGatedWitness g gi hC hK S a b`, a fixed width-gate
    record `D`, a time cap `τ₀`, and the carried zeroth-amplitude data
      • `Cfield` + `hgate` — the on-gate amplitude `∂_τ` `HasDerivAt` (the exact `GatedTauDerivRep`
        conjunct; BANKED unconditional via `OnGateJets.chartFieldAmp_hasDerivAt_tau`);
      • `hAmp0`  — `|chartFieldAmp … τ z 0| ≤ M` (zeroth amplitude sup, the accepted `WideAmplitudeData.hAmp0`);
      • `hCfield` — `|Cfield z 0| ≤ M'` (zeroth amplitude-SLOPE sup, same class),
    there is an explicit `C > 0` with, uniformly over `0 < τ ≤ τ₀` and every gate base point `z ∈ K`,
    `‖z‖ < D.r`,
        `|deriv (fun r => Wit r 0 z) τ| ≤ C · τ⁻¹ · gaussDdim (4·D.lam·τ) z`.
    Route: the EXACT `∂_τ` closed form (`witnessTauDeriv_eq_gatedTauRepProd`) + `tauCoeff_abs_bound` +
    self-absorption of the chart-image radial (`gaussDdim_poly_absorb` at gap `(1/2,4)`) + base transfer
    (`D.poly_absorb 0`) + width unification (`gaussDdim_width_mono`).  NOT `a₁ = R/6`. -/
theorem witnessTimeDeriv_domination (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK) (τ₀ M M' : ℝ)
    (hτ₀ : 0 < τ₀) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (Cfield : Point n → Point n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        w.2.1 ∈ S w.2.2 ∧
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |Cfield z 0| ≤ M') :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
      |deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) τ|
        ≤ C * τ⁻¹ * gaussDdim (4 * D.lam * τ) z := by
  -- uniform constants (independent of τ, z).
  have hlampos : 0 < D.lam := lt_trans one_pos D.hlam
  set Kw : ℝ := Real.sqrt ((4 * D.lam) / D.lam) ^ n with hKwdef
  have hKwnn : 0 ≤ Kw := by positivity
  obtain ⟨C₀, hC₀pos, habs0⟩ := D.poly_absorb 0
  obtain ⟨C₁, hC₁pos, hself⟩ :=
    gaussDdim_poly_absorb (n := n) (η := (1 : ℝ) / 2) (lam := (4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) 1
  -- the assembled uniform constant.
  set Ctot : ℝ := M * (C₁ * C₀ / 4) + M * ((n : ℝ) * C₀ * Kw / 2) + M' * C₀ * Kw * τ₀ with hCtotdef
  have hCtotnn : 0 ≤ Ctot := by
    rw [hCtotdef]
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · exact mul_nonneg hM (div_nonneg (mul_nonneg hC₁pos.le hC₀pos.le) (by norm_num))
    · exact mul_nonneg hM
        (div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hC₀pos.le) hKwnn) (by norm_num))
    · exact mul_nonneg (mul_nonneg (mul_nonneg hM' hC₀pos.le) hKwnn) hτ₀.le
  refine ⟨Ctot + 1, by linarith [hCtotnn], ?_⟩
  intro τ hτ hτ0 z hz hzr
  have hτne : τ ≠ 0 := hτ.ne'
  set v : Point n := uniformInverseChart g gi hC hK z 0 with hvdef
  set Gv : ℝ := gaussDdim τ v with hGvdef
  set Gl : ℝ := gaussDdim (4 * D.lam * τ) z with hGldef
  have hGvnn : 0 ≤ Gv := gaussDdim_nonneg τ v
  have hGlnn : 0 ≤ Gl := gaussDdim_nonneg _ _
  -- rewrite the witness time-derivative by its exact closed form, then evaluate the on-gate indicator.
  have hident := witnessTauDeriv_eq_gatedTauRepProd hn g gi hC hK S a b Cfield hgate (τ, (0 : Point n), z)
  have hval : deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) τ
      = ((∑ i, ((v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * Gv)
          * chartFieldAmp g gi hC hK a b τ z 0
        + Gv * Cfield z 0 := by
    rw [hident]
    simp only [gatedTauRepProd,
      Set.indicator_of_mem
        (show ((τ : ℝ), (0 : Point n), z) ∈ {w : ℝ × Point n × Point n | w.2.2 ∈ K} from hz),
      ← hvdef, ← hGvdef]
  rw [hval]
  -- the three-piece magnitude bound.
  set P : ℝ := rncRadialSq v / (4 * τ ^ 2) + (n : ℝ) / (2 * τ) with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    refine add_nonneg (div_nonneg (rncRadialSq_nonneg v) (by positivity))
      (div_nonneg (Nat.cast_nonneg n) (by linarith))
  have hcoef : |∑ i, ((v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| ≤ P := tauCoeff_abs_bound v hτ
  have hamp : |chartFieldAmp g gi hC hK a b τ z 0| ≤ M := hAmp0 τ hτ hτ0 z hz hzr
  have hcf : |Cfield z 0| ≤ M' := hCfield z hz hzr
  -- STEP 1: reduce to `P·Gv·M + Gv·M'`.
  have hstep : |((∑ i, ((v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * Gv)
        * chartFieldAmp g gi hC hK a b τ z 0 + Gv * Cfield z 0|
      ≤ P * Gv * M + Gv * M' := by
    calc |((∑ i, ((v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * Gv)
            * chartFieldAmp g gi hC hK a b τ z 0 + Gv * Cfield z 0|
        ≤ |((∑ i, ((v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))) * Gv)
              * chartFieldAmp g gi hC hK a b τ z 0| + |Gv * Cfield z 0| := abs_add_le _ _
      _ = |∑ i, ((v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * Gv
              * |chartFieldAmp g gi hC hK a b τ z 0| + Gv * |Cfield z 0| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hGvnn, abs_mul, abs_of_nonneg hGvnn]
      _ ≤ P * Gv * M + Gv * M' := by
            have hA : |∑ i, ((v i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ))| * Gv
                  * |chartFieldAmp g gi hC hK a b τ z 0| ≤ P * Gv * M :=
              mul_le_mul (mul_le_mul_of_nonneg_right hcoef hGvnn) hamp (abs_nonneg _)
                (mul_nonneg hPnn hGvnn)
            have hB : Gv * |Cfield z 0| ≤ Gv * M' := mul_le_mul_of_nonneg_left hcf hGvnn
            exact add_le_add hA hB
  refine le_trans hstep ?_
  -- STEP 2: the absorption facts.
  have hbaseτ : Gv ≤ C₀ * gaussDdim (D.lam * τ) z := by
    have h := habs0 τ hτ z hz hzr
    simp only [pow_zero, one_mul, ← hvdef, ← hGvdef] at h
    exact h
  have hbase4τ : gaussDdim (4 * τ) v ≤ C₀ * gaussDdim (4 * D.lam * τ) z := by
    have h := habs0 (4 * τ) (by linarith) z hz hzr
    have hw : D.lam * (4 * τ) = 4 * D.lam * τ := by ring
    simp only [pow_zero, one_mul, ← hvdef, hw] at h
    exact h
  have hselfv : (rncRadialSq v / τ) * Gv ≤ C₁ * gaussDdim (4 * τ) v := by
    have hgateself : (1 - (1 : ℝ) / 2) * rncRadialSq v ≤ rncRadialSq v := by
      nlinarith [rncRadialSq_nonneg v]
    have h := hself τ hτ v v hgateself
    simp only [pow_one, ← hGvdef] at h
    exact h
  have hpush : gaussDdim (D.lam * τ) z ≤ Kw * Gl :=
    QIQTH.HrawCampaignOne.gaussDdim_width_mono (w₀ := D.lam) (w₁ := 4 * D.lam) hlampos (by linarith) hτ z
  -- STEP 3: bound each of the three pieces by `cᵢ·τ⁻¹·Gl`.
  have hP1 : (rncRadialSq v / (4 * τ ^ 2)) * Gv ≤ (C₁ * C₀ / 4) * τ⁻¹ * Gl := by
    have e1 : (rncRadialSq v / (4 * τ ^ 2)) * Gv
        = (1 / (4 * τ)) * ((rncRadialSq v / τ) * Gv) := by
      field_simp
    rw [e1]
    have h4t : 0 ≤ (1 : ℝ) / (4 * τ) := by apply div_nonneg (by norm_num); linarith
    have h14 : (1 : ℝ) / (4 * τ) = 4⁻¹ * τ⁻¹ := by rw [one_div, mul_inv]
    calc (1 / (4 * τ)) * ((rncRadialSq v / τ) * Gv)
        ≤ (1 / (4 * τ)) * (C₁ * gaussDdim (4 * τ) v) :=
          mul_le_mul_of_nonneg_left hselfv h4t
      _ ≤ (1 / (4 * τ)) * (C₁ * (C₀ * Gl)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbase4τ hC₁pos.le) h4t
      _ = (C₁ * C₀ / 4) * τ⁻¹ * Gl := by rw [h14]; ring
  have hP2 : ((n : ℝ) / (2 * τ)) * Gv ≤ ((n : ℝ) * C₀ * Kw / 2) * τ⁻¹ * Gl := by
    have hnn : 0 ≤ (n : ℝ) / (2 * τ) := by apply div_nonneg (Nat.cast_nonneg n); linarith
    have h12 : (n : ℝ) / (2 * τ) = (n : ℝ) * 2⁻¹ * τ⁻¹ := by
      rw [div_eq_mul_inv, mul_inv]; ring
    calc ((n : ℝ) / (2 * τ)) * Gv
        ≤ ((n : ℝ) / (2 * τ)) * (C₀ * gaussDdim (D.lam * τ) z) :=
          mul_le_mul_of_nonneg_left hbaseτ hnn
      _ ≤ ((n : ℝ) / (2 * τ)) * (C₀ * (Kw * Gl)) := by
          refine mul_le_mul_of_nonneg_left ?_ hnn
          exact mul_le_mul_of_nonneg_left hpush hC₀pos.le
      _ = ((n : ℝ) * C₀ * Kw / 2) * τ⁻¹ * Gl := by rw [h12]; ring
  have hP3 : Gv * M' ≤ (M' * C₀ * Kw * τ₀) * τ⁻¹ * Gl := by
    have hτcap : (1 : ℝ) ≤ τ₀ * τ⁻¹ := by
      rw [mul_comm, ← inv_mul_cancel₀ hτne]
      exact mul_le_mul_of_nonneg_left hτ0 (inv_nonneg.mpr hτ.le)
    have hGvM' : Gv * M' ≤ (C₀ * (Kw * Gl)) * M' := by
      refine mul_le_mul_of_nonneg_right ?_ hM'
      calc Gv ≤ C₀ * gaussDdim (D.lam * τ) z := hbaseτ
        _ ≤ C₀ * (Kw * Gl) := mul_le_mul_of_nonneg_left hpush hC₀pos.le
    have hrhs_nn : 0 ≤ C₀ * (Kw * Gl) * M' :=
      mul_nonneg (mul_nonneg hC₀pos.le (mul_nonneg hKwnn hGlnn)) hM'
    calc Gv * M' ≤ (C₀ * (Kw * Gl)) * M' := hGvM'
      _ ≤ (C₀ * (Kw * Gl)) * M' * (τ₀ * τ⁻¹) := le_mul_of_one_le_right hrhs_nn hτcap
      _ = (M' * C₀ * Kw * τ₀) * τ⁻¹ * Gl := by ring
  -- STEP 4: assemble.
  have hdistr : P * Gv * M + Gv * M'
      = M * ((rncRadialSq v / (4 * τ ^ 2)) * Gv) + M * (((n : ℝ) / (2 * τ)) * Gv)
          + Gv * M' := by rw [hPdef]; ring
  rw [hdistr]
  have hbig : M * ((rncRadialSq v / (4 * τ ^ 2)) * Gv) + M * (((n : ℝ) / (2 * τ)) * Gv) + Gv * M'
      ≤ Ctot * τ⁻¹ * Gl := by
    have ht1 : M * ((rncRadialSq v / (4 * τ ^ 2)) * Gv)
        ≤ M * ((C₁ * C₀ / 4) * τ⁻¹ * Gl) := mul_le_mul_of_nonneg_left hP1 hM
    have ht2 : M * (((n : ℝ) / (2 * τ)) * Gv)
        ≤ M * (((n : ℝ) * C₀ * Kw / 2) * τ⁻¹ * Gl) := mul_le_mul_of_nonneg_left hP2 hM
    calc M * ((rncRadialSq v / (4 * τ ^ 2)) * Gv) + M * (((n : ℝ) / (2 * τ)) * Gv) + Gv * M'
        ≤ M * ((C₁ * C₀ / 4) * τ⁻¹ * Gl) + M * (((n : ℝ) * C₀ * Kw / 2) * τ⁻¹ * Gl)
            + (M' * C₀ * Kw * τ₀) * τ⁻¹ * Gl :=
          add_le_add (add_le_add ht1 ht2) hP3
      _ = Ctot * τ⁻¹ * Gl := by rw [hCtotdef]; ring
  refine le_trans hbig ?_
  apply mul_le_mul_of_nonneg_right _ hGlnn
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hτ.le)
  linarith [hCtotnn]

/-! ###############################################################################
    ### §C — the GlOBAL-`z` extension (the exact `hAcrude` `∀ z` shape, `wL = 4·lam`).
    ############################################################################### -/

/-- **★★★ `witnessTimeDeriv_domination_global` — the crude time-derivative envelope for ALL `z`.**  Extends
    `witnessTimeDeriv_domination` off the gate ball: the witness vanishes (hence `deriv = 0`) wherever
    `z ∉ K`, and the carried support fact `hSupp` (`z ∈ K`, `0 ∈ S z ⟹ ‖z‖ < D.r`; the same honest input
    as `WideAmplitudeData.zeroth_domination_global`'s `hSupp`) places the active `z ∈ K` inside the gate
    ball (using `hgate`'s `0 ∈ S z`), so the on-ball bound applies.  The `∀ z` `Ccr·τ⁻¹·gaussDdim(wL·τ)`
    shape is exactly `hAcrude`'s (`wL = 4·D.lam`; `gaussDdim` even so the `z` / `0−z` centring agrees).
    NOT `a₁ = R/6`. -/
theorem witnessTimeDeriv_domination_global (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (D : FixedFlowGateData g gi hC hK) (τ₀ M M' : ℝ)
    (hτ₀ : 0 < τ₀) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (Cfield : Point n → Point n → ℝ)
    (hgate : ∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        w.2.1 ∈ S w.2.2 ∧
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1)
    (hAmp0 : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M)
    (hCfield : ∀ z ∈ K, ‖z‖ < D.r → |Cfield z 0| ≤ M')
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < D.r) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n,
      |deriv (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) τ|
        ≤ C * τ⁻¹ * gaussDdim (4 * D.lam * τ) z := by
  obtain ⟨C, hCpos, hbound⟩ :=
    witnessTimeDeriv_domination hn g gi hC hK S a b D τ₀ M M' hτ₀ hM hM' Cfield hgate hAmp0 hCfield
  refine ⟨C, hCpos, ?_⟩
  intro τ hτ hτ0 z
  by_cases hzK : z ∈ K
  · have h0 : (0 : Point n) ∈ S z := (hgate (τ, (0 : Point n), z) hzK hτ).1
    exact hbound τ hτ hτ0 z hzK (hSupp z hzK h0)
  · have hzero : (fun r => vanVleckGatedWitness g gi hC hK S a b r 0 z) = fun _ => (0 : ℝ) := by
      funext r
      unfold vanVleckGatedWitness
      exact gatedKernel_apply_of_notMem K S _ r 0 z (Or.inl hzK)
    rw [hzero, deriv_const', abs_zero]
    exact mul_nonneg (mul_nonneg hCpos.le (inv_nonneg.mpr hτ.le)) (gaussDdim_nonneg _ _)

/-! ###############################################################################
    ### §D — NON-VACUITY: the hypothesis bundle is jointly satisfiable at a nonempty singleton gate.
    ############################################################################### -/

/-- **Non-vacuity witness.**  For ANY concrete geometry `(g, gi, hC, hK)` at the SINGlETON gate
    `K := {0}` (compact, NONEMPTY), the full hypothesis bundle of `witnessTimeDeriv_domination` is jointly
    satisfiable — `S := Set.univ` (so `0 ∈ S z` always), `Cfield` the AFFINE amplitude slope (exactly the
    `chartFieldAmp_hasDerivAt_tau` derivative), an explicit gate record `D` (`r = 1`, `η = 1/2`,
    `lam = 4`; its near-isometry gate holds trivially at `z = 0` since `rncRadialSq 0 = 0`), and the
    amplitude bounds `M`, `M'` supplied by the AFFINE-in-`τ` structure at the single point `0`.  So the
    reduction fires on a genuine nonempty gate, NOT an empty / unsatisfiable one.  NOT `a₁ = R/6`. -/
theorem witnessTimeDeriv_domination_hyp_satisfiable
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (a b : ℝ) :
    ∃ (K : Set (Point n)) (hK : IsCompact K) (S : Point n → Set (Point n))
      (D : FixedFlowGateData g gi hC hK) (τ₀ M M' : ℝ) (Cfield : Point n → Point n → ℝ),
      (0 : Point n) ∈ K ∧ 0 < τ₀ ∧ 0 ≤ M ∧ 0 ≤ M' ∧
      (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
        w.2.1 ∈ S w.2.2 ∧
        HasDerivAt (fun u : ℝ => chartFieldAmp g gi hC hK a b u w.2.2 w.2.1)
          (Cfield w.2.2 w.2.1) w.1) ∧
      (∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z ∈ K, ‖z‖ < D.r →
        |chartFieldAmp g gi hC hK a b τ z 0| ≤ M) ∧
      (∀ z ∈ K, ‖z‖ < D.r → |Cfield z 0| ≤ M') := by
  classical
  have hK0 : IsCompact ({0} : Set (Point n)) := isCompact_singleton
  set Cf : Point n → Point n → ℝ := fun z p =>
    radialCutoff a b (uniformInverseChart g gi hC hK0 z p)
      * (VanVleck.vanVleck g (uniformInverseChart g gi hC hK0 z p) ^ (-(1 : ℝ) / 2)
          * transportCoeff (transportOp (VanVleck.vanVleck g) g gi) 1 (uniformInverseChart g gi hC hK0 z p))
    with hCfdef
  refine ⟨({0} : Set (Point n)), hK0, fun _ => Set.univ,
    { a := 1 / 3, b := 1 / 2, r := 1, eta := 1 / 2, lam := 4,
      ha := by norm_num, hab := by norm_num, hbr := by norm_num,
      heta := by norm_num, hlam := by norm_num, hgap := by norm_num,
      hgate := by
        intro z hz _
        rw [Set.mem_singleton_iff] at hz; subst hz
        have h0 : rncRadialSq (0 : Point n) = 0 := by simp [rncRadialSq]
        rw [h0, mul_zero]; exact rncRadialSq_nonneg _ },
    1, |chartFieldAmp g gi hC hK0 a b 0 0 0| + |Cf 0 0|, |Cf 0 0|, Cf,
    Set.mem_singleton_iff.mpr rfl, one_pos, by positivity, abs_nonneg _, ?_, ?_, ?_⟩
  · -- hgate: `S = univ` frees the gate membership; the HasDerivAt is `chartFieldAmp_hasDerivAt_tau`.
    intro w _ _
    exact ⟨Set.mem_univ _, chartFieldAmp_hasDerivAt_tau g gi hC hK0 a b w.2.2 w.2.1 w.1⟩
  · -- hAmp0: only `z = 0`; affine-in-τ bound with `τ ≤ 1`.
    intro τ hτ hτ1 z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    have haff : chartFieldAmp g gi hC hK0 a b τ 0 0
        = chartFieldAmp g gi hC hK0 a b 0 0 0 + Cf 0 0 * τ := by
      simp only [hCfdef, chartFieldAmp]; ring
    rw [haff]
    calc |chartFieldAmp g gi hC hK0 a b 0 0 0 + Cf 0 0 * τ|
        ≤ |chartFieldAmp g gi hC hK0 a b 0 0 0| + |Cf 0 0 * τ| := abs_add_le _ _
      _ = |chartFieldAmp g gi hC hK0 a b 0 0 0| + |Cf 0 0| * τ := by
          rw [abs_mul, abs_of_nonneg hτ.le]
      _ ≤ |chartFieldAmp g gi hC hK0 a b 0 0 0| + |Cf 0 0| * 1 := by
          have : |Cf 0 0| * τ ≤ |Cf 0 0| * 1 := mul_le_mul_of_nonneg_left hτ1 (abs_nonneg _)
          linarith
      _ = |chartFieldAmp g gi hC hK0 a b 0 0 0| + |Cf 0 0| := by rw [mul_one]
  · -- hCfield: only `z = 0`; `|Cf 0 0| ≤ |Cf 0 0|`.
    intro z hz _
    rw [Set.mem_singleton_iff] at hz; subst hz
    exact le_refl _

end QIQTH.WitnessTimeDerivEnvelope

section AxiomChecks
open QIQTH.WitnessTimeDerivEnvelope
#print axioms tauCoeff_abs_bound
#print axioms witnessTimeDeriv_domination
#print axioms witnessTimeDeriv_domination_global
#print axioms witnessTimeDeriv_domination_hyp_satisfiable
end AxiomChecks
