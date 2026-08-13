/-
  WhiteGatePackageCombined — J4-690: THE CO-EMITTING GATE DISCHARGER.  One theorem producing, at
  ONE shared concrete flow-ball gate, BOTH the whitened all-τ defect PACKAGE (the `hpkgBound`
  feed that `WhiteHBdomAllRows.white_hBdom_discharged` consumes) AND the whitened-witness VALUE
  domination (the `hWdom` slot of `WhiteHInnerCont.white_hInnerCont_of_dominations`), so the
  composed whitened `hInnerCont` carries drop to `{S1, hmeas, hcont}` only.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE MONOTONICITY VERDICT (the finding).  Both banked constructions fix their gate as
     `whiteFlowGate κ hκ hKc <radius>` (a=<r>/4, b=<r>/2) and are RADIUS-MONOTONE below a threshold:
       • `WhiteAnnulus.white_hpkgBound_discharged` needs only `c < δ₀` and `CE·c < r₀`
         (r₀ = min rh rp, from the hann + ambient-displacement suppliers; CE from `whiteUnvel_norm_le`);
       • `WhiteWitnessValueDom.white_witness_value_dom` needs only `c ≤ δ₀` and `c ≤ Rf`
         (Rf = `uniformFlowRadius`, the tube-confinement radius).
     Neither construction runs any radius-SPECIFIC analysis: shrinking the flow ball only shrinks the
     domain on which the same chart germ / annulus / determinant bricks are read.  So a SHARED radius
     `c* = min(δ₀, Rf, r₀/(CE+1)) / 2` satisfies BOTH threshold packages at once (the J4-680
     threshold-monotonicity pattern), and re-instantiating both leg constructions at `c*` co-emits
     both bounds at the SAME `whiteFlowGate κ hκ hKc c*`.  This is a RE-INSTANTIATION, not new
     analysis — the two proof bodies are transplanted verbatim with the internal radius abstracted to
     `c*`, and the widths stay honest and DISTINCT (`lam = whiteLam = 2(nC₀²+1)` for the defect
     package; `wA = nC₀²+1` for the value bound — the builder consumes them on separate slots).

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `white_gate_package_combined` — ★★★ the co-emitter.  For EVERY `κ ≤ 0`, compact `K ⊆ B̄(0,R)`,
      there IS ONE gate `S = whiteFlowGate κ hκ hKc c*` with radii `0 < a < b`, fat/open at every
      `q ∈ K`, such that BOTH hold at that gate: the unconstrained all-τ defect package
      (`≤ (C(1+t'))·baseKernelW lam 0 τ p q`, `lam = whiteLam`) AND the affine-amplitude value
      domination (`≤ (A₀+A₁τ)·Cpre·gaussDdim (wA τ) (p−q)`, `wA = nC₀²+1`).
    • `white_hBdom_combined` — ★★ the re-threaded all-rows Levi `hBdom` at that SAME shared gate:
      MODULO the ONE S1 input, `|leviSeries (whiteDefectKernel …) s z y| ≤ C_L·G_{lam·s}(z−y)` on
      `(0,1]`, ∀ z y — the package fed through the gate-parametric `white_leviSeries_full_row`.
    • `white_hInnerCont_combined` — ★★★ the composed whitened inner-pairing time-continuity with the
      value domination DISCHARGED (no longer carried): carries drop to `{S1 measurability `hEmeas`,
      interior slice measurability `hmeas`, a.e.-z interior continuity `hcont`}`.
    • `white_gate_package_combined_witness_gate` — the cp466 non-vacuity certificate (`n = 2`,
      `κ = −1`, `K = closedBall 0 2`): the shared gate is fat/open at `0`, `0 < a < b`, both widths
      positive — not `∅`-degenerate.

  ── HONEST RESIDUAL.  The value-domination `hWdom` slot is now DISCHARGED at the shared gate; the
     composed `white_hInnerCont_combined` still owes only `{S1 `hEmeas`, `hmeas`, `hcont`}` plus the
     prior `K1TransportBudget` / capstone co-instantiation piles.  `a₁ = R/6` established
     non-vacuously ONLY for the FLAT tower.

  ⚠ HONEST FIREWALL.  Gate PLUMBING only — one shared radius emitting two already-proved bounds —
  NOT `a₁ = R/6`; the `R/6` value is a labelled carrier, untouched.  DERIVED from the banked
  leg-assembler + gate-parametric Levi engine + banked value bricks.  No `sorry`, no `admit`, no new
  axioms, no `:= True`, no vacuous hypothesis, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.WhiteWitnessValueDom
import QIQTH.WhiteHBdomAllRows
import QIQTH.WhiteHInnerCont

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz QIQTH.HeatDuhamel
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.ResidueBound QIQTH.RNCDecay QIQTH.LeviSeries
open QIQTH.CurvedA1CenterAmp
open QIQTH.WhiteWitness QIQTH.WhiteAmbient QIQTH.WhiteAnnulus QIQTH.WhiteGated
open QIQTH.WhiteBridge QIQTH.WhiteHBdomAllRows
open QIQTH.CurvedRNCVanVleckBound
open Set
open scoped Topology BigOperators

namespace QIQTH.WhiteGatePackageCombined

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★★ `white_gate_package_combined` — THE CO-EMITTING GATE DISCHARGER.**  For EVERY `κ ≤ 0` and
    compact seed `Kset ⊆ B̄(0,R)`, there IS ONE flow-ball gate `S = whiteFlowGate κ hκ hKc c*` with
    cutoff radii `0 < a < b`, fat and open at every `q ∈ Kset`, such that BOTH the whitened all-τ
    defect PACKAGE (width `lam = whiteLam`, affine time factor `C·(1+t')`) AND the whitened-witness
    VALUE Gaussian domination (positive width `wA`, affine amplitude `A₀+A₁τ`) hold at that SAME
    gate.  The shared radius `c* = min(δ₀, Rf, r₀/(CE+1))/2` lies below both banked thresholds; both
    leg constructions are re-instantiated at `c*`.  NOT `a₁ = R/6`. -/
theorem white_gate_package_combined (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ (∃ C : ℝ, 0 ≤ C ∧ ∃ lam : ℝ, 2 ≤ lam ∧
          ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
            |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (whiteGatedWitness κ hκ hKc S a b) τ p q|
              ≤ (C * (1 + t')) * QIQTH.GaussianWidthTolerant.baseKernelW lam 0 τ p q)
      ∧ (∃ wA Cpre A₀ A₁ : ℝ, 0 < wA ∧ 0 ≤ Cpre ∧ 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
          ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
            |whiteGatedWitness κ hκ hKc S a b τ p q|
              ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q)) := by
  classical
  -- shared chart germ radius + the two flow constants used by BOTH constructions.
  obtain ⟨δ₀, hδ₀0, hspec⟩ := uniformInverseChart_huniformChart (curvedRNCMetric κ)
    (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨rh, hrh0, hhann⟩ := white_hann_bound κ hκ hKc R hKb
  obtain ⟨rp, hrp0, Cp, hCp0, hprod⟩ := white_ambient_bound_displacement_lam κ hκ hKc R hKb
  obtain ⟨CE, hCE0, hCEle⟩ := whiteUnvel_norm_le κ hκ hKc
  set C₀ : ℝ := uniformFlowConst (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) hKc with hC₀def
  have hC₀0 : 0 ≤ C₀ := uniformFlowConst_nonneg (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) hKc
  set Rf : ℝ := uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) hKc with hRfdef
  have hRf0 : 0 < Rf := uniformFlowRadius_pos (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) hKc
  set r₀ : ℝ := min rh rp with hr₀def
  have hr₀0 : 0 < r₀ := lt_min hrh0 hrp0
  -- ★ THE SHARED RADIUS `c*` = below all three thresholds (δ₀, Rf, r₀/(CE+1)), halved for strictness.
  set thr : ℝ := min δ₀ (min Rf (r₀ / (CE + 1))) with hthrdef
  have hthr0 : 0 < thr :=
    lt_min hδ₀0 (lt_min hRf0 (div_pos hr₀0 (by linarith)))
  set c : ℝ := thr / 2 with hcdef
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hthrδ : thr ≤ δ₀ := min_le_left _ _
  have hthrRf : thr ≤ Rf := le_trans (min_le_right _ _) (min_le_left _ _)
  have hthrr : thr ≤ r₀ / (CE + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hcδ : c < δ₀ := by rw [hcdef]; linarith
  have hcδle : c ≤ δ₀ := le_of_lt hcδ
  have hcRf : c ≤ Rf := by rw [hcdef]; linarith
  -- CE·c < r₀ (the package tube constraint), mirroring the banked arithmetic.
  have hcr : CE * c < r₀ := by
    have h2 : c ≤ r₀ / (CE + 1) / 2 := by rw [hcdef]; linarith
    have h3 : CE * c ≤ CE * (r₀ / (CE + 1) / 2) := mul_le_mul_of_nonneg_left h2 hCE0
    have hx0 : 0 ≤ r₀ / (CE + 1) / 2 :=
      div_nonneg (div_nonneg hr₀0.le (by linarith)) (by norm_num)
    have h6 : CE * (r₀ / (CE + 1) / 2) ≤ (CE + 1) * (r₀ / (CE + 1) / 2) :=
      mul_le_mul_of_nonneg_right (by linarith) hx0
    have h5 : (CE + 1) * (r₀ / (CE + 1) / 2) = r₀ / 2 := by field_simp
    have h7 : r₀ / 2 < r₀ := by linarith
    linarith [h5 ▸ h6]
  have ha : 0 < c / 4 := by linarith
  have hab : c / 4 < c / 2 := by linarith
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- PART A.  The DEFECT PACKAGE at the shared gate (re-instantiation of `white_hpkgBound_discharged`).
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- leg (ii): the chart certificate at the flow-ball gate.
  have key : ∀ q ∈ Kset, ∀ p ∈ whiteFlowGate κ hκ hKc c q, ∃ w : Point n,
      p = whiteExp κ hκ hKc q w ∧ ‖w‖ < r₀ ∧ whiteInvChart κ hκ hKc q p = w
        ∧ ContinuousAt (fun p' => whiteInvChart κ hκ hKc q p') p := by
    intro q hq p hp
    obtain ⟨v, hvmem, hpv⟩ := hp
    have hv : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hvmem
    have hvδ : ‖v‖ < δ₀ := lt_trans hv hcδ
    have hVval : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc q p = v := by
      rw [← hpv]
      exact (((hspec q hq).1 v hvδ).1).eq_of_nhds
    refine ⟨whiteUnvel κ q v, ?_, ?_, ?_, ?_⟩
    · rw [whiteExp_whiteUnvel κ hκ hKc q v]
      exact hpv.symm
    · calc ‖whiteUnvel κ q v‖ ≤ CE * ‖v‖ := hCEle q hq v
        _ ≤ CE * c := mul_le_mul_of_nonneg_left hv.le hCE0
        _ < r₀ := hcr
    · show whiteUnvel κ q (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q p) = whiteUnvel κ q v
      rw [hVval]
    · have hC2 := ((hspec q hq).1 v hvδ).2
      have hCV : ContinuousAt (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q) p := by
        rw [← hpv]
        exact hC2.continuousAt
      exact ((whiteUnvel κ q).continuous.continuousAt).comp hCV
  -- leg (i): openness + fatness.
  have hSopen : ∀ q ∈ Kset, IsOpen (whiteFlowGate κ hκ hKc c q) :=
    fun q hq => ((hspec q hq).2 c hc0 hcδ).1
  have hfat : ∀ q ∈ Kset, q ∈ whiteFlowGate κ hκ hKc c q
      ∧ IsOpen (whiteFlowGate κ hκ hKc c q) := by
    intro q hq
    refine ⟨⟨0, mem_ball_zero_iff.mpr (by rw [norm_zero]; exact hc0), ?_⟩, hSopen q hq⟩
    exact uniformFlowExp_zero (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
      hKc q hq
  -- leg (iii): the frontier — interior-off or the cutoff zero collar.
  have hfrontier : ∀ q ∈ Kset, ∀ p : Point n, p ∉ whiteFlowGate κ hκ hKc c q →
      ({p' : Point n | p' ∉ whiteFlowGate κ hκ hKc c q} ∈ nhds p)
      ∨ ({p' : Point n | (c / 2) ^ 2
            ≤ rncRadialSq (whiteInvChart κ hκ hKc q p')} ∈ nhds p) := by
    intro q hq p hpS
    by_cases hcl : p ∈ closure (whiteFlowGate κ hκ hKc c q)
    · right
      have hsub := ((hspec q hq).2 c hc0 hcδ).2
      obtain ⟨v, hvmem, hpv⟩ := hsub hcl
      have hvle : ‖v‖ ≤ c := by rwa [Metric.mem_closedBall, dist_zero_right] at hvmem
      have hvδ : ‖v‖ < δ₀ := lt_of_le_of_lt hvle hcδ
      have hVval : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q p = v := by
        rw [← hpv]
        exact (((hspec q hq).1 v hvδ).1).eq_of_nhds
      have hval : whiteInvChart κ hκ hKc q p = whiteUnvel κ q v := by
        show whiteUnvel κ q (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q p) = whiteUnvel κ q v
        rw [hVval]
      have hvc : ‖v‖ = c := by
        by_contra hne
        have hlt : ‖v‖ < c := lt_of_le_of_ne hvle hne
        exact hpS ⟨v, mem_ball_zero_iff.mpr hlt, hpv⟩
      have h3 : rncRadialSq v ≤ rncRadialSq (whiteUnvel κ q v) := by
        have h4 := whiteVel_radialSq_le κ hκ q (whiteUnvel κ q v)
        rw [whiteVel_whiteUnvel κ hκ q v] at h4
        exact h4
      have h5 : ‖v‖ ^ 2 ≤ rncRadialSq v := by
        have h6 := norm_le_rncRadial v
        have h7 : rncRadial v ^ 2 = rncRadialSq v := by
          rw [rncRadial, Real.sq_sqrt (rncRadialSq_nonneg _)]
        nlinarith [norm_nonneg v]
      have hgt : (c / 2) ^ 2 < rncRadialSq (whiteInvChart κ hκ hKc q p) := by
        rw [hval]
        have h8 : c ^ 2 ≤ rncRadialSq (whiteUnvel κ q v) := by
          have : ‖v‖ ^ 2 ≤ rncRadialSq (whiteUnvel κ q v) := le_trans h5 h3
          rw [hvc] at this
          exact this
        nlinarith [hc0]
      have hC2 := ((hspec q hq).1 v hvδ).2
      have hCV : ContinuousAt (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q) p := by
        rw [← hpv]
        exact hC2.continuousAt
      have hVc : ContinuousAt (fun p' => whiteInvChart κ hκ hKc q p') p :=
        ((whiteUnvel κ q).continuous.continuousAt).comp hCV
      have hrc : ContinuousAt (fun p' => rncRadialSq (whiteInvChart κ hκ hKc q p')) p :=
        (rncRadialSq_contDiff.continuous.continuousAt).comp hVc
      have hopen : {p' : Point n | (c / 2) ^ 2
          < rncRadialSq (whiteInvChart κ hκ hKc q p')} ∈ nhds p :=
        hrc.preimage_mem_nhds (Ioi_mem_nhds hgt)
      refine Filter.mem_of_superset hopen fun p' hp' => ?_
      exact le_of_lt (show (c / 2) ^ 2
        < rncRadialSq (whiteInvChart κ hκ hKc q p') from hp')
    · left
      have hopen : (closure (whiteFlowGate κ hκ hKc c q))ᶜ ∈ nhds p :=
        (isClosed_closure.isOpen_compl).mem_nhds hcl
      exact Filter.mem_of_superset hopen
        (fun p' hp' hmem => hp' (subset_closure hmem))
  -- the (a,b)-instantiated hann + producer with the joint constant.
  obtain ⟨Ch, hCh0, hhann'⟩ := hhann (c / 4) (c / 2) ha hab
  have hCB0 : 0 ≤ max Cp Ch := le_trans hCp0 (le_max_left _ _)
  have hbd : ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ w : Point n, ‖w‖ < r₀ →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteAmbientKernel κ hκ hKc) τ
          (whiteExp κ hκ hKc q w) q|
        ≤ max Cp Ch * gaussDdim (whiteLam κ hκ hKc * τ) (whiteExp κ hκ hKc q w - q) := by
    intro q hq τ hτ w hw
    refine (hprod q hq τ hτ w (lt_of_lt_of_le hw (min_le_right _ _))).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
  have hann : ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ p ∈ whiteFlowGate κ hκ hKc c q,
      (c / 4) ^ 2 ≤ rncRadialSq (whiteInvChart κ hκ hKc q p) →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteCutKernel κ hκ hKc (c / 4) (c / 2)) τ p q|
        ≤ max Cp Ch * gaussDdim (whiteLam κ hκ hKc * τ) (p - q) := by
    intro q hq τ hτ p hp hannp
    obtain ⟨w, hpw, hwr, hVw, _⟩ := key q hq p hp
    have hannw : (c / 4) ^ 2 ≤ rncRadialSq w := by
      rw [← hVw]
      exact hannp
    have h := hhann' q hq τ hτ w (lt_of_lt_of_le hwr (min_le_left _ _)) hannw
    rw [hpw]
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
  have hpkgbd : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2)) τ p q|
        ≤ (max Cp Ch * (1 + t'))
            * QIQTH.GaussianWidthTolerant.baseKernelW (whiteLam κ hκ hKc) 0 τ p q :=
    white_hpkgBound_of_gatePackage κ hκ hKc (whiteFlowGate κ hκ hKc c)
      ha hab hCB0 hbd hSopen key hfrontier hann
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- PART B.  The VALUE domination at the SAME gate (re-instantiation of `white_witness_value_dom`).
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  set lamV : ℝ := (n : ℝ) * C₀ ^ 2 + 1 with hlamVdef
  have hlamV0 : 0 < lamV := by
    have : (0 : ℝ) ≤ (n : ℝ) * C₀ ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
    rw [hlamVdef]; linarith
  set Amp : ℝ := Real.sqrt ((1 - κ / 3 * ((n : ℝ) * R ^ 2)) ^ (n - 1)) with hAmpdef
  have hAmp0 : 0 ≤ Amp := Real.sqrt_nonneg _
  set Cpre : ℝ := Amp * Real.sqrt (lamV / 1) ^ n with hCpredef
  have hCpre0 : 0 ≤ Cpre :=
    mul_nonneg hAmp0 (pow_nonneg (Real.sqrt_nonneg _) n)
  have hvalbd : ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
      |whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2) τ p q|
        ≤ (1 + 0 * τ) * Cpre * gaussDdim (lamV * τ) (p - q) := by
    intro τ hτ p q
    have hRHS0 : 0 ≤ (1 + 0 * τ) * Cpre * gaussDdim (lamV * τ) (p - q) := by
      have hg := gaussDdim_nonneg (lamV * τ) (p - q)
      have : (0 : ℝ) ≤ (1 + 0 * τ) * Cpre := by nlinarith
      exact mul_nonneg this hg
    by_cases hq : q ∈ Kset
    · by_cases hpmem : p ∈ whiteFlowGate κ hκ hKc c q
      · obtain ⟨v, hvmem, hpv⟩ := id hpmem
        have hv : ‖v‖ < c := by rwa [mem_ball_zero_iff] at hvmem
        have hvδ : ‖v‖ < δ₀ := lt_of_lt_of_le hv hcδle
        set W : Point n := whiteUnvel κ q v with hWdef
        have hVval : uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q p = v := by
          rw [← hpv]
          exact (((hspec q hq).1 v hvδ).1).eq_of_nhds
        have hInvW : whiteInvChart κ hκ hKc q p = W := by
          show whiteUnvel κ q (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
            (curvedRNC_hChr κ hκ) hKc q p) = W
          rw [hVval]
        have hpW : whiteExp κ hκ hKc q W = p := by
          rw [hWdef, whiteExp_whiteUnvel κ hκ hKc q v]; exact hpv
        have hVelW : whiteVel κ q W = v := by
          rw [hWdef]; exact whiteVel_whiteUnvel κ hκ q v
        have hval : whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2) τ p q
            = radialCutoff (c / 4) (c / 2) W
              * (Real.sqrt (Matrix.det (curvedRNCMetric κ q)) * gaussDdim τ W) := by
          unfold whiteGatedWitness
          rw [gatedKernel_apply_of_mem Kset (whiteFlowGate κ hκ hKc c)
                (whiteCutKernel κ hκ hKc (c / 4) (c / 2)) τ hq hpmem]
          unfold whiteCutKernel whiteAmbientKernel
          rw [hInvW]
        have hqR : rncRadialSq q ≤ (n : ℝ) * R ^ 2 := rncRadialSq_le_of_mem_closedBall (hKb hq)
        have hdetle : Matrix.det (curvedRNCMetric κ q)
            ≤ (1 - κ / 3 * ((n : ℝ) * R ^ 2)) ^ (n - 1) :=
          curvedRNCMetric_det_le κ hκ q ((n : ℝ) * R ^ 2) hqR
        have hdetamp : Real.sqrt (Matrix.det (curvedRNCMetric κ q)) ≤ Amp :=
          Real.sqrt_le_sqrt hdetle
        have hdet0 : 0 ≤ Real.sqrt (Matrix.det (curvedRNCMetric κ q)) := Real.sqrt_nonneg _
        have hWvel : ‖whiteVel κ q W‖ ≤ Rf := by
          rw [hVelW]; exact le_of_lt (lt_of_lt_of_le hv hcRf)
        have hdisp : ‖whiteExp κ hκ hKc q W - q‖ ≤ C₀ * ‖whiteVel κ q W‖ :=
          whiteExp_displacement κ hκ hKc q hq W hWvel
        have hr2disp : rncRadialSq (whiteExp κ hκ hKc q W - q)
            ≤ (n : ℝ) * C₀ ^ 2 * rncRadialSq W := by
          have h1 : rncRadialSq (whiteExp κ hκ hKc q W - q)
              ≤ (n : ℝ) * ‖whiteExp κ hκ hKc q W - q‖ ^ 2 := by
            refine rncRadialSq_le_of_mem_closedBall
              (q := whiteExp κ hκ hKc q W - q) (r := ‖whiteExp κ hκ hKc q W - q‖) ?_
            rw [Metric.mem_closedBall, dist_zero_right]
          have h2 : ‖whiteExp κ hκ hKc q W - q‖ ^ 2 ≤ (C₀ * ‖whiteVel κ q W‖) ^ 2 := by
            have := mul_self_le_mul_self (norm_nonneg _) hdisp
            nlinarith
          have h3 : ‖whiteVel κ q W‖ ^ 2 ≤ rncRadialSq (whiteVel κ q W) := by
            have hle : ‖whiteVel κ q W‖ ≤ rncRadial (whiteVel κ q W) :=
              norm_le_rncRadial (whiteVel κ q W)
            have hsq : rncRadial (whiteVel κ q W) ^ 2 = rncRadialSq (whiteVel κ q W) := by
              rw [rncRadial, Real.sq_sqrt (rncRadialSq_nonneg _)]
            have := mul_self_le_mul_self (norm_nonneg _) hle
            nlinarith [this, hsq]
          have h4 : rncRadialSq (whiteVel κ q W) ≤ rncRadialSq W := whiteVel_radialSq_le κ hκ q W
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have hnc0 : (0 : ℝ) ≤ (n : ℝ) * C₀ ^ 2 := mul_nonneg hn0 (sq_nonneg _)
          calc rncRadialSq (whiteExp κ hκ hKc q W - q)
              ≤ (n : ℝ) * ‖whiteExp κ hκ hKc q W - q‖ ^ 2 := h1
            _ ≤ (n : ℝ) * (C₀ * ‖whiteVel κ q W‖) ^ 2 := mul_le_mul_of_nonneg_left h2 hn0
            _ = (n : ℝ) * C₀ ^ 2 * ‖whiteVel κ q W‖ ^ 2 := by ring
            _ ≤ (n : ℝ) * C₀ ^ 2 * rncRadialSq (whiteVel κ q W) :=
                mul_le_mul_of_nonneg_left h3 hnc0
            _ ≤ (n : ℝ) * C₀ ^ 2 * rncRadialSq W := mul_le_mul_of_nonneg_left h4 hnc0
        have hr2disp' : rncRadialSq (p - q) ≤ (n : ℝ) * C₀ ^ 2 * rncRadialSq W := by
          rw [hpW] at hr2disp; exact hr2disp
        have hnorm : 1 * rncRadialSq (p - q) ≤ lamV * rncRadialSq W := by
          have h0 : (0 : ℝ) ≤ rncRadialSq W := rncRadialSq_nonneg W
          rw [hlamVdef]; nlinarith [hr2disp']
        have hcmp : gaussDdim (1 * τ) W
            ≤ Real.sqrt (lamV / 1) ^ n * gaussDdim (lamV * τ) (p - q) :=
          gaussDdim_le_gaussDdim_chart (by norm_num) hlamV0 hτ hnorm
        have hcmp' : gaussDdim τ W
            ≤ Real.sqrt (lamV / 1) ^ n * gaussDdim (lamV * τ) (p - q) := by
          rw [one_mul] at hcmp; exact hcmp
        have hgW0 : 0 ≤ gaussDdim τ W := gaussDdim_nonneg τ W
        rw [hval]
        have hcut1 : |radialCutoff (c / 4) (c / 2) W| ≤ 1 := by
          rw [abs_of_nonneg (radialCutoff_nonneg _ _ W)]
          exact radialCutoff_le_one _ _ W
        calc |radialCutoff (c / 4) (c / 2) W
                * (Real.sqrt (Matrix.det (curvedRNCMetric κ q)) * gaussDdim τ W)|
            = |radialCutoff (c / 4) (c / 2) W|
                * (Real.sqrt (Matrix.det (curvedRNCMetric κ q)) * gaussDdim τ W) := by
              rw [abs_mul, abs_of_nonneg (mul_nonneg hdet0 hgW0)]
          _ ≤ 1 * (Amp * gaussDdim τ W) := by
              apply mul_le_mul hcut1 _ (mul_nonneg hdet0 hgW0) (by norm_num)
              exact mul_le_mul_of_nonneg_right hdetamp hgW0
          _ = Amp * gaussDdim τ W := by rw [one_mul]
          _ ≤ Amp * (Real.sqrt (lamV / 1) ^ n * gaussDdim (lamV * τ) (p - q)) :=
              mul_le_mul_of_nonneg_left hcmp' hAmp0
          _ = (1 + 0 * τ) * Cpre * gaussDdim (lamV * τ) (p - q) := by
              rw [hCpredef]; ring
      · rw [show whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2) τ p q = 0 from
          gatedKernel_apply_of_notMem Kset (whiteFlowGate κ hκ hKc c)
            (whiteCutKernel κ hκ hKc (c / 4) (c / 2)) τ p q (Or.inr hpmem), abs_zero]
        exact hRHS0
    · rw [show whiteGatedWitness κ hκ hKc (whiteFlowGate κ hκ hKc c) (c / 4) (c / 2) τ p q = 0 from
        gatedKernel_apply_of_notMem Kset (whiteFlowGate κ hκ hKc c)
          (whiteCutKernel κ hκ hKc (c / 4) (c / 2)) τ p q (Or.inl hq), abs_zero]
      exact hRHS0
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  -- ASSEMBLE both bounds at the single shared gate.
  -- ══════════════════════════════════════════════════════════════════════════════════════════════
  refine ⟨whiteFlowGate κ hκ hKc c, c / 4, c / 2, ha, hab, hfat,
    ⟨max Cp Ch, hCB0, whiteLam κ hκ hKc, whiteLam_ge_two κ hκ hKc, hpkgbd⟩,
    ⟨lamV, Cpre, 1, 0, hlamV0, hCpre0, by norm_num, le_rfl, hvalbd⟩⟩

/-- **★★ `white_hBdom_combined` — THE RE-THREADED ALL-ROWS `hBdom` AT THE SHARED GATE.**  From the
    co-emitted defect package of `white_gate_package_combined`, the gate-parametric width-`lam`
    full-row Levi engine (`WhiteHBdomAllRows.white_leviSeries_full_row`) yields, MODULO the ONE S1
    input, the FULL whitened signed Levi-series bound `|leviSeries (whiteDefectKernel …) s z y|
    ≤ C_L·G_{lam·s}(z − y)` on `(0,1]`, ∀ z y — at the SAME gate that co-emits the value bound.
    NOT `a₁ = R/6`. -/
theorem white_hBdom_combined (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ (∃ wA Cpre A₀ A₁ : ℝ, 0 < wA ∧ 0 ≤ Cpre ∧ 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
          ∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
            |whiteGatedWitness κ hκ hKc S a b τ p q|
              ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        (QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
            (whiteGatedWitness κ hκ hKc S a b) →
          ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ (s : ℝ) (z y : Point n), 0 < s → s ≤ 1 →
            |leviSeries (whiteDefectKernel κ hκ hKc S a b) s z y|
              ≤ C_L * gaussDdim (lam * s) (z - y)) := by
  obtain ⟨S, a, b, ha, hab, hgate, ⟨C, hC0, lam, hlam2, hpkg⟩, hval⟩ :=
    white_gate_package_combined κ hκ hKc R hKb
  refine ⟨S, a, b, ha, hab, hgate, hval, lam, hlam2, fun hEmeas => ?_⟩
  exact white_leviSeries_full_row κ hκ hKc S a b C lam hC0 hlam2 hpkg hEmeas

/-- **★★★ `white_hInnerCont_combined` — THE COMPOSED WHITENED INNER-PAIRING CONTINUITY.**  At the
    single shared gate of `white_gate_package_combined`, the value domination is DISCHARGED (fed as
    `hAdom`) and the width-`lam` Levi B-slot is discharged internally from the co-emitted package;
    the generic builder `CurvedA1HContDomGen.hInnerCont_of_dominations_generic` then delivers the
    interior-time continuity of the whitened inner pairing on `Ioo 0 u`, ∀ u ∈ U ⊆ (·,1], MODULO
    ONLY `{the whitened-defect S1 measurability `hEmeas`, the interior slice measurability `hmeas`,
    the a.e.-z interior time continuity `hcont`}` — the value-domination carry is GONE.
    ⚠ HONEST width `lam = whiteLam`.  NOT `a₁ = R/6`. -/
theorem white_hInnerCont_combined (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R)
    (U : Set ℝ) (hU1 : ∀ u ∈ U, u ≤ 1) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        (QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
            (whiteGatedWitness κ hκ hKc S a b) →
          (∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
              AEStronglyMeasurable
                (fun z => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
                  * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
                (volume : Measure (Point n))) →
          (∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
              ContinuousAt
                (fun s => whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
                  * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0) s₀) →
          ∀ u ∈ U, ContinuousOn
            (fun s => ∫ z, whiteGatedWitness κ hκ hKc S a b (u - s) 0 z
              * leviSeries (whiteDefectKernel κ hκ hKc S a b) s z 0)
            (Set.Ioo 0 u)) := by
  obtain ⟨S, a, b, ha, hab, hgate,
      ⟨wA, Cpre, A₀, A₁, hwA, hCpre, hA₀, hA₁, hWdom⟩,
      lam, hlam2, hBimpl⟩ :=
    white_hBdom_combined κ hκ hKc R hKb
  refine ⟨S, a, b, ha, hab, hgate, lam, hlam2, fun hEmeas hmeas hcont => ?_⟩
  obtain ⟨C_L, hC_L, hBdom⟩ := hBimpl hEmeas
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le two_pos hlam2
  exact QIQTH.CurvedA1HContDomGen.hInnerCont_of_dominations_generic
    (whiteGatedWitness κ hκ hKc S a b) (leviSeries (whiteDefectKernel κ hκ hKc S a b))
    1 U hU1 wA lam hwA hlam0 Cpre A₀ A₁ C_L hCpre hA₀ hA₁ hC_L
    hWdom (fun s hs hsT z y => hBdom s z y hs hsT) hmeas hcont

/-- **cp466 non-vacuity gate** — at genuinely curved data (`n = 2`, `κ = −1`, `K = closedBall 0 2`):
    the ∃-package of `white_gate_package_combined` produces ONE FAT gate (`0 ∈ S 0`, open) with
    `0 < a < b`, a defect width `lam ≥ 2`, and a positive value width `wA` — the co-emitted shared
    gate is not `∅`-degenerate.  NOT `a₁ = R/6`. -/
theorem white_gate_package_combined_witness_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ ((0 : Point 2) ∈ S 0 ∧ IsOpen (S 0))
      ∧ (∃ lam : ℝ, 2 ≤ lam) ∧ (∃ wA : ℝ, 0 < wA) := by
  obtain ⟨S, a, b, ha, hab, hgate, ⟨C, hC0, lam, hlam2, -⟩,
      ⟨wA, _Cpre, _A₀, _A₁, hwA, -, -, -, -⟩⟩ :=
    white_gate_package_combined (n := 2) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
  exact ⟨S, a, b, ha, hab,
    hgate 0 (Metric.mem_closedBall_self (by norm_num)), ⟨lam, hlam2⟩, ⟨wA, hwA⟩⟩

end QIQTH.WhiteGatePackageCombined

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.WhiteGatePackageCombined

#print axioms white_gate_package_combined
#print axioms white_hBdom_combined
#print axioms white_hInnerCont_combined
#print axioms white_gate_package_combined_witness_gate

end AxiomChecks
