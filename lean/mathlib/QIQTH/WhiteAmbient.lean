/-
  WhiteAmbient — J4-624: the chart→ambient naturality WELD at `whiteExp` and the AMBIENT transfer
  of the banked whitened off-diagonal bound — the whitened `hpkgBound` producer (on-gate layer).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; nothing here touches the coefficient VALUE.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved side still
  owes: whatever remains of the whitened `hpkgBound` assembly (the labelled residues R1–R3 of §6
  below) + `hEbound`/`hInt` at the transport kernel + the `K1TransportBudget` + the fat-`K`
  carrier piles + the capstone co-instantiation at the whitened witness + the prior analytic
  piles.  This brick = the naturality weld + the ambient transfer ONLY.

  ── ITEM (1): THE NATURALITY WELD `laplaceBeltrami_whiteExp_naturality`.
      `Δ_{ĝ_q}(f ∘ whiteExp_q)(w) = (Δ_{g^κ} f)(whiteExp_q w)`  on a uniform gate `‖w‖ < r₀`,
      every `q ∈ K`, for every `f` that is `C²` at the far point — the banked general local engine
      `laplaceBeltrami_pullback_naturality_local` (PullbackNaturalityLocal) instantiated at
      `φ := whiteExp_q`, with ALL side conditions DISCHARGED from banked suppliers:
        (i)   `IsUnit (fderiv whiteExp_q w)` — the Jacobian chain `whiteExp_fderiv` (J4-623)
              composed as a product of units: `uniformFlowExp_common_nondeg_radius` (banked)
              × the NEW explicit two-sided whitening inverse (§1: `E_q⁻¹ = g^κ(q)·E_q`, from the
              banked whitening identity `E_qᵀ g^κ(q) E_q = δ` — no abstract finite-dim argument);
        (ii)  `pullbackMet g^κ (whiteExp_q) = ĝ_q` — the banked J4-622 identification
              `whitePullbackMetric_eq_fderiv_pullback`, bridged to the `pd`-based `pullbackMet`
              (§3, mirror of the banked `pullbackMet_eq_uniformFlowPullbackMetric`);
        (iii) the entrywise inverse `ĝ⁻¹·ĝ = δ` — the banked Neumann package
              `whitePullbackMetric_neumann` through the banked `sum_invMat_mul`;
        (iv)  `hGGi`/`hGiG` at the far point — banked `curvedRNCMetric_hinvF`/`curvedRNCInv_mul_metric`;
        (v)   φ-regularity `ContDiffAt 2` — banked `contDiffAt2_uniformFlowExp` ∘ the linear `E_q`.

  ── ★ ITEM (2): THE AMBIENT WHITENED KERNEL AND THE PRODUCER BOUND.
    • `whiteInvChart` — the whitened inverse chart `p ↦ E_q⁻¹ (uniformInverseChart_q p)`: the
      banked uniform inverse chart (UniformChartRadius) post-composed with the explicit whitening
      inverse of §1.  MIRRORS the as-built witness's evaluation through `uniformInverseChart`,
      with the whitened chart `whiteExp_q = uniformFlowExp_q ∘ E_q` inverted factor-by-factor.
    • `whiteAmbientKernel τ p q := √det g^κ(q) · G_τ(whiteInvChart_q p)` — the whitened witness
      Gaussian AS AN AMBIENT KERNEL (in chart velocity it is exactly the banked `whiteW`,
      `whiteW_eq_det_mul_gaussDdim`; the √det amplitude is the J4-623 item-3 bookkeeping).
    • `white_ambient_heatOp_eq` — the EXACT transfer: on the gate `p = whiteExp_q w`, `‖w‖ < r₀`,
          `heatOp g^κ gi^κ (whiteAmbientKernel) τ p q
             = heatOp ĝ_q ĝ⁻¹_q (√det g^κ(q) · flat phase) τ w 0`
      — time-slice equality is definitional through the inverse-chart germ; the space slice is
      the weld (1) + the germ collapse `whiteInvChart_q ∘ whiteExp_q = id` near `w` (banked
      uniform-chart germ, pulled back along the continuous linear `E_q`).
    • ★ `white_ambient_heatOp_bound` — the producer: `∃ r₀ > 0, ∃ C ≥ 0`, for EVERY `q ∈ K`,
      EVERY `τ > 0`, every `‖w‖ < r₀`:
          `|heatOp g^κ gi^κ (whiteAmbientKernel) τ (whiteExp_q w) q| ≤ C · G_{2τ}(w)`
      — the banked J4-623 chart bound (`whiteChart_heatOp_offdiag_bound_amp`) transported through
      the exact transfer.  ⚠ HONEST GAUSSIAN BOOKKEEPING: here the Gaussian is in the CHART
      VELOCITY `w = whiteInvChart_q p`.  The AMBIENT-displacement form is a separate corollary:
    • `white_ambient_heatOp_bound_displacement` — `≤ C′ · G_{λτ}(p − q)` with the EXPLICIT width
      `λ = 2(n·C₀² + 1)` (`C₀` = the banked uniform tube-confinement constant): the displacement
      comparison `‖p − q‖ ≤ C₀·‖E_q w‖` (banked `uniformFlowTube_spec_conf` at `t = 1`) +
      `rncRadialSq(E_q w) ≤ rncRadialSq w` (banked contraction `whiteVel_radialSq_le`) feed the
      banked width-transfer `gaussDdim_le_gaussDdim_chart`; the constant pays `√(λ/2)^n`.  The
      width is `λ`, NOT `2` — stated honestly; aligning to the capstone's literal width-2
      `baseKernelW 2 0` is a labelled residue (R2 below).

  ── ITEM (3): `white_hpkgBound_gateShaped` — the capstone `hpkgBound` SHAPE
      (`∀ t' τ …, 0 < τ → τ ≤ t' → |heatOp …| ≤ (C·(1+t'))·baseKernelW λ 0 τ p q`) at the
      whitened ambient kernel, ON THE GATE (`p = whiteExp_q w`, `‖w‖ < r₀`, `q ∈ K`).
      ⚠ LABELLED RESIDUES (the honest gap to the literal capstone slot):
        R1 (off-gate/cutoff layer): the capstone quantifies over ALL ambient `(p,q)`; the as-built
           witness achieves this via the `gatedKernel`/cutoff constructor which VANISHES off-gate.
           Extending the whitened kernel by the same gating (and proving the off-gate heatOp
           vanishing for it) is J4-625 material — NOT done here.
        R2 (width alignment): the ambient Gaussian width is `λ = 2(nC₀²+1)`, not the literal `2`
           of `baseKernelW 2 0` (the capstone's width slot); a width-parametric capstone thread or
           a sharpened displacement constant is owed.
        R3 (row/column roles): the bound is for column `q ∈ K` with `p` in the gated image of the
           `q`-chart — the per-chart form; the capstone's unconstrained `(p,q)` needs R1.

  ── NON-VACUITY (cp466 discipline): `whiteAmbient_witness_gate` — the ★ producer is INSTANTIATED
  at the genuinely curved fat witness (`n = 2`, `κ = −1`, `K = closedBall 0 2`) where (i) the
  AMBIENT flat-phase pair provably admits NO such bound (the J4-621 pin, same witness), and
  (ii) the whitened ambient kernel is GENUINELY curved (amplitude `√(5/3) ≠ 1` at the off-center
  row `probeQ`) and everywhere nonzero; the gate `‖w‖ < r₀` is inhabited (`r₀ > 0`).

  No `sorry`, no `admit`, no new axioms, no `:= True`; no existing file edited except the
  `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.WhiteOffDiag
import QIQTH.PullbackNaturalityLocal
import QIQTH.UniformChartRadius
import QIQTH.VanVleckCancellation
import QIQTH.WidthMarginEngine
import QIQTH.GaussianWidthTolerant

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.RNCDecay
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.CurvedA1CenterAmp QIQTH.CurvedA1CenterN1 QIQTH.EquivProbe
open QIQTH.CConvV2GaussianPairing QIQTH.GaussianWidthTransfer
open QIQTH.FrozenGauss QIQTH.LeviSeries QIQTH.WhiteWitness QIQTH.WhiteReplay
open QIQTH.CurvedRNCVanVleckBound QIQTH.WhiteOffDiag
open Set Filter
open scoped Topology BigOperators

namespace QIQTH.WhiteAmbient

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ### 0. The flat-phase / Gaussian dictionary. -/

/-- `flatPhaseModel τ x 0 = gaussDdim τ x` — the column-0 slice of the flat phase IS the flat
    Gaussian in the chart coordinate. -/
theorem flatPhaseModel_zero_right (τ : ℝ) (x : Point n) :
    flatPhaseModel τ x (0 : Point n) = gaussDdim τ x := by
  simp only [flatPhaseModel]
  congr 1
  funext i
  simp

/-! ### 1. The explicit two-sided whitening inverse `E_q⁻¹ = g^κ(q)·E_q`. -/

/-- `matToCLM (curvedWhitening κ q)` acts as the whitened velocity map `whiteVel κ q`. -/
theorem matToCLM_curvedWhitening_apply (κ : ℝ) (q w : Point n) :
    matToCLM (curvedWhitening κ q) w = whiteVel κ q w := by
  funext i
  rw [matToCLM_apply]
  rfl

/-- **Left-inverse identity**: `(E_q·g^κ(q)) · E_q = δ` entrywise — the banked whitening identity
    `E_qᵀ g^κ(q) E_q = δ` (`curvedRNC_whitening_all`) re-associated.  NOT `a₁ = R/6`. -/
theorem whitening_left_inverse (κ : ℝ) (hκ : κ ≤ 0) (q : Point n) (i j : Fin n) :
    (∑ k, (∑ m, curvedWhitening κ q i m * curvedRNCMetric κ q m k) * curvedWhitening κ q k j)
      = if i = j then (1 : ℝ) else 0 := by
  have h := curvedRNC_whitening_all κ hκ q i j
  rw [← h]
  calc (∑ k, (∑ m, curvedWhitening κ q i m * curvedRNCMetric κ q m k)
        * curvedWhitening κ q k j)
      = ∑ k, ∑ m, curvedWhitening κ q i m * curvedRNCMetric κ q m k
          * curvedWhitening κ q k j := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ m, ∑ k, curvedWhitening κ q i m * curvedRNCMetric κ q m k
          * curvedWhitening κ q k j := Finset.sum_comm
    _ = ∑ k, ∑ l, curvedWhitening κ q i k * curvedRNCMetric κ q k l
          * curvedWhitening κ q l j := rfl

/-- **Right-inverse identity**: `E_q · (g^κ(q)·E_q) = δ` entrywise. -/
theorem whitening_right_inverse (κ : ℝ) (hκ : κ ≤ 0) (q : Point n) (i j : Fin n) :
    (∑ k, curvedWhitening κ q i k * (∑ m, curvedRNCMetric κ q k m * curvedWhitening κ q m j))
      = if i = j then (1 : ℝ) else 0 := by
  have h := curvedRNC_whitening_all κ hκ q i j
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => by ring

/-- **The whitening inverse operator** `E_q⁻¹ := matToCLM (g^κ(q)·E_q)` — an EXPLICIT closed-form
    two-sided inverse of the whitening frame (no abstract finite-dimension argument). -/
noncomputable def whiteUnvel (κ : ℝ) (q : Point n) : Point n →L[ℝ] Point n :=
  matToCLM (fun i j => ∑ m, curvedRNCMetric κ q i m * curvedWhitening κ q m j)

/-- `E_q · E_q⁻¹ = 1` as operators. -/
theorem whiteVel_mul_whiteUnvel (κ : ℝ) (hκ : κ ≤ 0) (q : Point n) :
    matToCLM (curvedWhitening κ q) * whiteUnvel κ q = 1 :=
  matToCLM_mul_eq_one _ _ (fun i c => whitening_right_inverse κ hκ q i c)

/-- `E_q⁻¹ · E_q = 1` as operators — via the left-inverse matrix and the two-sided cancellation
    `L = L(ER) = (LE)R = R`. -/
theorem whiteUnvel_mul_whiteVel (κ : ℝ) (hκ : κ ≤ 0) (q : Point n) :
    whiteUnvel κ q * matToCLM (curvedWhitening κ q) = 1 := by
  set E : Point n →L[ℝ] Point n := matToCLM (curvedWhitening κ q) with hE
  set L : Point n →L[ℝ] Point n :=
    matToCLM (fun i j => ∑ m, curvedWhitening κ q i m * curvedRNCMetric κ q m j) with hL
  have hLE : L * E = 1 :=
    matToCLM_mul_eq_one _ _ (fun i c => whitening_left_inverse κ hκ q i c)
  have hER : E * whiteUnvel κ q = 1 := whiteVel_mul_whiteUnvel κ hκ q
  have hLR : L = whiteUnvel κ q := by
    calc L = L * 1 := (mul_one L).symm
      _ = L * (E * whiteUnvel κ q) := by rw [hER]
      _ = (L * E) * whiteUnvel κ q := (mul_assoc L E (whiteUnvel κ q)).symm
      _ = 1 * whiteUnvel κ q := by rw [hLE]
      _ = whiteUnvel κ q := one_mul _
  rw [← hLR]
  exact hLE

/-- **The whitening frame is a UNIT** — with the explicit inverse `whiteUnvel`. -/
theorem curvedWhitening_isUnit (κ : ℝ) (hκ : κ ≤ 0) (q : Point n) :
    IsUnit (matToCLM (curvedWhitening κ q)) :=
  ⟨⟨matToCLM (curvedWhitening κ q), whiteUnvel κ q,
    whiteVel_mul_whiteUnvel κ hκ q, whiteUnvel_mul_whiteVel κ hκ q⟩, rfl⟩

/-- The inverse UNDOES the whitened velocity: `E_q⁻¹ (E_q w) = w`. -/
theorem whiteUnvel_whiteVel (κ : ℝ) (hκ : κ ≤ 0) (q w : Point n) :
    whiteUnvel κ q (whiteVel κ q w) = w := by
  have h := congrArg (fun T : Point n →L[ℝ] Point n => T w) (whiteUnvel_mul_whiteVel κ hκ q)
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply,
    matToCLM_curvedWhitening_apply] using h

/-! ### 2. Whitened-chart regularity: whole-map and per-component `ContDiffAt 2`. -/

/-- **The whitened chart is `C²` at gate points** (whole map): `whiteExp_q = F_q ∘ E_q` with the
    banked `contDiffAt2_uniformFlowExp` at the whitened velocity and the smooth linear `E_q`. -/
theorem whiteExp_contDiffAt2_whole (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (w : Point n)
    (hw : ‖whiteVel κ q w‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc) :
    ContDiffAt ℝ 2 (whiteExp κ hκ hKc q) w := by
  set F : Point n → Point n :=
    uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q with hF
  set E : Point n →L[ℝ] Point n := matToCLM (curvedWhitening κ q) with hE
  have hcomp : whiteExp κ hκ hKc q = F ∘ ⇑E := by
    funext v
    rw [Function.comp_apply, hE, matToCLM_curvedWhitening_apply]
    rfl
  have hFreg : ContDiffAt ℝ 2 F (E w) := by
    rw [hE, matToCLM_curvedWhitening_apply]
    exact contDiffAt2_uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q hq (whiteVel κ q w) hw
  rw [hcomp]
  exact hFreg.comp w (E.contDiff.contDiffAt)

/-- Per-component `ContDiffAt 2` — the exact `hφ` shape the local naturality tower consumes. -/
theorem whiteExp_contDiffAt2 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (w : Point n)
    (hw : ‖whiteVel κ q w‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc) (a : Fin n) :
    ContDiffAt ℝ 2 (fun y => whiteExp κ hκ hKc q y a) w :=
  (ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).contDiff.comp_contDiffAt w
    (whiteExp_contDiffAt2_whole κ hκ hKc q hq w hw)

/-! ### 3. The bridge: `pd`-based `pullbackMet` at `whiteExp` = the banked `ĝ_q`. -/

/-- **The pullback identification at the whitened chart** — the abstract congruence pullback
    (`pd`-based `pullbackMet`) at `φ = whiteExp_q` EQUALS the banked whitened chart metric `ĝ_q`
    on the flow gate; mirror of the banked `pullbackMet_eq_uniformFlowPullbackMetric` through the
    J4-622 `fderiv`-identification `whitePullbackMetric_eq_fderiv_pullback`. -/
theorem pullbackMet_eq_whitePullbackMetric (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (w : Point n)
    (hw : ‖whiteVel κ q w‖ < uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc) (i j : Fin n) :
    pullbackMet (curvedRNCMetric κ) (whiteExp κ hκ hKc q) w i j
      = whitePullbackMetric κ hκ hKc q w i j := by
  have hφd : DifferentiableAt ℝ (whiteExp κ hκ hKc q) w :=
    (whiteExp_contDiffAt2_whole κ hκ hKc q hq w hw).differentiableAt (by norm_num)
  have pdeq : ∀ (a p : Fin n), pd (fun y => whiteExp κ hκ hKc q y a) p w
      = (fderiv ℝ (whiteExp κ hκ hKc q) w) (Pi.single p 1) a := by
    intro a p
    have hHF : HasFDerivAt (fun y => whiteExp κ hκ hKc q y a)
        ((ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).comp
          (fderiv ℝ (whiteExp κ hκ hKc q) w)) w :=
      (ContinuousLinearMap.proj a : Point n →L[ℝ] ℝ).hasFDerivAt.comp w hφd.hasFDerivAt
    rw [pd_eq_fderiv (fun y => whiteExp κ hκ hKc q y a) p w hHF.differentiableAt, hHF.fderiv]
    simp [ContinuousLinearMap.comp_apply]
  rw [whitePullbackMetric_eq_fderiv_pullback κ hκ hKc q hq w hw i j]
  simp only [pullbackMet]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [pdeq a i, pdeq b j]

/-! ### 4. ITEM (1) — THE NATURALITY WELD. -/

/-- **★ J4-624 item (1) — Laplace–Beltrami naturality at the WHITENED chart.**
        `Δ_{ĝ_q}(f ∘ whiteExp_q)(w) = (Δ_{g^κ} f)(whiteExp_q w)`
    on ONE uniform gate `‖w‖ < r₀` over all `q ∈ K`, for EVERY `f` that is `C²` at the far point
    (the sole surviving side condition — genuine, consumed by the transfer below with a concrete
    smooth `f`).  All other inputs of the banked engine `laplaceBeltrami_pullback_naturality_local`
    are DISCHARGED: Jacobian invertibility (products of units, §1 + banked common nondeg radius),
    the metric identification (§3), the entrywise inverse (banked Neumann + `sum_invMat_mul`),
    `g·gi = δ = gi·g` at the far point (banked), φ-regularity (§2).  NOT `a₁ = R/6`. -/
theorem laplaceBeltrami_whiteExp_naturality (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ r₀ > (0 : ℝ), ∀ q ∈ Kset, ∀ w : Point n, ‖w‖ < r₀ → ∀ f : Point n → ℝ,
      ContDiffAt ℝ 2 f (whiteExp κ hκ hKc q w) →
      laplaceBeltrami (fun v => whitePullbackMetric κ hκ hKc q v)
          (fun v => whitePullbackMetricInv κ hκ hKc q v)
          (fun z => f (whiteExp κ hκ hKc q z)) w
        = laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ) f (whiteExp κ hκ hKc q w) := by
  classical
  obtain ⟨ρ₀, hρ₀0, hnondeg⟩ := uniformFlowExp_common_nondeg_radius (curvedRNCMetric κ)
    (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  obtain ⟨rN, hrN0, M, hM0, hpkgN⟩ := whitePullbackMetric_neumann κ hκ hKc
  set Rf : ℝ := uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) hKc with hRf
  have hRf0 : 0 < Rf := uniformFlowRadius_pos _ _ _ _
  have hsn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  set ρ : ℝ := min ρ₀ Rf with hρdef
  have hρ0 : 0 < ρ := lt_min hρ₀0 hRf0
  set r₀ : ℝ := min rN (ρ / (Real.sqrt n + 1)) with hr₀def
  have hr₀0 : 0 < r₀ := lt_min hrN0 (by positivity)
  refine ⟨r₀, hr₀0, ?_⟩
  intro q hq w hw f hf
  have hwN : ‖w‖ < rN := lt_of_lt_of_le hw (min_le_left _ _)
  -- velocity confinement into the base radii
  have hconf : ∀ w' : Point n, ‖w'‖ < r₀ → ‖whiteVel κ q w'‖ < ρ := by
    intro w' hw'
    have h1 : ‖whiteVel κ q w'‖ ≤ Real.sqrt n * ‖w'‖ := whiteVel_norm_le κ hκ q w'
    have h2 : ‖w'‖ < ρ / (Real.sqrt n + 1) := lt_of_lt_of_le hw' (min_le_right _ _)
    have h3 : Real.sqrt n * ‖w'‖ ≤ (Real.sqrt n + 1) * ‖w'‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have h4 : (Real.sqrt n + 1) * ‖w'‖ < (Real.sqrt n + 1) * (ρ / (Real.sqrt n + 1)) :=
      mul_lt_mul_of_pos_left h2 (by positivity)
    have h5 : (Real.sqrt n + 1) * (ρ / (Real.sqrt n + 1)) = ρ := by field_simp
    linarith
  have hvρ : ‖whiteVel κ q w‖ < ρ := hconf w hw
  have hvρ₀ : ‖whiteVel κ q w‖ < ρ₀ := lt_of_lt_of_le hvρ (min_le_left _ _)
  have hvRf : ‖whiteVel κ q w‖ < Rf := lt_of_lt_of_le hvρ (min_le_right _ _)
  -- φ-regularity, per component
  have hφreg : ∀ a, ContDiffAt ℝ 2 (fun y => whiteExp κ hκ hKc q y a) w :=
    fun a => whiteExp_contDiffAt2 κ hκ hKc q hq w hvRf a
  -- Jacobian invertibility (product of units)
  have hφinv : IsUnit (fderiv ℝ (whiteExp κ hκ hKc q) w) := by
    rw [whiteExp_fderiv κ hκ hKc q hq w hvRf]
    exact (hnondeg q hq (whiteVel κ q w) hvρ₀).mul (curvedWhitening_isUnit κ hκ q)
  -- the entrywise inverse of ĝ against pullbackMet
  have hU : IsUnit (matToCLM (fun a b => whitePullbackMetric κ hκ hKc q w a b)) :=
    (hpkgN q hq w hwN).2.1
  have hgtinv : ∀ p qq, (∑ k, whitePullbackMetricInv κ hκ hKc q w p k
      * pullbackMet (curvedRNCMetric κ) (whiteExp κ hκ hKc q) w k qq)
      = if p = qq then (1 : ℝ) else 0 := by
    intro p qq
    have h1 := sum_invMat_mul (fun a b => whitePullbackMetric κ hκ hKc q w a b) hU p qq
    rw [← h1]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pullbackMet_eq_whitePullbackMetric κ hκ hKc q hq w hvRf k qq]
    rfl
  -- the local capstone at φ = whiteExp
  have hL2 := laplaceBeltrami_pullback_naturality_local (curvedRNCMetric κ) (curvedRNCInv κ)
    (whiteExp κ hκ hKc q) (fun v => whitePullbackMetricInv κ hκ hKc q v) f
    (fun y a b => curvedRNCMetric_symm κ y a b) w hφinv
    (fun p c => curvedRNCMetric_hinvF κ hκ (whiteExp κ hκ hKc q w) p c)
    (fun p c => curvedRNCInv_mul_metric κ hκ (whiteExp κ hκ hKc q w) p c)
    hgtinv
    (fun a b => ((curvedRNCMetric_contDiff κ a b).of_le le_top).contDiffAt)
    hφreg hf
  -- swap the germ-equal metric functions ĝ ↔ pullbackMet
  have hne : ∀ a b,
      (fun v => whitePullbackMetric κ hκ hKc q v a b) =ᶠ[nhds w]
        (fun v => pullbackMet (curvedRNCMetric κ) (whiteExp κ hκ hKc q) v a b) := by
    intro a b
    have hball : Metric.ball (0 : Point n) r₀ ∈ nhds w :=
      Metric.isOpen_ball.mem_nhds (by rwa [mem_ball_zero_iff])
    filter_upwards [hball] with w' hw'
    rw [mem_ball_zero_iff] at hw'
    exact (pullbackMet_eq_whitePullbackMetric κ hκ hKc q hq w'
      (lt_of_lt_of_le (hconf w' hw') (min_le_right _ _)) a b).symm
  rw [laplaceBeltrami_congr_metric_nhds
      (fun v => whitePullbackMetric κ hκ hKc q v)
      (pullbackMet (curvedRNCMetric κ) (whiteExp κ hκ hKc q))
      (fun v => whitePullbackMetricInv κ hκ hKc q v)
      (fun z => f (whiteExp κ hκ hKc q z)) w hne]
  exact hL2

/-! ### 5. ITEM (2) — the ambient whitened kernel and the exact transfer. -/

/-- **The whitened inverse chart** `p ↦ E_q⁻¹ (uniformInverseChart_q p)` — the factor-by-factor
    inverse of `whiteExp_q = uniformFlowExp_q ∘ E_q`, mirroring the as-built witness's evaluation
    through the banked `uniformInverseChart`. -/
noncomputable def whiteInvChart (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q p : Point n) : Point n :=
  whiteUnvel κ q (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
    (curvedRNC_hChr κ hκ) hKc q p)

/-- **THE AMBIENT WHITENED KERNEL** `W_white(τ,p,q) := √det g^κ(q) · G_τ(whiteInvChart_q p)` —
    the whitened witness Gaussian as an ambient kernel: in chart velocity it is EXACTLY the
    banked `whiteW` (`whiteW_eq_det_mul_gaussDdim`). -/
noncomputable def whiteAmbientKernel (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) : ℝ → Point n → Point n → ℝ :=
  fun τ p q => Real.sqrt (Matrix.det (curvedRNCMetric κ q))
    * gaussDdim τ (whiteInvChart κ hκ hKc q p)

/-- **The inverse-chart germ package**: ONE radius `δ₀ > 0` with, for every `q ∈ K` and every
    chart point with `‖E_q w‖ < δ₀`: (i) `whiteInvChart_q ∘ whiteExp_q = id` as germs at `w`
    (the banked uniform-chart germ pulled back along the continuous linear `E_q`, then unwound by
    the explicit inverse §1), and (ii) `uniformInverseChart_q` is `C²` at the far point. -/
theorem whiteInvChart_pack (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ δ₀ > (0 : ℝ), ∀ q ∈ Kset, ∀ w : Point n, ‖whiteVel κ q w‖ < δ₀ →
      ((fun w' => whiteInvChart κ hκ hKc q (whiteExp κ hκ hKc q w')) =ᶠ[nhds w]
        fun w' => w')
      ∧ ContDiffAt ℝ 2 (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
          (curvedRNC_hChr κ hκ) hKc q) (whiteExp κ hκ hKc q w) := by
  obtain ⟨δ₀, hδ₀0, hspec⟩ := uniformInverseChart_huniformChart (curvedRNCMetric κ)
    (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
  refine ⟨δ₀, hδ₀0, ?_⟩
  intro q hq w hv
  obtain ⟨hgerm, hC2⟩ := (hspec q hq).1 (whiteVel κ q w) hv
  refine ⟨?_, hC2⟩
  -- pull the germ back along the continuous whitened-velocity map
  have hEc : Continuous (fun w' : Point n => whiteVel κ q w') := by
    have h := (matToCLM (curvedWhitening κ q)).continuous
    have hfe : ⇑(matToCLM (curvedWhitening κ q)) = fun w' : Point n => whiteVel κ q w' :=
      funext fun w' => matToCLM_curvedWhitening_apply κ q w'
    rwa [hfe] at h
  have htend : Filter.Tendsto (fun w' : Point n => whiteVel κ q w') (nhds w)
      (nhds (whiteVel κ q w)) := hEc.continuousAt
  have hpull : ∀ᶠ w' in nhds w,
      uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q
        (uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q
          (whiteVel κ q w')) = whiteVel κ q w' := htend.eventually hgerm
  filter_upwards [hpull] with w' hw'
  show whiteUnvel κ q (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc q (whiteExp κ hκ hKc q w')) = w'
  have hφ : whiteExp κ hκ hKc q w'
      = uniformFlowExp (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc q
          (whiteVel κ q w') := rfl
  rw [hφ, hw', whiteUnvel_whiteVel κ hκ q w']

/-- **★ THE EXACT CHART→AMBIENT TRANSFER** — on the gate `p = whiteExp_q w`, `‖w‖ < r₀`, the
    ambient heat defect of the whitened kernel EQUALS the banked chart-side defect of the
    amplitude-carrying whitened Gaussian:
        `heatOp g^κ gi^κ (W_white) τ (whiteExp_q w) q
           = heatOp ĝ_q ĝ⁻¹_q (√det g^κ(q)·flat phase) τ w 0`.
    Time slice: definitional through the inverse-chart value; space slice: the weld (item 1) +
    the germ collapse.  NOT `a₁ = R/6`. -/
theorem white_ambient_heatOp_eq (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    ∃ r₀ > (0 : ℝ), ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ w : Point n, ‖w‖ < r₀ →
      heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteAmbientKernel κ hκ hKc) τ
          (whiteExp κ hκ hKc q w) q
        = heatOp (fun v => whitePullbackMetric κ hκ hKc q v)
            (fun v => whitePullbackMetricInv κ hκ hKc q v)
            (fun t x y => Real.sqrt (Matrix.det (curvedRNCMetric κ q)) * flatPhaseModel t x y)
            τ w (0 : Point n) := by
  classical
  obtain ⟨r₁, hr₁0, hweld⟩ := laplaceBeltrami_whiteExp_naturality κ hκ hKc
  obtain ⟨δ₀, hδ₀0, hpack⟩ := whiteInvChart_pack κ hκ hKc
  have hsn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  set r₀ : ℝ := min r₁ (δ₀ / (Real.sqrt n + 1)) with hr₀def
  have hr₀0 : 0 < r₀ := lt_min hr₁0 (by positivity)
  refine ⟨r₀, hr₀0, ?_⟩
  intro q hq τ hτ w hw
  have hw1 : ‖w‖ < r₁ := lt_of_lt_of_le hw (min_le_left _ _)
  have hvδ : ‖whiteVel κ q w‖ < δ₀ := by
    have h1 : ‖whiteVel κ q w‖ ≤ Real.sqrt n * ‖w‖ := whiteVel_norm_le κ hκ q w
    have h2 : ‖w‖ < δ₀ / (Real.sqrt n + 1) := lt_of_lt_of_le hw (min_le_right _ _)
    have h3 : Real.sqrt n * ‖w‖ ≤ (Real.sqrt n + 1) * ‖w‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have h4 : (Real.sqrt n + 1) * ‖w‖ < (Real.sqrt n + 1) * (δ₀ / (Real.sqrt n + 1)) :=
      mul_lt_mul_of_pos_left h2 (by positivity)
    have h5 : (Real.sqrt n + 1) * (δ₀ / (Real.sqrt n + 1)) = δ₀ := by field_simp
    linarith
  obtain ⟨hgerm, hC2⟩ := hpack q hq w hvδ
  have hval : whiteInvChart κ hκ hKc q (whiteExp κ hκ hKc q w) = w := hgerm.eq_of_nhds
  set c : ℝ := Real.sqrt (Matrix.det (curvedRNCMetric κ q)) with hc
  -- the concrete ambient section is C² at the far point
  have hf : ContDiffAt ℝ 2 (fun p' => whiteAmbientKernel κ hκ hKc τ p' q)
      (whiteExp κ hκ hKc q w) := by
    have h1 : ContDiffAt ℝ 2 (fun p' => whiteInvChart κ hκ hKc q p')
        (whiteExp κ hκ hKc q w) := by
      have hlin : ContDiffAt ℝ 2 (⇑(whiteUnvel κ q))
          (uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
            hKc q (whiteExp κ hκ hKc q w)) := (whiteUnvel κ q).contDiff.contDiffAt
      exact hlin.comp _ hC2
    have h2 : ContDiffAt ℝ 2 (fun v : Point n => gaussDdim τ v)
        (whiteInvChart κ hκ hKc q (whiteExp κ hκ hKc q w)) :=
      (QIQTH.HeatParametrixOrder.gaussDdim_contDiff τ).contDiffAt.of_le le_top
    have h3 : ContDiffAt ℝ 2
        (fun p' => gaussDdim τ (whiteInvChart κ hκ hKc q p')) (whiteExp κ hκ hKc q w) :=
      h2.comp _ h1
    exact contDiffAt_const.mul h3
  -- the naturality weld at this concrete section
  have hnat := hweld q hq w hw1 (fun p' => whiteAmbientKernel κ hκ hKc τ p' q) hf
  -- assemble the two heatOp slices
  simp only [heatOp]
  have htime : (fun u => whiteAmbientKernel κ hκ hKc u (whiteExp κ hκ hKc q w) q)
      = (fun u => c * flatPhaseModel u w (0 : Point n)) := by
    funext u
    simp only [whiteAmbientKernel]
    rw [hval, flatPhaseModel_zero_right]
  have hlap : laplaceBeltrami (curvedRNCMetric κ) (curvedRNCInv κ)
      (fun p => whiteAmbientKernel κ hκ hKc τ p q) (whiteExp κ hκ hKc q w)
      = laplaceBeltrami (fun v => whitePullbackMetric κ hκ hKc q v)
          (fun v => whitePullbackMetricInv κ hκ hKc q v)
          (fun x => c * flatPhaseModel τ x (0 : Point n)) w := by
    rw [← hnat]
    refine QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds _ _ _ _ w ?_
    filter_upwards [hgerm] with w' hw'
    show whiteAmbientKernel κ hκ hKc τ (whiteExp κ hκ hKc q w') q
        = c * flatPhaseModel τ w' (0 : Point n)
    simp only [whiteAmbientKernel]
    rw [hw', flatPhaseModel_zero_right]
  rw [htime, hlap]

/-! ### 6. ★ THE PRODUCER BOUNDS. -/

/-- **★★ J4-624 item (2) — THE AMBIENT WHITENED PRODUCER BOUND (chart-velocity Gaussian).**
    ONE radius, ONE constant: for EVERY `q ∈ K`, EVERY `τ > 0`, every gate point `‖w‖ < r₀`,
        `|heatOp g^κ gi^κ (W_white) τ (whiteExp_q w) q| ≤ C · G_{2τ}(w)`
    — the banked J4-623 chart bound transported to the AMBIENT heat operator on the whitened
    kernel through the exact transfer.  ⚠ The Gaussian is in the chart velocity
    `w = whiteInvChart_q p`; the ambient-displacement form (with its honest width) follows. -/
theorem white_ambient_heatOp_bound (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ r₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ w : Point n, ‖w‖ < r₀ →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteAmbientKernel κ hκ hKc) τ
          (whiteExp κ hκ hKc q w) q|
        ≤ C * gaussDdim (2 * τ) w := by
  obtain ⟨r₁, hr₁0, heq⟩ := white_ambient_heatOp_eq κ hκ hKc
  obtain ⟨r₂, hr₂0, C, hC0, hbd⟩ := whiteChart_heatOp_offdiag_bound_amp κ hκ hKc R hKb
  refine ⟨min r₁ r₂, lt_min hr₁0 hr₂0, C, hC0, ?_⟩
  intro q hq τ hτ w hw
  rw [heq q hq τ hτ w (lt_of_lt_of_le hw (min_le_left _ _))]
  exact hbd q hq τ hτ w (lt_of_lt_of_le hw (min_le_right _ _))

/-- **The whitened chart displacement bound** `‖whiteExp_q w − q‖ ≤ C₀·‖E_q w‖` — the banked
    uniform tube confinement at `t = 1`, at the whitened velocity. -/
theorem whiteExp_displacement (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (w : Point n)
    (hv : ‖whiteVel κ q w‖ ≤ uniformFlowRadius (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) hKc) :
    ‖whiteExp κ hκ hKc q w - q‖
      ≤ uniformFlowConst (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ) hKc
        * ‖whiteVel κ q w‖ := by
  set g := curvedRNCMetric κ
  set gi := curvedRNCInv κ
  set hC := curvedRNC_hChr κ hκ
  set v : Point n := whiteVel κ q w with hvdef
  have hconf : ‖uniformFlowTube g gi hC hKc q v 1 - ((q, 0) : Point n × Point n)‖
      ≤ uniformFlowConst g gi hC hKc * ‖v‖ :=
    uniformFlowTube_spec_conf g gi hC hKc q hq v hv 1
      (Set.mem_Icc.mpr ⟨zero_le_one, le_refl _⟩)
  have hfst : (uniformFlowTube g gi hC hKc q v 1).1 - q
      = (uniformFlowTube g gi hC hKc q v 1 - ((q, 0) : Point n × Point n)).1 := by
    rw [Prod.fst_sub]
  have hproj : ‖(uniformFlowTube g gi hC hKc q v 1).1 - q‖
      ≤ ‖uniformFlowTube g gi hC hKc q v 1 - ((q, 0) : Point n × Point n)‖ := by
    rw [hfst, Prod.norm_def]
    exact le_max_left _ _
  calc ‖whiteExp κ hκ hKc q w - q‖
      = ‖(uniformFlowTube g gi hC hKc q v 1).1 - q‖ := by
        rw [show whiteExp κ hκ hKc q w = uniformFlowExp g gi hC hKc q v from rfl,
          uniformFlowExp_eq]
    _ ≤ ‖uniformFlowTube g gi hC hKc q v 1 - ((q, 0) : Point n × Point n)‖ := hproj
    _ ≤ uniformFlowConst g gi hC hKc * ‖v‖ := hconf

/-- **★ The AMBIENT-DISPLACEMENT producer bound** — the honest ambient Gaussian form:
        `|heatOp g^κ gi^κ (W_white) τ (whiteExp_q w) q| ≤ C′ · G_{λτ}(p − q)`,  `p = whiteExp_q w`,
    with the EXPLICIT width `λ = 2(n·C₀² + 1) ≥ 2` (`C₀` the banked tube-confinement constant)
    and `C′ = C·√(λ/2)ⁿ`: the displacement `rncRadialSq(p−q) ≤ n·C₀²·rncRadialSq w` (tube
    confinement + the whitening `rncRadialSq` contraction) feeds the banked width transfer
    `gaussDdim_le_gaussDdim_chart`.  ⚠ Width `λ`, NOT the capstone's literal `2` — residue R2. -/
theorem white_ambient_heatOp_bound_displacement (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ r₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ lam : ℝ, 2 ≤ lam ∧
      ∀ q ∈ Kset, ∀ τ : ℝ, 0 < τ → ∀ w : Point n, ‖w‖ < r₀ →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteAmbientKernel κ hκ hKc) τ
          (whiteExp κ hκ hKc q w) q|
        ≤ C * gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q) := by
  classical
  obtain ⟨r₁, hr₁0, C, hC0, hbd⟩ := white_ambient_heatOp_bound κ hκ hKc R hKb
  set g := curvedRNCMetric κ
  set gi := curvedRNCInv κ
  set hC := curvedRNC_hChr κ hκ
  set C₀ : ℝ := uniformFlowConst g gi hC hKc with hC₀def
  have hC₀0 : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hKc
  set Rf : ℝ := uniformFlowRadius g gi hC hKc with hRfdef
  have hRf0 : 0 < Rf := uniformFlowRadius_pos g gi hC hKc
  have hsn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  set lam : ℝ := 2 * ((n : ℝ) * C₀ ^ 2 + 1) with hlamdef
  have hlam2 : 2 ≤ lam := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) * C₀ ^ 2 := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
    rw [hlamdef]; nlinarith
  set r₀ : ℝ := min r₁ (Rf / (Real.sqrt n + 1)) with hr₀def
  have hr₀0 : 0 < r₀ := lt_min hr₁0 (by positivity)
  refine ⟨r₀, hr₀0, C * Real.sqrt (lam / 2) ^ n,
    mul_nonneg hC0 (pow_nonneg (Real.sqrt_nonneg _) n), lam, hlam2, ?_⟩
  intro q hq τ hτ w hw
  have hw1 : ‖w‖ < r₁ := lt_of_lt_of_le hw (min_le_left _ _)
  -- velocity confinement into the flow radius
  have hvRf : ‖whiteVel κ q w‖ ≤ Rf := by
    have h1 : ‖whiteVel κ q w‖ ≤ Real.sqrt n * ‖w‖ := whiteVel_norm_le κ hκ q w
    have h2 : ‖w‖ < Rf / (Real.sqrt n + 1) := lt_of_lt_of_le hw (min_le_right _ _)
    have h3 : Real.sqrt n * ‖w‖ ≤ (Real.sqrt n + 1) * ‖w‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have h4 : (Real.sqrt n + 1) * ‖w‖ < (Real.sqrt n + 1) * (Rf / (Real.sqrt n + 1)) :=
      mul_lt_mul_of_pos_left h2 (by positivity)
    have h5 : (Real.sqrt n + 1) * (Rf / (Real.sqrt n + 1)) = Rf := by field_simp
    linarith
  -- the displacement in radial-square form
  have hdisp : ‖whiteExp κ hκ hKc q w - q‖ ≤ C₀ * ‖whiteVel κ q w‖ :=
    whiteExp_displacement κ hκ hKc q hq w hvRf
  have hr2disp : rncRadialSq (whiteExp κ hκ hKc q w - q)
      ≤ (n : ℝ) * C₀ ^ 2 * rncRadialSq w := by
    have h1 : rncRadialSq (whiteExp κ hκ hKc q w - q)
        ≤ (n : ℝ) * ‖whiteExp κ hκ hKc q w - q‖ ^ 2 := by
      refine rncRadialSq_le_of_mem_closedBall
        (q := whiteExp κ hκ hKc q w - q) (r := ‖whiteExp κ hκ hKc q w - q‖) ?_
      rw [Metric.mem_closedBall, dist_zero_right]
    have h2 : ‖whiteExp κ hκ hKc q w - q‖ ^ 2 ≤ (C₀ * ‖whiteVel κ q w‖) ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg _) hdisp
      nlinarith
    have h3 : ‖whiteVel κ q w‖ ^ 2 ≤ rncRadialSq (whiteVel κ q w) := by
      have hle : ‖whiteVel κ q w‖ ≤ rncRadial (whiteVel κ q w) :=
        norm_le_rncRadial (whiteVel κ q w)
      have hsq : rncRadial (whiteVel κ q w) ^ 2 = rncRadialSq (whiteVel κ q w) := by
        rw [rncRadial, Real.sq_sqrt (rncRadialSq_nonneg _)]
      have := mul_self_le_mul_self (norm_nonneg _) hle
      nlinarith [this, hsq]
    have h4 : rncRadialSq (whiteVel κ q w) ≤ rncRadialSq w := whiteVel_radialSq_le κ hκ q w
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [h1, h2, h3, h4, sq_nonneg C₀]
  -- the width-transfer comparison
  have hnorm : 2 * rncRadialSq (whiteExp κ hκ hKc q w - q) ≤ lam * rncRadialSq w := by
    have h0 : (0 : ℝ) ≤ rncRadialSq w := rncRadialSq_nonneg w
    rw [hlamdef]
    nlinarith [hr2disp]
  have hcmp : gaussDdim (2 * τ) w
      ≤ Real.sqrt (lam / 2) ^ n * gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q) :=
    gaussDdim_le_gaussDdim_chart (by norm_num) (by linarith) hτ hnorm
  have hmain := hbd q hq τ hτ w hw1
  calc |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteAmbientKernel κ hκ hKc) τ
        (whiteExp κ hκ hKc q w) q|
      ≤ C * gaussDdim (2 * τ) w := hmain
    _ ≤ C * (Real.sqrt (lam / 2) ^ n * gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q)) :=
        mul_le_mul_of_nonneg_left hcmp hC0
    _ = C * Real.sqrt (lam / 2) ^ n * gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q) := by
        ring

/-! ### 7. ITEM (3) — the `hpkgBound`-SHAPED on-gate assembly (labelled residues R1–R3). -/

/-- **The capstone-`hpkgBound`-SHAPED on-gate assembly** — the exact `∀ t' τ …, 0 < τ → τ ≤ t' →
    |heatOp …| ≤ (C·(1+t'))·baseKernelW λ 0 τ p q` SHAPE of the capstone slot, at the whitened
    ambient kernel, restricted to the gate (`p = whiteExp_q w`, `‖w‖ < r₀`, `q ∈ K`).
    ⚠ LABELLED RESIDUES (see file header): R1 off-gate/cutoff quantification over all `(p,q)`
    (the gated-witness constructor layer), R2 width `λ = 2(nC₀²+1)` vs the literal `2`, R3 the
    per-chart row/column roles.  NOT the capstone instantiation; NOT `a₁ = R/6`. -/
theorem white_hpkgBound_gateShaped (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ r₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∃ lam : ℝ, 2 ≤ lam ∧
      ∀ t' : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ t' → ∀ q ∈ Kset, ∀ w : Point n, ‖w‖ < r₀ →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteAmbientKernel κ hκ hKc) τ
          (whiteExp κ hκ hKc q w) q|
        ≤ (C * (1 + t'))
            * QIQTH.GaussianWidthTolerant.baseKernelW lam 0 τ (whiteExp κ hκ hKc q w) q := by
  obtain ⟨r₀, hr₀0, C, hC0, lam, hlam2, hbd⟩ :=
    white_ambient_heatOp_bound_displacement κ hκ hKc R hKb
  refine ⟨r₀, hr₀0, C, hC0, lam, hlam2, ?_⟩
  intro t' τ hτ hτt q hq w hw
  have hG0 : 0 ≤ gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q) :=
    (gaussDdim_pos (lam * τ) (by nlinarith) _).le
  have h1t : (1 : ℝ) ≤ 1 + t' := by linarith
  have hkey := hbd q hq τ hτ w hw
  have hbaseval : QIQTH.GaussianWidthTolerant.baseKernelW lam (0 : ℝ) τ
      (whiteExp κ hκ hKc q w) q = gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q) := by
    simp only [QIQTH.GaussianWidthTolerant.baseKernelW]
    rw [Real.rpow_zero, one_mul]
  rw [hbaseval]
  calc |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteAmbientKernel κ hκ hKc) τ
        (whiteExp κ hκ hKc q w) q|
      ≤ C * gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q) := hkey
    _ ≤ (C * (1 + t')) * gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h1t hC0) hG0
        calc C * gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q)
            = (C * 1) * gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q) := by ring
          _ ≤ (C * (1 + t')) * gaussDdim (lam * τ) (whiteExp κ hκ hKc q w - q) := this

/-! ### 8. Non-vacuity / adversarial gates (cp466 discipline). -/

/-- **★ The witness gate**: at the genuinely curved fat witness (`n = 2`, `κ = −1`,
    `K = closedBall 0 2`): (i) the AMBIENT whitened kernel SATISFIES the producer bound
    (with an inhabited gate, `r₀ > 0`); (ii) the AMBIENT flat-phase pair at the SAME witness
    provably admits NO such bound (the J4-621 formal pin); (iii) the whitened ambient kernel is
    GENUINELY curved: at the off-center row `probeQ` its amplitude `√det g^κ(probeQ) = √(5/3) ≠ 1`
    separates it from the bare flat Gaussian at every `τ > 0` and every ambient point — the
    ambient transfer is not the flat tower in disguise.  NOT `a₁ = R/6`. -/
theorem whiteAmbient_witness_gate :
    (∃ r₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ q ∈ Metric.closedBall (0 : Point 2) 2, ∀ τ : ℝ, 0 < τ → ∀ w : Point 2, ‖w‖ < r₀ →
        |heatOp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
            (whiteAmbientKernel (-1 : ℝ) (by norm_num) (isCompact_closedBall (0 : Point 2) 2))
            τ (whiteExp (-1 : ℝ) (by norm_num) (isCompact_closedBall (0 : Point 2) 2) q w) q|
          ≤ C * gaussDdim (2 * τ) w)
    ∧ (¬ ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ p q : Point 2,
        |heatOp (curvedRNCMetric (-1 : ℝ)) (curvedRNCInv (-1 : ℝ))
            (fun t x y => flatPhaseModel t x y) τ p q|
          ≤ C * gaussDdim (2 * τ) (fun i => p i - q i))
    ∧ (∀ τ : ℝ, 0 < τ → ∀ p : Point 2,
        whiteAmbientKernel (-1 : ℝ) (by norm_num) (isCompact_closedBall (0 : Point 2) 2)
            τ p probeQ
          ≠ gaussDdim τ (whiteInvChart (-1 : ℝ) (by norm_num)
              (isCompact_closedBall (0 : Point 2) 2) probeQ p)) := by
  refine ⟨white_ambient_heatOp_bound (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 Set.Subset.rfl,
    flatPhase_hpkgBound_fails_witness, ?_⟩
  intro τ hτ p h
  simp only [whiteAmbientKernel] at h
  have hG : 0 < gaussDdim τ (whiteInvChart (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) probeQ p) := gaussDdim_pos τ hτ _
  have hamp : Real.sqrt (Matrix.det (curvedRNCMetric (-1 : ℝ) probeQ)) = 1 := by
    have h1 : Real.sqrt (Matrix.det (curvedRNCMetric (-1 : ℝ) probeQ))
        * gaussDdim τ (whiteInvChart (-1 : ℝ) (by norm_num)
            (isCompact_closedBall (0 : Point 2) 2) probeQ p)
        = 1 * gaussDdim τ (whiteInvChart (-1 : ℝ) (by norm_num)
            (isCompact_closedBall (0 : Point 2) 2) probeQ p) := by
      rw [h, one_mul]
    exact mul_right_cancel₀ hG.ne' h1
  rw [curvedRNC_det_probe] at hamp
  have h53 : (5 : ℝ) / 3 = 1 := Real.sqrt_eq_one.mp hamp
  norm_num at h53

end QIQTH.WhiteAmbient

section AxiomChecks
open QIQTH.WhiteAmbient
#print axioms QIQTH.WhiteAmbient.flatPhaseModel_zero_right
#print axioms QIQTH.WhiteAmbient.whitening_left_inverse
#print axioms QIQTH.WhiteAmbient.whitening_right_inverse
#print axioms QIQTH.WhiteAmbient.whiteVel_mul_whiteUnvel
#print axioms QIQTH.WhiteAmbient.whiteUnvel_mul_whiteVel
#print axioms QIQTH.WhiteAmbient.curvedWhitening_isUnit
#print axioms QIQTH.WhiteAmbient.whiteUnvel_whiteVel
#print axioms QIQTH.WhiteAmbient.whiteExp_contDiffAt2_whole
#print axioms QIQTH.WhiteAmbient.whiteExp_contDiffAt2
#print axioms QIQTH.WhiteAmbient.pullbackMet_eq_whitePullbackMetric
#print axioms QIQTH.WhiteAmbient.laplaceBeltrami_whiteExp_naturality
#print axioms QIQTH.WhiteAmbient.whiteInvChart_pack
#print axioms QIQTH.WhiteAmbient.white_ambient_heatOp_eq
#print axioms QIQTH.WhiteAmbient.white_ambient_heatOp_bound
#print axioms QIQTH.WhiteAmbient.whiteExp_displacement
#print axioms QIQTH.WhiteAmbient.white_ambient_heatOp_bound_displacement
#print axioms QIQTH.WhiteAmbient.white_hpkgBound_gateShaped
#print axioms QIQTH.WhiteAmbient.whiteAmbient_witness_gate
end AxiomChecks
