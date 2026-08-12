/-
  WhiteF1 — J4-643: the F1 RE-INSTANTIATION — the Jacobi bridge `r∂_r log det g = ρ`, the
  CORRECTED order-1 whitened witness (ansatz weight `Θ := (vanVleck ĝ)⁻¹`, fold
  `w₀ = (det ĝ)^{−1/4}`), and the re-derived K1 budget with {h0, h1, hamp} DISCHARGED.
  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★★ WHAT LANDS (executing the J4-642 §4/(g) verdict).
  (1) THE JACOBI BRIDGE (§1).  For a metric-symbol field `g` with entrywise partially
      differentiable entries at `v`, `gi(v)` a genuine right inverse of `g(v)` and symmetric
      at `v`:
          `r∂_r log det g (v) = ρ(v)`,   `ρ = radialLogDetSym` (the J4-642 symbolic form).
      Route: the BANKED analytic Jacobi formula (`QIQTH.JacobiFormula.hasDerivAt_log_det_matrix`,
      adjugate/cofactor route — Mathlib itself has NO det-derivative lemma) applied to the
      coordinate slice `t ↦ g(update v a t)` per direction `a`, entrywise `HasDerivAt` assembled
      through `hasDerivAt_pi`; the trace re-indexed through `gi`-symmetry.  This DISCHARGES the
      J4-642 labelled `hamp` chain rule: with `radialDeriv_rpow` (banked) one gets
          `r∂_r (det g)^{−1/4} = −¼·ρ·(det g)^{−1/4}`   (`radialDeriv_correctedFold`, §2).
  (2) THE CORRECTED WITNESS (§4).  `whiteChartKernel1'` = the order-1 whitened witness with the
      INVERTED ansatz weight `whiteThetaC := (whiteTheta)⁻¹ = √det ĝ`, so the amplitude fold is
      `whiteThetaC^{−1/2} = (det ĝ)^{−1/4}` — the classical Minakshisundaram amplitude (J4-642
      verdict; the OLD fold `(det ĝ)^{+1/4}` has `K₀ = ½ρw₀ ≠ 0`, counterexample banked).  The
      transported coefficients are UNCHANGED: the matched conjugation of the corrected weight is
      `transportOp ((whiteThetaC)⁻¹) = transportOp (whiteTheta)` (`transportOp_inv_inv`), i.e.
      the BANKED `whiteTransportOp` — the R/6 diagonal supplier is preserved
      (`whiteCoeffsC_matched`; carrier: `whiteChartKernel1'_diagonal_a1`).
  (3) THE RE-DERIVED BUDGET (§5–§6).  `white_h0_corrected` / `white_h1_corrected`: at any point
      carrying the whitened Gauss set + the Jacobi-bridge analytic legs, `K₀ = 0` AND `K₁ = 0`
      are THEOREMS at the corrected witness (via the banked J4-642 §4 cancellation theorems, hamp
      from (1), the ODE from the banked `transportCoeff_succ_transport_eq`).  The K1 `t²` budget
      `white_K1BudgetW_corrected` then holds with h0/h1/hamp GONE from the input list.
  (4) GATES (§7): the Jacobi bridge FIRES at the curved exponential witness (`ρ = 2 ≠ 0`) and
      agrees with the direct computation (two independent routes); the corrected-fold `K₀ = 0`
      is re-derived END-TO-END through the discharge machinery (no explicit exp computation) at
      the same curved witness; the corrected witness is nonzero at the curved κ = −1 data.

  ★ FOLD-SIGN-AGNOSTICISM AUDIT (J4-637→641 machinery, verified while wiring):
    • `parametrixResidual_N1_layers` / `_linear_gain`, `k1BudgetW_of_pointwise_linear_gain`,
      the `gaussDdim` width lemmas, `heatParametrix_diagonal_a1`, `whiteMetric_det_center`,
      `vanVleck_zero` — ALL generic in the ansatz weight `Θ` (consume it opaquely through
      `foldedCoeff`); the `hΔ` binder consumed `|Δ_g w₁|` generically.  Reused verbatim.
    • `whiteGauss_discharged` (J4-641) mentions NO fold at all — it supplies the corrected
      budget's `hGauss` verbatim (`white_hGauss_supplier_foldfree` pins this).
    • FLAGGED (fold-specific, NOT reusable): `heatParametrixFn` HARDWIRES `Θ := vanVleck G` —
      hence `whiteChartKernel1'` is built on `heatParametrix` directly; and the J4-640/641
      regularity DISCHARGES (`white_w0_contDiffAt2_gate`, `whiteDelta_discharged_C2_local`,
      `white_w1_contDiffAt2_of_chartC5`) are STATED at the old fold `whiteTheta` — their
      mechanisms (rpow chain / Δ-bound of a locally-C² field) are sign-agnostic but the
      statements must be re-instantiated at `whiteThetaC` (J4-644 work); here the corrected
      budget carries {hwsm, hu1d, hsm, hΔ} as labelled regularity legs.

  ⚠ HONEST SCOPE (binding).
    • The Jacobi bridge is UNCONDITIONAL at its stated generality (entrywise `PdiffAt` at the
      point, pointwise right inverse, `gi`-symmetry at the point).
    • THE POST-F1 K1 INPUT LIST of `white_K1BudgetW_corrected` (all at the whitened chart data):
        {hGauss — SUPPLIED by the banked fold-free `whiteGauss_discharged` (radius-existential);
         hsymI/hgsym (inverse/metric symmetry), hdGauss (differentiated Gauss — derivable from
         the banked pointwise `whitePullbackMetric_gauss` via `hdGauss_of_metric_gauss` given
         entry differentiability + field symmetry), hinv (pointwise right inverse — Neumann
         package territory), hdet (det positivity — pos-def territory): GEOMETRIC residue of the
         whitened-chart instantiation;
         hd (entrywise PdiffAt), hwsm, hu1d, hsm, hΔ: REGULARITY legs — the Jet-5 chart rung
         (their old-fold suppliers are chart-C⁵-conditional; corrected-fold re-instantiation
         owed)}.
      `htr` is DISCHARGED internally (`htr_of_inv_symm`); h0/h1/hamp are DISCHARGED.
    • `a₁ = R/6` remains CONDITIONAL: flat tower closed and non-vacuous; the curved side owes
      the post-F1 K1 residue above + the Jet-5 chart rung + the Duhamel-split carry + the
      fat-`K` carrier piles + the capstone co-instantiation at the CORRECTED witness + the prior
      analytic piles.  The diagonal `R/6` is a labelled CARRIER value (`hu1`), NOT derived.
  This brick = the F1 re-instantiation.  No axioms, no `sorry`, no `:= True`.
-/
import Mathlib
import QIQTH.WhiteTransport
import QIQTH.WhiteGauss
import QIQTH.JacobiFormula
import QIQTH.ParametrixTransportRadial

open Finset Filter Topology MeasureTheory Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.VanVleck QIQTH.HeatParametrixAnsatz QIQTH.ParametrixFunction
open QIQTH.HeatTransportRecursion
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.WhiteWitness QIQTH.WhiteReplay QIQTH.WhiteOffDiag QIQTH.WhiteAmbient
open QIQTH.WidthFree QIQTH.WhiteCapstoneWire
open QIQTH.WhiteOrder1 QIQTH.WhiteTransport QIQTH.WhiteGauss
open QIQTH.JacobiFormula
open scoped Matrix.Norms.Elementwise

namespace QIQTH.WhiteF1

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §1. ★ THE JACOBI BRIDGE — `r∂_r log det g = ρ` (radialLogDetSym), discharging `hamp`. -/

/-- The coordinate slice of the metric-symbol field is a differentiable MATRIX curve: entrywise
    `PdiffAt` at `v` along `a` assembles (via `hasDerivAt_pi`) into
    `HasDerivAt (t ↦ g(update v a t)) (∂_a g(v)) (v a)`. -/
theorem metric_slice_hasDerivAt (g : Point n → Fin n → Fin n → ℝ) (v : Point n) (a : Fin n)
    (hd : ∀ i j, PdiffAt (fun y => g y i j) a v) :
    HasDerivAt (fun t => (Matrix.of (g (Function.update v a t)) : Matrix (Fin n) (Fin n) ℝ))
      (Matrix.of (fun i j => pd (fun y => g y i j) a v)) (v a) := by
  refine hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ?_
  exact (hd i j).hasDerivAt

/-- **The determinant slice derivative** (the banked adjugate Jacobi formula
    `hasDerivAt_matrix_det` composed with the coordinate slice). -/
theorem det_slice_hasDerivAt (g : Point n → Fin n → Fin n → ℝ) (v : Point n) (a : Fin n)
    (hd : ∀ i j, PdiffAt (fun y => g y i j) a v) :
    HasDerivAt (fun t => Matrix.det (Matrix.of (g (Function.update v a t))))
      ((Matrix.of (g v)).adjugate
        * Matrix.of (fun i j => pd (fun y => g y i j) a v)).trace (v a) := by
  have h := hasDerivAt_matrix_det
    (fun t => (Matrix.of (g (Function.update v a t)) : Matrix (Fin n) (Fin n) ℝ))
    (fun _ => Matrix.of (fun i j => pd (fun y => g y i j) a v))
    (metric_slice_hasDerivAt g v a hd)
  simpa only [Function.update_eq_self] using h

/-- The determinant of the metric field is partially differentiable wherever the entries are —
    the analytic leg feeding `radialDeriv_rpow` at the corrected fold. -/
theorem det_pdiffAt (g : Point n → Fin n → Fin n → ℝ) (v : Point n) (a : Fin n)
    (hd : ∀ i j, PdiffAt (fun y => g y i j) a v) :
    PdiffAt (fun y => Matrix.det (g y)) a v :=
  (det_slice_hasDerivAt g v a hd).differentiableAt

/-- **★ The per-coordinate logarithmic Jacobi formula in symbol form.**  With `gi(v)` a
    pointwise right inverse of `g(v)`, symmetric at `v`:
        `∂_a log det g (v) = Σᵢⱼ gⁱʲ(v)·∂_a g_{ij}(v)`.
    Route: banked `hasDerivAt_log_det_matrix` + `Matrix.inv_eq_right_inv` + trace re-indexing
    through the `gi`-symmetry. -/
theorem pd_logDet_eq (g gi : Point n → Fin n → Fin n → ℝ) (v : Point n) (a : Fin n)
    (hd : ∀ i j, PdiffAt (fun y => g y i j) a v)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hinv : ∀ i j, (∑ k, g v i k * gi v k j) = if i = j then (1 : ℝ) else 0) :
    pd (fun y => Real.log (Matrix.det (g y))) a v
      = ∑ i, ∑ j, gi v i j * pd (fun y => g y i j) a v := by
  have hAB : (Matrix.of (g v) : Matrix (Fin n) (Fin n) ℝ) * Matrix.of (gi v) = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    exact hinv i j
  have hu : IsUnit (Matrix.det (Matrix.of (g v) : Matrix (Fin n) (Fin n) ℝ)) :=
    Matrix.isUnit_det_of_right_inverse hAB
  have hInv : (Matrix.of (g v) : Matrix (Fin n) (Fin n) ℝ)⁻¹ = Matrix.of (gi v) :=
    Matrix.inv_eq_right_inv hAB
  have hlog := hasDerivAt_log_det_matrix
    (fun t => (Matrix.of (g (Function.update v a t)) : Matrix (Fin n) (Fin n) ℝ))
    (fun _ => Matrix.of (fun i j => pd (fun y => g y i j) a v))
    (metric_slice_hasDerivAt g v a hd)
    (by simpa only [Function.update_eq_self] using hu)
  simp only [Function.update_eq_self] at hlog
  rw [hInv] at hlog
  have hderiv := hlog.deriv
  calc pd (fun y => Real.log (Matrix.det (g y))) a v
      = ((Matrix.of (gi v) : Matrix (Fin n) (Fin n) ℝ)
          * Matrix.of (fun i j => pd (fun y => g y i j) a v)).trace := hderiv
    _ = ∑ i, ∑ j, gi v i j * pd (fun y => g y i j) a v := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [hsym y x]

/-- **★★ THE JACOBI BRIDGE — `r∂_r log det g = ρ`.**  The radial derivative of the log
    determinant of the metric-symbol field equals the J4-642 symbolic radial log-determinant
    `radialLogDetSym` — the ONE h0 bridge lemma J4-642 labelled as owed.  Hypotheses: entrywise
    partial differentiability at `v`, `gi(v)` a pointwise right inverse of `g(v)`, `gi`
    symmetric at `v` — the honest generality (no global smoothness, no expMap). -/
theorem radial_logDet_eq_rho (g gi : Point n → Fin n → Fin n → ℝ) (v : Point n)
    (hd : ∀ (a i j : Fin n), PdiffAt (fun y => g y i j) a v)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hinv : ∀ i j, (∑ k, g v i k * gi v k j) = if i = j then (1 : ℝ) else 0) :
    radialDeriv (fun y => Real.log (Matrix.det (g y))) v = radialLogDetSym g gi v := by
  unfold radialDeriv radialLogDetSym
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pd_logDet_eq g gi v a (hd a) hsym hinv]

/-! ### §2. The `hamp` DISCHARGE — the corrected-fold radial chain rule. -/

/-- The corrected amplitude fold IS the classical Minakshisundaram amplitude:
    `((vanVleck g)⁻¹)^{−1/2} = (det g)^{−1/4}` (pointwise, given `det g ≥ 0`). -/
theorem correctedFold_eq_det_rpow (g : Point n → Fin n → Fin n → ℝ)
    (hdet0 : ∀ y, 0 ≤ Matrix.det (g y)) :
    (fun y => ((vanVleck g y)⁻¹) ^ (-(1 : ℝ) / 2))
      = fun y => (Matrix.det (g y)) ^ (-(1 : ℝ) / 4) := by
  funext y
  rw [vanVleck_apply, inv_inv, Real.sqrt_eq_rpow, ← Real.rpow_mul (hdet0 y)]
  congr 1
  norm_num

/-- **★ The J4-642 `hamp` chain rule, DISCHARGED**: the corrected fold obeys
        `r∂_r ((vanVleck g)⁻¹)^{−1/2} = −¼·ρ·((vanVleck g)⁻¹)^{−1/2}`
    at any point with the Jacobi-bridge legs (entrywise `PdiffAt`, pointwise right inverse,
    `gi`-symmetry, `det g ≥ 0` globally and `> 0` at the point).  Route: the fold rewrite +
    banked `radialDeriv_rpow` at `p = −1/4` + the Jacobi bridge (§1). -/
theorem radialDeriv_correctedFold (g gi : Point n → Fin n → Fin n → ℝ) (v : Point n)
    (hd : ∀ (a i j : Fin n), PdiffAt (fun y => g y i j) a v)
    (hsym : ∀ i j, gi v i j = gi v j i)
    (hinv : ∀ i j, (∑ k, g v i k * gi v k j) = if i = j then (1 : ℝ) else 0)
    (hdet0 : ∀ y, 0 ≤ Matrix.det (g y)) (hdetv : 0 < Matrix.det (g v)) :
    radialDeriv (fun y => ((vanVleck g y)⁻¹) ^ (-(1 : ℝ) / 2)) v
      = -((1 / 4) * radialLogDetSym g gi v * ((vanVleck g v)⁻¹) ^ (-(1 : ℝ) / 2)) := by
  have hPd : ∀ i, PdiffAt (fun y => Matrix.det (g y)) i v := fun i =>
    det_pdiffAt g v i (hd i)
  rw [correctedFold_eq_det_rpow g hdet0,
      QIQTH.ExpMap.radialDeriv_rpow (fun y => Matrix.det (g y)) v (-(1 : ℝ) / 4) hdetv hPd,
      radial_logDet_eq_rho g gi v hd hsym hinv]
  have hv : ((vanVleck g v)⁻¹) ^ (-(1 : ℝ) / 2) = (Matrix.det (g v)) ^ (-(1 : ℝ) / 4) :=
    congrFun (correctedFold_eq_det_rpow g hdet0) v
  rw [hv]
  ring

/-! ### §3. Auxiliary discharges: `htr` from the inverse; the differentiated Gauss identity
from the pointwise metric Gauss identity. -/

/-- **`htr` DISCHARGE**: the trace normalization `Σᵢⱼ gⁱʲ·g_{ij} = n` follows from the pointwise
    right inverse + metric symmetry at the point — it is NOT an independent input. -/
theorem htr_of_inv_symm (g gi : Point n → Fin n → Fin n → ℝ) (x : Point n)
    (hinv : ∀ i j, (∑ k, g x i k * gi x k j) = if i = j then (1 : ℝ) else 0)
    (hgsym : ∀ i j, g x i j = g x j i) :
    (∑ i, ∑ j, gi x i j * g x i j) = (n : ℝ) := by
  have h1 : ∀ i, (∑ k, g x i k * gi x k i) = 1 := fun i => by simpa using hinv i i
  calc (∑ i, ∑ j, gi x i j * g x i j)
      = ∑ i, ∑ j, g x j i * gi x i j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hgsym i j]
        ring
    _ = ∑ j, ∑ i, g x j i * gi x i j := Finset.sum_comm
    _ = ∑ _j : Fin n, (1 : ℝ) := Finset.sum_congr rfl fun j _ => h1 j
    _ = (n : ℝ) := by simp

/-- The coordinate partial derivative: `∂ᵢ(y ↦ yⱼ) = δᵢⱼ`. -/
lemma pd_coord (v : Point n) (j i : Fin n) :
    pd (fun y : Point n => y j) i v = if i = j then (1 : ℝ) else 0 := by
  by_cases h : i = j
  · subst h
    have hfun : (fun t : ℝ => Function.update v i t i) = fun t => t := by
      funext t
      simp [Function.update_apply]
    simp only [pd, hfun, if_pos rfl]
    exact deriv_id (v i)
  · have hji : ¬ j = i := fun hh => h hh.symm
    have hfun : (fun t : ℝ => Function.update v i t j) = fun _ => v j := by
      funext t
      simp [Function.update_apply, hji]
    simp only [pd, hfun, if_neg h]
    exact deriv_const _ _

/-- **The differentiated metric Gauss identity from the pointwise one** — the `hdGauss` leg of
    the J4-642 Gauss set is DERIVABLE: if `Σ_a g_{ja}(y)·y_a = y_j` on a ball around `v` (the
    banked shape of `whitePullbackMetric_gauss` / `metricGaussGauge_curvedRNC`), `g` is
    everywhere symmetric as a field, and the entries are partially differentiable at `v`, then
        `Σ_a v_a·∂ᵢg_{aj}(v) = δᵢⱼ − g_{ij}(v)`. -/
theorem hdGauss_of_metric_gauss (g : Point n → Fin n → Fin n → ℝ) (r : ℝ) (v : Point n)
    (hv : ‖v‖ < r)
    (hgauss : ∀ y : Point n, ‖y‖ < r → ∀ j, (∑ a, g y j a * y a) = y j)
    (hgsym : ∀ y i j, g y i j = g y j i)
    (hd : ∀ (a i j : Fin n), PdiffAt (fun y => g y i j) a v) :
    ∀ i j, (∑ a, v a * pd (fun y => g y a j) i v)
      = (if i = j then (1 : ℝ) else 0) - g v i j := by
  intro i j
  -- per-term slice derivatives of `F(y) = Σ_a g_{ja}(y)·y_a`
  have hslice : ∀ a : Fin n,
      HasDerivAt (fun t => g (Function.update v i t) j a * (Function.update v i t) a)
        (pd (fun y => g y j a) i v * v a + g v j a * (if i = a then (1 : ℝ) else 0)) (v i) := by
    intro a
    have h1 : HasDerivAt (fun t => g (Function.update v i t) j a)
        (pd (fun y => g y j a) i v) (v i) := (hd i j a).hasDerivAt
    have h2 : HasDerivAt (fun t => (Function.update v i t) a)
        (if i = a then (1 : ℝ) else 0) (v i) := by
      by_cases h : i = a
      · subst h
        have hfun : (fun t : ℝ => Function.update v i t i) = fun t => t := by
          funext t
          simp [Function.update_apply]
        rw [hfun, if_pos rfl]
        exact hasDerivAt_id (v i)
      · have hai : ¬ a = i := fun hh => h hh.symm
        have hfun : (fun t : ℝ => Function.update v i t a) = fun _ => v a := by
          funext t
          simp [Function.update_apply, hai]
        rw [hfun, if_neg h]
        exact hasDerivAt_const _ _
    simpa only [Function.update_eq_self] using h1.mul h2
  have hF : HasDerivAt
      (fun t => ∑ a, g (Function.update v i t) j a * (Function.update v i t) a)
      (∑ a, (pd (fun y => g y j a) i v * v a
        + g v j a * (if i = a then (1 : ℝ) else 0))) (v i) :=
    HasDerivAt.fun_sum (fun a _ => hslice a)
  -- eventual agreement with the coordinate slice on the Gauss ball
  have hcont : Continuous fun t : ℝ => Function.update v i t :=
    continuous_const.update i continuous_id
  have hopen : IsOpen {t : ℝ | ‖Function.update v i t‖ < r} :=
    isOpen_lt hcont.norm continuous_const
  have hmem : v i ∈ {t : ℝ | ‖Function.update v i t‖ < r} := by
    simp only [Set.mem_setOf_eq, Function.update_eq_self]
    exact hv
  have hev : (fun t => ∑ a, g (Function.update v i t) j a * (Function.update v i t) a)
      =ᶠ[nhds (v i)] (fun t => (Function.update v i t) j) := by
    filter_upwards [hopen.mem_nhds hmem] with t ht
    exact hgauss _ ht j
  -- combine the two derivative computations
  have hkey : (∑ a, (pd (fun y => g y j a) i v * v a
      + g v j a * (if i = a then (1 : ℝ) else 0))) = (if i = j then (1 : ℝ) else 0) := by
    have hd1 := hF.deriv
    have hd2 := hev.deriv_eq
    have hd3 : deriv (fun t => (Function.update v i t) j) (v i)
        = (if i = j then (1 : ℝ) else 0) := pd_coord v j i
    rw [← hd1, hd2, hd3]
  have hsplit : (∑ a, (pd (fun y => g y j a) i v * v a
      + g v j a * (if i = a then (1 : ℝ) else 0)))
      = (∑ a, v a * pd (fun y => g y j a) i v) + g v j i := by
    rw [Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun a _ => by ring
    · simp [mul_ite]
  have hfield : ∀ a : Fin n, (fun y => g y a j) = (fun y => g y j a) := fun a =>
    funext fun y => hgsym y a j
  rw [show (∑ a, v a * pd (fun y => g y a j) i v)
      = (∑ a, v a * pd (fun y => g y j a) i v) from
    Finset.sum_congr rfl fun a _ => by rw [hfield a]]
  rw [hgsym v i j]
  linarith [hkey, hsplit]

/-! ### §4. ★ THE CORRECTED ORDER-1 WHITENED WITNESS (the F1 re-instantiation). -/

/-- **The corrected (F1) ansatz weight** `Θ̂' := (whiteTheta)⁻¹ = (vanVleck ĝ)⁻¹ = √det ĝ` —
    so the amplitude fold `Θ̂'^{−1/2}` is `(det ĝ)^{−1/4}`, the classical Minakshisundaram
    amplitude (the J4-642 verdict; the old fold's exponent sign is corrected). -/
noncomputable def whiteThetaC (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) : Point n → ℝ :=
  fun x => (whiteTheta κ hκ hKc q x)⁻¹

/-- **★ The matched conjugation of the corrected weight IS the BANKED transport operator**
    (`transportOp_inv_inv` at the whitened data): `transportOp ((Θ̂')⁻¹) = whiteTransportOp` —
    the same operator that supplies the diagonal `R/6`. -/
theorem whiteThetaC_matched_op (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) :
    transportOp (fun y => (whiteThetaC κ hκ hKc q y)⁻¹)
        (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
      = whiteTransportOp κ hκ hKc q :=
  transportOp_inv_inv (whiteTheta κ hκ hKc q) (whiteMetric κ hκ hKc q)
    (whiteMetricInv κ hκ hKc q)

/-- **The R/6-supplier preservation pin**: the transported coefficient family of the corrected
    ansatz's matched conjugation IS the banked `whiteCoeffs` — `û₁` (and its labelled diagonal
    value `R/6`) is untouched by F1. -/
theorem whiteCoeffsC_matched (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) :
    transportCoeff (transportOp (fun y => (whiteThetaC κ hκ hKc q y)⁻¹)
        (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q))
      = whiteCoeffs κ hκ hKc q := by
  rw [whiteThetaC_matched_op]
  rfl

/-- **★ THE CORRECTED ORDER-1 WHITENED WITNESS (chart side)** —
    `W₁'(τ,x) = √det g^κ(q) · G_τ(x)·Θ̂'(x)^{−1/2}·(û₀(x) + τ·û₁(x))` : the order-1 parametrix
    ansatz at the INVERTED weight `Θ̂' = (whiteTheta)⁻¹` with the UNCHANGED banked transported
    coefficients.  (Built on `heatParametrix` directly: `heatParametrixFn` hardwires the OLD
    fold `Θ = vanVleck G` — flagged in the agnosticism audit.) -/
noncomputable def whiteChartKernel1' (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) : ℝ → Point n → ℝ :=
  fun τ x => Real.sqrt (Matrix.det (curvedRNCMetric κ q))
    * heatParametrix 1 (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) τ x

/-- The explicit product form of the corrected witness: the amplitude is
    `((whiteTheta)⁻¹)^{−1/2}·(1 + û₁·τ)` — same `û₁`, inverted fold. -/
theorem whiteChartKernel1'_apply (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (τ : ℝ) (x : Point n) :
    whiteChartKernel1' κ hκ hKc q τ x
      = Real.sqrt (Matrix.det (curvedRNCMetric κ q))
        * (gaussDdim τ x * ((whiteTheta κ hκ hKc q x)⁻¹) ^ (-(1 : ℝ) / 2)
            * (1 + whiteU1 κ hκ hKc q x * τ)) := by
  unfold whiteChartKernel1' heatParametrix
  have hsum : (∑ k ∈ Finset.range (1 + 1), whiteCoeffs κ hκ hKc q k x * τ ^ k)
      = 1 + whiteU1 κ hκ hKc q x * τ := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : whiteCoeffs κ hκ hKc q 0 x = 1 := by
      unfold whiteCoeffs
      rw [transportCoeff_zero]
    rw [h0]
    simp only [pow_zero, pow_one, one_mul]
    rfl
  rw [hsum]
  rfl

/-- **The diagonal `a₁` CARRIER at the CORRECTED witness (labelled).**  At the chart centre the
    corrected fold is `1` (`Θ̂'(0) = 1⁻¹ = 1`), so GIVEN the labelled DeWitt normalization
    `û₁(0) = R/6` (NOT derived — the SAME banked `whiteU1`, preserved by `whiteCoeffsC_matched`):
        `W₁'(t,0) = √det g^κ(q) · (4πt)^{−n/2}·(1 + (R/6)·t)`
    — the F1 fold inversion does NOT disturb the diagonal carrier. -/
theorem whiteChartKernel1'_diagonal_a1 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (t R : ℝ)
    (hu1 : whiteU1 κ hκ hKc q (0 : Point n) = R / 6) :
    whiteChartKernel1' κ hκ hKc q t (0 : Point n)
      = Real.sqrt (Matrix.det (curvedRNCMetric κ q))
        * ((heatKernel1D t 0) ^ n * (1 + R / 6 * t)) := by
  unfold whiteChartKernel1'
  have hΘ : whiteThetaC κ hκ hKc q (0 : Point n) = 1 := by
    show (whiteTheta κ hκ hKc q (0 : Point n))⁻¹ = 1
    rw [show whiteTheta κ hκ hKc q (0 : Point n) = 1 from
      vanVleck_zero _ (whiteMetric_det_center κ hκ hKc q hq), inv_one]
  rw [heatParametrix_diagonal_a1 1 _ _ t R hΘ le_rfl
    (by unfold whiteCoeffs; rw [transportCoeff_zero]) hu1]
  simp

/-- **Gate — the corrected order-1 whitened witness is genuinely NONZERO at the curved data**
    (`n = 2`, `κ = −1`, `K = B̄(0,2)`, row `q = 0`, chart centre) — the F1 inversion does not
    collapse the witness. -/
theorem whiteChartKernel1'_ne_zero_gate :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      whiteChartKernel1' (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2) (0 : Point 2) τ (0 : Point 2) ≠ 0 := by
  have hq : (0 : Point 2) ∈ Metric.closedBall (0 : Point 2) 2 :=
    Metric.mem_closedBall_self (by norm_num)
  set c : ℝ := whiteU1 (-1 : ℝ) (by norm_num)
    (isCompact_closedBall (0 : Point 2) 2) (0 : Point 2) (0 : Point 2) with hcdef
  refine ⟨1 / (1 + |c|), by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]
    linarith [abs_nonneg c]
  · set τ : ℝ := 1 / (1 + |c|) with hτdef
    have hτ0 : 0 < τ := by rw [hτdef]; positivity
    have hamp : 0 < 1 + c * τ := by
      have h1 : |c| * τ < 1 := by
        rw [hτdef, mul_one_div, div_lt_one (by positivity)]
        linarith [abs_nonneg c]
      have h2 : -(|c| * τ) ≤ c * τ := by
        have := neg_abs_le (c * τ)
        rwa [abs_mul, abs_of_pos hτ0] at this
      linarith
    rw [whiteChartKernel1'_apply]
    have hdet : 0 < Real.sqrt (Matrix.det (curvedRNCMetric (-1 : ℝ) (0 : Point 2))) :=
      Real.sqrt_pos.mpr (curvedRNCMetric_det_pos (-1 : ℝ) (by norm_num) (0 : Point 2))
    have hG : 0 < gaussDdim τ (0 : Point 2) := gaussDdim_pos τ hτ0 _
    have hΘ : whiteTheta (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2) (0 : Point 2) (0 : Point 2) = 1 :=
      vanVleck_zero _ (whiteMetric_det_center (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2) (0 : Point 2) hq)
    rw [hΘ, inv_one, Real.one_rpow]
    have hpos : 0 < Real.sqrt (Matrix.det (curvedRNCMetric (-1 : ℝ) (0 : Point 2)))
        * (gaussDdim τ (0 : Point 2) * 1 * (1 + c * τ)) := by
      apply mul_pos hdet
      rw [mul_one]
      exact mul_pos hG hamp
    exact ne_of_gt hpos

/-! ### §5. ★ h0 AND h1 ARE THEOREMS at the corrected whitened witness. -/

/-- **★ `white_h0_corrected` — the k = 0 off-diagonal DeWitt transport equation is a THEOREM at
    the corrected witness**: given the whitened Gauss set at `x` + the Jacobi-bridge analytic
    legs (entrywise `PdiffAt`, pointwise right inverse, det positivity), `K₀ = 0`.  The J4-642
    labelled `hamp` is DISCHARGED by `radialDeriv_correctedFold` (§2). -/
theorem white_h0_corrected (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (x : Point n)
    (hsym : ∀ i j, whiteMetricInv κ hκ hKc q x i j = whiteMetricInv κ hκ hKc q x j i)
    (hGauss : ∀ i, (∑ j, (whiteMetricInv κ hκ hKc q x i j
        - (if i = j then (1 : ℝ) else 0)) * x j) = 0)
    (hdGauss : ∀ i j, (∑ a, x a * pd (fun y => whiteMetric κ hκ hKc q y a j) i x)
        = (if i = j then (1 : ℝ) else 0) - whiteMetric κ hκ hKc q x i j)
    (htr : (∑ i, ∑ j, whiteMetricInv κ hκ hKc q x i j * whiteMetric κ hκ hKc q x i j)
        = (n : ℝ))
    (hd : ∀ (a i j : Fin n), PdiffAt (fun y => whiteMetric κ hκ hKc q y i j) a x)
    (hinv : ∀ i j, (∑ k, whiteMetric κ hκ hKc q x i k * whiteMetricInv κ hκ hKc q x k j)
        = if i = j then (1 : ℝ) else 0)
    (hdet0 : ∀ y, 0 ≤ Matrix.det (whiteMetric κ hκ hKc q y))
    (hdetx : 0 < Matrix.det (whiteMetric κ hκ hKc q x)) :
    totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
      (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0 := by
  refine totalRadialO1_coeff_corrected_vanishes _ _ _ _ x hsym hGauss hdGauss htr ?_
  have hfold : foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 0
      = fun y => ((vanVleck (whiteMetric κ hκ hKc q) y)⁻¹) ^ (-(1 : ℝ) / 2) := by
    funext y
    show (whiteThetaC κ hκ hKc q y) ^ (-(1 : ℝ) / 2) * whiteCoeffs κ hκ hKc q 0 y = _
    have h0 : whiteCoeffs κ hκ hKc q 0 y = 1 := by
      unfold whiteCoeffs
      rw [transportCoeff_zero]
    rw [h0, mul_one]
    rfl
  rw [hfold]
  exact radialDeriv_correctedFold (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) x
    hd hsym hinv hdet0 hdetx

/-- **★★ `white_h1_corrected` — the k = 1 transport equation is a THEOREM at the corrected
    witness**: with the fold direction matched, the banked radial ODE
    (`transportCoeff_succ_transport_eq`) cancels `K₁` exactly (the J4-642 §4 identification),
    with the matched operator being the BANKED `whiteTransportOp` (`transportOp_inv_inv`).
    Residual inputs: the Gauss set + Jacobi legs (as h0) + `û₁` differentiability + source
    smoothness (regularity legs — Jet-5 territory). -/
theorem white_h1_corrected (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (x : Point n)
    (hsym : ∀ i j, whiteMetricInv κ hκ hKc q x i j = whiteMetricInv κ hκ hKc q x j i)
    (hGauss : ∀ i, (∑ j, (whiteMetricInv κ hκ hKc q x i j
        - (if i = j then (1 : ℝ) else 0)) * x j) = 0)
    (hdGauss : ∀ i j, (∑ a, x a * pd (fun y => whiteMetric κ hκ hKc q y a j) i x)
        = (if i = j then (1 : ℝ) else 0) - whiteMetric κ hκ hKc q x i j)
    (htr : (∑ i, ∑ j, whiteMetricInv κ hκ hKc q x i j * whiteMetric κ hκ hKc q x i j)
        = (n : ℝ))
    (hd : ∀ (a i j : Fin n), PdiffAt (fun y => whiteMetric κ hκ hKc q y i j) a x)
    (hinv : ∀ i j, (∑ k, whiteMetric κ hκ hKc q x i k * whiteMetricInv κ hκ hKc q x k j)
        = if i = j then (1 : ℝ) else 0)
    (hdet : ∀ y, 0 < Matrix.det (whiteMetric κ hκ hKc q y))
    (hu1d : ∀ i, PdiffAt (whiteCoeffs κ hκ hKc q 1) i x)
    (hsm : ContDiff ℝ ⊤ (whiteTransportOp κ hκ hKc q (whiteCoeffs κ hκ hKc q 0))) :
    totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
      (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0 := by
  have hΘpos : ∀ y, 0 < whiteThetaC κ hκ hKc q y := by
    intro y
    show 0 < (whiteTheta κ hκ hKc q y)⁻¹
    have hpos : 0 < whiteTheta κ hκ hKc q y := by
      show 0 < (Real.sqrt (Matrix.det (whiteMetric κ hκ hKc q y)))⁻¹
      exact inv_pos.mpr (Real.sqrt_pos.mpr (hdet y))
    exact inv_pos.mpr hpos
  have haa : ∀ i, PdiffAt (fun y => (whiteThetaC κ hκ hKc q y) ^ (-(1 : ℝ) / 2)) i x := by
    intro i
    have hfun : (fun y => (whiteThetaC κ hκ hKc q y) ^ (-(1 : ℝ) / 2))
        = fun y => (Matrix.det (whiteMetric κ hκ hKc q y)) ^ (-(1 : ℝ) / 4) :=
      correctedFold_eq_det_rpow (whiteMetric κ hκ hKc q) (fun y => (hdet y).le)
    rw [hfun]
    have hslice := det_slice_hasDerivAt (whiteMetric κ hκ hKc q) x i (hd i)
    have hne : Matrix.det (Matrix.of (whiteMetric κ hκ hKc q
        (Function.update x i (x i)))) ≠ 0 := by
      rw [Function.update_eq_self]
      exact (hdet x).ne'
    exact (hslice.rpow_const (p := (-(1 : ℝ) / 4)) (Or.inl hne)).differentiableAt
  have hamp : radialDeriv (fun y => (whiteThetaC κ hκ hKc q y) ^ (-(1 : ℝ) / 2)) x
      = -((1 / 4) * radialLogDetSym (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) x
          * (whiteThetaC κ hκ hKc q x) ^ (-(1 : ℝ) / 2)) :=
    radialDeriv_correctedFold (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) x
      hd hsym hinv (fun y => (hdet y).le) (hdet x)
  have hCo := whiteCoeffsC_matched κ hκ hKc q
  have hOp := whiteThetaC_matched_op κ hκ hKc q
  have hu1d' : ∀ i, PdiffAt (transportCoeff (transportOp
      (fun y => (whiteThetaC κ hκ hKc q y)⁻¹)
      (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)) 1) i x := by
    rw [hCo]
    exact hu1d
  have hsm' : ContDiff ℝ ⊤ (transportOp (fun y => (whiteThetaC κ hκ hKc q y)⁻¹)
      (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
      (transportCoeff (transportOp (fun y => (whiteThetaC κ hκ hKc q y)⁻¹)
        (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)) 0)) := by
    rw [hCo, hOp]
    exact hsm
  have h := totalRadialO1_coeff_level1_transportCoeff_vanishes
    (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q) (whiteThetaC κ hκ hKc q) x
    hsym hGauss hdGauss htr hΘpos haa hu1d' hamp hsm'
  rw [hCo] at h
  exact h

/-! ### §6. The corrected gated defect and the re-derived K1 budget. -/

/-- The gated order-1 defect kernel at the CORRECTED witness (window × the already-computed
    N = 1 residual at the inverted weight; same gating as the banked `whiteDefect1`). -/
noncomputable def whiteDefect1' (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (r₀ : ℝ) : ℝ → Point n → Point n → ℝ :=
  fun s x _ => if 0 < s ∧ s ≤ 1 ∧ ‖x‖ < r₀ then
    parametrixResidualN 1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
      (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) s x
    else 0

/-- **★ The linear-gain column bound at the corrected witness, with h0/h1/hamp/htr DISCHARGED.**
    Inputs are now: the geometric whitened-Gauss residue {hsymI, hgsym, hGauss, hdGauss, hinv,
    hdet} + the regularity legs {hwsm, hd, hu1d, hsm, hΔ}.  The `s`-linearity is the banked
    J4-636 cancellation (fold-agnostic); the two transport equations are supplied by §5. -/
theorem whiteDefect1'_linear_gain (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (r₀ w C_Δ : ℝ) (hw1 : 1 ≤ w) (hCΔ : 0 ≤ C_Δ)
    (hwsm : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) k))
    (hdet : ∀ y, 0 < Matrix.det (whiteMetric κ hκ hKc q y))
    (hsymI : ∀ x : Point n, ‖x‖ < r₀ → ∀ i j,
      whiteMetricInv κ hκ hKc q x i j = whiteMetricInv κ hκ hKc q x j i)
    (hGauss : ∀ x : Point n, ‖x‖ < r₀ → ∀ i,
      (∑ j, (whiteMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)) * x j) = 0)
    (hdGauss : ∀ x : Point n, ‖x‖ < r₀ → ∀ i j,
      (∑ a, x a * pd (fun y => whiteMetric κ hκ hKc q y a j) i x)
        = (if i = j then (1 : ℝ) else 0) - whiteMetric κ hκ hKc q x i j)
    (hd : ∀ x : Point n, ‖x‖ < r₀ → ∀ (a i j : Fin n),
      PdiffAt (fun y => whiteMetric κ hκ hKc q y i j) a x)
    (hinv : ∀ x : Point n, ‖x‖ < r₀ → ∀ i j,
      (∑ k, whiteMetric κ hκ hKc q x i k * whiteMetricInv κ hκ hKc q x k j)
        = if i = j then (1 : ℝ) else 0)
    (hgsym : ∀ x : Point n, ‖x‖ < r₀ → ∀ i j,
      whiteMetric κ hκ hKc q x i j = whiteMetric κ hκ hKc q x j i)
    (hu1d : ∀ x : Point n, ‖x‖ < r₀ → ∀ i, PdiffAt (whiteCoeffs κ hκ hKc q 1) i x)
    (hsm : ContDiff ℝ ⊤ (whiteTransportOp κ hκ hKc q (whiteCoeffs κ hκ hKc q 0)))
    (hΔ : ∀ x : Point n, ‖x‖ < r₀ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ) :
    ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |whiteDefect1' κ hκ hKc q r₀ s p 0|
        ≤ (Real.sqrt w ^ n * C_Δ) * (s * gaussDdim (w * s) (p - 0)) := by
  intro s p hs hs1
  rw [sub_zero]
  have hG0 : 0 ≤ gaussDdim (w * s) p := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  by_cases hp : ‖p‖ < r₀
  · have htr : (∑ i, ∑ j, whiteMetricInv κ hκ hKc q p i j
        * whiteMetric κ hκ hKc q p i j) = (n : ℝ) :=
      htr_of_inv_symm _ _ p (hinv p hp) (hgsym p hp)
    have h0 : totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) p = 0 :=
      white_h0_corrected κ hκ hKc q p (hsymI p hp) (hGauss p hp) (hdGauss p hp) htr
        (hd p hp) (hinv p hp) (fun y => (hdet y).le) (hdet p)
    have h1 : totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q)
        (whiteMetricInv κ hκ hKc q) (whiteThetaC κ hκ hKc q)
        (whiteCoeffs κ hκ hKc q) p = 0 :=
      white_h1_corrected κ hκ hKc q p (hsymI p hp) (hGauss p hp) (hdGauss p hp) htr
        (hd p hp) (hinv p hp) hdet (hu1d p hp) hsm
    have hval : whiteDefect1' κ hκ hKc q r₀ s p (0 : Point n)
        = parametrixResidualN 1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
            (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) s p := by
      unfold whiteDefect1'
      rw [if_pos ⟨hs, hs1, hp⟩]
    rw [hval, parametrixResidual_N1_linear_gain _ _ _ _ s hs p hwsm
      (hGauss p hp) h0 h1, abs_neg]
    have hGs : 0 < gaussDdim s p := gaussDdim_pos s hs p
    have hwid : gaussDdim s p ≤ Real.sqrt w ^ n * gaussDdim (w * s) p := by
      have h := gaussDdim_le_of_width_le 1 w one_pos hw1 (τ := s) hs p
      rwa [one_mul, div_one] at h
    calc |s * gaussDdim s p
          * laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
              (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) p|
        = s * gaussDdim s p
          * |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
              (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) p| := by
          rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hGs]
      _ ≤ s * gaussDdim s p * C_Δ := by
          exact mul_le_mul_of_nonneg_left (hΔ p hp) (mul_nonneg hs.le hGs.le)
      _ ≤ s * (Real.sqrt w ^ n * gaussDdim (w * s) p) * C_Δ := by
          have := mul_le_mul_of_nonneg_left hwid hs.le
          exact mul_le_mul_of_nonneg_right this hCΔ
      _ = (Real.sqrt w ^ n * C_Δ) * (s * gaussDdim (w * s) p) := by ring
  · have hval : whiteDefect1' κ hκ hKc q r₀ s p (0 : Point n) = 0 := by
      unfold whiteDefect1'
      rw [if_neg (fun h => hp h.2.2)]
    rw [hval, abs_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hCΔ)
      (mul_nonneg hs.le hG0)

/-- **★★ `white_K1BudgetW_corrected` — the RE-DERIVED k = 1 `t²` budget at the CORRECTED
    witness: h0, h1, hamp, htr are GONE from the input list.**  Remaining inputs (the honest
    post-F1 K1 residue): the whitened-Gauss geometric legs {hsymI, hgsym, hGauss (banked
    supplier: `whiteGauss_discharged`, fold-free), hdGauss (derivable via
    `hdGauss_of_metric_gauss` from the banked pointwise Gauss), hinv, hdet} + the regularity
    legs {hwsm, hd, hu1d, hsm, hΔ} (Jet-5 territory; corrected-fold re-instantiation of the
    J4-640/641 dischargers owed).  ⚠ CONDITIONAL on those; NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_corrected (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (r₀ w C_Δ : ℝ) (hw2 : 2 ≤ w) (hCΔ : 0 ≤ C_Δ)
    (hwsm : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) k))
    (hdet : ∀ y, 0 < Matrix.det (whiteMetric κ hκ hKc q y))
    (hsymI : ∀ x : Point n, ‖x‖ < r₀ → ∀ i j,
      whiteMetricInv κ hκ hKc q x i j = whiteMetricInv κ hκ hKc q x j i)
    (hGauss : ∀ x : Point n, ‖x‖ < r₀ → ∀ i,
      (∑ j, (whiteMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)) * x j) = 0)
    (hdGauss : ∀ x : Point n, ‖x‖ < r₀ → ∀ i j,
      (∑ a, x a * pd (fun y => whiteMetric κ hκ hKc q y a j) i x)
        = (if i = j then (1 : ℝ) else 0) - whiteMetric κ hκ hKc q x i j)
    (hd : ∀ x : Point n, ‖x‖ < r₀ → ∀ (a i j : Fin n),
      PdiffAt (fun y => whiteMetric κ hκ hKc q y i j) a x)
    (hinv : ∀ x : Point n, ‖x‖ < r₀ → ∀ i j,
      (∑ k, whiteMetric κ hκ hKc q x i k * whiteMetricInv κ hκ hKc q x k j)
        = if i = j then (1 : ℝ) else 0)
    (hgsym : ∀ x : Point n, ‖x‖ < r₀ → ∀ i j,
      whiteMetric κ hκ hKc q x i j = whiteMetric κ hκ hKc q x j i)
    (hu1d : ∀ x : Point n, ‖x‖ < r₀ → ∀ i, PdiffAt (whiteCoeffs κ hκ hKc q 1) i x)
    (hsm : ContDiff ℝ ⊤ (whiteTransportOp κ hκ hKc q (whiteCoeffs κ hκ hKc q 0)))
    (hΔ : ∀ x : Point n, ‖x‖ < r₀ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ)
    (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ) (hCH : 0 ≤ C_H)
    (hH : ∀ (a : ℝ) (ζ : Point n), 0 < a →
      |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ))
    (hH0 : ∀ ζ : Point n, H 0 0 ζ = 0) :
    K1TransportBudgetW w H (whiteDefect1' κ hκ hKc q r₀) := by
  have hw1 : (1 : ℝ) ≤ w := le_trans one_le_two hw2
  exact k1BudgetW_of_pointwise_linear_gain w hw2 (whiteDefect1' κ hκ hKc q r₀)
    (Real.sqrt w ^ n * C_Δ)
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hCΔ)
    (whiteDefect1'_linear_gain κ hκ hKc q r₀ w C_Δ hw1 hCΔ hwsm hdet hsymI hGauss
      hdGauss hd hinv hgsym hu1d hsm hΔ)
    H C_H hCH hH hH0

/-- The corrected budget at the CONCRETE Gaussian `H`-witness (`n = 2`, `w = 8`, banked
    `frozenK2Sharp_H_witness`): the H-side hypotheses are discharged; only the post-F1
    geometric + regularity residue remains.  NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_corrected_concreteH (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point 2)}
    (hKc : IsCompact Kset) (q : Point 2) (r₀ C_Δ : ℝ) (hCΔ : 0 ≤ C_Δ)
    (hwsm : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) k))
    (hdet : ∀ y, 0 < Matrix.det (whiteMetric κ hκ hKc q y))
    (hsymI : ∀ x : Point 2, ‖x‖ < r₀ → ∀ i j,
      whiteMetricInv κ hκ hKc q x i j = whiteMetricInv κ hκ hKc q x j i)
    (hGauss : ∀ x : Point 2, ‖x‖ < r₀ → ∀ i,
      (∑ j, (whiteMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)) * x j) = 0)
    (hdGauss : ∀ x : Point 2, ‖x‖ < r₀ → ∀ i j,
      (∑ a, x a * pd (fun y => whiteMetric κ hκ hKc q y a j) i x)
        = (if i = j then (1 : ℝ) else 0) - whiteMetric κ hκ hKc q x i j)
    (hd : ∀ x : Point 2, ‖x‖ < r₀ → ∀ (a i j : Fin 2),
      PdiffAt (fun y => whiteMetric κ hκ hKc q y i j) a x)
    (hinv : ∀ x : Point 2, ‖x‖ < r₀ → ∀ i j,
      (∑ k, whiteMetric κ hκ hKc q x i k * whiteMetricInv κ hκ hKc q x k j)
        = if i = j then (1 : ℝ) else 0)
    (hgsym : ∀ x : Point 2, ‖x‖ < r₀ → ∀ i j,
      whiteMetric κ hκ hKc q x i j = whiteMetric κ hκ hKc q x j i)
    (hu1d : ∀ x : Point 2, ‖x‖ < r₀ → ∀ i, PdiffAt (whiteCoeffs κ hκ hKc q 1) i x)
    (hsm : ContDiff ℝ ⊤ (whiteTransportOp κ hκ hKc q (whiteCoeffs κ hκ hKc q 0)))
    (hΔ : ∀ x : Point 2, ‖x‖ < r₀ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteThetaC κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ) :
    K1TransportBudgetW 8 (fun a _ ζ => gaussDdim (2 * a) ((0 : Point 2) - ζ))
      (whiteDefect1' κ hκ hKc q r₀) := by
  have hW := QIQTH.FrozenK2Sharp.frozenK2Sharp_H_witness (n := 2) (by norm_num)
  exact white_K1BudgetW_corrected κ hκ hKc q r₀ 8 C_Δ (by norm_num) hCΔ
    hwsm hdet hsymI hGauss hdGauss hd hinv hgsym hu1d hsm hΔ
    (fun a _ ζ => gaussDdim (2 * a) ((0 : Point 2) - ζ)) 1 zero_le_one
    (fun a ζ ha => hW.1 a ζ ha) (fun ζ => hW.2.1 ζ)

/-- **Fold-free provenance pin for `hGauss`**: the J4-641 discharge `whiteGauss_discharged`
    mentions NO ansatz weight — it supplies the corrected budget's `hGauss` input VERBATIM
    (`whiteMetricInv` is definitionally `whitePullbackMetricInv`). -/
theorem white_hGauss_supplier_foldfree (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) :
    ∃ r₀ > (0 : ℝ), ∀ x : Point n, ‖x‖ < r₀ → ∀ i : Fin n,
      (∑ j, (whiteMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)) * x j) = 0 :=
  whiteGauss_discharged κ hκ hKc q hq

/-! ### §7. Non-vacuity gates for the Jacobi bridge (cp466 discipline) — at the CURVED
exponential witness `gW = diag(1, e^{2(y₀−1)})`, `vW = (1,0)` of J4-642 (`ρ = 2 ≠ 0`). -/

/-- Entrywise partial differentiability of the gate metric at the gate point. -/
lemma gW_pdiffAt : ∀ (a i j : Fin 2), PdiffAt (fun y => gW y i j) a vW := by
  intro a i j
  by_cases h : i = 1 ∧ j = 1
  · obtain ⟨hi, hj⟩ := h
    subst hi
    subst hj
    show DifferentiableAt ℝ (fun t => gW (Function.update vW a t) 1 1) (vW a)
    have hfun : (fun t : ℝ => gW (Function.update vW a t) 1 1)
        = fun t => Real.exp (2 * ((Function.update vW a t) 0 - 1)) := by
      funext t
      rw [gW_11]
    rw [hfun]
    by_cases ha : a = 0
    · subst ha
      have hupd : (fun t : ℝ => Real.exp (2 * ((Function.update vW 0 t) 0 - 1)))
          = fun t => Real.exp (2 * (t - 1)) := by
        funext t
        simp [Function.update_apply]
      rw [hupd]
      exact (((hasDerivAt_id (vW 0)).sub_const 1).const_mul 2).exp.differentiableAt
    · have ha1 : a = 1 := Fin.eq_one_of_ne_zero a ha
      subst ha1
      have hupd : (fun t : ℝ => Real.exp (2 * ((Function.update vW 1 t) 0 - 1)))
          = fun _ : ℝ => Real.exp (2 * (vW 0 - 1)) := by
        funext t
        simp [Function.update_apply]
      rw [hupd]
      exact differentiableAt_const _
  · show DifferentiableAt ℝ (fun t => gW (Function.update vW a t) i j) (vW a)
    have hfun : (fun t : ℝ => gW (Function.update vW a t) i j)
        = fun _ : ℝ => if i = j then (1 : ℝ) else 0 := by
      funext t
      simp only [gW]
      rw [if_neg h]
    rw [hfun]
    exact differentiableAt_const _

/-- The gate inverse identity at the gate point: `Σₖ gW(v)ᵢₖ·giW(v)ₖⱼ = δᵢⱼ`. -/
lemma gW_inv_at_vW : ∀ i j : Fin 2,
    (∑ k, gW vW i k * giW vW k j) = if i = j then (1 : ℝ) else 0 := by
  intro i j
  simp only [Fin.sum_univ_two, gW_at_vW, giW_at_vW]
  fin_cases i <;> fin_cases j <;> simp

/-- `det gW ≥ 0` everywhere (indeed `> 0`). -/
lemma det_gW_nonneg (y : Point 2) : 0 ≤ Matrix.det (gW y) := by
  rw [det_gW]
  exact (Real.exp_pos _).le

/-- `det gW(vW) = 1 > 0`. -/
lemma det_gW_at_vW_pos : 0 < Matrix.det (gW vW) := by
  rw [det_gW]
  exact Real.exp_pos _

/-- **The DIRECT computation** — `r∂_r log det gW (vW) = 2` by hand
    (`log det gW = 2(y₀ − 1)`): the independent cross-check value for the bridge gate. -/
theorem gate_logDet_direct :
    radialDeriv (fun y => Real.log (Matrix.det (gW y))) vW = 2 := by
  have hfun : (fun y : Point 2 => Real.log (Matrix.det (gW y)))
      = fun y => 2 * (y 0 - 1) := by
    funext y
    rw [det_gW, Real.log_exp]
  rw [hfun]
  unfold radialDeriv
  simp only [Fin.sum_univ_two, vW_zero, vW_one, one_mul, zero_mul, add_zero]
  have hupd : (fun t : ℝ => 2 * ((Function.update vW 0 t) 0 - 1))
      = fun t : ℝ => 2 * (t - 1) := by
    funext t
    simp [Function.update_apply]
  have hder : HasDerivAt (fun t : ℝ => 2 * (t - 1)) 2 1 := by
    simpa using ((hasDerivAt_id (1 : ℝ)).sub_const 1).const_mul 2
  simp only [pd, vW_zero, hupd]
  rw [hder.deriv]

/-- **★ GATE J — THE JACOBI BRIDGE FIRES AT CURVED DATA**: at the exponential witness the
    bridge instantiates (all hypotheses genuinely satisfied) and gives
    `r∂_r log det gW (vW) = ρ(vW)`. -/
theorem gate_jacobi_bridge :
    radialDeriv (fun y => Real.log (Matrix.det (gW y))) vW = radialLogDetSym gW giW vW :=
  radial_logDet_eq_rho gW giW vW gW_pdiffAt (gate_gauss_hyps.1) gW_inv_at_vW

/-- **GATE J′ — two independent routes agree at a NONZERO value**: the Jacobi-bridge route and
    the direct computation both give `2 ≠ 0` (a flat witness would give `0` — the gate
    genuinely exercises the curved content of the bridge). -/
theorem gate_jacobi_bridge_value :
    radialLogDetSym gW giW vW = 2
      ∧ radialDeriv (fun y => Real.log (Matrix.det (gW y))) vW = 2
      ∧ (2 : ℝ) ≠ 0 :=
  ⟨gate_rho_eq_two, gate_jacobi_bridge.trans gate_rho_eq_two, by norm_num⟩

/-- **★ GATE M — THE DISCHARGE MACHINERY END-TO-END AT CURVED DATA**: the corrected-fold
    `K₀ = 0` at the exponential witness re-derived THROUGH the hamp-discharge path
    (`totalRadialO1_coeff_corrected_vanishes` + `radialDeriv_correctedFold` + the Jacobi
    bridge) — NO explicit exponential computation.  Cross-checks the banked explicit
    `gate_corrected_h0_vanishes` (same statement, independent route). -/
theorem gate_corrected_h0_jacobi_route :
    totalRadialO1_coeff gW giW (fun y => (vanVleck gW y)⁻¹)
      (transportCoeff (transportOp (vanVleck gW) gW giW)) vW = 0 := by
  obtain ⟨hsym, hGauss, hdGauss, htr⟩ := gate_gauss_hyps
  refine totalRadialO1_coeff_corrected_vanishes gW giW _ _ vW hsym hGauss hdGauss htr ?_
  have hfold : foldedCoeff (fun y => (vanVleck gW y)⁻¹)
      (transportCoeff (transportOp (vanVleck gW) gW giW)) 0
      = fun y => ((vanVleck gW y)⁻¹) ^ (-(1 : ℝ) / 2) := by
    funext y
    show ((vanVleck gW y)⁻¹) ^ (-(1 : ℝ) / 2)
        * transportCoeff (transportOp (vanVleck gW) gW giW) 0 y = _
    rw [transportCoeff_zero]
    simp
  rw [hfold]
  exact radialDeriv_correctedFold gW giW vW gW_pdiffAt hsym gW_inv_at_vW
    det_gW_nonneg det_gW_at_vW_pos

end QIQTH.WhiteF1

-- std-3 verification (chk): READ these outputs — no sorryAx, no extra axioms.
#print axioms QIQTH.WhiteF1.metric_slice_hasDerivAt
#print axioms QIQTH.WhiteF1.det_slice_hasDerivAt
#print axioms QIQTH.WhiteF1.pd_logDet_eq
#print axioms QIQTH.WhiteF1.radial_logDet_eq_rho
#print axioms QIQTH.WhiteF1.correctedFold_eq_det_rpow
#print axioms QIQTH.WhiteF1.radialDeriv_correctedFold
#print axioms QIQTH.WhiteF1.htr_of_inv_symm
#print axioms QIQTH.WhiteF1.hdGauss_of_metric_gauss
#print axioms QIQTH.WhiteF1.whiteThetaC_matched_op
#print axioms QIQTH.WhiteF1.whiteCoeffsC_matched
#print axioms QIQTH.WhiteF1.whiteChartKernel1'_apply
#print axioms QIQTH.WhiteF1.whiteChartKernel1'_diagonal_a1
#print axioms QIQTH.WhiteF1.whiteChartKernel1'_ne_zero_gate
#print axioms QIQTH.WhiteF1.white_h0_corrected
#print axioms QIQTH.WhiteF1.white_h1_corrected
#print axioms QIQTH.WhiteF1.whiteDefect1'_linear_gain
#print axioms QIQTH.WhiteF1.white_K1BudgetW_corrected
#print axioms QIQTH.WhiteF1.white_K1BudgetW_corrected_concreteH
#print axioms QIQTH.WhiteF1.white_hGauss_supplier_foldfree
#print axioms QIQTH.WhiteF1.gate_logDet_direct
#print axioms QIQTH.WhiteF1.gate_jacobi_bridge
#print axioms QIQTH.WhiteF1.gate_jacobi_bridge_value
#print axioms QIQTH.WhiteF1.gate_corrected_h0_jacobi_route
