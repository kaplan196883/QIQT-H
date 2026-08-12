/-
  WhiteOrder1 — J4-636: the ORDER-1 whitened witness — the `u₀ + τ·u₁` transported amplitude,
  its exact N = 1 defect normal form, the transport-equation CANCELLATION to the LINEAR GAIN
  `−t·G·Δ_g w₁`, and the conditional K1 budget through the proved rung.  ONE brick of the
  `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`; proves NOTHING about the coefficient value.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ★ THE DEFINITIONAL READ (J4-636 finding; Sol-confirmed, gpt-5.6-sol high).
  The banked `gatedWitnessN1` amplitude IS already the order-1 transported family:
  `heatParametrixFn 1 G T = G_τ·Θ^{−1/2}·(u₀ + τ·u₁)` with `Θ = vanVleck G`, `u₀ ≡ 1`,
  `u₁ = radialTransportSolve 1 (T u₀)` (`transportCoeff`), `T = transportOp` the DeWitt conjugated
  Laplacian.  The banked general-`N` residual decomposition (`parametrixResidual_offdiag_O1_total`)
  regroups AT `N = 1` into FOUR `t`-layers (proved here, §1):
      Res₁ = (1/t²)·G·B·w₀ + (1/t)·G·(K₀ + B·w₁) + G·K₁ − t·G·Δ_g w₁ ,
  with `B = −¼Σ(gⁱʲ−δ)vⁱvʲ`, `K₀ = totalRadialO1_coeff` (the k = 0 off-diagonal DeWitt transport
  coefficient, banked) and `K₁ = totalRadialO1_coeff_level1` (the k = 1 coefficient, NEW here).
  THE CANCELLATION (§2): given the radial compatibility (Gauss lemma) `Σⱼ(gⁱʲ−δ)vʲ = 0` (kills
  `B`), `K₀ = 0` and `K₁ = 0` (the two off-diagonal transport equations), the ENTIRE singular +
  `O(1)` content vanishes and
      Res₁ = −t·G_t(v)·Δ_g w₁(v)      — ★ THE LINEAR GAIN, exact.
  §3 instantiates at the whitened chart data: the order-1 whitened witness `whiteChartKernel1` /
  `whiteAmbientKernel1` (the J4-635-mandated fix: `p`-DEPENDENT transported `u₁`, not a `q`-only
  `1+τc₁`), the gated defect kernel `whiteDefect1` (window × the already-computed residual — NOT
  the residual of a windowed kernel), the linear-gain column bound
      `|E₁(s,p,0)| ≤ (√wⁿ·C_Δ)·s·G_{ws}(p)`      — the EXACT antecedent of the proved K1 rung —
  and `white_K1BudgetW_of_transport`: the k = 1 `t²` budget `K1TransportBudgetW`, conditional on
  the FOUR labelled transport hypotheses {hGauss, h0, h1, hΔ} + coefficient smoothness.
  §4 gates: (i) ★ ANTECEDENT INHABITANCE (cp466 discipline): {hw, hGauss, h0, h1} are JOINTLY
  satisfiable at the flat data (g = δ, Θ ≡ 1, u = (1,0,0,…)) — consistency, NOT curved
  applicability; the residual there provably vanishes THROUGH the cancellation theorem;
  (ii) the order-1 witness kernel is genuinely NONZERO at the curved κ = −1 whitened data;
  (iii) the diagonal `a₁` CARRIER: `whiteChartKernel1(t,0) = √det g^κ(q)·pref·(1 + (R/6)t)` GIVEN
  the labelled `u₁(0) = R/6` — the amplitude CARRIES the coefficient; it is NOT derived here.

  ⚠ HONEST SCOPE (binding).
    • `hGauss` (radial compatibility of `ĝ⁻¹` in the whitened chart) is TRUE mathematically
      (the Gauss lemma transports along the LINEAR whitening: `ĝ(w)w = Eᵀg̃(Ew)Ew = Eᵀg̃(0)Ew
      = ĝ(0)w = w`) but is NOT yet a library theorem — carried as a labelled hypothesis.
    • `h0` (the k = 0 off-diagonal transport equation `totalRadialO1_coeff = 0`) is the
      CHECKPOINTED identity of ParametrixResidualO1Total (representation mismatch: radial-Ricci
      facts live in the expMap rep, the symbols in the (g,Γ) rep) — carried, not proved.
    • `h1` (the k = 1 equation `totalRadialO1_coeff_level1 = 0`): per the Sol audit this does
      NOT follow from the banked transport ODE `(1 + r∂_r)u₁ = T u₀` without an additional
      conjugation-direction identification (`L₁ = a·(1+r∂_r)u₁ − Δ_g a`-type unfolding, plus the
      same rep bridge as `h0`) — carried as a genuine labelled hypothesis; NOT claimed derivable.
    • `hΔ` (gate-uniform bound on `Δ_g w₁`) is a regularity input (transport-coefficient second
      derivatives) — carried.
  `a₁ = R/6` remains CONDITIONAL: flat tower closed and non-vacuous; the curved side still owes
  the DISCHARGE of {hGauss, h0, h1, hΔ, hw} at the whitened chart data + the Duhamel-split
  integrability carry + the fat-`K` carrier piles + the capstone co-instantiation at the whitened
  witness + the prior analytic piles.  This brick = the order-1 witness CONSTRUCTION + the exact
  cancellation + the conditional budget wiring.  No axioms, no `sorry`, no `:= True`.
-/
import Mathlib
import QIQTH.ParametrixResidualO1Total
import QIQTH.ParametrixFunction
import QIQTH.HeatTransportRecursion
import QIQTH.WhiteAmbient
import QIQTH.WhiteCapstoneWire
import QIQTH.WidthFree
import QIQTH.FrozenK2Sharp

open Finset Filter Topology MeasureTheory Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatKernelA1 QIQTH.HeatResidualBound QIQTH.LeviSeries
open QIQTH.VanVleck QIQTH.HeatParametrixAnsatz QIQTH.ParametrixFunction
open QIQTH.HeatTransportRecursion
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.WhiteWitness QIQTH.WhiteReplay QIQTH.WhiteOffDiag QIQTH.WhiteAmbient
open QIQTH.WidthFree QIQTH.WhiteCapstoneWire

namespace QIQTH.WhiteOrder1

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### §1. The N = 1 layer regrouping of the banked residual decomposition. -/

/-- **The k = 1 (level-1) off-diagonal DeWitt transport coefficient** — the `t⁰`-layer
    coefficient of the N = 1 parametrix residual (mirror of the banked `totalRadialO1_coeff`
    one level up):
      `K₁ = [½Σ(gⁱⁱ−1) − ½Σ gⁱʲΓᵏᵢⱼvᵏ]·w₁ + w₁ + (r∂_r w₁) + ½Σ(gⁱʲ−δ)(vⁱ∂ⱼw₁+vʲ∂ᵢw₁) − Δ_g w₀`.
    Its vanishing is the k = 1 off-diagonal DeWitt transport equation in folded form. -/
noncomputable def totalRadialO1_coeff_level1 (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (v : Point n) : ℝ :=
  ((1 / 2) * (∑ i, (gi v i i - 1))
      - (1 / 2) * (∑ i, ∑ j, ∑ k, gi v i j * christoffel g gi k i j v * v k))
      * foldedCoeff Θ u 1 v
    + foldedCoeff Θ u 1 v
    + radialDeriv (foldedCoeff Θ u 1) v
    + (1 / 2) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd (foldedCoeff Θ u 1) j v + v j * pd (foldedCoeff Θ u 1) i v))
    - laplaceBeltrami g gi (foldedCoeff Θ u 0) v

/-- **★ The N = 1 residual in exact `t`-layers.**  Regrouping the banked general-`N`
    decomposition (`parametrixResidual_offdiag_O1_total`) at `N = 1` (`P = w₀ + t·w₁`):
        `(∂_t − Δ_g)H₁(t,v) = (1/t²)·G·B·w₀ + (1/t)·G·(K₀ + B·w₁) + G·K₁ − t·G·Δ_g w₁`,
    with `B = −¼Σᵢⱼ(gⁱʲ−δ)vⁱvʲ`, `K₀ = totalRadialO1_coeff`, `K₁ = totalRadialO1_coeff_level1`.
    The only analytic step beyond the banked assembly is the `pd`-split of the two-term
    polynomial (coefficient smoothness `hw`).  NOT `a₁ = R/6`. -/
theorem parametrixResidual_N1_layers (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k)) :
    parametrixResidualN 1 g gi Θ u t v
      = (1 / t ^ 2) * gaussDdim t v
          * ((-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
          * foldedCoeff Θ u 0 v
        + (1 / t) * gaussDdim t v
          * (totalRadialO1_coeff g gi Θ u v
              + (-1 / 4) * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j))
                * foldedCoeff Θ u 1 v)
        + gaussDdim t v * totalRadialO1_coeff_level1 g gi Θ u v
        - t * gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 1) v := by
  have ht' : t ≠ 0 := ne_of_gt ht
  -- the pd-split of the two-term parametrix polynomial
  have hP : ∀ j : Fin n,
      pd (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k) j v
        = pd (foldedCoeff Θ u 0) j v + t * pd (foldedCoeff Θ u 1) j v := by
    intro j
    have hfun : (fun y => ∑ k ∈ Finset.range (1 + 1), foldedCoeff Θ u k y * t ^ k)
        = fun y => foldedCoeff Θ u 0 y + t * foldedCoeff Θ u 1 y := by
      funext y
      rw [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, mul_one]
      ring
    have hd0 : PdiffAt (foldedCoeff Θ u 0) j v := PdiffAt_of_contDiff _ (hw 0) j v
    have hd1 : PdiffAt (foldedCoeff Θ u 1) j v := PdiffAt_of_contDiff _ (hw 1) j v
    have hd1' : PdiffAt (fun y => t * foldedCoeff Θ u 1 y) j v := by
      simp only [PdiffAt] at hd1 ⊢
      exact hd1.const_mul t
    rw [hfun, pd_add _ _ j v hd0 hd1', pd_const_mul t (foldedCoeff Θ u 1) j v hd1]
  rw [parametrixResidual_offdiag_O1_total 1 g gi Θ u t ht v hw]
  simp only [hP]
  -- split the deviation cross-sum into its w₀ and w₁ parts
  have hIV : (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * (pd (foldedCoeff Θ u 0) j v + t * pd (foldedCoeff Θ u 1) j v)
            + v j * (pd (foldedCoeff Θ u 0) i v + t * pd (foldedCoeff Θ u 1) i v)))
      = (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
          * (v i * pd (foldedCoeff Θ u 0) j v + v j * pd (foldedCoeff Θ u 0) i v))
        + t * (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0))
          * (v i * pd (foldedCoeff Θ u 1) j v + v j * pd (foldedCoeff Θ u 1) i v)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hIV]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, mul_one, Nat.cast_zero, Nat.cast_one, Nat.sub_self,
    Nat.zero_sub, mul_zero, add_zero, zero_add]
  unfold totalRadialO1_coeff totalRadialO1_coeff_level1
  field_simp
  ring

/-! ### §2. ★ The cancellation: transport equations ⟹ the LINEAR GAIN. -/

/-- **★★ THE ORDER-1 CANCELLATION — the linear-gain identity.**  GIVEN
    * `hGauss` — the inverse-metric radial compatibility `Σⱼ(gⁱʲ(v)−δⁱʲ)vʲ = 0` (the Gauss-lemma
      face; kills the entire `1/t²` layer `B` and the `(1/t)·B·w₁` cross term),
    * `h0` — the k = 0 off-diagonal DeWitt transport equation `totalRadialO1_coeff v = 0`
      (the CHECKPOINTED identity), and
    * `h1` — the k = 1 equation `totalRadialO1_coeff_level1 v = 0`,
    the FULL N = 1 parametrix residual collapses to the single `O(t)` remainder
        `(∂_t − Δ_g)H₁(t,v) = −t·G_t(v)·Δ_g w₁(v)`
    — the defect of the order-1 witness gains EXACTLY one power of `t` over the order-0 shape
    (the J4-634 RUNG-1 linear-gain mechanism).  All three hypotheses are genuine geometric /
    transport inputs, none is the conclusion.  NOT `a₁ = R/6`. -/
theorem parametrixResidual_N1_linear_gain (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ) (ht : 0 < t) (v : Point n)
    (hw : ∀ k, ContDiff ℝ ⊤ (foldedCoeff Θ u k))
    (hGauss : ∀ i, (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    (h0 : totalRadialO1_coeff g gi Θ u v = 0)
    (h1 : totalRadialO1_coeff_level1 g gi Θ u v = 0) :
    parametrixResidualN 1 g gi Θ u t v
      = -(t * gaussDdim t v * laplaceBeltrami g gi (foldedCoeff Θ u 1) v) := by
  have hB : (∑ i, ∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have hfac : (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * (v i * v j))
        = v i * (∑ j, (gi v i j - (if i = j then (1 : ℝ) else 0)) * v j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hfac, hGauss i, mul_zero]
  rw [parametrixResidual_N1_layers g gi Θ u t ht v hw, hB, h0, h1]
  ring

/-! ### §3. The order-1 WHITENED witness and the conditional K1 budget. -/

/-- The whitened chart metric of row `q` as a metric field (the banked `whitePullbackMetric`). -/
noncomputable def whiteMetric (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) : Point n → Fin n → Fin n → ℝ :=
  fun w => whitePullbackMetric κ hκ hKc q w

/-- The whitened chart inverse metric of row `q` (the banked `whitePullbackMetricInv`). -/
noncomputable def whiteMetricInv (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) : Point n → Fin n → Fin n → ℝ :=
  fun w => whitePullbackMetricInv κ hκ hKc q w

/-- The van-Vleck determinant field of the whitened chart of row `q`. -/
noncomputable def whiteTheta (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) : Point n → ℝ :=
  vanVleck (whiteMetric κ hκ hKc q)

/-- **The whitened-frame DeWitt transport operator** `T̂_q = Θ̂^{−1/2}·Δ_{ĝ_q}(Θ̂^{1/2}·)` —
    the banked `transportOp` at the whitened chart data of row `q`. -/
noncomputable def whiteTransportOp (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) : (Point n → ℝ) → Point n → ℝ :=
  transportOp (whiteTheta κ hκ hKc q) (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)

/-- The whitened transported coefficient family `û = transportCoeff T̂_q`
    (`û₀ ≡ 1`, `û₁ = radialTransportSolve 1 (T̂_q û₀)` — the `p`-DEPENDENT transported `u₁`). -/
noncomputable def whiteCoeffs (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) : ℕ → Point n → ℝ :=
  transportCoeff (whiteTransportOp κ hκ hKc q)

/-- **The transported `u₁` of the whitened chart** — the `p`-dependent first heat coefficient
    (the J4-635-mandated amplitude layer; a `q`-only `1+τc₁` does NOT suffice). -/
noncomputable def whiteU1 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) : Point n → ℝ :=
  whiteCoeffs κ hκ hKc q 1

/-- **★ THE ORDER-1 WHITENED WITNESS (chart side)** —
    `W₁(τ,x) = √det g^κ(q) · G_τ(x)·Θ̂(x)^{−1/2}·(û₀(x) + τ·û₁(x))` : the banked N = 1
    parametrix (`heatParametrixFn 1`) at the whitened chart data, with the row amplitude
    `√det g^κ(q)` of the order-0 whitened witness kept.  This is the witness family whose
    diagonal the consuming capstone pins (`heatParametrixFn N`, `N ≥ 1`). -/
noncomputable def whiteChartKernel1 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) : ℝ → Point n → ℝ :=
  fun τ x => Real.sqrt (Matrix.det (curvedRNCMetric κ q))
    * heatParametrixFn 1 (whiteMetric κ hκ hKc q) (whiteTransportOp κ hκ hKc q) τ x

/-- **THE ORDER-1 WHITENED WITNESS (ambient)** — the chart kernel evaluated through the banked
    whitened inverse chart, mirroring the order-0 `whiteAmbientKernel`. -/
noncomputable def whiteAmbientKernel1 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) : ℝ → Point n → Point n → ℝ :=
  fun τ p q => whiteChartKernel1 κ hκ hKc q τ (whiteInvChart κ hκ hKc q p)

/-- Unfolding gate: the ambient order-1 kernel IS the chart kernel through the inverse chart
    (definitional). -/
theorem whiteAmbientKernel1_eq_chart (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (τ : ℝ) (p q : Point n) :
    whiteAmbientKernel1 κ hκ hKc τ p q
      = whiteChartKernel1 κ hκ hKc q τ (whiteInvChart κ hκ hKc q p) := rfl

/-- **The explicit product form** of the order-1 whitened chart witness:
    `W₁(τ,x) = √det g^κ(q) · (G_τ(x)·Θ̂(x)^{−1/2}·(1 + û₁(x)·τ))` — the amplitude is the
    genuine `u₀ + τ·u₁` transport layer (`û₀ ≡ 1`). -/
theorem whiteChartKernel1_apply (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (τ : ℝ) (x : Point n) :
    whiteChartKernel1 κ hκ hKc q τ x
      = Real.sqrt (Matrix.det (curvedRNCMetric κ q))
        * (gaussDdim τ x * (whiteTheta κ hκ hKc q x) ^ (-(1 : ℝ) / 2)
            * (1 + whiteU1 κ hκ hKc q x * τ)) := by
  unfold whiteChartKernel1
  rw [heatParametrixFn_apply]
  have hsum : (∑ k ∈ Finset.range (1 + 1),
      transportCoeff (whiteTransportOp κ hκ hKc q) k x * τ ^ k)
      = 1 + whiteU1 κ hκ hKc q x * τ := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, transportCoeff_zero]
    simp only [pow_zero, pow_one, one_mul]
    rfl
  rw [hsum]
  have hΘ : vanVleck (whiteMetric κ hκ hKc q) = whiteTheta κ hκ hKc q := rfl
  rw [hΘ]

/-- The whitened chart metric matrix at the centre is the identity (from the banked
    `whitePullbackMetric_zero` — the point of whitening), hence has determinant 1. -/
theorem whiteMetric_det_center (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) :
    Matrix.det (whiteMetric κ hκ hKc q (0 : Point n)) = 1 := by
  have hmat : (whiteMetric κ hκ hKc q (0 : Point n))
      = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    funext i j
    show whitePullbackMetric κ hκ hKc q 0 i j = _
    rw [whitePullbackMetric_zero κ hκ hKc q hq i j, Matrix.one_apply]
  rw [hmat, Matrix.det_one]

/-- **The diagonal `a₁` CARRIER (labelled).**  At the chart centre, GIVEN the labelled DeWitt
    normalization `û₁(0) = R/6` (the Seeley–DeWitt value — NOT derived here; the flat tower /
    J6 carry it), the order-1 whitened witness diagonal is
        `W₁(t,0) = √det g^κ(q) · (4πt)^{−n/2}·(1 + (R/6)·t)`
    — the amplitude CARRIES the `a₁` coefficient; building the carrier ≠ proving the value. -/
theorem whiteChartKernel1_diagonal_a1 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (hq : q ∈ Kset) (t R : ℝ)
    (hu1 : whiteU1 κ hκ hKc q (0 : Point n) = R / 6) :
    whiteChartKernel1 κ hκ hKc q t (0 : Point n)
      = Real.sqrt (Matrix.det (curvedRNCMetric κ q))
        * ((heatKernel1D t 0) ^ n * (1 + R / 6 * t)) := by
  unfold whiteChartKernel1
  rw [heatParametrixFn_eq]
  have hcoeffs : transportCoeff (whiteTransportOp κ hκ hKc q) = whiteCoeffs κ hκ hKc q := rfl
  rw [hcoeffs]
  rw [heatParametrix_diagonal_a1 1 _ _ t R
    (vanVleck_zero _ (whiteMetric_det_center κ hκ hKc q hq)) le_rfl
    (by unfold whiteCoeffs; rw [transportCoeff_zero]) hu1]
  simp

/-- **The GATED order-1 whitened defect kernel** — the window `0 < s ≤ 1 ∧ ‖x‖ < r₀` times the
    ALREADY-COMPUTED N = 1 residual at the whitened chart data of row `q` (window × residual,
    NOT the residual of a windowed kernel: no cutoff-derivative terms).  This is the `E`-slot
    kernel the K1 rung consumes. -/
noncomputable def whiteDefect1 (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (r₀ : ℝ) : ℝ → Point n → Point n → ℝ :=
  fun s x _ => if 0 < s ∧ s ≤ 1 ∧ ‖x‖ < r₀ then
    parametrixResidualN 1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
      (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) s x
    else 0

/-- On the window, the gated kernel IS the heat defect `∂_s − Δ_{ĝ_q}` of the (normalized)
    order-1 whitened chart parametrix (definitional through `heatParametrixFn_eq`; the row
    constant `√det g^κ(q)` is bookkeeping that commutes with the heat operator and folds into
    the column constant). -/
theorem whiteDefect1_eq_defect (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (r₀ s : ℝ) (x y : Point n)
    (hgate : 0 < s ∧ s ≤ 1 ∧ ‖x‖ < r₀) :
    whiteDefect1 κ hκ hKc q r₀ s x y
      = deriv (fun σ => heatParametrixFn 1 (whiteMetric κ hκ hKc q)
          (whiteTransportOp κ hκ hKc q) σ x) s
        - laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
            (heatParametrixFn 1 (whiteMetric κ hκ hKc q) (whiteTransportOp κ hκ hKc q) s) x := by
  unfold whiteDefect1
  rw [if_pos hgate]
  rfl

/-- **★ THE LINEAR-GAIN COLUMN BOUND** — the EXACT antecedent of the proved K1 rung
    (`k1BudgetW_of_pointwise_linear_gain`).  GIVEN, on the gate `‖x‖ < r₀`, the four labelled
    transport inputs (coefficient smoothness `hwsm`; radial compatibility `hGauss`; the two
    off-diagonal transport equations `h0`, `h1`) and the remainder regularity `hΔ`
    (`|Δ_{ĝ}û-fold₁| ≤ C_Δ`), the gated order-1 defect obeys
        `|E₁(s,p,0)| ≤ (√wⁿ·C_Δ)·(s·G_{ws}(p−0))`   for ALL `p` and `s ∈ (0,1]`
    (off-gate the kernel vanishes).  The `s`-linearity is the cancellation of §2; the width
    transfer pays `√wⁿ`.  ⚠ CONDITIONAL on the labelled inputs — see the header scope. -/
theorem whiteDefect1_linear_gain (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (r₀ w C_Δ : ℝ) (hw1 : 1 ≤ w) (hCΔ : 0 ≤ C_Δ)
    (hwsm : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) k))
    (hGauss : ∀ x : Point n, ‖x‖ < r₀ → ∀ i,
      (∑ j, (whiteMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)) * x j) = 0)
    (h0 : ∀ x : Point n, ‖x‖ < r₀ →
      totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0)
    (h1 : ∀ x : Point n, ‖x‖ < r₀ →
      totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0)
    (hΔ : ∀ x : Point n, ‖x‖ < r₀ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ) :
    ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |whiteDefect1 κ hκ hKc q r₀ s p 0|
        ≤ (Real.sqrt w ^ n * C_Δ) * (s * gaussDdim (w * s) (p - 0)) := by
  intro s p hs hs1
  rw [sub_zero]
  have hG0 : 0 ≤ gaussDdim (w * s) p := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  by_cases hp : ‖p‖ < r₀
  · have hval : whiteDefect1 κ hκ hKc q r₀ s p (0 : Point n)
        = parametrixResidualN 1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
            (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) s p := by
      unfold whiteDefect1
      rw [if_pos ⟨hs, hs1, hp⟩]
    rw [hval, parametrixResidual_N1_linear_gain _ _ _ _ s hs p hwsm
      (hGauss p hp) (h0 p hp) (h1 p hp), abs_neg]
    have hGs : 0 < gaussDdim s p := gaussDdim_pos s hs p
    have hwid : gaussDdim s p ≤ Real.sqrt w ^ n * gaussDdim (w * s) p := by
      have h := gaussDdim_le_of_width_le 1 w one_pos hw1 (τ := s) hs p
      rwa [one_mul, div_one] at h
    calc |s * gaussDdim s p
          * laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
              (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) p|
        = s * gaussDdim s p
          * |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
              (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) p| := by
          rw [abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hGs]
      _ ≤ s * gaussDdim s p * C_Δ := by
          exact mul_le_mul_of_nonneg_left (hΔ p hp)
            (mul_nonneg hs.le hGs.le)
      _ ≤ s * (Real.sqrt w ^ n * gaussDdim (w * s) p) * C_Δ := by
          have := mul_le_mul_of_nonneg_left hwid hs.le
          exact mul_le_mul_of_nonneg_right this hCΔ
      _ = (Real.sqrt w ^ n * C_Δ) * (s * gaussDdim (w * s) p) := by ring
  · have hval : whiteDefect1 κ hκ hKc q r₀ s p (0 : Point n) = 0 := by
      unfold whiteDefect1
      rw [if_neg (fun h => hp h.2.2)]
    rw [hval, abs_zero]
    exact mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hCΔ)
      (mul_nonneg hs.le hG0)

/-- **★★ `white_K1BudgetW_of_transport` — the k = 1 `t²` BUDGET at the order-1 whitened
    witness, through the proved rung.**  Under the SAME labelled transport inputs as
    `whiteDefect1_linear_gain` (`w ≥ 2` for the rung) and a Gaussian-dominated `H` with
    `H(0,0,·) = 0`, the k = 1 Duhamel budget holds:
        `K1TransportBudgetW w H E₁`  ,  `E₁ = whiteDefect1`.
    ZERO new consumer work: the column bound is fed verbatim to the banked
    `k1BudgetW_of_pointwise_linear_gain`.  ⚠ CONDITIONAL on {hwsm, hGauss, h0, h1, hΔ} —
    the honest owed content is their discharge at the whitened chart data.  NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_of_transport (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (q : Point n) (r₀ w C_Δ : ℝ) (hw2 : 2 ≤ w) (hCΔ : 0 ≤ C_Δ)
    (hwsm : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) k))
    (hGauss : ∀ x : Point n, ‖x‖ < r₀ → ∀ i,
      (∑ j, (whiteMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)) * x j) = 0)
    (h0 : ∀ x : Point n, ‖x‖ < r₀ →
      totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0)
    (h1 : ∀ x : Point n, ‖x‖ < r₀ →
      totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0)
    (hΔ : ∀ x : Point n, ‖x‖ < r₀ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ)
    (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ) (hCH : 0 ≤ C_H)
    (hH : ∀ (a : ℝ) (ζ : Point n), 0 < a →
      |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ))
    (hH0 : ∀ ζ : Point n, H 0 0 ζ = 0) :
    K1TransportBudgetW w H (whiteDefect1 κ hκ hKc q r₀) := by
  have hw1 : (1 : ℝ) ≤ w := le_trans one_le_two hw2
  exact k1BudgetW_of_pointwise_linear_gain w hw2 (whiteDefect1 κ hκ hKc q r₀)
    (Real.sqrt w ^ n * C_Δ)
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hCΔ)
    (whiteDefect1_linear_gain κ hκ hKc q r₀ w C_Δ hw1 hCΔ hwsm hGauss h0 h1 hΔ)
    H C_H hCH hH hH0

/-- The budget at the CONCRETE Gaussian `H`-witness (`n = 2`, `w = 8`, the banked
    `frozenK2Sharp_H_witness` — `C_H = 1`): the H-side hypotheses of the rung are DISCHARGED;
    only the transport inputs remain.  NOT `a₁ = R/6`. -/
theorem white_K1BudgetW_concreteH (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point 2)}
    (hKc : IsCompact Kset) (q : Point 2) (r₀ C_Δ : ℝ) (hCΔ : 0 ≤ C_Δ)
    (hwsm : ∀ k, ContDiff ℝ ⊤
      (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) k))
    (hGauss : ∀ x : Point 2, ‖x‖ < r₀ → ∀ i,
      (∑ j, (whiteMetricInv κ hκ hKc q x i j - (if i = j then (1 : ℝ) else 0)) * x j) = 0)
    (h0 : ∀ x : Point 2, ‖x‖ < r₀ →
      totalRadialO1_coeff (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0)
    (h1 : ∀ x : Point 2, ‖x‖ < r₀ →
      totalRadialO1_coeff_level1 (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) x = 0)
    (hΔ : ∀ x : Point 2, ‖x‖ < r₀ →
      |laplaceBeltrami (whiteMetric κ hκ hKc q) (whiteMetricInv κ hκ hKc q)
        (foldedCoeff (whiteTheta κ hκ hKc q) (whiteCoeffs κ hκ hKc q) 1) x| ≤ C_Δ) :
    K1TransportBudgetW 8 (fun a _ ζ => gaussDdim (2 * a) ((0 : Point 2) - ζ))
      (whiteDefect1 κ hκ hKc q r₀) := by
  have hW := QIQTH.FrozenK2Sharp.frozenK2Sharp_H_witness (n := 2) (by norm_num)
  exact white_K1BudgetW_of_transport κ hκ hKc q r₀ 8 C_Δ (by norm_num) hCΔ
    hwsm hGauss h0 h1 hΔ
    (fun a _ ζ => gaussDdim (2 * a) ((0 : Point 2) - ζ)) 1 zero_le_one
    (fun a ζ ha => hW.1 a ζ ha) (fun ζ => hW.2.1 ζ)

/-! ### §4. Non-vacuity gates (cp466 discipline). -/

/-- **★ ANTECEDENT INHABITANCE** — the hypothesis set {hw, hGauss, h0, h1} of the cancellation
    theorem is JOINTLY SATISFIABLE, at the flat data `g = gi = δ`, `Θ ≡ 1`, `u = (1,0,0,…)`,
    at EVERY point `v` (no `K = {0}` collapse; the quantifiers are over all of `Point n`).
    ⚠ HONEST: this proves CONSISTENCY of the antecedent set (the cp466 inhabitance gate), NOT
    curved applicability — discharging the set at the genuinely curved whitened chart data is
    exactly the owed content listed in the header. -/
theorem flat_order1_hyps_inhabited :
    (∀ k, ContDiff ℝ ⊤ (foldedCoeff (fun _ : Point n => (1 : ℝ))
        (fun k _ => if k = 0 then (1 : ℝ) else 0) k))
    ∧ (∀ v : Point n, ∀ i, (∑ j, ((fun _ : Point n => fun i j : Fin n =>
          if i = j then (1 : ℝ) else 0) v i j - (if i = j then (1 : ℝ) else 0)) * v j) = 0)
    ∧ (∀ v : Point n, totalRadialO1_coeff
        (fun _ : Point n => fun i j : Fin n => if i = j then (1 : ℝ) else 0)
        (fun _ : Point n => fun i j : Fin n => if i = j then (1 : ℝ) else 0)
        (fun _ : Point n => (1 : ℝ)) (fun k _ => if k = 0 then (1 : ℝ) else 0) v = 0)
    ∧ (∀ v : Point n, totalRadialO1_coeff_level1
        (fun _ : Point n => fun i j : Fin n => if i = j then (1 : ℝ) else 0)
        (fun _ : Point n => fun i j : Fin n => if i = j then (1 : ℝ) else 0)
        (fun _ : Point n => (1 : ℝ)) (fun k _ => if k = 0 then (1 : ℝ) else 0) v = 0) := by
  have hfold0 : foldedCoeff (fun _ : Point n => (1 : ℝ))
      (fun k _ => if k = 0 then (1 : ℝ) else 0) 0 = fun _ : Point n => (1 : ℝ) := by
    funext y
    simp [foldedCoeff, Real.one_rpow]
  have hfold1 : foldedCoeff (fun _ : Point n => (1 : ℝ))
      (fun k _ => if k = 0 then (1 : ℝ) else 0) 1 = fun _ : Point n => (0 : ℝ) := by
    funext y
    simp [foldedCoeff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    match k with
    | 0 => rw [hfold0]; exact contDiff_const
    | (k + 1) =>
      have hfoldk : foldedCoeff (fun _ : Point n => (1 : ℝ))
          (fun k _ => if k = 0 then (1 : ℝ) else 0) (k + 1) = fun _ : Point n => (0 : ℝ) := by
        funext y
        simp [foldedCoeff]
      rw [hfoldk]; exact contDiff_const
  · intro v i
    refine Finset.sum_eq_zero fun j _ => ?_
    simp
  · intro v
    unfold totalRadialO1_coeff
    rw [hfold0]
    simp [christoffel_of_const, radialDeriv, pd_const]
  · intro v
    unfold totalRadialO1_coeff_level1
    rw [hfold0, hfold1]
    simp [christoffel_of_const, radialDeriv, pd_const, laplaceBeltrami_const]

/-- **Consistency gate — the cancellation FIRES at the inhabited witness**: at the flat data the
    linear-gain identity applies (all antecedents supplied by `flat_order1_hyps_inhabited`) and
    yields residual `= 0` (since `w₁ ≡ 0` there) — the theorem chain is non-degenerate
    end-to-end at one explicit witness. -/
theorem flat_N1_residual_vanishes (t : ℝ) (ht : 0 < t) (v : Point n) :
    parametrixResidualN 1
      (fun _ : Point n => fun i j : Fin n => if i = j then (1 : ℝ) else 0)
      (fun _ : Point n => fun i j : Fin n => if i = j then (1 : ℝ) else 0)
      (fun _ : Point n => (1 : ℝ)) (fun k _ => if k = 0 then (1 : ℝ) else 0) t v = 0 := by
  obtain ⟨hw, hG, h0, h1⟩ := flat_order1_hyps_inhabited (n := n)
  rw [parametrixResidual_N1_linear_gain _ _ _ _ t ht v hw (hG v) (h0 v) (h1 v)]
  have hfold1 : foldedCoeff (fun _ : Point n => (1 : ℝ))
      (fun k _ => if k = 0 then (1 : ℝ) else 0) 1 = fun _ : Point n => (0 : ℝ) := by
    funext y
    simp [foldedCoeff]
  rw [hfold1, laplaceBeltrami_const]
  ring

/-- **Gate — the order-1 whitened witness is genuinely NONZERO at the curved data**
    (`n = 2`, `κ = −1`, `K = B̄(0,2)`, row `q = 0`, chart centre): there is a time `τ ∈ (0,1]`
    with `whiteChartKernel1(τ,0) ≠ 0` — the constructed witness is not the zero family
    (`√det g^κ(q) > 0`, `G_τ(0) > 0`, `Θ̂(0) = 1`, and `1 + û₁(0)·τ > 0` at
    `τ = 1/(1+|û₁(0)|)`). -/
theorem whiteChartKernel1_ne_zero_gate :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧
      whiteChartKernel1 (-1 : ℝ) (by norm_num)
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
    -- the amplitude `1 + c·τ` is positive: `|c|·τ = |c|/(1+|c|) < 1`
    have hamp : 0 < 1 + c * τ := by
      have h1 : |c| * τ < 1 := by
        rw [hτdef, mul_one_div, div_lt_one (by positivity)]
        linarith [abs_nonneg c]
      have h2 : -(|c| * τ) ≤ c * τ := by
        have := neg_abs_le (c * τ)
        rwa [abs_mul, abs_of_pos hτ0] at this
      linarith
    rw [whiteChartKernel1_apply]
    have hdet : 0 < Real.sqrt (Matrix.det (curvedRNCMetric (-1 : ℝ) (0 : Point 2))) :=
      Real.sqrt_pos.mpr (curvedRNCMetric_det_pos (-1 : ℝ) (by norm_num) (0 : Point 2))
    have hG : 0 < gaussDdim τ (0 : Point 2) := gaussDdim_pos τ hτ0 _
    have hΘ : whiteTheta (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2) (0 : Point 2) (0 : Point 2) = 1 :=
      vanVleck_zero _ (whiteMetric_det_center (-1 : ℝ) (by norm_num)
        (isCompact_closedBall (0 : Point 2) 2) (0 : Point 2) hq)
    rw [hΘ, Real.one_rpow]
    have hpos : 0 < Real.sqrt (Matrix.det (curvedRNCMetric (-1 : ℝ) (0 : Point 2)))
        * (gaussDdim τ (0 : Point 2) * 1 * (1 + c * τ)) := by
      apply mul_pos hdet
      rw [mul_one]
      exact mul_pos hG hamp
    exact ne_of_gt hpos

end QIQTH.WhiteOrder1

-- std-3 verification (chk): READ these outputs — no sorryAx, no extra axioms.
#print axioms QIQTH.WhiteOrder1.parametrixResidual_N1_layers
#print axioms QIQTH.WhiteOrder1.parametrixResidual_N1_linear_gain
#print axioms QIQTH.WhiteOrder1.whiteChartKernel1_apply
#print axioms QIQTH.WhiteOrder1.whiteMetric_det_center
#print axioms QIQTH.WhiteOrder1.whiteChartKernel1_diagonal_a1
#print axioms QIQTH.WhiteOrder1.whiteDefect1_eq_defect
#print axioms QIQTH.WhiteOrder1.whiteDefect1_linear_gain
#print axioms QIQTH.WhiteOrder1.white_K1BudgetW_of_transport
#print axioms QIQTH.WhiteOrder1.white_K1BudgetW_concreteH
#print axioms QIQTH.WhiteOrder1.flat_order1_hyps_inhabited
#print axioms QIQTH.WhiteOrder1.flat_N1_residual_vanishes
#print axioms QIQTH.WhiteOrder1.whiteChartKernel1_ne_zero_gate
