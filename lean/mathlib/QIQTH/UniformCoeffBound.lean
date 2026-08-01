/-
  UniformCoeffBound — J4-87: discharging the F-res-1 firewall of J4-86.

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## The firewall this file addresses (F-res-1 = `hCoeffU`).

  J4-86 (`UniformResidualBound.lean`) reduced the whole uniform cutoff-residual bound over `K` to the
  SINGLE conditional input `hCoeffU` — the UNIFORM quantitative `O(r²)` bound on the off-diagonal
  van-Vleck coefficient:
      `∃ ρ_c > 0, ∃ C_c ≥ 0, ∀ q ∈ K, ∀ v, ‖v‖ < ρ_c →
         |totalRadialO1_coeff g̃_q g̃⁻¹_q Θ u v| ≤ C_c · rncRadialSq v`.
  J4-86 assessed this as blocked on a uniform `C³`/`∂Γ̃` layer.  THIS FILE DISCHARGES IT WITH ONLY THE
  EXISTING `C²` MACHINERY.

  ## Corrected assessment (verified here): `C²` of `g̃` SUFFICES.

  `totalRadialO1_coeff = coeffAF·w₀ + radialDeriv(w₀) + coeffDevF` (the def in `ParametrixResidualO1Total`),
  and each summand is `O(rncRadialSq)` with a UNIFORM constant using ONLY the available `C²` packet:

  (T-a) `coeffAF = ½Σ(g̃⁻¹_ii−1) − ½ΣΣΣ g̃⁻¹_ij·Γ̃^k_ij·v_k`.  Both parts are `O(r²)`:
        `Σ(g̃⁻¹_ii−1)` is `O(r²)` (`uniformFlowPullbackMetricInv_dev_uniform`); the `Γ̃·v` part is
        `O(r)·O(r)` from the CHRISTOFFEL LINEAR DECAY `|Γ̃(v)| ≤ KdΓ·‖v‖` (this file, R2).  Times the
        bounded `w₀` (EVT).  NO `∂Γ̃` / `C³` needed — the linear decay of `Γ̃` follows from `Γ̃(0)=0`
        plus `Γ̃ = ½g̃⁻¹(∂g̃+∂g̃−∂g̃)` with each `|∂g̃(v)| ≤ Kpd·‖v‖` (this file, R1), which is the
        `fderiv_decay` MVT applied to the `C²` second Fréchet layer of `g̃`.
  (T-b) `radialDeriv(w₀) = Σ v_i·∂_i w₀(v)` is `O(r)·O(r)` from `hw0flat` (`∂w₀(0)=0`, the SAME genuine
        gauge hypothesis the old per-`q` `totalRadialO1_coeff_center_grad_vanishes` uses) + `decay_order_one`.
  (T-c) `coeffDevF = ½ΣΣ(g̃⁻¹_ij−δ)(v_i∂_j w₀+v_j∂_i w₀)` is `O(r²)·O(r)·O(1)` — `O(r³)⊆O(r²)` on the ball.

  ## Landed here (green; NO `sorry`, NO new axioms, NO `expRho` in statements, NO vacuous hypotheses).

  * `uniformFlowPullbackMetric_pd_linear_decay` (R1) — `|∂g̃(v)| ≤ Kpd·‖v‖`, uniform over `K`.
  * `uniformFlowChristoffel_zero_at_zero` — `Γ̃(0)=0` from the jet.
  * `uniformFlowChristoffel_linear_decay` (R2) — THE LOAD-BEARING lemma `|Γ̃(v)| ≤ KdΓ·‖v‖`, uniform over `K`.
  * `uniformCoeff_bound` (R3) — the CAPSTONE `hCoeffU`, from ONLY the geometric+heat-side hypotheses.
  * `cutoffResidual_uniformFlow_unconditional` (R4) — `hCoeffU` discharged into J4-86's cutoff engine:
    the full uniform-over-`K` cutoff-parametrix residual bound from geometric+heat-side hypotheses alone.

  All hypotheses genuine (satisfiable by `g = gi = δ`, `Θ = 1`, `u` constant); NONE is the conclusion.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.UniformResidualBound
import QIQTH.ParametrixResidualO1Total
import QIQTH.UniformFlowMetricInvProps
import QIQTH.RNCDecay
import QIQTH.ChristoffelSmooth

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.GaussianWidthTolerant QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### R1 — uniform linear decay of `∂g̃` near `0`. -/

/-- **★ J4-87 (R1) — UNIFORM `|∂g̃(v)| ≤ Kpd·‖v‖`.**  Each first partial of the uniform-flow pullback
    metric decays LINEARLY near `0`, uniformly over `q ∈ K`.  Since `∂g̃(0)=0` (`_jet_zero` ⟹
    `fderiv g̃ 0 = 0` via `fderiv_zero_of_pd_zero`) and the SECOND Fréchet layer of `g̃` is bounded by `M`
    (`uniformFlowPullbackMetric_c2_uniform_full`), the mean-value inequality `fderiv_decay` gives
    `‖fderiv g̃ v‖ ≤ M·‖v‖`, hence `|∂_e g̃(v)| = |fderiv g̃ v (e)| ≤ M·‖v‖`.  This is the one-derivative
    input to the Christoffel linear decay — using ONLY `C²`, NOT `C³`. -/
theorem uniformFlowPullbackMetric_pd_linear_decay (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0)) :
    ∃ r > (0 : ℝ), ∃ Kpd : ℝ, 0 ≤ Kpd ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r → ∀ a b e : Fin n,
      |pd (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) e v| ≤ Kpd * ‖v‖ := by
  obtain ⟨r₀, hr₀0, M, hpk⟩ := uniformFlowPullbackMetric_c2_uniform_full g gi hg hC hK
  refine ⟨r₀ / 2, by positivity, max 0 M, le_max_left _ _, ?_⟩
  intro q hq v hv a b e
  obtain ⟨_, hjetpd⟩ :=
    uniformFlowPullbackMetric_jet_zero g gi hC hK hg hgsymm hinvF q hq (hframeK q hq)
  set f : Point n → ℝ := fun w => uniformFlowPullbackMetric g gi hC hK q w a b with hfdef
  have hballs : ∀ w : Point n, w ∈ Metric.closedBall (0 : Point n) (r₀ / 2) → ‖w‖ < r₀ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    linarith
  have h0mem : ‖(0 : Point n)‖ < r₀ := by rw [norm_zero]; exact hr₀0
  -- `fderiv f 0 = 0` from vanishing partials + differentiability at `0`.
  have hdf0 : fderiv ℝ f 0 = 0 :=
    fderiv_zero_of_pd_zero ((hpk q hq 0 h0mem a b).1.differentiableAt) (fun e' => hjetpd a b e')
  -- second-layer differentiability + bound on the closed half-ball.
  have hdiff2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2),
      DifferentiableAt ℝ (fderiv ℝ f) w :=
    fun w hw => (hpk q hq w (hballs w hw) a b).2.1.differentiableAt
  have hbound2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2),
      ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ max 0 M :=
    fun w hw => le_trans (hpk q hq w (hballs w hw) a b).2.2.2.2 (le_max_right _ _)
  have hvmem : v ∈ Metric.closedBall (0 : Point n) (r₀ / 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hgrad := fderiv_decay f (max 0 M) (r₀ / 2) (by positivity) hdf0 hdiff2 hbound2 hvmem
  -- convert `pd` to `fderiv` and bound.
  have hdiffAt : DifferentiableAt ℝ f v := (hpk q hq v (hballs v hvmem) a b).1.differentiableAt
  rw [pd_eq_fderiv f e v hdiffAt]
  calc |fderiv ℝ f v (Pi.single e 1)|
      = ‖fderiv ℝ f v (Pi.single e (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ f v‖ * ‖(Pi.single e (1 : ℝ) : Point n)‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ f v‖ * 1 := by rw [Pi.norm_single, norm_one]
    _ = ‖fderiv ℝ f v‖ := mul_one _
    _ ≤ max 0 M * ‖v‖ := hgrad

/-! ### Γ̃(0) = 0. -/

/-- **★ J4-87 — `Γ̃(0) = 0`.**  At the RNC centre the Christoffel symbols of `g̃` vanish, because each
    `∂g̃(0) = 0` (`uniformFlowPullbackMetric_jet_zero`) and `Γ̃ = ½g̃⁻¹(∂g̃+∂g̃−∂g̃)`. -/
theorem uniformFlowChristoffel_zero_at_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (q : Point n) (hq : q ∈ K)
    (hframe : ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0)) (k i j : Fin n) :
    christoffel (fun w a b => uniformFlowPullbackMetric g gi hC hK q w a b)
        (fun w a b => uniformFlowPullbackMetricInv g gi hC hK q w a b) k i j (0 : Point n) = 0 := by
  obtain ⟨_, hjetpd⟩ :=
    uniformFlowPullbackMetric_jet_zero g gi hC hK hg hgsymm hinvF q hq hframe
  simp only [christoffel]
  rw [show (∑ α, uniformFlowPullbackMetricInv g gi hC hK q 0 k α
        * (pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α j) i 0
            + pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α i) j 0
            - pd (fun y => uniformFlowPullbackMetric g gi hC hK q y i j) α 0)) = 0 from ?_]
  · ring
  · refine Finset.sum_eq_zero fun α _ => ?_
    rw [hjetpd α j i, hjetpd α i j, hjetpd i j α]; ring

/-! ### R2 — the load-bearing Christoffel linear decay `|Γ̃(v)| ≤ KdΓ·‖v‖`. -/

/-- **★ J4-87 (R2) — THE CHRISTOFFEL LINEAR DECAY, uniform over `K`.**  `|Γ̃^k_ij(v)| ≤ KdΓ·‖v‖` for
    every `q ∈ K`, `‖v‖ < r₀`.  Same `½·g̃⁻¹·(∂g̃+∂g̃−∂g̃)` assembly as `uniformFlowChristoffel_uniform_bound`
    but with the UNIFORM `∂g̃` bound upgraded from `|∂g̃| ≤ M` to the LINEAR DECAY `|∂g̃(v)| ≤ Kpd·‖v‖`
    (R1).  So `|Γ̃(v)| ≤ ½·n·Kg·3·Kpd·‖v‖`.  Hypotheses ONLY `hg`+`hC`+`IsCompact K`+`hgnd`+`hgsymm`
    +`hinvF`+`hframeK`, all genuine; NOT `a₁ = R/6`.  This replaces the `C³`/`∂Γ̃` layer J4-86 feared. -/
theorem uniformFlowChristoffel_linear_decay (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0)) :
    ∃ r₀ > (0 : ℝ), ∃ KdΓ : ℝ, 0 ≤ KdΓ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ k i j : Fin n,
      |christoffel (fun w a b => uniformFlowPullbackMetric g gi hC hK q w a b)
          (fun w a b => uniformFlowPullbackMetricInv g gi hC hK q w a b) k i j v|
        ≤ KdΓ * ‖v‖ := by
  obtain ⟨r₁, hr₁0, Kg, hKg0, hGIb⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound g gi hg hC hK hgnd
  obtain ⟨r₂, hr₂0, Kpd, hKpd0, hpdb⟩ :=
    uniformFlowPullbackMetric_pd_linear_decay g gi hg hC hK hgsymm hinvF hframeK
  refine ⟨min r₁ r₂, lt_min hr₁0 hr₂0,
    (1 / 2) * (n : ℝ) * Kg * (3 * Kpd), by positivity, ?_⟩
  intro q hq v hv k i j
  have hv1 : ‖v‖ < r₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v‖ < r₂ := lt_of_lt_of_le hv (min_le_right _ _)
  have hGI : ∀ a b : Fin n, |uniformFlowPullbackMetricInv g gi hC hK q v a b| ≤ Kg :=
    fun a b => hGIb q hq v hv1 a b
  have hpd : ∀ a b e : Fin n,
      |pd (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) e v| ≤ Kpd * ‖v‖ :=
    fun a b e => hpdb q hq v hv2 a b e
  -- per-α term bound.
  have hterm : ∀ α : Fin n,
      |uniformFlowPullbackMetricInv g gi hC hK q v k α
          * (pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α j) i v
            + pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α i) j v
            - pd (fun y => uniformFlowPullbackMetric g gi hC hK q y i j) α v)|
        ≤ Kg * (3 * (Kpd * ‖v‖)) := by
    intro α
    rw [abs_mul]
    set A := pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α j) i v with hAdef
    set B := pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α i) j v with hBdef
    set C := pd (fun y => uniformFlowPullbackMetric g gi hC hK q y i j) α v with hCdef
    have h2 : |A + B - C| ≤ 3 * (Kpd * ‖v‖) := by
      have htri := abs_add_le (A + B) (-C)
      rw [← sub_eq_add_neg, abs_neg] at htri
      have hle : |A + B - C| ≤ |A| + |B| + |C| :=
        le_trans htri (by gcongr; exact abs_add_le _ _)
      calc |A + B - C| ≤ |A| + |B| + |C| := hle
        _ ≤ Kpd * ‖v‖ + Kpd * ‖v‖ + Kpd * ‖v‖ := by
            gcongr
            · exact hpd α j i
            · exact hpd α i j
            · exact hpd i j α
        _ = 3 * (Kpd * ‖v‖) := by ring
    exact mul_le_mul (hGI k α) h2 (abs_nonneg _) hKg0
  -- assemble.
  simp only [christoffel]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc (1 / 2 : ℝ)
        * |∑ α, uniformFlowPullbackMetricInv g gi hC hK q v k α
            * (pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α j) i v
              + pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α i) j v
              - pd (fun y => uniformFlowPullbackMetric g gi hC hK q y i j) α v)|
      ≤ (1 / 2 : ℝ) * ∑ α, Kg * (3 * (Kpd * ‖v‖)) := by
        gcongr
        exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun α _ => hterm α)
    _ = (1 / 2 : ℝ) * (n : ℝ) * Kg * (3 * Kpd) * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### R3 — the CAPSTONE `hCoeffU`, from geometric + heat-side hypotheses only. -/

/-- **★ J4-87 (R3) — THE UNIFORM `O(r²)` COEFFICIENT BOUND (`hCoeffU`), DISCHARGED.**  The single
    firewalled input of J4-86 is now a theorem from ONLY the geometric data (`hg`/`hC`/`hK`/`hgnd`/
    `hgsymm`/`hinvF`/`hframeK`) and the heat-side data (`Θ`/`u`/`hw0smooth`/`hw0flat`):
      `∃ ρ_c > 0, ∃ C_c ≥ 0, ∀ q ∈ K, ∀ v, ‖v‖ < ρ_c →
         |totalRadialO1_coeff g̃_q g̃⁻¹_q Θ u v| ≤ C_c · rncRadialSq v`.
    Split `totalRadialO1_coeff = coeffAF·w₀ + radialDeriv(w₀) + coeffDevF` and bound each summand by a
    UNIFORM constant times `rncRadialSq v`, using ONLY the `C²` machinery:
    * `coeffAF·w₀` : `coeffAF = ½Σ(g̃⁻¹_ii−1) − ½ΣΣΣ g̃⁻¹·Γ̃·v` is `O(r²)` — the diagonal deviation from
      `uniformFlowPullbackMetricInv_dev_uniform` and `Γ̃·v` from the CHRISTOFFEL LINEAR DECAY (R2) times
      `v`; times the EVT-bounded `w₀`.
    * `radialDeriv(w₀) = Σ v_i·∂_i w₀` : `O(r)·O(r)` via `hw0flat` (`∂w₀(0)=0`) + `decay_order_one`.
    * `coeffDevF` : `O(r²)·O(r)` from the deviation and the gradient decay of `w₀`.
    `hw0flat` is the SAME genuine gauge hypothesis the old per-`q` `totalRadialO1_coeff_center_grad_vanishes`
    uses; all hypotheses satisfiable by `g = gi = δ`, `Θ = 1`, `u` constant; NONE is the conclusion; NO
    `expRho` in the statement.  NOT `a₁ = R/6`. -/
theorem uniformCoeff_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0) :
    ∃ ρ_c : ℝ, 0 < ρ_c ∧ ∃ C_c : ℝ, 0 ≤ C_c ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c * rncRadialSq v := by
  classical
  -- geometric ingredients (each on its own ball; radius min'd below).
  obtain ⟨r_d, hr_d0, Md, hMd0, hdev⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform g gi hC hK hg hgnd hgsymm hinvF hframeK
  obtain ⟨r_e, hr_e0, Kg, hKg0, hGIb⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound g gi hg hC hK hgnd
  obtain ⟨r_Γ, hr_Γ0, KdΓ, hKdΓ0, hChb⟩ :=
    uniformFlowChristoffel_linear_decay g gi hg hC hK hgnd hgsymm hinvF hframeK
  set ρ_c : ℝ := min r_d (min r_e r_Γ) with hρ_c_def
  have hρ_c0 : 0 < ρ_c := lt_min hr_d0 (lt_min hr_e0 hr_Γ0)
  -- heat-side `q`-independent EVT data on the closed ball of radius `ρ_c`.
  obtain ⟨W, hW0, hWbd⟩ : ∃ W : ℝ, 0 ≤ W ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_c, |foldedCoeff Θ u 0 v| ≤ W := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_c).exists_bound_of_continuousOn
        hw0smooth.continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  obtain ⟨Kw2, hKw20, hpdw⟩ : ∃ Kw2 : ℝ, 0 ≤ Kw2 ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_c, ∀ i : Fin n,
        |pd (foldedCoeff Θ u 0) i v| ≤ Kw2 * ‖v‖ := by
    have hcont : Continuous
        (fun w => ∑ i, ‖fderiv ℝ (fun y => pd (foldedCoeff Θ u 0) i y) w‖) :=
      continuous_finsetSum _
        (fun i _ => ((contDiff_pd (foldedCoeff Θ u 0) hw0smooth i).continuous_fderiv (by simp)).norm)
    obtain ⟨C, hC'⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_c).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun v hvmem i => ?_⟩
    have hvle : ‖v‖ ≤ ρ_c := by rw [mem_closedBall_zero_iff] at hvmem; exact hvmem
    refine decay_order_one (fun y => pd (foldedCoeff Θ u 0) i y) (max C 0) ρ_c hρ_c0
      (hw0flat i) ?_ ?_ hvle
    · exact fun w _ =>
        ((contDiff_pd (foldedCoeff Θ u 0) hw0smooth i).differentiable (by simp)).differentiableAt
    · intro w hw
      have hsum := hC' w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at hsum
      calc ‖fderiv ℝ (fun y => pd (foldedCoeff Θ u 0) i y) w‖
          ≤ ∑ i', ‖fderiv ℝ (fun y => pd (foldedCoeff Θ u 0) i' y) w‖ :=
            Finset.single_le_sum
              (f := fun i' => ‖fderiv ℝ (fun y => pd (foldedCoeff Θ u 0) i' y) w‖)
              (fun i' _ => norm_nonneg _) (Finset.mem_univ i)
        _ ≤ C := hsum
        _ ≤ max C 0 := le_max_left _ _
  -- the assembled constant.
  refine ⟨ρ_c, hρ_c0,
    ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * W
      + (n : ℝ) * Kw2 + (n : ℝ) ^ 2 * Md * Kw2 * ρ_c ^ 2, ?_, ?_⟩
  · -- `0 ≤ C_c`.
    have hCA1nn : (0 : ℝ) ≤ (1 / 2) * (n : ℝ) * Md :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hMd0
    have hCA2nn : (0 : ℝ) ≤ (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hKg0) hKdΓ0
    have hCB0 : (0 : ℝ) ≤ (n : ℝ) * Kw2 := mul_nonneg (Nat.cast_nonneg n) hKw20
    have hCC0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * Md * Kw2 * ρ_c ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hMd0) hKw20) (by positivity)
    have := mul_nonneg (add_nonneg hCA1nn hCA2nn) hW0
    positivity
  intro q hq v hv
  have hvd : ‖v‖ < r_d := lt_of_lt_of_le hv (min_le_left _ _)
  have hve : ‖v‖ < r_e := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvΓ : ‖v‖ < r_Γ := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_c := by
    rw [mem_closedBall_zero_iff]; exact hv.le
  unfold totalRadialO1_coeff radialDeriv
  set Gm : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetric g gi hC hK q with hGmdef
  set Gi : Point n → Fin n → Fin n → ℝ := uniformFlowPullbackMetricInv g gi hC hK q with hGidef
  set w0 : Point n → ℝ := foldedCoeff Θ u 0 with hw0def
  -- pointwise data at `v`.
  have hGI : ∀ i j : Fin n, |Gi v i j| ≤ Kg := fun i j => hGIb q hq v hve i j
  have hdevv : ∀ i j : Fin n, |Gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ Md * rncRadialSq v :=
    fun i j => hdev q hq v hvd i j
  have hΓv : ∀ k i j : Fin n, |christoffel Gm Gi k i j v| ≤ KdΓ * ‖v‖ :=
    fun k i j => hChb q hq v hvΓ k i j
  have hpdwv : ∀ i : Fin n, |pd w0 i v| ≤ Kw2 * ‖v‖ := hpdw v hvball
  have hWv : |w0 v| ≤ W := hWbd v hvball
  have hvi : ∀ i : Fin n, |v i| ≤ ‖v‖ := fun i => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v i
  have hnv2 : ‖v‖ * ‖v‖ ≤ rncRadialSq v := by
    have h := norm_le_rncRadial v
    calc ‖v‖ * ‖v‖ ≤ rncRadial v * rncRadial v :=
          mul_le_mul h h (norm_nonneg _) (rncRadial_nonneg _)
      _ = rncRadialSq v := by rw [← rncRadial_sq]; ring
  have hvρ2 : ‖v‖ * ‖v‖ ≤ ρ_c * ρ_c := mul_le_mul hv.le hv.le (norm_nonneg _) hρ_c0.le
  have habs_sub : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
    have h := abs_add_le x (-y); rwa [← sub_eq_add_neg, abs_neg] at h
  -- (A1) diagonal-trace part `|½Σ(Gi_ii−1)|`.
  have hA1 : |(1 / 2) * (∑ i, (Gi v i i - 1))| ≤ (1 / 2) * (n : ℝ) * Md * rncRadialSq v := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, (Gi v i i - 1)| ≤ (n : ℝ) * Md * rncRadialSq v := by
      calc |∑ i, (Gi v i i - 1)| ≤ ∑ i, |Gi v i i - 1| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, Md * rncRadialSq v := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h := hdevv i i; simpa using h
        _ = (n : ℝ) * Md * rncRadialSq v := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    calc (1 / 2 : ℝ) * |∑ i, (Gi v i i - 1)|
        ≤ (1 / 2) * ((n : ℝ) * Md * rncRadialSq v) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = (1 / 2) * (n : ℝ) * Md * rncRadialSq v := by ring
  -- (A2) Christoffel-contraction part `|½ΣΣΣ Gi·Γ̃·v|`.
  have hA2 : |(1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
      ≤ (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
        ≤ (n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖) := by
      calc |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
          ≤ ∑ i, ∑ j, ∑ k, |Gi v i j * christoffel Gm Gi k i j v * v k| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n, Kg * (KdΓ * ‖v‖) * ‖v‖ := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
              Finset.sum_le_sum fun k _ => ?_
            rw [abs_mul, abs_mul]
            exact mul_le_mul (mul_le_mul (hGI i j) (hΓv k i j) (abs_nonneg _) hKg0) (hvi k)
              (abs_nonneg _) (mul_nonneg hKg0 (mul_nonneg hKdΓ0 (norm_nonneg _)))
        _ = (n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    calc (1 / 2 : ℝ) * |∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k|
        ≤ (1 / 2) * ((n : ℝ) ^ 3 * Kg * KdΓ * (‖v‖ * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ ≤ (1 / 2) * ((n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
          exact mul_le_mul_of_nonneg_left hnv2
            (mul_nonneg (mul_nonneg (by positivity) hKg0) hKdΓ0)
      _ = (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := by ring
  -- (TA) `coeffAF · w₀`.
  have hCAcoeff : (0 : ℝ) ≤ (1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ :=
    add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hMd0)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hKg0) hKdΓ0)
  have hTA : |((1 / 2) * (∑ i, (Gi v i i - 1))
        - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)) * w0 v|
      ≤ ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * W * rncRadialSq v := by
    rw [abs_mul]
    have hAF : |(1 / 2) * (∑ i, (Gi v i i - 1))
          - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
        ≤ ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * rncRadialSq v := by
      calc |(1 / 2) * (∑ i, (Gi v i i - 1))
              - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)|
          ≤ |(1 / 2) * (∑ i, (Gi v i i - 1))|
              + |(1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)| :=
            habs_sub _ _
        _ ≤ (1 / 2) * (n : ℝ) * Md * rncRadialSq v
              + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ * rncRadialSq v := add_le_add hA1 hA2
        _ = ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * rncRadialSq v := by ring
    calc |(1 / 2) * (∑ i, (Gi v i i - 1))
            - (1 / 2) * (∑ i, ∑ j, ∑ k, Gi v i j * christoffel Gm Gi k i j v * v k)| * |w0 v|
        ≤ (((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * rncRadialSq v) * W :=
          mul_le_mul hAF hWv (abs_nonneg _) (mul_nonneg hCAcoeff (rncRadialSq_nonneg v))
      _ = ((1 / 2) * (n : ℝ) * Md + (1 / 2) * (n : ℝ) ^ 3 * Kg * KdΓ) * W * rncRadialSq v := by ring
  -- (TB) `radialDeriv(w₀) = Σ v_i ∂_i w₀`.
  have hTB : |∑ i, v i * pd w0 i v| ≤ (n : ℝ) * Kw2 * rncRadialSq v := by
    calc |∑ i, v i * pd w0 i v| ≤ ∑ i, |v i * pd w0 i v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, ‖v‖ * (Kw2 * ‖v‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hvi i) (hpdwv i) (abs_nonneg _) (norm_nonneg _)
      _ = (n : ℝ) * Kw2 * (‖v‖ * ‖v‖) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ (n : ℝ) * Kw2 * rncRadialSq v :=
          mul_le_mul_of_nonneg_left hnv2 (mul_nonneg (Nat.cast_nonneg n) hKw20)
  -- (TC) `coeffDevF`.
  have hTC : |(1 / 2) * (∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
        * (v i * pd w0 j v + v j * pd w0 i v))|
      ≤ (n : ℝ) ^ 2 * Md * Kw2 * ρ_c ^ 2 * rncRadialSq v := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    have hsum : |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
          * (v i * pd w0 j v + v j * pd w0 i v)|
        ≤ (n : ℝ) ^ 2 * Md * Kw2 * 2 * rncRadialSq v * (‖v‖ * ‖v‖) := by
      calc |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
              * (v i * pd w0 j v + v j * pd w0 i v)|
          ≤ ∑ i, ∑ j, (Md * rncRadialSq v) * (2 * (‖v‖ * (Kw2 * ‖v‖))) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul]
            refine mul_le_mul (hdevv i j) ?_ (abs_nonneg _)
              (mul_nonneg hMd0 (rncRadialSq_nonneg v))
            calc |v i * pd w0 j v + v j * pd w0 i v|
                ≤ |v i * pd w0 j v| + |v j * pd w0 i v| := abs_add_le _ _
              _ ≤ ‖v‖ * (Kw2 * ‖v‖) + ‖v‖ * (Kw2 * ‖v‖) := by
                  refine add_le_add ?_ ?_
                  · rw [abs_mul]
                    exact mul_le_mul (hvi i) (hpdwv j) (abs_nonneg _) (norm_nonneg _)
                  · rw [abs_mul]
                    exact mul_le_mul (hvi j) (hpdwv i) (abs_nonneg _) (norm_nonneg _)
              _ = 2 * (‖v‖ * (Kw2 * ‖v‖)) := by ring
        _ = (n : ℝ) ^ 2 * Md * Kw2 * 2 * rncRadialSq v * (‖v‖ * ‖v‖) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    calc (1 / 2 : ℝ) * |∑ i, ∑ j, (Gi v i j - (if i = j then (1 : ℝ) else 0))
            * (v i * pd w0 j v + v j * pd w0 i v)|
        ≤ (1 / 2) * ((n : ℝ) ^ 2 * Md * Kw2 * 2 * rncRadialSq v * (‖v‖ * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = ((n : ℝ) ^ 2 * Md * Kw2 * rncRadialSq v) * (‖v‖ * ‖v‖) := by ring
      _ ≤ ((n : ℝ) ^ 2 * Md * Kw2 * rncRadialSq v) * (ρ_c * ρ_c) :=
          mul_le_mul_of_nonneg_left hvρ2
            (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hMd0) hKw20) (rncRadialSq_nonneg v))
      _ = (n : ℝ) ^ 2 * Md * Kw2 * ρ_c ^ 2 * rncRadialSq v := by ring
  -- assemble the three summands by the triangle inequality.
  refine le_trans (abs_add_le _ _)
    (le_trans (add_le_add (abs_add_le _ _) (le_refl _))
      (le_trans (add_le_add (add_le_add hTA hTB) hTC) ?_))
  apply le_of_eq; ring

/-! ### R4 — the uniform cutoff engine, UNCONDITIONAL (geometric + heat-side hypotheses only). -/

/-- **★ J4-87 (R4) — THE CUTOFF ENGINE UNIFORM OVER `K`, UNCONDITIONAL.**  Feeds the discharged
    `hCoeffU` (`uniformCoeff_bound`, R3) into J4-86's `cutoffResidual_uniformFlow_of_coeffBound`,
    removing the LAST firewall.  The uniform-over-`K` single-`(a,b,B)` cutoff-parametrix residual bound
    now holds under ONLY the geometric data (`hg`/`hC`/`hK`/`hgnd`/`hgsymm`/`hinvF`/`hframeK`) and the
    heat-side data (`Θ`/`u`/`hw0smooth`/`hw0flat`/`ht`) — no conditional coefficient input remains.  All
    hypotheses are genuine (satisfiable by `g = gi = δ`, `Θ = 1`, `u` constant, `hframeK` the RNC-gauge
    family), none is the conclusion; NO `expRho` in the statement.  NOT `a₁ = R/6`. -/
theorem cutoffResidual_uniformFlow_unconditional (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    {t : ℝ} (ht : 0 < t) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∀ q ∈ K, ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) t
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u t y) v|
        ≤ B * gaussDdimWide t v := by
  obtain ⟨ρ_c, hρ_c, C_c, hC_c0, hCoeffU⟩ :=
    uniformCoeff_bound g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw0smooth hw0flat
  exact cutoffResidual_uniformFlow_of_coeffBound g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u
    hw0smooth ht ρ_c C_c hρ_c hC_c0 hCoeffU

end QIQTH.HeatResidualBound
