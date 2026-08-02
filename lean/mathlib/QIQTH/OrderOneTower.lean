/-
  OrderOneTower — J4-105: the ORDER-`N = 1` RE-RUN of the τ-uniform residual tower, targeting the
  `(0,t]`-restricted MIXED-α consumer shape of the restricted `a₁ = R/6` capstone (J4-104).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT IS BUILT HERE (the honest boundary — read it).

  J4-102 (`OrderNResidual`) built the `N`-generic plumbing (near packet consumer, `N`-parametric
  witness `globalCutoffParametrixWitnessN`) and the `N = 1` diagonal tail; J4-103
  (`ResidualN1GaussianBound`) built the EXACT `N = 1` residual algebraic split
      `R₁ = R₀[u] + H₀[u'] + τ·R₀[u']`   (`u' := fun j => u (j+1)`)
  and the FIXED-`t` `N = 1` residual Gaussian bound; J4-104 (`RestrictedEboundW`) built the
  `(0,t]`-restricted capstone consuming the MIXED-α bound via `capstone_inputs_N1_shape`.  This file
  runs the analytic heart of the order-1 re-plumb.

    • `uniformResidualN1_narrow_mixed` — ★ THE `N = 1` UNIFORM (over `K`) RESIDUAL MIXED BOUND, at the
      NARROW width `G_{3/2} = gaussDdim (3/2·τ)`.  From the J4-103 split and the EXISTING `N = 0`
      NARROW τ-uniform residual bound `uniformResidual_gaussian_bound_tau_narrow` (WidthMarginEngine)
      applied at BOTH the profile `u` (term i) and the SHIFTED profile `u' = fun j => u (j+1)`
      (term iii, via `foldedCoeff_shift`), plus the middle term `gauss·w₁` (term ii) dominated by
      `W₁·√(3/2)ⁿ·G_{3/2}` (`gaussDdim_le_gaussDdim_narrow`):
          `|parametrixResidualN 1 g̃_q g̃⁻¹_q Θ u τ v| ≤ (B₀ + B₁·τ)·gaussDdim (3/2·τ) v`
      uniformly over `q ∈ K`, `‖v‖ < ρ_u`, with `B₀ = C₀ + W₁·√(3/2)ⁿ`, `B₁ = C₁`.  This is the
      honest `C₀ + C₁·τ` MIXED shape the restricted capstone needs (the `τ¹` tail = the `α = 1`
      diagonal margin, exactly the `baseKernelW 2 1` power).

  The `N = 1` witness diagonal-evaluation siblings (gate-generic; the payoff for `hHdiag`):

    • `gatedWitnessN1_diag_eval` — the `N = 1` sibling of `CapstoneWiring.gatedWitness_diag_eval`:
      the gated `globalCutoffParametrixWitnessN 1` on the diagonal at the origin collapses to
      `heatParametrix 1 Θ u t 0` (the `gauss·(u₀ + t·u₁)` ansatz `hHdiag` at `N = 1` demands).
    • `gatedWitnessN1_diag_eval_vanVleck` — the concrete van-Vleck `N = 1` identification:
      `gatedKernel … t 0 0 = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t 0`
      (`heatParametrixFn_eq` definitional).  This IS the capstone's `hHdiag` shape at `N = 1`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST SCOPE (binding).  `uniformResidualN1_narrow_mixed` is the τ-uniform residual bound at the
  PULLBACK metric (the in-chart engine input), MIXED shape, NOT `a₁ = R/6`.  It carries as GENUINE,
  load-bearing hypotheses the two `totalRadialO1_coeff` bounds (`hCoeffU0` for `u`, `hCoeffU1` for the
  shifted profile `u'` — the same firewalled coefficient input the `N = 0` narrow engine carries, at
  each of the two profiles) and the folded-coefficient smoothness `hw : ∀ k, ContDiff … (foldedCoeff
  Θ u k)`.  The step from THIS pullback-metric bound to the GLOBAL gated `hEboundW_le` (the transport
  identity at `N = 1`, the mixed cover assembly, the LOCAL→GLOBAL/single-`t`→`∀τ≤t` uniformization) is
  the C4c wall and is NOT discharged here.  No `sorry`, no new axioms, no `expRho`, no vacuous
  hypotheses.
-/
import Mathlib
import QIQTH.ResidualN1GaussianBound
import QIQTH.WidthMarginEngine
import QIQTH.OrderNResidual
import QIQTH.CapstoneWiring
import QIQTH.RestrictedEboundW

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped BigOperators ContDiff Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### T1 — the `N = 1` uniform residual MIXED bound at the narrow width `G_{3/2}`. -/

/-- **★ J4-105 (T1) — THE `N = 1` UNIFORM RESIDUAL MIXED BOUND, at the narrow width `G_{3/2}`.**
    Over the compact `K`, the order-1 parametrix residual at the pullback metric `g̃_q` obeys a MIXED-α
    bound
        `|parametrixResidualN 1 g̃_q g̃⁻¹_q Θ u τ v| ≤ (B₀ + B₁·τ)·gaussDdim (3/2·τ) v`
    uniformly for `τ > 0`, `q ∈ K`, `‖v‖ < ρ_u`.  ROUTE: the J4-103 exact residual split
    `R₁ = R₀[u] + H₀[u'] + τ·R₀[u']` (`parametrixResidual_one_split`, metric-arbitrary) reduces the
    bound to: (i) the `N = 0` NARROW uniform residual bound at profile `u`
    (`uniformResidual_gaussian_bound_tau_narrow`, constant `C₀`); (iii) the SAME at the shifted profile
    `u' = fun j => u (j+1)` (`foldedCoeff_shift`; constant `C₁`), scaled by `τ`; (ii) the middle term
    `H₀[u'](τ,v) = gauss·w₁` dominated by `W₁·√(3/2)ⁿ·G_{3/2}` (`gaussDdim_le_gaussDdim_narrow`, with
    `W₁` a compact sup of `w₁`).  Constants: `B₀ = C₀ + W₁·√(3/2)ⁿ`, `B₁ = C₁`.  The `τ¹` tail is the
    `α = 1` diagonal margin (`baseKernelW 2 1`).  Hypotheses genuine: `hw` (all folded coefficients
    smooth), and the two `totalRadialO1_coeff` firewall inputs (`hCoeffU0`/`hCoeffU1`), same-shape at
    the two profiles.  NOT `a₁ = R/6`. -/
theorem uniformResidualN1_narrow_mixed (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (ρ_c C_c0 C_c1 : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c0) (hC_c1 : 0 ≤ C_c1)
    (hCoeffU0 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c0 * rncRadialSq v)
    (hCoeffU1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadialSq v) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ B₀ B₁ : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
        |parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
          ≤ (B₀ + B₁ * τ) * gaussDdim (3 / 2 * τ) v := by
  -- (i) the `N = 0` narrow uniform residual bound at profile `u`.
  obtain ⟨ρ₀, hρ₀0, C₀, hC₀0, hbnd0⟩ :=
    uniformResidual_gaussian_bound_tau_narrow g gi hg hC hK hgnd hgsymm hinvF hframeK
      Θ u (hw 0) ρ_c C_c0 hρ_c hC_c0 hCoeffU0
  -- (iii) the same at the SHIFTED profile `u' = fun j => u (j+1)` (`foldedCoeff Θ u' 0 = w₁`).
  obtain ⟨ρ₁, hρ₁0, C₁, hC₁0, hbnd1⟩ :=
    uniformResidual_gaussian_bound_tau_narrow g gi hg hC hK hgnd hgsymm hinvF hframeK
      Θ (fun j => u (j + 1)) (hw 1) ρ_c C_c1 hρ_c hC_c1 hCoeffU1
  set ρ_u : ℝ := min ρ₀ ρ₁ with hρ_u_def
  have hρ_u0 : 0 < ρ_u := lt_min hρ₀0 hρ₁0
  -- the compact sup `W₁` of `w₁ = foldedCoeff Θ u 1` on the closed ball of radius `ρ_u`.
  obtain ⟨W₁, hW₁0, hW₁bd⟩ : ∃ W₁ : ℝ, 0 ≤ W₁ ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_u, |foldedCoeff Θ u 1 v| ≤ W₁ := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_u).exists_bound_of_continuousOn
        (hw 1).continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  refine ⟨ρ_u, hρ_u0, C₀ + W₁ * Real.sqrt (3 / 2) ^ n, C₁, by positivity, hC₁0, ?_⟩
  intro τ hτ q hq v hv
  have hv0 : ‖v‖ < ρ₀ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv1 : ‖v‖ < ρ₁ := lt_of_lt_of_le hv (min_le_right _ _)
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  rw [parametrixResidual_one_split (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ hτ v hw]
  set G : ℝ := gaussDdim (3 / 2 * τ) v with hGdef
  set R0 : ℝ := parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v with hR0def
  set Mid : ℝ := heatParametrix 0 Θ (fun j => u (j + 1)) τ v with hMiddef
  set R0' : ℝ := parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) τ v with hR0'def
  have hb0 : |R0| ≤ C₀ * G := hbnd0 τ hτ q hq v hv0
  have hb1 : |R0'| ≤ C₁ * G := hbnd1 τ hτ q hq v hv1
  -- (ii) the middle term `gauss·w₁`.
  have hmid : |Mid| ≤ (W₁ * Real.sqrt (3 / 2) ^ n) * G := by
    have hfold : Mid = gaussDdim τ v * foldedCoeff Θ (fun j => u (j + 1)) 0 v := by
      rw [hMiddef, heatParametrix_folded, Finset.sum_range_one, pow_zero, mul_one]
    rw [hfold, abs_mul, abs_of_nonneg (gaussDdim_nonneg τ v)]
    have hv' : |foldedCoeff Θ (fun j => u (j + 1)) 0 v| ≤ W₁ := hW₁bd v hvball
    calc gaussDdim τ v * |foldedCoeff Θ (fun j => u (j + 1)) 0 v|
        ≤ gaussDdim τ v * W₁ := mul_le_mul_of_nonneg_left hv' (gaussDdim_nonneg τ v)
      _ = W₁ * gaussDdim τ v := by ring
      _ ≤ W₁ * (Real.sqrt (3 / 2) ^ n * G) :=
          mul_le_mul_of_nonneg_left (gaussDdim_le_gaussDdim_narrow hτ v) hW₁0
      _ = (W₁ * Real.sqrt (3 / 2) ^ n) * G := by ring
  -- assemble via the residual split and the triangle inequality.
  calc |R0 + Mid + τ * R0'|
      ≤ |R0 + Mid| + |τ * R0'| := abs_add_le _ _
    _ ≤ (|R0| + |Mid|) + |τ * R0'| := add_le_add (abs_add_le _ _) le_rfl
    _ = (|R0| + |Mid|) + τ * |R0'| := by rw [abs_mul, abs_of_pos hτ]
    _ ≤ (C₀ * G + (W₁ * Real.sqrt (3 / 2) ^ n) * G) + τ * (C₁ * G) :=
        add_le_add (add_le_add hb0 hmid) (mul_le_mul_of_nonneg_left hb1 hτ.le)
    _ = ((C₀ + W₁ * Real.sqrt (3 / 2) ^ n) + C₁ * τ) * G := by ring

/-! ### T5 — the `N = 1` gated-witness diagonal evaluation (the `hHdiag` payoff). -/

/-- **★ J4-105 (T5) — THE `N = 1` GATED-WITNESS DIAGONAL EVALUATION.**  The `N = 1` sibling of
    `CapstoneWiring.gatedWitness_diag_eval`: where the origin lies in the base gate (`0 ∈ K`), the
    spatial gate (`0 ∈ S 0`), and the inverse chart fixes the origin (`Vmap 0 0 = 0`), the gated
    order-`1` global cutoff-parametrix witness collapses on the diagonal to the raw ORDER-`1` parametrix
    at the centre:
        `gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap) t 0 0 = heatParametrix 1 Θ u t 0`.
    Proof identical to the `N = 0` template with `globalCutoffParametrixWitnessN` in place of
    `globalCutoffParametrixWitness` (gate-generic; the witness def is the only change).  This is the
    `gauss·(u₀ + t·u₁)` ansatz the capstone's `hHdiag` (with `1 ≤ N`) demands.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_diag_eval (K : Set (Point n)) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Vmap : Point n → Point n → Point n) (t : ℝ)
    (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hV : Vmap 0 0 = 0) :
    gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b Vmap) t 0 0
      = heatParametrix 1 Θ u t 0 := by
  rw [gatedKernel_apply_of_mem K S _ t hK0 hS0]
  simp only [globalCutoffParametrixWitnessN, hV]
  rw [radialCutoff_eq_one ha hab (by rw [rncRadialSq_zero]; positivity), one_mul]

/-- **★ J4-105 (T5) — THE CONCRETE VAN-VLECK `N = 1` DIAGONAL IDENTIFICATION.**  Specialising
    `gatedWitnessN1_diag_eval` to the DeWitt profile `Θ := vanVleck g`,
    `u := transportCoeff (transportOp (vanVleck g) g gi)`, the gated van-Vleck order-`1` witness on the
    diagonal is exactly the assembled parametrix function AT ORDER 1:
        `gatedKernel … t 0 0 = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t 0`.
    This IS the capstone's `hHdiag` shape at `N = 1` (`heatParametrixFn_eq` is definitional) — the order
    the residual capstone (`hN : 1 ≤ N`) requires, closing the `hHdiag` slot for the `N = 1` witness.
    NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_diag_eval_vanVleck (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Vmap : Point n → Point n → Point n) (t : ℝ)
    (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hV : Vmap 0 0 = 0) :
    gatedKernel K S (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b Vmap) t 0 0
      = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t 0 := by
  rw [gatedWitnessN1_diag_eval K S (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi))
        a b ha hab Vmap t hK0 hS0 hV, heatParametrixFn_eq]

/-! ### T4 — the MIXED-α gated cover and its wiring into the restricted capstone. -/

/-- **★ J4-105 (T4) — THE MIXED-α GATED COVER (`H`-abstract).**  The `N = 1` / MIXED-α analogue of
    `HunifTrichotomy.gatedKernel_uniform_perBasePoint_of_cover` (composed with the `baseKernelW`
    reduction).  For each `q ∈ K`, `τ > 0`, `p`, ONE of THREE legs holds: (1) `S q ∈ 𝓝 p` and the
    UNgated residual obeys the MIXED bound `|heatOp g gi H τ p q| ≤ C·(baseKernelW 2 0 + baseKernelW 2 1)
    τ p q`; (2) off-gate; (3) `H(·,·,q)` locally `0` at `(τ,p)`.  Then the GATED kernel obeys the same
    MIXED bound for ALL `p, q, τ > 0`.  Leg (1) transfers in-gate (`gatedKernel_heatOp_eq_of_mem_nhds`),
    legs (2)/(3) vanish (`…eq_zero_of_notMem` / `…eq_zero_of_kernel_locally_zero`); the mixed RHS is
    `≥ 0` (both `baseKernelW` powers nonneg on `τ > 0`), closing the zero cases.  This is the
    gate/cover layer the mission flags as fully `H`-abstract — a strict re-instantiation, NOT re-proof.
    NOT `a₁ = R/6`. -/
theorem gatedKernel_hEboundW_mixed_of_cover (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hcover : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
        (S q ∈ nhds p ∧ |heatOp g gi H τ p q|
            ≤ C * (baseKernelW (2 : ℝ) (0 : ℝ) τ p q + baseKernelW (2 : ℝ) (1 : ℝ) τ p q))
      ∨ ({p' : Point n | p' ∉ S q} ∈ nhds p)
      ∨ ((fun t => H t p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ))
          ∧ (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ)))) :
    ∀ τ p q, 0 < τ →
      |heatOp g gi (gatedKernel K S H) τ p q|
        ≤ C * (baseKernelW (2 : ℝ) (0 : ℝ) τ p q + baseKernelW (2 : ℝ) (1 : ℝ) τ p q) := by
  intro τ p q hτ
  have hbase0 : 0 ≤ baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    rw [baseKernelW_zero_apply]; exact gaussDdim_nonneg _ _
  have hbase1 : 0 ≤ baseKernelW (2 : ℝ) (1 : ℝ) τ p q := by
    rw [baseKernelW_one_eq_tau_mul]; exact mul_nonneg hτ.le hbase0
  have hrhs : 0 ≤ C * (baseKernelW (2 : ℝ) (0 : ℝ) τ p q + baseKernelW (2 : ℝ) (1 : ℝ) τ p q) :=
    mul_nonneg hC (by linarith)
  by_cases hq : q ∈ K
  · rcases hcover q hq τ hτ p with ⟨hS, hbd⟩ | hoff | ⟨ht, hs⟩
    · rw [gatedKernel_heatOp_eq_of_mem_nhds g gi K S H τ p q hq hS]; exact hbd
    · rw [gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inr hoff), abs_zero]
      exact hrhs
    · rw [gatedKernel_heatOp_eq_zero_of_kernel_locally_zero g gi K S H τ p q ht hs, abs_zero]
      exact hrhs
  · rw [gatedKernel_heatOp_eq_zero_of_notMem g gi K S H τ p q (Or.inl hq), abs_zero]
    exact hrhs

/-- **★ J4-105 (T4) — THE RESTRICTED-CAPSTONE `hEboundW_le` FROM THE MIXED GATED COVER.**  Composing the
    MIXED gated cover (`gatedKernel_hEboundW_mixed_of_cover`, `H`-abstract) with the route-β shape bridge
    `capstone_inputs_N1_shape` (J4-104): from the 3-leg MIXED cover, the GATED kernel obeys EXACTLY the
    `(0,t]`-restricted PURE α=0 primitive
        `∀ τ p q, 0 < τ → τ ≤ t → |heatOp g gi (gatedKernel K S H) τ p q| ≤ (C·(1+t))·baseKernelW 2 0 τ p q`
    the restricted capstone `trueKernel_diagonal_a1_eq_R6_residual_restricted` consumes as its single C4c
    primitive `hEboundW_le` (with `H := gatedKernel K S H`, `C := C·(1+t)`).  The mixed cover gives the
    `∀ τ` MIXED bound; on `(0,t]` the `baseKernelW 2 1 = τ·baseKernelW 2 0 ≤ t·baseKernelW 2 0` tail
    collapses to `α = 0` with constant `C·(1+t)`.  This is the exact T4 hand-off; the REMAINING input is
    the per-base-point leg-(1) MIXED residual bound for the concrete `N = 1` witness (the C4c wall, whose
    ANALYTIC core `uniformResidualN1_narrow_mixed` is discharged above).  NOT `a₁ = R/6`. -/
theorem gatedKernel_hEboundW_le_of_mixedCover (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ)
    (C t : ℝ) (hC : 0 ≤ C)
    (hcover : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
        (S q ∈ nhds p ∧ |heatOp g gi H τ p q|
            ≤ C * (baseKernelW (2 : ℝ) (0 : ℝ) τ p q + baseKernelW (2 : ℝ) (1 : ℝ) τ p q))
      ∨ ({p' : Point n | p' ∉ S q} ∈ nhds p)
      ∨ ((fun s => H s p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ))
          ∧ (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ)))) :
    ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi (gatedKernel K S H) τ p q|
        ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
  capstone_inputs_N1_shape g gi (gatedKernel K S H) C t hC
    (fun τ p q hτ _ => gatedKernel_hEboundW_mixed_of_cover g gi K S H C hC hcover τ p q hτ)

end QIQTH.HeatResidualBound
