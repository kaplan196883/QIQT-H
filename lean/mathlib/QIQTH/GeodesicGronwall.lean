/-
  GeodesicGronwall — J4-150: the TWO-SOLUTION (nonlinear) Grönwall comparison for the geodesic
  phase-flow, closing the BASE-POINT flow difference `‖φ_{q'} w − φ_q w‖ ≤ e^L·‖q − q'‖` and — via the
  J4-149 transfer lemma + the right-inverse identity — the Lipschitz modulus of the origin chart
  `z ↦ uniformInverseChart … z 0`, hence `hWmeas₀`.  ONE brick of the a₁=R/6 campaign; **NOT a₁=R/6**.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms, NO `expRho`).

    * `geodesicField_lipschitzOnWith_closedBall` — **W1.**  `geodesicField g gi` (which is `C^∞` from
      `hC`) is `LipschitzOnWith` some `L : ℝ≥0` on ANY closed ball of the phase space
      `Point n × Point n` (a CONVEX COMPACT set).  Via `ContDiffOn.exists_lipschitzOnWith`
      (`convex_closedBall`, `isCompact_closedBall` — the phase space is finite-dimensional, hence
      proper).  The reusable Lipschitz engine for the nonlinear Grönwall.

    * `uniformTube_twopoint_diff_bound` — **W2 (★ the nonlinear two-solution Grönwall).**  For two
      confined geodesic tubes through `(q, w)` and `(q', w)` (SAME velocity `w`, `‖w‖ ≤ ρ_K`, both
      `q, q' ∈ K`), a SINGLE uniform Lipschitz constant `L ≥ 0` over `K` gives, on `[0,1]`,
        `dist (uniformFlowTube … q w t) (uniformFlowTube … q' w t) ≤ dist q q' · exp (L·t)`.
      Both tubes live in the fixed convex compact ball `closedBall 0 (M + C₀·ρ_K)` (`K ⊆ closedBall 0 M`
      + the `C₀‖w‖`-confinement), where `geodesicField` is `L`-Lipschitz (W1); Mathlib's two-trajectory
      comparison `dist_le_of_trajectories_ODE_of_mem` (same autonomous field, ICs differing by
      `(q−q', 0)`) closes it.

    * `uniformFlowExp_base_diff_bound` — **W3 (the base-flow difference).**  Projecting W2 at `t = 1`
      onto the position component (`‖p.1‖ ≤ ‖p‖`),
        `‖uniformFlowExp … q w − uniformFlowExp … q' w‖ ≤ exp L · ‖q − q'‖`   (q, q' ∈ K, ‖w‖ ≤ ρ_K).
      This is EXACTLY the residue `‖φ_{q'} w − φ_q w‖ → 0` isolated by the J4-149 transfer lemma — the
      base-point flow difference at a FIXED velocity, now CLOSED (a genuine Lipschitz-in-base bound).

    * `chartOrigin_lipschitz_modulus` — **W4a (the origin-chart Lipschitz modulus).**  Welding W3 to the
      J4-149 transfer lemma `chart_joint_velocity_modulus` and the right-inverse identity
      `φ_z (W z 0) = 0`, the origin chart `W₀ z := uniformInverseChart … z 0` is Lipschitz in the base:
        `‖W₀ z − W₀ z'‖ ≤ (C_inv · exp L) · ‖z − z'‖`.
      (The transfer's first term `‖φ_z(W z 0) − φ_{z'}(W z' 0)‖ = ‖0 − 0‖ = 0` by the right-inverse; the
      second term `= ‖φ_{z'}(W z' 0) − φ_z(W z' 0)‖` is W3 at velocity `W z' 0`.)

    * `chartOrigin_continuousOn` / `hWmeas₀_unconditional` — **W4b (the `hWmeas₀` discharge).**  The
      Lipschitz modulus ⟹ `LipschitzOnWith` ⟹ `ContinuousOn (z ↦ W₀ z) S`, threaded through
      `hWmeas₀_of_continuousOn` to deliver `hWmeas₀` — no longer carried as an opaque input, but reduced
      to the honest geometric side-conditions below (all TRUE facts of the chart, satisfiable, never a
      conclusion).

  ⚠ CARRIED (labelled hypotheses of W4 — genuine geometric facts of the honest chart, NOT exposed by
     the `.choose`-built tower, satisfiable, non-vacuous, never a conclusion):
    * `hRightInv : ∀ z ∈ S, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0` — the
      right-inverse (forward∘inverse = id at the origin) identity.  This is the J4-129-recovered
      `φ_z(W z 0) = 0` fact (the surjOn + germ pin), carried here as the labelled hypothesis.
    * the on-domain memberships `W₀ z ∈ ball 0 δ₀` (for the transfer lemma) and `‖W₀ z‖ ≤ ρ_K` (for the
      geodesic Grönwall's shared-velocity slot) on `S ⊆ K`.

  HONEST FIREWALL — W2 is the *nonlinear* two-solution Grönwall (the geodesic analogue of the linear
  `linODE_twopoint_diff_bound`); it closes the base-flow difference **UNCONDITIONALLY** on-domain, and
  hence `hWmeas₀` modulo ONLY the carried geometric side-conditions above.  It does NOT build
  Raychaudhuri (L3) nor `a₁ = R/6`.
-/
import QIQTH.FlowJointRegularity
import QIQTH.UniformFlowNondeg
import Mathlib

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.Geodesic QIQTH.ExpMap QIQTH.HeatResidualBound QIQTH.FlatHeatEquation
open scoped Topology BigOperators NNReal

namespace QIQTH.GeodesicGronwall

variable {n : ℕ}

set_option maxHeartbeats 1000000

/-! ### W1 — `geodesicField` is Lipschitz on any closed ball of the phase space. -/

/-- **W1 — `geodesicField_lipschitzOnWith_closedBall`.**  The geodesic phase-field `geodesicField g gi`
    (which is `C^∞` from `hC`, `contDiff_geodesicField`) is `LipschitzOnWith` some constant `L : ℝ≥0`
    on ANY closed ball `closedBall 0 R` of the phase space `Point n × Point n`.  The ball is CONVEX
    (`convex_closedBall`) and COMPACT (`isCompact_closedBall` — the phase space is finite-dimensional,
    hence proper); `ContDiffOn.exists_lipschitzOnWith` then supplies the Lipschitz constant.  The
    reusable Lipschitz engine feeding the nonlinear two-solution Grönwall below. -/
theorem geodesicField_lipschitzOnWith_closedBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (R : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (geodesicField g gi)
      (Metric.closedBall (0 : Point n × Point n) R) :=
  (contDiff_geodesicField g gi hC).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)

/-! ### W2 — the nonlinear two-solution Grönwall for the uniform geodesic tube. -/

/-- **W2 (★) — `uniformTube_twopoint_diff_bound`.**  The nonlinear two-solution Grönwall for the
    confined geodesic phase-flow.  There is a SINGLE uniform Lipschitz constant `L ≥ 0` over `K` such
    that for all `q, q' ∈ K` and all `w` with `‖w‖ ≤ ρ_K`, the two tubes through `(q, w)` and `(q', w)`
    (same velocity, different base) stay exponentially close on `[0,1]`:
        `dist (uniformFlowTube … q w t) (uniformFlowTube … q' w t) ≤ dist q q' · exp (L·t)`.
    Both tubes are confined to the fixed convex compact ball `closedBall 0 (M + C₀·ρ_K)` (`K` bounded by
    `M`, `C₀‖w‖`-confinement), on which `geodesicField` is `L`-Lipschitz (W1); the initial conditions
    are `(q, w)` and `(q', w)`, differing by `(q − q', 0)`; Mathlib's two-trajectory comparison
    `dist_le_of_trajectories_ODE_of_mem` (same autonomous field) closes it. -/
theorem uniformTube_twopoint_diff_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ K, ∀ q' ∈ K, ∀ w : Point n,
      ‖w‖ ≤ uniformFlowRadius g gi hC hK →
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (uniformFlowTube g gi hC hK q w t) (uniformFlowTube g gi hC hK q' w t)
          ≤ dist q q' * Real.exp (L * t) := by
  -- `K ⊆ closedBall 0 M`.
  obtain ⟨M, hM⟩ := (hK.isBounded).subset_closedBall (0 : Point n)
  set ρ := uniformFlowRadius g gi hC hK with hρ
  set C₀ := uniformFlowConst g gi hC hK with hC₀
  have hC₀0 : 0 ≤ C₀ := uniformFlowConst_nonneg g gi hC hK
  have hρ0 : 0 ≤ ρ := le_of_lt (uniformFlowRadius_pos g gi hC hK)
  set Rrad : ℝ := M + C₀ * ρ with hRrad
  -- W1 on the confinement ball.
  obtain ⟨L, hLip⟩ := geodesicField_lipschitzOnWith_closedBall g gi hC Rrad
  refine ⟨(L : ℝ), L.2, ?_⟩
  intro q hq q' hq' w hw t ht
  -- specs of both tubes.
  have hic := uniformFlowTube_spec_ic g gi hC hK q hq w hw
  have hode := uniformFlowTube_spec_ode g gi hC hK q hq w hw
  have hconf := uniformFlowTube_spec_conf g gi hC hK q hq w hw
  have hic' := uniformFlowTube_spec_ic g gi hC hK q' hq' w hw
  have hode' := uniformFlowTube_spec_ode g gi hC hK q' hq' w hw
  have hconf' := uniformFlowTube_spec_conf g gi hC hK q' hq' w hw
  -- membership of `Ico 0 1` (and `Icc 0 1`) inside `Ioo (-2) 2`.
  have hIco : ∀ s ∈ Set.Ico (0 : ℝ) 1, s ∈ Set.Ioo (-2 : ℝ) 2 := by
    intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hIcc : ∀ s ∈ Set.Icc (0 : ℝ) 1, s ∈ Set.Ioo (-2 : ℝ) 2 := by
    intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- confinement ⟹ both tubes live in `closedBall 0 Rrad`.
  have hbase : ‖((q, 0) : Point n × Point n)‖ ≤ M := by
    rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
    have := hM hq; rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hbase' : ‖((q', 0) : Point n × Point n)‖ ≤ M := by
    rw [Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)]
    have := hM hq'; rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hmem : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      uniformFlowTube g gi hC hK q w s ∈ Metric.closedBall (0 : Point n × Point n) Rrad := by
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := hconf s (Set.Ico_subset_Icc_self hs)
    calc ‖uniformFlowTube g gi hC hK q w s‖
        ≤ ‖((q, 0) : Point n × Point n)‖
            + ‖uniformFlowTube g gi hC hK q w s - ((q, 0) : Point n × Point n)‖ := by
          have := norm_add_le ((q, 0) : Point n × Point n)
            (uniformFlowTube g gi hC hK q w s - ((q, 0) : Point n × Point n))
          simpa using this
      _ ≤ M + C₀ * ‖w‖ := add_le_add hbase h1
      _ ≤ M + C₀ * ρ := by
          have : C₀ * ‖w‖ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hw hC₀0
          linarith
  have hmem' : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      uniformFlowTube g gi hC hK q' w s ∈ Metric.closedBall (0 : Point n × Point n) Rrad := by
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := hconf' s (Set.Ico_subset_Icc_self hs)
    calc ‖uniformFlowTube g gi hC hK q' w s‖
        ≤ ‖((q', 0) : Point n × Point n)‖
            + ‖uniformFlowTube g gi hC hK q' w s - ((q', 0) : Point n × Point n)‖ := by
          have := norm_add_le ((q', 0) : Point n × Point n)
            (uniformFlowTube g gi hC hK q' w s - ((q', 0) : Point n × Point n))
          simpa using this
      _ ≤ M + C₀ * ‖w‖ := add_le_add hbase' h1
      _ ≤ M + C₀ * ρ := by
          have : C₀ * ‖w‖ ≤ C₀ * ρ := mul_le_mul_of_nonneg_left hw hC₀0
          linarith
  -- continuity of both tubes on `Icc 0 1`.
  have hcont : ContinuousOn (uniformFlowTube g gi hC hK q w) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => ((hode s (hIcc s hs)).continuousAt).continuousWithinAt
  have hcont' : ContinuousOn (uniformFlowTube g gi hC hK q' w) (Set.Icc (0 : ℝ) 1) :=
    fun s hs => ((hode' s (hIcc s hs)).continuousAt).continuousWithinAt
  -- initial-condition distance.
  have haIC : dist (uniformFlowTube g gi hC hK q w 0) (uniformFlowTube g gi hC hK q' w 0)
      ≤ dist q q' := by
    rw [hic, hic', Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
  -- Mathlib two-trajectory comparison with the autonomous field `geodesicField`.
  have hbnd := dist_le_of_trajectories_ODE_of_mem
    (v := fun (_ : ℝ) (p : Point n × Point n) => geodesicField g gi p)
    (s := fun (_ : ℝ) => Metric.closedBall (0 : Point n × Point n) Rrad)
    (K := L) (a := 0) (b := 1)
    (f := uniformFlowTube g gi hC hK q w) (g := uniformFlowTube g gi hC hK q' w)
    (δ := dist q q')
    (fun s _ => hLip)
    hcont
    (fun s hs => (hode s (hIco s hs)).hasDerivWithinAt)
    hmem
    hcont'
    (fun s hs => (hode' s (hIco s hs)).hasDerivWithinAt)
    hmem'
    haIC
  have := hbnd t ht
  simpa [sub_zero] using this

/-! ### W3 — the base-point flow difference (position component). -/

/-- **W3 — `uniformFlowExp_base_diff_bound`.**  Projecting the two-solution Grönwall W2 at `t = 1` onto
    the position component (`‖p.1‖ ≤ ‖p‖`, `Prod.norm_mk`), the forward geodesic-flow endpoint map is
    Lipschitz in the BASE point at a fixed velocity:
        `‖uniformFlowExp … q w − uniformFlowExp … q' w‖ ≤ exp L · ‖q − q'‖`   (q, q' ∈ K, ‖w‖ ≤ ρ_K).
    This is exactly the base-flow residue `‖φ_{q'} w − φ_q w‖` isolated by the J4-149 transfer lemma —
    now CLOSED (`dist q q' = ‖q − q'‖`). -/
theorem uniformFlowExp_base_diff_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ q ∈ K, ∀ q' ∈ K, ∀ w : Point n,
      ‖w‖ ≤ uniformFlowRadius g gi hC hK →
        ‖uniformFlowExp g gi hC hK q w - uniformFlowExp g gi hC hK q' w‖
          ≤ Real.exp L * ‖q - q'‖ := by
  obtain ⟨L, hL0, hgron⟩ := uniformTube_twopoint_diff_bound g gi hC hK
  refine ⟨L, hL0, ?_⟩
  intro q hq q' hq' w hw
  have ht1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl _⟩
  have hd := hgron q hq q' hq' w hw 1 ht1
  -- position component: `‖(Y 1).1 − (Y' 1).1‖ ≤ ‖Y 1 − Y' 1‖`.
  have hproj : ‖uniformFlowExp g gi hC hK q w - uniformFlowExp g gi hC hK q' w‖
      ≤ dist (uniformFlowTube g gi hC hK q w 1) (uniformFlowTube g gi hC hK q' w 1) := by
    rw [uniformFlowExp_eq, uniformFlowExp_eq, dist_eq_norm, ← Prod.fst_sub, Prod.norm_def]
    exact le_max_left _ _
  calc ‖uniformFlowExp g gi hC hK q w - uniformFlowExp g gi hC hK q' w‖
      ≤ dist (uniformFlowTube g gi hC hK q w 1) (uniformFlowTube g gi hC hK q' w 1) := hproj
    _ ≤ dist q q' * Real.exp (L * 1) := hd
    _ = Real.exp L * ‖q - q'‖ := by rw [mul_one, dist_eq_norm]; ring

/-! ### W4 — the origin-chart Lipschitz modulus and the `hWmeas₀` discharge. -/

/-- **W4a — `chartOrigin_lipschitz_modulus`.**  Welding the base-flow difference W3 to the J4-149
    transfer lemma `chart_joint_velocity_modulus` and the right-inverse identity `φ_z (W z 0) = 0`, the
    origin chart `W₀ z := uniformInverseChart g gi hC hK z 0` is Lipschitz in the BASE on any subset
    `S ⊆ K` where the two carried geometric side-conditions hold:
        `‖W₀ z − W₀ z'‖ ≤ (C_inv · exp L) · ‖z − z'‖`.
    In the transfer bound `‖W₀ z − W₀ z'‖ ≤ C_inv·(‖φ_z(W z 0) − φ_{z'}(W z' 0)‖ + ‖φ_{z'}(W z' 0) −
    φ_z(W z' 0)‖)`, the right-inverse kills the first term (`‖0 − 0‖ = 0`) and W3 (at velocity `W z' 0`)
    bounds the second (`= ‖φ_z(W z' 0) − φ_{z'}(W z' 0)‖ ≤ exp L·‖z − z'‖`). -/
theorem chartOrigin_lipschitz_modulus (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ > (0 : ℝ), ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ {S : Set (Point n)}, S ⊆ K →
      (∀ z ∈ S, uniformInverseChart g gi hC hK z 0 ∈ Metric.ball (0 : Point n) δ₀) →
      (∀ z ∈ S, ‖uniformInverseChart g gi hC hK z 0‖ ≤ uniformFlowRadius g gi hC hK) →
      (∀ z ∈ S, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0) →
      ∀ z ∈ S, ∀ z' ∈ S,
        ‖uniformInverseChart g gi hC hK z 0 - uniformInverseChart g gi hC hK z' 0‖
          ≤ Λ * ‖z - z'‖ := by
  obtain ⟨δ₀, hδ₀, C_inv, hCinv0, htrans⟩ := chart_joint_velocity_modulus g gi hC hK
  obtain ⟨L, hL0, hbase⟩ := uniformFlowExp_base_diff_bound g gi hC hK
  refine ⟨δ₀, hδ₀, C_inv * Real.exp L, mul_nonneg hCinv0 (le_of_lt (Real.exp_pos _)), ?_⟩
  intro S hSK hball hnorm hRI z hz z' hz'
  set Wz := uniformInverseChart g gi hC hK z 0 with hWz
  set Wz' := uniformInverseChart g gi hC hK z' 0 with hWz'
  -- transfer lemma at `q := z`, `q' := z'`, `w := Wz`, `w' := Wz'`.
  have hT := htrans z (hSK hz) z' (hSK hz') Wz (hball z hz) Wz' (hball z' hz')
  -- right-inverse: `φ_z(Wz) = 0`, `φ_{z'}(Wz') = 0`.
  have hRIz : uniformFlowExp g gi hC hK z Wz = 0 := hRI z hz
  have hRIz' : uniformFlowExp g gi hC hK z' Wz' = 0 := hRI z' hz'
  -- first transfer term vanishes.
  have hterm1 : ‖uniformFlowExp g gi hC hK z Wz - uniformFlowExp g gi hC hK z' Wz'‖ = 0 := by
    rw [hRIz, hRIz', sub_zero, norm_zero]
  -- second transfer term = W3 at velocity `Wz'`.
  have hb := hbase z (hSK hz) z' (hSK hz') Wz' (hnorm z' hz')
  have hterm2 : ‖uniformFlowExp g gi hC hK z' Wz' - uniformFlowExp g gi hC hK z Wz'‖
      ≤ Real.exp L * ‖z - z'‖ := by
    rw [hRIz', zero_sub, norm_neg]
    -- `‖φ_z(Wz')‖ = ‖φ_z(Wz') − φ_{z'}(Wz')‖` since `φ_{z'}(Wz') = 0`.
    have hrw : uniformFlowExp g gi hC hK z Wz'
        = uniformFlowExp g gi hC hK z Wz' - uniformFlowExp g gi hC hK z' Wz' := by
      rw [hRIz', sub_zero]
    rw [hrw]; exact hb
  -- assemble.
  calc ‖Wz - Wz'‖
      ≤ C_inv * (‖uniformFlowExp g gi hC hK z Wz - uniformFlowExp g gi hC hK z' Wz'‖
          + ‖uniformFlowExp g gi hC hK z' Wz' - uniformFlowExp g gi hC hK z Wz'‖) := hT
    _ ≤ C_inv * (0 + Real.exp L * ‖z - z'‖) := by
        apply mul_le_mul_of_nonneg_left _ hCinv0
        exact add_le_add (le_of_eq hterm1) hterm2
    _ = (C_inv * Real.exp L) * ‖z - z'‖ := by ring

/-- **W4b — `chartOrigin_continuousOn`.**  The Lipschitz modulus W4a ⟹ `ContinuousOn` of the origin
    chart `z ↦ uniformInverseChart … z 0` on `S ⊆ K`, under the carried geometric side-conditions. -/
theorem chartOrigin_continuousOn (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {S : Set (Point n)} (hSK : S ⊆ K)
    (hball : ∀ z ∈ S, uniformInverseChart g gi hC hK z 0
      ∈ Metric.ball (0 : Point n) (chartOrigin_lipschitz_modulus g gi hC hK).choose)
    (hnorm : ∀ z ∈ S, ‖uniformInverseChart g gi hC hK z 0‖ ≤ uniformFlowRadius g gi hC hK)
    (hRI : ∀ z ∈ S, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0) :
    ContinuousOn (fun z : Point n => uniformInverseChart g gi hC hK z 0) S := by
  obtain ⟨Λ, hΛ0, hmod⟩ := (chartOrigin_lipschitz_modulus g gi hC hK).choose_spec.2
  have hlip : LipschitzOnWith Λ.toNNReal
      (fun z : Point n => uniformInverseChart g gi hC hK z 0) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz z' hz'
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal Λ hΛ0]
    exact hmod hSK hball hnorm hRI z hz z' hz'
  exact hlip.continuousOn

/-- **W4b (capstone) — `hWmeas₀_unconditional`.**  Threading the origin-chart `ContinuousOn` (W4b)
    through the J4-149 conditional discharge `hWmeas₀_of_continuousOn`, the carried consumer input
    `hWmeas₀` holds on any measurable `S ⊆ K` satisfying the geometric side-conditions:
        `∀ τ, AEStronglyMeasurable (z ↦ gaussDdim τ (W₀ z)) (volume.restrict S)`.
    So `hWmeas₀` is no longer an opaque input, but reduced to the honest (satisfiable, non-vacuous)
    geometric facts about the honest chart. -/
theorem hWmeas₀_unconditional (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    {S : Set (Point n)} (hS : MeasurableSet S) (hSK : S ⊆ K)
    (hball : ∀ z ∈ S, uniformInverseChart g gi hC hK z 0
      ∈ Metric.ball (0 : Point n) (chartOrigin_lipschitz_modulus g gi hC hK).choose)
    (hnorm : ∀ z ∈ S, ‖uniformInverseChart g gi hC hK z 0‖ ≤ uniformFlowRadius g gi hC hK)
    (hRI : ∀ z ∈ S, uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0) :
    ∀ τ : ℝ, AEStronglyMeasurable
      (fun z : Point n => gaussDdim τ (uniformInverseChart g gi hC hK z 0))
      (volume.restrict S) :=
  hWmeas₀_of_continuousOn g gi hC hK hS
    (chartOrigin_continuousOn g gi hC hK hSK hball hnorm hRI)

end QIQTH.GeodesicGronwall
