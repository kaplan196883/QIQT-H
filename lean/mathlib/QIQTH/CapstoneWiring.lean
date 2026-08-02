/-
  CapstoneWiring — J4-101: the WIRING CENSUS between the (now unconditional) `hEboundW` tower
  (`UniformChartRadius.gatedWitness_hEboundW_unconditional`) and the reduced true-kernel diagonal
  `a₁ = R/6` capstone (`TrueKernelA1.trueKernel_diagonal_a1_eq_R6_residual`), plus the CHEAPEST green
  wiring bricks that survive the census.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## The census verdict (see the module note at the bottom for the full per-hypothesis table).

  The residual capstone consumes an abstract `H : ℝ → Point n → Point n → ℝ` and asks, at the RNC
  origin and a fixed `t > 0`, for BOTH

    • `hEboundW` : `∀ τ p q, 0 < τ → |heatOp g gi H τ p q| ≤ C · baseKernelW 2 0 τ p q`, and
    • `hHdiag`  : `H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t 0`,   `1 ≤ N`.

  The `hunif` tower delivers `hEboundW` VERBATIM for the concrete gated van-Vleck witness
  `H_G := gatedKernel K S (globalCutoffParametrixWitness (vanVleck g) (transportCoeff …) a b
  (uniformInverseChart g gi hC hK))` — this is `gatedWitness_hEboundW_vanVleck` below, a pure
  specialization of the tower to the concrete DeWitt profile `Θ := vanVleck g`,
  `u := transportCoeff (transportOp (vanVleck g) g gi)`.

  BUT the same `H_G` has an **order-0** diagonal: unfolding the gate at the origin
  (`gatedWitness_diag_eval`) gives
      `H_G t 0 0 = heatParametrix 0 Θ u t 0 = heatParametrixFn 0 g (transportOp (vanVleck g) g gi) t 0`
  (`gatedWitness_diag_eval_vanVleck`), because `globalCutoffParametrixWitness` hard-codes the
  `N = 0` truncation `heatParametrix 0 Θ u`.  The capstone's `hHdiag` needs the **order-N** diagonal
  (`N ≥ 1`): `heatParametrixFn` at `N = 1` contains `gauss·(u₀ + t·u₁)` with `u₁(0) = R/6`
  generically nonzero (the capstone's `Finset.Ico 2 (N+1)` remainder only drops `u₂` and above), so
  the `hHdiag` equality is impossible for the `gauss·u₀`-only witness: `H_G` CANNOT satisfy `hHdiag`.

  ⚠ CENSUS CONCLUSION (binding; Sol-consult verdict incorporated).  The gated witness must be
  RE-INSTANTIATED at the MINIMAL `N = 1` parametrix (time-dependent amplitude `u₀ + t·u₁`), and the
  residual chain needs `parametrixResidualN 1` + `N = 1` variants of the τ-derivative/cutoff engines
  — a genuine order-1 re-plumb, NOT cheap wiring.  Its cost is CENSUSED in the module note at the
  bottom (which chain layers are N-generic vs hardcoded `N = 0`).  This file lands the two halves
  honestly and separately; `gatedWitness_diag_eval` is stated gate-generically so its `N = 1`
  sibling is a one-line variant once the `N = 1` witness exists.  No `sorry`, no new axioms, no
  vacuous hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.TrueKernelA1Reduced
import QIQTH.UniformChartRadius

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.TrueHeatKernel QIQTH.HeatParametrixAnsatz
open QIQTH.GaussianWidthTolerant QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### (1) The uniform inverse chart fixes the origin: `W₀(0) = 0`. -/

/-- **`uniformInverseChart_zero`.**  At the base point `q = 0 ∈ K`, the K-uniform inverse chart maps
    the origin to the origin: `uniformInverseChart g gi hC hK 0 0 = 0`.  This is the germ value of the
    left-inverse chart at `v = 0`, evaluated through `uniformFlowExp g gi hC hK 0 0 = 0`
    (`uniformFlowExp_zero`).  It is the fact that makes `Vmap 0 0 = 0` for the concrete tower chart,
    the hypothesis `gatedWitness_diag_eval` needs. -/
theorem uniformInverseChart_zero (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0 : (0 : Point n) ∈ K) :
    uniformInverseChart g gi hC hK 0 0 = 0 := by
  obtain ⟨δ₀, hδ₀, hspec⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨hgermC2, _⟩ := hspec 0 h0
  obtain ⟨hgerm, _⟩ := hgermC2 0 (by rw [norm_zero]; exact hδ₀)
  have h := hgerm.eq_of_nhds
  simp only [uniformFlowExp_zero g gi hC hK 0 h0] at h
  exact h

/-! ### (2) The gated-witness diagonal evaluation — the ORDER-0 identification (`hHdiag` at `N=0`). -/

/-- **`gatedWitness_diag_eval` — the gated cutoff-parametrix witness on the diagonal at the origin.**
    Where the origin lies in the base gate (`0 ∈ K`), in the spatial gate (`0 ∈ S 0`), and the inverse
    chart fixes the origin (`Vmap 0 0 = 0`), the gated global cutoff-parametrix witness collapses to the
    raw **order-0** parametrix at the centre:
        `gatedKernel K S (globalCutoffParametrixWitness Θ u a b Vmap) t 0 0 = heatParametrix 0 Θ u t 0`.
    Proof: unfold the gate (`gatedKernel_apply_of_mem`); `Vmap 0 0 = 0` sends both the cutoff argument
    and the parametrix argument to `0`; the radial cutoff is `1` at the centre (`radialCutoff_eq_one`,
    `rncRadialSq 0 = 0 ≤ a²`).  Genuine hypotheses (`0 < a < b`, gate memberships, chart-fixes-origin);
    none is the conclusion. -/
theorem gatedWitness_diag_eval (K : Set (Point n)) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Vmap : Point n → Point n → Point n) (t : ℝ)
    (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hV : Vmap 0 0 = 0) :
    gatedKernel K S (globalCutoffParametrixWitness Θ u a b Vmap) t 0 0
      = heatParametrix 0 Θ u t 0 := by
  rw [gatedKernel_apply_of_mem K S _ t hK0 hS0]
  simp only [globalCutoffParametrixWitness, hV]
  rw [radialCutoff_eq_one ha hab (by rw [rncRadialSq_zero]; positivity), one_mul]

/-- **`gatedWitness_diag_eval_vanVleck` — the concrete van-Vleck order-0 diagonal identification.**
    Specialising `gatedWitness_diag_eval` to the DeWitt profile `Θ := vanVleck g`,
    `u := transportCoeff (transportOp (vanVleck g) g gi)`, the gated van-Vleck witness on the diagonal is
    exactly the assembled parametrix function AT ORDER 0:
        `gatedKernel … t 0 0 = heatParametrixFn 0 g (transportOp (vanVleck g) g gi) t 0`.
    This is the capstone's `hHdiag` shape but with `N = 0` — the honest reachable order for the current
    tower witness (`heatParametrixFn_eq` is definitional; no `det g̃(0)=1` needed at order 0). -/
theorem gatedWitness_diag_eval_vanVleck (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (Vmap : Point n → Point n → Point n) (t : ℝ)
    (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (hV : Vmap 0 0 = 0) :
    gatedKernel K S (globalCutoffParametrixWitness (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b Vmap) t 0 0
      = heatParametrixFn 0 g (transportOp (vanVleck g) g gi) t 0 := by
  rw [gatedWitness_diag_eval K S (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi))
        a b ha hab Vmap t hK0 hS0 hV, heatParametrixFn_eq]

/-! ### (3) The `hEboundW` half — the tower specialised to the concrete van-Vleck DeWitt profile. -/

/-- **`gatedWitness_hEboundW_vanVleck` — `hEboundW` for the concrete gated van-Vleck witness.**  A pure
    specialisation of the unconditional `hEboundW` tower `gatedWitness_hEboundW_unconditional` to the
    concrete DeWitt profile `Θ := vanVleck g`, `u := transportCoeff (transportOp (vanVleck g) g gi)`.
    It carries EXACTLY the two profile inputs the tower demands — smoothness `hw0smooth` and
    RNC-flatness `hw0flat` of the folded leading coefficient `w₀ = (vanVleck g)^{−1/2}` (both genuine
    van-Vleck geometric facts) — and delivers the width-2 residual bound
        `|heatOp g gi H_G τ p q| ≤ B · baseKernelW 2 0 τ p q`
    for the concrete van-Vleck gated witness `H_G`.  This IS the residual capstone's `hEboundW` slot
    (with `H := H_G`, `C := B`).  NOT `a₁ = R/6`. -/
theorem gatedWitness_hEboundW_vanVleck (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a' b', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a' b'))
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a' b' => g y a' b')))
    (hgsymm : ∀ y a' b', g y a' b' = g y b' a')
    (hinvF : ∀ y a' b', (∑ σ, g y a' σ * gi y σ b') = if a' = b' then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) 0))
    (hw0flat : ∀ e, pd
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) 0) e (0 : Point n)
        = 0) :
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∃ S : Point n → Set (Point n),
      ∀ τ p q, 0 < τ →
        |heatOp g gi (gatedKernel K S
            (globalCutoffParametrixWitness (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK))) τ p q|
          ≤ B * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
  gatedWitness_hEboundW_unconditional g gi hg hC hK hgnd hgsymm hinvF hframeK
    (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) hw0smooth hw0flat

/-!
  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## FULL WIRING CENSUS — `trueKernel_diagonal_a1_eq_R6_residual` (`H := H_G`, `C := B`).

  For each hypothesis of the residual capstone, its status against the concrete gated van-Vleck
  witness `H_G` (order-0), classified as: [WIRING-EASY] · [WIRING-MEDIUM] · [ORDER-N REBUILD] ·
  [hDuhamel/Levi WALL] · [GENUINE GAUGE INPUT].

    • `hg`,`hg0`,`hgi`,`hΓ`,`hdg0`,`htr`,`hsrc`  — [GENUINE GAUGE INPUT].  RNC/metric-Hessian data
      for the ambient `g` at the origin (`g(0)=δ`, `Γ(0)=0`, `∂g(0)=0`, the `−⅔Ric` Hessian trace,
      transport-source smoothness).  Carried by the capstone; satisfiable for a genuine RNC metric; no
      wiring work.

    • `hEboundW` : `|heatOp g gi H_G τ p q| ≤ C·baseKernelW 2 0 τ p q`  — [WIRING-EASY, LANDED].
      Delivered VERBATIM by `gatedWitness_hEboundW_vanVleck` (the tower at the concrete van-Vleck
      profile), with `C := B`.  The former sole residue `huniformChart` is discharged upstream.

    • `hHdiag` : `H_G t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t 0`, `1 ≤ N`
      — [ORDER-N REBUILD].  `gatedWitness_diag_eval_vanVleck` proves this AT `N = 0`
      (`H_G t 0 0 = heatParametrixFn 0 …`).  For `N ≥ 1` it is FALSE for the current witness: the
      order-N diagonal carries the derived `transportCoeff₁(0)·t = (R/6)·t` term, absent from the
      order-0 `H_G`.  Requires `globalCutoffParametrixWitness` re-run with `heatParametrix N`.  This is
      the single obstruction to feeding both `hEboundW` and `hHdiag` from one witness.

    • `hInt` : `IterConvIntegrableW (heatOp g gi H_G) 2 0 C`  — [WIRING-MEDIUM].  Producible by
      `IterEMeasurable.iterConvIntegrableW_of_bound_baseMeas` from `hEboundW` (have it) + `hEzero`
      (heat-operator vanishing at `τ ≤ 0`) + `hEmeas` (joint strong measurability of `heatOp g gi H_G`).
      `hEmeas` is a genuine measurability carry for the piecewise (gate-indicator × smooth-profile)
      witness and its `deriv`/`laplaceBeltrami`; the gate `S q` is OPEN, so the indicators are
      measurable and the pieces continuous on the open gate — reachable but not a one-liner.

    • `hEzero` : `heatOp g gi H_G τ = 0` for `τ ≤ 0`  — [WIRING-MEDIUM].  For `n ≥ 1`,
      `gaussDdim τ x = 0` at `τ ≤ 0` (`heatKernel1D_of_nonpos`), so `H_G(τ,·,q) ≡ 0`, giving `Δ_g = 0`;
      the `∂_τ` slot is `0` for `τ < 0` (locally constant) and, at `τ = 0`, `0` via the junk-`deriv`
      convention (the right-hand profile blows up, so `H_G` is not differentiable there and `deriv` is
      `0`).  Fails at `n = 0` (empty Gaussian product `= 1`); needs a `1 ≤ n` side hypothesis.

    • `hDuhamel`, `hInter`  — [hDuhamel/Levi WALL].  The parametrix Duhamel output `(∂_t−Δ)(H*F)=F+E*F`
      and the tsum/heatConv interchange — the Levi-series analytic wall, not wiring (see the residual
      capstone's own module note).

    • `hDH`,`hDConv`,`hCH`,`hCConv`  — [WIRING-MEDIUM / near-diagonal regularity].  `t`- and
      `x`-regularity of `t ↦ H_G(t,0,0)` and of the convolution `heatConv H_G (leviSeries …)`; the
      `H_G` part is smooth near the diagonal (gate = neighbourhood of the origin, cutoff `≡ 1`, profile
      `C∞`), but the convolution parts ride on the Levi series and belong with the `hDuhamel` wall.

  NET.  `hEboundW` is LANDED for the concrete witness; the order-0 `hHdiag` is LANDED; the pair cannot
  be packaged into ONE `N ≥ 1` capstone witness without the order-N rebuild of the residual tower.
-/

end QIQTH.HeatResidualBound
