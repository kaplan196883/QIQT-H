/-
  UniformNearEngine — J4-84: making the NEAR ENGINE uniform over the compact base set `K`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## The firewall this file addresses.

  J4-83 (`UniformResidualPacket.lean`) refactored the cutoff-residual producer into the
  construction-independent `cutoffResidual_bound_from_packet`, which chains the NEAR engine
  `near_uncutResidual_gaussianWide_ball_C3` (`NearResidualC3.lean:129`) with the cutoff engine
  `cutoffResidual_global_gaussianWide_bound_C2` (`CutoffResidualFiniteReg.lean:73`).  Its deep firewall:
  the near engine `near_uncutResidual_gaussianWide_ball_C3` returns a PER-`q` radius `b = ρ/2`, because it
  extracts `ρ` INTERNALLY (via `eventually_nhds_zero_ball` inside `residualN0_local_baseKernelW_slice_C3`)
  from the `∀ᶠ v in 𝓝 0` residual Gaussian bound `residualN0_gaussian_bound_C3`.  The near constant
  `C = (1 + 32·n²·M·W + L)·(√2)ⁿ` is already ABSTRACT (explicit in the passed `M`,`W`,`L`); only the RADIUS
  is internally chosen.

  ## N1 census — internally-chosen vs abstract inputs of the near engine (`…_ball_C3`).

  Following the chain `near_uncutResidual_gaussianWide_ball_C3`
    → `residualN0_local_baseKernelW_slice_C3` = `residualBound_local_baseKernelW ht (residualN0_gaussian_bound_C3 …)`
    → `residualN0_gaussian_bound_C3` produces `∀ᶠ v in 𝓝 0, |parametrixResidualN 0 …| ≤ C·gaussDdimWide`
    → `residualBound_local_baseKernelW` = `eventually_nhds_zero_ball` (the RADIUS chooser):

    • ABSTRACT (already passed in, uniform if their sources are uniform):
        the constant `C = (1 + 32·n²·M·W + L)·(√2)ⁿ`, explicit in `M`,`W`,`L`;
        the whole RNC van-Vleck jet-at-`0` package (`hg`/`hgiC`/`hCd`/`hw0` regularity, `hg0`/`hgi0`/`hdg0`/
        `hdgi0`/`hΓ0`/`hsymm`/`hinv`/`hgauge`/`hw0flat`/`hw0hessRicci` gauge/2-jet).

    • INTERNALLY CHOSEN (the per-`q` firewall):
        the RADIUS `ρ` (hence `b = ρ/2`) — extracted by `eventually_nhds_zero_ball` from the intersection
        of the eventual sets of `residualLeading_gaussian_bound_C3` (the off-diagonal little-`o` radius,
        driven by `totalRadialO1_coeff_isLittleO_C3`), `residualQuadratic_gaussian_bound`, `hlap`, and the
        `w₀ ∈ C²` germ.  NONE of these expose an explicit radius; the near engine sees only `∀ᶠ`.

  So the near engine is NOT already packet-parametrized by an abstract radius: it internally chooses `ρ`.
  Per the J4-83 recipe (N2), we REFACTOR it — copy the ball-conversion core, replace the internal radius
  choose by an ABSTRACT explicit-radius residual-bound packet field.

  ## Landed here (green; NO `sorry`, NO new axioms, NO `expRho` in statements, NO vacuous hypotheses).

  * `near_uncutResidual_gaussianWide_ball_from_packet` (N2) — the CONSTRUCTION-INDEPENDENT near engine:
    over ANY metric/inverse fields `g`/`gi`, from an EXPLICIT-radius residual Gaussian bound
    `hRes : ∀ v, ‖v‖ < ρ → |parametrixResidualN 0 g gi Θ u t v| ≤ C·gaussDdimWide t v` (`ρ > 0`),
    produce the `hEnear` shape `∃ b > 0, ∀ w, rncRadialSq w ≤ b² → |∂ₜH − Δ_g H| ≤ C·gaussDdimWide t w`
    (`b = ρ/2`).  This is `…_ball_C3`'s ball-conversion core with the internal radius choose replaced by
    the packet field `hRes`.

  * `near_uncutResidual_gaussianWide_ball_C3_viaPacket` — SANITY: the abstract packet IS satisfiable by
    the real van-Vleck jet data.  Re-derives the `…_ball_C3` conclusion (with the SHARPER constant
    `1 + 32·n²·M·W + L`, no `(√2)ⁿ` round-trip) by producing `hRes` from `residualN0_gaussian_bound_C3` +
    `eventually_nhds_zero_ball` and feeding `from_packet`.

  * `near_uncutResidual_uniform` (N3) — THE NEAR ENGINE MADE UNIFORM: given a UNIFORM explicit-radius
    residual Gaussian bound over `K` (ONE `ρ_u`, ONE `C`, `∀ q ∈ K`), the near output is uniform with the
    SINGLE outer radius `b = ρ_u/2` and constant `C` for every `q ∈ K`.  This discharges the near engine's
    OWN per-`q` behaviour (the radius halving + `rncRadialSq ≤ b² ⟹ ‖·‖ ≤ b` ball conversion), reducing
    the full uniform `hEnear` to the SINGLE remaining input — the uniform residual bound (the firewall
    below), exactly as J4-83 reduced the cutoff producer to the near packet.

  ## FIREWALLED (exact open statements; the residual-side deep wall + the cutoff-B uniformity).

  (F-res) THE UNIFORM RESIDUAL GAUSSIAN BOUND over `K` — the hypothesis `near_uncutResidual_uniform`
  consumes:
      `∃ ρ_u > 0, ∃ C ≥ 0, ∀ q ∈ K, ∀ v, ‖v‖ < ρ_u →
         |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) Θ u t v| ≤ C·gaussDdimWide t v`.
  Its open residue is the UNIFORM version of `residualN0_gaussian_bound_C3`: term (2) is already uniform
  (`uniformFlowPullbackMetricInv_dev_uniform`, J4-82, gives ONE `M`/`r₀`; `w₀ = foldedCoeff Θ u 0` is
  `q`-independent, so `W` is uniform), but term (1) needs the UNIFORM little-`o` of `totalRadialO1_coeff`
  (a uniform C³ Taylor remainder of the off-diagonal cancellation over `K` — absent) and term (3) the
  uniform Laplacian bound `L`.  This is the C³ Taylor-remainder wall.

  (F-cut) THE UNIFORM CUTOFF ASSEMBLY (N4).  Feeding `near_uncutResidual_uniform`'s uniform `hEnear` to
  `cutoffResidual_global_gaussianWide_bound_C2` per `q` yields, for each `q`, a bound with
  `B_q = C + Mann·Kc2 + 2·n²·Kg·Kc1·Mann·(8/a²)`.  Here `Mann` (from `parametrixH_annulus_bounds`, on the
  `q`-INDEPENDENT `heatParametrix 0 Θ u t`) and `Kc1` (cutoff-derivative bound) are `q`-independent; the
  only `q`-dependent pieces are `Kg` (`|g̃⁻¹_q|` on the annulus) and `Kc2` (`|Δ_g̃_q χ|` on the annulus).
  With UNIFORM annulus suppliers `∀ a b, ∃ Kg, ∀ q ∈ K, …` and `∀ a b, ∃ Kc2, ∀ q ∈ K, …` the whole `B`
  is uniform, but the existing engine returns `B` EXISTENTIALLY (hiding the formula), so a uniform `B`
  needs an explicit-`B` cutoff-engine variant.  Left as the F-cut wall.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.NearResidualC3
import QIQTH.ResidualN0GaussianC3
import QIQTH.ParametrixResidualBaseKernel
import QIQTH.UniformResidualPacket

open Finset MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation QIQTH.HeatKernelA1
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatParametrixError
open QIQTH.RadialDistance QIQTH.ResidueBound
open QIQTH.GaussianWidthTolerant QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### N2 — the construction-independent near engine (abstract explicit-radius residual packet). -/

/-- **★ J4-84 (N2) — THE NEAR ENGINE, CONSTRUCTION-INDEPENDENT (from an explicit-radius residual
    packet).**  Over ANY abstract metric field `g` with inverse `gi` and heat profiles `Θ`/`u`, from an
    EXPLICIT-radius near residual Gaussian bound
        `hRes : ∀ v, ‖v‖ < ρ → |parametrixResidualN 0 g gi Θ u t v| ≤ C · gaussDdimWide t v`   (`ρ > 0`),
    we obtain the `hEnear` shape at outer radius `b = ρ/2`:
        `∃ b > 0, ∀ w, rncRadialSq w ≤ b² →
           |∂ₜ(heatParametrix 0 Θ u · t)(w) − Δ_g(heatParametrix 0 Θ u t)(w)| ≤ C · gaussDdimWide t w` .
    This is `near_uncutResidual_gaussianWide_ball_C3`'s ball-conversion CORE (`rncRadialSq w ≤ (ρ/2)² ⟹
    ‖w‖ ≤ ρ/2 < ρ`, via `norm_le_rncRadial`) with the INTERNAL radius choose (`eventually_nhds_zero_ball`
    inside the slice) replaced by the packet field `hRes`.  `parametrixResidualN 0` unfolds definitionally
    to `∂ₜH − Δ_g H`.  No `expRho`; NOT `a₁ = R/6`. -/
theorem near_uncutResidual_gaussianWide_ball_from_packet
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {t : ℝ} (C ρ : ℝ) (hρ : 0 < ρ)
    (hRes : ∀ v : Point n, ‖v‖ < ρ →
      |parametrixResidualN 0 g gi Θ u t v| ≤ C * gaussDdimWide t v) :
    ∃ b : ℝ, 0 < b ∧
      ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |deriv (fun s => heatParametrix 0 Θ u s w) t
            - laplaceBeltrami g gi (heatParametrix 0 Θ u t) w|
          ≤ C * gaussDdimWide t w := by
  refine ⟨ρ / 2, by linarith, fun w hw => ?_⟩
  -- (rnc-ball → norm-ball): `rncRadialSq w ≤ (ρ/2)²` ⟹ `‖w‖ ≤ ρ/2 < ρ`.
  have hb0 : (0 : ℝ) ≤ ρ / 2 := by linarith
  have hnw : ‖w‖ < ρ := by
    have h1 : ‖w‖ ≤ rncRadial w := norm_le_rncRadial w
    have h2 : rncRadial w ≤ ρ / 2 := by
      rw [rncRadial]
      calc Real.sqrt (rncRadialSq w)
          ≤ Real.sqrt ((ρ / 2) ^ 2) := Real.sqrt_le_sqrt hw
        _ = ρ / 2 := by rw [Real.sqrt_sq hb0]
    linarith
  -- packet field on the norm-ball; unfold `parametrixResidualN 0` = `∂ₜH − Δ_g H`.
  have hs := hRes w hnw
  simpa only [parametrixResidualN] using hs

/-- **SANITY — the abstract packet is satisfiable by the real van-Vleck jet data.**  Re-derives the
    `near_uncutResidual_gaussianWide_ball_C3` conclusion (with the SHARPER constant
    `1 + 32·n²·M·W + L`, dropping the `(√2)ⁿ` base-kernel round-trip of the original) by producing the
    explicit-radius residual packet `hRes` from `residualN0_gaussian_bound_C3` +
    `eventually_nhds_zero_ball`, then feeding `near_uncutResidual_gaussianWide_ball_from_packet`.  Every
    hypothesis is the genuine van-Vleck jet/RNC/analytic-bound package of the near engine — verbatim,
    load-bearing, none vacuous.  NOT `a₁ = R/6`. -/
theorem near_uncutResidual_gaussianWide_ball_C3_viaPacket
    (g gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hg : ∀ a b, ContDiffAt ℝ 2 (fun y => g y a b) 0)
    (hgiC : ∀ i j, ContDiffAt ℝ 2 (fun y => gi y i j) 0)
    (hCd : ∀ a b c, ContDiffAt ℝ 2 (fun y => christoffel g gi a b c y) 0)
    (hw0 : ContDiffAt ℝ 3 (foldedCoeff Θ u 0) 0)
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi0 : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hdgi0 : ∀ i j e, pd (fun y => gi y i j) e (0 : Point n) = 0)
    (hΓ0 : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hsymm : ∀ y a b, g y a b = g y b a)
    (hinv : ∀ y i j, (∑ σ, gi y i σ * g y σ j) = if i = j then 1 else 0)
    (hgauge : ∀ i a b c, pd (fun y => christoffel g gi i b c y) a 0
        + pd (fun y => christoffel g gi i c a y) b 0
        + pd (fun y => christoffel g gi i a b y) c 0 = 0)
    (hw0flat : ∀ e, pd (foldedCoeff Θ u 0) e (0 : Point n) = 0)
    (hw0hessRicci : ∀ a b : Fin n,
        pd (fun y => pd (foldedCoeff Θ u 0) b y) a (0 : Point n)
          + pd (fun y => pd (foldedCoeff Θ u 0) a y) b 0
        = - ((1 / 3) * ricci g gi a b 0
             - (1 / 2) * ((∑ i, pd (fun y => christoffel g gi a i i y) b 0)
                        + (∑ i, pd (fun y => christoffel g gi b i i y) a 0)))
            * foldedCoeff Θ u 0 0)
    {t : ℝ} (ht : 0 < t) (M W L : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hdev : ∀ᶠ v in nhds (0 : Point n),
      ∀ i j, |gi v i j - (if i = j then (1 : ℝ) else 0)| ≤ M * rncRadialSq v)
    (hw0bd : ∀ᶠ v in nhds (0 : Point n), |foldedCoeff Θ u 0 v| ≤ W)
    (hlap : ∀ᶠ v in nhds (0 : Point n),
      |laplaceBeltrami g gi (foldedCoeff Θ u 0) v| ≤ L) :
    ∃ b : ℝ, 0 < b ∧
      ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |deriv (fun s => heatParametrix 0 Θ u s w) t
            - laplaceBeltrami g gi (heatParametrix 0 Θ u t) w|
          ≤ (1 + 32 * (n : ℝ) ^ 2 * M * W + L) * gaussDdimWide t w := by
  -- the residual Gaussian bound (finite regularity), then promote `∀ᶠ` to an explicit ρ-ball.
  obtain ⟨ρ, hρ, hRes⟩ :=
    eventually_nhds_zero_ball
      (residualN0_gaussian_bound_C3 g gi Θ u hg hgiC hCd hw0 hg0 hgi0 hdg0 hdgi0 hΓ0
        hsymm hinv hgauge hw0flat hw0hessRicci ht M W L hM hW hdev hw0bd hlap)
  exact near_uncutResidual_gaussianWide_ball_from_packet g gi Θ u
    (1 + 32 * (n : ℝ) ^ 2 * M * W + L) ρ hρ hRes

/-! ### N3 — the near engine MADE UNIFORM over the compact base set `K`. -/

/-- **★ J4-84 (N3) — THE NEAR ENGINE, UNIFORM OVER `K`.**  Given a UNIFORM explicit-radius near residual
    Gaussian bound over `K` — ONE radius `ρ_u > 0`, ONE constant `C`, valid for EVERY `q ∈ K` on the
    `uniformFlowExp` pullback metric `g̃_q = uniformFlowPullbackMetric g gi hC hK q` and its genuine
    inverse `g̃⁻¹_q = uniformFlowPullbackMetricInv g gi hC hK q` —
        `hResU : ∀ q ∈ K, ∀ v, ‖v‖ < ρ_u → |parametrixResidualN 0 g̃_q g̃⁻¹_q Θ u t v| ≤ C·gaussDdimWide`,
    the near-engine output is UNIFORM: the SINGLE outer radius `b = ρ_u/2` and the SINGLE constant `C`
    give the `hEnear` bound for every `q ∈ K`:
        `∃ b > 0, ∀ q ∈ K, ∀ w, rncRadialSq w ≤ b² →
           |∂ₜH(w) − Δ_g̃_q(heatParametrix 0 Θ u t)(w)| ≤ C·gaussDdimWide t w` .
    This is the per-`q` ball-conversion core `near_uncutResidual_gaussianWide_ball_from_packet`, applied
    with the SHARED radius `ρ_u`, so the produced `b = ρ_u/2` is one-and-the-same across `K`.  This
    DISCHARGES the near engine's own per-`q` firewall (the internal radius halving + `rncRadialSq ≤ b² ⟹
    ‖·‖ ≤ b` conversion), reducing the uniform `hEnear` to the SINGLE input `hResU` (the F-res wall).
    `hResU` is genuine (a real residual bound, satisfiable, not the conclusion — it lives on the norm-ball
    `‖v‖ < ρ_u`, the conclusion on the `rncRadialSq ≤ (ρ_u/2)²` sub-ball with an existential `b`); NO
    `expRho` in the statement.  NOT `a₁ = R/6`. -/
theorem near_uncutResidual_uniform
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {t : ℝ} (C ρ_u : ℝ) (hρ_u : 0 < ρ_u)
    (hResU : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
      |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u t v|
        ≤ C * gaussDdimWide t v) :
    ∃ b : ℝ, 0 < b ∧
      ∀ q ∈ K, ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |deriv (fun s => heatParametrix 0 Θ u s w) t
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 0 Θ u t) w|
          ≤ C * gaussDdimWide t w := by
  refine ⟨ρ_u / 2, by linarith, fun q hq w hw => ?_⟩
  -- SHARED radius: `b = ρ_u/2` is the same for every `q`.  Ball conversion `rncRadialSq w ≤ (ρ_u/2)²`.
  have hb0 : (0 : ℝ) ≤ ρ_u / 2 := by linarith
  have hnw : ‖w‖ < ρ_u := by
    have h1 : ‖w‖ ≤ rncRadial w := norm_le_rncRadial w
    have h2 : rncRadial w ≤ ρ_u / 2 := by
      rw [rncRadial]
      calc Real.sqrt (rncRadialSq w)
          ≤ Real.sqrt ((ρ_u / 2) ^ 2) := Real.sqrt_le_sqrt hw
        _ = ρ_u / 2 := by rw [Real.sqrt_sq hb0]
    linarith
  have hs := hResU q hq w hnw
  simpa only [parametrixResidualN] using hs

end QIQTH.HeatResidualBound
