/-
  CConvLayerDischarge — J4-155: two F3-frontier bricks of the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It supplies two
  slots carried elsewhere in the campaign:

    ── ITEM 1 (LANDED) — `hdetz_general`.  `AmplitudeFamilyDischarge.amp_contDiffAt_general` carries
       the Riemannian positivity `hdetz : 0 < det (g (uniformInverseChart g gi hChr hK z 0))` at a
       GENERAL base `z`.  Here it is GENUINELY PROVED on a small ball around `0`:
         `∃ r>0, ∀ z ∈ K, ‖z‖ < r → 0 < det (g (uniformInverseChart g gi hChr hK z 0))`.
       Route: the RNC gauge `hg0` gives `det (g 0) = 1 > 0`; `z ↦ det (g y)` is continuous (matrix
       determinant is a polynomial in the continuous metric entries — `continuous_matrix` +
       `Continuous.matrix_det`), so `{y | 0 < det (g y)}` is an open nbhd of `0`; the inverse-chart
       displacement bound `chartW0_displacement` (`‖W₀ z + z‖ ≤ C_W‖z‖²`) gives
       `‖W₀ z‖ ≤ (1+C_W)‖z‖ → 0`, so shrinking `r` forces `W₀ z` into that nbhd.  NO Grönwall needed.

    ── ITEM 2 — the `hCConv` L1 layer.  `SpatialC2.hCConv_reduction` carries
         `L1 : ∃ u ∈ 𝓝 0, ∀ x ∈ u, HasFDerivAt (fun p => heatConv H F t p 0) (D x) x`
       (the FIRST spatial derivative of the singular space-time convolution under `∫₀ᵗ ∫`; the `s`-
       integral's `τ^{−1/2}`-domination is integrable, unlike the second derivative).  Two pieces:

         • `hConvDeriv_linewise` (★ PROVED) — the per-coordinate `HasDerivAt` of the SINGULAR (gap-
           free upper-limit `t`) convolution along the `i`-th coordinate line, obtained by moving
           `∂_w` under BOTH integrals via `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_-
           deriv_le` (mirroring `SecondOrderInterchange.line_pd_double_integral`, but returning the
           `HasDerivAt` and at `b = t`, using `heatConv A B t = heatConvFrozen A B t t`).  The engine
           accepts the `s`-dependent NON-constant integrable dominator (`bound : ℝ → ℝ`, interval-
           integrable), which is exactly the `C·(t−s)^{−1/2}` sliver bound.

         • `hCConv_L1_of_partialsContinuity` (honest reduction) — assembles the L1 `∃`-shape from the
           linewise family plus a LABELLED partials→FDeriv assembly carry (the standard fact that
           coordinate derivatives + their continuity give the Fréchet derivative — no single Mathlib
           lemma for a general `Fin n → ℝ` domain, so it is carried, not the conclusion).

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, never the conclusion).
    • The `s`-domination bundle of `hConvDeriv_linewise` (`snb`/`hFmeas`/`hFint`/`hF'meas`/`bound`/
      `hbdd`/`hbound`/`hdiff`) — genuine differentiation-under-∫ inputs, dischargeable from the C4b
      Gaussian/sliver bounds (the `EngineInstantiation` E1/E2 kernel facts).
    • The partials→FDeriv assembly `hAssembly` of `hCConv_L1_of_partialsContinuity` (needs continuity
      of the coordinate derivatives).

  NO `sorry`.  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InverseChartDisplacement
import QIQTH.SecondOrderInterchange

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatDuhamel
open scoped BigOperators Topology Interval

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### ITEM 1 — `hdetz_general`: Riemannian positivity of `det (g (W₀ z))` on a ball.
    ############################################################################### -/

/-- **★ ITEM 1 — `hdetz_general`.**  The Riemannian positivity carried by
    `AmplitudeFamilyDischarge.amp_contDiffAt_general` (its `hdetz` slot), GENUINELY PROVED on a small
    ball around the base `0`:  there is `r > 0` such that for every `z ∈ K` with `‖z‖ < r`,
      `0 < Matrix.det (g (uniformInverseChart g gi hChr hK z 0))`.
    Proof: `det (g ·)` is continuous (matrix determinant of the continuous metric entries), and equals
    `1 > 0` at `0` by the RNC gauge `hg0`; so `{y | 0 < det (g y)}` is an open nbhd of `0`.  The
    inverse-chart displacement bound `chartW0_displacement` gives `‖W₀ z + z‖ ≤ C_W‖z‖²`, hence
    `‖W₀ z‖ ≤ (1+C_W)‖z‖`, which is `< ε` once `‖z‖` is small enough (no Grönwall).  NOT `a₁ = R/6`. -/
theorem hdetz_general (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j) :
    ∃ r > (0 : ℝ), ∀ z ∈ K, ‖z‖ < r →
      0 < Matrix.det (g (uniformInverseChart g gi hChr hK z 0)) := by
  -- `det (g ·)` continuous; value `1` at `0` (RNC gauge).
  have hdmap_cont : Continuous (fun y : Point n => Matrix.det (g y)) :=
    (continuous_matrix (fun i j => (hg i j).continuous)).matrix_det
  have hgmat : (fun i j => g 0 i j) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    funext i j; exact hg0 i j
  have hd0 : Matrix.det (g (0 : Point n)) = 1 := by
    rw [show (g (0 : Point n)) = (1 : Matrix (Fin n) (Fin n) ℝ) from hgmat, Matrix.det_one]
  -- the open positivity nbhd of `0`, converted to a metric ball.
  have hopen : IsOpen {y : Point n | 0 < Matrix.det (g y)} :=
    isOpen_lt continuous_const hdmap_cont
  have h0mem : (0 : Point n) ∈ {y : Point n | 0 < Matrix.det (g y)} := by
    show 0 < Matrix.det (g (0 : Point n)); rw [hd0]; norm_num
  have hnhd : {y : Point n | 0 < Matrix.det (g y)} ∈ 𝓝 (0 : Point n) := hopen.mem_nhds h0mem
  rw [Metric.mem_nhds_iff] at hnhd
  obtain ⟨ε, hε, hball⟩ := hnhd
  -- inverse-chart displacement bound.
  obtain ⟨r₁, hr₁, C_W, hCW0, hdisp⟩ := chartW0_displacement g gi hChr hK
  have hCW1 : (0 : ℝ) < C_W + 1 := by linarith
  refine ⟨min r₁ (min 1 (ε / (C_W + 1))), lt_min hr₁ (lt_min one_pos (div_pos hε hCW1)),
    fun z hzK hzr => ?_⟩
  have hzr₁ : ‖z‖ < r₁ := lt_of_lt_of_le hzr (min_le_left _ _)
  have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hzr (le_trans (min_le_right _ _) (min_le_left _ _))
  have hzε : ‖z‖ < ε / (C_W + 1) :=
    lt_of_lt_of_le hzr (le_trans (min_le_right _ _) (min_le_right _ _))
  set W : Point n := uniformInverseChart g gi hChr hK z 0 with hWdef
  have hdispz : ‖W + z‖ ≤ C_W * ‖z‖ * ‖z‖ := hdisp z hzK hzr₁
  have hWn : ‖W‖ ≤ ‖z‖ + C_W * ‖z‖ * ‖z‖ := by
    calc ‖W‖ = ‖(W + z) - z‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖W + z‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ C_W * ‖z‖ * ‖z‖ + ‖z‖ := by linarith
      _ = ‖z‖ + C_W * ‖z‖ * ‖z‖ := by ring
  have hkey : ‖z‖ * (C_W + 1) < ε := (lt_div_iff₀ hCW1).mp hzε
  have hsq : C_W * ‖z‖ * ‖z‖ ≤ C_W * ‖z‖ := by
    nlinarith [mul_nonneg (mul_nonneg hCW0 (norm_nonneg z))
      (by linarith [hz1] : (0 : ℝ) ≤ 1 - ‖z‖)]
  have hWlt : ‖W‖ < ε := by nlinarith [hWn, hkey, hsq]
  have hWmem : W ∈ Metric.ball (0 : Point n) ε := by
    rw [Metric.mem_ball, dist_zero_right]; exact hWlt
  exact hball hWmem

/-! ###############################################################################
    ### ITEM 2 — the `hCConv` L1 layer.
    ############################################################################### -/

/-- **★ ITEM 2 (linewise) — `hConvDeriv_linewise`.**  The per-coordinate `HasDerivAt` of the SINGULAR
    space-time convolution `p ↦ heatConv H F t p 0` along the `i`-th coordinate line through `x`:
      `HasDerivAt (fun w => heatConv H F t (Function.update x i w) 0)
                  (∫ s in (0)..t, ∫ z, dH (t − s) x z · F s z 0) (x i)`.
    Since `heatConv A B t = heatConvFrozen A B t t` on the diagonal, the frozen upper-limit `b = t`,
    and `∂_w` moves under BOTH integrals via `intervalIntegral.hasDerivAt_integral_of_dominated_loc_-
    of_deriv_le` (the same engine as `SecondOrderInterchange.line_pd_double_integral`, but the singular
    upper limit is admissible because the `s`-dominator `bound : ℝ → ℝ` is NON-constant, interval-
    integrable — the `C·(t−s)^{−1/2}` sliver bound with `∫₀ᵗ (t−s)^{−1/2} = 2√t`).  All differentiation-
    under-∫ inputs are carried; none is the conclusion.  NOT `a₁ = R/6`. -/
theorem hConvDeriv_linewise (H dH F : ℝ → Point n → Point n → ℝ)
    (t : ℝ) (i : Fin n) (x : Point n)
    (snb : Set ℝ) (hsnb : snb ∈ 𝓝 (x i))
    (hFmeas : ∀ w, AEStronglyMeasurable
      (fun s => ∫ z, H (t - s) (Function.update x i w) z * F s z 0)
      (volume.restrict (Set.uIoc 0 t)))
    (hFint : IntervalIntegrable
      (fun s => ∫ z, H (t - s) x z * F s z 0) volume 0 t)
    (hF'meas : AEStronglyMeasurable
      (fun s => ∫ z, dH (t - s) x z * F s z 0)
      (volume.restrict (Set.uIoc 0 t)))
    (bound : ℝ → ℝ) (hbdd : IntervalIntegrable bound volume 0 t)
    (hbound : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
      ‖∫ z, dH (t - s) (Function.update x i w) z * F s z 0‖ ≤ bound s)
    (hdiff : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 t → ∀ w ∈ snb,
      HasDerivAt (fun w => ∫ z, H (t - s) (Function.update x i w) z * F s z 0)
        (∫ z, dH (t - s) (Function.update x i w) z * F s z 0) w) :
    HasDerivAt (fun w => heatConv H F t (Function.update x i w) 0)
      (∫ s in (0)..t, ∫ z, dH (t - s) x z * F s z 0) (x i) := by
  have hy : Function.update x i (x i) = x := Function.update_eq_self i x
  have hFint' : IntervalIntegrable
      (fun s => ∫ z, H (t - s) (Function.update x i (x i)) z * F s z 0) volume 0 t := by
    rw [hy]; exact hFint
  have hF'meas' : AEStronglyMeasurable
      (fun s => ∫ z, dH (t - s) (Function.update x i (x i)) z * F s z 0)
      (volume.restrict (Set.uIoc 0 t)) := by rw [hy]; exact hF'meas
  have hHD := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := 0) (b := t) (x₀ := x i) (s := snb) (bound := bound)
      (F := fun w s => ∫ z, H (t - s) (Function.update x i w) z * F s z 0)
      (F' := fun w s => ∫ z, dH (t - s) (Function.update x i w) z * F s z 0)
      hsnb (Filter.Eventually.of_forall hFmeas) hFint' hF'meas' hbound hbdd hdiff
  have hgoal : HasDerivAt
      (fun w => ∫ s in (0)..t, ∫ z, H (t - s) (Function.update x i w) z * F s z 0)
      (∫ s in (0)..t, ∫ z, dH (t - s) (Function.update x i (x i)) z * F s z 0) (x i) := hHD.2
  rw [hy] at hgoal
  simpa only [heatConv] using hgoal

/-- **ITEM 2 (assembly) — `hCConv_L1_of_partialsContinuity`.**  The exact L1 `∃`-shape carried by
    `SpatialC2.hCConv_reduction`
      `∃ u ∈ 𝓝 0, ∀ x ∈ u, HasFDerivAt (fun p => heatConv H F t p 0) (D x) x`
    assembled HONESTLY from two inputs on a common field nbhd `u ∋ 0`:
      • `hlin` — the per-coordinate `HasDerivAt` family (each instance = `hConvDeriv_linewise`, with
        `(D x) (Pi.single i 1)` the `i`-th coordinate derivative value);
      • `hAssembly` — the LABELLED partials→FDeriv assembly: given the coordinate derivatives at `x`,
        their (continuity-backed) assembly into the Fréchet derivative `D x`.  There is no single
        Mathlib lemma producing `HasFDerivAt` from coordinate derivatives on a general `Fin n → ℝ`
        domain, so this standard fact is carried, not proved here; it is satisfiable (continuity of
        the coordinate derivatives) and never the (global `∃`) conclusion.
    NOT `a₁ = R/6`. -/
theorem hCConv_L1_of_partialsContinuity (H F : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (D : Point n → (Point n →L[ℝ] ℝ))
    (u : Set (Point n)) (hu : u ∈ 𝓝 (0 : Point n))
    (hlin : ∀ x ∈ u, ∀ i : Fin n,
      HasDerivAt (fun w => heatConv H F t (Function.update x i w) 0)
        ((D x) (Pi.single i (1 : ℝ))) (x i))
    (hAssembly : ∀ x ∈ u,
      (∀ i : Fin n, HasDerivAt (fun w => heatConv H F t (Function.update x i w) 0)
        ((D x) (Pi.single i (1 : ℝ))) (x i)) →
      HasFDerivAt (fun p => heatConv H F t p 0) (D x) x) :
    ∃ u ∈ 𝓝 (0 : Point n), ∀ x ∈ u, HasFDerivAt (fun p => heatConv H F t p 0) (D x) x :=
  ⟨u, hu, fun x hx => hAssembly x hx (hlin x hx)⟩

end QIQTH.HeatResidualBound

section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms hdetz_general
#print axioms hConvDeriv_linewise
#print axioms hCConv_L1_of_partialsContinuity
end AxiomChecks
