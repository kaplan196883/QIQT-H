/-
  BaseSlotTransportBallLocal — J4-939: the BALL-LOCAL `∘V` transport that closes the AMPLITUDE half of
  junction piece (3)'s transport for `hCensusBound`.  J4-932's `transported_ratio_regularity` demands a
  GLOBALLY bounded + globally Lipschitz weight `P` (`∀ z, |P z| ≤ M_P` and `∀ x y, |P x − P y| ≤ …`),
  but the CONCRETE census weight `amp·F` produced by J4-938
  (`CensusAmpConcreteRegularity.census_ampF_ratio_regularity`) is only BALL-LOCALLY bounded + Lipschitz
  (on `ball 0 ρ`, not on all of `ℝⁿ`).  THIS FILE supplies the ball-local transport variant — a close
  MECHANICAL adaptation of J4-932's proof (the SAME radius-shrinking `σ = min σ0 (rQ/(L_V+1))` that
  already keeps `V`'s image inside the weight's ball of validity) — and composes it with J4-938's
  concrete `q₁ = (amp·F)/|det|` and `q₂ = (Cfield·F)/|det|` to close the AMPLITUDE half of the transport.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure ANALYSIS-INFRASTRUCTURE brick.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable / conclusion-in-disguise hypothesis, no existing banked file edited.

  ## THE KEY OBSERVATION (why this is essentially free from banked machinery).  J4-932's own image-ball
  bookkeeping `σ = min σ0 (rQ/(L_V+1))` was ALREADY chosen precisely so that `V` maps the image ball
  `ball 0 σ` INTO the base ball `ball 0 rQ` (`‖V w‖ ≤ L_V ‖w‖`, `V 0 = 0`).  Nothing in that argument
  used global validity of the weight — only validity of the weight ON `ball 0 rQ` (the base ball `V`'s
  image lands in).  So relaxing J4-932's global `P`-hypotheses to BALL-LOCAL ones (`∀ z ∈ ball 0 rQ …`)
  is a verbatim adaptation: the `hmaps` step is unchanged, and the bound / Lipschitz steps consume the
  weight only at points `V w ∈ ball 0 rQ`.

  ## WHAT LANDS (all conditional on `hbaseC2 : ContDiffAt ℝ 2 Wbv 0`, the J4-930/931 residual).
    • `transport_ballLocal_regularity` — ★★ the GENERIC ball-local `∘V` transport: for ANY weight `Q`
        bounded (`M_Q`) + pairwise-Lipschitz (`L_Q`) ONLY on a base ball `ball 0 rQ`, the transported
        `w ↦ Q (V w)` is bounded (`M_Q`) + pairwise-Lipschitz (`L_Q·L_V`) on an image ball `ball 0 σ`,
        with `V 0 = 0` and `V` mapping `ball 0 σ` into `ball 0 rQ`.
    • `transported_ratio_regularity_ballLocal` — ★★ the BALL-LOCAL analogue of J4-932's
        `transported_ratio_regularity`: for ANY BALL-LOCALLY (on `ball 0 rP`) bounded + Lipschitz weight
        `P`, the transported ratio `w ↦ P (V w) / |det (fderiv Wbv (V w))|` is bounded (`2 M_P`) +
        pairwise-Lipschitz on an image ball.  (J4-932 required GLOBAL `P`; this is the drop-in ball-local
        replacement.)  Route: `det_fderiv_regularity_bundle` (J4-931) + `ratio_abs_lipschitzOn` (J4-925)
        on the base ball, then `transport_ballLocal_regularity`.
    • `census_ampF_transported_ratio_regularity` — ★★ THE CONCRETE q₁ TRANSPORTED: composing J4-938's
        `census_ampF_ratio_regularity` with the generic transport, `w ↦ (chartFieldAmp … τ (V w) 0 ·
        F0 (V w)) / |det (fderiv Wbv (V w))|` is bounded + pairwise-Lipschitz on an image ball — the
        AMPLITUDE-half of piece (3)'s `∘V` transport, with the amplitude concrete and only `F0` carried.
    • `census_CfieldF_transported_ratio_regularity` — ★★ the same for q₂ (`censusAmpTauDeriv · F0`).
    • `transport_ballLocal_slot_satisfiable` — non-vacuity of the ball-local weight slot (TEETH:
        `cos‖·‖`, bounded but genuinely varying, Lipschitz `1`, on `ball 0 1`).

  ## HONEST STATUS.  The AMPLITUDE half of junction piece (3)'s `∘V` transport is now CLOSED (the
  ball-local variant J4-932 lacked, composed with J4-938's concrete `amp·F`/`Cfield·F` ratio), modulo
  the honest residual `hbaseC2` (⟸ `hT0`).  What REMAINS for `hCensusBound`/`hCross`:  the F-factor's
  own ball-local bounded+Lipschitz regularity (the `leviSeries` carry, downstream of Ebound/heatConv —
  the `{hDuhamel,hDConv,hCConv}`-family input, NOT attempted here), `hbaseC2` itself, and piece (6)
  [`Bball + tail ≤ C_far·(u−s)^{−1/2}` rate absorption].  `hDuhamel`/`hDConv`/`hCConv` remain carried.
  `a₁ = R/6` remains CONDITIONAL on `{hDuhamel, hDConv, hCConv}`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.BaseSlotInverseChartLipschitz
import QIQTH.CensusAmpConcreteRegularity

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.RadialDistance
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped Topology BigOperators

namespace QIQTH.BaseSlotTransportBallLocal

open QIQTH.HeatResidualBound QIQTH.CensusTauDerivGateSplit QIQTH.BaseSlotDetRegularity
open QIQTH.BaseSlotInverseChartLipschitz QIQTH.CensusAmpConcreteRegularity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the GENERIC ball-local `∘V` transport (obstruction (iii), ball-local).
    ############################################################################### -/

/-- **★★ `transport_ballLocal_regularity` — the GENERIC ball-local `∘V` transport.**  For ANY real
    weight `Q` bounded (`M_Q`) + pairwise-Lipschitz (`L_Q`) ONLY on a base ball `ball 0 rQ` (NOT
    globally), the IFT local inverse `V` (`inverseChart_lipschitz_package`, J4-932) transports it: the
    composite `w ↦ Q (V w)` is bounded (`M_Q`) + pairwise-Lipschitz (`L_Q·L_V`) on an image ball
    `ball 0 σ`, with `V 0 = 0` and `V` mapping `ball 0 σ` into `ball 0 rQ`.  Route: the SAME
    radius-shrinking `σ = min σ0 (rQ/(L_V+1))` J4-932 already uses keeps `V`'s image inside `ball 0 rQ`,
    where the weight's ball-local bounds apply.  ⚠ NOT `a₁ = R/6`. -/
theorem transport_ballLocal_regularity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (Q : Point n → ℝ) (rQ M_Q L_Q : ℝ) (hrQ : 0 < rQ) (hMQ : 0 ≤ M_Q) (hLQ : 0 ≤ L_Q)
    (hQb : ∀ z ∈ Metric.ball (0 : Point n) rQ, |Q z| ≤ M_Q)
    (hQl : ∀ x ∈ Metric.ball (0 : Point n) rQ, ∀ y ∈ Metric.ball (0 : Point n) rQ,
      |Q x - Q y| ≤ L_Q * dist x y) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (Lc : ℝ), 0 ≤ Lc ∧ V 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ, V w ∈ Metric.ball (0 : Point n) rQ) ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ, |Q (V w)| ≤ M_Q) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        |Q (V x) - Q (V y)| ≤ Lc * dist x y) := by
  obtain ⟨σ0, hσ0, V, L_V, hLV, hV0, hVlip⟩ :=
    inverseChart_lipschitz_package g gi hC hK h0Kmem hbaseC2
  -- `V` maps the chosen image ball `ball 0 (min σ0 (rQ/(L_V+1)))` into the base ball `ball 0 rQ`
  -- (verbatim J4-932's `hmaps`, with `r := rQ`).
  have hmaps : ∀ w ∈ Metric.ball (0 : Point n) (min σ0 (rQ / (L_V + 1))),
      V w ∈ Metric.ball (0 : Point n) rQ := by
    intro w hw
    have hwσ0 : w ∈ Metric.ball (0 : Point n) σ0 :=
      Metric.ball_subset_ball (min_le_left _ _) hw
    have h0σ0 : (0 : Point n) ∈ Metric.ball (0 : Point n) σ0 := Metric.mem_ball_self hσ0
    have hlip0 := hVlip w hwσ0 0 h0σ0
    rw [hV0] at hlip0
    have hVwnorm : ‖V w‖ ≤ L_V * ‖w‖ := by
      simpa [dist_zero_right, sub_zero] using hlip0
    have hwr : ‖w‖ < rQ / (L_V + 1) := by
      have hd : dist w (0 : Point n) < min σ0 (rQ / (L_V + 1)) := Metric.mem_ball.mp hw
      rw [dist_zero_right] at hd
      exact lt_of_lt_of_le hd (min_le_right _ _)
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖V w‖ ≤ L_V * ‖w‖ := hVwnorm
      _ ≤ (L_V + 1) * ‖w‖ := by nlinarith [norm_nonneg w]
      _ < (L_V + 1) * (rQ / (L_V + 1)) := by
            apply mul_lt_mul_of_pos_left hwr (by positivity)
      _ = rQ := by field_simp
  refine ⟨min σ0 (rQ / (L_V + 1)), lt_min hσ0 (by positivity), V, L_Q * L_V,
    mul_nonneg hLQ hLV, hV0, hmaps, ?_, ?_⟩
  · intro w hw
    exact hQb (V w) (hmaps w hw)
  · intro x hx y hy
    have hVx := hmaps x hx
    have hVy := hmaps y hy
    have h1 := hQl (V x) hVx (V y) hVy
    have h2 := hVlip x (Metric.ball_subset_ball (min_le_left _ _) hx)
                      y (Metric.ball_subset_ball (min_le_left _ _) hy)
    calc |Q (V x) - Q (V y)| ≤ L_Q * dist (V x) (V y) := h1
      _ = L_Q * ‖V x - V y‖ := by rw [dist_eq_norm]
      _ ≤ L_Q * (L_V * dist x y) := mul_le_mul_of_nonneg_left h2 hLQ
      _ = L_Q * L_V * dist x y := by ring

/-! ###############################################################################
    ### §B — the BALL-LOCAL analogue of J4-932's `transported_ratio_regularity`.
    ############################################################################### -/

/-- **★★ `transported_ratio_regularity_ballLocal` — the BALL-LOCAL drop-in for J4-932.**  J4-932's
    `transported_ratio_regularity` demanded a GLOBALLY bounded + Lipschitz weight `P`; this is the
    ball-local replacement: for ANY weight `P` bounded (`M_P`) + pairwise-Lipschitz (`L_P`) ONLY on a
    base ball `ball 0 rP`, the transported ratio `w ↦ P (V w) / |det (fderiv Wbv (V w))|` is bounded by
    `2 M_P` AND pairwise-Lipschitz on an image ball `ball 0 σ`.  Route: build the base ratio
    `z ↦ P z / |det (fderiv Wbv z)|` bounded+Lipschitz on `ball 0 (min rP rD)` via
    `det_fderiv_regularity_bundle` (J4-931) + `ratio_abs_lipschitzOn` (J4-925), then feed it to the
    generic ball-local transport (§A).  CONDITIONAL on `hbaseC2`.  ⚠ NOT `a₁ = R/6`. -/
theorem transported_ratio_regularity_ballLocal (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (P : Point n → ℝ) (rP M_P L_P : ℝ) (hrP : 0 < rP) (hMP : 0 ≤ M_P) (hLP : 0 ≤ L_P)
    (hPb : ∀ z ∈ Metric.ball (0 : Point n) rP, |P z| ≤ M_P)
    (hPl : ∀ x ∈ Metric.ball (0 : Point n) rP, ∀ y ∈ Metric.ball (0 : Point n) rP,
      |P x - P y| ≤ L_P * dist x y) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (Lc : ℝ), 0 ≤ Lc ∧ V 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (P (V w) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|)
          ≤ M_P / (1 / 2 : ℝ)) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        abs (P (V x) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V x)).det|
            - P (V y) / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V y)).det|)
          ≤ Lc * dist x y) := by
  -- det/ratio regularity on a base ball `ball 0 rD`.
  obtain ⟨rD, hrD, L_D, hLD, hlbdet, hDlip⟩ :=
    det_fderiv_regularity_bundle g gi hC hK h0Kmem hbaseC2
  set S : Set (Point n) := Metric.ball (0 : Point n) (min rP rD) with hSdef
  have hSP : S ⊆ Metric.ball (0 : Point n) rP := Metric.ball_subset_ball (min_le_left _ _)
  have hSD : S ⊆ Metric.ball (0 : Point n) rD := Metric.ball_subset_ball (min_le_right _ _)
  -- the base ratio `Q z = P z / |det|` bounded + Lipschitz on `S`.
  obtain ⟨hQb, hQl⟩ :=
    ratio_abs_lipschitzOn S P
      (fun z => (fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det)
      M_P L_P (1 / 2) L_D hMP hLP (by norm_num) hLD
      (fun x hx => hPb x (hSP hx))
      (fun x hx y hy => hPl x (hSP hx) y (hSP hy))
      (fun x hx => hlbdet x (hSD hx))
      (fun x hx y hy => hDlip x (hSD hx) y (hSD hy))
  -- transport `Q ∘ V` via the generic ball-local transport.
  obtain ⟨σ, hσ, V, Lc, hLc, hV0, _, htqb, htql⟩ :=
    transport_ballLocal_regularity g gi hC hK h0Kmem hbaseC2
      (fun z => P z / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|)
      (min rP rD) (M_P / (1 / 2 : ℝ)) (L_P / (1 / 2 : ℝ) + M_P * L_D / (1 / 2 : ℝ) ^ 2)
      (lt_min hrP hrD) (by positivity) (by positivity) hQb hQl
  exact ⟨σ, hσ, V, Lc, hLc, hV0, htqb, htql⟩

/-! ###############################################################################
    ### §C — CONCRETE compositions with J4-938's `q₁ = (amp·F)/|det|`, `q₂ = (Cfield·F)/|det|`.
    ############################################################################### -/

/-- **★★ `census_ampF_transported_ratio_regularity` — THE CONCRETE q₁ TRANSPORTED (amplitude-half).**
    Composing J4-938's concrete base-ball ratio `census_ampF_ratio_regularity` with the generic
    ball-local transport (§A), the TRANSPORTED census integrand
    `w ↦ (chartFieldAmp … τ (V w) 0 · F0 (V w)) / |det (fderiv Wbv (V w))|` is bounded + pairwise-
    Lipschitz on an image ball `ball 0 σ`.  This closes the AMPLITUDE half of junction piece (3)'s `∘V`
    transport for q₁: the amplitude factor is concrete (J4-938 §B), only `F0` (the Levi carry) is
    abstract.  CONDITIONAL on `hbaseC2`.  ⚠ NOT `a₁ = R/6`. -/
theorem census_ampF_transported_ratio_regularity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F0 : Point n → ℝ) (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMFnn : 0 ≤ M_F) (hLFnn : 0 ≤ L_F)
    (hFb : ∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F)
    (hFl : ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (M Lc : ℝ), 0 ≤ M ∧ 0 ≤ Lc ∧ V 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (chartFieldAmp g gi hC hK a b τ (V w) 0 * F0 (V w)
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|) ≤ M) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        abs (chartFieldAmp g gi hC hK a b τ (V x) 0 * F0 (V x)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V x)).det|
            - chartFieldAmp g gi hC hK a b τ (V y) 0 * F0 (V y)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V y)).det|)
          ≤ Lc * dist x y) := by
  obtain ⟨ρ, hρ, M, L, hM, hL, hb, hl⟩ :=
    census_ampF_ratio_regularity g gi hC hK a b τ h0Kmem hbaseC2 hg hg0 hu
      F0 rF M_F L_F hrF hMFnn hLFnn hFb hFl
  obtain ⟨σ, hσ, V, Lc, hLc, hV0, _, htqb, htql⟩ :=
    transport_ballLocal_regularity g gi hC hK h0Kmem hbaseC2
      (fun z => chartFieldAmp g gi hC hK a b τ z 0 * F0 z
          / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|)
      ρ M L hρ hM hL hb hl
  exact ⟨σ, hσ, V, M, Lc, hM, hLc, hV0, htqb, htql⟩

/-- **★★ `census_CfieldF_transported_ratio_regularity` — THE CONCRETE q₂ TRANSPORTED.**  As
    `census_ampF_transported_ratio_regularity` but for the `∂_τ`-slope weight `censusAmpTauDeriv · F0` —
    the transported second census integrand `q₂ = (Cfield·F)/|det| ∘ V`.  CONDITIONAL on `hbaseC2`.
    ⚠ NOT `a₁ = R/6`. -/
theorem census_CfieldF_transported_ratio_regularity (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b : ℝ) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hbaseC2 : ContDiffAt ℝ 2 (fun z => uniformInverseChart g gi hC hK z 0) (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (F0 : Point n → ℝ) (rF M_F L_F : ℝ) (hrF : 0 < rF) (hMFnn : 0 ≤ M_F) (hLFnn : 0 ≤ L_F)
    (hFb : ∀ z : Point n, ‖z‖ < rF → |F0 z| ≤ M_F)
    (hFl : ∀ z w : Point n, ‖z‖ < rF → ‖w‖ < rF → |F0 z - F0 w| ≤ L_F * dist z w) :
    ∃ σ > (0 : ℝ), ∃ (V : Point n → Point n) (M Lc : ℝ), 0 ≤ M ∧ 0 ≤ Lc ∧ V 0 = 0 ∧
      (∀ w ∈ Metric.ball (0 : Point n) σ,
        abs (censusAmpTauDeriv g gi hC hK a b (V w) * F0 (V w)
            / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V w)).det|) ≤ M) ∧
      (∀ x ∈ Metric.ball (0 : Point n) σ, ∀ y ∈ Metric.ball (0 : Point n) σ,
        abs (censusAmpTauDeriv g gi hC hK a b (V x) * F0 (V x)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V x)).det|
            - censusAmpTauDeriv g gi hC hK a b (V y) * F0 (V y)
              / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) (V y)).det|)
          ≤ Lc * dist x y) := by
  obtain ⟨ρ, hρ, M, L, hM, hL, hb, hl⟩ :=
    census_CfieldF_ratio_regularity g gi hC hK a b h0Kmem hbaseC2 hg hg0 hu
      F0 rF M_F L_F hrF hMFnn hLFnn hFb hFl
  obtain ⟨σ, hσ, V, Lc, hLc, hV0, _, htqb, htql⟩ :=
    transport_ballLocal_regularity g gi hC hK h0Kmem hbaseC2
      (fun z => censusAmpTauDeriv g gi hC hK a b z * F0 z
          / |(fderiv ℝ (fun z => uniformInverseChart g gi hC hK z 0) z).det|)
      ρ M L hρ hM hL hb hl
  exact ⟨σ, hσ, V, M, Lc, hM, hLc, hV0, htqb, htql⟩

/-! ###############################################################################
    ### §D — non-vacuity of the ball-local weight slot (TEETH).
    ############################################################################### -/

/-- **Non-vacuity of the ball-local weight slot.**  The `Q` hypothesis bundle of
    `transport_ballLocal_regularity` (bounded + pairwise-Lipschitz on a GENUINE ball `rQ>0`) is
    satisfiable with TEETH by `Q z := cos ‖z‖` (bounded by `1`, genuinely varying, Lipschitz `1` via
    `Real.lipschitzWith_cos` ∘ `abs_norm_sub_norm_le`), `rQ = 1`.  Confirms the ball-local slot is not
    vacuous.  ⚠ NOT `a₁ = R/6`. -/
theorem transport_ballLocal_slot_satisfiable :
    ∃ (Q : Point n → ℝ) (rQ M_Q L_Q : ℝ), 0 < rQ ∧ 0 ≤ M_Q ∧ 0 ≤ L_Q ∧
      (∀ z ∈ Metric.ball (0 : Point n) rQ, |Q z| ≤ M_Q) ∧
      (∀ x ∈ Metric.ball (0 : Point n) rQ, ∀ y ∈ Metric.ball (0 : Point n) rQ,
        |Q x - Q y| ≤ L_Q * dist x y) := by
  refine ⟨fun z => Real.cos ‖z‖, 1, 1, 1, one_pos, zero_le_one, zero_le_one, ?_, ?_⟩
  · intro z _
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  · intro x _ y _
    have h1 : |Real.cos ‖x‖ - Real.cos ‖y‖| ≤ |‖x‖ - ‖y‖| := by
      have hlip := Real.lipschitzWith_cos.dist_le_mul ‖x‖ ‖y‖
      simpa [Real.dist_eq, one_mul] using hlip
    have h2 : |‖x‖ - ‖y‖| ≤ dist x y := by
      rw [dist_eq_norm]; exact abs_norm_sub_norm_le x y
    calc |Real.cos ‖x‖ - Real.cos ‖y‖| ≤ |‖x‖ - ‖y‖| := h1
      _ ≤ dist x y := h2
      _ = 1 * dist x y := (one_mul _).symm

end QIQTH.BaseSlotTransportBallLocal

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.BaseSlotTransportBallLocal
#print axioms transport_ballLocal_regularity
#print axioms transported_ratio_regularity_ballLocal
#print axioms census_ampF_transported_ratio_regularity
#print axioms census_CfieldF_transported_ratio_regularity
#print axioms transport_ballLocal_slot_satisfiable
end AxiomChecks
