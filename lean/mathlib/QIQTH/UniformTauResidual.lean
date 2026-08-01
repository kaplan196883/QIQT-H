/-
  UniformTauResidual — J4-88: quantifying the uniform cutoff-residual engine over the TIME `τ`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════════
  ## Goal.

  `UniformCoeffBound.cutoffResidual_uniformFlow_unconditional` (J4-87) gives, at a FIXED time `t > 0`, a
  single `(a, b, B)` uniform over the compact base set `K`:
      `|χ(v)·∂ₜH(t,v) − Δ_g̃_q(χ·H(t))(v)| ≤ B · gaussDdimWide t v`   (∀ q ∈ K, ∀ v).
  The capstone consumer `RecenterReduction.hEboundW_of_uniform_perBasePoint` (feeding the M6 true-kernel
  Neumann convergence, hence conditional `a₁ = R/6`) needs this bound for ALL `τ > 0` with the constants
  `(a, b, B)` `τ`-FREE.

  ## The τ-dependence trace (the reason this is reachable ∀ τ > 0, not merely on `(0,T]`).

  Threading `τ` through the J4-84…J4-87 chain, EVERY constant is `τ`-independent EXCEPT the annulus
  parametrix bound `Mann` of `parametrixH_annulus_bounds`, whose `M = max Kcof (b·Kcof/2 + τ·Kdcof)`
  carries a `τ·Kdcof` term (⟹ linear growth as `τ → ∞`; `(0,T]` alone would suffice for that term but the
  consumer literally quantifies `∀ τ > 0`).  The growth is an ARTEFACT of the single-constant packaging:
  the residual's cutoff-derivative term `2·Σ g̃⁻¹·∂χ·∂H` is genuinely `τ`-uniformly bounded because
      `∂ⱼH = (−wʲ/(2τ))·G·cof + G·∂ⱼcof` ,   `(1/τ)·G ≤ (8/a²)·G_wide`  (annulus, `r ≥ a > 0`),  `G ≤ G_wide`,
  so `|∂ⱼH| ≤ (b·Kcof/2·(8/a²) + Kdcof)·G_wide` — a `τ`-FREE constant.  Absorbing the derivative directly
  into `G_wide` (rather than through the intermediate `M·(1/τ)·G`) removes ALL `τ`-growth, giving a genuine
  `∀ τ > 0` uniform bound.

  ## Landed here (green; NO `sorry`, NO new axioms, NO `expRho` in statements, NO vacuous hypotheses).

  * `parametrixCofactor_value_annulus_tauUniform` — τ-uniform annulus VALUE bound `|G_τ·cof| ≤ Kcof·G_τ`.
  * `parametrixCofactor_deriv_annulus_gaussDdimWide_tauUniform` — ★ the τ-uniform annulus DERIVATIVE
    absorption `|∂ⱼ(G_τ·cof)| ≤ Kd·G_wide,τ`, `Kd` τ-free (the crux reusable Gaussian absorption).
  * `uniformResidual_gaussian_bound_tau` — the F-res (near) constant made τ-uniform (`∀ τ > 0`).
  * `near_uncutResidual_uniform_tau` — the near engine made τ-uniform.
  * `cutoffResidual_gaussianWide_tauUniform_engine` — the explicit-`B` cutoff engine with the τ-free
    derivative-absorbed annulus inputs.
  * `cutoffResidual_uniformFlow_unconditional_tau` — ★ THE CAPSTONE: a single `(a, b, B)`, uniform over
    BOTH `q ∈ K` and ALL `τ > 0`, dominating the cutoff-parametrix residual by `B·gaussDdimWide τ v`, from
    ONLY the geometric + heat-side hypotheses.

  ## FIREWALLED (exact, honest).  The `E`-identification (`Vmap`) gap to
  `hEboundW_of_uniform_perBasePoint` is NOT closed here: that consumer's residual `E τ p q` is the GLOBAL
  parametrix residual `heatOp g gi H` in the ORIGINAL chart at base `0`, whereas this bound is the residual
  of the CUTOFF parametrix under the `q`-RECENTERED pullback metric `g̃_q` in the recentered coordinate `v`.
  Connecting them is the arbitrary-base-point exp-transport (`RecenterReduction` header: "infrastructure-
  scale, blocked on ⊤-global smoothness of the arbitrary-center chart") — NOT a one-lemma gap.  See the
  module note at the bottom for the exact remaining statement.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.UniformCoeffBound
import QIQTH.ParametrixHAnnulusBounds
import QIQTH.AnnulusGaussianBound

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.RadialDistance QIQTH.ResidueBound QIQTH.GaussianWidthTolerant QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap
open scoped BigOperators ContDiff

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### Part 2 — τ-uniform Gaussian absorption for the concrete parametrix on the annulus. -/

/-- **τ-UNIFORM ANNULUS VALUE BOUND.**  For `H_τ = gaussDdim τ · cofactor`, on the annulus
    `a² ≤ rncRadialSq w ≤ b²` the value is dominated by `Kcof · gaussDdim τ w` with `Kcof` the annulus
    sup of `|cofactor|` — INDEPENDENT of `τ`.  (First half of `parametrixH_annulus_bounds`, with the
    time-independence of `Kcof` made explicit by quantifying `∀ τ > 0` after fixing `Kcof`.) -/
theorem parametrixCofactor_value_annulus_tauUniform
    (a b : ℝ) (cofactor : Point n → ℝ) (hcof_cont : Continuous cofactor) :
    ∃ Kcof : ℝ, 0 ≤ Kcof ∧ ∀ (τ : ℝ), 0 < τ → ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |(fun y => gaussDdim τ y * cofactor y) w| ≤ Kcof * gaussDdim τ w := by
  obtain ⟨Kcof, hKcof0, hKcof⟩ := exists_bound_on_annulus cofactor hcof_cont a b
  refine ⟨Kcof, hKcof0, ?_⟩
  intro τ _hτ w h1 h2
  have hG0 : 0 ≤ gaussDdim τ w := gaussDdim_nonneg τ w
  show |gaussDdim τ w * cofactor w| ≤ Kcof * gaussDdim τ w
  rw [abs_mul, abs_of_nonneg hG0]
  calc gaussDdim τ w * |cofactor w|
      ≤ gaussDdim τ w * Kcof := mul_le_mul_of_nonneg_left (hKcof w h1 h2) hG0
    _ = Kcof * gaussDdim τ w := by ring

/-- **★ τ-UNIFORM ANNULUS DERIVATIVE ABSORPTION (the crux reusable Gaussian bound).**  For
    `H_τ = gaussDdim τ · cofactor`, on the annulus `a² ≤ rncRadialSq w ≤ b²` (`0 < a`), EACH partial
    `∂ⱼH_τ` is dominated by `Kd · gaussDdimWide τ w` with `Kd = b·Kcof/2·(8/a²) + Kdcof` INDEPENDENT of
    `τ`.  Route: Leibniz `∂ⱼ(G·cof) = (−wʲ/2τ)·G·cof + G·∂ⱼcof` (`pd_mul` + `gaussDdim_pd_eq`), then the
    two Gaussian absorptions `(1/τ)·G ≤ (8/a²)·G_wide` (`invTpow_gaussDdim_le_gaussDdimWide`, `k=1`,
    annulus) and `G ≤ G_wide` (`gaussDdim_le_gaussDdimWide`) DEPOSIT the polynomial `wʲ`- and `(1/τ)`-
    factors into the wide Gaussian, so no `τ`-growth survives.  This is the deletion of the `τ·Kdcof`
    growth of `parametrixH_annulus_bounds`' single constant. -/
theorem parametrixCofactor_deriv_annulus_gaussDdimWide_tauUniform
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (cofactor : Point n → ℝ) (hcof_cont : Continuous cofactor)
    (hcof_pdiff : ∀ (i : Fin n) (x : Point n), PdiffAt cofactor i x)
    (hdcof_cont : ∀ j, Continuous (fun w => pd cofactor j w)) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (τ : ℝ), 0 < τ → ∀ (w : Point n) (j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (fun y => gaussDdim τ y * cofactor y) j w| ≤ Kd * gaussDdimWide τ w := by
  classical
  obtain ⟨Kcof, hKcof0, hKcof⟩ := exists_bound_on_annulus cofactor hcof_cont a b
  have hbd : ∀ j : Fin n, ∃ K : ℝ, 0 ≤ K ∧ ∀ w : Point n,
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |pd cofactor j w| ≤ K :=
    fun j => exists_bound_on_annulus (fun w => pd cofactor j w) (hdcof_cont j) a b
  choose Kd' hKd'0 hKdbd using hbd
  set Kdcof : ℝ := ∑ j, Kd' j with hKdcof_def
  have hKdcof0 : 0 ≤ Kdcof := Finset.sum_nonneg fun j _ => hKd'0 j
  have hKdcof : ∀ (w : Point n) (j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 → |pd cofactor j w| ≤ Kdcof := by
    intro w j h1 h2
    refine (hKdbd j w h1 h2).trans ?_
    exact Finset.single_le_sum (f := fun j' => Kd' j') (fun j' _ => hKd'0 j') (Finset.mem_univ j)
  refine ⟨b * Kcof / 2 * (8 / a ^ 2) + Kdcof, by positivity, ?_⟩
  intro τ hτ w j h1 h2
  have hG0 : 0 ≤ gaussDdim τ w := gaussDdim_nonneg τ w
  have hGw0 : 0 ≤ gaussDdimWide τ w := gaussDdimWide_nonneg τ w
  have h2tpos : (0 : ℝ) < 2 * τ := by linarith
  -- `|wʲ| ≤ b` on the annulus.
  have hwj : |w j| ≤ b := by
    have hle : (w j) ^ 2 ≤ b ^ 2 :=
      calc (w j) ^ 2 ≤ ∑ i, (w i) ^ 2 :=
            Finset.single_le_sum (f := fun i => (w i) ^ 2)
              (fun i _ => sq_nonneg _) (Finset.mem_univ j)
        _ = rncRadialSq w := rfl
        _ ≤ b ^ 2 := h2
    calc |w j| = Real.sqrt ((w j) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hle
      _ = |b| := Real.sqrt_sq_eq_abs _
      _ = b := abs_of_pos hb
  -- Leibniz + exact Gaussian gradient.
  have hpg : PdiffAt (fun y => gaussDdim τ y) j w :=
    PdiffAt_of_contDiff (fun y => gaussDdim τ y) (gaussDdim_contDiff τ) j w
  have hpc : PdiffAt cofactor j w := hcof_pdiff j w
  rw [pd_mul (fun y => gaussDdim τ y) cofactor j w hpg hpc, gaussDdim_pd_eq τ hτ w j]
  -- absorptions.
  have hinvT : (1 / τ) * gaussDdim τ w ≤ (8 / a ^ 2) * gaussDdimWide τ w := by
    have h := invTpow_gaussDdim_le_gaussDdimWide 1 a ha hτ h1
    simpa [pow_one, Nat.factorial_one, Nat.cast_one] using h
  have hGle : gaussDdim τ w ≤ gaussDdimWide τ w := gaussDdim_le_gaussDdimWide hτ w
  -- term (1): `|(−wʲ/2τ)·G·cof|`.
  have hT1 : |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w|
      ≤ b / (2 * τ) * gaussDdim τ w * Kcof := by
    rw [abs_mul, abs_mul, abs_of_nonneg hG0, abs_div, abs_neg, abs_of_pos h2tpos]
    have hGA : 0 ≤ |w j| / (2 * τ) * gaussDdim τ w :=
      mul_nonneg (div_nonneg (abs_nonneg _) (le_of_lt h2tpos)) hG0
    calc |w j| / (2 * τ) * gaussDdim τ w * |cofactor w|
        ≤ |w j| / (2 * τ) * gaussDdim τ w * Kcof :=
          mul_le_mul_of_nonneg_left (hKcof w h1 h2) hGA
      _ ≤ b / (2 * τ) * gaussDdim τ w * Kcof :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right ((div_le_div_iff_of_pos_right h2tpos).mpr hwj) hG0)
            hKcof0
  -- term (2): `|G·∂ⱼcof|`.
  have hT2 : |gaussDdim τ w * pd cofactor j w| ≤ gaussDdim τ w * Kdcof := by
    rw [abs_mul, abs_of_nonneg hG0]
    exact mul_le_mul_of_nonneg_left (hKdcof w j h1 h2) hG0
  -- absorb both terms into `G_wide`.
  have hT1abs : b / (2 * τ) * gaussDdim τ w * Kcof
      ≤ b * Kcof / 2 * (8 / a ^ 2) * gaussDdimWide τ w := by
    have hcoef : (0 : ℝ) ≤ b * Kcof / 2 := by positivity
    calc b / (2 * τ) * gaussDdim τ w * Kcof
        = (b * Kcof / 2) * ((1 / τ) * gaussDdim τ w) := by ring
      _ ≤ (b * Kcof / 2) * ((8 / a ^ 2) * gaussDdimWide τ w) :=
          mul_le_mul_of_nonneg_left hinvT hcoef
      _ = b * Kcof / 2 * (8 / a ^ 2) * gaussDdimWide τ w := by ring
  have hT2abs : gaussDdim τ w * Kdcof ≤ Kdcof * gaussDdimWide τ w := by
    calc gaussDdim τ w * Kdcof = Kdcof * gaussDdim τ w := by ring
      _ ≤ Kdcof * gaussDdimWide τ w := mul_le_mul_of_nonneg_left hGle hKdcof0
  calc |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w + gaussDdim τ w * pd cofactor j w|
      ≤ |(-(w j) / (2 * τ)) * gaussDdim τ w * cofactor w| + |gaussDdim τ w * pd cofactor j w| :=
        abs_add_le _ _
    _ ≤ b / (2 * τ) * gaussDdim τ w * Kcof + gaussDdim τ w * Kdcof := add_le_add hT1 hT2
    _ ≤ b * Kcof / 2 * (8 / a ^ 2) * gaussDdimWide τ w + Kdcof * gaussDdimWide τ w :=
        add_le_add hT1abs hT2abs
    _ = (b * Kcof / 2 * (8 / a ^ 2) + Kdcof) * gaussDdimWide τ w := by ring

/-! ### Part 3a — the explicit-`B` cutoff engine with τ-free derivative-absorbed annulus inputs. -/

/-- **THE CUTOFF ENGINE WITH DERIVATIVE-ABSORBED ANNULUS INPUTS.**  Same region-split as
    `cutoffResidual_global_gaussianWide_bound_explicitB`, but the annulus derivative bound is supplied
    ALREADY ABSORBED into `gaussDdimWide` (`|∂ⱼH| ≤ Kder·G_wide`) and the value bound as `|H| ≤ Kcof·G`
    (no shared constant).  Consequently the dominating constant
        `B = C + Kcof·Kc2 + 2·n²·Kg·Kc1·Kder`
    contains NO intermediate `M·(1/t)` factor, so when `Kcof`, `Kder`, `Kg`, `Kc1`, `Kc2`, `C` are all
    `t`-free (as they are for the concrete parametrix, `Part 2`), `B` is `t`-free.  This is the packaging
    that makes the whole cutoff bound uniform in `t = τ`.  All hypotheses genuine, none the conclusion. -/
theorem cutoffResidual_gaussianWide_tauUniform_engine
    (g gi : Point n → Fin n → Fin n → ℝ) (H dtH : Point n → ℝ)
    (a b t : ℝ) (ha : 0 < a) (hab : a < b) (ht : 0 < t)
    (hH2 : ∀ w : Point n, ContDiffAt ℝ 2 H w)
    (hgisymm : ∀ w i j, gi w i j = gi w j i)
    (C : ℝ) (hCnn : 0 ≤ C)
    (hEnear : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |dtH w - laplaceBeltrami g gi H w| ≤ C * gaussDdimWide t w)
    (Kcof : ℝ) (hKcof : 0 ≤ Kcof)
    (hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |H w| ≤ Kcof * gaussDdim t w)
    (Kder : ℝ) (hKder : 0 ≤ Kder)
    (hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd H j w| ≤ Kder * gaussDdimWide t w)
    (Kg Kc1 Kc2 : ℝ) (hKg : 0 ≤ Kg) (hKc1 : 0 ≤ Kc1) (hKc2 : 0 ≤ Kc2)
    (hgibd : ∀ (w : Point n) (i j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |gi w i j| ≤ Kg)
    (hDchi : ∀ (w : Point n) (i : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |pd (radialCutoff a b) i w| ≤ Kc1)
    (hLapChi : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
        |laplaceBeltrami g gi (radialCutoff a b) w| ≤ Kc2) :
    0 ≤ C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder ∧ ∀ v : Point n,
      |radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v|
        ≤ (C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdimWide t v := by
  have hb2 : 0 ≤ Kcof * Kc2 := mul_nonneg hKcof hKc2
  have hb3 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by positivity
  refine ⟨by linarith, ?_⟩
  intro v
  have hχC2 : ContDiffAt ℝ 2 (radialCutoff a b) v :=
    (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hgd : gaussDdim t v ≤ gaussDdimWide t v := gaussDdim_le_gaussDdimWide ht v
  have hWnn : 0 ≤ gaussDdimWide t v := gaussDdimWide_nonneg t v
  have ha2b2 : a ^ 2 ≤ b ^ 2 := by nlinarith
  rcases lt_or_ge (rncRadialSq v) (a ^ 2) with hnear | ha2
  · -- (a) NEAR
    have hb : rncRadialSq v ≤ b ^ 2 := le_trans (le_of_lt hnear) ha2b2
    have hχ1 : radialCutoff a b v = 1 := radialCutoff_eq_one ha hab (le_of_lt hnear)
    have hlbmul := laplaceBeltrami_mul_C2 g gi (radialCutoff a b) H v hχC2 (hH2 v) (hgisymm v)
    have hlapχ : laplaceBeltrami g gi (radialCutoff a b) v = 0 :=
      laplaceBeltrami_radialCutoff_zero_near g gi ha hab hnear
    have hpdχ : ∀ i, pd (radialCutoff a b) i v = 0 :=
      fun i => pd_radialCutoff_eq_zero_of_near ha hab hnear i
    have hRcut : radialCutoff a b v * dtH v
        - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v
          = dtH v - laplaceBeltrami g gi H v := by
      rw [hlbmul, hχ1, hlapχ]; simp [hpdχ]
    rw [hRcut]
    calc |dtH v - laplaceBeltrami g gi H v| ≤ C * gaussDdimWide t v := hEnear v hb
      _ ≤ (C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdimWide t v := by
          apply mul_le_mul_of_nonneg_right _ hWnn; linarith
  · rcases le_or_gt (rncRadialSq v) (b ^ 2) with hb | hfar
    · -- (b) ANNULUS
      have hlbmul := laplaceBeltrami_mul_C2 g gi (radialCutoff a b) H v hχC2 (hH2 v) (hgisymm v)
      have hRcut : radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v
            = radialCutoff a b v * (dtH v - laplaceBeltrami g gi H v)
              - H v * laplaceBeltrami g gi (radialCutoff a b) v
              - 2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v := by
        rw [hlbmul]; ring
      rw [hRcut]
      have hsub2 : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => by
        rw [sub_eq_add_neg]; exact (abs_add_le x (-y)).trans_eq (by rw [abs_neg])
      set A := radialCutoff a b v * (dtH v - laplaceBeltrami g gi H v) with hA
      set B' := H v * laplaceBeltrami g gi (radialCutoff a b) v with hB'
      set Cc := 2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v with hCc
      have htri : |A - B' - Cc| ≤ |A| + |B'| + |Cc| :=
        (hsub2 (A - B') Cc).trans (by have := hsub2 A B'; linarith)
      -- |A| ≤ C·W
      have hAbd : |A| ≤ C * gaussDdimWide t v := by
        rw [hA, abs_mul]
        have hχle : |radialCutoff a b v| ≤ 1 := by
          rw [abs_of_nonneg (radialCutoff_nonneg a b v)]; exact radialCutoff_le_one a b v
        calc |radialCutoff a b v| * |dtH v - laplaceBeltrami g gi H v|
            ≤ 1 * (C * gaussDdimWide t v) :=
              mul_le_mul hχle (hEnear v hb) (abs_nonneg _) (by norm_num)
          _ = C * gaussDdimWide t v := by ring
      -- |B'| ≤ (Kcof·Kc2)·W
      have hBbd : |B'| ≤ (Kcof * Kc2) * gaussDdimWide t v := by
        rw [hB', abs_mul]
        calc |H v| * |laplaceBeltrami g gi (radialCutoff a b) v|
            ≤ (Kcof * gaussDdim t v) * Kc2 :=
              mul_le_mul (hHann v ha2 hb) (hLapChi v ha2 hb) (abs_nonneg _)
                (mul_nonneg hKcof (gaussDdim_nonneg t v))
          _ = (Kcof * Kc2) * gaussDdim t v := by ring
          _ ≤ (Kcof * Kc2) * gaussDdimWide t v := mul_le_mul_of_nonneg_left hgd hb2
      -- |Cc| ≤ (2 n² Kg Kc1 Kder)·W
      have hSabs : |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      have hterm : ∀ i j : Fin n, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ Kg * Kc1 * (Kder * gaussDdimWide t v) := by
        intro i j
        rw [abs_mul, abs_mul]
        exact mul_le_mul
          (mul_le_mul (hgibd v i j ha2 hb) (hDchi v i ha2 hb) (abs_nonneg _) hKg)
          (hDHann v j ha2 hb) (abs_nonneg _) (mul_nonneg hKg hKc1)
      have hsum2 : ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v|
          ≤ ∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (Kder * gaussDdimWide t v)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      have hconst : (∑ _i : Fin n, ∑ _j : Fin n, (Kg * Kc1 * (Kder * gaussDdimWide t v)))
          = (n : ℝ) ^ 2 * (Kg * Kc1 * (Kder * gaussDdimWide t v)) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      have hCcbd : |Cc| ≤ (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdimWide t v := by
        rw [hCc]
        calc |2 * ∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v|
            = 2 * |∑ i, ∑ j, gi v i j * pd (radialCutoff a b) i v * pd H j v| := by
              rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
          _ ≤ 2 * ∑ i, ∑ j, |gi v i j * pd (radialCutoff a b) i v * pd H j v| :=
              mul_le_mul_of_nonneg_left hSabs (by norm_num)
          _ ≤ 2 * ((n : ℝ) ^ 2 * (Kg * Kc1 * (Kder * gaussDdimWide t v))) :=
              mul_le_mul_of_nonneg_left (hsum2.trans hconst.le) (by norm_num)
          _ = (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdimWide t v := by ring
      calc |A - B' - Cc|
          ≤ C * gaussDdimWide t v + (Kcof * Kc2) * gaussDdimWide t v
              + (2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdimWide t v :=
            htri.trans (add_le_add (add_le_add hAbd hBbd) hCcbd)
        _ = (C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder) * gaussDdimWide t v := by ring
    · -- (c) FAR
      have hχ0 : radialCutoff a b v = 0 := radialCutoff_eq_zero ha hab (le_of_lt hfar)
      have hlbmul := laplaceBeltrami_mul_C2 g gi (radialCutoff a b) H v hχC2 (hH2 v) (hgisymm v)
      have hlapχ : laplaceBeltrami g gi (radialCutoff a b) v = 0 :=
        laplaceBeltrami_radialCutoff_zero_far g gi ha hab hfar
      have hpdχ : ∀ i, pd (radialCutoff a b) i v = 0 :=
        fun i => pd_radialCutoff_eq_zero_of_far ha hab hfar i
      have hRcut : radialCutoff a b v * dtH v
          - laplaceBeltrami g gi (fun y => radialCutoff a b y * H y) v = 0 := by
        rw [hlbmul, hχ0, hlapχ]; simp [hpdχ]
      rw [hRcut, abs_zero]
      have : (0 : ℝ) ≤ C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by linarith
      exact mul_nonneg this hWnn

/-! ### Part 3b — the F-res (near) constant made τ-uniform. -/

/-- **THE UNIFORM RESIDUAL GAUSSIAN BOUND, QUANTIFIED OVER ALL `τ > 0`.**  `uniformResidual_gaussian_bound`
    with the time quantifier moved INSIDE: a SINGLE radius `ρ_u > 0` and constant `C ≥ 0` dominate the
    `N=0` uniform-flow parametrix residual by `C·gaussDdimWide τ v` for EVERY `q ∈ K`, `‖v‖ < ρ_u`, and
    EVERY `τ > 0`.  Sound because every constant of the fixed-`t` proof (`M`, `W`, `L`, `ρ_u`, `C_c`) is
    `t`-FREE; only the per-point Gaussian absorptions consume `hτ`, and they hold for every `τ > 0`. -/
theorem uniformResidual_gaussian_bound_tau (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw0smooth : ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u 0))
    (ρ_c C_c : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c)
    (hCoeffU : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c * rncRadialSq v) :
    ∃ ρ_u : ℝ, 0 < ρ_u ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
      |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
        ≤ C * gaussDdimWide τ v := by
  classical
  obtain ⟨rM, hrM0, M, hM0, hdevU⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform g gi hC hK hg hgnd hgsymm hinvF hframeK
  obtain ⟨rL, hrL0, L, hL0, hLapU⟩ :=
    uniformFlowLaplaceBeltrami_w0_near_uniform g gi hg hC hK hgnd Θ u hw0smooth
  set ρ_u : ℝ := min rM (min rL ρ_c) with hρ_u_def
  have hρ_u0 : 0 < ρ_u := lt_min hrM0 (lt_min hrL0 hρ_c)
  obtain ⟨W, hW0, hWbd⟩ : ∃ W : ℝ, 0 ≤ W ∧
      ∀ v ∈ Metric.closedBall (0 : Point n) ρ_u, |foldedCoeff Θ u 0 v| ≤ W := by
    obtain ⟨Cw, hCw⟩ :=
      (isCompact_closedBall (0 : Point n) ρ_u).exists_bound_of_continuousOn
        hw0smooth.continuous.continuousOn
    refine ⟨max Cw 0, le_max_right _ _, fun v hv => ?_⟩
    have h := hCw v hv; rw [Real.norm_eq_abs] at h; exact h.trans (le_max_left _ _)
  refine ⟨ρ_u, hρ_u0, 8 * C_c + 32 * (n : ℝ) ^ 2 * M * W + L, by positivity, ?_⟩
  intro τ hτ q hq v hv
  have hτne : τ ≠ 0 := hτ.ne'
  have hvM : ‖v‖ < rM := lt_of_lt_of_le hv (min_le_left _ _)
  have hvL : ‖v‖ < rL := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_left _ _))
  have hvc : ‖v‖ < ρ_c := lt_of_lt_of_le hv (le_trans (min_le_right _ _) (min_le_right _ _))
  have hvball : v ∈ Metric.closedBall (0 : Point n) ρ_u := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hw0at : ContDiffAt ℝ 2 (foldedCoeff Θ u 0) v := hw0smooth.contDiffAt.of_le le_top
  rw [parametrixResidual_N0_O1_isolated_C2 (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ hτ v hw0at]
  set Gw : ℝ := gaussDdimWide τ v with hGwdef
  have hGwnn : 0 ≤ Gw := gaussDdimWide_nonneg τ v
  have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg τ v
  set T1 : ℝ := (1 / τ) * gaussDdim τ v
      * totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v with hT1def
  set T2 : ℝ := (1 / τ ^ 2) * gaussDdim τ v
      * ((-1 / 4) * (∑ i, ∑ j, (uniformFlowPullbackMetricInv g gi hC hK q v i j
          - (if i = j then (1 : ℝ) else 0)) * (v i * v j)))
      * foldedCoeff Θ u 0 v with hT2def
  set T3 : ℝ := gaussDdim τ v * laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
      (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v with hT3def
  have hT1bd : |T1| ≤ 8 * C_c * Gw := by
    rw [hT1def, abs_mul, abs_of_nonneg (mul_nonneg (one_div_nonneg.mpr hτ.le) hGnn)]
    calc (1 / τ) * gaussDdim τ v
            * |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v|
        ≤ (1 / τ) * gaussDdim τ v * (C_c * rncRadialSq v) :=
          mul_le_mul_of_nonneg_left (hCoeffU q hq v hvc)
            (mul_nonneg (one_div_nonneg.mpr hτ.le) hGnn)
      _ = C_c * (1 / τ) * (rncRadialSq v * gaussDdim τ v) := by ring
      _ ≤ C_c * (1 / τ) * (8 * τ * Gw) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_c0 (one_div_nonneg.mpr hτ.le))
          rw [hGwdef, ← rncRadial_sq]; exact rncRadialSq_mul_gaussDdim_le hτ v
      _ = 8 * C_c * Gw := by field_simp
  have hT2bd : |T2| ≤ 32 * (n : ℝ) ^ 2 * M * W * Gw := by
    rw [hT2def, hGwdef]
    exact residualQuadratic_pointwise (uniformFlowPullbackMetricInv g gi hC hK q) Θ u hτ M W hM0 hW0 v
      (hdevU q hq v hvM) (hWbd v hvball)
  have hT3bd : |T3| ≤ L * Gw := by
    rw [hT3def, abs_mul, abs_of_nonneg hGnn]
    calc gaussDdim τ v * |laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q) (foldedCoeff Θ u 0) v|
        ≤ gaussDdim τ v * L := mul_le_mul_of_nonneg_left (hLapU q hq v hvL) hGnn
      _ ≤ Gw * L := by rw [hGwdef]; exact mul_le_mul_of_nonneg_right (gaussDdim_le_gaussDdimWide hτ v) hL0
      _ = L * Gw := by ring
  have htri : |T1 + T2 - T3| ≤ |T1| + |T2| + |T3| := by
    have h1 : |T1 + T2 - T3| ≤ |T1 + T2| + |T3| := by
      have h := abs_add_le (T1 + T2) (-T3); rwa [← sub_eq_add_neg, abs_neg] at h
    have h2 : |T1 + T2| ≤ |T1| + |T2| := abs_add_le _ _
    linarith
  calc |T1 + T2 - T3|
      ≤ |T1| + |T2| + |T3| := htri
    _ ≤ 8 * C_c * Gw + 32 * (n : ℝ) ^ 2 * M * W * Gw + L * Gw :=
        add_le_add (add_le_add hT1bd hT2bd) hT3bd
    _ = (8 * C_c + 32 * (n : ℝ) ^ 2 * M * W + L) * Gw := by ring

/-! ### Part 3c — the near engine made τ-uniform. -/

/-- **THE NEAR ENGINE, UNIFORM OVER `K` AND ALL `τ > 0`.**  `near_uncutResidual_uniform` with the time
    quantifier moved inside: from the τ-uniform residual bound (`hResU`, ONE `ρ_u`, ONE `C`, all `q ∈ K`,
    all `τ > 0`) the near output holds with the SINGLE radius `b = ρ_u/2` for every `q ∈ K` and every
    `τ > 0`.  The ball conversion `rncRadialSq w ≤ b² ⟹ ‖w‖ < ρ_u` is `τ`-independent. -/
theorem near_uncutResidual_uniform_tau
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (C ρ_u : ℝ) (hρ_u : 0 < ρ_u)
    (hResU : ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_u →
      |parametrixResidualN 0 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v|
        ≤ C * gaussDdimWide τ v) :
    ∃ b : ℝ, 0 < b ∧
      ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
        |deriv (fun s => heatParametrix 0 Θ u s w) τ
            - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 0 Θ u τ) w|
          ≤ C * gaussDdimWide τ w := by
  refine ⟨ρ_u / 2, by linarith, fun τ hτ q hq w hw => ?_⟩
  have hb0 : (0 : ℝ) ≤ ρ_u / 2 := by linarith
  have hnw : ‖w‖ < ρ_u := by
    have h1 : ‖w‖ ≤ rncRadial w := norm_le_rncRadial w
    have h2 : rncRadial w ≤ ρ_u / 2 := by
      rw [rncRadial]
      calc Real.sqrt (rncRadialSq w)
          ≤ Real.sqrt ((ρ_u / 2) ^ 2) := Real.sqrt_le_sqrt hw
        _ = ρ_u / 2 := by rw [Real.sqrt_sq hb0]
    linarith
  have hs := hResU τ hτ q hq w hnw
  simpa only [parametrixResidualN] using hs

/-! ### Part 3d — ★ THE CAPSTONE: the cutoff engine uniform over `K` AND all `τ > 0`. -/

/-- **★ J4-88 — THE CUTOFF ENGINE UNIFORM OVER `K` AND ALL `τ > 0`, UNCONDITIONAL.**  A single
    `(a, b, B)` — with `a`, `b`, `B` all INDEPENDENT of `τ` — such that for EVERY `τ > 0` and EVERY
    `q ∈ K` the cutoff-parametrix residual on `g̃_q = uniformFlowPullbackMetric g gi hC hK q` is dominated
    by `B · gaussDdimWide τ v`.  This upgrades `cutoffResidual_uniformFlow_unconditional` (J4-87, fixed
    `t`) to the ALL-`τ` form the capstone consumer `hEboundW_of_uniform_perBasePoint` requires, using the
    τ-free packaging: the residual constant `C` (`uniformResidual_gaussian_bound_tau`) is `τ`-free, and
    the annulus derivative term is absorbed directly into `gaussDdimWide` with a `τ`-free `Kder`
    (`parametrixCofactor_deriv_annulus_gaussDdimWide_tauUniform`), removing the `τ·Kdcof` growth of the
    single-constant engine.  Hypotheses ONLY the geometric data (`hg`/`hC`/`hK`/`hgnd`/`hgsymm`/`hinvF`/
    `hframeK`) and the heat-side data (`Θ`/`u`/`hw0smooth`/`hw0flat`); all genuine (satisfiable by
    `g = gi = δ`, `Θ = 1`, `u` constant), none the conclusion; NO `expRho` in the statement.  NOT
    `a₁ = R/6` (the `E`-identification / `Vmap` transport to the capstone remains — see the module note). -/
theorem cutoffResidual_uniformFlow_unconditional_tau (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ a b B : ℝ, 0 < a ∧ a < b ∧ 0 ≤ B ∧ ∀ (τ : ℝ), 0 < τ → ∀ q ∈ K, ∀ v : Point n,
      |radialCutoff a b v * deriv (fun s => heatParametrix 0 Θ u s v) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 0 Θ u τ y) v|
        ≤ B * gaussDdimWide τ v := by
  classical
  -- (1) uniform coefficient bound (τ-free, from J4-87).
  obtain ⟨ρ_c, hρ_c, C_c, hC_c0, hCoeffU⟩ :=
    uniformCoeff_bound g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw0smooth hw0flat
  -- (2) τ-uniform residual bound.
  obtain ⟨ρ_u, hρ_u0, C, hC0, hResU⟩ :=
    uniformResidual_gaussian_bound_tau g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw0smooth
      ρ_c C_c hρ_c hC_c0 hCoeffU
  -- (3) τ-uniform near engine; FIXES `bN = ρ_u/2`.
  obtain ⟨bN, hbN0, hEnearU⟩ :=
    near_uncutResidual_uniform_tau g gi hC hK Θ u C ρ_u hρ_u0 hResU
  -- (4) uniform annulus suppliers.
  obtain ⟨rKg, hrKg0, Kg, hKg0, hGIann⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound_annulus g gi hg hC hK hgnd
  obtain ⟨rKc2, hrKc20, hLapAnn⟩ :=
    uniformFlowLaplaceBeltrami_radialCutoff_annulus_bound g gi hg hC hK hgnd
  -- (5) the SINGLE annulus `(a,b)`.
  set rmin : ℝ := min rKg rKc2 with hrmin_def
  have hrmin0 : 0 < rmin := lt_min hrKg0 hrKc20
  set b : ℝ := min bN (rmin / 2) with hb_def
  have hb0 : 0 < b := lt_min hbN0 (by linarith)
  have hb_nonneg : (0 : ℝ) ≤ b := le_of_lt hb0
  set a : ℝ := b / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have hab : a < b := by rw [ha_def]; linarith
  have hb_le_bN : b ≤ bN := min_le_left _ _
  have hb_lt_rmin : b < rmin := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hb_lt_rKg : b < rKg := lt_of_lt_of_le hb_lt_rmin (min_le_left _ _)
  have hb_lt_rKc2 : b < rKc2 := lt_of_lt_of_le hb_lt_rmin (min_le_right _ _)
  -- (6) instantiate the uniform annulus bounds at `(a,b)`.
  have hGIannK := hGIann a b hb_nonneg hb_lt_rKg
  obtain ⟨Kc2, hKc20, hLapChiU⟩ := hLapAnn a b hb_nonneg hb_lt_rKc2
  -- (7) `Kc1` cutoff-derivative bound.
  obtain ⟨Kc1, hKc10, hDchi⟩ := pd_radialCutoff_bound_on_annulus (n := n) a b
  -- (8) τ-uniform parametrix annulus value + absorbed-derivative bounds (cofactor = foldedCoeff Θ u 0).
  obtain ⟨Kcof, hKcof0, hHannU⟩ :=
    parametrixCofactor_value_annulus_tauUniform a b (foldedCoeff Θ u 0) hw0smooth.continuous
  obtain ⟨Kder, hKder0, hDHannU⟩ :=
    parametrixCofactor_deriv_annulus_gaussDdimWide_tauUniform a b ha0 hb0 (foldedCoeff Θ u 0)
      hw0smooth.continuous
      (fun i x => PdiffAt_of_contDiff (foldedCoeff Θ u 0) hw0smooth i x)
      (fun j => (contDiff_pd (foldedCoeff Θ u 0) hw0smooth j).continuous)
  -- (9) the SINGLE τ-free constant `B`.
  have hBnn : 0 ≤ C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by
    have h1 : 0 ≤ Kcof * Kc2 := mul_nonneg hKcof0 hKc20
    have h2 : 0 ≤ 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder := by positivity
    linarith
  refine ⟨a, b, C + Kcof * Kc2 + 2 * (n : ℝ) ^ 2 * Kg * Kc1 * Kder, ha0, hab, hBnn, ?_⟩
  intro τ hτ q hq v
  -- the concrete parametrix `H_τ = gaussDdim τ · foldedCoeff Θ u 0` and its regularity.
  have hHeq : (heatParametrix 0 Θ u τ : Point n → ℝ)
      = fun y => gaussDdim τ y * foldedCoeff Θ u 0 y := by
    funext x; rw [heatParametrix_folded]; simp
  have hHeqw : ∀ w : Point n,
      heatParametrix 0 Θ u τ w = gaussDdim τ w * foldedCoeff Θ u 0 w := fun w => congrFun hHeq w
  have hH : ContDiff ℝ (⊤ : WithTop ℕ∞) (heatParametrix 0 Θ u τ) := by
    rw [hHeq]; exact (gaussDdim_contDiff τ).mul hw0smooth
  have hH2 : ∀ w : Point n, ContDiffAt ℝ 2 (heatParametrix 0 Θ u τ) w :=
    fun w => hH.contDiffAt.of_le le_top
  -- value annulus bound for `H_τ`.
  have hHann : ∀ w : Point n, a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |heatParametrix 0 Θ u τ w| ≤ Kcof * gaussDdim τ w := by
    intro w h1 h2; rw [hHeqw w]; exact hHannU τ hτ w h1 h2
  -- absorbed-derivative annulus bound for `H_τ`.
  have hDHann : ∀ (w : Point n) (j : Fin n), a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |pd (heatParametrix 0 Θ u τ) j w| ≤ Kder * gaussDdimWide τ w := by
    intro w j h1 h2; rw [hHeq]; exact hDHannU τ hτ w j h1 h2
  -- near bound restricted to the sub-ball `rncRadialSq ≤ b² (≤ bN²)`.
  have hb2_le : b ^ 2 ≤ bN ^ 2 := by nlinarith [hb_le_bN, hb0, hbN0]
  have hEnear_q : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
      |deriv (fun s => heatParametrix 0 Θ u s w) τ
          - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q) (heatParametrix 0 Θ u τ) w|
        ≤ C * gaussDdimWide τ w :=
    fun w hw => hEnearU τ hτ q hq w (le_trans hw hb2_le)
  -- inverse-metric symmetry (global) and annulus bounds.
  have hgisymm_q : ∀ w i j, uniformFlowPullbackMetricInv g gi hC hK q w i j
      = uniformFlowPullbackMetricInv g gi hC hK q w j i :=
    fun w i j => uniformFlowPullbackMetricInv_symm_global g gi hC hK hgsymm q w i j
  have hgibd_q : ∀ (w : Point n) (i j : Fin n),
      a ^ 2 ≤ rncRadialSq w → rncRadialSq w ≤ b ^ 2 →
      |uniformFlowPullbackMetricInv g gi hC hK q w i j| ≤ Kg :=
    fun w i j h1 h2 => hGIannK q hq w h1 h2 i j
  -- fire the τ-uniform engine.
  exact (cutoffResidual_gaussianWide_tauUniform_engine
    (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
    (heatParametrix 0 Θ u τ) (fun x => deriv (fun s => heatParametrix 0 Θ u s x) τ)
    a b τ ha0 hab hτ hH2 hgisymm_q
    C hC0 hEnear_q Kcof hKcof0 hHann Kder hKder0 hDHann
    Kg Kc1 Kc2 hKg0 hKc10 hKc20 hgibd_q hDchi (hLapChiU q hq)).2 v

end QIQTH.HeatResidualBound
