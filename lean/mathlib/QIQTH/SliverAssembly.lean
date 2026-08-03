/-
  SliverAssembly — J4-133: the S6 ASSEMBLY of the concrete second-derivative heat-sliver bound.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS BRICK IS.  One ASSEMBLY brick of the `a₁ = R/6` heat-kernel campaign.  It is NOT
  `a₁ = R/6`, and proves NOTHING about `R/6`.  Everything hard is already banked; this file is honest
  plumbing that (i) extracts, as standalone bankable lemmas, the **Hermite-argument replacement
  bridge bounds** (the `T1'` bridge — the polynomial-argument replacement `⟨Y,P⟩² ↔ (zᵢ)²`,
  `⟨P,P⟩ ↔ 1`, `⟨Y,Q⟩ ↔ 0` estimates), and (ii) assembles the concrete-witness formal-Hessian sliver
  into a `√ε` bound via the banked sliver-rpow machinery.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  THE CONCRETE NORMAL FORM (the interface `hNormalForm`).  For the concrete van-Vleck witness the
  `i`-th formal second field-derivative at the RNC center, base `z`, time `τ`, is (from
  `ChartJetHessian.gaussComp_amp_pd_pd`, with `Y z = W z 0`, `P z`/`Q z` the base-`z` chart jets,
  `A₀/A₁/A₂` the amplitude jets, and `⟨a,b⟩ = ∑ₖ a k · b k`):
      `D2H τ z =`
        `  G_τ(Y z)·[⟨Y z,P z⟩²/4τ² − (⟨P z,P z⟩+⟨Y z,Q z⟩)/2τ]·A₀ τ z`     (`sTerm0`)
        `+ 2·G_τ(Y z)·(−⟨Y z,P z⟩/2τ)·A₁ τ z`                                (`sTerm1`)
        `+ G_τ(Y z)·A₂ τ z`.                                                 (`sTerm2`)
  This IS satisfiable — it is `gaussComp_amp_pd_pd` instantiated (the J1b/C² per-`z` jet existence
  lives INSIDE it), so carrying it as the interface hypothesis avoids re-running the jet-existence
  layer here.  It is a genuine equality (not the conclusion) and NON-vacuous (it constrains `D2H` to
  the exact Leibniz-Gaussian 3-term shape).

  ──────────────────────────────────────────────────────────────────────────────────────────────
  WHAT LANDS (this file, UNCONDITIONALLY — the bridge lemmas):
    • `abs_inner_le`             — `|∑ₖ a k·b k| ≤ n·‖a‖·‖b‖` (sup-norm coordinate bound).
    • `sum_mul_single_eq`        — `∑ₖ z k·(eᵢ)k = z i`;  `norm_single_le_one`, `sum_single_sq_eq_one`.
    • `innerYP_add_zi_bound`     — ★ the first bridge: `|⟨Y,P⟩ + z i| ≤ n·β·γ + n·β + n·‖z‖·γ`
        from the displacement `‖Y+z‖ ≤ β` and the jet gap `‖P − eᵢ‖ ≤ γ` (so `⟨Y,P⟩ ≈ −z i`).
    • `innerYP_sq_sub_zi_sq_bound` — ★ the cubic bridge: `|⟨Y,P⟩² − (z i)²| ≤ Δ·(Δ + 2‖z‖)`
        from `|⟨Y,P⟩ + z i| ≤ Δ` (the `‖z‖³`-shape feeding the S4 envelope `∫‖z‖³·G/τ² ~ τ^{−1/2}`).
    • `innerPP_sub_one_bound`    — ★ the coercive bridge: `|⟨P,P⟩ − 1| ≤ n·γ² + 2·γ` (linear `‖z‖`).
    • `normY_le` / `innerYQ_bound` — the centerJet bridge: `|⟨Y,Q⟩| ≤ n·(β+‖z‖)·C_Q` (linear `‖z‖`).
    • `exp_tail_beats_inv`       — the off-gate tail brick: `e^{−c/τ}/τ ≤ 4·τ/c²` for `c,τ > 0`
        (the exponential beats `1/τ`; `∫₀^ε (1/τ)·e^{−c/τ} ~ ε²/c² → 0`).  Route: `e^x ≥ (x/2)²`.

  WHAT LANDS (the ASSEMBLY):
    • `witness_sliver2_assembly` — ★★★ the concrete formal-Hessian sliver `√ε` bound.  Given the
        concrete normal form `hNormalForm` (the 3-term Leibniz-Gaussian identity for the base-`z`
        jets), the three per-slice inner bounds `hInner0`/`hInner1` (Hessian & gradient terms with the
        `(u−s)^{−1/2}` rate) / `hInner2` (mass term, `O(1)`), and per-slice integrabilities, the
        terminal sliver obeys `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z 0| ≤ (C₀+C₁)·2√ε + C₂·ε`.
        Route: split the inner integral into the three concrete terms (the algebra identity PROVED via
        `hNormalForm` + `integral_add`), bound each by its carried rate, then `sliver_rpow_sub`.

  ⚠ HONEST FIREWALL — the carry list of `witness_sliver2_assembly` (each a genuine fact, NONE the
    conclusion, none vacuous, all satisfiable by the true chart-pullback amplitude of `H_G`):
      • `hNormalForm` — the concrete Leibniz-Gaussian 3-term identity (`gaussComp_amp_pd_pd`
        instantiated at the base-`z` chart jets `Y/P/Q` and amplitudes `A₀/A₁/A₂`).  NON-vacuous.
      • `hInner0` — `|∫ z, sTerm0 (u−s) z · F s z 0| ≤ C₀·(u−s)^{−1/2}`.  Satisfiable via the T1'
        decomposition: the PLAIN Hermite term uses the exact cancellation `gaussian_hessian_cancel`
        (`τ^{−1/2}` gain, `hqLip`), and the difference `sTerm0 − plainHermite` gains a `‖z‖` from the
        bridges (`innerYP_sq_sub_zi_sq_bound`/`innerPP_sub_one_bound`/`innerYQ_bound`) + the Gaussian
        replacement (`gaussDdim_replace_bound` / `weighted_chart_replace_bound`, `(√τ)^{k+1}` rates)
        + the moment envelope `pow_norm_mul_gauss_integral`, all of which give `‖z‖³/τ²·G ~ τ^{−1/2}`
        (integrable).  The pointwise domination of the ENTANGLED `G_τ(Y z)`-integrand is a multi-file
        effort (the `G_τ(Y z)`-vs-`G_τ(z)` replacement inside the integrand); it is carried here.
      • `hInner1` — `|∫ z, sTerm1 (u−s) z · F s z 0| ≤ C₁·(u−s)^{−1/2}` (gradient term, crude odd
        moment `∫|zᵢ|·G ~ √τ` after the `G`-replacement; `‖⟨Y,P⟩‖ ≤ C‖z‖` from the bridges).
      • `hInner2` — `|∫ z, sTerm2 (u−s) z · F s z 0| ≤ C₂` (mass term, total mass one, `O(1)`).
      • `hInt0`/`hInt1`/`hInt2` — the per-slice base integrabilities (measurability family
        J4-117/118/119 + the amplitude/`F` sup-bounds).
    The bridge lemmas `innerYP_*`/`innerPP_*`/`innerYQ_*`/`exp_tail_beats_inv` are LANDED
    unconditionally and are precisely the content that makes `hInner0`/`hInner1` satisfiable — the
    minimum bankable deliverable, per the campaign plan.  NO `sorry`, no new axioms, no `expRho` in
    statements, no vacuous hypotheses.  Reusable ASSEMBLY brick; NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.SliverEstimates

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open scoped Interval Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- The standard unit coordinate vector `eᵢ` (as a `Point n`). -/
noncomputable def unitVec (i : Fin n) : Point n := Pi.single i (1 : ℝ)

/-! ###############################################################################
    Bridge helpers — the sup-norm inner-product estimate + single-coordinate facts.
    ############################################################################### -/

/-- **The sup-norm inner-product bound.**  `|∑ₖ a k · b k| ≤ n·‖a‖·‖b‖`, via `|a k| ≤ ‖a‖`
    (`norm_le_pi_norm`) coordinatewise. -/
theorem abs_inner_le (a b : Point n) : |∑ k, a k * b k| ≤ (n : ℝ) * ‖a‖ * ‖b‖ := by
  calc |∑ k, a k * b k|
      ≤ ∑ k, |a k * b k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |a k| * |b k| := Finset.sum_congr rfl (fun k _ => abs_mul _ _)
    _ ≤ ∑ _k : Fin n, ‖a‖ * ‖b‖ :=
        Finset.sum_le_sum (fun k _ =>
          mul_le_mul
            (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm a k)
            (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm b k)
            (abs_nonneg _) (norm_nonneg _))
    _ = (n : ℝ) * ‖a‖ * ‖b‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `‖eᵢ‖ ≤ 1` for the standard unit `eᵢ = unitVec i` (sup norm). -/
theorem norm_single_le_one (i : Fin n) : ‖(unitVec i : Point n)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
  intro k
  simp only [unitVec, Pi.single_apply]
  split <;> simp

/-- `∑ₖ z k · (eᵢ)k = z i`. -/
theorem sum_mul_single_eq (z : Point n) (i : Fin n) :
    ∑ k, z k * unitVec i k = z i := by
  have h : ∀ k, z k * unitVec i k = if k = i then z k else 0 := by
    intro k; simp only [unitVec, Pi.single_apply]; split <;> simp
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_ite_eq' Finset.univ i]
  simp

/-- `∑ₖ (eᵢ)k · (eᵢ)k = 1`. -/
theorem sum_single_sq_eq_one (i : Fin n) :
    ∑ k, unitVec i k * unitVec i k = 1 := by
  have h : ∀ k, unitVec i k * unitVec i k = if k = i then 1 else 0 := by
    intro k; simp only [unitVec, Pi.single_apply]; split <;> simp
  rw [Finset.sum_congr rfl (fun k _ => h k), Finset.sum_ite_eq' Finset.univ i]
  simp

/-- `∑ₖ c k · c k ≤ n·‖c‖²` (each square `≤ ‖c‖²`). -/
theorem sum_sq_le (c : Point n) : ∑ k, c k * c k ≤ (n : ℝ) * ‖c‖ ^ 2 := by
  calc ∑ k, c k * c k
      ≤ ∑ _k : Fin n, ‖c‖ ^ 2 := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        have hck : |c k| ≤ ‖c‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm c k
        nlinarith [abs_nonneg (c k), norm_nonneg c, sq_abs (c k)]
    _ = (n : ℝ) * ‖c‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `∑ₖ c k · c k ≥ 0`. -/
theorem sum_sq_nonneg (c : Point n) : 0 ≤ ∑ k, c k * c k :=
  Finset.sum_nonneg (fun k _ => mul_self_nonneg _)

/-! ###############################################################################
    ★ THE T1' BRIDGE BOUNDS — Hermite-argument replacement estimates.
    ############################################################################### -/

/-- **★ First bridge — `⟨Y,P⟩ ≈ −z i`.**  With the inverse-chart displacement `‖Y + z‖ ≤ β`
    (`chartW0_displacement`, so `Y ≈ −z`) and the first-jet gap `‖P − eᵢ‖ ≤ γ` (`hJ3`, `P ≈ eᵢ`),
      `|⟨Y,P⟩ + z i| ≤ n·β·γ + n·β + n·‖z‖·γ`.
    (Writing `b := Y+z`, `c := P−eᵢ`, `⟨Y,P⟩ + z i = ⟨b,c⟩ + ⟨b,eᵢ⟩ − ⟨z,c⟩`; each `⟨·,·⟩` is bounded
    by `abs_inner_le`.)  On the ball `‖z‖ ≤ 1` this is the QUADRATIC gain `≤ C·‖z‖²`. -/
theorem innerYP_add_zi_bound (Y z Pv : Point n) (i : Fin n) (β γ : ℝ)
    (hb : ‖Y + z‖ ≤ β) (hc : ‖Pv - unitVec i‖ ≤ γ) :
    |(∑ k, Y k * Pv k) + z i| ≤ (n : ℝ) * β * γ + (n : ℝ) * β + (n : ℝ) * ‖z‖ * γ := by
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg _) hb
  have hγ0 : 0 ≤ γ := le_trans (norm_nonneg _) hc
  set A : ℝ := ∑ k, (Y + z) k * (Pv - unitVec i) k with hA
  set B : ℝ := ∑ k, (Y + z) k * unitVec i k with hB
  set C : ℝ := ∑ k, z k * (Pv - unitVec i) k with hC
  -- the exact regrouping identity.
  have hsum_eq : (∑ k, Y k * Pv k) + z i = A + B - C := by
    have e1 : A + B - C
        = ∑ k, ((Y + z) k * (Pv - unitVec i) k + (Y + z) k * unitVec i k
            - z k * (Pv - unitVec i) k) := by
      rw [hA, hB, hC, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    have e2 : ∀ k, (Y + z) k * (Pv - unitVec i) k + (Y + z) k * unitVec i k
          - z k * (Pv - unitVec i) k
        = Y k * Pv k + z k * unitVec i k := by
      intro k; simp only [Pi.add_apply, Pi.sub_apply]; ring
    rw [e1, Finset.sum_congr rfl (fun k _ => e2 k), Finset.sum_add_distrib, sum_mul_single_eq]
  rw [hsum_eq]
  -- triangle |A + B − C| ≤ |A| + |B| + |C|.
  have htri : |A + B - C| ≤ |A| + |B| + |C| := by
    calc |A + B - C| = |(A + B) + (-C)| := by rw [sub_eq_add_neg]
      _ ≤ |A + B| + |(-C)| := abs_add_le _ _
      _ ≤ (|A| + |B|) + |(-C)| := add_le_add (abs_add_le _ _) (le_refl _)
      _ = |A| + |B| + |C| := by rw [abs_neg]
  -- bound each inner product.
  have hAbd : |A| ≤ (n : ℝ) * β * γ :=
    (abs_inner_le (Y + z) (Pv - unitVec i)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) hc
        (norm_nonneg _) (mul_nonneg (by positivity) hβ0))
  have hBbd : |B| ≤ (n : ℝ) * β := by
    refine (abs_inner_le (Y + z) (unitVec i)).trans ?_
    have h1 : (n : ℝ) * ‖Y + z‖ * ‖(unitVec i : Point n)‖ ≤ (n : ℝ) * β * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity)) (norm_single_le_one i)
        (norm_nonneg _) (mul_nonneg (by positivity) hβ0)
    linarith [h1]
  have hCbd : |C| ≤ (n : ℝ) * ‖z‖ * γ :=
    (abs_inner_le z (Pv - unitVec i)).trans
      (mul_le_mul_of_nonneg_left hc (by positivity))
  linarith [htri, hAbd, hBbd, hCbd]

/-- **★ Cubic bridge — `⟨Y,P⟩² ≈ (z i)²`.**  From `|⟨Y,P⟩ + z i| ≤ Δ` (the first bridge, so
    `⟨Y,P⟩ ≈ −z i`),
      `|⟨Y,P⟩² − (z i)²| ≤ Δ·(Δ + 2‖z‖)`.
    (`⟨Y,P⟩² − (z i)² = (⟨Y,P⟩ + z i)·(⟨Y,P⟩ − z i)`; `|⟨Y,P⟩ − z i| ≤ Δ + 2|z i| ≤ Δ + 2‖z‖`.)
    With `Δ ~ C‖z‖²` this is the CUBIC gain `≤ C‖z‖³` feeding `∫‖z‖³·G/τ² ~ τ^{−1/2}`. -/
theorem innerYP_sq_sub_zi_sq_bound (Y z Pv : Point n) (i : Fin n) (Δ : ℝ)
    (hΔ : |(∑ k, Y k * Pv k) + z i| ≤ Δ) :
    |(∑ k, Y k * Pv k) ^ 2 - (z i) ^ 2| ≤ Δ * (Δ + 2 * ‖z‖) := by
  set S : ℝ := ∑ k, Y k * Pv k with hS
  have hΔ0 : 0 ≤ Δ := le_trans (abs_nonneg _) hΔ
  have hzi : |z i| ≤ ‖z‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z i
  have hfac : S ^ 2 - (z i) ^ 2 = (S + z i) * (S - z i) := by ring
  have hSsub : |S - z i| ≤ Δ + 2 * ‖z‖ := by
    have h : S - z i = (S + z i) - 2 * z i := by ring
    rw [h]
    calc |(S + z i) - 2 * z i|
        = |(S + z i) + (-(2 * z i))| := by rw [sub_eq_add_neg]
      _ ≤ |S + z i| + |(-(2 * z i))| := abs_add_le _ _
      _ = |S + z i| + |2 * z i| := by rw [abs_neg]
      _ ≤ Δ + 2 * ‖z‖ := by rw [abs_mul, abs_two]; linarith [hΔ, hzi]
  rw [hfac, abs_mul]
  exact mul_le_mul hΔ hSsub (abs_nonneg _) hΔ0

/-- **★ Coercive bridge — `⟨P,P⟩ ≈ 1`.**  With `‖P − eᵢ‖ ≤ γ` (`hJ3`),
      `|⟨P,P⟩ − 1| ≤ n·γ² + 2·γ`.
    (`c := P − eᵢ`; `⟨P,P⟩ − 1 = ⟨c,c⟩ + 2·c i`; `⟨c,c⟩ ≤ n‖c‖² ≤ nγ²`, `2|c i| ≤ 2‖c‖ ≤ 2γ`.)
    On the ball this is the LINEAR gain `≤ C‖z‖` feeding `∫‖z‖·G/τ ~ τ^{−1/2}`. -/
theorem innerPP_sub_one_bound (Pv : Point n) (i : Fin n) (γ : ℝ)
    (hc : ‖Pv - unitVec i‖ ≤ γ) :
    |(∑ k, Pv k * Pv k) - 1| ≤ (n : ℝ) * γ ^ 2 + 2 * γ := by
  have hγ0 : 0 ≤ γ := le_trans (norm_nonneg _) hc
  set c : Point n := Pv - unitVec i with hcdef
  have hPeq : Pv = c + unitVec i := by rw [hcdef]; abel
  -- expand ⟨P,P⟩ = ⟨c,c⟩ + 2⟨c,eᵢ⟩ + ⟨eᵢ,eᵢ⟩.
  have hexp : (∑ k, Pv k * Pv k)
      = (∑ k, c k * c k) + 2 * (∑ k, c k * unitVec i k)
        + (∑ k, unitVec i k * unitVec i k) := by
    rw [hPeq]
    have hpt : ∀ k, (c + unitVec i) k * (c + unitVec i) k
        = c k * c k + 2 * (c k * unitVec i k)
          + unitVec i k * unitVec i k := by
      intro k; simp only [Pi.add_apply]; ring
    rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
  rw [hexp, sum_mul_single_eq, sum_single_sq_eq_one]
  have hci : |c i| ≤ ‖c‖ := by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm c i
  have hcnormsq : ‖c‖ ^ 2 ≤ γ ^ 2 := by nlinarith [norm_nonneg c, hc, hγ0]
  have hsumsq : (∑ k, c k * c k) ≤ (n : ℝ) * γ ^ 2 :=
    le_trans (sum_sq_le c) (by nlinarith [Nat.cast_nonneg (α := ℝ) n, hcnormsq])
  -- |⟨c,c⟩ + 2 c i + 1 − 1| = |⟨c,c⟩ + 2 c i|.
  have hgoal : (∑ k, c k * c k) + 2 * c i + 1 - 1 = (∑ k, c k * c k) + 2 * c i := by ring
  rw [hgoal]
  calc |(∑ k, c k * c k) + 2 * c i|
      ≤ |∑ k, c k * c k| + |2 * c i| := abs_add_le _ _
    _ = (∑ k, c k * c k) + 2 * |c i| := by
        rw [abs_of_nonneg (sum_sq_nonneg c), abs_mul, abs_two]
    _ ≤ (n : ℝ) * γ ^ 2 + 2 * γ := by
        have h2 : 2 * |c i| ≤ 2 * γ :=
          mul_le_mul_of_nonneg_left (le_trans hci hc) (by norm_num)
        linarith [hsumsq, h2]

/-- `‖Y‖ ≤ β + ‖z‖` from `‖Y + z‖ ≤ β` (since `Y = (Y+z) − z`). -/
theorem normY_le (Y z : Point n) (β : ℝ) (hb : ‖Y + z‖ ≤ β) : ‖Y‖ ≤ β + ‖z‖ := by
  calc ‖Y‖ = ‖(Y + z) - z‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖Y + z‖ + ‖z‖ := norm_sub_le _ _
    _ ≤ β + ‖z‖ := by linarith

/-- **★ CenterJet bridge — `⟨Y,Q⟩ = O(‖z‖)`.**  With `‖Y + z‖ ≤ β` and the second-jet bound
    `‖Q‖ ≤ C_Q` (`hJ3Q`),
      `|⟨Y,Q⟩| ≤ n·(β + ‖z‖)·C_Q`.
    (`abs_inner_le` + `normY_le`.)  On the ball this is the LINEAR gain feeding `∫‖z‖·G/τ ~ τ^{−1/2}`
    (crude — no parity needed). -/
theorem innerYQ_bound (Y z Qv : Point n) (β CQ : ℝ)
    (hb : ‖Y + z‖ ≤ β) (hQ : ‖Qv‖ ≤ CQ) (hCQ : 0 ≤ CQ) :
    |∑ k, Y k * Qv k| ≤ (n : ℝ) * (β + ‖z‖) * CQ := by
  refine (abs_inner_le Y Qv).trans ?_
  have hYnn : 0 ≤ ‖Y‖ := norm_nonneg _
  calc (n : ℝ) * ‖Y‖ * ‖Qv‖
      ≤ (n : ℝ) * (β + ‖z‖) * CQ :=
        mul_le_mul (mul_le_mul_of_nonneg_left (normY_le Y z β hb) (by positivity)) hQ
          (norm_nonneg _)
          (by have := le_trans hYnn (normY_le Y z β hb); positivity)

/-! ###############################################################################
    The off-gate tail brick — the exponential beats `1/τ`.
    ############################################################################### -/

/-- `(x/2)² ≤ eˣ` for `x ≥ 0`.  Route: `e^{x/2} ≥ 1 + x/2 ≥ x/2 ≥ 0`, then square. -/
theorem sq_half_le_exp (x : ℝ) (hx : 0 ≤ x) : (x / 2) ^ 2 ≤ Real.exp x := by
  have h1 : x / 2 ≤ Real.exp (x / 2) := by
    have := Real.add_one_le_exp (x / 2); linarith
  have h0 : 0 ≤ x / 2 := by linarith
  have hsq : (x / 2) ^ 2 ≤ Real.exp (x / 2) ^ 2 := by
    have := mul_le_mul h1 h1 h0 (Real.exp_pos _).le
    nlinarith [this]
  calc (x / 2) ^ 2 ≤ Real.exp (x / 2) ^ 2 := hsq
    _ = Real.exp x := by rw [pow_two, ← Real.exp_add]; congr 1; ring

/-- **★ Off-gate tail brick — the exponential beats `1/τ`.**  For `c, τ > 0`,
      `e^{−c/τ} / τ ≤ 4·τ / c²`.
    Route: with `x = c/τ > 0`, `e^{−x} = 1/eˣ ≤ 4/x²` (from `(x/2)² ≤ eˣ`), so
    `e^{−c/τ}/τ ≤ (4/(c/τ)²)/τ = 4τ/c²`.  Hence `∫₀^ε (1/τ)·(n√2·e^{−δ²/8τ}) ~ ε²/δ⁴ → 0`, killing
    the off-ball tail of the FORMAL derivative faster than any power of `τ`. -/
theorem exp_tail_beats_inv (c τ : ℝ) (hc : 0 < c) (hτ : 0 < τ) :
    Real.exp (-c / τ) / τ ≤ 4 * τ / c ^ 2 := by
  set x : ℝ := c / τ with hx
  have hxpos : 0 < x := div_pos hc hτ
  have hexp_ge : x ^ 2 / 4 ≤ Real.exp x := by
    have h := sq_half_le_exp x hxpos.le; nlinarith [h]
  have hx24pos : 0 < x ^ 2 / 4 := by positivity
  -- e^{−x} ≤ 4/x².
  have hemx : Real.exp (-x) ≤ 4 / x ^ 2 := by
    rw [Real.exp_neg]
    calc (Real.exp x)⁻¹ = 1 / Real.exp x := by rw [one_div]
      _ ≤ 1 / (x ^ 2 / 4) := one_div_le_one_div_of_le hx24pos hexp_ge
      _ = 4 / x ^ 2 := by rw [one_div_div]
  have hexpc : Real.exp (-c / τ) = Real.exp (-x) := by congr 1; rw [hx]; ring
  rw [hexpc]
  calc Real.exp (-x) / τ = Real.exp (-x) * τ⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (4 / x ^ 2) * τ⁻¹ := mul_le_mul_of_nonneg_right hemx (by positivity)
    _ = 4 * τ / c ^ 2 := by rw [hx]; field_simp

/-! ###############################################################################
    The concrete normal-form terms (the 3-term Leibniz-Gaussian shape).
    ############################################################################### -/

/-- **`sTerm0`** — the Hessian-weighted concrete term of the normal form:
    `G_τ(Y z)·[⟨Y z,P z⟩²/4τ² − (⟨P z,P z⟩+⟨Y z,Q z⟩)/2τ]·A₀ τ z`. -/
noncomputable def sTerm0 (Y P Q : Point n → Point n) (A0 : ℝ → Point n → ℝ)
    (τ : ℝ) (z : Point n) : ℝ :=
  gaussDdim τ (Y z)
    * ((∑ k, Y z k * P z k) ^ 2 / (4 * τ ^ 2)
        - ((∑ k, P z k * P z k) + (∑ k, Y z k * Q z k)) / (2 * τ))
    * A0 τ z

/-- **`sTerm1`** — the gradient-weighted concrete term of the normal form:
    `2·G_τ(Y z)·(−⟨Y z,P z⟩/2τ)·A₁ τ z`. -/
noncomputable def sTerm1 (Y P : Point n → Point n) (A1 : ℝ → Point n → ℝ)
    (τ : ℝ) (z : Point n) : ℝ :=
  2 * (gaussDdim τ (Y z) * (-(∑ k, Y z k * P z k) / (2 * τ))) * A1 τ z

/-- **`sTerm2`** — the mass-weighted concrete term of the normal form: `G_τ(Y z)·A₂ τ z`. -/
noncomputable def sTerm2 (Y : Point n → Point n) (A2 : ℝ → Point n → ℝ)
    (τ : ℝ) (z : Point n) : ℝ :=
  gaussDdim τ (Y z) * A2 τ z

/-! ###############################################################################
    ★★★ THE S6 ASSEMBLY — the concrete formal-Hessian sliver `√ε` bound.
    ############################################################################### -/

/-- **★★★ J4-133 — THE S6 ASSEMBLY.**  The terminal formal second-`x`-derivative sliver for the
    CONCRETE van-Vleck witness (base-`z`-dependent chart jets `Y/P/Q`, amplitudes `A₀/A₁/A₂`) obeys
    the `√ε` bound.  Given
      • `hNormalForm` — the concrete Leibniz-Gaussian 3-term identity (`gaussComp_amp_pd_pd`
        instantiated): `D2H τ z = sTerm0 τ z + sTerm1 τ z + sTerm2 τ z` on `Ioo 0 τ₀`;
      • `hInner0`/`hInner1` — the Hessian/gradient per-slice inner bounds with the `(u−s)^{−1/2}` rate
        (satisfiable via the T1' bridges + `gaussian_hessian_cancel` + `weighted_chart_replace_bound`
        + `pow_norm_mul_gauss_integral`; see FIREWALL);
      • `hInner2` — the mass per-slice inner bound, `O(1)`;
      • `hInt0`/`hInt1`/`hInt2` — the per-slice base integrabilities,
    the terminal sliver obeys
      `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z 0| ≤ (C₀+C₁)·2√ε + C₂·ε`.
    Route: split the inner integral into the three concrete terms (algebra identity PROVED via
    `hNormalForm` + `integral_add`), bound each by its carried rate, then the banked `sliver_rpow_sub`.
    NOT `a₁ = R/6`. -/
theorem witness_sliver2_assembly
    (D2H : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (Y P Q : Point n → Point n) (A0 A1 A2 : ℝ → Point n → ℝ)
    (C₀ C₁ C₂ τ₀ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (u ε : ℝ) (hε0 : 0 ≤ ε) (hεu : ε ≤ u) (hετ₀ : ε ≤ τ₀)
    (hNormalForm : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z : Point n,
        D2H τ z = sTerm0 Y P Q A0 τ z + sTerm1 Y P A1 τ z + sTerm2 Y A2 τ z)
    (hInner0 : ∀ s ∈ Set.Ioo (u - ε) u,
        |∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0| ≤ C₀ * (u - s) ^ (-(1 : ℝ) / 2))
    (hInner1 : ∀ s ∈ Set.Ioo (u - ε) u,
        |∫ z, sTerm1 Y P A1 (u - s) z * F s z 0| ≤ C₁ * (u - s) ^ (-(1 : ℝ) / 2))
    (hInner2 : ∀ s ∈ Set.Ioo (u - ε) u,
        |∫ z, sTerm2 Y A2 (u - s) z * F s z 0| ≤ C₂)
    (hInt0 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm0 Y P Q A0 (u - s) z * F s z 0) volume)
    (hInt1 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm1 Y P A1 (u - s) z * F s z 0) volume)
    (hInt2 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm2 Y A2 (u - s) z * F s z 0) volume) :
    |∫ s in (u - ε)..u, ∫ z, D2H (u - s) z * F s z 0|
      ≤ (C₀ + C₁) * (2 * Real.sqrt ε) + C₂ * ε := by
  -- per-slice inner bound (rpow form)
  have hpsl : ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, D2H (u - s) z * F s z 0| ≤ (C₀ + C₁) * (u - s) ^ (-(1 : ℝ) / 2) + C₂ := by
    intro s hs
    have hτpos : 0 < u - s := by linarith [hs.2]
    have hττ₀ : u - s < τ₀ := by linarith [hs.1, hετ₀]
    have hτIoo : (u - s) ∈ Set.Ioo (0 : ℝ) τ₀ := ⟨hτpos, hττ₀⟩
    -- split the inner integral into the three concrete terms.
    have hpt : ∀ z, D2H (u - s) z * F s z 0
        = sTerm0 Y P Q A0 (u - s) z * F s z 0
          + sTerm1 Y P A1 (u - s) z * F s z 0
          + sTerm2 Y A2 (u - s) z * F s z 0 := by
      intro z; rw [hNormalForm (u - s) hτIoo z]; ring
    have e1 : (∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0
          + sTerm1 Y P A1 (u - s) z * F s z 0)
        = (∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0)
          + ∫ z, sTerm1 Y P A1 (u - s) z * F s z 0 :=
      integral_add (hInt0 s hs) (hInt1 s hs)
    have e2 : (∫ z, (sTerm0 Y P Q A0 (u - s) z * F s z 0
            + sTerm1 Y P A1 (u - s) z * F s z 0)
          + sTerm2 Y A2 (u - s) z * F s z 0)
        = (∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0
            + sTerm1 Y P A1 (u - s) z * F s z 0)
          + ∫ z, sTerm2 Y A2 (u - s) z * F s z 0 :=
      integral_add ((hInt0 s hs).add (hInt1 s hs)) (hInt2 s hs)
    have hsplit : (∫ z, D2H (u - s) z * F s z 0)
        = (∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0)
          + (∫ z, sTerm1 Y P A1 (u - s) z * F s z 0)
          + (∫ z, sTerm2 Y A2 (u - s) z * F s z 0) := by
      rw [integral_congr_ae (ae_of_all _ hpt), e2, e1]
    rw [hsplit]
    calc |(∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0)
            + (∫ z, sTerm1 Y P A1 (u - s) z * F s z 0)
            + (∫ z, sTerm2 Y A2 (u - s) z * F s z 0)|
        ≤ |∫ z, sTerm0 Y P Q A0 (u - s) z * F s z 0|
            + |∫ z, sTerm1 Y P A1 (u - s) z * F s z 0|
            + |∫ z, sTerm2 Y A2 (u - s) z * F s z 0| :=
          le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) (le_refl _))
      _ ≤ C₀ * (u - s) ^ (-(1 : ℝ) / 2) + C₁ * (u - s) ^ (-(1 : ℝ) / 2) + C₂ :=
          add_le_add (add_le_add (hInner0 s hs) (hInner1 s hs)) (hInner2 s hs)
      _ = (C₀ + C₁) * (u - s) ^ (-(1 : ℝ) / 2) + C₂ := by ring
  -- assemble the outer sliver.
  rw [← Real.norm_eq_abs]
  calc ‖∫ s in (u - ε)..u, ∫ z, D2H (u - s) z * F s z 0‖
      ≤ ∫ s in (u - ε)..u, ((C₀ + C₁) * (u - s) ^ (-(1 : ℝ) / 2) + C₂) := by
        refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_
          (((rpow_sub_intervalIntegrable u ε hε0).const_mul _).add intervalIntegrable_const)
        filter_upwards [ae_ne_point u] with s hsu hsmem
        have hs_mem : s ∈ Set.Ioo (u - ε) u := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hsu⟩
        rw [Real.norm_eq_abs]; exact hpsl s hs_mem
    _ = (C₀ + C₁) * (2 * Real.sqrt ε) + C₂ * ε := by
        rw [intervalIntegral.integral_add ((rpow_sub_intervalIntegrable u ε hε0).const_mul _)
            intervalIntegrable_const, intervalIntegral.integral_const_mul, sliver_rpow_sub u ε hε0,
            intervalIntegral.integral_const, smul_eq_mul, show u - (u - ε) = ε from by ring]
        ring

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.abs_inner_le
#print axioms QIQTH.HeatResidualBound.innerYP_add_zi_bound
#print axioms QIQTH.HeatResidualBound.innerYP_sq_sub_zi_sq_bound
#print axioms QIQTH.HeatResidualBound.innerPP_sub_one_bound
#print axioms QIQTH.HeatResidualBound.innerYQ_bound
#print axioms QIQTH.HeatResidualBound.exp_tail_beats_inv
#print axioms QIQTH.HeatResidualBound.witness_sliver2_assembly
