/-
  PartialsToFDeriv — J4-158: the CLASSICAL analysis theorem
  "continuous coordinate partials ⟹ Fréchet differentiability" on `Point n = Fin n → ℝ`,
  plus the `hAssembly` reduction it discharges in the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It supplies ONE
  reusable brick: the standard multivariable-calculus fact that if `f : (Fin n → ℝ) → ℝ` has, on a
  ball around `x₀`, coordinate partial derivatives (in the `Function.update`-line form that matches
  the repo's `pd` machinery) whose derivative functions `gᵢ` are continuous at `x₀`, then `f` is
  Fréchet-differentiable at `x₀` with derivative `∑ᵢ gᵢ(x₀) • (proj i)`.

  Mathlib has this only for the BIVARIATE product `E₁ × E₂` (`hasStrictFDerivAt_uncurry_coprod`,
  `Analysis/Calculus/FDeriv/Partial.lean`); there is **no** single lemma for a general `Fin n → ℝ`
  domain — that is the J4-155-identified gap, closed here by the standard telescoping + 1-D
  mean-value estimate.

  ── PROOF TECHNIQUE.  Coordinate path `p k j := if (j:ℕ) < k then y j else x₀ j` (`p 0 = x₀`,
     `p n = y`, each step flips ONE coordinate: `p (k+1) = update (p k) k (y k)`).  Telescoping
     `∑_{i:Fin n} (f (p (i+1)) − f (p i)) = f y − f x₀` (`Fin.sum_univ_eq_sum_range` +
     `Finset.sum_range_sub`).  Each step is bounded by the 1-D MVT on the `uIcc` segment
     (`norm_image_sub_le_of_norm_hasDerivWithin_le`, orientation-free), with the derivative-defect
     `|gᵢ(z) − gᵢ(x₀)|` uniformly small once `‖y − x₀‖` is small (continuity of `gᵢ` at `x₀`, via
     `Filter.eventually_all` over `Fin n`).  Summing gives the `isLittleO`.

  ── COROLLARY `hAssembly_reduced` — plugs the theorem into `hCConv_L1_of_partialsContinuity`'s
     `hAssembly` slot, reducing that carried assembly to: (a) the linewise partials on the open set
     (from `hConvDeriv_linewise`), (b) the CONTINUITY of the derivative-integral coefficient
     functions near `0` (the NEW carried, dominated-convergence, labelled input), (c) the
     coefficient/`proj`-sum representation of `D`.

  NO `sorry`.  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CConvLayerDischarge

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open scoped BigOperators Topology

namespace QIQTH.PartialsToFDeriv

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- If `s` lies in the (unordered) segment `[[a, b]]`, then `|s − a| ≤ |b − a|`.  The elementary
    orientation-free 1-D fact used to keep segment points inside the ball. -/
theorem abs_sub_le_of_mem_uIcc {a b s : ℝ} (h : s ∈ Set.uIcc a b) : |s - a| ≤ |b - a| := by
  rcases Set.mem_uIcc.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith

/-- **★ THE THEOREM (J4-158).**  Continuous coordinate partials ⟹ Fréchet differentiability on
    `Point n = Fin n → ℝ`.

    Hypotheses on a ball `B(x₀, r)`:
      • `hpart` — the coordinate partials exist in the `Function.update`-line form: for every
        `y ∈ B` and every `i`, `s ↦ f (update y i s)` has derivative `g i y` at `y i`;
      • `hcont` — each derivative function `g i` is `ContinuousAt` `x₀`.
    Conclusion: `HasFDerivAt f (∑ i, (g i x₀) • proj i) x₀`, where `proj i` is the `i`-th coordinate
    evaluation CLM.  NOT `a₁ = R/6`. -/
theorem partials_continuous_hasFDerivAt
    (f : Point n → ℝ) (x₀ : Point n) (r : ℝ) (hr : 0 < r)
    (g : Fin n → Point n → ℝ)
    (hpart : ∀ y ∈ Metric.ball x₀ r, ∀ i : Fin n,
       HasDerivAt (fun s => f (Function.update y i s)) (g i y) (y i))
    (hcont : ∀ i : Fin n, ContinuousAt (g i) x₀) :
    HasFDerivAt f
      (∑ i : Fin n, (g i x₀) • (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ)) x₀ := by
  set L : Point n →L[ℝ] ℝ :=
    ∑ i : Fin n, (g i x₀) • (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ) with hLdef
  -- action of `L`.
  have hLapp : ∀ v : Point n, L v = ∑ i : Fin n, g i x₀ * v i := by
    intro v
    rw [hLdef, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- degenerate domain `Point 0` is a subsingleton.
    subst hn0
    filter_upwards with y
    have hyx : y = x₀ := Subsingleton.elim y x₀
    subst hyx
    simp [hLdef]
    positivity
  · -- the substantive case `n > 0`.
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
    have hnRpos : (0 : ℝ) < n := by exact_mod_cast hnpos
    set ε' : ℝ := ε / (n : ℝ) with hε'def
    have hε' : 0 < ε' := div_pos hε hnRpos
    have hnε : (n : ℝ) * ε' = ε := by rw [hε'def]; exact mul_div_cancel₀ ε hnR
    -- a single δ making every coefficient defect ≤ ε'.
    have hcomb : ∀ᶠ z in 𝓝 x₀, ∀ i : Fin n, dist (g i z) (g i x₀) ≤ ε' := by
      rw [Filter.eventually_all]
      intro i
      exact (Metric.tendsto_nhds.mp (hcont i).tendsto ε' hε').mono (fun z hz => hz.le)
    rw [Metric.eventually_nhds_iff] at hcomb
    obtain ⟨δ, hδ, hδball⟩ := hcomb
    set ρ : ℝ := min r δ with hρdef
    have hρpos : 0 < ρ := lt_min hr hδ
    filter_upwards [Metric.ball_mem_nhds x₀ hρpos] with y hy
    have hyρ : dist y x₀ < ρ := Metric.mem_ball.mp hy
    have hynorm : ‖y - x₀‖ < r := by
      rw [← dist_eq_norm]; exact lt_of_lt_of_le hyρ (min_le_left _ _)
    have hynormδ : ‖y - x₀‖ < δ := by
      rw [← dist_eq_norm]; exact lt_of_lt_of_le hyρ (min_le_right _ _)
    have hcoord : ∀ j : Fin n, |y j - x₀ j| ≤ ‖y - x₀‖ := by
      intro j
      have := norm_le_pi_norm (y - x₀) j
      simpa [Real.norm_eq_abs, Pi.sub_apply] using this
    -- the coordinate path.
    set p : ℕ → Point n := fun k j => if (j : ℕ) < k then y j else x₀ j with hpdef
    have hp0 : p 0 = x₀ := by funext j; simp [hpdef]
    have hpn : p n = y := by funext j; simp only [hpdef]; rw [if_pos j.isLt]
    have hbefore : ∀ i : Fin n, p (i : ℕ) i = x₀ i := by
      intro i; simp only [hpdef]; rw [if_neg (lt_irrefl _)]
    have hstepupd : ∀ i : Fin n,
        p ((i : ℕ) + 1) = Function.update (p (i : ℕ)) i (y i) := by
      intro i; funext j
      by_cases hji : j = i
      · subst hji
        rw [Function.update_self]; simp only [hpdef]; rw [if_pos (Nat.lt_succ_self _)]
      · rw [Function.update_of_ne hji]
        have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
        simp only [hpdef]
        by_cases hlt : (j : ℕ) < (i : ℕ)
        · rw [if_pos (by omega), if_pos hlt]
        · rw [if_neg (by omega), if_neg hlt]
    -- per-coordinate MVT step bound.
    have hDbound : ∀ i : Fin n,
        ‖f (p ((i : ℕ) + 1)) - f (p (i : ℕ)) - g i x₀ * (y i - x₀ i)‖
          ≤ ε' * |y i - x₀ i| := by
      intro i
      -- segment points stay within `‖y − x₀‖` of `x₀`.
      have hnormbound : ∀ s ∈ Set.uIcc (x₀ i) (y i),
          ‖Function.update (p (i : ℕ)) i s - x₀‖ ≤ ‖y - x₀‖ := by
        intro s hs
        rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
        intro j
        rw [Pi.sub_apply, Real.norm_eq_abs, Function.update_apply]
        by_cases hji : j = i
        · subst hji
          rw [if_pos rfl]
          exact le_trans (abs_sub_le_of_mem_uIcc hs) (hcoord j)
        · rw [if_neg hji]
          simp only [hpdef]
          by_cases hlt : (j : ℕ) < (i : ℕ)
          · rw [if_pos hlt]; exact hcoord j
          · rw [if_neg hlt, sub_self, abs_zero]; exact norm_nonneg _
      have hzball : ∀ s ∈ Set.uIcc (x₀ i) (y i),
          Function.update (p (i : ℕ)) i s ∈ Metric.ball x₀ r := by
        intro s hs
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_le_of_lt (hnormbound s hs) hynorm
      -- derivative of the 1-D shifted function on the segment.
      have hderiv : ∀ s ∈ Set.uIcc (x₀ i) (y i),
          HasDerivWithinAt (fun s => f (Function.update (p (i : ℕ)) i s) - g i x₀ * s)
            (g i (Function.update (p (i : ℕ)) i s) - g i x₀) (Set.uIcc (x₀ i) (y i)) s := by
        intro s hs
        have hd := hpart (Function.update (p (i : ℕ)) i s) (hzball s hs) i
        rw [Function.update_self] at hd
        simp only [Function.update_idem] at hd
        have hlin : HasDerivAt (fun s : ℝ => g i x₀ * s) (g i x₀) s := by
          simpa using (hasDerivAt_id s).const_mul (g i x₀)
        exact (hd.sub hlin).hasDerivWithinAt
      -- uniform bound on that derivative over the segment.
      have hboundfn : ∀ s ∈ Set.uIcc (x₀ i) (y i),
          ‖g i (Function.update (p (i : ℕ)) i s) - g i x₀‖ ≤ ε' := by
        intro s hs
        have hzδ : dist (Function.update (p (i : ℕ)) i s) x₀ < δ := by
          rw [dist_eq_norm]; exact lt_of_le_of_lt (hnormbound s hs) hynormδ
        have h := hδball hzδ i
        rw [Real.dist_eq] at h
        rwa [Real.norm_eq_abs]
      have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hboundfn
        (convex_uIcc (x₀ i) (y i)) Set.left_mem_uIcc Set.right_mem_uIcc
      -- identify the segment endpoints with the path points.
      have he_after : f (Function.update (p (i : ℕ)) i (y i)) = f (p ((i : ℕ) + 1)) := by
        rw [← hstepupd i]
      have he_before : f (Function.update (p (i : ℕ)) i (x₀ i)) = f (p (i : ℕ)) := by
        congr 1
        conv_lhs => rw [← hbefore i]
        rw [Function.update_eq_self]
      have hbeta : (fun s => f (Function.update (p (i : ℕ)) i s) - g i x₀ * s) (y i)
                 - (fun s => f (Function.update (p (i : ℕ)) i s) - g i x₀ * s) (x₀ i)
                 = f (p ((i : ℕ) + 1)) - f (p (i : ℕ)) - g i x₀ * (y i - x₀ i) := by
        simp only []
        rw [he_after, he_before]; ring
      rw [hbeta] at hmvt
      rw [Real.norm_eq_abs (y i - x₀ i)] at hmvt
      exact hmvt
    -- telescoping + assembly.
    have htel : (∑ i : Fin n, (f (p ((i : ℕ) + 1)) - f (p (i : ℕ)))) = f y - f x₀ := by
      rw [Fin.sum_univ_eq_sum_range (fun k => f (p (k + 1)) - f (p k)) n,
        Finset.sum_range_sub (fun k => f (p k)) n, hpn, hp0]
    have hLval : L (y - x₀) = ∑ i : Fin n, g i x₀ * (y i - x₀ i) := by
      rw [hLapp]; refine Finset.sum_congr rfl ?_; intro i _; rw [Pi.sub_apply]
    have hfinal : f y - f x₀ - L (y - x₀)
        = ∑ i : Fin n, (f (p ((i : ℕ) + 1)) - f (p (i : ℕ)) - g i x₀ * (y i - x₀ i)) := by
      rw [← htel, hLval, ← Finset.sum_sub_distrib]
    show ‖f y - f x₀ - L (y - x₀)‖ ≤ ε * ‖y - x₀‖
    rw [hfinal]
    calc ‖∑ i : Fin n, (f (p ((i : ℕ) + 1)) - f (p (i : ℕ)) - g i x₀ * (y i - x₀ i))‖
        ≤ ∑ i : Fin n, ‖f (p ((i : ℕ) + 1)) - f (p (i : ℕ)) - g i x₀ * (y i - x₀ i)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ε' * |y i - x₀ i| := Finset.sum_le_sum (fun i _ => hDbound i)
      _ ≤ ∑ i : Fin n, ε' * ‖y - x₀‖ :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hcoord i) hε'.le)
      _ = (n : ℝ) * (ε' * ‖y - x₀‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ε * ‖y - x₀‖ := by rw [← mul_assoc, hnε]

/-- **COROLLARY `hAssembly_reduced`.**  The partials→FDeriv `hAssembly` slot of
    `QIQTH.HeatResidualBound.hCConv_L1_of_partialsContinuity`, supplied by the theorem above.  It
    reduces the carried assembly to three satisfiable, non-vacuous inputs on an OPEN set `u`:
      • `hpart` — the linewise partials of the singular convolution on all of `u` (the family
        produced by `hConvDeriv_linewise`), with derivative functions `gcoef i`;
      • `hcont` — the NEW reduced carry: continuity of each coefficient function `gcoef i`
        (the derivative-integral `x ↦ ∫∫ dH · F`) at each point of `u` (a dominated-convergence
        fact, labelled);
      • `hDrep` — the representation `D x = ∑ i, gcoef i x • proj i` matching the Fréchet
        derivative to the coefficients.
    The resulting statement is exactly the `hAssembly` hypothesis of
    `hCConv_L1_of_partialsContinuity`.  NOT `a₁ = R/6`. -/
theorem hAssembly_reduced (H F : ℝ → Point n → Point n → ℝ) (t : ℝ)
    (D : Point n → (Point n →L[ℝ] ℝ))
    (u : Set (Point n)) (hu_open : IsOpen u)
    (gcoef : Fin n → Point n → ℝ)
    (hpart : ∀ x ∈ u, ∀ i : Fin n,
       HasDerivAt (fun w => heatConv H F t (Function.update x i w) 0) (gcoef i x) (x i))
    (hcont : ∀ x ∈ u, ∀ i : Fin n, ContinuousAt (gcoef i) x)
    (hDrep : ∀ x ∈ u,
       D x = ∑ i : Fin n, gcoef i x • (ContinuousLinearMap.proj i : Point n →L[ℝ] ℝ)) :
    ∀ x ∈ u,
      (∀ i : Fin n, HasDerivAt (fun w => heatConv H F t (Function.update x i w) 0)
        ((D x) (Pi.single i (1 : ℝ))) (x i)) →
      HasFDerivAt (fun p => heatConv H F t p 0) (D x) x := by
  intro x hx _hlin
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hu_open x hx
  have hfd := partials_continuous_hasFDerivAt (fun p => heatConv H F t p 0) x r hr gcoef
    (fun y hy i => hpart y (hball hy) i) (fun i => hcont x hx i)
  rw [hDrep x hx]
  exact hfd

end QIQTH.PartialsToFDeriv

section AxiomChecks
open QIQTH.PartialsToFDeriv
#print axioms partials_continuous_hasFDerivAt
#print axioms hAssembly_reduced
end AxiomChecks
