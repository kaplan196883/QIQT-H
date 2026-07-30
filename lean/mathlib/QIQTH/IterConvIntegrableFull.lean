/-
  IterConvIntegrableFull — M6 / analytic carry: the FULL per-step integrability family
  `IterConvIntegrableW E 2 0 C`, discharged from the one-step residual bound `hEbound` plus
  genuine measurability/vanishing regularity on the residual `E`, by a joint induction on `k`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  CONTEXT.  `ParametrixHEboundWiring.IterConvIntegrableW` bundles the FIVE integral facts the
  width-tolerant Levi/Duhamel domination step (`heatConv_le_of_abs_le_pos`) demands, at every
  `k ≥ 1`, `t > 0`, `x y`, with `A = E`, `B = iterE E k`, `A' = C·baseKernelW 2 0`,
  `B' = C^k·iterKernelW 2 0 k`:

    (1)  `IntervalIntegrable (fun s => ‖∫ z, E (t−s) x z · iterE E k s z y‖) 0 t`
    (2)  `IntervalIntegrable (fun s => ∫ z, |E (t−s) x z|·|iterE E k s z y|) 0 t`
    (3)  `∀ s, Integrable (fun z => |E (t−s) x z|·|iterE E k s z y|)`
    (4)  `∀ s, Integrable (fun z => C·baseKernelW 2 0 (t−s) x z · (C^k·iterKernelW 2 0 k s z y))`
    (5)  `IntervalIntegrable (fun s => ∫ z, C·baseKernelW 2 0 (t−s) x z · (C^k·iterKernelW 2 0 k s z y)) 0 t`

  The MODEL conjuncts (4)∧(5) are ALREADY PROVED unconditionally in
  `ModelIntegrableW.iterConvIntegrableW_model`.  This file discharges the three RESIDUAL-side
  conjuncts (1),(2),(3) — the interval/Lebesgue integrability of the ACTUAL iterated convolutions.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE JOINT INDUCTION.  The residual conjuncts require the iterated-residual domination
  `|iterE E k| ≤ C^k·iterKernelW 2 0 k` (`iterConvW_bound`), which itself consumes the FULL
  `IterConvIntegrableW`.  So domination and integrability cannot be obtained separately — they are
  proved TOGETHER:

    ▸ `Dall` — the domination `|iterE E k τ p q| ≤ C^k·iterKernelW 2 0 k τ p q` (all `τ > 0`), by
      `Nat.le_induction`: base `k=1` = `hEbound` (`iterE_one`, `iterKernelW_one`); step
      `k → k+1` via `heatConv_le_of_abs_le_pos` fed the level-`k` integrability `mkI k … (Dall k)`.
    ▸ `mkI` — GIVEN the level-`k` domination, produces the five conjuncts at level `k`:
        • (3) interior `0<s<t`: `Integrable.mono'` — the actual product is `≤` the model
          integrand (`hEbound`, the level-`k` domination) and is `AEStronglyMeasurable`; boundary
          `s ≤ 0` / `s ≥ t` kills the integrand via the residual's vanishing at nonpositive time.
        • (1),(2) : `Integrable.mono'` on `Ioc 0 t` — the actual `s`-integrand is `≤` the model
          `s`-integrand (integral monotonicity, resp. `norm_integral_le_integral_norm`) and is
          `AEStronglyMeasurable` (via `AEStronglyMeasurable.integral_prod_right'` from the carried
          joint measurability).  The single endpoint `s = t` is null.
        • (4),(5) : `iterConvIntegrableW_model` verbatim.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE CARRIED REGULARITY HYPOTHESES (all genuine, non-vacuous, satisfied by the CONCRETE residual
  `parametrixResidualN 0`, which is a continuous function built from the Gaussian `gaussDdim`):

    • `hEzero`      — `E` vanishes at nonpositive time (`∀ τ ≤ 0, E τ = 0`).  Needed ONLY for the
      literal `∀ s` of conjunct (3) at the boundary `s ∉ (0,t)`.  Genuine: the concrete residual is
      built from `gaussDdim τ`, which vanishes for `τ ≤ 0` when `n ≥ 1`.
    • `hE_zmeas`    — the space-slice `z ↦ E τ p z` is `AEStronglyMeasurable` (each time/point).
    • `hIterE_zmeas`— the space-slice `z ↦ iterE E k s z y` is `AEStronglyMeasurable` (each level).
    • `hConv_meas`  — the space-time integrand `(s,z) ↦ E (t−s) x z · iterE E k s z y` is jointly
      `AEStronglyMeasurable` on `(volume.restrict (Ioc 0 t)).prod volume`.
    All four hold for a jointly-continuous `E` and its (continuous) iterated convolutions; none is
    the conclusion (measurability ⊊ integrability), none is vacuous.

  ⚠ HONEST SCOPE.  This DISCHARGES `IterConvIntegrableW E 2 0 C` down to `hEbound` + the four
  regularity carries above.  It does NOT discharge `hEbound` itself (the global width-2 one-step
  bound — the C4c far-field/off-diagonal wall), and it is NOT `a₁ = R/6`.  The remaining brick is to
  discharge the four regularity carries for the concrete residual via joint continuity + the Fubini
  measurability of the (variable-upper-limit) convolution.  No `sorry`, no new axioms, no vacuous
  hypotheses; every carried hypothesis is genuinely used.
-/
import Mathlib
import QIQTH.ModelIntegrableW

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 800000

/-- **★ THE FULL WIDTH-2 PER-STEP INTEGRABILITY FAMILY, from the one-step bound + regularity.**
    Given the global width-2 one-step residual bound `hEbound`, the residual's vanishing at
    nonpositive time (`hEzero`), the space-slice measurabilities of `E` and every `iterE E k`
    (`hE_zmeas`, `hIterE_zmeas`), and the joint space-time measurability of the convolution
    integrand (`hConv_meas`), the FULL per-step integrability family `IterConvIntegrableW E 2 0 C`
    holds.  Proof by the joint domination/integrability induction described in the file header:
    `Dall` (the iterated-residual domination) and `mkI` (the five conjuncts from a level's
    domination) are proved by mutual `Nat.le_induction`, the model conjuncts supplied by
    `iterConvIntegrableW_model`.  This discharges the carried `IterConvIntegrableW` in
    `neumann_summable_alpha0_width2` to `hEbound` plus the four genuine regularity hypotheses. -/
theorem iterConvIntegrableW_of_bound_continuous
    (E : ℝ → Point n → Point n → ℝ) (C : ℝ)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hE_zmeas : ∀ (τ : ℝ) (p : Point n),
      AEStronglyMeasurable (fun z : Point n => E τ p z) volume)
    (hIterE_zmeas : ∀ (k : ℕ), 1 ≤ k → ∀ (s : ℝ) (y : Point n),
      AEStronglyMeasurable (fun z : Point n => iterE E k s z y) volume)
    (hConv_meas : ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
      AEStronglyMeasurable
        (Function.uncurry (fun (s : ℝ) (z : Point n) => E (t - s) x z * iterE E k s z y))
        ((volume.restrict (Set.Ioc 0 t)).prod volume)) :
    IterConvIntegrableW E (2 : ℝ) (0 : ℝ) C := by
  -- The iterated residual vanishes at nonpositive time (from `hEzero`).
  have iterE_nonpos : ∀ (k : ℕ), 1 ≤ k → ∀ (s : ℝ), s ≤ 0 → ∀ (z y : Point n),
      iterE E k s z y = 0 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro s hs z y; rw [iterE_one]; exact hEzero s hs z y
    | succ m hm ih =>
        intro s hs z y
        rw [iterE_succ E hm, heatConvK_apply]
        simp only [heatConv]
        refine (intervalIntegral.integral_congr (fun s' hs' => ?_)).trans
          intervalIntegral.integral_zero
        have hmem : s' ∈ Set.Icc s 0 := by rwa [Set.uIcc_of_ge hs] at hs'
        have hzero : (fun w => E (s - s') z w * iterE E m s' w y) = fun _ => (0 : ℝ) := by
          funext w; rw [ih s' hmem.2 w y, mul_zero]
        show (∫ w, E (s - s') z w * iterE E m s' w y) = 0
        rw [hzero, integral_zero]
  -- The five conjuncts at level `k`, GIVEN the level-`k` domination.
  have mkI : ∀ (k : ℕ), 1 ≤ k →
      (∀ τ, 0 < τ → ∀ p q, |iterE E k τ p q| ≤ C ^ k * iterKernelW (2:ℝ) (0:ℝ) k τ p q) →
      ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
        IntervalIntegrable (fun s => ‖∫ z, E (t - s) x z * iterE E k s z y‖) volume 0 t ∧
        IntervalIntegrable (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t ∧
        (∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|)) ∧
        (∀ s, Integrable
          (fun z => C * baseKernelW (2:ℝ) (0:ℝ) (t - s) x z
            * (C ^ k * iterKernelW (2:ℝ) (0:ℝ) k s z y))) ∧
        IntervalIntegrable
          (fun s => ∫ z, C * baseKernelW (2:ℝ) (0:ℝ) (t - s) x z
            * (C ^ k * iterKernelW (2:ℝ) (0:ℝ) k s z y)) volume 0 t := by
    intro k hk domk t ht x y
    obtain ⟨hmodZ, hmodS⟩ := iterConvIntegrableW_model (2:ℝ) C (by norm_num) k hk t ht x y
    -- Conjunct (3): per-`s` `z`-integrability of the actual product.
    have c3 : ∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|) := by
      intro s
      by_cases hs : 0 < s ∧ s < t
      · obtain ⟨hs0, hst⟩ := hs
        have hts : 0 < t - s := by linarith
        have hmeas : AEStronglyMeasurable (fun z => |E (t - s) x z| * |iterE E k s z y|) volume :=
          (continuous_abs.comp_aestronglyMeasurable (hE_zmeas (t - s) x)).mul
            (continuous_abs.comp_aestronglyMeasurable (hIterE_zmeas k hk s y))
        refine Integrable.mono' (hmodZ s) hmeas (ae_of_all _ (fun z => ?_))
        rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
        have hE := hEbound (t - s) x z hts
        have hIt := domk s hs0 z y
        calc |E (t - s) x z| * |iterE E k s z y|
            ≤ (C * baseKernelW (2:ℝ) (0:ℝ) (t - s) x z)
                * (C ^ k * iterKernelW (2:ℝ) (0:ℝ) k s z y) :=
              mul_le_mul hE hIt (abs_nonneg _) (le_trans (abs_nonneg _) hE)
          _ = C * baseKernelW (2:ℝ) (0:ℝ) (t - s) x z
                * (C ^ k * iterKernelW (2:ℝ) (0:ℝ) k s z y) := by ring
      · have hz : (fun z => |E (t - s) x z| * |iterE E k s z y|) = fun _ => (0 : ℝ) := by
          funext z
          rcases not_and_or.mp hs with h | h
          · push_neg at h
            rw [iterE_nonpos k hk s h z y, abs_zero, mul_zero]
          · push_neg at h
            rw [hEzero (t - s) (by linarith) x z, abs_zero, zero_mul]
        rw [hz]; exact integrable_zero _ _ _
    -- Joint / slice measurability of the actual `s`-integrands on `Ioc 0 t`.
    have hjoint := hConv_meas k hk t ht x y
    have hsig : AEStronglyMeasurable (fun s => ∫ z, E (t - s) x z * iterE E k s z y)
        (volume.restrict (Set.Ioc 0 t)) := by
      simpa only [Function.uncurry_apply_pair] using hjoint.integral_prod_right'
    have habs : AEStronglyMeasurable (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|)
        (volume.restrict (Set.Ioc 0 t)) := by
      have hju : AEStronglyMeasurable
          (Function.uncurry (fun (s : ℝ) (z : Point n) => |E (t - s) x z| * |iterE E k s z y|))
          ((volume.restrict (Set.Ioc 0 t)).prod volume) := by
        have heqf :
            (Function.uncurry (fun (s : ℝ) (z : Point n) => |E (t - s) x z| * |iterE E k s z y|))
              = fun p =>
                |Function.uncurry (fun (s : ℝ) (z : Point n) => E (t - s) x z * iterE E k s z y) p| := by
          funext p
          obtain ⟨s, z⟩ := p
          simp only [Function.uncurry_apply_pair]
          rw [abs_mul]
        rw [heqf]
        exact continuous_abs.comp_aestronglyMeasurable hjoint
      simpa only [Function.uncurry_apply_pair] using hju.integral_prod_right'
    -- The model `s`-integrand is integrable on `Ioc 0 t`.
    have hh : Integrable
        (fun s => ∫ z, C * baseKernelW (2:ℝ) (0:ℝ) (t - s) x z
          * (C ^ k * iterKernelW (2:ℝ) (0:ℝ) k s z y)) (volume.restrict (Set.Ioc 0 t)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hmodS
    -- The pointwise integrand domination on the interior `0 < s < t`.
    have hptdom : ∀ s, 0 < s → s < t → ∀ z,
        |E (t - s) x z| * |iterE E k s z y|
          ≤ C * baseKernelW (2:ℝ) (0:ℝ) (t - s) x z
              * (C ^ k * iterKernelW (2:ℝ) (0:ℝ) k s z y) := by
      intro s hs0 hst z
      have hts : 0 < t - s := by linarith
      have hE := hEbound (t - s) x z hts
      have hIt := domk s hs0 z y
      calc |E (t - s) x z| * |iterE E k s z y|
          ≤ (C * baseKernelW (2:ℝ) (0:ℝ) (t - s) x z)
              * (C ^ k * iterKernelW (2:ℝ) (0:ℝ) k s z y) :=
            mul_le_mul hE hIt (abs_nonneg _) (le_trans (abs_nonneg _) hE)
        _ = C * baseKernelW (2:ℝ) (0:ℝ) (t - s) x z
              * (C ^ k * iterKernelW (2:ℝ) (0:ℝ) k s z y) := by ring
    -- Conjunct (2): interval-integrability of `s ↦ ∫ z |E|·|iterE|`.
    have c2 : IntervalIntegrable (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
      refine Integrable.mono' hh habs ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
      filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)] with s hst
      intro hmem
      obtain ⟨hs0, hsle⟩ := hmem
      have hsne : s ≠ t := by simpa using hst
      have hst2 : s < t := lt_of_le_of_ne hsle hsne
      rw [Real.norm_of_nonneg
            (integral_nonneg (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _)))]
      exact integral_mono (c3 s) (hmodZ s) (fun z => hptdom s hs0 hst2 z)
    -- Conjunct (1): interval-integrability of `s ↦ ‖∫ z E·iterE‖`.
    have c1 : IntervalIntegrable
        (fun s => ‖∫ z, E (t - s) x z * iterE E k s z y‖) volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
      refine Integrable.mono' hh hsig.norm ?_
      refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
      filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)] with s hst
      intro hmem
      obtain ⟨hs0, hsle⟩ := hmem
      have hsne : s ≠ t := by simpa using hst
      have hst2 : s < t := lt_of_le_of_ne hsle hsne
      rw [Real.norm_of_nonneg (norm_nonneg _)]
      calc ‖∫ z, E (t - s) x z * iterE E k s z y‖
          ≤ ∫ z, ‖E (t - s) x z * iterE E k s z y‖ := norm_integral_le_integral_norm _
        _ = ∫ z, |E (t - s) x z| * |iterE E k s z y| := by
              refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
              simp only [Real.norm_eq_abs, abs_mul]
        _ ≤ ∫ z, C * baseKernelW (2:ℝ) (0:ℝ) (t - s) x z
                * (C ^ k * iterKernelW (2:ℝ) (0:ℝ) k s z y) :=
              integral_mono (c3 s) (hmodZ s) (fun z => hptdom s hs0 hst2 z)
    exact ⟨c1, c2, c3, hmodZ, hmodS⟩
  -- The iterated-residual domination, by induction (the step consumes `mkI`).
  have Dall : ∀ (k : ℕ), 1 ≤ k → ∀ τ, 0 < τ → ∀ p q,
      |iterE E k τ p q| ≤ C ^ k * iterKernelW (2:ℝ) (0:ℝ) k τ p q := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        intro τ hτ p q
        rw [iterE_one, pow_one, iterKernelW_one]
        exact hEbound τ p q hτ
    | succ m hm ih =>
        intro τ hτ p q
        obtain ⟨hI1, hI2, hIf, hIg, hIsg⟩ := mkI m hm ih τ hτ p q
        rw [iterE_succ E hm, iterKernelW_succ (2:ℝ) (0:ℝ) hm]
        simp only [heatConvK_apply]
        have hbound := heatConv_le_of_abs_le_pos E (iterE E m)
          (fun τ' p' q' => C * baseKernelW (2:ℝ) (0:ℝ) τ' p' q')
          (fun τ' p' q' => C ^ m * iterKernelW (2:ℝ) (0:ℝ) m τ' p' q')
          τ p q hτ
          (fun τ' p' q' hτ' => hEbound τ' p' q' hτ')
          (fun τ' p' q' hτ' => ih τ' hτ' p' q')
          hI1 hI2 hIf hIg hIsg
        calc |heatConv E (iterE E m) τ p q|
            ≤ heatConv (fun τ' p' q' => C * baseKernelW (2:ℝ) (0:ℝ) τ' p' q')
                (fun τ' p' q' => C ^ m * iterKernelW (2:ℝ) (0:ℝ) m τ' p' q') τ p q := hbound
          _ = C ^ (m + 1) * heatConv (baseKernelW (2:ℝ) (0:ℝ)) (iterKernelW (2:ℝ) (0:ℝ) m) τ p q := by
                rw [heatConv_smul_left C (baseKernelW (2:ℝ) (0:ℝ))
                      (fun τ' p' q' => C ^ m * iterKernelW (2:ℝ) (0:ℝ) m τ' p' q'),
                    heatConv_smul_right (C ^ m) (baseKernelW (2:ℝ) (0:ℝ))
                      (iterKernelW (2:ℝ) (0:ℝ) m), pow_succ]
                ring
  exact fun k hk t ht x y => mkI k hk (Dall k hk) t ht x y

end QIQTH.HeatResidualBound
