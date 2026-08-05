/-
  TruncatedHIntRethread — J4-262: the SMALL-TIME truncation rethread of the wide `hInt`
  (`IterConvIntegrableW`) slot.  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`;
  proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  This file DISSOLVES the affine obstruction that J4-261
  (`WideHIntDischarge`) pinned as blocking the internalization of the wide capstone's `hInt` slot,
  by restricting the integrability family to a SMALL-TIME window `(0, T₀]`.  It carries no
  coefficient / geometry content of its own; it is pure integrability plumbing on top of banked
  machinery.  It does NOT close `a₁ = R/6`.

  ── THE AFFINE OBSTRUCTION (J4-261, recalled).  The wide `hInt` producer
     `WidthAdapters.iterConvIntegrableW_of_bound_baseMeas_wide` needs an ALL-τ one-step bound at a
     FIXED constant `C`:  `∀ τ p q, 0 < τ → |E τ p q| ≤ C·baseKernelW κ 0 τ p q`.  The geometric
     residual provider `ResidualAssemblyRecon.hEboundW_wide_from_geometry` supplies only the
     `τ ≤ t` bound, whose valid constant `C·(1+t)` is AFFINE in the cutoff.  Extending to all τ
     (cutoff `= τ`) forces the coefficient `C·(1+τ)`, which admits NO fixed-constant Gaussian
     majorant (a linear `(1+τ)` prefactor survives every Gaussian width change).  Hence the geometry
     bound does NOT feed the all-τ producer, and `hInt` is not internalizable from geometry alone.

  ── THE SMALL-TIME FIX HYPOTHESIS (this file, VERIFIED).  `a₁ = R/6` is a `t → 0⁺` DIAGONAL
     asymptotic.  The Levi/Duhamel conclusion chain that consumes `hInt` does so at a SINGLE outer
     time `t`, and — crucially — the ONLY consumption of `hInt` anywhere in the capstone lineage is
        `hInt m hm t ht x y`   (`RestrictedEboundW.iterConvW_bound_le`, the induction step),
     at the OUTER time `t` (never at any larger time).  See the CONSUMPTION-SITE VERDICT below.
     Therefore, on a truncated window `t ≤ T₀`, the affine coefficient is bounded:
        `C·(1+τ) ≤ C·(1+T₀)`  for `0 < τ ≤ T₀`,
     a FIXED constant — dissolving the obstruction.  This file banks the truncated integrability
     family `IterConvIntegrableWOn`, its producer from the affine bound, and the truncated Levi
     summability engine that demonstrates the truncated family is SUFFICIENT for the exact thing the
     capstone consumes `hInt` for (Neumann convergence at every `t ≤ T₀`).

  ── CONSUMPTION-SITE VERDICT:  **C-ROUTE (small-time consumption CONFIRMED).**
     `IterConvIntegrableW E κ α C` quantifies `∀ t > 0`.  BUT every downstream consumer touches it
     only at the outer conclusion time:
       • `WideA1Assembly.wide_trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty` uses `hInt`
         ONLY via `leviSeries_summableW_le (heatOp …) κ 0 C t … hEboundW_le hInt t ht le_rfl 0 0`
         (its single width-specific line) — at the outer time `t`.
       • `RestrictedEboundW.leviSeries_summableW_le` forwards `hInt` to `iterConvW_bound_le`, whose
         induction step consumes it as `hInt m hm t ht x y` — again at the outer `t` (the file's own
         docstring: "`hInt` … only ever used at the outer time `t ≤ T`").
     No consumer evaluates `hInt` at any time `> t`.  So a family restricted to `(0, T₀]` (with the
     capstone applied at `t ≤ T₀`) SUFFICES.  The affine obstruction is a `τ`-RANGE artifact; on the
     truncated range it evaporates.

  ── WHAT IS DISCHARGED HERE vs CARRIED.
     • DISCHARGED:  the affine → fixed-constant dissolution on `(0, T₀]` (`eboundW_affine_to_fixed_
       trunc`); the truncated producer (affine `τ ≤ T₀` bound + `hEzero` + S1 measurability ⟹
       truncated family `iterConvIntegrableWOn_of_affine_trunc`); the truncated Levi summability
       engine (`leviSeries_summableW_le_trunc`); and the END-TO-END composition
       `levi_converges_from_affine_trunc` (affine `τ ≤ T₀` bound + `hEzero` + S1 ⟹ Neumann
       convergence at every `t ≤ T₀`) — the precise property the capstone consumes `hInt` for.
     • CARRIED (honest residual):  the truncated-window RETHREAD of the banked ~130-binder wide
       capstone is NOT materialized here (kernel-freeze firewall: never restate the capstone from
       scratch).  The banked `ResidualAssemblyRecon.wide_a1_R6_of_residue_inf_hEboundW_discharged`
       demands the FULL `IterConvIntegrableW`; swapping its consumed engine
       `leviSeries_summableW_le → leviSeries_summableW_le_trunc` (a purely mechanical in-place edit,
       and the ONLY hInt-touching line) rethreads it to consume `IterConvIntegrableWOn` instead.
       That single edit is left to the orchestrator; this file proves the truncated family is a
       drop-in for it (both the producer and the summability sufficiency).

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses.  Every carried hypothesis is satisfiable, non-vacuous, and NEVER equal to the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WidthAdapters
import QIQTH.RestrictedEboundW

open MeasureTheory
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound QIQTH.WidthAdapters
open scoped BigOperators Topology

namespace QIQTH.TruncatedHIntRethread

variable {n : ℕ}

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 800000

/-! ###############################################################################
    ### 0. THE TRUNCATED INTEGRABILITY FAMILY `IterConvIntegrableWOn` (window `(0, T₀]`).
    ############################################################################### -/

/-- **★ J4-262 (0) — the SMALL-TIME truncated per-step integrability family.**  Verbatim
    `ParametrixHEboundWiring.IterConvIntegrableW`, but with the outer-time quantifier RESTRICTED to
    the window `0 < t ≤ T₀`.  The C-route verdict (see the file header) shows the entire capstone
    lineage consumes the integrability family ONLY at the outer conclusion time; on a truncated
    window this suffices while dissolving the affine-constant obstruction.  NOT `a₁ = R/6`. -/
def IterConvIntegrableWOn (E : ℝ → Point n → Point n → ℝ) (κ α C T₀ : ℝ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → t ≤ T₀ → ∀ (x y : Point n),
    IntervalIntegrable (fun s => ‖∫ z, E (t - s) x z * iterE E k s z y‖) volume 0 t ∧
    IntervalIntegrable (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t ∧
    (∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|)) ∧
    (∀ s, Integrable
      (fun z => C * baseKernelW κ α (t - s) x z * (C ^ k * iterKernelW κ α k s z y))) ∧
    IntervalIntegrable
      (fun s => ∫ z, C * baseKernelW κ α (t - s) x z * (C ^ k * iterKernelW κ α k s z y)) volume 0 t

/-! ###############################################################################
    ### 1. THE AFFINE → FIXED-CONSTANT DISSOLUTION ON `(0, T₀]` (the conceptual core).
    ############################################################################### -/

/-- **★★ J4-262 (1) — `eboundW_affine_to_fixed_trunc`.**  THE dissolution of the affine obstruction.
    On the window `(0, T₀]` the affine one-step bound with coefficient `C·(1+τ)` becomes a bound at
    the FIXED constant `C·(1+T₀)`, because `C·(1+τ) ≤ C·(1+T₀)` for `0 < τ ≤ T₀` (and
    `baseKernelW κ 0 τ p q > 0`).  This is exactly the step J4-261 showed is IMPOSSIBLE at all τ (the
    linear prefactor `(1+τ)` diverges) but TRIVIAL once truncated.  NOT `a₁ = R/6`. -/
theorem eboundW_affine_to_fixed_trunc (E : ℝ → Point n → Point n → ℝ) (κ C T₀ : ℝ)
    (hκ : 0 < κ) (hC : 0 ≤ C)
    (hAff : ∀ τ p q, 0 < τ → τ ≤ T₀ →
        |E τ p q| ≤ C * (1 + τ) * baseKernelW κ (0 : ℝ) τ p q) :
    ∀ τ p q, 0 < τ → τ ≤ T₀ →
      |E τ p q| ≤ (C * (1 + T₀)) * baseKernelW κ (0 : ℝ) τ p q := by
  intro τ p q hτ hτT
  refine le_trans (hAff τ p q hτ hτT) ?_
  have hbk : 0 ≤ baseKernelW κ (0 : ℝ) τ p q := by
    rw [baseKernelW_zero_apply]
    exact (gaussDdim_pos (κ * τ) (mul_pos hκ hτ) (p - q)).le
  refine mul_le_mul_of_nonneg_right ?_ hbk
  have : (1 : ℝ) + τ ≤ 1 + T₀ := by linarith
  exact mul_le_mul_of_nonneg_left this hC

/-! ###############################################################################
    ### 2. THE TRUNCATED PRODUCER — from a `(0, T₀]`-restricted one-step bound.
    ############################################################################### -/

/-- **★★★ J4-262 (2) — `iterConvIntegrableWOn_of_bound_baseMeas_trunc`.**  The small-time analogue of
    `WidthAdapters.iterConvIntegrableW_of_bound_baseMeas_wide`: from the `(0, T₀]`-RESTRICTED one-step
    width-`κ` fixed-`C` bound, the nonpositive-time vanishing, and the S1 joint strong measurability,
    the TRUNCATED family `IterConvIntegrableWOn E κ 0 C T₀` holds.  The proof mirrors the wide
    producer verbatim, threading the extra `τ ≤ T₀` (sound because at outer time `t ≤ T₀` all inner
    convolution times `t−s`, `s` lie in `(0, t) ⊆ (0, T₀]`).  This is where the affine coefficient,
    already collapsed to a FIXED constant by (1), yields the genuine integrability family.  NOT
    `a₁ = R/6`. -/
theorem iterConvIntegrableWOn_of_bound_baseMeas_trunc
    (E : ℝ → Point n → Point n → ℝ) (κ C T₀ : ℝ) (hκ : 0 < κ)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ T₀ → |E τ p q| ≤ C * baseKernelW κ (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)) :
    IterConvIntegrableWOn E κ (0 : ℝ) C T₀ := by
  -- The three measurability carriers, from the single S1 base measurability (wide-producer route).
  have hE_zmeas : ∀ (τ : ℝ) (p : Point n),
      AEStronglyMeasurable (fun z : Point n => E τ p z) volume := by
    intro τ p
    exact (hEmeas.comp_measurable
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have hIterE_zmeas := iterE_zmeas E hEmeas
  have hConv_meas := conv_meas E hEmeas
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
  -- The five conjuncts at level `k`, GIVEN the `(0,T₀]`-restricted level-`k` domination.
  have mkI : ∀ (k : ℕ), 1 ≤ k →
      (∀ τ, 0 < τ → τ ≤ T₀ → ∀ p q,
        |iterE E k τ p q| ≤ C ^ k * iterKernelW κ (0:ℝ) k τ p q) →
      ∀ (t : ℝ), 0 < t → t ≤ T₀ → ∀ (x y : Point n),
        IntervalIntegrable (fun s => ‖∫ z, E (t - s) x z * iterE E k s z y‖) volume 0 t ∧
        IntervalIntegrable (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t ∧
        (∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|)) ∧
        (∀ s, Integrable
          (fun z => C * baseKernelW κ (0:ℝ) (t - s) x z
            * (C ^ k * iterKernelW κ (0:ℝ) k s z y))) ∧
        IntervalIntegrable
          (fun s => ∫ z, C * baseKernelW κ (0:ℝ) (t - s) x z
            * (C ^ k * iterKernelW κ (0:ℝ) k s z y)) volume 0 t := by
    intro k hk domk t ht htT x y
    obtain ⟨hmodZ, hmodS⟩ := iterConvIntegrableW_model κ C hκ k hk t ht x y
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
        have hE := hEbound (t - s) x z hts (by linarith)
        have hIt := domk s hs0 (by linarith) z y
        calc |E (t - s) x z| * |iterE E k s z y|
            ≤ (C * baseKernelW κ (0:ℝ) (t - s) x z)
                * (C ^ k * iterKernelW κ (0:ℝ) k s z y) :=
              mul_le_mul hE hIt (abs_nonneg _) (le_trans (abs_nonneg _) hE)
          _ = C * baseKernelW κ (0:ℝ) (t - s) x z
                * (C ^ k * iterKernelW κ (0:ℝ) k s z y) := by ring
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
        (fun s => ∫ z, C * baseKernelW κ (0:ℝ) (t - s) x z
          * (C ^ k * iterKernelW κ (0:ℝ) k s z y)) (volume.restrict (Set.Ioc 0 t)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hmodS
    -- The pointwise integrand domination on the interior `0 < s < t`.
    have hptdom : ∀ s, 0 < s → s < t → ∀ z,
        |E (t - s) x z| * |iterE E k s z y|
          ≤ C * baseKernelW κ (0:ℝ) (t - s) x z
              * (C ^ k * iterKernelW κ (0:ℝ) k s z y) := by
      intro s hs0 hst z
      have hts : 0 < t - s := by linarith
      have hE := hEbound (t - s) x z hts (by linarith)
      have hIt := domk s hs0 (by linarith) z y
      calc |E (t - s) x z| * |iterE E k s z y|
          ≤ (C * baseKernelW κ (0:ℝ) (t - s) x z)
              * (C ^ k * iterKernelW κ (0:ℝ) k s z y) :=
            mul_le_mul hE hIt (abs_nonneg _) (le_trans (abs_nonneg _) hE)
        _ = C * baseKernelW κ (0:ℝ) (t - s) x z
              * (C ^ k * iterKernelW κ (0:ℝ) k s z y) := by ring
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
        _ ≤ ∫ z, C * baseKernelW κ (0:ℝ) (t - s) x z
                * (C ^ k * iterKernelW κ (0:ℝ) k s z y) :=
              integral_mono (c3 s) (hmodZ s) (fun z => hptdom s hs0 hst2 z)
    exact ⟨c1, c2, c3, hmodZ, hmodS⟩
  -- The `(0,T₀]`-restricted iterated-residual domination, by induction (the step consumes `mkI`).
  have Dall : ∀ (k : ℕ), 1 ≤ k → ∀ τ, 0 < τ → τ ≤ T₀ → ∀ p q,
      |iterE E k τ p q| ≤ C ^ k * iterKernelW κ (0:ℝ) k τ p q := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        intro τ hτ hτT p q
        rw [iterE_one, pow_one, iterKernelW_one]
        exact hEbound τ p q hτ hτT
    | succ m hm ih =>
        intro τ hτ hτT p q
        obtain ⟨hI1, hI2, hIf, hIg, hIsg⟩ := mkI m hm ih τ hτ hτT p q
        rw [iterE_succ E hm, iterKernelW_succ κ (0:ℝ) hm]
        simp only [heatConvK_apply]
        have hbound := heatConv_le_of_abs_le_pos_le E (iterE E m)
          (fun τ' p' q' => C * baseKernelW κ (0:ℝ) τ' p' q')
          (fun τ' p' q' => C ^ m * iterKernelW κ (0:ℝ) m τ' p' q')
          τ p q hτ
          (fun τ' p' q' hτ' hτ'τ => hEbound τ' p' q' hτ' (le_trans hτ'τ hτT))
          (fun τ' p' q' hτ' hτ'τ => ih τ' hτ' (le_trans hτ'τ hτT) p' q')
          hI1 hI2 hIf hIg hIsg
        calc |heatConv E (iterE E m) τ p q|
            ≤ heatConv (fun τ' p' q' => C * baseKernelW κ (0:ℝ) τ' p' q')
                (fun τ' p' q' => C ^ m * iterKernelW κ (0:ℝ) m τ' p' q') τ p q := hbound
          _ = C ^ (m + 1) * heatConv (baseKernelW κ (0:ℝ)) (iterKernelW κ (0:ℝ) m) τ p q := by
                rw [heatConv_smul_left C (baseKernelW κ (0:ℝ))
                      (fun τ' p' q' => C ^ m * iterKernelW κ (0:ℝ) m τ' p' q'),
                    heatConv_smul_right (C ^ m) (baseKernelW κ (0:ℝ))
                      (iterKernelW κ (0:ℝ) m), pow_succ]
                ring
  exact fun k hk t ht htT x y => mkI k hk (Dall k hk) t ht htT x y

/-- **★★★ J4-262 (2') — `iterConvIntegrableWOn_of_affine_trunc` (THE MINIMUM BANKABLE).**  The
    genuine derivation the mission asks for: from the AFFINE `τ ≤ T₀` one-step bound (coefficient
    `C·(1+τ)`), the nonpositive-time vanishing, and the S1 joint strong measurability, the TRUNCATED
    integrability family holds AT THE FIXED CONSTANT `C·(1+T₀)`.  Composition of the affine→fixed
    dissolution (1) with the truncated producer (2).  This is precisely "affine `τ ≤ t` bound ⟹ the
    truncated integrability family with fixed constant", the obstruction J4-261 pinned, now dissolved
    on the small-time window.  NOT `a₁ = R/6`. -/
theorem iterConvIntegrableWOn_of_affine_trunc
    (E : ℝ → Point n → Point n → ℝ) (κ C T₀ : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hAff : ∀ τ p q, 0 < τ → τ ≤ T₀ →
        |E τ p q| ≤ C * (1 + τ) * baseKernelW κ (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)) :
    IterConvIntegrableWOn E κ (0 : ℝ) (C * (1 + T₀)) T₀ :=
  iterConvIntegrableWOn_of_bound_baseMeas_trunc E κ (C * (1 + T₀)) T₀ hκ
    (eboundW_affine_to_fixed_trunc E κ C T₀ hκ hC hAff) hEzero hEmeas

/-! ###############################################################################
    ### 3. THE TRUNCATED LEVI ENGINE — the truncated family SUFFICES for consumption.
    ############################################################################### -/

/-- **★★ J4-262 (3a) — `iterConvW_bound_le_trunc`.**  The `(0,T]`-restricted iterated residual bound
    (mirror of `RestrictedEboundW.iterConvW_bound_le`), consuming the TRUNCATED family
    `IterConvIntegrableWOn E κ α C T` instead of the full `IterConvIntegrableW`.  The proof is
    byte-for-byte the banked one except the single consumption `hInt m hm t ht x y` becomes
    `hInt m hm t ht htT x y` (the truncated family's extra `t ≤ T` argument) — the DIRECT witness of
    the C-route verdict that `hInt` is only ever touched at the outer time.  NOT `a₁ = R/6`. -/
theorem iterConvW_bound_le_trunc (E : ℝ → Point n → Point n → ℝ) (κ α C T : ℝ)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ C * baseKernelW κ α τ p q)
    (hInt : IterConvIntegrableWOn E κ α C T) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → t ≤ T → ∀ (x y : Point n),
      |iterE E k t x y| ≤ C ^ k * iterKernelW κ α k t x y := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      intro t ht htT x y
      rw [iterE_one, pow_one, iterKernelW_one]
      exact hEbound t x y ht htT
  | succ m hm ih =>
      intro t ht htT x y
      obtain ⟨hI1, hI2, hIf, hIg, hIsg⟩ := hInt m hm t ht htT x y
      rw [iterE_succ E hm, iterKernelW_succ κ α hm]
      simp only [heatConvK_apply]
      have hbound := heatConv_le_of_abs_le_pos_le E (iterE E m)
        (fun τ p q => C * baseKernelW κ α τ p q) (fun τ p q => C ^ m * iterKernelW κ α m τ p q)
        t x y ht
        (fun τ p q hτ hτt => hEbound τ p q hτ (le_trans hτt htT))
        (fun τ p q hτ hτt => ih τ hτ (le_trans hτt htT) p q)
        hI1 hI2 hIf hIg hIsg
      calc |heatConv E (iterE E m) t x y|
          ≤ heatConv (fun τ p q => C * baseKernelW κ α τ p q)
              (fun τ p q => C ^ m * iterKernelW κ α m τ p q) t x y := hbound
        _ = C ^ (m + 1) * heatConv (baseKernelW κ α) (iterKernelW κ α m) t x y := by
              rw [heatConv_smul_left C (baseKernelW κ α)
                    (fun τ p q => C ^ m * iterKernelW κ α m τ p q),
                  heatConv_smul_right (C ^ m) (baseKernelW κ α) (iterKernelW κ α m), pow_succ]
              ring

/-- **★★★ J4-262 (3b) — `leviSeries_summableW_le_trunc`.**  The `(0,T]`-restricted width-tolerant
    Neumann convergence (mirror of `RestrictedEboundW.leviSeries_summableW_le`), from the TRUNCATED
    family.  This is the exact property `WideA1Assembly.wide_trueKernel_diagonal_a1_eq_R6_residual_
    restricted_C2_infty` consumes `hInt` for (its single width-specific line
    `leviSeries_summableW_le … hInt t ht le_rfl 0 0`); it therefore CERTIFIES that the truncated
    family is a drop-in for the capstone's `hInt`, provided the capstone is applied at `t ≤ T`.  The
    only mechanical rethread left to the orchestrator is the in-place swap
    `leviSeries_summableW_le → leviSeries_summableW_le_trunc` in the banked capstone.  NOT
    `a₁ = R/6`. -/
theorem leviSeries_summableW_le_trunc (E : ℝ → Point n → Point n → ℝ) (κ α C T : ℝ)
    (hκ : 0 < κ) (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hEbound : ∀ τ p q, 0 < τ → τ ≤ T → |E τ p q| ≤ C * baseKernelW κ α τ p q)
    (hInt : IterConvIntegrableWOn E κ α C T) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) (x y : Point n) :
    Summable (fun k : ℕ => iterE E (k + 1) t x y) := by
  refine Summable.of_norm_bounded (scaledIterKernelW_summable κ α t C hκ hα ht hC x y) (fun k => ?_)
  rw [Real.norm_eq_abs]
  exact iterConvW_bound_le_trunc E κ α C T hEbound hInt (k + 1) (by omega) t ht htT x y

/-! ###############################################################################
    ### 4. THE END-TO-END DEMONSTRATION — affine geometry bound ⟹ Neumann convergence.
    ############################################################################### -/

/-- **★★★★ J4-262 (4) — `levi_converges_from_affine_trunc`.**  The full small-time chain: from the
    AFFINE `τ ≤ T₀` one-step bound (coefficient `C·(1+τ)`, the exact shape the geometry residual
    provider `ResidualAssemblyRecon.hEboundW_wide_from_geometry` delivers), the nonpositive-time
    vanishing, and the S1 joint strong measurability, the residual Levi/Neumann series
    `∑ₖ iterE E (k+1) t x y` CONVERGES at every `0 < t ≤ T₀`.  Composes the affine→fixed dissolution
    (1), the truncated producer (2), and the truncated Levi engine (3).  This is the precise property
    the wide capstone consumes `hInt` for, now derived from the AFFINE geometry bound alone (no all-τ
    fixed-constant bound needed) — the J4-261 obstruction dissolved end-to-end on the small-time
    window.  ⚠ STILL NOT `a₁ = R/6`: it certifies the integrability/summability substrate on the
    truncated window; the leading-coefficient identity and the geometry inputs are elsewhere. -/
theorem levi_converges_from_affine_trunc
    (E : ℝ → Point n → Point n → ℝ) (κ C T₀ : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hAff : ∀ τ p q, 0 < τ → τ ≤ T₀ →
        |E τ p q| ≤ C * (1 + τ) * baseKernelW κ (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2))
    (t : ℝ) (ht : 0 < t) (htT : t ≤ T₀) (x y : Point n) :
    Summable (fun k : ℕ => iterE E (k + 1) t x y) := by
  have hbound : ∀ τ p q, 0 < τ → τ ≤ T₀ →
      |E τ p q| ≤ (C * (1 + T₀)) * baseKernelW κ (0 : ℝ) τ p q :=
    eboundW_affine_to_fixed_trunc E κ C T₀ hκ hC hAff
  have hInt : IterConvIntegrableWOn E κ (0 : ℝ) (C * (1 + T₀)) T₀ :=
    iterConvIntegrableWOn_of_bound_baseMeas_trunc E κ (C * (1 + T₀)) T₀ hκ hbound hEzero hEmeas
  exact leviSeries_summableW_le_trunc E κ (0 : ℝ) (C * (1 + T₀)) T₀ hκ le_rfl
    (mul_nonneg hC (by linarith)) hbound hInt t ht htT x y

end QIQTH.TruncatedHIntRethread

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.TruncatedHIntRethread
#print axioms eboundW_affine_to_fixed_trunc
#print axioms iterConvIntegrableWOn_of_bound_baseMeas_trunc
#print axioms iterConvIntegrableWOn_of_affine_trunc
#print axioms iterConvW_bound_le_trunc
#print axioms leviSeries_summableW_le_trunc
#print axioms levi_converges_from_affine_trunc
end AxiomChecks
