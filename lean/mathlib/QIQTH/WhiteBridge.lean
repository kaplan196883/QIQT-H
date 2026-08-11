/-
  WhiteBridge — J4-627: the BRIDGE FEED — threading the unconditional whitened `hpkgBound`
  (J4-626, `WhiteAnnulus.white_hpkgBound_discharged`) into the bridge consumer chain
  (`BridgeWidth.bridgeGeneric_tail_O_s_w` → `FrozenTransportBridge` → the corrHigher API).
  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`; proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL — what is DISCHARGED here vs CARRIED.

  ── DISCHARGED (this file):
     ▸ `whiteDefectKernel` — the τ-GATED (window `(0,1]`) heat-operator defect of the whitened
       gated witness, the `FrozenWire.frozenDefectKernel` gating pattern.  The two-sided τ-gate is
       WHAT DISSOLVES the affine obstruction (J4-261): the pkg bound's `C·(1+t')` coefficient is a
       fixed constant `2C` once capped at `t' = 1`, and above the cap the kernel is literally `0` —
       so a FULL-∀τ fixed-constant bound holds and the full `IterConvIntegrableW` producer applies.
     ▸ `white_hEuni` / `white_hEbound_negHalf` — the τ-capped width-`lam` uniform O(1) domination
       and the α = −1/2 shape (a fortiori: `1 ≤ τ^{−1/2}` on `(0,1]`), from the pkg bound alone.
     ▸ `iterConvIntegrableW_of_bound_baseMeas_alpha_w` — the WIDTH-κ, α-PARAMETRIC per-step
       integrability producer (the missing generalization: `FrozenWire`'s α-parametric producer was
       width-2-pinned; `WidthAdapters`' width-κ producer was α=0-pinned).  Pure mirror of the two.
     ▸ ★ `white_tail_O_s` — the whitened k ≥ 2 tail `O(s)·G_{lam·s}` at width `lam`, and
       ★ `white_tail_O_s_discharged` — the ∃-shaped feeder: for EVERY `κ ≤ 0`, compact
       `K ⊆ B̄(0,R)`, there ARE a fat gate + radii + width `lam ≥ 2` such that the tail bound holds
       MODULO exactly ONE labelled input (S1 measurability, below).
     ▸ ★ `white_transport_bridge` / `white_corrHigher` — the bridge Prop + the bounded-cRem O(t²)
       API at the whitened defect, under the SAME single S1 input PLUS the honest width condition
       `lam ≤ 8` (see the width verdict below).

  ── CARRIED (labelled inputs, NOT proved here):
     (M1/S1)  `tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ) (whiteGatedWitness κ hκ hKc S a b)`
        — the base joint (τ,p,q) strong measurability of the whitened heat-operator defect.  The
        as-built vanVleck witness precedent (S1TripleHEmeasGate / GatedRepSFix / JetsGcUnification)
        discharged the SAME slot for `vanVleckGatedWitness` through a multi-brick chart-jet /
        gate-carrier campaign (Route B, continuity-free); NO such chain is yet banked for the
        WHITENED witness (`whiteCutKernel`'s chart is the `.choose`-based `uniformInverseChart`
        composed with the q-dependent whitening `E_q`; its per-derivative-field measurability is a
        mirror of that campaign, not a one-brick corollary).  Honest carried input.
     (R2)  `lam ≤ 8` — the whitened width `lam = whiteLam = 2(n·C₀²+1)` has an OPAQUE compactness
        constant `C₀`; `lam ≤ 8 ↔ n·C₀² ≤ 3` (`WhiteGated.whiteLam_le_eight_iff`) is a genuine
        unproved condition.  The tail theorems `white_tail_O_s`/`white_tail_O_s_discharged` are
        width-PARAMETRIC (they land at `G_{lam·s}`, no `lam ≤ 8` needed); only the FROZEN-side
        bridge comparison (whose banked landing shape is `G_{8s}`) needs `lam ∈ [2,8]` — carried
        there explicitly (`hlam8`).
     + the prior piles: `K1TransportBudget`, fat-K carriers, capstone co-instantiation at the
       whitened witness (the capstone is pinned at `vanVleckGatedWitness`, NOT this witness).

  ⚠ `whiteDefectKernel` equals the heat-operator defect ONLY on the window `(0,1]` (by
  construction); every conclusion about it is honest about that gating (the τ-capped consumer
  chain never evaluates above the cap — the C-route verdict of `TruncatedHIntRethread`).

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous hypotheses; every
  conditional theorem's antecedent bundle is satisfiability-gated below.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WhiteAnnulus
import QIQTH.BridgeWidth
import QIQTH.HEmeasBorelAudit

open Finset Filter Topology MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.FrozenWire QIQTH.AlphaLevi QIQTH.CoInstSmoke QIQTH.BridgeDefect QIQTH.BridgeWidth
open QIQTH.WhiteGated QIQTH.WhiteAnnulus QIQTH.ExpMap QIQTH.CurvedA1CenterAmp

namespace QIQTH.WhiteBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

/-! ###############################################################################
    ### 1. Generic α/width plumbing: the α = −1/2 shape a fortiori from the O(1) shape.
    ############################################################################### -/

/-- **`hEbound_negHalf_of_hEuni` — the α = −1/2 one-step shape is a FORTIORI from the τ-capped
    uniform O(1) bound**: on `0 < τ ≤ 1` one has `1 ≤ τ^{−1/2}`, so
    `C_U·G_{wτ} ≤ C_U·τ^{−1/2}·G_{wτ} = C_U·baseKernelW w (−1/2)`.  (This is the point of the
    whitening: the whitened defect obeys the STRONGER O(1) bound, so the engine's α = −1/2 slot
    is free.)  Honest τ ≤ 1 usage; NOT `a₁ = R/6`. -/
theorem hEbound_negHalf_of_hEuni (E : ℝ → Point n → Point n → ℝ) (w C_U : ℝ)
    (hCU : 0 ≤ C_U)
    (hEuni : ∀ τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C_U * gaussDdim (w * τ) (p - q)) :
    ∀ τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ 1 →
      |E τ p q| ≤ C_U * baseKernelW w (-(1 / 2) : ℝ) τ p q := by
  intro τ p q hτ hτ1
  have hG : 0 ≤ gaussDdim (w * τ) (p - q) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
  have h1 : (1 : ℝ) ≤ τ ^ (-(1 / 2) : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by norm_num)
  calc |E τ p q| ≤ C_U * gaussDdim (w * τ) (p - q) := hEuni τ p q hτ hτ1
    _ = C_U * gaussDdim (w * τ) (p - q) * 1 := by ring
    _ ≤ C_U * gaussDdim (w * τ) (p - q) * τ ^ (-(1 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hCU hG)
    _ = C_U * baseKernelW w (-(1 / 2) : ℝ) τ p q := by
        simp only [baseKernelW]; ring

/-! ###############################################################################
    ### 2. The WIDTH-κ, α-PARAMETRIC model conjuncts (4)∧(5) — the `FrozenWire` α-parametric
    ###    model at general width `κ > 0` (that file was width-2-pinned; `ModelIntegrableW`'s
    ###    width-κ model was α = 0-pinned).  Pure mechanical mirror.
    ############################################################################### -/

/-- **Model conjunct (4) at general width `κ > 0` and `α > −1`** (the `z`-integrand is integrable
    for every `s`): the width-κ mirror of `FrozenWire.modelZ_integrableW_alpha`. -/
theorem modelZ_integrableW_alpha_w (κ α C : ℝ) (hκ : 0 < κ) (hα : -1 < α)
    (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (_ht : 0 < t) (x y : Point n) (s : ℝ) :
    Integrable
      (fun z => C * baseKernelW κ α (t - s) x z
        * (C ^ k * iterKernelW κ α k s z y)) volume := by
  by_cases hs : 0 < s ∧ s < t
  · obtain ⟨hs0, hst⟩ := hs
    have hform : (fun z => C * baseKernelW κ α (t - s) x z
          * (C ^ k * iterKernelW κ α k s z y))
        = fun z => (C * C ^ k
              * (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
              * (t - s) ^ α * s ^ ((k : ℝ) * (α + 1) - 1))
            * (gaussDdim (κ * (t - s)) (x - z) * gaussDdim (κ * s) (z - y)) := by
      funext z
      rw [iterKernelW_eq κ α hκ hα s hs0 z y hk]
      simp only [baseKernelW]
      ring
    rw [hform]
    exact (gaussDdim_mul_integrable (κ * (t - s)) (κ * s) x y).const_mul _
  · rcases Nat.eq_zero_or_pos n with hn0 | hn1
    · subst hn0
      exact Integrable.of_finite
    · have hzero : (fun z => C * baseKernelW κ α (t - s) x z
            * (C ^ k * iterKernelW κ α k s z y))
          = fun _ => (0 : ℝ) := by
        funext z
        rcases not_and_or.mp hs with h | h
        · push_neg at h
          rw [iterKernelW_of_nonpos_time κ α hκ hn1 k hk s h z y,
              mul_zero, mul_zero]
        · push_neg at h
          simp only [baseKernelW]
          rw [gaussDdim_eq_zero_of_nonpos hn1 (by nlinarith : κ * (t - s) ≤ 0) (x - z),
              mul_zero, mul_zero, zero_mul]
      rw [hzero]; exact integrable_zero _ _ _

/-- **Model conjunct (5) at general width `κ > 0` and `α > −1`** (the `s ↦ ∫ z (…)` map is
    interval-integrable on `[0,t]`): the width-κ mirror of
    `FrozenWire.modelS_intervalIntegrableW_alpha` (the Beta integrand via
    `FrozenWire.rpow_mul_rpow_intervalIntegrable`, reused verbatim). -/
theorem modelS_intervalIntegrableW_alpha_w (κ α C : ℝ) (hκ : 0 < κ) (hα : -1 < α)
    (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 < t) (x y : Point n) :
    IntervalIntegrable
      (fun s => ∫ z, C * baseKernelW κ α (t - s) x z
        * (C ^ k * iterKernelW κ α k s z y)) volume 0 t := by
  have he1 : (-1 : ℝ) < (k : ℝ) * (α + 1) - 1 := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hg_ii : IntervalIntegrable
      (fun s => (C * C ^ k * (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
                  * gaussDdim (κ * t) (x - y))
                * ((t - s) ^ α * s ^ ((k : ℝ) * (α + 1) - 1))) volume 0 t :=
    (rpow_mul_rpow_intervalIntegrable α ((k : ℝ) * (α + 1) - 1) t hα he1 ht).const_mul _
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  have hg : IntegrableOn
      (fun s => (C * C ^ k * (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
                  * gaussDdim (κ * t) (x - y))
                * ((t - s) ^ α * s ^ ((k : ℝ) * (α + 1) - 1))) (Set.Ioc 0 t) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]; exact hg_ii
  refine hg.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr (show volume ({t} : Set ℝ) = 0 by simp)] with s hst
  intro hmem
  obtain ⟨hs0, hsle⟩ := hmem
  have hsne : s ≠ t := by simpa using hst
  have hst2 : s < t := lt_of_le_of_ne hsle hsne
  have hts : 0 < t - s := by linarith
  have hform : (fun z => C * baseKernelW κ α (t - s) x z
        * (C ^ k * iterKernelW κ α k s z y))
      = fun z => (C * C ^ k
            * (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
            * ((t - s) ^ α * s ^ ((k : ℝ) * (α + 1) - 1)))
          * (gaussDdim (κ * (t - s)) (x - z) * gaussDdim (κ * s) (z - y)) := by
    funext z
    rw [iterKernelW_eq κ α hκ hα s hs0 z y hk]
    simp only [baseKernelW]
    ring
  show (C * C ^ k * (Real.Gamma (α + 1) ^ k / Real.Gamma ((k : ℝ) * (α + 1)))
          * gaussDdim (κ * t) (x - y))
        * ((t - s) ^ α * s ^ ((k : ℝ) * (α + 1) - 1))
      = ∫ z, C * baseKernelW κ α (t - s) x z * (C ^ k * iterKernelW κ α k s z y)
  rw [hform, integral_const_mul,
      QIQTH.GaussianConvolution.gaussDdim_conv (κ * (t - s)) (κ * s)
        (mul_pos hκ hts) (mul_pos hκ hs0) x y,
      show κ * (t - s) + κ * s = κ * t from by ring]
  ring

/-- The packaged model conjuncts (4)∧(5) at general width `κ > 0` and `α > −1` (the exact shape
    they occupy in `IterConvIntegrableW E κ α C`). -/
theorem iterConvIntegrableW_model_alpha_w (κ α C : ℝ) (hκ : 0 < κ) (hα : -1 < α) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
      (∀ s, Integrable
        (fun z => C * baseKernelW κ α (t - s) x z
          * (C ^ k * iterKernelW κ α k s z y))) ∧
      IntervalIntegrable
        (fun s => ∫ z, C * baseKernelW κ α (t - s) x z
          * (C ^ k * iterKernelW κ α k s z y)) volume 0 t :=
  fun k hk t ht x y =>
    ⟨fun s => modelZ_integrableW_alpha_w κ α C hκ hα k hk t ht x y s,
     modelS_intervalIntegrableW_alpha_w κ α C hκ hα k hk t ht x y⟩

/-! ###############################################################################
    ### 3. ★ THE WIDTH-κ, α-PARAMETRIC PER-STEP INTEGRABILITY PRODUCER — the mirror of
    ###    `FrozenWire.iterConvIntegrableW_of_bound_baseMeas_alpha` at general width.
    ############################################################################### -/

/-- **★ The width-κ α-parametric `hInt` producer**: from a FULL-∀τ width-`κ` order-`α` one-step
    bound at a FIXED constant, vanishing at nonpositive time, and the single base joint
    measurability, the full family `IterConvIntegrableW E κ α C` holds.  The exact mirror of
    `FrozenWire.iterConvIntegrableW_of_bound_baseMeas_alpha` (width 2 → κ), with the model
    conjuncts supplied by `iterConvIntegrableW_model_alpha_w`; the measurability carries by the
    width-free `iterE_zmeas` / `conv_meas`.  NOT `a₁ = R/6`. -/
theorem iterConvIntegrableW_of_bound_baseMeas_alpha_w
    (E : ℝ → Point n → Point n → ℝ) (κ α C : ℝ) (hκ : 0 < κ) (hα : -1 < α)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ α τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n => E w.1 w.2.1 w.2.2)) :
    IterConvIntegrableW E κ α C := by
  have hE_zmeas : ∀ (τ : ℝ) (p : Point n),
      AEStronglyMeasurable (fun z : Point n => E τ p z) volume := fun τ p =>
    (hEmeas.comp_measurable
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
  -- The five conjuncts at level `k`, GIVEN the level-`k` domination.
  have mkI : ∀ (k : ℕ), 1 ≤ k →
      (∀ τ, 0 < τ → ∀ p q, |iterE E k τ p q| ≤ C ^ k * iterKernelW κ α k τ p q) →
      ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
        IntervalIntegrable (fun s => ‖∫ z, E (t - s) x z * iterE E k s z y‖) volume 0 t ∧
        IntervalIntegrable (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t ∧
        (∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|)) ∧
        (∀ s, Integrable
          (fun z => C * baseKernelW κ α (t - s) x z
            * (C ^ k * iterKernelW κ α k s z y))) ∧
        IntervalIntegrable
          (fun s => ∫ z, C * baseKernelW κ α (t - s) x z
            * (C ^ k * iterKernelW κ α k s z y)) volume 0 t := by
    intro k hk domk t ht x y
    obtain ⟨hmodZ, hmodS⟩ := iterConvIntegrableW_model_alpha_w κ α C hκ hα k hk t ht x y
    -- Conjunct (3): per-`s` `z`-integrability of the actual product.
    have c3 : ∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|) := by
      intro s
      by_cases hs : 0 < s ∧ s < t
      · obtain ⟨hs0, hst⟩ := hs
        have hts : 0 < t - s := by linarith
        have hmeas : AEStronglyMeasurable
            (fun z => |E (t - s) x z| * |iterE E k s z y|) volume :=
          (continuous_abs.comp_aestronglyMeasurable (hE_zmeas (t - s) x)).mul
            (continuous_abs.comp_aestronglyMeasurable (hIterE_zmeas k hk s y))
        refine Integrable.mono' (hmodZ s) hmeas (ae_of_all _ (fun z => ?_))
        rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
        have hE := hEbound (t - s) x z hts
        have hIt := domk s hs0 z y
        calc |E (t - s) x z| * |iterE E k s z y|
            ≤ (C * baseKernelW κ α (t - s) x z)
                * (C ^ k * iterKernelW κ α k s z y) :=
              mul_le_mul hE hIt (abs_nonneg _) (le_trans (abs_nonneg _) hE)
          _ = C * baseKernelW κ α (t - s) x z
                * (C ^ k * iterKernelW κ α k s z y) := by ring
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
                |Function.uncurry
                  (fun (s : ℝ) (z : Point n) => E (t - s) x z * iterE E k s z y) p| := by
          funext p
          obtain ⟨s, z⟩ := p
          simp only [Function.uncurry_apply_pair]
          rw [abs_mul]
        rw [heqf]
        exact continuous_abs.comp_aestronglyMeasurable hjoint
      simpa only [Function.uncurry_apply_pair] using hju.integral_prod_right'
    -- The model `s`-integrand is integrable on `Ioc 0 t`.
    have hh : Integrable
        (fun s => ∫ z, C * baseKernelW κ α (t - s) x z
          * (C ^ k * iterKernelW κ α k s z y)) (volume.restrict (Set.Ioc 0 t)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mp hmodS
    -- The pointwise integrand domination on the interior `0 < s < t`.
    have hptdom : ∀ s, 0 < s → s < t → ∀ z,
        |E (t - s) x z| * |iterE E k s z y|
          ≤ C * baseKernelW κ α (t - s) x z
              * (C ^ k * iterKernelW κ α k s z y) := by
      intro s hs0 hst z
      have hts : 0 < t - s := by linarith
      have hE := hEbound (t - s) x z hts
      have hIt := domk s hs0 z y
      calc |E (t - s) x z| * |iterE E k s z y|
          ≤ (C * baseKernelW κ α (t - s) x z)
              * (C ^ k * iterKernelW κ α k s z y) :=
            mul_le_mul hE hIt (abs_nonneg _) (le_trans (abs_nonneg _) hE)
        _ = C * baseKernelW κ α (t - s) x z
              * (C ^ k * iterKernelW κ α k s z y) := by ring
    -- Conjunct (2): interval-integrability of `s ↦ ∫ z |E|·|iterE|`.
    have c2 : IntervalIntegrable
        (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t := by
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
        _ ≤ ∫ z, C * baseKernelW κ α (t - s) x z
                * (C ^ k * iterKernelW κ α k s z y) :=
              integral_mono (c3 s) (hmodZ s) (fun z => hptdom s hs0 hst2 z)
    exact ⟨c1, c2, c3, hmodZ, hmodS⟩
  -- The iterated-residual domination, by induction (the step consumes `mkI`).
  have Dall : ∀ (k : ℕ), 1 ≤ k → ∀ τ, 0 < τ → ∀ p q,
      |iterE E k τ p q| ≤ C ^ k * iterKernelW κ α k τ p q := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        intro τ hτ p q
        rw [iterE_one, pow_one, iterKernelW_one]
        exact hEbound τ p q hτ
    | succ m hm ih =>
        intro τ hτ p q
        obtain ⟨hI1, hI2, hIf, hIg, hIsg⟩ := mkI m hm ih τ hτ p q
        rw [iterE_succ E hm, iterKernelW_succ κ α hm]
        simp only [heatConvK_apply]
        have hbound := heatConv_le_of_abs_le_pos E (iterE E m)
          (fun τ' p' q' => C * baseKernelW κ α τ' p' q')
          (fun τ' p' q' => C ^ m * iterKernelW κ α m τ' p' q')
          τ p q hτ
          (fun τ' p' q' hτ' => hEbound τ' p' q' hτ')
          (fun τ' p' q' hτ' => ih τ' hτ' p' q')
          hI1 hI2 hIf hIg hIsg
        calc |heatConv E (iterE E m) τ p q|
            ≤ heatConv (fun τ' p' q' => C * baseKernelW κ α τ' p' q')
                (fun τ' p' q' => C ^ m * iterKernelW κ α m τ' p' q') τ p q := hbound
          _ = C ^ (m + 1)
                * heatConv (baseKernelW κ α) (iterKernelW κ α m) τ p q := by
              rw [heatConv_smul_left C (baseKernelW κ α)
                    (fun τ' p' q' => C ^ m * iterKernelW κ α m τ' p' q'),
                  heatConv_smul_right (C ^ m) (baseKernelW κ α)
                    (iterKernelW κ α m), pow_succ]
              ring
  exact fun k hk t ht x y => mkI k hk (Dall k hk) t ht x y

/-! ###############################################################################
    ### 4. THE τ-GATED WHITENED DEFECT KERNEL (the `FrozenWire.frozenDefectKernel` pattern).
    ############################################################################### -/

/-- **`whiteDefectKernel` — the τ-GATED heat-operator defect of the whitened gated witness**:
        `E_white τ p q := (heatOp g^κ gi^κ (whiteGatedWitness S a b)) τ p q` on `0 < τ ≤ 1`,
        and `0` outside the window.
    The two-sided gate (the `FrozenWire`/`timeCap` pattern) is what turns the pkg bound's
    AFFINE coefficient `C·(1+t')` into a FIXED full-∀τ constant `2C` (cap at `t' = 1`; zero above)
    — dissolving the J4-261 affine obstruction for the whitened kernel.  ⚠ HONEST: this object
    equals the actual defect ONLY on `(0,1]`; the τ-capped bridge chain never looks above. -/
noncomputable def whiteDefectKernel (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) :
    ℝ → Point n → Point n → ℝ :=
  fun τ p q => if 0 < τ ∧ τ ≤ 1 then
    heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b) τ p q
  else 0

/-- On the window `(0,1]`, `whiteDefectKernel` IS the heat-operator defect. -/
theorem whiteDefectKernel_eq (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (p q : Point n) :
    whiteDefectKernel κ hκ hKc S a b τ p q
      = heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q := by
  simp only [whiteDefectKernel, if_pos (And.intro hτ hτ1)]

/-- `whiteDefectKernel` vanishes at nonpositive time (the `hEzero` slot). -/
theorem whiteDefectKernel_zero_nonpos (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) :
    ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, whiteDefectKernel κ hκ hKc S a b τ p q = 0 := by
  intro τ hτ p q
  simp only [whiteDefectKernel]
  exact if_neg (fun h => absurd h.1 (not_lt.mpr hτ))

/-- `whiteDefectKernel` vanishes above the cap `τ > 1`. -/
theorem whiteDefectKernel_zero_gt_one (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    {τ : ℝ} (hτ : 1 < τ) (p q : Point n) :
    whiteDefectKernel κ hκ hKc S a b τ p q = 0 := by
  simp only [whiteDefectKernel]
  exact if_neg (fun h => absurd h.2 (not_le.mpr hτ))

/-- **The joint strong measurability of `whiteDefectKernel`, FROM the S1 slot** — a measurable
    `ite` over the window set `{0 < τ ≤ 1}`, given `tripleHEmeas` of the whitened defect (the
    single carried measurability input; see the header firewall). -/
theorem whiteDefectKernel_stronglyMeasurable (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    StronglyMeasurable (fun w : ℝ × Point n × Point n =>
      whiteDefectKernel κ hκ hKc S a b w.1 w.2.1 w.2.2) := by
  classical
  have hset : MeasurableSet {w : ℝ × Point n × Point n | 0 < w.1 ∧ w.1 ≤ 1} :=
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)
  have hE : Measurable (fun w : ℝ × Point n × Point n =>
      heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
        (whiteGatedWitness κ hκ hKc S a b) w.1 w.2.1 w.2.2) := hEmeas.measurable
  have hrw : (fun w : ℝ × Point n × Point n =>
        whiteDefectKernel κ hκ hKc S a b w.1 w.2.1 w.2.2)
      = fun w : ℝ × Point n × Point n =>
          if 0 < w.1 ∧ w.1 ≤ 1 then
            heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (whiteGatedWitness κ hκ hKc S a b) w.1 w.2.1 w.2.2
          else 0 := by
    funext w; simp only [whiteDefectKernel]
  rw [hrw]
  exact (Measurable.ite hset hE measurable_const).stronglyMeasurable

/-! ###############################################################################
    ### 5. The three engine slots at the whitened defect, from the pkg bound.
    ############################################################################### -/

/-- **`white_hEuni` — the τ-capped width-`lam` uniform O(1) domination at `whiteDefectKernel`**,
    from the capstone-`hpkgBound` shape (slice `t' = 1`, via `hEuni_of_hpkgBound_w`). -/
theorem white_hEuni (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q) :
    ∀ τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ 1 →
      |whiteDefectKernel κ hκ hKc S a b τ p q|
        ≤ (2 * C) * gaussDdim (lam * τ) (p - q) := by
  intro τ p q hτ hτ1
  rw [whiteDefectKernel_eq κ hκ hKc S a b hτ hτ1 p q]
  exact hEuni_of_hpkgBound_w
    (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (whiteGatedWitness κ hκ hKc S a b))
    C lam hpkg τ p q hτ hτ1

/-- **`white_hEbound_negHalf` — the α = −1/2 one-step shape at `whiteDefectKernel`, FULL ∀τ**:
    on `(0,1]` a fortiori from `white_hEuni` (`1 ≤ τ^{−1/2}`); above the cap the gated kernel is
    `0 ≤ RHS`.  This is the exact full-∀τ fixed-constant shape the width-κ producer consumes —
    the affine obstruction dissolved by the gate. -/
theorem white_hEbound_negHalf (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ) (hC : 0 ≤ C)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q) :
    ∀ τ : ℝ, ∀ p q : Point n, 0 < τ →
      |whiteDefectKernel κ hκ hKc S a b τ p q|
        ≤ (2 * C) * baseKernelW lam (-(1 / 2) : ℝ) τ p q := by
  intro τ p q hτ
  by_cases hτ1 : τ ≤ 1
  · exact hEbound_negHalf_of_hEuni (whiteDefectKernel κ hκ hKc S a b) lam (2 * C)
      (by linarith) (white_hEuni κ hκ hKc S a b C lam hpkg) τ p q hτ hτ1
  · rw [whiteDefectKernel_zero_gt_one κ hκ hKc S a b (not_le.mp hτ1) p q, abs_zero]
    have hG : 0 ≤ gaussDdim (lam * τ) (p - q) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
    have hpow : 0 ≤ τ ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hτ.le _
    simp only [baseKernelW]
    exact mul_nonneg (by linarith) (mul_nonneg hpow hG)

/-- **`white_hInt` — the per-step integrability family at `whiteDefectKernel`, width `lam`,
    α = −1/2** — from the pkg bound + the SINGLE carried S1 measurability input, through the
    width-κ α-parametric producer.  ⚠ CONDITIONAL on `hEmeas` (labelled; see the firewall). -/
theorem white_hInt (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam : 0 < lam)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    IterConvIntegrableW (whiteDefectKernel κ hκ hKc S a b) lam (-(1 / 2) : ℝ) (2 * C) :=
  iterConvIntegrableW_of_bound_baseMeas_alpha_w
    (whiteDefectKernel κ hκ hKc S a b) lam (-(1 / 2) : ℝ) (2 * C) hlam (by norm_num)
    (fun τ p q hτ => white_hEbound_negHalf κ hκ hKc S a b C lam hC hpkg τ p q hτ)
    (whiteDefectKernel_zero_nonpos κ hκ hKc S a b)
    (whiteDefectKernel_stronglyMeasurable κ hκ hKc S a b hEmeas)

/-! ###############################################################################
    ### 6. ★ THE WHITENED k ≥ 2 TAIL — the bridge engine fed at width `lam`.
    ############################################################################### -/

/-- **★ `white_tail_O_s` — the whitened k ≥ 2 tail is `O(s)·G_{lam·s}`** — the width-`lam`
    tail engine `bridgeGeneric_tail_O_s_w` instantiated at the τ-gated whitened defect, all
    three slots supplied from {the pkg bound, the S1 input}.  Width-PARAMETRIC (no `lam ≤ 8`
    needed here — the honest conclusion width is `lam`). -/
theorem white_tail_O_s (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    ∃ C_os : ℝ, 0 ≤ C_os ∧ ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |leviSeries (whiteDefectKernel κ hκ hKc S a b) s p 0
          + whiteDefectKernel κ hκ hKc S a b s p 0|
        ≤ C_os * (s * gaussDdim (lam * s) (p - 0)) := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le two_pos hlam2
  exact bridgeGeneric_tail_O_s_w (whiteDefectKernel κ hκ hKc S a b) lam (2 * C) (2 * C)
    hlam0 (by linarith) (by linarith)
    (fun τ p q hτ _hτ1 => white_hEbound_negHalf κ hκ hKc S a b C lam hC hpkg τ p q hτ)
    (white_hEuni κ hκ hKc S a b C lam hpkg)
    (white_hInt κ hκ hKc S a b C lam hC hlam0 hpkg hEmeas)

/-- **★★ `white_tail_O_s_discharged` — THE BRIDGE FEED**: for EVERY `κ ≤ 0` and compact
    `K ⊆ B̄(0,R)` there ARE a fat open gate `S`, radii `0 < a < b`, and a width `lam ≥ 2` such
    that, MODULO exactly ONE labelled input — the S1 joint measurability of the whitened defect —
    the whitened k ≥ 2 tail obeys `O(s)·G_{lam·s}` on `(0,1]`.  All Gaussian-domination and
    integrability slots of the bridge engine are UNCONDITIONALLY discharged from J4-626's
    `white_hpkgBound_discharged`; the pkg-bound itself is re-exported in the conjunction so the
    consumer sees the constants' provenance.  ⚠ HONEST WIDTH: `lam` is `whiteLam`-valued
    (opaque `C₀`); the conclusion is at `G_{lam·s}`, NOT at the frozen chain's `G_{8s}`.
    NOT `a₁ = R/6`. -/
theorem white_tail_O_s_discharged (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (R : ℝ) (hKb : Kset ⊆ Metric.closedBall (0 : Point n) R) :
    ∃ S : Point n → Set (Point n), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ (∀ q ∈ Kset, q ∈ S q ∧ IsOpen (S q))
      ∧ ∃ lam : ℝ, 2 ≤ lam ∧
        (QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
            (whiteGatedWitness κ hκ hKc S a b) →
          ∃ C_os : ℝ, 0 ≤ C_os ∧ ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
            |leviSeries (whiteDefectKernel κ hκ hKc S a b) s p 0
                + whiteDefectKernel κ hκ hKc S a b s p 0|
              ≤ C_os * (s * gaussDdim (lam * s) (p - 0))) := by
  obtain ⟨S, a, b, ha, hab, hgate, C, hC0, lam, hlam2, hpkg⟩ :=
    white_hpkgBound_discharged κ hκ hKc R hKb
  exact ⟨S, a, b, ha, hab, hgate, lam, hlam2,
    fun hEmeas => white_tail_O_s κ hκ hKc S a b C lam hC0 hlam2 hpkg hEmeas⟩

/-! ###############################################################################
    ### 7. ★ THE BRIDGE + corrHigher API — the width reconciliation made explicit.
    ############################################################################### -/

/-- **★ `white_transport_bridge` — the bridge Prop at the whitened defect** against the frozen
    defect `frozenDefectKernel K r`, via `frozenTransportBridge_of_dominations_w`.
    ⚠ WIDTH RECONCILIATION (honest): the FROZEN side of the bridge triangle lands at `G_{8s}`,
    so the single-step widening `G_{lam·s} ≤ 2ⁿ·G_{8s}` demands `lam ∈ [2,8]` — and
    `lam = whiteLam = 2(nC₀²+1) ≤ 8 ↔ n·C₀² ≤ 3` is UNPROVED (opaque `C₀`;
    `WhiteGated.whiteLam_le_eight_iff`).  `hlam8` is therefore a CARRIED, labelled width input
    alongside the S1 measurability.  NOT `a₁ = R/6`. -/
theorem white_transport_bridge (K r : ℝ) (hK : K ≤ 0) (hr : 0 ≤ r)
    (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam) (hlam8 : lam ≤ 8)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    FrozenTransportBridge (whiteDefectKernel κ hκ hKc S a b) (frozenDefectKernel K r) := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le two_pos hlam2
  exact frozenTransportBridge_of_dominations_w K r hK hr
    (whiteDefectKernel κ hκ hKc S a b) lam (2 * C) (2 * C) hlam2 hlam8
    (by linarith) (by linarith)
    (fun τ p q hτ _hτ1 => white_hEbound_negHalf κ hκ hKc S a b C lam hC hpkg τ p q hτ)
    (white_hEuni κ hκ hKc S a b C lam hpkg)
    (white_hInt κ hκ hKc S a b C lam hC hlam0 hpkg hEmeas)

/-- **★ `white_corrHigher` — the capstone-shaped bounded-cRem O(t²) API for the whitened k ≥ 2
    tail**, chained through the certified `smoke_bridge_verdict` transfer at a `FatFrozenPackage`.
    Same carried inputs as the bridge (`hEmeas` + `hlam8`).  NOT `a₁ = R/6`. -/
theorem white_corrHigher (P : FatFrozenPackage n)
    (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC : 0 ≤ C) (hlam2 : 2 ≤ lam) (hlam8 : lam ≤ 8)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    ∃ C_t : ℝ, 0 ≤ C_t ∧
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a' : ℝ) (ζ : Point n), 0 < a' →
          |H a' 0 ζ| ≤ C_H * gaussDdim (2 * a') ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        ∀ (pref t : ℝ), 0 < t → t ≤ 1 → pref ≠ 0 →
          (heatConv H (fun σ p q => leviSeries (whiteDefectKernel κ hκ hKc S a b) σ p q
                + whiteDefectKernel κ hκ hKc S a b σ p q) t 0 0
            = pref * (t ^ 2
                * (heatConv H (fun σ p q => leviSeries (whiteDefectKernel κ hκ hKc S a b) σ p q
                      + whiteDefectKernel κ hκ hKc S a b σ p q) t 0 0
                    / (pref * t ^ 2))))
          ∧ |heatConv H (fun σ p q => leviSeries (whiteDefectKernel κ hκ hKc S a b) σ p q
                + whiteDefectKernel κ hκ hKc S a b σ p q) t 0 0|
            ≤ (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) * t ^ 2
          ∧ |heatConv H (fun σ p q => leviSeries (whiteDefectKernel κ hκ hKc S a b) σ p q
                + whiteDefectKernel κ hκ hKc S a b σ p q) t 0 0 / (pref * t ^ 2)|
            ≤ (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) / |pref| :=
  smoke_bridge_verdict P (whiteDefectKernel κ hκ hKc S a b)
    (white_transport_bridge P.κ P.rS P.hκ.le P.hrS.le κ hκ hKc S a b C lam
      hC hlam2 hlam8 hpkg hEmeas)

/-! ###############################################################################
    ### 8. Non-vacuity / adversarial gates (cp466 discipline).
    ############################################################################### -/

/-- **Gate 1 — the feeder's unconditional legs are INHABITED at genuinely curved data**
    (`n = 2`, `κ = −1`, `K = closedBall 0 2`): the ∃-package of `white_tail_O_s_discharged`
    produces a FAT gate (`q ∈ S q`, open, at every `q ∈ K ≠ ∅`) with `0 < a < b` and `lam ≥ 2` —
    the antecedent chain up to the single S1 input is genuinely satisfiable, not `∅`-degenerate. -/
theorem white_bridge_feed_witness_gate :
    ∃ S : Point 2 → Set (Point 2), ∃ a b : ℝ, 0 < a ∧ a < b
      ∧ ((0 : Point 2) ∈ S 0 ∧ IsOpen (S 0))
      ∧ ∃ lam : ℝ, 2 ≤ lam := by
  obtain ⟨S, a, b, ha, hab, hgate, lam, hlam2, -⟩ :=
    white_tail_O_s_discharged (n := 2) (-1 : ℝ) (by norm_num)
      (isCompact_closedBall (0 : Point 2) 2) 2 (subset_refl _)
  exact ⟨S, a, b, ha, hab,
    hgate 0 (Metric.mem_closedBall_self (by norm_num)), lam, hlam2⟩

/-- **Gate 2 — the width-κ α-parametric producer's antecedent bundle is jointly satisfiable**
    (axiom-budget-blind-spot check): witness `E = 0, C = 0` inhabits {full-∀τ bound, `hEzero`,
    `hEmeas`} at any width `κ > 0`, `α > −1` — the producer is not vacuously conditioned.
    ⚠ HONEST: mere satisfiability; the genuinely nonzero consumer is the whitened defect, whose
    S1 measurability is the carried input. -/
theorem producer_antecedent_satisfiable_w (κ α : ℝ) :
    ∃ (E : ℝ → Point n → Point n → ℝ) (C : ℝ),
      (∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ α τ p q) ∧
      (∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0) ∧
      StronglyMeasurable (fun w : ℝ × Point n × Point n => E w.1 w.2.1 w.2.2) :=
  ⟨fun _ _ _ => 0, 0, fun τ p q _ => by simp, fun _ _ _ _ => rfl,
    stronglyMeasurable_const⟩

/-- **Gate 3 — NO-FALSE-CLAIM width honesty (re-export)**: the conclusion width `lam = whiteLam`
    reconciles with the frozen `G_{8s}` landing IFF `n·C₀² ≤ 3` — restated here so this file's
    own audit trail carries the exact unproved width condition its bridge theorems assume. -/
theorem white_bridge_width_condition (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) :
    (2 * ((n : ℝ) * (uniformFlowConst (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc) ^ 2 + 1) ≤ 8)
      ↔ ((n : ℝ) * (uniformFlowConst (curvedRNCMetric κ) (curvedRNCInv κ)
        (curvedRNC_hChr κ hκ) hKc) ^ 2 ≤ 3) :=
  whiteLam_le_eight_iff κ hκ hKc

end QIQTH.WhiteBridge
