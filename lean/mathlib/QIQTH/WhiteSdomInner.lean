/-
  WhiteSdomInner — J4-704 (S-dom): THE WHITENED INNER-ENGINE SPATIAL DOMINATOR.  Produces the
  `hbnd_int` / `hbound` (S-dom) slots of `InnerEngineRecursion.innerStep_cont_ae` at the whitened
  kernel `E := whiteDefectKernel κ hκ hKc S a b` — the uniform integrable spatial dominator of the
  convolution step.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── THE SLOT.  `InnerEngineRecursion.innerStep_cont_ae` consumes, at each rung `k ≥ 1`, an
     `p`-UNIFORM (over the positive-time compact `Icc t₁ t₂ ×ˢ closedBall 0 R`) integrable spatial
     dominator `bnd : ℝ → Point n → ℝ` with
       • `hbnd_int : ∀ᵐ u ∂restrict(Ioc 0 1), Integrable (bnd u) volume`;
       • `hbound   : ∀ᵐ u ∂restrict(Ioc 0 1), ∀ p ∈ box, ∀ᵐ w,
                       ‖E (p.1−p.1·u) p.2 w · iterE E k (p.1·u) w 0‖ ≤ bnd u w`.

  ── THE ROUTE (the cheapest honest one; the `SdomHnearDischarge.hSdom_concrete` template at the
     WHITENED kernel).  The whitened defect `E := whiteDefectKernel` is:
       (a) SUPPORTED in the fat compact base gate `Kset` — `whiteDefectKernel τ z w = 0` for
           `w ∉ Kset` (the off-gate vanishing `whiteGated_heatOp_zero_offGate` on the window, `0` by
           definition off the window) — the new `whiteDefectKernel_baseNotMem_eq_zero` below;
       (b) width-`lam` peaked-Gaussian bounded by the banked fixed-constant `2C` one-step bound
           `WhiteLeviMajorWire.white_hEbound_zero` (from the capstone pkg bound `hpkg`), and its
           iterates by `iterConvW_bound` fed `white_hEbound_zero` + `white_hInt_zero`.
     Hence, for fixed `u ∈ (0,1)` (the a.e.-`u` leg drops the null endpoint `u = 1`), the product
     vanishes off the COMPACT `Kset` (⟹ finite measure ⟹ `𝟙_Kset` integrable), and on `Kset` the
     peaked diagonal majorants (`gaussDdim_le_diagonal`, `gaussDdim_zero_antitone`) collapse the
     `(s,z,w)`-dependence to the explicit constant
       `M(u) = (2C·G_{lam·t₁·(1−u)}(0))·((2C)^k·Γ(k)⁻¹·(t₂·u)^{k−1}·G_{lam·t₁·u}(0))`.
     So `bnd u w = M(u)·𝟙_Kset(w)` — an `(s,z)`-free, integrable, `p`-uniform spatial dominator.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It is a
  regularity / domination brick (the whitened replay of `SdomHnearDischarge.hSdom_concrete`).  No
  `sorry`, no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no hypothesis equal to
  (or trivially yielding) the conclusion, no existing file edited, nothing committed, nothing wired
  into `QIQTH.lean` / `AxiomAudit`.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).
    * `whiteDefectKernel_baseNotMem_eq_zero` — the whitened `K`-gate zero: `w ∉ Kset ⟹
      whiteDefectKernel … τ z w = 0` for EVERY `τ` (window leg via `whiteGated_heatOp_zero_offGate`,
      off-window leg by definition).
    * `white_hSdom` — ★★★ the whitened S-dom discharge: the `∃ bnd, hbnd_int ∧ hbound` package in
      EXACTLY the shape `InnerEngineRecursion.innerStep_cont_ae` consumes, at the whitened defect,
      from `{hpkg, hEmeas}` + `0 ≤ C`, `0 < lam`, `Kset` compact.

  ── HONEST RESIDUAL (precisely named; NOT the conclusion, NOT a₁ = R/6).
    * `hpkg` — the capstone width-`lam` pkg bound of the whitened gated witness heatOp;
    * `hEmeas` — the whitened-defect S1 base measurability `tripleHEmeas`.
    Both are the standard labelled whitened carries (every whitened integrability owes `hEmeas`).

  ⚠  STILL NOT `a₁ = R/6`.  `R/6` is a labelled carrier, untouched.
-/
import Mathlib
import QIQTH.SdomHnearDischarge
import QIQTH.WhiteLeviMajorWire
import QIQTH.WhiteGated

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.LeviSeries QIQTH.HeatResidualBound QIQTH.TrueHeatKernel
open QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant QIQTH.ResidueBound
open QIQTH.RDomEnvelope QIQTH.RadialDistance
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.WhiteGated QIQTH.WhiteBridge QIQTH.WhiteLeviMajorWire
open scoped Topology

namespace QIQTH.WhiteSdomInner

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## The whitened `K`-gate zero: the defect vanishes off the compact base gate.
    ############################################################################### -/

/-- **`whiteDefectKernel_baseNotMem_eq_zero`.**  Where the base point `w` is outside the compact gate
    `Kset`, the whitened defect kernel vanishes for EVERY `τ`: on the window `(0,1]` it is the gated
    `heatOp`, which vanishes by `whiteGated_heatOp_zero_offGate` (`Or.inl`); off the window it is `0`
    by definition.  The whitened analogue of `heatOpWitness_baseNotMem_eq_zero`. -/
theorem whiteDefectKernel_baseNotMem_eq_zero (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b : ℝ) (τ : ℝ) (z w : Point n)
    (hwK : w ∉ Kset) :
    whiteDefectKernel κ hκ hKc S a b τ z w = 0 := by
  by_cases hw : 0 < τ ∧ τ ≤ 1
  · rw [whiteDefectKernel_eq κ hκ hKc S a b hw.1 hw.2 z w]
    exact whiteGated_heatOp_zero_offGate κ hκ hKc S a b τ z w (Or.inl hwK)
  · simp only [whiteDefectKernel, if_neg hw]

/-! ###############################################################################
    ## ★★★ The whitened S-dom discharge — the `p`-uniform integrable spatial dominator.
    ############################################################################### -/

/-- **★★★ `white_hSdom` — THE WHITENED S-DOM DISCHARGE.**  For the whitened defect kernel
    `E := whiteDefectKernel κ hκ hKc S a b`, produces the EXACT `hbnd_int` / `hbound` (S-dom) slots
    consumed by `InnerEngineRecursion.innerStep_cont_ae`:

      `∀ k, 1 ≤ k → ∀ t₁ t₂ R, 0<t₁ → t₁≤t₂ → 0<R →
        ∃ bnd : ℝ → Point n → ℝ,
          (∀ᵐ u ∂restrict(Ioc 0 1), Integrable (bnd u)) ∧
          (∀ᵐ u ∂restrict(Ioc 0 1), ∀ p ∈ Icc t₁ t₂ ×ˢ closedBall 0 R, ∀ᵐ w,
            ‖E (p.1−p.1·u) p.2 w · iterE E k (p.1·u) w 0‖ ≤ bnd u w)`,

    from `{hpkg (the capstone width-`lam` pkg bound), hEmeas (S1 measurability)}` + `0 ≤ C`,
    `0 < lam`, `Kset` compact.  The dominator `bnd u w = M(u)·𝟙_Kset(w)` uses the whitened `K`-gate
    zero (`whiteDefectKernel_baseNotMem_eq_zero`) to localize to the finite-measure compact `Kset`,
    and on `Kset` the peaked Gaussian majorants (banked `white_hEbound_zero` / `white_hInt_zero` /
    `iterConvW_bound`) to reach the explicit `(s,z,w)`-free constant `M(u)`.  The whitened replay of
    `SdomHnearDischarge.hSdom_concrete`.  ⚠ CONDITIONAL on `{hpkg, hEmeas}`.  NOT `a₁ = R/6`. -/
theorem white_hSdom (κ : ℝ) (hκ : κ ≤ 0) {Kset : Set (Point n)}
    (hKc : IsCompact Kset) (S : Point n → Set (Point n)) (a b C lam : ℝ)
    (hC0 : 0 ≤ C) (hlam : 0 < lam)
    (hpkg : ∀ t' τ : ℝ, ∀ p q : Point n, 0 < τ → τ ≤ t' →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (whiteGatedWitness κ hκ hKc S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW lam 0 τ p q)
    (hEmeas : QIQTH.HEmeasBorelAudit.tripleHEmeas (curvedRNCMetric κ) (curvedRNCInv κ)
      (whiteGatedWitness κ hκ hKc S a b)) :
    ∀ (k : ℕ), 1 ≤ k → ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ∃ bnd : ℝ → Point n → ℝ,
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), Integrable (bnd u) volume) ∧
        (∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)),
          ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
            ∀ᵐ w ∂volume,
              ‖whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w
                * iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0‖
                ≤ bnd u w) := by
  intro k hk t₁ t₂ R ht₁ ht₁₂ hR
  -- the banked whitened one-step + iterated bounds (fixed constant `2C`, width `lam`).
  have hEb : ∀ τ p q, 0 < τ →
      |whiteDefectKernel κ hκ hKc S a b τ p q| ≤ (2 * C) * baseKernelW lam 0 τ p q :=
    fun τ p q hτ => white_hEbound_zero κ hκ hKc S a b C lam hC0 hpkg τ p q hτ
  have hInt : IterConvIntegrableW (whiteDefectKernel κ hκ hKc S a b) lam 0 (2 * C) :=
    white_hInt_zero κ hκ hKc S a b C lam hC0 hlam hpkg hEmeas
  have hiter := iterConvW_bound (whiteDefectKernel κ hκ hKc S a b) lam 0 (2 * C) hEb hInt
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  -- measure facts for the compact base gate `Kset`.
  have hKmeas : MeasurableSet Kset := hKc.isClosed.measurableSet
  have hKfin : volume Kset < ⊤ := hKc.measure_lt_top
  have hΓ : 0 < Real.Gamma (k : ℝ) :=
    Real.Gamma_pos_of_pos (by exact_mod_cast (show 0 < k by omega))
  have he : 0 ≤ (k : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hk)
  have ht₂ : 0 < t₂ := lt_of_lt_of_le ht₁ ht₁₂
  refine ⟨fun u w =>
      ((2 * C) * gaussDdim (lam * (t₁ * (1 - u))) (0 : Point n))
        * ((2 * C) ^ k * (1 / Real.Gamma (k : ℝ) * (t₂ * u) ^ ((k : ℝ) - 1)
            * gaussDdim (lam * (t₁ * u)) (0 : Point n)))
        * Set.indicator Kset (fun _ => (1 : ℝ)) w, ?_, ?_⟩
  · -- (integrability) `bnd u` = constant · 𝟙_Kset, integrable since `Kset` has finite measure.
    refine ae_of_all _ (fun u => ?_)
    have hind : Integrable (Set.indicator Kset (fun _ => (1 : ℝ))) volume :=
      (integrable_indicator_iff hKmeas).mpr (integrableOn_const hKfin.ne)
    exact hind.const_mul _
  · -- (the pointwise bound) drop the null endpoint `u = 1`, then split `w ∈ Kset` / `w ∉ Kset`.
    have hlt1 : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0:ℝ) 1)), u ≠ (1:ℝ) := by
      refine ae_restrict_of_ae ?_
      rw [ae_iff]; simp only [ne_eq, not_not]
      rw [show {a : ℝ | a = 1} = ({1} : Set ℝ) from by ext x; simp]
      exact measure_singleton 1
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hlt1] with u hu hune
    have hu0 : 0 < u := hu.1
    have hu1 : u < 1 := lt_of_le_of_ne hu.2 hune
    have h1u : (0:ℝ) < 1 - u := by linarith
    intro p hp
    obtain ⟨hps, _hpz⟩ := hp
    have hs : p.1 ∈ Set.Icc t₁ t₂ := hps
    have hspos : 0 < p.1 := lt_of_lt_of_le ht₁ hs.1
    have hs1 : 0 < p.1 - p.1 * u := by nlinarith [mul_pos hspos h1u]
    have hs2 : 0 < p.1 * u := mul_pos hspos hu0
    refine ae_of_all _ (fun w => ?_)
    by_cases hwK : w ∈ Kset
    · -- NEAR: `w ∈ Kset`; the peaked Gaussian majorants give the constant `M u`.
      have hind1 : Set.indicator Kset (fun _ => (1:ℝ)) w = 1 := by
        simp [Set.indicator_of_mem hwK]
      rw [hind1, mul_one]
      -- factor majorants
      have hb1 : |whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w|
          ≤ (2 * C) * baseKernelW lam 0 (p.1 - p.1 * u) p.2 w :=
        hEb (p.1 - p.1 * u) p.2 w hs1
      have hb2 : |iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0|
          ≤ (2 * C) ^ k * iterKernelW lam 0 k (p.1 * u) w 0 :=
        hiter k hk (p.1 * u) hs2 w 0
      -- first factor ≤ `2C · G_{lam·t₁·(1−u)}(0)`
      have hpos1 : 0 < lam * (t₁ * (1 - u)) := mul_pos hlam (mul_pos ht₁ h1u)
      have hle1 : lam * (t₁ * (1 - u)) ≤ lam * (p.1 - p.1 * u) := by
        have hinner : t₁ * (1 - u) ≤ p.1 - p.1 * u := by
          nlinarith [mul_le_mul_of_nonneg_right hs.1 h1u.le]
        exact mul_le_mul_of_nonneg_left hinner hlam.le
      have hgd1 : gaussDdim (lam * (p.1 - p.1 * u)) (0 : Point n)
          ≤ gaussDdim (lam * (t₁ * (1 - u))) (0 : Point n) :=
        gaussDdim_zero_antitone hpos1 hle1
      have hA : (2 * C) * baseKernelW lam 0 (p.1 - p.1 * u) p.2 w
          ≤ (2 * C) * gaussDdim (lam * (t₁ * (1 - u))) (0 : Point n) := by
        rw [baseKernelW_zero_apply]
        exact mul_le_mul_of_nonneg_left
          (le_trans (gaussDdim_le_diagonal (mul_pos hlam hs1) (p.2 - w)) hgd1) hC20
      -- second factor ≤ `(2C)^k · Γ(k)⁻¹ · (t₂·u)^{k−1} · G_{lam·t₁·u}(0)`
      have hpos2 : 0 < lam * (t₁ * u) := mul_pos hlam (mul_pos ht₁ hu0)
      have hle2 : lam * (t₁ * u) ≤ lam * (p.1 * u) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs.1 hu0.le) hlam.le
      have hgd2 : gaussDdim (lam * (p.1 * u)) (0 : Point n)
          ≤ gaussDdim (lam * (t₁ * u)) (0 : Point n) :=
        gaussDdim_zero_antitone hpos2 hle2
      have hrp : (p.1 * u) ^ ((k : ℝ) - 1) ≤ (t₂ * u) ^ ((k : ℝ) - 1) :=
        Real.rpow_le_rpow hs2.le (mul_le_mul_of_nonneg_right hs.2 hu0.le) he
      have hiterle : iterKernelW lam 0 k (p.1 * u) w 0
          ≤ 1 / Real.Gamma (k : ℝ) * (t₂ * u) ^ ((k : ℝ) - 1)
              * gaussDdim (lam * (t₁ * u)) (0 : Point n) := by
        rw [iterKernelW_zero_apply lam hlam hk hs2 w]
        refine mul_le_mul (mul_le_mul_of_nonneg_left hrp (one_div_nonneg.mpr hΓ.le))
          (le_trans (gaussDdim_le_diagonal (mul_pos hlam hs2) (w - 0)) hgd2)
          (gaussDdim_nonneg _ _)
          (mul_nonneg (one_div_nonneg.mpr hΓ.le) (Real.rpow_nonneg (mul_nonneg ht₂.le hu0.le) _))
      have hB : (2 * C) ^ k * iterKernelW lam 0 k (p.1 * u) w 0
          ≤ (2 * C) ^ k * (1 / Real.Gamma (k : ℝ) * (t₂ * u) ^ ((k : ℝ) - 1)
              * gaussDdim (lam * (t₁ * u)) (0 : Point n)) :=
        mul_le_mul_of_nonneg_left hiterle (pow_nonneg hC20 k)
      -- combine
      rw [Real.norm_eq_abs, abs_mul]
      calc |whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w|
              * |iterE (whiteDefectKernel κ hκ hKc S a b) k (p.1 * u) w 0|
          ≤ ((2 * C) * baseKernelW lam 0 (p.1 - p.1 * u) p.2 w)
              * ((2 * C) ^ k * iterKernelW lam 0 k (p.1 * u) w 0) :=
            mul_le_mul hb1 hb2 (abs_nonneg _) (le_trans (abs_nonneg _) hb1)
        _ ≤ _ :=
            mul_le_mul hA hB (le_trans (abs_nonneg _) hb2)
              (mul_nonneg hC20 (gaussDdim_nonneg _ _))
    · -- K-GATE ZERO: `w ∉ Kset` ⟹ `E (…,w) = 0`, so the product and the dominator both vanish.
      have hEz : whiteDefectKernel κ hκ hKc S a b (p.1 - p.1 * u) p.2 w = 0 :=
        whiteDefectKernel_baseNotMem_eq_zero κ hκ hKc S a b _ p.2 w hwK
      simp [hEz, Set.indicator_of_notMem hwK]

#check @whiteDefectKernel_baseNotMem_eq_zero
#check @white_hSdom

end QIQTH.WhiteSdomInner

/-! ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WhiteSdomInner
#print axioms whiteDefectKernel_baseNotMem_eq_zero
#print axioms white_hSdom
end AxiomChecks
