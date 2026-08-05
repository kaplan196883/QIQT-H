/-
  # `QIQTH.WidthAdapters` — the thin width adapters between the WIDE bank and the width-free capstone.

  Post-wide-map items [3]+[4]:  connect the width-`κ` bank (`FixedGateDichotomy.*`, the base-field
  `p = 0` slice) to the width-free capstone slots of
  `WideA1Assembly.wide_a1_R6_of_residue_inf_v5`, whose two residual slots are

      hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t → |heatOp g gi H τ p q| ≤ C · baseKernelW κ 0 τ p q
      hInt        : IterConvIntegrableW (heatOp g gi H) κ 0 C.

  This file delivers, at GENERAL width `κ` (`0 < κ`):

  (a) THE GAUSSIAN-FACTOR BRIDGE.  `baseKernelW κ 0 τ p q = gaussDdim (κ·τ) (p−q)` is already
      `HeatResidualBound.baseKernelW_zero_apply`.  Here we add the DIAGONAL (`p = 0`) form the wide
      bank actually needs — `baseKernelW κ 0 τ 0 z = gaussDdim (κ·τ) z` — via Gaussian evenness
      (`gaussDdim_neg`, `0 − z = −z`, the heat kernel is even).

  (b) THE WIDE `hInt` PRODUCERS.  The width-2 producers
      `iterConvIntegrableW_of_bound_{continuous,baseMeas}` are WIDTH-2-HARDCODED but width-PARAMETRIC
      in structure: the only width-specific step is the model-integrability call
      `iterConvIntegrableW_model 2 C (by norm_num)`, which is itself parametric in `κ` (takes
      `hκ : 0 < κ`).  We re-run both proofs verbatim at free `κ`, yielding
      `iterConvIntegrableW_of_bound_continuous_wide` / `iterConvIntegrableW_of_bound_baseMeas_wide :
      IterConvIntegrableW E κ 0 C`.  These fill the capstone's `hInt` slot at any `κ`, given the
      one-step wide bound + `hEzero` + a single base measurability (the width-free regularity
      carriers `iterE_zmeas` / `conv_meas` are reused untouched).

  (c) THE SLOT GLUE — HONEST VERDICT.  What composes TODAY is the diagonal factor bridge:
      `eboundW_le_diag_of_gaussDdim` turns ANY `gaussDdim (κ·τ)`-shaped diagonal bound into the
      `baseKernelW κ 0 τ 0 z` slot shape.  Composed with the LIVE wide bank
      `FixedGateDichotomy.zeroth_global_of_package` it gives
      `witness_zeroth_baseKernelW_diag` — the gated WITNESS in exact slot shape at `p = 0`.

      ⚠ HONEST FIREWALL.  Two named gaps remain before `hEboundW_le` is discharged:
        • [1] THE RESIDUAL ASSEMBLY.  The wide bank bounds the WITNESS `H_G` and its second
          `x`-derivative `D²H_G`, NOT the residual `heatOp g gi H = ∂_τH − Δ_g H`.  Item [1] must
          assemble `∂_τ H_G` (a `τ⁻¹·gaussDdim` bound) and `Δ_g H_G = gⁱʲ ∂ᵢ∂ⱼ H_G − Γ·∂H_G` (the
          `second_global`/metric/Christoffel contraction) into a residual bound of shape
          `|heatOp g gi H τ 0 z| ≤ C · gaussDdim (κ·τ) z`.  ONLY THEN does `eboundW_le_diag_of_gaussDdim`
          hand the capstone the `p = 0` slice of `hEboundW_le`.
        • [2] THE UNIFORMIZATION.  The bank is at the base field-centre `p = 0`; the slot is `∀ p q`.
          Item [2] is the `(p,q)`-translation / covariance of the gated-witness residual.

      Neither is claimed here.  This file is the factor bridge + width transport; the residual and
      uniformization are the next bricks.  No `sorry`, no new axioms, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.IterConvIntegrableFull
import QIQTH.IterEMeasurable
import QIQTH.FixedGateDichotomy

open MeasureTheory
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.LeviSeries QIQTH.HeatDuhamel
open QIQTH.GaussianWidthTolerant QIQTH.HeatResidualBound QIQTH.HeatKernelA1
open QIQTH.FixedGateDichotomy QIQTH.WideWitnessAmplitude

namespace QIQTH.WidthAdapters

variable {n : ℕ}

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 800000

/-! ### (a) The Gaussian-factor bridge (diagonal `p = 0`). -/

/-- **The 1-D heat kernel is even.** `heatKernel1D t (−x) = heatKernel1D t x` (`(−x)² = x²`). -/
theorem heatKernel1D_neg (t x : ℝ) :
    heatKernel1D t (-x) = heatKernel1D t x := by
  simp only [heatKernel1D, neg_sq]

/-- **`gaussDdim` is even.** `gaussDdim t (−z) = gaussDdim t z` (product of even 1-D factors,
    `(−z) k = −(z k)`). -/
theorem gaussDdim_neg (t : ℝ) (z : Point n) :
    gaussDdim t (-z) = gaussDdim t z := by
  simp only [gaussDdim]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Pi.neg_apply, heatKernel1D_neg]

/-- **THE DIAGONAL FACTOR BRIDGE (a).**  At the base field-centre `p = 0`, the width-`κ` model
    kernel IS the plain width-`κ` Gaussian in `z`:
        `baseKernelW κ 0 τ 0 z = gaussDdim (κ·τ) z`.
    Route: `baseKernelW_zero_apply` (`= gaussDdim (κτ) (0 − z)`), `0 − z = −z`, `gaussDdim_neg`. -/
theorem baseKernelW_zero_diag (κ τ : ℝ) (z : Point n) :
    baseKernelW κ (0 : ℝ) τ (0 : Point n) z = gaussDdim (κ * τ) z := by
  rw [baseKernelW_zero_apply, zero_sub, gaussDdim_neg]

/-! ### (b) The wide `hInt` producers (width-parametric transport of the width-2 producers). -/

/-- **★ THE FULL WIDTH-`κ` PER-STEP INTEGRABILITY FAMILY, from the one-step bound + regularity.**
    The exact width-parametric mirror of `HeatResidualBound.iterConvIntegrableW_of_bound_continuous`
    (which is hardcoded at `κ = 2`): given the width-`κ` one-step residual bound `hEbound`, the
    vanishing at nonpositive time `hEzero`, the space-slice measurabilities of `E` and every
    `iterE E k` (`hE_zmeas`, `hIterE_zmeas`), and the joint space-time measurability of the
    convolution integrand (`hConv_meas`), the full family `IterConvIntegrableW E κ 0 C` holds.  The
    proof is byte-for-byte the width-2 proof with `2 ↦ κ`; the ONLY width-specific line is the model
    call `iterConvIntegrableW_model κ C hκ` (parametric in `κ`, needs `0 < κ`). -/
theorem iterConvIntegrableW_of_bound_continuous_wide
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hκ : 0 < κ)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hE_zmeas : ∀ (τ : ℝ) (p : Point n),
      AEStronglyMeasurable (fun z : Point n => E τ p z) volume)
    (hIterE_zmeas : ∀ (k : ℕ), 1 ≤ k → ∀ (s : ℝ) (y : Point n),
      AEStronglyMeasurable (fun z : Point n => iterE E k s z y) volume)
    (hConv_meas : ∀ (k : ℕ), 1 ≤ k → ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
      AEStronglyMeasurable
        (Function.uncurry (fun (s : ℝ) (z : Point n) => E (t - s) x z * iterE E k s z y))
        ((volume.restrict (Set.Ioc 0 t)).prod volume)) :
    IterConvIntegrableW E κ (0 : ℝ) C := by
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
      (∀ τ, 0 < τ → ∀ p q, |iterE E k τ p q| ≤ C ^ k * iterKernelW κ (0:ℝ) k τ p q) →
      ∀ (t : ℝ), 0 < t → ∀ (x y : Point n),
        IntervalIntegrable (fun s => ‖∫ z, E (t - s) x z * iterE E k s z y‖) volume 0 t ∧
        IntervalIntegrable (fun s => ∫ z, |E (t - s) x z| * |iterE E k s z y|) volume 0 t ∧
        (∀ s, Integrable (fun z => |E (t - s) x z| * |iterE E k s z y|)) ∧
        (∀ s, Integrable
          (fun z => C * baseKernelW κ (0:ℝ) (t - s) x z
            * (C ^ k * iterKernelW κ (0:ℝ) k s z y))) ∧
        IntervalIntegrable
          (fun s => ∫ z, C * baseKernelW κ (0:ℝ) (t - s) x z
            * (C ^ k * iterKernelW κ (0:ℝ) k s z y)) volume 0 t := by
    intro k hk domk t ht x y
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
        have hE := hEbound (t - s) x z hts
        have hIt := domk s hs0 z y
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
      have hE := hEbound (t - s) x z hts
      have hIt := domk s hs0 z y
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
  -- The iterated-residual domination, by induction (the step consumes `mkI`).
  have Dall : ∀ (k : ℕ), 1 ≤ k → ∀ τ, 0 < τ → ∀ p q,
      |iterE E k τ p q| ≤ C ^ k * iterKernelW κ (0:ℝ) k τ p q := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
        intro τ hτ p q
        rw [iterE_one, pow_one, iterKernelW_one]
        exact hEbound τ p q hτ
    | succ m hm ih =>
        intro τ hτ p q
        obtain ⟨hI1, hI2, hIf, hIg, hIsg⟩ := mkI m hm ih τ hτ p q
        rw [iterE_succ E hm, iterKernelW_succ κ (0:ℝ) hm]
        simp only [heatConvK_apply]
        have hbound := heatConv_le_of_abs_le_pos E (iterE E m)
          (fun τ' p' q' => C * baseKernelW κ (0:ℝ) τ' p' q')
          (fun τ' p' q' => C ^ m * iterKernelW κ (0:ℝ) m τ' p' q')
          τ p q hτ
          (fun τ' p' q' hτ' => hEbound τ' p' q' hτ')
          (fun τ' p' q' hτ' => ih τ' hτ' p' q')
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
  exact fun k hk t ht x y => mkI k hk (Dall k hk) t ht x y

/-- **★ THE WIDE `hInt` PRODUCER FROM A SINGLE BASE MEASURABILITY.**  The width-parametric mirror of
    `HeatResidualBound.iterConvIntegrableW_of_bound_baseMeas`: from the width-`κ` one-step bound
    `hEbound`, `hEzero`, and the joint strong measurability `hEmeas` of `E`, the full family
    `IterConvIntegrableW E κ 0 C` holds.  The three regularity carries of the continuous producer are
    supplied by the WIDTH-FREE `iterE_zmeas` / `conv_meas` (reused untouched) plus the space slice of
    `hEmeas`.  This is the drop-in `hInt` discharge for the capstone at any `κ`. -/
theorem iterConvIntegrableW_of_bound_baseMeas_wide
    (E : ℝ → Point n → Point n → ℝ) (κ C : ℝ) (hκ : 0 < κ)
    (hEbound : ∀ τ p q, 0 < τ → |E τ p q| ≤ C * baseKernelW κ (0 : ℝ) τ p q)
    (hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, E τ p q = 0)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n => E q.1 q.2.1 q.2.2)) :
    IterConvIntegrableW E κ (0 : ℝ) C := by
  refine iterConvIntegrableW_of_bound_continuous_wide E κ C hκ hEbound hEzero ?_ ?_ ?_
  · intro τ p
    exact (hEmeas.comp_measurable
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · exact iterE_zmeas E hEmeas
  · exact conv_meas E hEmeas

/-! ### (c) The slot glue — the diagonal factor bridge, and its composition with the live bank. -/

/-- **THE DIAGONAL `hEboundW_le` FACTOR BRIDGE (c, what composes TODAY).**  Any diagonal (`p = 0`)
    bound of the wide-bank `gaussDdim (κ·τ)` shape is exactly the capstone's `hEboundW_le` slot at
    `p = 0`, via `baseKernelW_zero_diag`.  This is the bridge item [1] plugs into: once the residual
    assembly produces `|F τ z| ≤ C · gaussDdim (κ·τ) z` for `F = heatOp g gi H` at the base centre,
    this hands the capstone the `p = 0` slice of `hEboundW_le`.  Abstract in `F` so it serves both
    the witness and (after [1]) the residual. -/
theorem eboundW_le_diag_of_gaussDdim
    (F : ℝ → Point n → ℝ) (κ C t : ℝ)
    (hF : ∀ τ, 0 < τ → τ ≤ t → ∀ z : Point n, |F τ z| ≤ C * gaussDdim (κ * τ) z) :
    ∀ τ, 0 < τ → τ ≤ t → ∀ z : Point n,
      |F τ z| ≤ C * baseKernelW κ (0 : ℝ) τ (0 : Point n) z := by
  intro τ hτ hτt z
  rw [baseKernelW_zero_diag]
  exact hF τ hτ hτt z

/-- **THE LIVE-BANK COMPOSITION (c).**  Feeding `FixedGateDichotomy.zeroth_global_of_package`
    through the diagonal bridge puts the gated WITNESS into the exact `baseKernelW κ 0 τ 0 z` slot
    shape, globally in `z`, at the base field-centre `p = 0`:
        `∃ C > 0, ∀ 0 < τ ≤ τ₀, ∀ z, |vanVleckGatedWitness … τ 0 z| ≤ C · baseKernelW lam 0 τ 0 z`.
    ⚠ This bounds the WITNESS `H_G`, NOT the residual `heatOp g gi H = ∂_τH − Δ_g H`; discharging the
    capstone's `hEboundW_le` still needs item [1] (the `∂_τ`/`Δ_g` residual assembly) to relate the
    two, and item [2] (the `p = 0 → ∀ p q` uniformization).  It certifies the width bridge composes
    end-to-end with the LIVE bank. -/
theorem witness_zeroth_baseKernelW_diag {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {S : Point n → Set (Point n)} {i : Fin n}
    (P : WideAmplitudePackage g gi hC hK S i)
    (hSupp : ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
      vanVleckGatedWitness g gi hC hK S P.a P.b τ (0 : Point n) z ≠ 0 → z ∈ K ∧ ‖z‖ < P.r) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ, 0 < τ → τ ≤ P.τ₀ → ∀ z : Point n,
      |vanVleckGatedWitness g gi hC hK S P.a P.b τ (0 : Point n) z|
        ≤ C * baseKernelW P.lam (0 : ℝ) τ (0 : Point n) z := by
  obtain ⟨C, hC0, hbound⟩ := zeroth_global_of_package P hSupp
  exact ⟨C, hC0,
    eboundW_le_diag_of_gaussDdim
      (fun τ z => vanVleckGatedWitness g gi hC hK S P.a P.b τ (0 : Point n) z)
      P.lam C P.τ₀ hbound⟩

#print axioms heatKernel1D_neg
#print axioms gaussDdim_neg
#print axioms baseKernelW_zero_diag
#print axioms iterConvIntegrableW_of_bound_continuous_wide
#print axioms iterConvIntegrableW_of_bound_baseMeas_wide
#print axioms eboundW_le_diag_of_gaussDdim
#print axioms witness_zeroth_baseKernelW_diag

end QIQTH.WidthAdapters
