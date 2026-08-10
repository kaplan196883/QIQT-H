/-
  MemAdjHiMomentBound — J4-543: constructing the `MemAdjHi` moment-cancellation carry `hGpow` from the
  concrete amplitude data bundle (the DIRECT flat 3-term route), rather than carrying it abstractly.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It CONSTRUCTS
  the `τ^{-1/2}` signed-integral moment-cancellation carry `hGpow` (of `MemAdjHiSliver.hII_hi_from_sliver`
  / `DaLimLUMemAdjHi`) from the honest, satisfiable `AmplitudeDerivativeData` bundle — replacing the
  ABSTRACT `hGpow` carry by the geometric derivative-layer data it actually reduces to.  No `sorry`/`admit`
  (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypothesis, no
  hypothesis equal to (or trivially yielding) the conclusion, no existing file edited, nothing committed.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE MOMENT-CANCELLATION STRUCTURE (the adversarial gate, made explicit).

  The signed `z`-integral of the CURVED second-`x`-derivative pairing
      `∫ z, witnessSecondXDeriv i (u−s) z · F s z 0`
  does NOT enjoy `∫ z ∂²_x(H_G) = 0` "outright" — the curved/gated van-Vleck witness has no standalone
  vanishing-second-moment identity.  The cancellation is UNAVOIDABLY routed through the carried 3-term
  Leibniz-Gaussian decomposition (`AmplitudeDerivativeData.hD2Hexpand`, a genuine geometric fact — chart
  Jacobian at the RNC center + the C⁴ regularity tower):
      `witnessSecondXDeriv i τ z = (z_i²−2τ)/(4τ²)·G_τ(z)·Aamp τ z          -- LEADING flat-Gaussian Hessian
                                 + z_i/(2τ)·G_τ(z)·A1amp τ z               -- gradient
                                 + G_τ(z)·A2amp τ z.`                       -- mass
  The EXACT second-moment cancellation `∫ z ((z_i)²−2τ)/(4τ²)·G_τ(z) = 0` (`gaussian_hessian_moment_zero`)
  is applied to the LEADING flat-Gaussian Hessian term; ALL curvature (van-Vleck factor, chart image,
  radial cutoff) is absorbed into the BOUNDED, Lipschitz amplitudes `Aamp/A1amp/A2amp`.  So carrying the
  `AmplitudeDerivativeData` bundle IS the honest and unavoidable carry — not a hidden hole, and NOT a
  false "flat symmetry gives it for free" claim.  (Sol #J4-543 confirmed: no standalone `∫ ∂²ₓH_G = 0`.)

  ## WHAT LANDS.
    • `slice2_inner_bound` — ★ the GENERIC per-slice inner bound (the exposed `hinner` core of
      `SliverEstimates.sliver2_bound`): for a 3-term-decomposed `D2H` and width-2-dominated `F`,
          `|∫ z, D2H(u−s) z · F s z 0| ≤ (L·(15/2·n) + (3/4)·M₁·C_F)·(u−s)^{-1/2} + M₂·C_F`
      on the OPEN window `s ∈ Ioo (u−ε) u`, `C_F = C_L·gaussDdim a 0`.  Term 1 via the Hessian
      cancellation `gaussian_hessian_cancel`; term 2 via the crude odd first moment; term 3 via mass one.
    • `hGpow_of_amplitudeData` — ★★★ the capstone: from the concrete `AmplitudeDerivativeData` bundle
      (`∀ i`), uniform leading/mass constants `K₁`/`K₀`, the window floor data, and the single measure-zero
      `τ = 0` endpoint carry `hEndpoint`, produces `∃ Cpair ≥ 0` with the EXACT `hGpow` type of
      `MemAdjHiSliver.hII_hi_from_sliver`.  Route: `slice2_inner_bound` (per slice) → the `m`-uniform
      `τ^{-1/2}` absorption `GpowBridge.leviSecondPairing_le_invSqrt` (upper-endpoint trick) →
      the `Ioo → uIoc` upgrade `GpowClosure.hGpow_uIoc_of_Ioo_zeroEndpoint`.

  ## THE CARRIED INPUTS (honest, satisfiable, none the conclusion).
    • the `AmplitudeDerivativeData` bundle `data i` — the geometric 3-term decomposition + amplitude
      sup-bounds + the term-1 Lipschitz carry + measurability + the width-2 Levi domination;
    • `K₁`/`K₀` with the per-`i` comparison hypotheses (the uniform envelope of the per-coordinate
      constants — `m`- and `i`-uniform, chosen BEFORE the binders, no `εₘ⁻¹` leakage);
    • `hEndpoint` — the single `s = u` (`τ = 0`) measure-zero endpoint value (satisfiable: the pairing
      vanishes at `τ = 0` because `gaussDdim 0 ≡ 0` for `n ≥ 1`, so `witnessSecondXDeriv i 0 z = 0`; and
      it is measure-zero, hence irrelevant to the downstream integrability).

  ⚠  `a₁ = R/6` remains CONDITIONAL and effectively FLAT-ONLY.  Constructing `hGpow` from the amplitude
  data does NOT derive the coefficient — the capped leg-2 `hLapFull`, the convergence trio, and the
  Seeley–DeWitt geometric wiring all remain; and the curvature is carried honestly inside the amplitude
  bundle (`hD2Hexpand`), NOT eliminated.  NOT `a₁ = R/6`. -/
import Mathlib
import QIQTH.AmplitudePackage
import QIQTH.GpowClosure

open MeasureTheory Filter Set Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel QIQTH.TrueHeatKernel
open QIQTH.LaplaceBeltrami QIQTH.HeatResidualBound QIQTH.RadialDistance
open QIQTH.GaussianConvolution
open scoped Interval Topology BigOperators

namespace QIQTH.MemAdjHiMomentBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §A — the generic per-slice inner bound (the exposed `hinner` of `sliver2_bound`).
    ############################################################################### -/

/-- **★ `slice2_inner_bound`.**  THE GENERIC PER-SLICE INNER BOUND.  For a formal second-`x`-derivative
    object `D2H` carried with the exact 3-term Leibniz-Gaussian decomposition `hD2Hexpand` and a
    width-2-dominated `F`, the SIGNED `z`-pairing on the residual strip `s ∈ Ioo (u−ε) u` obeys
        `|∫ z, D2H(u−s) z · F s z 0| ≤ (L·(15/2·n) + (3/4)·M₁·C_F)·(u−s)^{-1/2} + M₂·C_F`,
    `C_F = C_L·gaussDdim a 0`.  This is the per-slice core of `SliverEstimates.sliver2_bound`, exposed as
    a standalone lemma: term 1 (Hessian) uses the EXACT second-moment cancellation
    `gaussian_hessian_cancel` (the `τ^{-1/2}` gain, needing `Aamp·F` Lipschitz); term 2 (gradient) uses
    the crude odd moment `∫|z_i|·G ≤ (3/2)√τ`; term 3 uses total mass one.  ⚠ NOT `a₁ = R/6`. -/
theorem slice2_inner_bound
    (D2H : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (Aamp A1amp A2amp : ℝ → Point n → ℝ)
    (i : Fin n) (T τ₀ : ℝ)
    (M₀ M₁ M₂ L C_L : ℝ)
    (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hL : 0 ≤ L) (hC_L : 0 ≤ C_L)
    (u ε a : ℝ) (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (_hε0 : 0 ≤ ε) (hεa : ε < a / 2)
    (hετ₀ : ε ≤ τ₀)
    (hD2Hexpand : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z : Point n,
        D2H τ z = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * Aamp τ z
          + z i / (2 * τ) * gaussDdim τ z * A1amp τ z
          + gaussDdim τ z * A2amp τ z)
    (hAampBdd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z, |Aamp τ z| ≤ M₀)
    (hA1ampBdd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z, |A1amp τ z| ≤ M₁)
    (hA2ampBdd : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z, |A2amp τ z| ≤ M₂)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hAampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => Aamp τ z) volume)
    (hA1ampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => A1amp τ z) volume)
    (hA2ampmeas : ∀ τ, AEStronglyMeasurable (fun z : Point n => A2amp τ z) volume)
    (hFmeas : ∀ s, AEStronglyMeasurable (fun z : Point n => F s z 0) volume)
    (hqLip : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ s, 0 < s → s ≤ T →
        ∀ z w : Point n, |Aamp τ z * F s z 0 - Aamp τ w * F s w 0| ≤ L * dist z w)
    (s : ℝ) (hsmem : s ∈ Set.Ioo (u - ε) u) :
    |∫ z, D2H (u - s) z * F s z 0|
      ≤ (L * (15 / 2 * (n : ℝ))
            + 3 / 4 * (M₁ * (C_L * gaussDdim a (0 : Point n)))) * (u - s) ^ (-(1 : ℝ) / 2)
        + M₂ * (C_L * gaussDdim a (0 : Point n)) := by
  have hT0 : 0 < T := lt_of_lt_of_le ha (le_trans hau huT)
  set C_F : ℝ := C_L * gaussDdim a (0 : Point n) with hCF_def
  have hCFnn : 0 ≤ C_F := mul_nonneg hC_L (gaussDdim_nonneg' _ _)
  have hFcap : ∀ s, a / 2 ≤ s → s ≤ T → ∀ z, |F s z 0| ≤ C_F := fun s hs hsT z =>
    B_le_MB F C_L T a hC_L hFdom ha s hs hsT z
  -- the per-slice inner bound (rpow form)
  have hτpos : 0 < u - s := by linarith [hsmem.2]
  have hlo : u - ε > a / 2 := by linarith
  have hspos : 0 < s := by linarith [hsmem.1, hlo]
  have hsT : s ≤ T := by linarith [hsmem.2, huT]
  have hsa2 : a / 2 ≤ s := by linarith [hsmem.1, hlo]
  have hττ₀ : u - s < τ₀ := by linarith [hsmem.1, hετ₀]
  have hFcaps : ∀ z, |F s z 0| ≤ C_F := fun z => hFcap s hsa2 hsT z
  set τ : ℝ := u - s with hτ_def
  have hτIoo : τ ∈ Set.Ioo (0 : ℝ) τ₀ := ⟨hτpos, hττ₀⟩
  -- integrability of the three terms
  have hqbdd : ∃ M, ∀ z, |Aamp τ z * F s z 0| ≤ M :=
    ⟨M₀ * C_F, fun z => by
      rw [abs_mul]; exact mul_le_mul (hAampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₀⟩
  have hT1int : Integrable
      (fun z => (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)) volume :=
    (hessCoeff_gaussDdim_integrable τ hτpos i).mul_bdd ((hAampmeas τ).mul (hFmeas s))
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hAampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₀))
  have hT2int : Integrable
      (fun z => z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)) volume :=
    (gradCoeff_gaussDdim_integrable τ hτpos i).mul_bdd ((hA1ampmeas τ).mul (hFmeas s))
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hA1ampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₁))
  have hT3int : Integrable (fun z => gaussDdim τ z * (A2amp τ z * F s z 0)) volume :=
    (gaussDdim_integrable τ hτpos).mul_bdd ((hA2ampmeas τ).mul (hFmeas s))
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hA2ampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₂))
  -- split into the three integrals
  have hsplit : (∫ z, D2H τ z * F s z 0)
      = (∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0))
        + (∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0))
        + (∫ z, gaussDdim τ z * (A2amp τ z * F s z 0)) := by
    have hpt : ∀ z : Point n, D2H τ z * F s z 0
        = (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)
          + z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)
          + gaussDdim τ z * (A2amp τ z * F s z 0) := by
      intro z; rw [hD2Hexpand τ hτIoo z]; ring
    have hf12 : Integrable (fun z : Point n =>
        (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)
          + z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)) volume := hT1int.add hT2int
    have e1 : (∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)
          + z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0))
        = (∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0))
          + ∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0) :=
      integral_add hT1int hT2int
    have e2 : (∫ z, ((z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)
            + z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0))
          + gaussDdim τ z * (A2amp τ z * F s z 0))
        = (∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)
            + z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0))
          + ∫ z, gaussDdim τ z * (A2amp τ z * F s z 0) :=
      integral_add hf12 hT3int
    rw [integral_congr_ae (ae_of_all _ hpt), e2, e1]
  -- term 1: the Hessian cancellation
  have hb1 : |∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)|
      ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ :=
    gaussian_hessian_cancel τ hτpos i (fun z => Aamp τ z * F s z 0) L hL
      (fun z w => hqLip τ hτIoo s hspos hsT z w) ((hAampmeas τ).mul (hFmeas s)) hqbdd
  -- term 2: the crude gradient moment
  have hb2 : |∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)|
      ≤ 3 / 4 * (M₁ * C_F) * (Real.sqrt τ)⁻¹ := by
    calc |∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)|
        = ‖∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ z, (1 / (2 * τ)) * (M₁ * C_F) * (|z i| * gaussDdim τ z) := by
          refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _))
            ((absCoord_gaussDdim_integrable τ hτpos i).const_mul _) (ae_of_all _ (fun z => ?_))
          dsimp only
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (gaussDdim_nonneg' τ z), abs_div,
              abs_of_pos (show (0 : ℝ) < 2 * τ by linarith)]
          have hq1 : |A1amp τ z * F s z 0| ≤ M₁ * C_F := by
            rw [abs_mul]; exact mul_le_mul (hA1ampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₁
          calc |z i| / (2 * τ) * gaussDdim τ z * |A1amp τ z * F s z 0|
              ≤ |z i| / (2 * τ) * gaussDdim τ z * (M₁ * C_F) :=
                mul_le_mul_of_nonneg_left hq1
                  (mul_nonneg (div_nonneg (abs_nonneg _) (by linarith)) (gaussDdim_nonneg' τ z))
            _ = (1 / (2 * τ)) * (M₁ * C_F) * (|z i| * gaussDdim τ z) := by ring
      _ = (1 / (2 * τ)) * (M₁ * C_F) * ∫ z, |z i| * gaussDdim τ z := integral_const_mul _ _
      _ ≤ (1 / (2 * τ)) * (M₁ * C_F) * (3 / 2 * Real.sqrt τ) := by
          refine mul_le_mul_of_nonneg_left (absCoord_gaussDdim_integral_le τ hτpos i) ?_
          exact mul_nonneg (div_nonneg zero_le_one (by linarith)) (mul_nonneg hM₁ hCFnn)
      _ = 3 / 4 * (M₁ * C_F) * (Real.sqrt τ)⁻¹ := by
          rw [show (1 / (2 * τ)) * (M₁ * C_F) * (3 / 2 * Real.sqrt τ)
                = 3 / 4 * (M₁ * C_F) * (τ⁻¹ * Real.sqrt τ) from by ring, invT_mul_sqrt τ hτpos]
  -- term 3: total mass one
  have hb3 : |∫ z, gaussDdim τ z * (A2amp τ z * F s z 0)| ≤ M₂ * C_F := by
    calc |∫ z, gaussDdim τ z * (A2amp τ z * F s z 0)|
        = ‖∫ z, gaussDdim τ z * (A2amp τ z * F s z 0)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ z, ‖gaussDdim τ z * (A2amp τ z * F s z 0)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, gaussDdim τ z * (M₂ * C_F) := by
          refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _))
            ((gaussDdim_integrable τ hτpos).mul_const _) (ae_of_all _ (fun z => ?_))
          dsimp only
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussDdim_nonneg' τ z)]
          refine mul_le_mul_of_nonneg_left ?_ (gaussDdim_nonneg' τ z)
          rw [abs_mul]; exact mul_le_mul (hA2ampBdd τ hτIoo z) (hFcaps z) (abs_nonneg _) hM₂
      _ = (∫ z, gaussDdim τ z) * (M₂ * C_F) := integral_mul_const _ _
      _ = 1 * (M₂ * C_F) := by rw [gaussDdim_integral_eq_one τ hτpos]
      _ = M₂ * C_F := one_mul _
  rw [hsplit]
  calc |(∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0))
          + (∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0))
          + (∫ z, gaussDdim τ z * (A2amp τ z * F s z 0))|
      ≤ |∫ z, (z i ^ 2 - 2 * τ) / (4 * τ ^ 2) * gaussDdim τ z * (Aamp τ z * F s z 0)|
          + |∫ z, z i / (2 * τ) * gaussDdim τ z * (A1amp τ z * F s z 0)|
          + |∫ z, gaussDdim τ z * (A2amp τ z * F s z 0)| :=
        le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ L * (15 / 2 * (n : ℝ)) / Real.sqrt τ + 3 / 4 * (M₁ * C_F) * (Real.sqrt τ)⁻¹ + M₂ * C_F :=
        add_le_add (add_le_add hb1 hb2) hb3
    _ = (L * (15 / 2 * (n : ℝ)) + 3 / 4 * (M₁ * C_F)) * τ ^ (-(1 : ℝ) / 2) + M₂ * C_F := by
        rw [← inv_sqrt_eq_rpow τ hτpos, div_eq_mul_inv]; ring

/-! ###############################################################################
    ### §B — ★★★ the capstone: `hGpow` from the concrete amplitude data bundle.
    ############################################################################### -/

/-- **★★★ `hGpow_of_amplitudeData`.**  THE CONSTRUCTION OF THE `MemAdjHi` MOMENT-CANCELLATION CARRY.
    From the concrete `AmplitudeDerivativeData` bundle `data i` (for `F := leviSeries (heatOp g gi H_G)`,
    `H_G := vanVleckGatedWitness …`), uniform leading/mass constants `K₁`/`K₀` (with the per-`i`
    comparison hypotheses `hK₁bound`/`hK₀bound`), the window floor data (`aa ≤ u`, `u ≤ T`,
    `epsSeq m < aa/2`, `epsSeq m ≤ τ₀`), and the single measure-zero `τ = 0` endpoint carry `hEndpoint`,
    there is a SINGLE `m`- and `i`-uniform `Cpair ≥ 0` with the EXACT `hGpow` type of
    `MemAdjHiSliver.hII_hi_from_sliver`:
        `|∫ z, witnessSecondXDeriv i (u−s) z · F s z 0| ≤ Cpair·(u−s)^{-1/2}`   on `Set.uIoc (u−ε_m) u`.
    Route: `slice2_inner_bound` (per slice, from `hD2Hexpand`) → `GpowBridge.leviSecondPairing_le_invSqrt`
    (the `m`-uniform upper-endpoint `τ^{-1/2}` absorption of the additive `K₀`) →
    `GpowClosure.hGpow_uIoc_of_Ioo_zeroEndpoint` (the `Ioo → uIoc` endpoint upgrade).  The moment
    cancellation lives in the LEADING flat-Gaussian Hessian term of `hD2Hexpand`; the curvature is carried
    inside the bounded amplitudes.  ⚠ NOT `a₁ = R/6`. -/
theorem hGpow_of_amplitudeData (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (T τ₀ aa : ℝ) (U : Set ℝ)
    (data : ∀ i : Fin n, AmplitudeDerivativeData g gi hChr hK S a b
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) i T τ₀)
    (haa : 0 < aa) (hau : ∀ u ∈ U, aa ≤ u) (hUT : ∀ u ∈ U, u ≤ T)
    (hεaa : ∀ m : ℕ, epsSeq m < aa / 2) (hετ₀ : ∀ m : ℕ, epsSeq m ≤ τ₀)
    (K₁ K₀ : ℝ) (hK₁ : 0 ≤ K₁) (hK₀ : 0 ≤ K₀)
    (hK₁bound : ∀ i : Fin n,
        (data i).L * (15 / 2 * (n : ℝ))
            + 3 / 4 * ((data i).M₁ * ((data i).C_L * gaussDdim aa (0 : Point n))) ≤ K₁)
    (hK₀bound : ∀ i : Fin n,
        (data i).M₂ * ((data i).C_L * gaussDdim aa (0 : Point n)) ≤ K₀)
    (hEndpoint : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U,
        ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - u) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) u z 0 = 0) :
    ∃ Cpair : ℝ, 0 ≤ Cpair ∧
      ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.uIoc (u - epsSeq m) u,
        |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
          ≤ Cpair * (u - s) ^ (-(1 : ℝ) / 2) := by
  -- the per-slice OPEN-window inner bound in the `K₁·(u−s)^{-1/2} + K₀` shape.
  have hinner_window : ∀ (m : ℕ) (i : Fin n), ∀ u ∈ U, ∀ s ∈ Set.Ioo (u - epsSeq m) u,
      |∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0|
        ≤ K₁ * (u - s) ^ (-(1 : ℝ) / 2) + K₀ := by
    intro m i u hu s hsmem
    have hrpow : 0 ≤ (u - s) ^ (-(1 : ℝ) / 2) :=
      (Real.rpow_pos_of_pos (by linarith [hsmem.2] : (0 : ℝ) < u - s) _).le
    have hbase := slice2_inner_bound
      (fun τ z => witnessSecondXDeriv g gi hChr hK S a b i τ z)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      (data i).Aamp (data i).A1amp (data i).A2amp i T τ₀
      (data i).M₀ (data i).M₁ (data i).M₂ (data i).L (data i).C_L
      (data i).hM₀ (data i).hM₁ (data i).hM₂ (data i).hL (data i).hC_L
      u (epsSeq m) aa haa (hau u hu) (hUT u hu) (epsSeq_pos m).le (hεaa m) (hετ₀ m)
      (data i).hD2Hexpand (data i).hAampBdd (data i).hA1ampBdd (data i).hA2ampBdd (data i).hFdom
      (data i).hAampmeas (data i).hA1ampmeas (data i).hA2ampmeas (data i).hFmeas (data i).hqLip
      s hsmem
    refine le_trans hbase ?_
    exact add_le_add (mul_le_mul_of_nonneg_right (hK₁bound i) hrpow) (hK₀bound i)
  -- the `m`-uniform `τ^{-1/2}` absorption (upper-endpoint trick) → OPEN-window `Cpair`.
  obtain ⟨Cpair, hCpair, hIoo⟩ :=
    QIQTH.GpowBridge.leviSecondPairing_le_invSqrt (n := n) U K₁ K₀ hK₁ hK₀
      (fun m i u s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
      hinner_window
  -- the `Ioo → uIoc` endpoint upgrade → the EXACT `hGpow` type.
  refine ⟨Cpair, hCpair, ?_⟩
  exact QIQTH.GpowClosure.hGpow_uIoc_of_Ioo_zeroEndpoint (n := n) U Cpair
    (fun m i u s => ∫ z, witnessSecondXDeriv g gi hChr hK S a b i (u - s) z
        * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
    hIoo hEndpoint

end QIQTH.MemAdjHiMomentBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.MemAdjHiMomentBound.slice2_inner_bound
#print axioms QIQTH.MemAdjHiMomentBound.hGpow_of_amplitudeData
