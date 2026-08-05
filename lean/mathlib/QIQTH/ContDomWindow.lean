/-
  ContDomWindow — J4-247: the `hContDom` brick — the last F2 carry.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  It discharges
  the ANALYTIC HALF of the per-interior-point dominated-continuity datum `hContDom` that
  `InnerMeasFubini.hInnerCont_concrete` / `F2CarryDischarge2.f2Pack_concrete_v2` still consume as a
  single opaque carry, and re-bundles the F2 pile in `f2Pack_concrete_v3`.  No `sorry` (prose
  excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no
  conclusion-in-disguise.  No existing file is edited.

  ── WHAT IS DISCHARGED HERE (axiom-free, no `sorry`).

    `hContDom` (the `InnerMeasFubini` shape) is, for each `u ∈ U`, each interior `s₀ ∈ Ioo 0 u`, the
    package `∃ bound, Integrable bound ∧ (∀ᶠ s, AEStronglyMeasurable slice) ∧
    (∀ᶠ s, ∀ᵐ z, ‖slice‖ ≤ bound) ∧ (∀ᵐ z, ContinuousAt s-slice)`.  Two of its four conjuncts — the
    **existence of an integrable dominator** and the **uniform-over-a-window norm bound** — are the
    genuinely analytic pieces.  This file BUILDS them from the RAW Gaussian dominations of the two
    kernels, leaving only the measurability (`AEStronglyMeasurable`) and continuity (`ContinuousAt`)
    conjuncts as separate, lighter carries.

    (1)  `gaussDdim_window_le` — THE WINDOW DOMINATOR.  For `0 < σlo ≤ σ ≤ σhi`,
             `gaussDdim σ x ≤ (√(σhi/σlo))ⁿ · gaussDdim σhi x`
         (the wider Gaussian, up-scaled by the fixed prefactor ratio, dominates the whole
         width-window).  Bankable in isolation; the foundation of the window bound.

    (2)  `hContDom_of_gaussDom` — THE ABSTRACT BUILDER.  For abstract kernels `A`, `B` carrying the
         D1 Gaussian domination `|A τ p q| ≤ (A₀+A₁τ)·√(3/2)ⁿ·gaussDdim((3/2)τ)(p−q)` (∀ τ>0) and the
         width-`2` Levi domination `|B s z y| ≤ C_L·gaussDdim(2s)(z−y)` on `(0,T]`, plus the two
         lighter measurability/continuity carries, produces the FULL `hContDom` existential with the
         CONSTRUCTED integrable dominator `Kc·gaussDdim sAhi(0−z)·gaussDdim sBhi(z−0)` (a fixed
         product Gaussian, integrable by `gaussDdim_mul_integrable`) and the PROVED uniform norm
         bound on the window `Ioo (s₀−δ) (s₀+δ)`, `δ := min s₀ (u−s₀)/2` (which keeps `u−s`, `s`
         bounded away from `0` and `s ≤ u ≤ T`).

    (3)  `hContDom_discharged` — (2) instantiated at the CONCRETE gated van-Vleck / Levi kernels, in
         the EXACT `InnerMeasFubini` carry shape.

    (4)  `f2Pack_concrete_v3` — the F2 pack with `hContDom`'s analytic half internal; only v2'-level
         binders remain (the Gaussian dominations, `hBcont`, `hKm`/`hSm0`, the windows, plus the two
         lighter measurability/continuity carries of the interior slice).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.F2CarryDischarge2
import QIQTH.ConvCarriesDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.ContDomWindow

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (1) — the window dominator lemma.
    ############################################################################### -/

/-- **1-D window dominator.**  For `0 < σlo ≤ σ ≤ σhi`,
    `heatKernel1D σ x ≤ √(σhi/σlo) · heatKernel1D σhi x`: the prefactor `(√(4πσ))⁻¹` is `≤ (√(4πσlo))⁻¹`
    (width `≥ σlo`) and the exponential `exp(−x²/(4σ)) ≤ exp(−x²/(4σhi))` (width `≤ σhi`); the two
    fixed prefactors combine into the ratio `√(σhi/σlo)`.  NOT `a₁ = R/6`. -/
theorem heatKernel1D_window_le {σ σlo σhi : ℝ} (hposlo : 0 < σlo) (hlo : σlo ≤ σ) (hhi : σ ≤ σhi)
    (x : ℝ) :
    QIQTH.HeatKernelA1.heatKernel1D σ x
      ≤ Real.sqrt (σhi / σlo) * QIQTH.HeatKernelA1.heatKernel1D σhi x := by
  have hσ : 0 < σ := lt_of_lt_of_le hposlo hlo
  have hσhi : 0 < σhi := lt_of_lt_of_le hσ hhi
  -- exponent monotonicity
  have hexp : Real.exp (-x ^ 2 / (4 * σ)) ≤ Real.exp (-x ^ 2 / (4 * σhi)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div, neg_le_neg_iff]
    gcongr
  -- prefactor monotonicity
  have hpre_le : (Real.sqrt (4 * Real.pi * σ))⁻¹ ≤ (Real.sqrt (4 * Real.pi * σlo))⁻¹ := by
    have h0 : (0 : ℝ) < Real.sqrt (4 * Real.pi * σlo) := by
      apply Real.sqrt_pos.mpr; positivity
    apply inv_anti₀ h0
    apply Real.sqrt_le_sqrt; nlinarith [Real.pi_pos]
  -- the fixed-prefactor identity
  have hpre : (Real.sqrt (4 * Real.pi * σlo))⁻¹
      = Real.sqrt (σhi / σlo) * (Real.sqrt (4 * Real.pi * σhi))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_inv,
        ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ σhi / σlo)]
    congr 1
    have hσlo : σlo ≠ 0 := hposlo.ne'
    have hσhi' : σhi ≠ 0 := hσhi.ne'
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  calc QIQTH.HeatKernelA1.heatKernel1D σ x
      = (Real.sqrt (4 * Real.pi * σ))⁻¹ * Real.exp (-x ^ 2 / (4 * σ)) := by
        rw [QIQTH.HeatKernelA1.heatKernel1D]
    _ ≤ (Real.sqrt (4 * Real.pi * σ))⁻¹ * Real.exp (-x ^ 2 / (4 * σhi)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ (Real.sqrt (4 * Real.pi * σlo))⁻¹ * Real.exp (-x ^ 2 / (4 * σhi)) :=
        mul_le_mul_of_nonneg_right hpre_le (Real.exp_pos _).le
    _ = Real.sqrt (σhi / σlo) *
          ((Real.sqrt (4 * Real.pi * σhi))⁻¹ * Real.exp (-x ^ 2 / (4 * σhi))) := by
        rw [hpre]; ring
    _ = Real.sqrt (σhi / σlo) * QIQTH.HeatKernelA1.heatKernel1D σhi x := by
        rw [QIQTH.HeatKernelA1.heatKernel1D]

/-- **★ `gaussDdim_window_le` — THE WINDOW DOMINATOR.**  For `0 < σlo ≤ σ ≤ σhi`,
        `gaussDdim σ x ≤ (√(σhi/σlo))ⁿ · gaussDdim σhi x`.
    Coordinatewise `heatKernel1D_window_le`, then `∏ₖ (r · fₖ) = rⁿ · ∏ₖ fₖ`.  NOT `a₁ = R/6`. -/
theorem gaussDdim_window_le {σ σlo σhi : ℝ} (hposlo : 0 < σlo) (hlo : σlo ≤ σ) (hhi : σ ≤ σhi)
    (x : Point n) :
    gaussDdim σ x ≤ (Real.sqrt (σhi / σlo)) ^ n * gaussDdim σhi x := by
  have hσ : 0 < σ := lt_of_lt_of_le hposlo hlo
  simp only [gaussDdim]
  calc ∏ k, QIQTH.HeatKernelA1.heatKernel1D σ (x k)
      ≤ ∏ k, Real.sqrt (σhi / σlo) * QIQTH.HeatKernelA1.heatKernel1D σhi (x k) := by
        apply Finset.prod_le_prod
        · intro i _; exact (QIQTH.GaussianConvolution.heatKernel1D_pos σ (x i) hσ).le
        · intro i _; exact heatKernel1D_window_le hposlo hlo hhi (x i)
    _ = (Real.sqrt (σhi / σlo)) ^ n * ∏ k, QIQTH.HeatKernelA1.heatKernel1D σhi (x k) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ###############################################################################
    ### (2) — the abstract builder: raw Gaussian dominations ⟹ the `hContDom` existential.
    ############################################################################### -/

/-- **★★ `hContDom_of_gaussDom` — THE ABSTRACT `hContDom` BUILDER.**  For abstract kernels `A`, `B`
    carrying the D1 Gaussian domination (for `A`, ∀ `τ>0`) and the width-`2` Levi domination (for `B`
    on `(0,T]`), together with the two lighter carries — the eventual slice `AEStronglyMeasurable`
    `hmeas` and the a.e.-`z` `ContinuousAt` `hcont` — this produces the FULL `hContDom` existential at
    every interior `s₀ ∈ Ioo 0 u`.  The integrable dominator
    `bound z := Kc · gaussDdim sAhi (0−z) · gaussDdim sBhi (z−0)` is CONSTRUCTED (integrable by
    `gaussDdim_mul_integrable`) and the uniform norm bound is PROVED on the window
    `Ioo (s₀−δ) (s₀+δ)`, `δ := min s₀ (u−s₀)/2`.  NOT `a₁ = R/6`. -/
theorem hContDom_of_gaussDom
    (A B : ℝ → Point n → Point n → ℝ) (u T : ℝ) (huT : u ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |A τ p q| ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |B s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hmeas : ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
        AEStronglyMeasurable (fun z => A (u - s) 0 z * B s z 0) (volume : Measure (Point n)))
    (hcont : ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
        ContinuousAt (fun s => A (u - s) 0 z * B s z 0) s₀) :
    ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∃ bound : Point n → ℝ,
        Integrable bound (volume : Measure (Point n)) ∧
        (∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable
          (fun z => A (u - s) 0 z * B s z 0) (volume : Measure (Point n))) ∧
        (∀ᶠ s in 𝓝 s₀, ∀ᵐ z ∂(volume : Measure (Point n)),
          ‖A (u - s) 0 z * B s z 0‖ ≤ bound z) ∧
        (∀ᵐ z ∂(volume : Measure (Point n)),
          ContinuousAt (fun s => A (u - s) 0 z * B s z 0) s₀) := by
  intro s₀ hs₀
  obtain ⟨hs₀pos, hs₀u⟩ := hs₀
  have hτ0 : 0 < u - s₀ := by linarith
  -- the window radius
  set δ : ℝ := min s₀ (u - s₀) / 2 with hδdef
  have hδs₀ : δ ≤ s₀ / 2 := by
    rw [hδdef]; have := min_le_left s₀ (u - s₀); linarith
  have hδτ : δ ≤ (u - s₀) / 2 := by
    rw [hδdef]; have := min_le_right s₀ (u - s₀); linarith
  have hδpos : 0 < δ := by
    rw [hδdef]; have := lt_min hs₀pos hτ0; linarith
  -- fixed window widths
  set sAhi : ℝ := 3 / 2 * (u - s₀ + δ) with hsAhi
  set sAlo : ℝ := 3 / 2 * (u - s₀ - δ) with hsAlo
  set sBhi : ℝ := 2 * (s₀ + δ) with hsBhi
  set sBlo : ℝ := 2 * (s₀ - δ) with hsBlo
  have hsAlo_pos : 0 < sAlo := by rw [hsAlo]; nlinarith
  have hsBlo_pos : 0 < sBlo := by rw [hsBlo]; nlinarith
  set Sc : ℝ := Real.sqrt (3 / 2 : ℝ) ^ n with hSc
  set rA : ℝ := (Real.sqrt (sAhi / sAlo)) ^ n with hrA
  set rB : ℝ := (Real.sqrt (sBhi / sBlo)) ^ n with hrB
  set ampH : ℝ := A₀ + A₁ * (u - s₀ + δ) with hampH
  set Kc : ℝ := ampH * Sc * rA * C_L * rB with hKc
  have hScnn : 0 ≤ Sc := by rw [hSc]; positivity
  have hrAnn : 0 ≤ rA := by rw [hrA]; positivity
  have hrBnn : 0 ≤ rB := by rw [hrB]; positivity
  have hampHnn : 0 ≤ ampH := by rw [hampH]; nlinarith
  have hKcnn : 0 ≤ Kc := by rw [hKc]; positivity
  -- the constructed dominator
  refine ⟨fun z => Kc * (gaussDdim sAhi (0 - z) * gaussDdim sBhi (z - 0)), ?_,
    hmeas s₀ ⟨hs₀pos, hs₀u⟩, ?_, hcont s₀ ⟨hs₀pos, hs₀u⟩⟩
  · -- integrability of the dominator
    exact (gaussDdim_mul_integrable sAhi sBhi 0 0).const_mul Kc
  · -- the uniform norm bound on the open window
    have hmem : Set.Ioo (s₀ - δ) (s₀ + δ) ∈ 𝓝 s₀ :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    refine Filter.eventually_of_mem hmem (fun s hs => ?_)
    obtain ⟨hsl, hsr⟩ := hs
    refine ae_of_all _ (fun z => ?_)
    -- window facts for this `s`
    have hspos : 0 < s := by linarith
    have hτpos : 0 < u - s := by linarith
    have hsT : s ≤ T := by linarith
    -- widths in range
    have hsA_lo : sAlo ≤ 3 / 2 * (u - s) := by rw [hsAlo]; nlinarith
    have hsA_hi : 3 / 2 * (u - s) ≤ sAhi := by rw [hsAhi]; nlinarith
    have hsB_lo : sBlo ≤ 2 * s := by rw [hsBlo]; nlinarith
    have hsB_hi : 2 * s ≤ sBhi := by rw [hsBhi]; nlinarith
    -- bound on the `A`-factor
    have hAbound : |A (u - s) 0 z| ≤ ampH * Sc * (rA * gaussDdim sAhi (0 - z)) := by
      calc |A (u - s) 0 z|
          ≤ (A₀ + A₁ * (u - s)) * Sc * gaussDdim (3 / 2 * (u - s)) (0 - z) := by
            rw [hSc]; exact hAdom (u - s) hτpos 0 z
        _ ≤ (A₀ + A₁ * (u - s)) * Sc * (rA * gaussDdim sAhi (0 - z)) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by nlinarith) hScnn)
            rw [hrA]; exact gaussDdim_window_le hsAlo_pos hsA_lo hsA_hi (0 - z)
        _ ≤ ampH * Sc * (rA * gaussDdim sAhi (0 - z)) := by
            apply mul_le_mul_of_nonneg_right _
              (mul_nonneg hrAnn (QIQTH.ResidueBound.gaussDdim_nonneg _ _))
            apply mul_le_mul_of_nonneg_right _ hScnn
            rw [hampH]; nlinarith
    -- bound on the `B`-factor
    have hBbound : |B s z 0| ≤ C_L * (rB * gaussDdim sBhi (z - 0)) := by
      calc |B s z 0|
          ≤ C_L * gaussDdim (2 * s) (z - 0) := hBdom s hspos hsT z 0
        _ ≤ C_L * (rB * gaussDdim sBhi (z - 0)) := by
            apply mul_le_mul_of_nonneg_left _ hC_L
            rw [hrB]; exact gaussDdim_window_le hsBlo_pos hsB_lo hsB_hi (z - 0)
    -- combine
    have hXnn : 0 ≤ ampH * Sc * (rA * gaussDdim sAhi (0 - z)) :=
      mul_nonneg (mul_nonneg hampHnn hScnn)
        (mul_nonneg hrAnn (QIQTH.ResidueBound.gaussDdim_nonneg _ _))
    calc ‖A (u - s) 0 z * B s z 0‖
        = |A (u - s) 0 z| * |B s z 0| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ (ampH * Sc * (rA * gaussDdim sAhi (0 - z))) * (C_L * (rB * gaussDdim sBhi (z - 0))) :=
          mul_le_mul hAbound hBbound (abs_nonneg _) hXnn
      _ = Kc * (gaussDdim sAhi (0 - z) * gaussDdim sBhi (z - 0)) := by rw [hKc]; ring

/-! ###############################################################################
    ### (3) — the concrete `hContDom_discharged`, in the exact `InnerMeasFubini` carry shape.
    ############################################################################### -/

/-- **★★ `hContDom_discharged` — THE CONCRETE `hContDom`, ANALYTIC HALF DISCHARGED.**  Exactly the
    `hContDom` shape `InnerMeasFubini.hInnerCont_concrete` / `F2CarryDischarge2.f2Pack_concrete_v2`
    consume, for the concrete gated van-Vleck value kernel `A := vanVleckGatedWitness …` and the Levi
    kernel `B := leviSeries (heatOp g gi A)`.  The integrable dominator and the uniform norm bound are
    BUILT INTERNALLY by `hContDom_of_gaussDom` from the raw Gaussian dominations
    {`hAdom` (D1), `hBdom` (width-`2`)}; the remaining measurability/continuity of the interior slice
    are carried as the two lighter inputs {`hmeas`, `hcont`}.  NOT `a₁ = R/6`. -/
theorem hContDom_discharged (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hmeas : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
        AEStronglyMeasurable
          (fun z => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (volume : Measure (Point n)))
    (hcont : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
        ContinuousAt
          (fun s => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) s₀) :
    ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u,
        ∃ bound : Point n → ℝ, Integrable bound (volume : Measure (Point n)) ∧
          (∀ᶠ s in 𝓝 s₀, AEStronglyMeasurable
            (fun z => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
            (volume : Measure (Point n))) ∧
          (∀ᶠ s in 𝓝 s₀, ∀ᵐ z ∂(volume : Measure (Point n)),
            ‖vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0‖
              ≤ bound z) ∧
          (∀ᵐ z ∂(volume : Measure (Point n)), ContinuousAt
            (fun s => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
              * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) s₀) :=
  fun u hu =>
    hContDom_of_gaussDom
      (vanVleckGatedWitness g gi hChr hK S a b)
      (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
      u T (hUT u hu) A₀ A₁ C_L hA₀ hA₁ hC_L hAdom hBdom (hmeas u hu) (hcont u hu)

/-! ###############################################################################
    ### ★ (4) — THE F2 PACK v3: `hContDom`'s analytic half internal.
    ############################################################################### -/

/-- **★★★ `f2Pack_concrete_v3` — THE F2 SUPPLY WITH `hContDom`'s ANALYTIC HALF DISCHARGED.**
    Identical conclusion (the four deferred F2 slots `hMeasFII`/`hInnerCont`/`hFmeas`/`hF'meas`) to
    `F2CarryDischarge2.f2Pack_concrete_v2`, but the `hContDom` carry is now BUILT INTERNALLY by
    `hContDom_discharged`: the opaque existential integrable dominator + the uniform-over-window norm
    bound are CONSTRUCTED from the raw Gaussian dominations {`hAdom` (D1), `hBdom` (width-`2`)}, so
    only the two lighter measurability/continuity carries of the interior slice {`hmeas`, `hcont`}
    remain in its place (alongside the already-discharged `hInner`/`hWitDeriv` of v2).  Each carried
    input is satisfiable, non-vacuous, none the conclusion.  NOT `a₁ = R/6`. -/
theorem f2Pack_concrete_v3 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (U : Set ℝ)
    (hKm : MeasurableSet K)
    (hSm0 : MeasurableSet {z : Point n | (0 : Point n) ∈ S z})
    (hΘc : Continuous (vanVleck g))
    (hΘne : ∀ w, vanVleck g w ≠ 0)
    (huc : ∀ k, Continuous (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hVmap0 : AEMeasurable
      (fun z : Point n => uniformInverseChart g gi hChr hK z (0 : Point n)) volume)
    (hKSmeas : MeasurableSet {w : ℝ × Point n × Point n | w.2.2 ∈ K ∧ w.2.1 ∈ S w.2.2})
    (hcar : ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 → w.2.1 ∈ S w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hLeviJoint : ∀ d : ℝ, AEStronglyMeasurable
      (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) p.1 p.2 0)
      ((volume.restrict (Set.uIoc 0 d)).prod (volume : Measure (Point n))))
    (hBcont : ContinuousOn
      (fun x : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) x.1 x.2 0)
      (Set.Ioc 0 T ×ˢ (Set.univ : Set (Point n))))
    (hUpos : ∀ u ∈ U, 0 < u) (hUT : ∀ u ∈ U, u ≤ T)
    (A₀ A₁ C_L : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness g gi hChr hK S a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y|
          ≤ C_L * gaussDdim (2 * s) (z - y))
    (hmeas : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
        AEStronglyMeasurable
          (fun z => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
          (volume : Measure (Point n)))
    (hcont : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
        ContinuousAt
          (fun s => vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
            * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0) s₀) :
    -- (F2-a) hMeasFII
    (∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 u)))
    -- (F2-b) hInnerCont
    ∧ (∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (u - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (Set.Ioo 0 u))
    -- (F2-c) hFmeas
    ∧ (∀ (m : ℕ), ∀ u ∈ U, ∀ a', AEStronglyMeasurable
        (fun s => ∫ z, vanVleckGatedWitness g gi hChr hK S a b (a' - s) 0 z
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m))))
    -- (F2-d) hF'meas
    ∧ (∀ (m : ℕ), ∀ u ∈ U, AEStronglyMeasurable
        (fun s => ∫ z, deriv (fun r => vanVleckGatedWitness g gi hChr hK S a b r 0 z) (u - s)
          * leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z 0)
        (volume.restrict (Set.uIoc 0 (u - epsSeq m)))) :=
  QIQTH.F2CarryDischarge2.f2Pack_concrete_v2 hn g gi hChr hK S a b T U hKm hSm0
    hΘc hΘne huc hVmap0 hKSmeas hcar hLeviJoint hBcont hUpos hUT
    (hContDom_discharged g gi hChr hK S a b T U hUT A₀ A₁ C_L hA₀ hA₁ hC_L
      hAdom hBdom hmeas hcont)

end QIQTH.ContDomWindow

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ContDomWindow
#print axioms heatKernel1D_window_le
#print axioms gaussDdim_window_le
#print axioms hContDom_of_gaussDom
#print axioms hContDom_discharged
#print axioms f2Pack_concrete_v3
end AxiomChecks
