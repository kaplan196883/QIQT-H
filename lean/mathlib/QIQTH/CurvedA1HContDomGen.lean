/-
  CurvedA1HContDomGen — J4-688: the WIDTH-GENERIC, WITNESS-GENERIC re-base of the `hContDom` /
  `hInnerCont` reduction.  Downstream item (a) of the J4-687 all-rows whitened `hBdom` re-base:
  the builder `CurvedA1HContDom.curved_hInnerCont_of_dominations` is PINNED at the concrete
  `vanVleckGatedWitness` W-slot and the width `2` B-slot; this file ABSTRACTS both, so the
  full-matrix whitened `WhiteHBdomAllRows.white_hBdom_discharged` (width `lam = whiteLam`) can
  actually feed an `hInnerCont`-shaped conclusion at the WHITENED witness.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ── ★★ THE WITNESS-GENERICITY VERDICT (the finding).  The entire `hContDom → hInnerCont` chain is
     WITNESS-GENERIC modulo the two Gaussian dominations + the two measurability/continuity carries,
     and only WIDTH-SPECIFIC at ONE hardcoded spot:

       • The DCT/continuity ENGINE `InnerMeasFubini.innerIntegral_continuousOn_of_dominated` is
         stated at an ABSTRACT integrand `F : X → α → ℝ` and abstract `μ`; the witness identity NEVER
         enters — `hInnerCont_concrete` / `curved_hInnerCont_at_gate` merely PLUG IN the concrete
         product `fun s z => W (u−s) 0 z · L s z 0` as `F`.  So the continuity half is already fully
         abstract.
       • The domination BUILDER `ContDomWindow.hContDom_of_gaussDom` is ALREADY stated at abstract
         kernels `A B : ℝ → Point n → Point n → ℝ`; it is only WIDTH-SPECIFIC — the A-slot width
         `3/2` and the B-slot width `2` are hardcoded (and the A-slot prefactor `√(3/2)ⁿ`).  Those
         widths are used ONLY to fix the window Gaussian widths `sAhi/sAlo/sBhi/sBlo`; the proof
         needs them only POSITIVE.  Generalizing `3/2 ↦ wA`, `2 ↦ wB`, `√(3/2)ⁿ ↦ Cpre` is a verbatim
         replay.

     Hence a genuinely GENERIC builder exists: abstract kernels `(A,B)`, abstract widths `(wA,wB)`,
     abstract prefactor `Cpre` and affine amplitude `(A₀+A₁τ)`.  The vanVleck version is the instance
     `wA := 3/2`, `wB := 2`, `Cpre := √(3/2)ⁿ`; the whitened version is the instance `wA :=` (the
     whitened value width), `wB := lam = whiteLam`.

  ── WHAT LANDS HERE (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    • `hContDom_of_gaussDom_gen` — ★★ the WIDTH-GENERIC abstract `hContDom` builder: for abstract
      kernels `A`, `B`, ANY positive widths `wA`, `wB`, prefactor `Cpre ≥ 0`, affine amplitude
      `(A₀+A₁τ)`, from {the A-slot Gaussian domination at width `wA`, the B-slot Gaussian domination
      at width `wB` on `(0,T]`, the eventual slice `AEStronglyMeasurable`, the a.e.-`z` `ContinuousAt`}
      it CONSTRUCTS the integrable window dominator + the uniform-over-window norm bound and produces
      the FULL `hContDom` existential at every interior `s₀ ∈ Ioo 0 u`.
    • `hInnerCont_of_dominations_generic` — ★★ the COMPOSED width/witness-generic reduction: feeds
      `hContDom_of_gaussDom_gen` into `InnerMeasFubini.innerIntegral_continuousOn_of_dominated`, so
      for abstract kernels/widths the interior-time continuity of the inner pairing
      `s ↦ ∫ z, A (u−s) 0 z · B s z 0` on `Ioo 0 u` is reduced ALL THE WAY to the four raw carries
      `{hAdom, hBdom, hmeas, hcont}`.  This is the metric-agnostic, width-agnostic core the pinned
      `CurvedA1HContDom.curved_hInnerCont_of_dominations` is a specialization of.

  ⚠ HONEST FIREWALL.  Builder re-base ONLY — this is NOT `a₁ = R/6` and proves NOTHING about `R/6`
  (the `R/6` value is a labelled carrier, untouched).  The generic conclusion is the interior-time
  continuity of an ABSTRACT inner pairing, reduced to abstract dominations; instantiating it at the
  whitened witness still owes the whitened value-domination + the whitened-defect S1 measurability +
  the interior measurability/continuity carries.  Everything here is DERIVED from the PROVED
  `ContDomWindow` window lemma + the PROVED abstract continuity engine, NOT axiomatized, NOT the `a₁`
  conclusion.  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous / conclusion-in-disguise
  hypothesis, no existing file edited, nothing committed.
-/
import Mathlib
import QIQTH.ContDomWindow
import QIQTH.InnerMeasFubini

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open scoped Interval Topology BigOperators

namespace QIQTH.CurvedA1HContDomGen

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (1) — the WIDTH-GENERIC abstract `hContDom` builder.
    ############################################################################### -/

/-- **★★ `hContDom_of_gaussDom_gen` — THE WIDTH-GENERIC ABSTRACT `hContDom` BUILDER.**  The
    width-parametric replay of `ContDomWindow.hContDom_of_gaussDom`: for abstract kernels `A`, `B`,
    ANY positive widths `wA`, `wB`, a nonnegative prefactor `Cpre` and affine amplitude `(A₀+A₁τ)`,
    from the A-slot Gaussian domination `|A τ p q| ≤ (A₀+A₁τ)·Cpre·gaussDdim (wA·τ)(p−q)` (∀ `τ>0`),
    the B-slot Gaussian domination `|B s z y| ≤ C_L·gaussDdim (wB·s)(z−y)` on `(0,T]`, and the two
    lighter carries {eventual slice `AEStronglyMeasurable` `hmeas`, a.e.-`z` `ContinuousAt` `hcont`},
    this produces the FULL `hContDom` existential at every interior `s₀ ∈ Ioo 0 u`.  The integrable
    dominator `Kc·gaussDdim sAhi (0−z)·gaussDdim sBhi (z−0)` is CONSTRUCTED (integrable by
    `gaussDdim_mul_integrable`) and the uniform norm bound PROVED on the window `Ioo (s₀−δ)(s₀+δ)`,
    `δ := min s₀ (u−s₀)/2` (both `u−s`, `s` bounded away from `0`, `s ≤ u ≤ T`).  The widths enter
    ONLY as the positive window Gaussian widths — verbatim the `3/2`/`2` argument with `3/2 ↦ wA`,
    `2 ↦ wB`, `√(3/2)ⁿ ↦ Cpre`.  NOT `a₁ = R/6`. -/
theorem hContDom_of_gaussDom_gen
    (A B : ℝ → Point n → Point n → ℝ) (u T wA wB : ℝ) (huT : u ≤ T)
    (hwA : 0 < wA) (hwB : 0 < wB)
    (Cpre A₀ A₁ C_L : ℝ) (hCpre : 0 ≤ Cpre) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |A τ p q| ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q))
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |B s z y| ≤ C_L * gaussDdim (wB * s) (z - y))
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
  set δ : ℝ := min s₀ (u - s₀) / 2 with hδdef
  have hδs₀ : δ ≤ s₀ / 2 := by
    rw [hδdef]; have := min_le_left s₀ (u - s₀); linarith
  have hδτ : δ ≤ (u - s₀) / 2 := by
    rw [hδdef]; have := min_le_right s₀ (u - s₀); linarith
  have hδpos : 0 < δ := by
    rw [hδdef]; have := lt_min hs₀pos hτ0; linarith
  -- fixed window widths (at the generic widths `wA`, `wB`)
  set sAhi : ℝ := wA * (u - s₀ + δ) with hsAhi
  set sAlo : ℝ := wA * (u - s₀ - δ) with hsAlo
  set sBhi : ℝ := wB * (s₀ + δ) with hsBhi
  set sBlo : ℝ := wB * (s₀ - δ) with hsBlo
  have humsδ : 0 < u - s₀ - δ := by linarith
  have hs₀mδ : 0 < s₀ - δ := by linarith
  have hsAlo_pos : 0 < sAlo := by rw [hsAlo]; exact mul_pos hwA humsδ
  have hsBlo_pos : 0 < sBlo := by rw [hsBlo]; exact mul_pos hwB hs₀mδ
  set rA : ℝ := (Real.sqrt (sAhi / sAlo)) ^ n with hrA
  set rB : ℝ := (Real.sqrt (sBhi / sBlo)) ^ n with hrB
  set ampH : ℝ := A₀ + A₁ * (u - s₀ + δ) with hampH
  set Kc : ℝ := ampH * Cpre * rA * C_L * rB with hKc
  have hrAnn : 0 ≤ rA := by rw [hrA]; positivity
  have hrBnn : 0 ≤ rB := by rw [hrB]; positivity
  have hampHnn : 0 ≤ ampH := by rw [hampH]; positivity
  have hKcnn : 0 ≤ Kc := by rw [hKc]; positivity
  refine ⟨fun z => Kc * (gaussDdim sAhi (0 - z) * gaussDdim sBhi (z - 0)), ?_,
    hmeas s₀ ⟨hs₀pos, hs₀u⟩, ?_, hcont s₀ ⟨hs₀pos, hs₀u⟩⟩
  · exact (gaussDdim_mul_integrable sAhi sBhi 0 0).const_mul Kc
  · have hmem : Set.Ioo (s₀ - δ) (s₀ + δ) ∈ 𝓝 s₀ :=
      isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    refine Filter.eventually_of_mem hmem (fun s hs => ?_)
    obtain ⟨hsl, hsr⟩ := hs
    refine ae_of_all _ (fun z => ?_)
    have hspos : 0 < s := by linarith
    have hτpos : 0 < u - s := by linarith
    have hsT : s ≤ T := by linarith
    -- widths in range (monotone in the linear argument since `wA, wB > 0`)
    have hsA_lo : sAlo ≤ wA * (u - s) := by
      rw [hsAlo]; exact mul_le_mul_of_nonneg_left (by linarith) hwA.le
    have hsA_hi : wA * (u - s) ≤ sAhi := by
      rw [hsAhi]; exact mul_le_mul_of_nonneg_left (by linarith) hwA.le
    have hsB_lo : sBlo ≤ wB * s := by
      rw [hsBlo]; exact mul_le_mul_of_nonneg_left (by linarith) hwB.le
    have hsB_hi : wB * s ≤ sBhi := by
      rw [hsBhi]; exact mul_le_mul_of_nonneg_left (by linarith) hwB.le
    -- bound on the `A`-factor
    have hAbound : |A (u - s) 0 z| ≤ ampH * Cpre * (rA * gaussDdim sAhi (0 - z)) := by
      calc |A (u - s) 0 z|
          ≤ (A₀ + A₁ * (u - s)) * Cpre * gaussDdim (wA * (u - s)) (0 - z) :=
            hAdom (u - s) hτpos 0 z
        _ ≤ (A₀ + A₁ * (u - s)) * Cpre * (rA * gaussDdim sAhi (0 - z)) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) hCpre)
            rw [hrA]
            exact QIQTH.ContDomWindow.gaussDdim_window_le hsAlo_pos hsA_lo hsA_hi (0 - z)
        _ ≤ ampH * Cpre * (rA * gaussDdim sAhi (0 - z)) := by
            apply mul_le_mul_of_nonneg_right _
              (mul_nonneg hrAnn (QIQTH.ResidueBound.gaussDdim_nonneg _ _))
            apply mul_le_mul_of_nonneg_right _ hCpre
            rw [hampH]; nlinarith
    -- bound on the `B`-factor
    have hBbound : |B s z 0| ≤ C_L * (rB * gaussDdim sBhi (z - 0)) := by
      calc |B s z 0|
          ≤ C_L * gaussDdim (wB * s) (z - 0) := hBdom s hspos hsT z 0
        _ ≤ C_L * (rB * gaussDdim sBhi (z - 0)) := by
            apply mul_le_mul_of_nonneg_left _ hC_L
            rw [hrB]
            exact QIQTH.ContDomWindow.gaussDdim_window_le hsBlo_pos hsB_lo hsB_hi (z - 0)
    have hXnn : 0 ≤ ampH * Cpre * (rA * gaussDdim sAhi (0 - z)) :=
      mul_nonneg (mul_nonneg hampHnn hCpre)
        (mul_nonneg hrAnn (QIQTH.ResidueBound.gaussDdim_nonneg _ _))
    calc ‖A (u - s) 0 z * B s z 0‖
        = |A (u - s) 0 z| * |B s z 0| := by rw [Real.norm_eq_abs, abs_mul]
      _ ≤ (ampH * Cpre * (rA * gaussDdim sAhi (0 - z))) * (C_L * (rB * gaussDdim sBhi (z - 0))) :=
          mul_le_mul hAbound hBbound (abs_nonneg _) hXnn
      _ = Kc * (gaussDdim sAhi (0 - z) * gaussDdim sBhi (z - 0)) := by rw [hKc]; ring

/-! ###############################################################################
    ### (2) — the COMPOSED width/witness-generic `hInnerCont` reduction.
    ############################################################################### -/

/-- **★★ `hInnerCont_of_dominations_generic` — THE WIDTH/WITNESS-GENERIC `hInnerCont` REDUCTION.**
    Composes `hContDom_of_gaussDom_gen` (this file) into the abstract dominated-continuity engine
    `InnerMeasFubini.innerIntegral_continuousOn_of_dominated`.  For abstract kernels `A`, `B`, ANY
    positive widths `wA`, `wB`, the interior-time continuity of the inner space-time pairing
    `s ↦ ∫ z, A (u−s) 0 z · B s z 0` on `Ioo 0 u` (∀ `u ∈ U ⊆ (·,T]`) is reduced ALL THE WAY to the
    four raw carries `{hAdom (A-slot width `wA`), hBdom (B-slot width `wB`), hmeas, hcont}`.  BOTH the
    opaque `ContinuousOn` and the per-interior-point dominated-continuity existential are removed.
    This is the metric-agnostic, width-agnostic CORE that `CurvedA1HContDom.curved_hInnerCont_of_
    dominations` (pinned `wA=3/2`, `wB=2`, `A := vanVleckGatedWitness`) is a specialization of.
    NOT `a₁ = R/6`. -/
theorem hInnerCont_of_dominations_generic
    (A B : ℝ → Point n → Point n → ℝ) (T : ℝ) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (wA wB : ℝ) (hwA : 0 < wA) (hwB : 0 < wB)
    (Cpre A₀ A₁ C_L : ℝ) (hCpre : 0 ≤ Cpre) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hC_L : 0 ≤ C_L)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |A τ p q| ≤ (A₀ + A₁ * τ) * Cpre * gaussDdim (wA * τ) (p - q))
    (hBdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
        |B s z y| ≤ C_L * gaussDdim (wB * s) (z - y))
    (hmeas : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
        AEStronglyMeasurable (fun z => A (u - s) 0 z * B s z 0) (volume : Measure (Point n)))
    (hcont : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
        ContinuousAt (fun s => A (u - s) 0 z * B s z 0) s₀) :
    ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, A (u - s) 0 z * B s z 0) (Set.Ioo 0 u) :=
  fun u hu =>
    QIQTH.InnerMeasFubini.innerIntegral_continuousOn_of_dominated
      (fun s z => A (u - s) 0 z * B s z 0) (Set.Ioo 0 u)
      (hContDom_of_gaussDom_gen A B u T wA wB (hUT u hu) hwA hwB Cpre A₀ A₁ C_L
        hCpre hA₀ hA₁ hC_L hAdom hBdom (hmeas u hu) (hcont u hu))

end QIQTH.CurvedA1HContDomGen

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1HContDomGen

#print axioms hContDom_of_gaussDom_gen
#print axioms hInnerCont_of_dominations_generic

end AxiomChecks
