/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# HT1a — the abstract null-triangle FTC / boundary-decomposition identity

This is **HT1a** of `THE_HTKK_PHYSICAL_PLAN.md`: the pure-calculus honest core of the classical
Rindler boost-charge = horizon-null-energy identity `K₀(R) = H_+(R) + N_+(R)`.

For scalar fields `A B : ℝ → ℝ → ℝ` on the null triangle `{(U,V) : 0 ≤ U ≤ V ≤ R}` obeying the
conservation law `∂_U A + ∂_V B = 0` (pointwise, `dA U V + dB U V = 0`), the flux-balance identity

    ∫₀ᴿ (A s s − B s s) ds  =  ∫₀ᴿ A 0 V dV  −  ∫₀ᴿ B U R dU

holds.  **Interpretation.**  The LHS is the flux through the hypotenuse (the `t=0` slice, `U=V=s`);
the first RHS term is the flux through the `U=0` edge (the future horizon `H⁺`); the second RHS term
is the flux through the `V=R` edge (the outer / null-infinity cutoff `N⁺`).  This is the pure-calculus
skeleton of `K₀(R) = H_+(R) + N_+(R)`.

**Proof strategy** (no divergence theorem, no PDE).  Two applications of the fundamental theorem of
calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`, once in each variable) plus a single
triangular Fubini swap on `0 ≤ U ≤ V ≤ R` (`MeasureTheory.integral_integral_swap` on the square
product measure with the diagonal-truncated integrand).  The conservation law `dA + dB = 0` collapses
the `A`-column integral to the negative of the `B`-column integral.  Axiom-free.

**Scope firewall.**  HT1a fixes the boost-charge ↔ null-energy STRUCTURE only.  It establishes NO
physics: the KG-stress instantiation (HT1b, giving `K₀ = H_+ + N_+` with the explicit outer flux
`N_+`) and the no-flux limit (HT1c) follow separately, and the modular coefficient `2π/ℏ` is a
Bisognano–Wichmann / KMS normalization (HT2) — not decided here.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.Compact

namespace QIQTH.HTkkPhysical

open MeasureTheory Set

/-- The diagonal-truncated integrand `if U < V then f U V else 0`, used to realise the two nested
interval integrals over the null triangle `0 ≤ U ≤ V ≤ R` as a single integral over the square
against a common product measure (so that Fubini applies). -/
private noncomputable def diagTrunc (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun U V => if U < V then f U V else 0

/-- **Triangular Fubini swap.**  For a jointly-continuous `dA`, the two iterated interval integrals
over the null triangle `{0 ≤ U ≤ V ≤ R}` coincide:

    ∫₀ᴿ (∫_U^R dA U V dV) dU  =  ∫₀ᴿ (∫₀^V dA U V dU) dV.

This is the one genuinely two-dimensional step of HT1a.  Both sides equal the integral of `dA` over
the triangle; the proof routes through the square product measure via a diagonal indicator and
`MeasureTheory.integral_integral_swap`. -/
private lemma triangle_swap (R : ℝ) (hR : 0 ≤ R) (dA : ℝ → ℝ → ℝ)
    (hdAc : Continuous (Function.uncurry dA)) :
    (∫ U in (0:ℝ)..R, ∫ V in U..R, dA U V)
      = ∫ V in (0:ℝ)..R, ∫ U in (0:ℝ)..V, dA U V := by
  classical
  set S : Set ℝ := Ioc (0:ℝ) R with hS
  have hSmeas : MeasurableSet S := measurableSet_Ioc
  -- each factor of the product measure is finite
  haveI hfin : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, hS, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  -- measurability of the uncurried diagonal-truncated integrand
  have hFmeas : Measurable (Function.uncurry (diagTrunc dA)) := by
    have hEq : Function.uncurry (diagTrunc dA)
        = fun p : ℝ × ℝ => if p.1 < p.2 then Function.uncurry dA p else 0 := by
      funext p; rfl
    rw [hEq]
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      hdAc.measurable measurable_const
  -- a uniform bound for `‖dA‖` on the compact square, giving integrability
  obtain ⟨p₀, -, hp₀max⟩ :=
    (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
      (⟨(0, 0), ⟨⟨le_refl 0, hR⟩, ⟨le_refl 0, hR⟩⟩⟩ :
        (Icc (0:ℝ) R ×ˢ Icc (0:ℝ) R).Nonempty)
      hdAc.norm.continuousOn
  set M : ℝ := ‖Function.uncurry dA p₀‖ with hM
  have hMnonneg : 0 ≤ M := norm_nonneg _
  have hFint : Integrable (Function.uncurry (diagTrunc dA))
      ((volume.restrict S).prod (volume.restrict S)) := by
    refine ⟨hFmeas.aestronglyMeasurable, ?_⟩
    refine HasFiniteIntegral.of_bounded (C := M) ?_
    rw [Measure.prod_restrict]
    refine (ae_restrict_iff' (hSmeas.prod hSmeas)).mpr ?_
    filter_upwards with p hp
    have hpK : p ∈ Icc (0:ℝ) R ×ˢ Icc (0:ℝ) R :=
      ⟨Ioc_subset_Icc_self hp.1, Ioc_subset_Icc_self hp.2⟩
    have hb : ‖Function.uncurry dA p‖ ≤ M := hp₀max hpK
    show ‖Function.uncurry (diagTrunc dA) p‖ ≤ M
    by_cases h : p.1 < p.2
    · have hval : Function.uncurry (diagTrunc dA) p = Function.uncurry dA p := by
        simp [Function.uncurry, diagTrunc, h]
      rw [hval]; exact hb
    · have hval : Function.uncurry (diagTrunc dA) p = 0 := by
        simp [Function.uncurry, diagTrunc, h]
      rw [hval]; simpa using hMnonneg
  -- express the left side as a product integral
  have hLHS : (∫ U in (0:ℝ)..R, ∫ V in U..R, dA U V)
      = ∫ U in S, ∫ V in S, diagTrunc dA U V := by
    rw [intervalIntegral.integral_of_le hR, ← hS]
    refine setIntegral_congr_fun hSmeas ?_
    intro U hU
    have hU0 : (0:ℝ) ≤ U := le_of_lt hU.1
    have hUR : U ≤ R := hU.2
    have hind : (fun V => diagTrunc dA U V) = (Ioi U).indicator (fun V => dA U V) := by
      funext V; simp only [diagTrunc, Set.indicator_apply, Set.mem_Ioi]
    calc (∫ V in U..R, dA U V)
        = ∫ V in Ioc U R, dA U V := intervalIntegral.integral_of_le hUR
      _ = ∫ V in S ∩ Ioi U, dA U V := by rw [hS, Ioc_inter_Ioi, sup_eq_right.mpr hU0]
      _ = ∫ V in S, (Ioi U).indicator (fun V => dA U V) V :=
            (setIntegral_indicator measurableSet_Ioi).symm
      _ = ∫ V in S, diagTrunc dA U V := by rw [hind]
  -- express the right side as a product integral in the opposite order
  have hRHS : (∫ V in (0:ℝ)..R, ∫ U in (0:ℝ)..V, dA U V)
      = ∫ V in S, ∫ U in S, diagTrunc dA U V := by
    rw [intervalIntegral.integral_of_le hR, ← hS]
    refine setIntegral_congr_fun hSmeas ?_
    intro V hV
    have hV0 : (0:ℝ) ≤ V := le_of_lt hV.1
    have hVR : V ≤ R := hV.2
    have hind : (fun U => diagTrunc dA U V) = (Iio V).indicator (fun U => dA U V) := by
      funext U; simp only [diagTrunc, Set.indicator_apply, Set.mem_Iio]
    have hset : S ∩ Iio V = Ioo (0:ℝ) V := by
      rw [hS]; ext U
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
      constructor
      · rintro ⟨⟨h0, _⟩, hlt⟩; exact ⟨h0, hlt⟩
      · rintro ⟨h0, hlt⟩; exact ⟨⟨h0, le_of_lt (lt_of_lt_of_le hlt hVR)⟩, hlt⟩
    calc (∫ U in (0:ℝ)..V, dA U V)
        = ∫ U in Ioc (0:ℝ) V, dA U V := intervalIntegral.integral_of_le hV0
      _ = ∫ U in Ioo (0:ℝ) V, dA U V := integral_Ioc_eq_integral_Ioo
      _ = ∫ U in S ∩ Iio V, dA U V := by rw [hset]
      _ = ∫ U in S, (Iio V).indicator (fun U => dA U V) U :=
            (setIntegral_indicator measurableSet_Iio).symm
      _ = ∫ U in S, diagTrunc dA U V := by rw [hind]
  rw [hLHS, hRHS]
  exact integral_integral_swap hFint

/-- **HT1a — the abstract null-triangle FTC / boundary-decomposition identity.**

For scalar fields `A B : ℝ → ℝ → ℝ` on the null triangle `{(U,V) : 0 ≤ U ≤ V ≤ R}` whose columns
and rows are `C¹` (given as `HasDerivAt`-parametrised partials `dA = ∂_U A`, `dB = ∂_V B`, all
jointly continuous) and that satisfy the conservation law `∂_U A + ∂_V B = 0` pointwise, the
flux-balance identity holds:

    ∫₀ᴿ (A s s − B s s) ds  =  ∫₀ᴿ A 0 V dV  −  ∫₀ᴿ B U R dU.

The LHS is the flux through the hypotenuse (`t = 0` slice `U = V = s`); the first RHS term is the
flux through the `U = 0` edge (future horizon `H⁺`); the second is the flux through the `V = R` edge
(outer / null-infinity cutoff `N⁺`).  Pure calculus — no physics is discharged here. -/
theorem nullTriangle_ftc (R : ℝ) (hR : 0 ≤ R)
    (A B dA dB : ℝ → ℝ → ℝ)
    (hAc : Continuous (Function.uncurry A))
    (hBc : Continuous (Function.uncurry B))
    (hdAc : Continuous (Function.uncurry dA))
    (hdBc : Continuous (Function.uncurry dB))
    (hA : ∀ U V, HasDerivAt (fun u => A u V) (dA U V) U)
    (hB : ∀ U V, HasDerivAt (fun v => B U v) (dB U V) V)
    (hcons : ∀ U V, dA U V + dB U V = 0) :
    (∫ s in (0:ℝ)..R, (A s s - B s s))
      = (∫ V in (0:ℝ)..R, A 0 V) - (∫ U in (0:ℝ)..R, B U R) := by
  -- continuity of the various edge / diagonal traces (from joint continuity)
  have cAdiag : Continuous (fun s : ℝ => A s s) :=
    hAc.comp (continuous_id.prodMk continuous_id)
  have cA0V : Continuous (fun V : ℝ => A 0 V) :=
    hAc.comp (continuous_const.prodMk continuous_id)
  have cBdiag : Continuous (fun s : ℝ => B s s) :=
    hBc.comp (continuous_id.prodMk continuous_id)
  have cBUR : Continuous (fun U : ℝ => B U R) :=
    hBc.comp (continuous_id.prodMk continuous_const)
  -- interval integrability of the partials along each slice
  have hdAII : ∀ U, IntervalIntegrable (fun V => dA U V) volume U R := fun U =>
    (hdAc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hdBII : ∀ U, IntervalIntegrable (fun V => dB U V) volume U R := fun U =>
    (hdBc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  -- FTC in `V` for the `B`-column, and in `U` for the `A`-row
  have hIB : ∀ U, (∫ V in U..R, dB U V) = B U R - B U U := fun U =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hB U v) (hdBII U)
  have hIA : ∀ V, (∫ U in (0:ℝ)..V, dA U V) = A V V - A 0 V := by
    intro V
    have hint : IntervalIntegrable (fun U => dA U V) volume 0 V :=
      (hdAc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hA u V) hint
  -- conservation collapses the `A`-column to `-` the `B`-column
  have hAneg : ∀ U, (∫ V in U..R, dA U V) = -(∫ V in U..R, dB U V) := by
    intro U
    have hsum : (∫ V in U..R, dA U V) + (∫ V in U..R, dB U V) = 0 := by
      rw [← intervalIntegral.integral_add (hdAII U) (hdBII U)]
      have hz : (fun V => dA U V + dB U V) = fun _ => (0:ℝ) := by
        funext V; exact hcons U V
      rw [hz]; simp
    linarith [hsum]
  -- the triangular Fubini swap
  have hswap := triangle_swap R hR dA hdAc
  -- integrability of the four boundary integrands
  have hInt_AVV : IntervalIntegrable (fun V => A V V) volume 0 R := cAdiag.intervalIntegrable _ _
  have hInt_A0V : IntervalIntegrable (fun V => A 0 V) volume 0 R := cA0V.intervalIntegrable _ _
  have hInt_BUR : IntervalIntegrable (fun U => B U R) volume 0 R := cBUR.intervalIntegrable _ _
  have hInt_BUU : IntervalIntegrable (fun U => B U U) volume 0 R := cBdiag.intervalIntegrable _ _
  -- the swapped `A`-integral, evaluated two ways
  have e1 : (∫ U in (0:ℝ)..R, ∫ V in U..R, dA U V)
      = (∫ V in (0:ℝ)..R, A V V) - (∫ V in (0:ℝ)..R, A 0 V) := by
    rw [hswap]; simp_rw [hIA]
    rw [intervalIntegral.integral_sub hInt_AVV hInt_A0V]
  have e2 : (∫ U in (0:ℝ)..R, ∫ V in U..R, dA U V)
      = -((∫ U in (0:ℝ)..R, B U R) - (∫ U in (0:ℝ)..R, B U U)) := by
    simp_rw [hAneg]
    rw [intervalIntegral.integral_neg]
    simp_rw [hIB]
    rw [intervalIntegral.integral_sub hInt_BUR hInt_BUU]
  have key : (∫ V in (0:ℝ)..R, A V V) - (∫ V in (0:ℝ)..R, A 0 V)
      = -((∫ U in (0:ℝ)..R, B U R) - (∫ U in (0:ℝ)..R, B U U)) := by
    rw [← e1, e2]
  -- finish: split the LHS and rearrange
  rw [intervalIntegral.integral_sub hInt_AVV hInt_BUU]
  linarith [key]

end QIQTH.HTkkPhysical
