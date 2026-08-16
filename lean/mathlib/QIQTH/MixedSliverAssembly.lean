/-
  MixedSliverAssembly — J4-784: the FOUR-TERM off-diagonal (`∂ᵢ∂ⱼ`, `i ≠ j`) sliver assembly — the mixed
  analogue of `SliverAssembly.witness_sliver2_assembly`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is ONE
  combinatorial brick of the `a₁ = R/6` heat-kernel campaign — the outer-slice `√ε` gluing that turns
  FOUR per-slice inner bounds into the terminal mixed-Hessian sliver bound.

  ## THE OBSTRUCTION THIS CLOSES (scoped in J4-783 / `MixedTE2Slice`).
  The diagonal `witness_sliver2_assembly` is hard-wired to the THREE-term normal form
  `D2H = sTerm0 + sTerm1 + sTerm2` (Hessian + ONE gradient + mass).  The mixed normal form
  (`ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed`) is a FOUR-term form
    `∂ᵢ∂ⱼ(G∘V·A) = G·[Hessianᵢⱼ]·A + G·(−⟨V,Pj⟩/2τ)·∂ᵢA + G·(−⟨V,Pi⟩/2τ)·∂ⱼA + G·∂ᵢ∂ⱼA`
  — TWO DISTINCT gradient terms (no longer the merged `2·(…)·∂ᵢA` of the diagonal) plus mass.  This file
  builds the four-term outer assembly.

  ## WHAT THIS DELIVERS.
    • `mTerm0` — the mixed Hessian normal-form term `G_τ(V z)·(⟨V,Pi⟩⟨V,Pj⟩/4τ² − (⟨Pi,Pj⟩+⟨V,Q⟩)/2τ)·A₀`.
        The off-diagonal analogue of `sTerm0`: the Gaussian second-moment is the PRODUCT `⟨V,Pi⟩·⟨V,Pj⟩`
        of two DISTINCT first-moment factors (no `−1/2τ` diagonal piece), plus the cross-jet `⟨Pi,Pj⟩` and
        second-jet `⟨V,Q⟩` corrections.  Setting `Pi = Pj`, `i = j` recovers `sTerm0`.
    • `mTerm1` — the SINGLE mixed gradient normal-form term `G_τ(V z)·(−⟨V,P⟩/2τ)·A₁` (NO factor `2`,
        unlike `sTerm1`).  Both mixed gradient terms are ONE instantiation each of this single shape:
        gradient-`i` = `mTerm1 V Pj (∂ᵢA)`, gradient-`j` = `mTerm1 V Pi (∂ⱼA)` — the SAME machinery fed
        the two asymmetric (displacement-direction, amplitude-derivative-direction) pairings.  This is the
        step-3 observation of the task made precise.
    • The mass term is `sTerm2 V (∂ᵢ∂ⱼA)` — SYNTACTICALLY the diagonal mass term (`G·A₂`), so it is
        REUSED verbatim; the diagonal mass bound applies unchanged (step-4 observation).
    • `witness_sliver2_assembly_mixed` — ★★★ the four-term outer `√ε` sliver bound.  Given the mixed
        normal form `D2H = mTerm0 + mTerm1(Pj,∂ᵢA) + mTerm1(Pi,∂ⱼA) + sTerm2(∂ᵢ∂ⱼA)`, the FOUR carried
        per-slice inner bounds (Hessian `C₀·(u−s)^{−1/2}`, the two gradients `C₁·(u−s)^{−1/2}` and
        `C₁'·(u−s)^{−1/2}`, mass `C₂`), and the four base integrabilities, the terminal sliver obeys
          `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z 0| ≤ (C₀ + C₁ + C₁')·2√ε + C₂·ε`.
        Route: split the inner integral into the four concrete terms (algebra via `hNormalForm` +
        `integral_add` thrice), bound each by its carried rate, then the banked `sliver_rpow_sub` — the
        VERBATIM four-term extension of the diagonal three-term assembly.

  ## WHAT THIS DOES NOT DO (honest scope).
  The FOUR inner bounds are CARRIED hypotheses (exactly as the diagonal assembly carries its three).
  Discharging the mixed Hessian inner bound at the CHART Gaussian `G_τ(V z)` still needs the mixed E1
  Gaussian-replacement port `G_τ(V z)→G_τ(z)` (`MixedTE2Slice.mixedHessianSlice_plain_bound` is the plain
  `G_τ(z)` half only); the two gradient inner bounds need the x-uniform mixed gradient slice.  Those are
  downstream discharges; THIS file is the pure four-term combinatorial gluing.

  Every hypothesis is satisfiable and non-vacuous (`D2H ≡ 0`, `F ≡ 0`, `A0/A1i/A1j/A2 ≡ 0`,
  `C₀=C₁=C₁'=C₂=0`, `ε=0` satisfies all with both sides `0`; the width-2 Gaussian model with the mixed
  chart jets `Pi=eᵢ`, `Pj=eⱼ` gives a genuinely-nonzero witness), and none equals the conclusion.
  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.SliverAssembly

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound
open scoped Interval Topology

namespace QIQTH.MixedSliverAssembly

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    The concrete mixed normal-form terms (the FOUR-term off-diagonal Leibniz–Gaussian shape).
    ############################################################################### -/

/-- **`mTerm0`** — the mixed Hessian-weighted normal-form term:
    `G_τ(V z)·[⟨V z,Pi z⟩·⟨V z,Pj z⟩/4τ² − (⟨Pi z,Pj z⟩+⟨V z,Q z⟩)/2τ]·A₀ τ z`.
    The off-diagonal analogue of `sTerm0` (product `⟨V,Pi⟩·⟨V,Pj⟩` of two DISTINCT first-moment factors,
    with cross-jet `⟨Pi,Pj⟩` and second-jet `⟨V,Q⟩` corrections; setting `Pi = Pj` recovers `sTerm0`). -/
noncomputable def mTerm0 (V Pi Pj Q : Point n → Point n) (A0 : ℝ → Point n → ℝ)
    (τ : ℝ) (z : Point n) : ℝ :=
  gaussDdim τ (V z)
    * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * τ ^ 2)
        - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * τ))
    * A0 τ z

/-- **`mTerm1`** — the SINGLE mixed gradient-weighted normal-form term:
    `G_τ(V z)·(−⟨V z,P z⟩/2τ)·A₁ τ z`.  NO factor `2` (unlike `sTerm1`, whose two gradient contributions
    merged into `2·(…)`).  Both mixed gradient terms are ONE instantiation each of this shape:
    gradient-`i` = `mTerm1 V Pj (∂ᵢA)`, gradient-`j` = `mTerm1 V Pi (∂ⱼA)`. -/
noncomputable def mTerm1 (V P : Point n → Point n) (A1 : ℝ → Point n → ℝ)
    (τ : ℝ) (z : Point n) : ℝ :=
  gaussDdim τ (V z) * (-(∑ k, V z k * P z k) / (2 * τ)) * A1 τ z

/-! ###############################################################################
    ★★★ THE FOUR-TERM MIXED ASSEMBLY — the mixed formal-Hessian sliver `√ε` bound.
    ############################################################################### -/

/-- **★★★ J4-784 — THE FOUR-TERM MIXED SLIVER ASSEMBLY.**  The mixed (`i ≠ j`) analogue of
    `SliverAssembly.witness_sliver2_assembly`.  For the off-diagonal formal second-`x`-derivative of the
    concrete van-Vleck witness whose normal form is the FOUR-term
    `D2H = mTerm0 + mTerm1(V,Pj,∂ᵢA) + mTerm1(V,Pi,∂ⱼA) + sTerm2(V,∂ᵢ∂ⱼA)`
    (`ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed`), given
      • `hNormalForm` — the mixed Leibniz–Gaussian four-term identity on `Ioo 0 τ₀`;
      • `hInner0` — the mixed Hessian per-slice bound (`C₀·(u−s)^{−1/2}`);
      • `hInner1i`/`hInner1j` — the TWO gradient per-slice bounds (`C₁`/`C₁'·(u−s)^{−1/2}`), one per
        (displacement-direction, amplitude-derivative-direction) pairing — the same `mTerm1` shape;
      • `hInner2` — the mass per-slice bound (`C₂`, `O(1)`), on the REUSED diagonal `sTerm2`;
      • `hInt0`/`hInt1i`/`hInt1j`/`hInt2` — the four per-slice base integrabilities,
    the terminal mixed sliver obeys
      `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z 0| ≤ (C₀ + C₁ + C₁')·2√ε + C₂·ε`.
    Route: split the inner integral into the four concrete terms (algebra via `hNormalForm` +
    `integral_add` thrice), bound each by its carried rate, then the banked `sliver_rpow_sub` — the
    verbatim four-term extension of the diagonal three-term assembly.  NOT `a₁ = R/6`. -/
theorem witness_sliver2_assembly_mixed
    (D2H : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (V Pi Pj Q : Point n → Point n) (A0 A1i A1j A2 : ℝ → Point n → ℝ)
    (C₀ C₁ C₁' C₂ τ₀ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₁' : 0 ≤ C₁') (hC₂ : 0 ≤ C₂)
    (u ε : ℝ) (hε0 : 0 ≤ ε) (hεu : ε ≤ u) (hετ₀ : ε ≤ τ₀)
    (hNormalForm : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z : Point n,
        D2H τ z = mTerm0 V Pi Pj Q A0 τ z + mTerm1 V Pj A1i τ z
          + mTerm1 V Pi A1j τ z + sTerm2 V A2 τ z)
    (hInner0 : ∀ s ∈ Set.Ioo (u - ε) u,
        |∫ z, mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0| ≤ C₀ * (u - s) ^ (-(1 : ℝ) / 2))
    (hInner1i : ∀ s ∈ Set.Ioo (u - ε) u,
        |∫ z, mTerm1 V Pj A1i (u - s) z * F s z 0| ≤ C₁ * (u - s) ^ (-(1 : ℝ) / 2))
    (hInner1j : ∀ s ∈ Set.Ioo (u - ε) u,
        |∫ z, mTerm1 V Pi A1j (u - s) z * F s z 0| ≤ C₁' * (u - s) ^ (-(1 : ℝ) / 2))
    (hInner2 : ∀ s ∈ Set.Ioo (u - ε) u,
        |∫ z, sTerm2 V A2 (u - s) z * F s z 0| ≤ C₂)
    (hInt0 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0) volume)
    (hInt1i : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => mTerm1 V Pj A1i (u - s) z * F s z 0) volume)
    (hInt1j : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => mTerm1 V Pi A1j (u - s) z * F s z 0) volume)
    (hInt2 : ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm2 V A2 (u - s) z * F s z 0) volume) :
    |∫ s in (u - ε)..u, ∫ z, D2H (u - s) z * F s z 0|
      ≤ (C₀ + C₁ + C₁') * (2 * Real.sqrt ε) + C₂ * ε := by
  -- per-slice inner bound (rpow form): the four-term split + triangle inequality.
  have hpsl : ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, D2H (u - s) z * F s z 0|
        ≤ (C₀ + C₁ + C₁') * (u - s) ^ (-(1 : ℝ) / 2) + C₂ := by
    intro s hs
    have hτpos : 0 < u - s := by linarith [hs.2]
    have hττ₀ : u - s < τ₀ := by linarith [hs.1, hετ₀]
    have hτIoo : (u - s) ∈ Set.Ioo (0 : ℝ) τ₀ := ⟨hτpos, hττ₀⟩
    -- split the inner integral into the four concrete terms.
    have hpt : ∀ z, D2H (u - s) z * F s z 0
        = mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0
          + mTerm1 V Pj A1i (u - s) z * F s z 0
          + mTerm1 V Pi A1j (u - s) z * F s z 0
          + sTerm2 V A2 (u - s) z * F s z 0 := by
      intro z; rw [hNormalForm (u - s) hτIoo z]; ring
    have e1 : (∫ z, mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0
          + mTerm1 V Pj A1i (u - s) z * F s z 0)
        = (∫ z, mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0)
          + ∫ z, mTerm1 V Pj A1i (u - s) z * F s z 0 :=
      integral_add (hInt0 s hs) (hInt1i s hs)
    have e2 : (∫ z, (mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0
            + mTerm1 V Pj A1i (u - s) z * F s z 0)
          + mTerm1 V Pi A1j (u - s) z * F s z 0)
        = (∫ z, mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0
            + mTerm1 V Pj A1i (u - s) z * F s z 0)
          + ∫ z, mTerm1 V Pi A1j (u - s) z * F s z 0 :=
      integral_add ((hInt0 s hs).add (hInt1i s hs)) (hInt1j s hs)
    have e3 : (∫ z, ((mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0
              + mTerm1 V Pj A1i (u - s) z * F s z 0)
            + mTerm1 V Pi A1j (u - s) z * F s z 0)
          + sTerm2 V A2 (u - s) z * F s z 0)
        = (∫ z, (mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0
              + mTerm1 V Pj A1i (u - s) z * F s z 0)
            + mTerm1 V Pi A1j (u - s) z * F s z 0)
          + ∫ z, sTerm2 V A2 (u - s) z * F s z 0 :=
      integral_add (((hInt0 s hs).add (hInt1i s hs)).add (hInt1j s hs)) (hInt2 s hs)
    have hsplit : (∫ z, D2H (u - s) z * F s z 0)
        = (∫ z, mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0)
          + (∫ z, mTerm1 V Pj A1i (u - s) z * F s z 0)
          + (∫ z, mTerm1 V Pi A1j (u - s) z * F s z 0)
          + (∫ z, sTerm2 V A2 (u - s) z * F s z 0) := by
      rw [integral_congr_ae (ae_of_all _ hpt), e3, e2, e1]
    rw [hsplit]
    calc |(∫ z, mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0)
            + (∫ z, mTerm1 V Pj A1i (u - s) z * F s z 0)
            + (∫ z, mTerm1 V Pi A1j (u - s) z * F s z 0)
            + (∫ z, sTerm2 V A2 (u - s) z * F s z 0)|
        ≤ |∫ z, mTerm0 V Pi Pj Q A0 (u - s) z * F s z 0|
            + |∫ z, mTerm1 V Pj A1i (u - s) z * F s z 0|
            + |∫ z, mTerm1 V Pi A1j (u - s) z * F s z 0|
            + |∫ z, sTerm2 V A2 (u - s) z * F s z 0| :=
          le_trans (abs_add_le _ _)
            (add_le_add (le_trans (abs_add_le _ _)
              (add_le_add (abs_add_le _ _) (le_refl _))) (le_refl _))
      _ ≤ C₀ * (u - s) ^ (-(1 : ℝ) / 2) + C₁ * (u - s) ^ (-(1 : ℝ) / 2)
            + C₁' * (u - s) ^ (-(1 : ℝ) / 2) + C₂ :=
          add_le_add (add_le_add (add_le_add (hInner0 s hs) (hInner1i s hs)) (hInner1j s hs))
            (hInner2 s hs)
      _ = (C₀ + C₁ + C₁') * (u - s) ^ (-(1 : ℝ) / 2) + C₂ := by ring
  -- assemble the outer sliver.
  rw [← Real.norm_eq_abs]
  calc ‖∫ s in (u - ε)..u, ∫ z, D2H (u - s) z * F s z 0‖
      ≤ ∫ s in (u - ε)..u, ((C₀ + C₁ + C₁') * (u - s) ^ (-(1 : ℝ) / 2) + C₂) := by
        refine intervalIntegral.norm_integral_le_of_norm_le (by linarith) ?_
          (((rpow_sub_intervalIntegrable u ε hε0).const_mul _).add intervalIntegrable_const)
        filter_upwards [ae_ne_point u] with s hsu hsmem
        have hs_mem : s ∈ Set.Ioo (u - ε) u := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hsu⟩
        rw [Real.norm_eq_abs]; exact hpsl s hs_mem
    _ = (C₀ + C₁ + C₁') * (2 * Real.sqrt ε) + C₂ * ε := by
        rw [intervalIntegral.integral_add ((rpow_sub_intervalIntegrable u ε hε0).const_mul _)
            intervalIntegrable_const, intervalIntegral.integral_const_mul, sliver_rpow_sub u ε hε0,
            intervalIntegral.integral_const, smul_eq_mul, show u - (u - ε) = ε from by ring]
        ring

end QIQTH.MixedSliverAssembly

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverAssembly
#print axioms witness_sliver2_assembly_mixed
end AxiomChecks
