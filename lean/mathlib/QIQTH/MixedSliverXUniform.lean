/-
  MixedSliverXUniform — J4-787: the CLOSED x-uniform MIXED sliver rate theorem.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is the pure
  WIRING step that combines the four already-proven mixed inner-bound discharges
  (J4-784→786) through the four-term mixed assembly `MixedSliverAssembly.witness_sliver2_assembly_mixed`
  into a single closed `√ε` sliver rate, with NO carried inner-bound hypotheses (the four `hInner*`
  slots are discharged INTERNALLY from the geometric/amplitude/domination data).  It is the mixed
  (`i ≠ j`) twin of the diagonal `XUniformSliverFull.witness_sliver2_xuniform`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE FOUR INTERNAL DISCHARGES (mirror of the diagonal three).

    • `hInner0` (mixed Hessian, chart Gaussian) — `MixedGaussReplaceSlice.mixedHessianSlice_chart_bound`
      (J4-786), constant `C₀ = sliverRateConst + (tE2RateConst + L·n)` at `C_F = C_L·gaussDdim a 0`.
    • `hInner1i`/`hInner1j` (the TWO mixed gradients) — `MixedGradientSlice.mTerm1_slice_xuniform`
      (J4-785), ONE lemma at the two asymmetric pairings `(Pj,∂ᵢA)` / `(Pi,∂ⱼA)`, constants
      `C₁ = mTerm1RateConst n M₁i …`, `C₁' = mTerm1RateConst n M₁j …`.
    • `hInner2` (mass) — `XUniformSliverFull.hInner2_xuniform` (the diagonal `sTerm2` reused verbatim,
      J4-784), constant `C₂ = (√2)ⁿ·M₂·C_L·gaussDdim a 0`.

  The per-slice `hgcap` (uniform field cap `|F s z x| ≤ C_L·gaussDdim a 0`) that the Hessian slice needs
  is derived INTERNALLY from the Gaussian-domination carry `hFdom` via `XUniformSliver.F_le_const_xuniform`
  (the interval `s ∈ Ioo (u−ε) u` sits inside `a/2 < s ≤ T` because `ε < a/2 ≤ a ≤ u ≤ T`), exactly the
  route `hInner2_xuniform` uses.  The genuine carries are: the geometric jet data
  (`hco`/`hVdisp`/`hJ3i`/`hJ3j`/`hJ3Q`), the amplitude sup bounds, the Gaussian-domination `hFdom`, the
  Lipschitz/measurability bundle `hqLip`, the mixed normal form `hNormalForm`, and the per-slice
  integrabilities — the same class of carries the diagonal sliver theorem carries.

  Every hypothesis is satisfiable and non-vacuous (`F ≡ 0`, all amplitudes `≡ 0`, `ε = 0` gives both sides
  `0`; the width-2 Gaussian model with `V = −id`, `Pi = eᵢ`, `Pj = eⱼ`, `Q = 0` is a genuinely-nonzero
  witness), and none equals the conclusion.  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverAssembly
import QIQTH.MixedGaussReplaceSlice
import QIQTH.MixedGradientSlice

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.XUniformSliver QIQTH.XUniformSliverFull
open QIQTH.MixedSliverAssembly QIQTH.MixedGaussReplaceSlice QIQTH.MixedGradientSlice
open scoped Interval Topology

namespace QIQTH.MixedSliverXUniform

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-- **★★★ J4-787 — THE CLOSED x-UNIFORM MIXED SLIVER RATE.**  The mixed (`i ≠ j`) twin of
    `XUniformSliverFull.witness_sliver2_xuniform`: for the off-diagonal formal second-`x`-derivative
    kernel `D2H` in the FOUR-term mixed Leibniz–Gaussian normal form
    `D2H = mTerm0 + mTerm1(V,Pj,∂ᵢA) + mTerm1(V,Pi,∂ⱼA) + sTerm2(V,∂ᵢ∂ⱼA)`
    (`ChartJetHessianMixed.gaussComp_amp_pd_pd_mixed`), the terminal `√ε` sliver at EVERY field point `x`
    obeys `|∫ s in (u−ε)..u, ∫ z, D2H (u−s) z · F s z x| ≤ (C₀+C₁+C₁')·2√ε + C₂·ε` with the four
    constants FIXED (x-free).  The four `hInner*` inner bounds are discharged internally (J4-784→786).
    NOT `a₁ = R/6`. -/
theorem witness_sliver2_xuniform_mixed
    (D2H : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (V Pi Pj Q : Point n → Point n) (A0 A1i A1j A2 : ℝ → Point n → ℝ)
    (i j : Fin n) (hij : i ≠ j)
    (L M₀ M₁i M₁j M₂ C_L T a τ₀ C_W C_P C_Q : ℝ)
    (hL : 0 ≤ L) (hM₀ : 0 ≤ M₀) (hM₁i : 0 ≤ M₁i) (hM₁j : 0 ≤ M₁j) (hM₂ : 0 ≤ M₂) (hC_L : 0 ≤ C_L)
    (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (u ε : ℝ) (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεu : ε ≤ u)
    (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (V z))
    (hVdisp : ∀ z : Point n, ‖V z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3i : ∀ z : Point n, ‖Pi z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3j : ∀ z : Point n, ‖Pj z - unitVec j‖ ≤ C_P * ‖z‖)
    (hJ3Q : ∀ z : Point n, ‖Q z‖ ≤ C_Q)
    (hA0bdd : ∀ τ, ∀ z : Point n, |A0 τ z| ≤ M₀)
    (hA1ibdd : ∀ τ, ∀ z : Point n, |A1i τ z| ≤ M₁i)
    (hA1jbdd : ∀ τ, ∀ z : Point n, |A1j τ z| ≤ M₁j)
    (hA2bdd : ∀ τ, ∀ z : Point n, |A2 τ z| ≤ M₂)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (hNormalForm : ∀ τ ∈ Set.Ioo (0 : ℝ) τ₀, ∀ z : Point n,
        D2H τ z = mTerm0 V Pi Pj Q A0 τ z + mTerm1 V Pj A1i τ z
          + mTerm1 V Pi A1j τ z + sTerm2 V A2 τ z)
    (hqLip : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        (∀ z w : Point n, |A0 (u - s) z * F s z x - A0 (u - s) w * F s w x| ≤ L * dist z w)
        ∧ AEStronglyMeasurable (fun z : Point n => A0 (u - s) z * F s z x) volume
        ∧ ∃ M, ∀ z : Point n, |A0 (u - s) z * F s z x| ≤ M)
    (hIntE1 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => (gaussDdim (u - s) (V z) - gaussDdim (u - s) z)
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * F s z x)) volume)
    (hIntPlain : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * F s z x)) volume)
    (hIntRem : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => gaussDdim (u - s) z
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s))
                - (z i * z j) / (4 * (u - s) ^ 2))
            * (A0 (u - s) z * F s z x)) volume)
    (hInt0 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => mTerm0 V Pi Pj Q A0 (u - s) z * F s z x) volume)
    (hInt1i : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => mTerm1 V Pj A1i (u - s) z * F s z x) volume)
    (hInt1j : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => mTerm1 V Pi A1j (u - s) z * F s z x) volume)
    (hInt2 : ∀ x : Point n, ∀ s ∈ Set.Ioo (u - ε) u,
        Integrable (fun z => sTerm2 V A2 (u - s) z * F s z x) volume) :
    ∀ x : Point n,
      |∫ s in (u - ε)..u, ∫ z, D2H (u - s) z * F s z x|
        ≤ ((sliverRateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀
              + (tE2RateConst n M₀ (C_L * gaussDdim a (0 : Point n)) C_W C_P C_Q τ₀ + L * (n : ℝ)))
            + mTerm1RateConst n M₁i C_L a τ₀ C_W C_P
            + mTerm1RateConst n M₁j C_L a τ₀ C_W C_P) * (2 * Real.sqrt ε)
          + ((Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n)) * ε := by
  have hga : (0 : ℝ) ≤ gaussDdim a (0 : Point n) := gaussDdim_nonneg' a 0
  have hτ₀0 : (0 : ℝ) ≤ τ₀ := le_trans hε0 hετ₀
  set C_F : ℝ := C_L * gaussDdim a (0 : Point n) with hCF_def
  have hCF : (0 : ℝ) ≤ C_F := by rw [hCF_def]; positivity
  -- the four x-free constants.
  set C₀ : ℝ := sliverRateConst n M₀ C_F C_W C_P C_Q τ₀
      + (tE2RateConst n M₀ C_F C_W C_P C_Q τ₀ + L * (n : ℝ)) with hC₀_def
  set C₁ : ℝ := mTerm1RateConst n M₁i C_L a τ₀ C_W C_P with hC₁_def
  set C₁' : ℝ := mTerm1RateConst n M₁j C_L a τ₀ C_W C_P with hC₁'_def
  set C₂ : ℝ := (Real.sqrt 2) ^ n * M₂ * C_L * gaussDdim a (0 : Point n) with hC₂_def
  have hC₀ : (0 : ℝ) ≤ C₀ := by
    rw [hC₀_def]
    exact add_nonneg (sliverRateConst_nonneg _ _ _ _ _ _ hM₀ hCF hC_W hC_P hC_Q)
      (add_nonneg (tE2RateConst_nonneg _ _ _ _ _ _ hM₀ hCF hC_W hC_P hC_Q)
        (mul_nonneg hL (Nat.cast_nonneg _)))
  have hC₁ : (0 : ℝ) ≤ C₁ := by
    rw [hC₁_def]; exact mTerm1RateConst_nonneg _ _ _ _ _ _ hM₁i hC_L hC_W hC_P hτ₀0
  have hC₁' : (0 : ℝ) ≤ C₁' := by
    rw [hC₁'_def]; exact mTerm1RateConst_nonneg _ _ _ _ _ _ hM₁j hC_L hC_W hC_P hτ₀0
  have hC₂ : (0 : ℝ) ≤ C₂ := by
    rw [hC₂_def]; exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hM₂) hC_L) hga
  -- `a/2 < s ≤ T` on the sliver interval, for the uniform field cap.
  have hlo : a / 2 < u - ε := by linarith
  intro x
  -- the uniform field cap on the sliver interval (from `hFdom`).
  have hgcap : ∀ s ∈ Set.Ioo (u - ε) u, ∀ z : Point n, |F s z x| ≤ C_F := by
    intro s hs z
    have hsa2 : a / 2 ≤ s := le_of_lt (lt_trans hlo hs.1)
    have hsT : s ≤ T := le_of_lt (lt_of_lt_of_le hs.2 huT)
    exact F_le_const_xuniform F C_L T a hC_L hFdom ha s hsa2 hsT x z
  -- ── hInner0: the mixed Hessian chart-Gaussian slice, converted to the `mTerm0` shape.
  have hchart := mixedHessianSlice_chart_bound V Pi Pj Q A0 (fun s z => F s z x) i j hij
    L M₀ C_F u ε τ₀ C_W C_P C_Q hL hM₀ hCF hC_W hC_P hC_Q hετ₀
    hco hVdisp hJ3i hJ3j hJ3Q hA0bdd hgcap (fun s hs => hqLip x s hs)
    (fun s hs => hIntE1 x s hs) (fun s hs => hIntPlain x s hs) (fun s hs => hIntRem x s hs)
  have hI0 : ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, mTerm0 V Pi Pj Q A0 (u - s) z * (fun s z (_ : Point n) => F s z x) s z 0|
        ≤ C₀ * (u - s) ^ (-(1 : ℝ) / 2) := by
    intro s hs
    have heq : (∫ z, mTerm0 V Pi Pj Q A0 (u - s) z * (fun s z (_ : Point n) => F s z x) s z 0)
        = ∫ z, gaussDdim (u - s) (V z)
            * ((∑ k, V z k * Pi z k) * (∑ k, V z k * Pj z k) / (4 * (u - s) ^ 2)
                - ((∑ k, Pi z k * Pj z k) + (∑ k, V z k * Q z k)) / (2 * (u - s)))
            * (A0 (u - s) z * (fun s z => F s z x) s z) := by
      refine integral_congr_ae (ae_of_all _ (fun z => ?_))
      simp only [mTerm0]; ring
    rw [heq]; exact hchart s hs
  -- ── hInner1i / hInner1j: the two mixed gradient slices (one lemma, two asymmetric pairings).
  have hI1i := mTerm1_slice_xuniform V Pj A1i F j M₁i C_L T a u ε τ₀ C_W C_P x
    hM₁i hC_L hC_W hC_P ha hau huT hε0 hεa hετ₀ hco hVdisp hJ3j hA1ibdd hFdom
  have hI1j := mTerm1_slice_xuniform V Pi A1j F i M₁j C_L T a u ε τ₀ C_W C_P x
    hM₁j hC_L hC_W hC_P ha hau huT hε0 hεa hετ₀ hco hVdisp hJ3i hA1jbdd hFdom
  -- ── hInner2: the mass slice (the diagonal `sTerm2` reused verbatim).
  have hI2 := hInner2_xuniform V A2 F M₂ C_L T a u ε x
    hM₂ hC_L ha hau huT hε0 hεa hco hA2bdd hFdom
  -- ── glue through the four-term mixed assembly.
  exact witness_sliver2_assembly_mixed D2H (fun s z _ => F s z x) V Pi Pj Q A0 A1i A1j A2
    C₀ C₁ C₁' C₂ τ₀ hC₀ hC₁ hC₁' hC₂ u ε hε0 hεu hετ₀ hNormalForm
    hI0 hI1i hI1j hI2 (hInt0 x) (hInt1i x) (hInt1j x) (hInt2 x)

end QIQTH.MixedSliverXUniform

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverXUniform
#print axioms witness_sliver2_xuniform_mixed
end AxiomChecks
