/-
  MixedGradientSlice — J4-785: the x-UNIFORM MIXED gradient per-slice bound — discharging the two
  asymmetric gradient inner bounds (`hInner1i`/`hInner1j`) of `MixedSliverAssembly`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is ONE brick
  of the `a₁ = R/6` heat-kernel campaign — the mixed (`i ≠ j`) analogue of the diagonal x-uniform
  gradient slice `XUniformSliverFull.hInner1_xuniform`, feeding the two carried `hInner1i`/`hInner1j`
  hypotheses of `MixedSliverAssembly.witness_sliver2_assembly_mixed`.

  ## THE OBSERVATION THIS MAKES PRECISE (step-3 of the ledger).
  The diagonal x-uniform gradient slice bounds `|∫ z, sTerm1 Y P A1 (u−s) z · F s z x|`, where
    `sTerm1 Y P A1 τ z = 2·G_τ(Y z)·(−⟨Y z,P z⟩/2τ)·A₁ τ z`.
  Its proof is ALREADY GENERIC in the two directions: the DISPLACEMENT field `Y` (which enters BOTH the
  Gaussian argument `G_τ(Y z)` and the FIRST slot of the pairing `⟨Y z,P z⟩`) and the AMPLITUDE-DERIVATIVE
  direction `P` (near `unitVec i`, the SECOND slot) are INDEPENDENT parameters — the pairing is bounded by
  Cauchy–Schwarz (`abs_inner_le`), then `‖Y z‖` and `‖P z‖` are dominated SEPARATELY (`normY_le`/`normP_le`).
  NOTHING in the proof exploits the displacement direction and the amplitude-derivative direction being the
  SAME index.  So the mixed ASYMMETRIC pairing (`mTerm1 V Pj (∂ᵢA)`: displacement `V`, amplitude-direction
  `Pj` near `unitVec j`, amplitude `∂ᵢA`) is a pure INSTANTIATION with `Y := V`, `P := Pj`, `i := j`.

  The SOLE structural gap between the diagonal and mixed gradient terms is the leading factor `2`:
    `mTerm1 V P A1 τ z = G_τ(V z)·(−⟨V z,P z⟩/2τ)·A₁ τ z`   (NO factor `2`)
    `sTerm1 V P A1 τ z = 2·G_τ(V z)·(−⟨V z,P z⟩/2τ)·A₁ τ z` (factor `2`)
  i.e. `sTerm1 = 2·mTerm1` DEFINITIONALLY (same displacement in both slots after renaming `Y := V`).  So
  the mixed bound is the diagonal bound scaled by `1/2`.

  ## WHAT LANDS (this file, ns `QIQTH.MixedGradientSlice`).
    • `mTerm1RateConst`         — the explicit, x-FREE per-slice constant = `(1/2)·(diagonal constant)`.
    • `mTerm1RateConst_nonneg`  — its nonnegativity (feeds the `hC₁` hypothesis of the mixed assembly).
    • `mTerm1_slice_xuniform`   — ★★★ the x-uniform mixed gradient per-slice bound at a GENERAL field
        point `x`, discharging BOTH `hInner1i` (via `P := Pj`, `A1 := ∂ᵢA`, index `j`) and `hInner1j`
        (via `P := Pi`, `A1 := ∂ⱼA`, index `i`) of `witness_sliver2_assembly_mixed` — ONE lemma, two
        instantiations, exactly as `mTerm1`'s docstring predicts.

  ## WHAT THIS DOES NOT DO (honest scope).
  This closes ONLY the two gradient inner bounds of the four-term mixed assembly.  The mixed HESSIAN inner
  bound (`hInner0`) still needs the mixed E1 Gaussian-replacement port (owned separately); the mass inner
  bound (`hInner2`) reuses the diagonal `sTerm2` verbatim (`XUniformSliverFull.hInner2_xuniform`).

  Every hypothesis is satisfiable and non-vacuous (the model `V = −id`, `P = eⱼ`, `A₁` bounded, `F` a
  width-`2s` Gaussian bump satisfies all — the SAME model as the diagonal brick, with the amplitude-
  direction taken along a DIFFERENT axis than the displacement to exhibit the genuine asymmetry), and none
  equals the conclusion.  No `sorry`, no new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedSliverAssembly
import QIQTH.XUniformSliverFull

open MeasureTheory Finset
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.ResidueBound QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.XUniformSliver QIQTH.XUniformSliverFull
open QIQTH.MixedSliverAssembly
open scoped Interval Topology

namespace QIQTH.MixedGradientSlice

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ★ The explicit, x-free per-slice mixed-gradient constant.
    ############################################################################### -/

/-- **THE EXPLICIT, x-FREE PER-SLICE MIXED-GRADIENT CONSTANT.**  Exactly `(1/2)·(diagonal constant)` of
    `XUniformSliverFull.hInner1_xuniform` — the factor `1/2` accounts for `mTerm1 = (1/2)·sTerm1`.  It does
    NOT mention the field point, so it serves as the SINGLE x-uniform constant of the mixed gradient
    per-slice bound (for EITHER asymmetric pairing). -/
noncomputable def mTerm1RateConst (n : ℕ) (M₁ C_L a τ₀ C_W C_P : ℝ) : ℝ :=
  (1 / 2) * ((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
    * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
      + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
      + ((n : ℝ) * C_W * C_P)
        * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀)))

/-- The per-slice mixed-gradient constant is nonnegative (feeds the `hC₁`/`hC₁'` hypotheses of the mixed
    assembly). -/
theorem mTerm1RateConst_nonneg (M₁ C_L a τ₀ C_W C_P : ℝ)
    (hM₁ : 0 ≤ M₁) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hτ₀ : 0 ≤ τ₀) :
    0 ≤ mTerm1RateConst n M₁ C_L a τ₀ C_W C_P := by
  unfold mTerm1RateConst
  have hga : (0 : ℝ) ≤ gaussDdim a (0 : Point n) := gaussDdim_nonneg' a 0
  positivity

/-! ###############################################################################
    ★★★ The x-uniform mixed gradient per-slice bound.
    ############################################################################### -/

/-- **★★★ J4-785 — THE x-UNIFORM MIXED GRADIENT PER-SLICE BOUND.**  `MixedSliverAssembly.mTerm1` at a
    GENERAL field point `x`, with the explicit x-free constant `mTerm1RateConst` = `(1/2)·(diagonal
    constant)`.  Proved by reducing to the diagonal `XUniformSliverFull.hInner1_xuniform` on the
    definitional identity `mTerm1 V P A1 = (1/2)·sTerm1 V P A1` (both share the displacement `V` in the
    Gaussian argument and the first pairing slot; the diagonal proof is generic in the amplitude-direction
    `P` near `unitVec i`).  Discharges BOTH gradient inner bounds of `witness_sliver2_assembly_mixed`:
      • `hInner1i` — instantiate `P := Pj`, `A1 := ∂ᵢA`, index `i := j`;
      • `hInner1j` — instantiate `P := Pi`, `A1 := ∂ⱼA`, index `i := i`.
    NOT `a₁ = R/6`. -/
theorem mTerm1_slice_xuniform
    (V P : Point n → Point n) (A1 : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (i : Fin n) (M₁ C_L T a u ε τ₀ C_W C_P : ℝ) (x : Point n)
    (hM₁ : 0 ≤ M₁) (hC_L : 0 ≤ C_L) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P)
    (ha : 0 < a) (hau : a ≤ u) (huT : u ≤ T) (hε0 : 0 ≤ ε) (hεa : ε < a / 2) (hετ₀ : ε ≤ τ₀)
    (hco : ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (V z))
    (hVdisp : ∀ z : Point n, ‖V z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3 : ∀ z : Point n, ‖P z - unitVec i‖ ≤ C_P * ‖z‖)
    (hA1bdd : ∀ τ, ∀ z : Point n, |A1 τ z| ≤ M₁)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y)) :
    ∀ s ∈ Set.Ioo (u - ε) u,
      |∫ z, mTerm1 V P A1 (u - s) z * F s z x|
        ≤ mTerm1RateConst n M₁ C_L a τ₀ C_W C_P * (u - s) ^ (-(1 : ℝ) / 2) := by
  intro s hs
  -- the diagonal x-uniform gradient slice (generic in displacement `V` and amplitude-direction `P`).
  have hbig := hInner1_xuniform V P A1 F i M₁ C_L T a u ε τ₀ C_W C_P x
    hM₁ hC_L hC_W hC_P ha hau huT hε0 hεa hετ₀ hco hVdisp hJ3 hA1bdd hFdom s hs
  -- the definitional scaling `mTerm1 · F = (1/2)·(sTerm1 · F)`.
  have hpt : ∀ z : Point n, mTerm1 V P A1 (u - s) z * F s z x
      = (1 / 2) * (sTerm1 V P A1 (u - s) z * F s z x) := by
    intro z; unfold mTerm1 sTerm1; ring
  have hint : (∫ z, mTerm1 V P A1 (u - s) z * F s z x)
      = (1 / 2) * ∫ z, sTerm1 V P A1 (u - s) z * F s z x := by
    rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul]
  rw [hint, abs_mul, show |(1 : ℝ) / 2| = 1 / 2 from by norm_num]
  calc (1 / 2) * |∫ z, sTerm1 V P A1 (u - s) z * F s z x|
      ≤ (1 / 2) * (((Real.sqrt 2) ^ n * M₁ * (C_L * gaussDdim a (0 : Point n))
            * ((n : ℝ) * ((n : ℝ) * (3 / 2) * Real.sqrt 2)
              + ((n : ℝ) * (C_W + C_P)) * ((4 * (n : ℝ)) * Real.sqrt τ₀)
              + ((n : ℝ) * C_W * C_P)
                * ((n : ℝ) * (64 * Real.sqrt 2 + 1) * (Real.sqrt 2) ^ 3 * τ₀)))
          * (u - s) ^ (-(1 : ℝ) / 2)) := mul_le_mul_of_nonneg_left hbig (by norm_num)
    _ = mTerm1RateConst n M₁ C_L a τ₀ C_W C_P * (u - s) ^ (-(1 : ℝ) / 2) := by
        unfold mTerm1RateConst; ring

end QIQTH.MixedGradientSlice

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedGradientSlice
#print axioms mTerm1_slice_xuniform
end AxiomChecks
