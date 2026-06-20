/-
# The KMS correlation on the strip — furnishing the strip-uniqueness hypotheses

This bridges the entire bounded correlation `corrC` (built in `StandardSubspaceModularFlow`) to the
strip-uniqueness machinery (`StripUniqueness`).  It establishes the two analytic hypotheses that
`kms_correlation_boundary_determined` consumes — `DiffContOnCl` on the open KMS strip and a uniform bound
on the strip — *concretely for `corrC`*, so the abstract uniqueness lemma can finally be applied to a
genuine candidate modular flow.  This is the structural core of the RvD Theorem 3.8 discharge of `hUniq`:
once two flows' correlations are known to be entire + strip-bounded and to agree on both edges, they
coincide on the strip, hence (by density of the entire vectors) the flows coincide.

All results axiom-free (standard three only).
-/
import QIQTH.StandardSubspaceModularFlow
import QIQTH.StripUniqueness

namespace QIQTH.StandardSubspaceModular

open MeasureTheory QIQTH

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The KMS correlation is bounded-holomorphic on the strip** (`DiffContOnCl`): `corrC ξ V n η` is entire
    (`differentiable_corrC`), hence in particular differentiable on the open KMS strip and continuous up to
    its closure.  The first of the two analytic hypotheses of `kms_correlation_boundary_determined`. -/
theorem diffContOnCl_corrC {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η ξ : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) :
    DiffContOnCl ℂ (corrC ξ V n η) StripUniqueness.kmsStripOpen :=
  (differentiable_corrC hn η ξ hcont hbd).diffContOnCl

/-- **Uniform bound of the KMS correlation on the open strip**: for `0 < Im z < 1`,
    `|corrC ξ V n η z| ≤ ‖ξ‖·e^{n}·‖η‖·√(π/n)`.  The Gaussian bound `corrC_norm_le` gives the factor
    `e^{n(Im z)²}`, and `(Im z)² < 1` on the open strip.  The second analytic hypothesis of
    `kms_correlation_boundary_determined`. -/
theorem corrC_bdd_strip {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η ξ : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) :
    ∀ z ∈ StripUniqueness.kmsStripOpen,
      ‖corrC ξ V n η z‖ ≤ ‖ξ‖ * (Real.exp n * ‖η‖ * Real.sqrt (Real.pi / n)) := by
  intro z hz
  simp only [StripUniqueness.kmsStripOpen, Set.mem_preimage, Set.mem_Ioo] at hz
  refine (corrC_norm_le hn η ξ hcont hbd z).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine Real.exp_le_exp.mpr ?_
  nlinarith [hz.1, hz.2, hn.le,
    mul_pos (by linarith [hz.2] : (0:ℝ) < 1 - z.im) (by linarith [hz.1] : (0:ℝ) < 1 + z.im)]

/-- **Strip-uniqueness comparison for two KMS correlations** — the structural core of the `hUniq` discharge.
    If two strongly-continuous contraction flows `V`, `V'` produce correlations `corrC ξ V n η` and
    `corrC ξ V' n η` that agree on the **real axis** and on the **KMS top edge** `t + i`, then the
    correlations coincide on the whole closed KMS strip.  This is `kms_correlation_boundary_determined`
    applied to the now-furnished entirety (`diffContOnCl_corrC`) and strip bound (`corrC_bdd_strip`).
    With the density of the entire vectors (`entireVec_tendsto`) this upgrades to `V_t = V'_t`. -/
theorem corrC_eqOn_strip_of_boundary_eq {V V' : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η ξ : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hcont' : Continuous (fun t => V' t η)) (hbd' : ∀ t, ‖V' t η‖ ≤ ‖η‖)
    (hreal : ∀ t : ℝ, corrC ξ V n η (t : ℂ) = corrC ξ V' n η (t : ℂ))
    (htop : ∀ t : ℝ, corrC ξ V n η ((t : ℂ) + Complex.I) = corrC ξ V' n η ((t : ℂ) + Complex.I)) :
    Set.EqOn (corrC ξ V n η) (corrC ξ V' n η) StripUniqueness.kmsStrip :=
  StripUniqueness.kms_correlation_boundary_determined
    (diffContOnCl_corrC hn η ξ hcont hbd) (diffContOnCl_corrC hn η ξ hcont' hbd')
    (corrC_bdd_strip hn η ξ hcont hbd) (corrC_bdd_strip hn η ξ hcont' hbd') hreal htop

/-- **Constancy of `g` ⟹ the orbit's matrix element is `t`-independent** (RvD Theorem 3.8, step 6b).
    If the KMS correlation `g = corrC w V n η` is constant on the closed KMS strip (the conclusion of
    "real on both edges ⟹ constant"), then evaluating at the real axis `t` vs the origin `0` gives
    `⟨w, V_t(gaussSmear)⟩ = ⟨w, gaussSmear⟩` for every real `t` — using `g(0) = ⟨w, η_n⟩` (`gaussSmearC_zero`).
    Comparing this for `V` and for the modular flow `Δ^{it}` (both yield `⟨w, gaussSmear⟩`) forces
    `⟨w, V_t(gaussSmear)⟩ = ⟨w, Δ^{it}(gaussSmear)⟩`; totality of `w` + density then give `V_t = Δ^{it}`. -/
theorem corrC_eq_at_real_of_const {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η w : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η)
    (hconst : ∀ z ∈ StripUniqueness.kmsStrip, corrC w V n η z = corrC w V n η 0) (t : ℝ) :
    innerSL ℂ w (V t (gaussSmear V n η)) = innerSL ℂ w (gaussSmear V n η) := by
  have hmem : (t : ℂ) ∈ StripUniqueness.kmsStrip := by
    simp only [StripUniqueness.kmsStrip, Set.mem_preimage, Complex.ofReal_im, Set.mem_Icc]
    exact ⟨le_rfl, zero_le_one⟩
  have h1 := hconst (t : ℂ) hmem
  rw [corrC_ofReal hn η w hcont hbd hgrp t, corrC, gaussSmearC_zero] at h1
  exact h1

/-- **Real on both edges ⟹ constant on the closed strip** (RvD Theorem 3.8, step 6a, completed to the
    closed KMS strip).  If `Im(corrC w V n η) = 0` on both boundary lines `Im z = 0` and `Im z = 1`, then
    `corrC w V n η` is constant on the *closed* strip `kmsStrip` (equal to its value at `0`).  `Im g = 0` on
    the edges forces (`eqConst_of_im_zero_strip`, via Phragmén–Lindelöf) `g` constant on the open strip;
    continuity of the entire `g` then propagates the constant to the closure `kmsStrip = closure kmsStripOpen`
    (`Set.EqOn.closure`).  Feeds `corrC_eq_at_real_of_const`. -/
theorem corrC_const_on_strip_of_edges {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η w : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (h0 : ∀ z : ℂ, z.im = 0 → (corrC w V n η z).im = 0)
    (h1 : ∀ z : ℂ, z.im = 1 → (corrC w V n η z).im = 0) :
    ∀ z ∈ StripUniqueness.kmsStrip, corrC w V n η z = corrC w V n η 0 := by
  obtain ⟨c, hc⟩ := StripUniqueness.eqConst_of_im_zero_strip
    (diffContOnCl_corrC hn η w hcont hbd) (corrC_bdd_strip hn η w hcont hbd) h0 h1
  have hclos : StripUniqueness.kmsStrip = closure StripUniqueness.kmsStripOpen := by
    rw [StripUniqueness.kmsStrip, StripUniqueness.kmsStripOpen, Complex.closure_preimage_im,
      closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hcl : ∀ z ∈ StripUniqueness.kmsStrip, corrC w V n η z = c := by
    rw [hclos]
    exact Set.EqOn.closure (fun z hz => hc z hz)
      (differentiable_corrC hn η w hcont hbd).continuous continuous_const
  have h0mem : (0 : ℂ) ∈ StripUniqueness.kmsStrip := by
    simp only [StripUniqueness.kmsStrip, Set.mem_preimage, Complex.zero_im, Set.mem_Icc]
    exact ⟨le_rfl, zero_le_one⟩
  intro z hz
  rw [hcl z hz, hcl 0 h0mem]

/-- **Edge-reality ⟹ the orbit matrix element is `t`-independent** (RvD Theorem 3.8, the full step-6
    closeout chain).  If the KMS correlation `g = corrC w V n η` is real on *both* strip edges, then
    `⟨w, V_t(gaussSmear)⟩ = ⟨w, gaussSmear⟩` for every real `t`.  Just the composition
    `corrC_eq_at_real_of_const ∘ corrC_const_on_strip_of_edges`.  The two edge-reality inputs are
    `corrC_real_on_axis` (the `Im = 0` edge, RvD step 4) and the KMS-flip top edge (`Im = 1`, RvD step 5,
    where `StripKMSrvd` is consumed).  Applied to `V` and to `Δ^{it}` (both giving `⟨w, gaussSmear⟩`) it
    yields `⟨w, V_t(gaussSmear)⟩ = ⟨w, Δ^{it}(gaussSmear)⟩`; totality of `w` + density close to `V = Δ^{it}`. -/
theorem corrC_orbit_eq_of_edges_real {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η w : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η)
    (h0 : ∀ z : ℂ, z.im = 0 → (corrC w V n η z).im = 0)
    (h1 : ∀ z : ℂ, z.im = 1 → (corrC w V n η z).im = 0) (t : ℝ) :
    innerSL ℂ w (V t (gaussSmear V n η)) = innerSL ℂ w (gaussSmear V n η) :=
  corrC_eq_at_real_of_const hn η w hcont hbd hgrp
    (corrC_const_on_strip_of_edges hn η w hcont hbd h0 h1) t

end QIQTH.StandardSubspaceModular
