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
import QIQTH.ModularRelativeEntropy

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

/-- **Uniform bound of the KMS correlation on the CLOSED strip**: for `0 ≤ Im z ≤ 1`,
    `‖corrC ξ V n η z‖ ≤ ‖ξ‖·e^{n}·‖η‖·√(π/n)`.  Same as `corrC_bdd_strip` but on the closed `kmsStrip`
    (`(Im z)² ≤ 1` there).  The bound hypothesis of `eqOn_of_im_zero_edge`. -/
theorem corrC_bdd_closed_strip {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η ξ : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) :
    ∀ z ∈ StripUniqueness.kmsStrip,
      ‖corrC ξ V n η z‖ ≤ ‖ξ‖ * (Real.exp n * ‖η‖ * Real.sqrt (Real.pi / n)) := by
  intro z hz
  simp only [StripUniqueness.kmsStrip, Set.mem_preimage, Set.mem_Icc] at hz
  refine (corrC_norm_le hn η ξ hcont hbd z).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine Real.exp_le_exp.mpr ?_
  nlinarith [hz.1, hz.2, hn.le, mul_nonneg hn.le
    (mul_nonneg (by linarith [hz.2] : (0:ℝ) ≤ 1 - z.im) (by linarith [hz.1] : (0:ℝ) ≤ 1 + z.im))]

/-- **Uniform bound of the KMS correlation on the HALF strip** `{−1/2 ≤ Im z ≤ 0}` (the strip RvD Thm 3.8
    / Prop 3.5 actually use): `‖corrC ξ V n η z‖ ≤ ‖ξ‖·e^{n/4}·‖η‖·√(π/n)`, since `(Im z)² ≤ 1/4` there.
    The bounded-holomorphic input the *correct-strip* `g`-function argument consumes (with
    `diffContOnCl_corrC` restricted to `kmsHalfStripOpen` and `eqOn_of_im_zero_edge_halfStrip`). -/
theorem corrC_bdd_halfStrip {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η ξ : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖) :
    ∀ z ∈ StripUniqueness.kmsHalfStrip,
      ‖corrC ξ V n η z‖ ≤ ‖ξ‖ * (Real.exp (n / 4) * ‖η‖ * Real.sqrt (Real.pi / n)) := by
  intro z hz
  simp only [StripUniqueness.kmsHalfStrip, Set.mem_preimage, Set.mem_Icc] at hz
  refine (corrC_norm_le hn η ξ hcont hbd z).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine Real.exp_le_exp.mpr ?_
  nlinarith [hz.1, hz.2, hn.le, mul_nonneg hn.le
    (mul_nonneg (by linarith [hz.2] : (0:ℝ) ≤ 1/2 - z.im) (by linarith [hz.1] : (0:ℝ) ≤ 1/2 + z.im))]

/-- **Step-5 reality transfer** (RvD Theorem 3.8): the KMS top-edge reality transfers to the orbit
    correlation.  Suppose a function `f` (the KMS function produced by `StripKMSrvd`) is bounded-holomorphic
    on the strip, agrees with the orbit correlation `g = corrC w V n η` on the *real axis*, and has *real*
    top-edge values `Im f(t+i) = 0`.  Then `g`'s top edge is also real: `Im g(t+i) = 0`.  By
    `eqOn_of_im_zero_edge` (one-edge determination via Hadamard three-lines), `f = g` on the closed strip,
    so `g(t+i) = f(t+i)` is real.  This is exactly the `Im=1` edge hypothesis `h1` of
    `corrC_orbit_eq_of_edges_real` — the last analytic input, supplied from the labelled KMS condition. -/
theorem corrC_top_edge_real_of_kms_match {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n) (η w : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    {f : ℂ → ℂ} {M : ℝ} (hf : DiffContOnCl ℂ f StripUniqueness.kmsStripOpen)
    (hfb : ∀ z ∈ StripUniqueness.kmsStrip, ‖f z‖ ≤ M)
    (hmatch : ∀ t : ℝ, f (t : ℂ) = corrC w V n η (t : ℂ))
    (hftop : ∀ t : ℝ, (f ((t : ℂ) + Complex.I)).im = 0) (t : ℝ) :
    (corrC w V n η ((t : ℂ) + Complex.I)).im = 0 := by
  have heq : Set.EqOn f (corrC w V n η) StripUniqueness.kmsStrip :=
    StripUniqueness.eqOn_of_im_zero_edge
      (M := max M (‖w‖ * (Real.exp n * ‖η‖ * Real.sqrt (Real.pi / n))))
      hf (diffContOnCl_corrC hn η w hcont hbd)
      (fun z hz => le_trans (hfb z hz) (le_max_left _ _))
      (fun z hz => le_trans (corrC_bdd_closed_strip hn η w hcont hbd z hz) (le_max_right _ _))
      (fun z hz0 => by
        have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz0])
        rw [hz']; exact hmatch z.re)
  have hmem : ((t : ℂ) + Complex.I) ∈ StripUniqueness.kmsStrip := by
    simp only [StripUniqueness.kmsStrip, Set.mem_preimage, Set.mem_Icc, Complex.add_im,
      Complex.ofReal_im, Complex.I_im, zero_add]
    exact ⟨zero_le_one, le_rfl⟩
  rw [← heq hmem]
  exact hftop t

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

/-- **Analytic capstone of the KMS-uniqueness proof** (RvD Theorem 3.8): given the labelled KMS function,
    the orbit matrix element is `t`-independent.  Assembles the whole verified analytic chain.  Inputs: the
    *geometric* facts (`w ⊥ i𝒦`, the orbit `V_t(gaussSmear)` stays in `𝒦`) and the *labelled KMS input* — a
    function `f` (the `StripKMSrvd` output) bounded-holomorphic on the strip, agreeing with the orbit
    correlation `g = corrC w V n η` on the real axis, with real top-edge values `Im f(t+i) = 0`.  Conclusion:
    `⟨w, V_t(gaussSmear)⟩ = ⟨w, gaussSmear⟩` for all real `t`.  Chain: `corrC_real_on_axis` (bottom edge) +
    `corrC_top_edge_real_of_kms_match` (top edge, via the Hadamard one-edge matching) ⟹
    `corrC_orbit_eq_of_edges_real`.  Comparing this for `V` and `Δ^{it}` + totality of `w` + density of the
    entire vectors (`operator_ext_inner_dense`) discharges `hUniq`; the only non-machine-checked content is
    producing `f` from `StripKMSrvd` at the RvD vectors (the labelled physics input). -/
theorem corrC_orbit_eq_of_kms_function (S : StandardSubspace H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ}
    (hn : 0 < n) (η w : H) (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η) (hw : projIK S w = 0)
    (hKinv : ∀ s : ℝ, projK S (V s (gaussSmear V n η)) = V s (gaussSmear V n η))
    {f : ℂ → ℂ} {M : ℝ} (hf : DiffContOnCl ℂ f StripUniqueness.kmsStripOpen)
    (hfb : ∀ z ∈ StripUniqueness.kmsStrip, ‖f z‖ ≤ M)
    (hmatch : ∀ t : ℝ, f (t : ℂ) = corrC w V n η (t : ℂ))
    (hftop : ∀ t : ℝ, (f ((t : ℂ) + Complex.I)).im = 0) (t : ℝ) :
    innerSL ℂ w (V t (gaussSmear V n η)) = innerSL ℂ w (gaussSmear V n η) := by
  refine corrC_orbit_eq_of_edges_real hn η w hcont hbd hgrp (fun z hz0 => ?_) (fun z hz1 => ?_) t
  · have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz0])
    rw [hz']; exact corrC_real_on_axis S hn η w hcont hbd hgrp hw hKinv z.re
  · have hz' : z = ((z.re : ℝ) : ℂ) + Complex.I := Complex.ext (by simp) (by simp [hz1])
    rw [hz']
    exact corrC_top_edge_real_of_kms_match hn η w hcont hbd hf hfb hmatch hftop z.re

/-- **Density extension of the orbit identity** (RvD Theorem 3.8): from the smeared identity to the vector
    identity.  If `⟨w, V_t(gaussSmear V n η)⟩ = ⟨w, gaussSmear V n η⟩` holds for every `n > 0` (the output of
    `corrC_orbit_eq_of_kms_function`), then `⟨w, V_t η⟩ = ⟨w, η⟩`.  Scaling by `√(n/π)` turns `gaussSmear`
    into the *normalised* entire vector `entireVec V n η`, which converges to `η` (`entireVec_tendsto`);
    continuity of `V_t` and `⟨w, ·⟩` passes to the limit.  Resolves the smearing mismatch in the `V`-vs-`Δ`
    comparison: applying this to both flows gives `⟨w, V_t η⟩ = ⟨w, η⟩ = ⟨w, Δ^{it} η⟩` on the same `η ∈ 𝒦`,
    so `V_t η − Δ^{it} η ⊥` (the total set `{w}` ⊆ `(i𝒦)^⊥`) ⟹ `∈ i𝒦`; with both in `𝒦` and `𝒦 ∩ i𝒦 = {0}`,
    `V_t η = Δ^{it} η`. -/
theorem orbit_inner_eq_of_entire {V : ℝ → (H →L[ℂ] H)} (η w : H) (t : ℝ)
    (hcont : Continuous (fun s => V s η)) (hbd : ∀ s, ‖V s η‖ ≤ ‖η‖) (hV0 : V 0 η = η)
    (hconc : ∀ n : ℝ, 0 < n →
      innerSL ℂ w (V t (gaussSmear V n η)) = innerSL ℂ w (gaussSmear V n η)) :
    innerSL ℂ w (V t η) = innerSL ℂ w η := by
  have hsc : ∀ n : ℝ, 0 < n →
      innerSL ℂ w (V t (entireVec V n η)) = innerSL ℂ w (entireVec V n η) := by
    intro n hn
    rw [entireVec, (V t).map_smul_of_tower, (innerSL ℂ w).map_smul_of_tower,
      (innerSL ℂ w).map_smul_of_tower, hconc n hn]
  have hlhs : Filter.Tendsto (fun n => innerSL ℂ w (V t (entireVec V n η))) Filter.atTop
      (nhds (innerSL ℂ w (V t η))) :=
    ((innerSL ℂ w).continuous.tendsto _).comp
      (((V t).continuous.tendsto _).comp (entireVec_tendsto η hcont hbd hV0))
  have hrhs : Filter.Tendsto (fun n => innerSL ℂ w (entireVec V n η)) Filter.atTop
      (nhds (innerSL ℂ w η)) :=
    ((innerSL ℂ w).continuous.tendsto _).comp (entireVec_tendsto η hcont hbd hV0)
  exact tendsto_nhds_unique
    (hlhs.congr' ((Filter.eventually_gt_atTop 0).mono (fun n hn => hsc n hn))) hrhs

/-- **Operator equality from matrix elements on dense sets** (RvD Theorem 3.8, the totality + density
    wiring, step 6e).  If two continuous operators `A, B` have equal matrix elements `⟨w, A x⟩ = ⟨w, B x⟩`
    for `w` ranging over a dense (total) set `Dw` and `x` over a dense set `Dx`, then `A = B`.  For fixed
    `x ∈ Dx`, density of `Dw` + continuity of `w ↦ ⟨w, ·⟩` upgrades to all `w`, giving `A x = B x`
    (`ext_inner_left`); then `A, B` continuous and agreeing on the dense `Dx` are equal.  This is the final
    step of the KMS-uniqueness proof: `Dw =` the total set `{J(2−R)^{1/2}R^{−1/2}ζ}`, `Dx =` the dense
    entire vectors (`entireVec_tendsto`), and the matrix-element equality is `corrC_orbit_eq_of_edges_real`
    applied to `V` and `Δ^{it}`. -/
theorem operator_ext_inner_dense {A B : H →L[ℂ] H} {Dw Dx : Set H}
    (hDw : Dense Dw) (hDx : Dense Dx)
    (h : ∀ w ∈ Dw, ∀ x ∈ Dx, inner ℂ w (A x) = inner ℂ w (B x)) : A = B := by
  have key : ∀ a b : H, (∀ w ∈ Dw, inner ℂ w a = inner ℂ w b) → a = b := by
    intro a b hab
    have heq : (fun w : H => (inner ℂ w a : ℂ)) = fun w => inner ℂ w b :=
      Continuous.ext_on hDw (by fun_prop) (by fun_prop) hab
    exact ext_inner_left ℂ (fun w => congrFun heq w)
  apply DFunLike.coe_injective
  exact Continuous.ext_on hDx A.continuous B.continuous
    (fun x hx => key (A x) (B x) (fun w hw => h w hw x hx))

/-- **Top-level assembly of RvD Theorem 3.8** (the `hUniq` discharge, modulo the labelled orbit identities).
    If `V` and the modular flow `Δ^{it} = modUnitary S` both **preserve `𝒦`** and both satisfy the *orbit
    identity* `⟨w, ·_t η⟩ = ⟨w, η⟩` for every `η ∈ 𝒦` and every `w ⊥ i𝒦`, then `Δ^{it} = V_t`.  Proof: the two
    orbit identities give `⟨w, Δ^{it} η⟩ = ⟨w, η⟩ = ⟨w, V_t η⟩` for all `w ⊥ i𝒦`, with both `Δ^{it} η, V_t η ∈
    𝒦`; `eq_of_mem_K_of_inner_perp_IK` (totality, `𝒦 ∩ i𝒦 = {0}`) gives `Δ^{it} η = V_t η` on `𝒦`, and
    `clm_eq_of_eqOn_K` (density, `𝒦 + i𝒦 = ⊤`) lifts to the operator identity.  The orbit identities are the
    output of the verified KMS chain (`corrC_orbit_eq_of_kms_function` ∘ `orbit_inner_eq_of_entire`); the
    `𝒦`-invariance is the standing `hUniq` hypothesis.  Only producing the KMS function `f` from
    `StripKMSrvd` at the RvD vectors remains to make the orbit identities themselves theorems. -/
theorem modUnitary_eq_of_orbit_inner (S : StandardSubspace H) {V : ℝ → (H →L[ℂ] H)} (t : ℝ)
    (hVK : ∀ η ∈ S.toClosedSubmodule, V t η ∈ S.toClosedSubmodule)
    (hΔK : ∀ η ∈ S.toClosedSubmodule, modUnitary S t η ∈ S.toClosedSubmodule)
    (hVorbit : ∀ η ∈ S.toClosedSubmodule, ∀ w, projIK S w = 0 →
      inner ℂ w (V t η) = inner ℂ w η)
    (hΔorbit : ∀ η ∈ S.toClosedSubmodule, ∀ w, projIK S w = 0 →
      inner ℂ w (modUnitary S t η) = inner ℂ w η) :
    modUnitary S t = V t := by
  refine clm_eq_of_eqOn_K S (fun η hη => ?_)
  refine eq_of_mem_K_of_inner_perp_IK S ((mem_K_iff_projK S _).mp (hΔK η hη))
    ((mem_K_iff_projK S _).mp (hVK η hη)) (fun w hw => ?_)
  rw [hΔorbit η hη w hw, hVorbit η hη w hw]

/-- **The Δ-side modular correlation is pinned by its boundary data** (RvD Theorem 3.8, the comparison
    target).  In the regular spectral regime `σ(R) ⊆ [a, 2−a]`, the strip extension `modCorrExt S ξ`
    (`= ⟨ξ, Δ^{it} ξ⟩` continued to the KMS strip) is bounded-holomorphic (`diffContOnCl_modCorrExt`,
    `modCorrExt_norm_le`); hence any competitor `F` that is bounded-holomorphic on the strip and shares
    `modCorrExt`'s real-axis values *and* its KMS top-edge values coincides with it on the whole closed
    strip.  This is the concrete RvD comparison: the modular correlation, and any KMS competitor's, are
    pinned by the same two edges — the `Δ`-side dual of `corrC_eqOn_strip_of_boundary_eq`. -/
theorem modCorrExt_eq_of_boundary (S : StandardSubspace H) (ξ : H) {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hspec : ∀ ω : spectrum ℝ (rvdRC S),
      a ≤ (ω : spectrum ℝ (rvdRC S)).val ∧ (ω : spectrum ℝ (rvdRC S)).val ≤ 2 - a)
    {F : ℂ → ℂ} {M : ℝ} (hF : DiffContOnCl ℂ F StripUniqueness.kmsStripOpen)
    (hFb : ∀ z ∈ StripUniqueness.kmsStripOpen, ‖F z‖ ≤ M)
    (hreal : ∀ t : ℝ, F (t : ℂ) = modCorrExt S ξ (t : ℂ))
    (htop : ∀ t : ℝ, F ((t : ℂ) + Complex.I) = modCorrExt S ξ ((t : ℂ) + Complex.I)) :
    Set.EqOn F (modCorrExt S ξ) StripUniqueness.kmsStrip := by
  refine StripUniqueness.kms_correlation_boundary_determined (M := max M ((2 - a) / a * ‖ξ‖ ^ 2))
    hF (diffContOnCl_modCorrExt S ξ ha0 ha1 hspec)
    (fun z hz => le_trans (hFb z hz) (le_max_left _ _)) (fun z hz => ?_) hreal htop
  simp only [StripUniqueness.kmsStripOpen, Set.mem_preimage, Set.mem_Ioo] at hz
  exact le_trans (modCorrExt_norm_le S ξ ha0 ha1 hspec (le_of_lt hz.1) (le_of_lt hz.2)) (le_max_right _ _)

end QIQTH.StandardSubspaceModular
