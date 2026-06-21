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

open StripUniqueness in
/-- **The device g-function is constant on the real axis** (RvD Theorem 3.8 constancy, the analytic heart of
    the GConstancy output): if the device g-function `g(z) = ⟪J·d_z(R)ζ, V_z η_n⟫` is real on BOTH half-strip
    edges `Im z = 0` and `Im z = −1/2`, then `g(t) = g(0)` for every real `t`.  The g-function is
    bounded-holomorphic (`diffContOnCl_gFunction`, `gFunction_norm_le` + `gaussSmearC_norm_le` give the uniform
    bound `2√2‖ζ‖·e^{n/4}‖η‖√(π/n)` since `(Im z)² ≤ 1/4`), so the two-edge half-strip Phragmén–Lindelöf
    (`eqConst_of_im_zero_halfStrip`) forces it constant on the open half-strip; continuity to the closure
    (`Set.EqOn.closure`) propagates the constant to the real axis.  The top edge is geometric
    (`gFunction_top_edge_real`); the bottom edge `Im z = −1/2` is the KMS input (`HalfStripReal`). -/
theorem gFunction_eq_zero_const (S : StandardSubspace H) (ζ : H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ}
    (hn : 0 < n) (η : H) (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (h0 : ∀ z : ℂ, z.im = 0 →
      (modConjBilin S (deviceVecF S ζ z) (gaussSmearC V n η z)).im = 0)
    (h1 : ∀ z : ℂ, z.im = -(1 / 2) →
      (modConjBilin S (deviceVecF S ζ z) (gaussSmearC V n η z)).im = 0) (t : ℝ) :
    modConjBilin S (deviceVecF S ζ (t : ℂ)) (gaussSmearC V n η (t : ℂ))
      = modConjBilin S (deviceVecF S ζ 0) (gaussSmearC V n η 0) := by
  have hM : ∀ z ∈ kmsHalfStripOpen,
      ‖modConjBilin S (deviceVecF S ζ z) (gaussSmearC V n η z)‖ ≤
      2 * Real.sqrt 2 * ‖ζ‖ * (Real.exp (n / 4) * ‖η‖ * Real.sqrt (Real.pi / n)) := by
    intro z hz
    simp only [kmsHalfStripOpen, Set.mem_preimage, Set.mem_Ioo] at hz
    refine (gFunction_norm_le S ζ η z).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine (gaussSmearC_norm_le hn η hcont hbd z).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_)
        (norm_nonneg _)) (Real.sqrt_nonneg _))
    nlinarith [hz.1, hz.2, hn.le, mul_pos (show (0:ℝ) < z.im + 1/2 by linarith)
      (show (0:ℝ) < 1/2 - z.im by linarith)]
  obtain ⟨c, hc⟩ := eqConst_of_im_zero_halfStrip
    (diffContOnCl_gFunction S ζ hn η hcont hbd) hM h0 h1
  have hcl : Complex.im ⁻¹' Set.Icc (-(1 / 2) : ℝ) 0 = closure kmsHalfStripOpen := by
    rw [kmsHalfStripOpen, Complex.closure_preimage_im, closure_Ioo (by norm_num : (-(1/2):ℝ) ≠ 0)]
  have hext := Set.EqOn.of_subset_closure (s := kmsHalfStripOpen)
    (t := Complex.im ⁻¹' Set.Icc (-(1 / 2) : ℝ) 0) hc
    ((diffContOnCl_gFunction S ζ hn η hcont hbd).2.mono (le_of_eq hcl)) continuousOn_const
    (Set.preimage_mono Set.Ioo_subset_Icc_self) (le_of_eq hcl)
  rw [show modConjBilin S (deviceVecF S ζ (t : ℂ)) (gaussSmearC V n η (t : ℂ)) = c from
      hext (by simp only [Set.mem_preimage, Complex.ofReal_im, Set.mem_Icc]; constructor <;> norm_num),
    show modConjBilin S (deviceVecF S ζ (0 : ℂ)) (gaussSmearC V n η (0 : ℂ)) = c from
      hext (by simp only [Set.mem_preimage, Complex.zero_im, Set.mem_Icc]; constructor <;> norm_num)]

/-- **GConstancy for the entire vectors** (RvD Theorem 3.8 output, assembled): from the g-function constancy
    `g(t) = g(0)` and the edge value identities, `⟪V_t η_n, Δ^{it}(J ξ)⟫ = ⟪η_n, J ξ⟫` for `ξ = √R ζ`,
    `η_n = gaussSmear`.  `gFunction_eq_zero_const` gives `g(t) = g(0)`; `gFunction_real_eq` evaluates the top
    edge `g(t) = ⟪Δ^{it}(Jξ), V_t η_n⟫`, `gFunction_zero` the origin `g(0) = ⟪Jξ, η_n⟫`; conjugating
    (`inner_conj_symm`) flips both slots to the GConstancy form.  This is exactly `GConstancy S V` evaluated at
    `(η_n, √R ζ)` — the analytic conclusion of RvD Theorem 3.8, modulo the two edge-reality inputs. -/
theorem gConstancy_entire (S : StandardSubspace H) (ζ : H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ}
    (hn : 0 < n) (η : H) (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η)
    (h0 : ∀ z : ℂ, z.im = 0 →
      (modConjBilin S (deviceVecF S ζ z) (gaussSmearC V n η z)).im = 0)
    (h1 : ∀ z : ℂ, z.im = -(1 / 2) →
      (modConjBilin S (deviceVecF S ζ z) (gaussSmearC V n η z)).im = 0) (t : ℝ) :
    inner ℂ (V t (gaussSmear V n η)) (modUnitary S t (modConj S (rvdSqrtR S ζ)))
      = inner ℂ (gaussSmear V n η) (modConj S (rvdSqrtR S ζ)) := by
  have hconst := gFunction_eq_zero_const S ζ hn η hcont hbd h0 h1 t
  rw [gFunction_real_eq S ζ hn η hcont hbd hgrp t, gFunction_zero] at hconst
  rw [← inner_conj_symm (V t (gaussSmear V n η)) (modUnitary S t (modConj S (rvdSqrtR S ζ))),
    ← inner_conj_symm (gaussSmear V n η) (modConj S (rvdSqrtR S ζ))]
  exact congrArg (starRingEnd ℂ) hconst

/-- **Top-edge reality of the g-function, `∀ z` form** (the `h0` input to `gFunction_eq_zero_const`): if
    `ξ = √R ζ ∈ 𝒦` and the V-orbit `V_s(gaussSmear)` stays in `𝒦`, then `Im g(z) = 0` on the whole edge
    `Im z = 0`.  Any `z` with `Im z = 0` is real (`z = ↑z.re`), so this is just `gFunction_top_edge_real` at
    `t = z.re`.  Geometric — the always-available top edge of the device g-function. -/
theorem gFunction_top_edge_real_all (S : StandardSubspace H) (ζ : H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ}
    (hn : 0 < n) (η : H) (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η)
    (hξ : projK S (rvdSqrtR S ζ) = rvdSqrtR S ζ)
    (hKinv : ∀ s : ℝ, projK S (V s (gaussSmear V n η)) = V s (gaussSmear V n η))
    (z : ℂ) (hz : z.im = 0) :
    (modConjBilin S (deviceVecF S ζ z) (gaussSmearC V n η z)).im = 0 := by
  have hz_eq : z = (z.re : ℂ) := Complex.ext rfl (by rw [hz, Complex.ofReal_im])
  rw [hz_eq]
  exact gFunction_top_edge_real S ζ hn η hcont hbd hgrp hξ z.re (hKinv z.re)

/-- **GConstancy for the entire vectors, reduced to the BOTTOM-EDGE KMS reality** (the precise residual of the
    RvD Theorem 3.8 discharge).  With the geometric inputs (`ξ = √R ζ ∈ 𝒦`, the V-orbit stays in `𝒦`) the
    top-edge reality is automatic (`gFunction_top_edge_real_all`), so the ENTIRE analytic g-function argument
    collapses to a single hypothesis: `h1`, the reality of `g` on the mid-line `Im z = −1/2`.  That mid-line
    reality is exactly the KMS input (`HalfStripReal` / `StripKMSrvd`).  Conclusion: `⟪V_t η_n, Δ^{it}(Jξ)⟫ =
    ⟪η_n, Jξ⟫` (GConstancy at the entire vector `η_n` and `ξ = √R ζ`) — everything but the bottom-edge KMS step
    is now machine-checked. -/
theorem gConstancy_entire_of_bottom (S : StandardSubspace H) (ζ : H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ}
    (hn : 0 < n) (η : H) (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η)
    (hξ : projK S (rvdSqrtR S ζ) = rvdSqrtR S ζ)
    (hKinv : ∀ s : ℝ, projK S (V s (gaussSmear V n η)) = V s (gaussSmear V n η))
    (h1 : ∀ z : ℂ, z.im = -(1 / 2) →
      (modConjBilin S (deviceVecF S ζ z) (gaussSmearC V n η z)).im = 0) (t : ℝ) :
    inner ℂ (V t (gaussSmear V n η)) (modUnitary S t (modConj S (rvdSqrtR S ζ)))
      = inner ℂ (gaussSmear V n η) (modConj S (rvdSqrtR S ζ)) :=
  gConstancy_entire S ζ hn η hcont hbd hgrp
    (gFunction_top_edge_real_all S ζ hn η hcont hbd hgrp hξ hKinv) h1 t

open Filter in
/-- **GConstancy density**: GConstancy holds for `η` if it holds for every normalised entire vector
    `entireVec V n η` (`n → ∞`).  The entire vectors converge to `η` (`entireVec_tendsto`), and both sides
    `⟪V_t·, w⟫`, `⟪·, w⟫` are continuous, so the constant equality passes to the limit (`tendsto_nhds_unique`).
    This lifts the entire-vector GConstancy (`gConstancy_entire_of_bottom`) to the genuine `η ∈ 𝒦`. -/
theorem gConstancy_of_entireVec_limit (S : StandardSubspace H) {V : ℝ → (H →L[ℂ] H)} (η ξ : H)
    (t : ℝ) (hcont : Continuous (fun s => V s η)) (hbd : ∀ s, ‖V s η‖ ≤ ‖η‖) (hV0 : V 0 η = η)
    (hGC : ∀ n : ℝ, 0 < n →
      inner ℂ (V t (entireVec V n η)) (modUnitary S t (modConj S ξ))
        = inner ℂ (entireVec V n η) (modConj S ξ)) :
    inner ℂ (V t η) (modUnitary S t (modConj S ξ)) = inner ℂ η (modConj S ξ) := by
  have htend := entireVec_tendsto η hcont hbd hV0
  have hL : Tendsto (fun n => inner ℂ (V t (entireVec V n η)) (modUnitary S t (modConj S ξ)))
      atTop (nhds (inner ℂ (V t η) (modUnitary S t (modConj S ξ)))) :=
    (Continuous.tendsto (Continuous.inner (V t).continuous continuous_const) η).comp htend
  have hR : Tendsto (fun n => inner ℂ (entireVec V n η) (modConj S ξ))
      atTop (nhds (inner ℂ η (modConj S ξ))) :=
    (Continuous.tendsto (Continuous.inner continuous_id continuous_const) η).comp htend
  exact tendsto_nhds_unique hL
    (hR.congr' (eventually_atTop.mpr ⟨1, fun n hn => (hGC n (by linarith)).symm⟩))

/-- **GConstancy is real-scalar linear in the vector**: if GConstancy holds for `v`, it holds for `c • v`
    (`c : ℝ`).  `V_t` is ℂ-linear (so commutes with the real scalar) and `⟪·, w⟫` pulls out `conj(c) = c`
    (`inner_smul_left`, `c` real).  This bridges `gConstancy_entire_of_bottom` (for `gaussSmear`) to the
    normalised entire vector `entireVec = √(n/π) • gaussSmear` the density limit consumes. -/
theorem gConstancy_real_smul (S : StandardSubspace H) {V : ℝ → (H →L[ℂ] H)} (v ξ : H) (t : ℝ) (c : ℝ)
    (hGC : inner ℂ (V t v) (modUnitary S t (modConj S ξ)) = inner ℂ v (modConj S ξ)) :
    inner ℂ (V t (c • v)) (modUnitary S t (modConj S ξ)) = inner ℂ (c • v) (modConj S ξ) := by
  rw [← algebraMap_smul ℂ c v, map_smul, inner_smul_left, inner_smul_left, hGC]

/-- **GConstancy for `η ∈ 𝒦` reduced to the bottom-edge KMS reality** (the full density+scaling closeout):
    `⟪V_t η, Δ^{it}(Jξ)⟫ = ⟪η, Jξ⟫` for `ξ = √R ζ`, given the geometric inputs (`ξ ∈ 𝒦`, the orbit stays in
    `𝒦` for every entire vector) and the bottom-edge reality `h1` for every entire vector.  Chains
    `gConstancy_entire_of_bottom` (GConstancy for `gaussSmear V n η`) → `gConstancy_real_smul` (scale to the
    normalised `entireVec = √(n/π)·gaussSmear`) → `gConstancy_of_entireVec_limit` (`n → ∞`, `entireVec → η`).
    So the FULL GConstancy at `η` (any `η ∈ 𝒦` with the orbit hypotheses) now rests only on the bottom-edge
    mid-line KMS reality — the single labelled input of RvD Theorem 3.8. -/
theorem gConstancy_eta_of_bottom (S : StandardSubspace H) (ζ : H) {V : ℝ → (H →L[ℂ] H)} (η : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η) (hV0 : V 0 η = η)
    (hξ : projK S (rvdSqrtR S ζ) = rvdSqrtR S ζ)
    (hKinv : ∀ n : ℝ, 0 < n → ∀ s : ℝ,
      projK S (V s (gaussSmear V n η)) = V s (gaussSmear V n η))
    (h1 : ∀ n : ℝ, 0 < n → ∀ z : ℂ, z.im = -(1 / 2) →
      (modConjBilin S (deviceVecF S ζ z) (gaussSmearC V n η z)).im = 0) (t : ℝ) :
    inner ℂ (V t η) (modUnitary S t (modConj S (rvdSqrtR S ζ)))
      = inner ℂ η (modConj S (rvdSqrtR S ζ)) := by
  refine gConstancy_of_entireVec_limit S η (rvdSqrtR S ζ) t hcont hbd hV0 (fun n hn => ?_)
  rw [entireVec]
  exact gConstancy_real_smul S (gaussSmear V n η) (rvdSqrtR S ζ) t (Real.sqrt (n / Real.pi))
    (gConstancy_entire_of_bottom S ζ hn η hcont hbd hgrp hξ (hKinv n hn) (h1 n hn) t)

open Filter in
/-- **GConstancy is closed in `ξ`** (continuity in the second-slot vector): if GConstancy at `(η, ξ_k)` holds
    for a sequence `ξ_k → ξ`, it holds at `(η, ξ)`.  Both sides `⟪V_t η, Δ^{it}(J·)⟫` and `⟪η, J·⟫` are
    continuous in `ξ` (`modConj`, `modUnitary` continuous, inner continuous), so the equality passes to the
    limit (`tendsto_nhds_unique`).  This lifts GConstancy from `ξ = √R ζ` (`gConstancy_eta_of_bottom`) to any
    `ξ` in the closure of the `√R`-range — and `√R` has dense range (`R` injective via
    `rvdRC_mul_rvdTwoSubRC_injective`), the `ξ = √R ζ` reconciliation. -/
theorem gConstancy_of_tendsto_xi (S : StandardSubspace H) {V : ℝ → (H →L[ℂ] H)} (η : H) (t : ℝ)
    {ξ : H} {ξs : ℕ → H} (htend : Tendsto ξs atTop (nhds ξ))
    (hGC : ∀ k, inner ℂ (V t η) (modUnitary S t (modConj S (ξs k)))
      = inner ℂ η (modConj S (ξs k))) :
    inner ℂ (V t η) (modUnitary S t (modConj S ξ)) = inner ℂ η (modConj S ξ) := by
  have hcL : Continuous (fun x => inner ℂ (V t η) (modUnitary S t (modConj S x))) :=
    Continuous.inner continuous_const ((modUnitary S t).continuous.comp (modConj S).continuous)
  have hcR : Continuous (fun x => inner ℂ η (modConj S x)) :=
    Continuous.inner continuous_const (modConj S).continuous
  exact tendsto_nhds_unique ((hcL.tendsto ξ).comp htend)
    (((hcR.tendsto ξ).comp htend).congr (fun k => (hGC k).symm))

open Filter in
/-- **GConstancy at every `ξ ∈ 𝒦`, from the `√R`-vector GConstancy + the `√R`-range density** (the `ξ`-side
    closeout).  Given GConstancy holds at every `√R ζ ∈ 𝒦` (`hsqrt`, supplied by `gConstancy_eta_of_bottom`)
    and the `√R`-range is dense in `𝒦` (`hdense`: every `ξ ∈ 𝒦` is a limit of `√R ζ_k ∈ 𝒦` — the structural
    fact that `√R` has dense range, `R` injective via `rvdRC_mul_rvdTwoSubRC_injective`), GConstancy holds at
    every `ξ ∈ 𝒦` by closedness in `ξ` (`gConstancy_of_tendsto_xi`).  This is exactly the `∀ ξ ∈ 𝒦` premise of
    the comparison wrapper `comparisonDatum_of_gConstancy`, completing the `ξ`-reconciliation modulo the named
    `√R`-density input. -/
theorem gConstancy_xi_of_density (S : StandardSubspace H) {V : ℝ → (H →L[ℂ] H)} (η : H) (t : ℝ)
    (hsqrt : ∀ ζ : H, projK S (rvdSqrtR S ζ) = rvdSqrtR S ζ →
      inner ℂ (V t η) (modUnitary S t (modConj S (rvdSqrtR S ζ)))
        = inner ℂ η (modConj S (rvdSqrtR S ζ)))
    (hdense : ∀ ξ ∈ (S.toClosedSubmodule : Set H), ∃ ζs : ℕ → H,
      (∀ k, projK S (rvdSqrtR S (ζs k)) = rvdSqrtR S (ζs k)) ∧
        Tendsto (fun k => rvdSqrtR S (ζs k)) atTop (nhds ξ))
    (ξ : H) (hξ : ξ ∈ (S.toClosedSubmodule : Set H)) :
    inner ℂ (V t η) (modUnitary S t (modConj S ξ)) = inner ℂ η (modConj S ξ) := by
  obtain ⟨ζs, hζmem, hζtend⟩ := hdense ξ hξ
  exact gConstancy_of_tendsto_xi S η t hζtend (fun k => hsqrt (ζs k) (hζmem k))

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

/-- **CORRECTED top-level assembly of RvD Theorem 3.8** (`hUniq` discharge, faithful form).  Supersedes
    `modUnitary_eq_of_orbit_inner`, whose hypotheses `⟨w, ·_t η⟩ = ⟨w, η⟩` are VACUOUS (they would force
    `V_t = id`; see the FRAMEWORK CAVEAT in AxiomAudit).  The correct orbit datum is the *U-vs-Δ comparison*
    `⟨w, V_t η⟩ = ⟨w, Δ^{it} η⟩` directly — what RvD's `g`-function constancy + the KMS-matching against
    `⟨h(z), Δ^{it}ξ⟩` actually produce (the KMS condition is applied to the pair `(η, Δ^{it}ξ)`, so `Δ^{it}`
    genuinely enters; it does NOT factor through `⟨w, η⟩`).  This hypothesis is satisfiable and non-vacuous.
    Given it (+ both flows preserving `𝒦`): `eq_of_mem_K_of_inner_perp_IK` (`IsSeparating`) gives `V_t η =
    Δ^{it} η` on `𝒦`, and `clm_eq_of_eqOn_K` (`IsCyclic`) lifts to `Δ^{it} = V_t`.  Producing the comparison
    datum from `StripKMSrvd` via the half-strip `g`-function still needs RvD's `R^{−1/2}` ζ-device (Prop 3.7),
    garbled in the available scan — not fabricated. -/
theorem modUnitary_eq_of_orbit_compare (S : StandardSubspace H) {V : ℝ → (H →L[ℂ] H)} (t : ℝ)
    (hVK : ∀ η ∈ S.toClosedSubmodule, V t η ∈ S.toClosedSubmodule)
    (hΔK : ∀ η ∈ S.toClosedSubmodule, modUnitary S t η ∈ S.toClosedSubmodule)
    (hcompare : ∀ η ∈ S.toClosedSubmodule, ∀ w, projIK S w = 0 →
      inner ℂ w (V t η) = inner ℂ w (modUnitary S t η)) :
    modUnitary S t = V t := by
  refine clm_eq_of_eqOn_K S (fun η hη => ?_)
  exact eq_of_mem_K_of_inner_perp_IK S ((mem_K_iff_projK S _).mp (hΔK η hη))
    ((mem_K_iff_projK S _).mp (hVK η hη)) (fun w hw => (hcompare η hη w hw).symm)

/-- **Polarization bridge: diagonal quadratic forms pin a bounded operator** (final step of the
    *diagonal-correlation* route to the `hUniq` discharge).  Over `ℂ`, two bounded operators with equal
    diagonal forms `⟨ξ, A ξ⟩ = ⟨ξ, B ξ⟩` for all `ξ` are equal — the polarization identity packaged as
    `inner_map_self_eq_zero` applied to `A − B`.  This converts the SCALAR correlation equality that
    strip-uniqueness delivers (`modCorrExt`, the `Δ`-side `⟨ξ, Δ^{iz} ξ⟩`, against a competitor's KMS
    extension `F`) into the operator identity `Δ^{it} = V_t`.  Unlike the discredited `corrC(Jξ)` constancy
    route, this bridge is non-vacuous: it is the standard, correct closeout once the diagonal correlations
    `⟨ξ, V_t ξ⟩ = ⟨ξ, Δ^{it} ξ⟩` are shown equal for every `ξ`. -/
theorem clm_eq_of_inner_self_eq {A B : H →L[ℂ] H}
    (h : ∀ ξ : H, inner ℂ (A ξ) ξ = inner ℂ (B ξ) ξ) : A = B := by
  have key : ∀ ξ : H, inner ℂ ((A - B) ξ) ξ = 0 := by
    intro ξ
    rw [ContinuousLinearMap.sub_apply, inner_sub_left, h ξ, sub_self]
  have h0 : (A - B).toLinearMap = 0 := (inner_map_self_eq_zero _).mp key
  ext x
  exact sub_eq_zero.mp (by simpa using LinearMap.congr_fun h0 x)

/-- **Diagonal-correlation form of the RvD Theorem 3.8 closeout**: if the modular correlations agree,
    `⟨ξ, V_t ξ⟩ = ⟨ξ, Δ^{it} ξ⟩` for every `ξ`, then `V_t = Δ^{it}` (stated with `ξ` in the first slot, the
    `modCorrExt` convention).  This is the operator-level conclusion that the `modCorrExt` strip-uniqueness
    comparison (`modCorrExt_eq_of_boundary`) targets: once a KMS competitor's correlation is forced to equal
    the `Δ`-side `modCorrExt` on the whole strip — in particular on the real axis — this upgrades the scalar
    equality to the operator identity (`clm_eq_of_inner_self_eq` after conjugating both sides). -/
theorem modUnitary_eq_of_diag_corr (S : StandardSubspace H) {V : H →L[ℂ] H} (t : ℝ)
    (h : ∀ ξ : H, inner ℂ ξ (V ξ) = inner ℂ ξ (modUnitary S t ξ)) : V = modUnitary S t := by
  refine clm_eq_of_inner_self_eq (fun ξ => ?_)
  have hc := congrArg (starRingEnd ℂ) (h ξ)
  rwa [inner_conj_symm, inner_conj_symm] at hc

/-- **Faithful RvD `g`-function, top-edge reality** (RvD Thm 3.8, *p. 198*, the "`g(t) = ⟨U_t η, Jξ⟩` is
    real" step — verified against the clean PDF text, not the earlier garbled scan).  The genuine RvD
    half-strip function is `g(z) = ⟨Jξ, h(z)⟩` with the vector `Jξ = modConj S ξ` for `ξ ∈ 𝒦`.  RvD write
    that vector as `(2−R)^{1/2} R^{−1/2} ξ`, but their *own* identity `(2−R)^{1/2} R^{−1/2} ξ = Jξ`
    (the `modConj` sqrt-algebra, `modConj_rvdSqrtR` etc.) shows it equals the **bounded** `Jξ`: the
    unbounded `R^{−1/2}` is only motivation and is entirely AVOIDED here.  On the real axis
    `g(t) = ⟨Jξ, V_t(gaussSmear)⟩` is real because `Jξ ⊥ i𝒦` (`projIK (Jξ) = 0`, via
    `projIK_modConj_eq_zero_of_mem_K`, RvD Prop 2.3) while the smeared orbit stays in `𝒦`
    (`inner_real_of_mem_K_perp_IK`).  This is the **J-twisted** half-strip top edge — the faithful
    replacement for the discredited full-strip `corrC_real_on_axis` taken at a generic `w`.  (The
    paradox flagged earlier dissolves: `J𝒦 = (i𝒦)^{⊥ℝ}` is a *real*-orthogonal complement, so
    `⟨v, Jξ⟩ = 0 ∀ξ` does NOT place `v ∈ i𝒦`; the consistent conclusion is the U-vs-Δ comparison of
    `modUnitary_eq_of_orbit_compare`, the shared constant `⟨η, Jξ⟩` cancelling between the U- and Δ-sides.) -/
theorem corrJ_real_on_axis (S : StandardSubspace H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ} (hn : 0 < n)
    (η : H) {ξ : H} (hξ : projK S ξ = ξ)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    (hgrp : ∀ s t, V s (V t η) = V (s + t) η)
    (hKinv : ∀ s : ℝ, projK S (V s (gaussSmear V n η)) = V s (gaussSmear V n η)) (t : ℝ) :
    (corrC (modConj S ξ) V n η (t : ℂ)).im = 0 :=
  corrC_real_on_axis S hn η (modConj S ξ) hcont hbd hgrp
    (projIK_modConj_eq_zero_of_mem_K S hξ) hKinv t

/-- **Bottom-edge reality transfer for the half-strip correlation** (RvD Thm 3.8, the genuine "apply the KMS
    condition for `{U_t}` to the pair `(η, w)`" step) — stated for an ARBITRARY fixed second-slot vector `w`.
    If a function `f` is bounded-holomorphic on the half-strip `{−1/2 ≤ Im z ≤ 0}`, matches the orbit
    correlation `g = corrC w V n η` on the real axis, and is real on the lower edge `Im = −1/2`, then `g`'s
    lower edge inherits the reality: by `eqOn_of_im_zero_edge_halfStrip` (Hadamard one-edge), `f = g` on the
    half-strip, so `g(t − i/2)` is real.  **Satisfiability of the premise depends on `w`** — this is the
    discriminating point.  For `w = Δ^{it}ξ` (`= modUnitary S t ξ`, a VALID `𝒦`-pair vector since `Δ^{it}`
    preserves `𝒦`), the KMS condition for `{U_t}` genuinely supplies such an `f`, and the lower edge IS real
    (for `V = Δ` it is `⟨Δ^{it}Jη, Δ^{it}ξ⟩ = ⟨Jη, ξ⟩`, real by `inner_real_of_mem_K_perp_IK`).  This is RvD's
    actual non-circular step: it brings `Δ` in through a legitimate `𝒦`-pair, NOT by assuming `⟨ξ,U_tξ⟩ =
    ⟨ξ,Δ^{it}ξ⟩`.  For `w = Jξ` (the `corrJ` instance below) the premise is instead VACUOUS — see that lemma. -/
theorem corrW_bottom_edge_real_of_kms {V : ℝ → (H →L[ℂ] H)} {n : ℝ}
    (hn : 0 < n) (η w : H)
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    {f : ℂ → ℂ} {M : ℝ} (hf : DiffContOnCl ℂ f StripUniqueness.kmsHalfStripOpen)
    (hfb : ∀ z ∈ StripUniqueness.kmsHalfStrip, ‖f z‖ ≤ M)
    (hmatch : ∀ t : ℝ, f (t : ℂ) = corrC w V n η (t : ℂ))
    (hfbot : ∀ t : ℝ, (f ((t : ℂ) - Complex.I / 2)).im = 0) (t : ℝ) :
    (corrC w V n η ((t : ℂ) - Complex.I / 2)).im = 0 := by
  have hg : DiffContOnCl ℂ (corrC w V n η) StripUniqueness.kmsHalfStripOpen :=
    (differentiable_corrC hn η w hcont hbd).diffContOnCl
  have heq : Set.EqOn f (corrC w V n η) StripUniqueness.kmsHalfStrip :=
    StripUniqueness.eqOn_of_im_zero_edge_halfStrip
      (M := max M (‖w‖ * (Real.exp (n / 4) * ‖η‖ * Real.sqrt (Real.pi / n))))
      hf hg
      (fun z hz => le_trans (hfb z hz) (le_max_left _ _))
      (fun z hz => le_trans (corrC_bdd_halfStrip hn η w hcont hbd z hz) (le_max_right _ _))
      (fun z hz0 => by
        have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz0])
        rw [hz']; exact hmatch z.re)
  have hmem : ((t : ℂ) - Complex.I / 2) ∈ StripUniqueness.kmsHalfStrip := by
    have him : ((t : ℂ) - Complex.I / 2).im = -(1 / 2) := by
      simp [Complex.sub_im, Complex.div_im, Complex.I_im]
    simp only [StripUniqueness.kmsHalfStrip, Set.mem_preimage, Set.mem_Icc, him]
    norm_num
  rw [← heq hmem]
  exact hfbot t

/-- **Non-vacuity witness for `corrW_bottom_edge_real_of_kms`**: for `ξ, η ∈ 𝒦` the geometric pairing
    `⟨ξ, Jη⟩` is real (`Jη = modConj S η ∈ (i𝒦)^⊥` by `projIK_modConj_eq_zero_of_mem_K`, `ξ ∈ 𝒦`, so
    `inner_real_of_mem_K_perp_IK` applies).  This is the lower-edge value that makes the Δ-rotated-pair instance
    of `corrW_bottom_edge_real_of_kms` (`w = Δ^{it}ξ`) genuinely satisfiable — for `V = Δ` the lower edge
    `⟨Δ^{it}Jη, Δ^{it}ξ⟩` reduces to exactly `⟨Jη, ξ⟩` (unitary invariance), the conjugate of this. -/
theorem inner_mem_K_modConj_real (S : StandardSubspace H) {ξ η : H}
    (hξ : projK S ξ = ξ) (hη : projK S η = η) : (inner ℂ ξ (modConj S η)).im = 0 :=
  inner_real_of_mem_K_perp_IK S hξ (projIK_modConj_eq_zero_of_mem_K S hη)

/-- ⚠⚠ **VACUOUS PREMISE — does NOT advance the discharge** (honest correction, 2026-06-21).  This is a true
    conditional, but its hypothesis is UNSATISFIABLE for the relevant flows, so it establishes nothing toward
    `hUniq`.  Rigorous reason: `g = corrC (Jξ) = ⟨Jξ, h(z)⟩` has a FIXED second slot (forced by holomorphy).
    For `V = Δ` its top edge `⟨Δ^{it}η, Jξ⟩` is real (`Δ^{it}η ∈ 𝒦`, `Jξ ∈ (i𝒦)^⊥`).  Were the bottom edge
    *also* real, then bounded + holomorphic + real-on-both-edges ⟹ CONSTANT (Schwarz reflection + Liouville)
    ⟹ `⟨Δ^{it}η, Jξ⟩ = ⟨η, Jξ⟩ ∀ξ ∈ 𝒦`; but `Jξ` EXHAUSTS `{projIK = 0}` (`projK_modConj_eq_self_of_perp_IK`),
    so the machine-checked `eq_of_mem_K_of_inner_perp_IK` forces `Δ^{it}η = η`, i.e. `Δ = id` — absurd.  Hence
    `g`'s bottom edge is NOT real, no matching `f` exists, and the premise is vacuous (same failure class as the
    discredited full-strip `corrC_top_edge_real_of_kms_match`).  The GENUINE RvD `g` is NOT `⟨h(z), Jξ⟩`: it is
    the Prop 3.7 *device* `⟨(2−R)^{iz} R^{−iz+1/2}[·], η⟩` with the VARYING vector in the FIRST slot (bounded on
    the half-strip by Lemma 3.6 — no unbounded `R^{−1/2}`), pairing the orbit against `η` through the modular
    continuation.  That is the correct target.  `corrJ_real_on_axis` (the top edge) is UNAFFECTED and valid.
    Kept (not deleted) as a labelled record of the failed approach. -/
theorem corrJ_bottom_edge_real_of_kms (S : StandardSubspace H) {V : ℝ → (H →L[ℂ] H)} {n : ℝ}
    (hn : 0 < n) (η : H) {ξ : H}
    (hcont : Continuous (fun t => V t η)) (hbd : ∀ t, ‖V t η‖ ≤ ‖η‖)
    {f : ℂ → ℂ} {M : ℝ} (hf : DiffContOnCl ℂ f StripUniqueness.kmsHalfStripOpen)
    (hfb : ∀ z ∈ StripUniqueness.kmsHalfStrip, ‖f z‖ ≤ M)
    (hmatch : ∀ t : ℝ, f (t : ℂ) = corrC (modConj S ξ) V n η (t : ℂ))
    (hfbot : ∀ t : ℝ, (f ((t : ℂ) - Complex.I / 2)).im = 0) (t : ℝ) :
    (corrC (modConj S ξ) V n η ((t : ℂ) - Complex.I / 2)).im = 0 :=
  corrW_bottom_edge_real_of_kms hn η (modConj S ξ) hcont hbd hf hfb hmatch hfbot t

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

/-- **The device strip extension is pinned by its real-axis edge** (device Δ-side strip-uniqueness, NO regular
    window).  Any competitor `F` that is bounded-holomorphic on the half-strip and agrees with `devCorrExt` on
    the real axis `Im z = 0` coincides with it on the whole closed half-strip — by the half-strip one-edge
    uniqueness `eqOn_of_im_zero_edge_halfStrip` (Hadamard three-lines), with `devCorrExt` supplying the second
    bounded-holomorphic function (`diffContOnCl_devCorrExt`, `devCorrExt_norm_le`).  Available for EVERY
    standard subspace, unlike the `modCorrExt` analogue (`modCorrExt_eq_of_boundary`) which needs the regular
    regime.  The Δ-side half of the strip-uniqueness comparison; pinning a U-side competitor then transfers. -/
theorem devCorrExt_eqOn_of_boundary (S : StandardSubspace H) (ξ : H) {F : ℂ → ℂ} {M : ℝ}
    (hF : DiffContOnCl ℂ F (Complex.im ⁻¹' Set.Ioo (-(1 / 2) : ℝ) 0))
    (hFb : ∀ z ∈ StripUniqueness.kmsHalfStrip, ‖F z‖ ≤ M)
    (hreal : ∀ t : ℝ, F (t : ℂ) = devCorrExt S ξ (t : ℂ)) :
    Set.EqOn F (devCorrExt S ξ) StripUniqueness.kmsHalfStrip :=
  StripUniqueness.eqOn_of_im_zero_edge_halfStrip (M := max M (Real.sqrt 2 * ‖ξ‖ ^ 2)) hF
    (diffContOnCl_devCorrExt S ξ)
    (fun z hz => le_trans (hFb z hz) (le_max_left _ _))
    (fun z hz => le_trans (devCorrExt_norm_le S ξ hz.2 hz.1) (le_max_right _ _))
    (fun z hz0 => by
      have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz0])
      rw [hz']; exact hreal z.re)

end QIQTH.StandardSubspaceModular
