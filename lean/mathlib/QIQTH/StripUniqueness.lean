import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Hadamard

/-!
# The KMS strip-uniqueness principle (analytic core of one-particle KMS-uniqueness)

The wedge KMS property (the labelled input of the one-particle Bisognano–Wichmann theorem,
`QIQTH/Fock/OneParticleBW.lean`) rests on the **KMS-uniqueness lemma**: a one-parameter group whose
correlations satisfy the strip/KMS boundary conditions of the modular flow IS the modular flow.  Its analytic
heart is a uniqueness statement on the KMS strip `{0 ≤ Im z ≤ 1}` — *a bounded holomorphic function on the
strip is determined by its boundary values on the two edges*.

This file formalizes that heart, axiom-free, from Mathlib's Phragmén–Lindelöf principle on a horizontal strip
(`PhragmenLindelof.eqOn_horizontal_strip`).  It is precisely the "operator-algebra / Hardy-strip"
infrastructure that the gravity-thread scope note describes as *not yet present in Mathlib* — assembled here
for this purpose, confirming the claim was "not an impossibility, just a separate undertaking."

The remaining step toward discharging the labelled `hUniq` hypothesis (turning the KMS-uniqueness lemma from a
hypothesis into a theorem) is the Borchers/Florig reduction of the *group* equality `V = Δ^{it}` to this
boundary-value uniqueness; that reduction is the genuine next target and is documented in the BW file.
-/

namespace QIQTH.StripUniqueness

open Complex Set Filter Asymptotics
open scoped Topology Real

/-- The (closed) **KMS strip** `{0 ≤ Im z ≤ 1}` — the inverse temperature is normalised to `β = 1`. -/
def kmsStrip : Set ℂ := Complex.im ⁻¹' Set.Icc (0 : ℝ) 1

/-- The **open** KMS strip `{0 < Im z < 1}`. -/
def kmsStripOpen : Set ℂ := Complex.im ⁻¹' Set.Ioo (0 : ℝ) 1

/-- **A bounded function on the strip satisfies the Phragmén–Lindelöf growth bound trivially.**  Mathlib's
strip principle asks for a sub-double-exponential bound `‖H z‖ = O(exp(B·exp(c|Re z|)))` with `c < π/(b−a)`;
for a function bounded by `M` on the strip this holds with `c = 0`, `B = 0` (the bounding function is then the
constant `1`). -/
theorem isBigO_const_of_bdd_strip {H : ℂ → ℂ} {M : ℝ}
    (hH : ∀ z ∈ kmsStripOpen, ‖H z‖ ≤ M) :
    ∃ c < Real.pi / (1 - 0), ∃ B,
      H =O[comap (_root_.abs ∘ Complex.re) atTop ⊓ 𝓟 (Complex.im ⁻¹' Set.Ioo (0 : ℝ) 1)]
        fun z => Real.exp (B * Real.exp (c * |z.re|)) := by
  refine ⟨0, by simpa using Real.pi_pos, 0, ?_⟩
  rw [isBigO_iff]
  refine ⟨M, ?_⟩
  rw [eventually_inf_principal]
  refine Filter.Eventually.of_forall (fun z hz => ?_)
  simp only [zero_mul, Real.exp_zero, mul_one, norm_one]
  exact hH z hz

/-- **★ The KMS strip-uniqueness principle.**  Two functions that are holomorphic on the open KMS strip,
continuous up to its closure, **bounded** on the strip, and **agree on both boundary edges** (`Im = 0` and
`Im = 1`) agree on the whole closed strip.  This is the analytic core of one-particle KMS-uniqueness: a KMS
two-point correlation is determined by its boundary data.  Proved from `PhragmenLindelof.eqOn_horizontal_strip`
with the bounded ⇒ growth-bound discharge above.  Axiom-free. -/
theorem eqOn_of_bdd_holomorphic_strip {F G : ℂ → ℂ} {M : ℝ}
    (hF : DiffContOnCl ℂ F kmsStripOpen) (hG : DiffContOnCl ℂ G kmsStripOpen)
    (hFb : ∀ z ∈ kmsStripOpen, ‖F z‖ ≤ M) (hGb : ∀ z ∈ kmsStripOpen, ‖G z‖ ≤ M)
    (h0 : ∀ z : ℂ, z.im = 0 → F z = G z) (h1 : ∀ z : ℂ, z.im = 1 → F z = G z) :
    Set.EqOn F G kmsStrip :=
  PhragmenLindelof.eqOn_horizontal_strip hF (isBigO_const_of_bdd_strip hFb) hG
    (isBigO_const_of_bdd_strip hGb) h0 h1

/-- **A KMS correlation is determined by its boundary data** (strip-uniqueness, restated for the modular
setting).  If two correlation functions `F, G` on the closed KMS strip are bounded, holomorphic inside,
continuous up to the boundary, share the **same real-axis values** `F(t) = G(t)` and the **same KMS-flipped
top-edge values** `F(t + i) = G(t + i)` for every real `t`, then they coincide everywhere on the strip.  This
is the exact shape consumed by the KMS-uniqueness argument: the modular flow's correlations, and any
competitor's, are pinned by these two edge conditions. -/
theorem kms_correlation_boundary_determined {F G : ℂ → ℂ} {M : ℝ}
    (hF : DiffContOnCl ℂ F kmsStripOpen) (hG : DiffContOnCl ℂ G kmsStripOpen)
    (hFb : ∀ z ∈ kmsStripOpen, ‖F z‖ ≤ M) (hGb : ∀ z ∈ kmsStripOpen, ‖G z‖ ≤ M)
    (hreal : ∀ t : ℝ, F t = G t) (htop : ∀ t : ℝ, F ((t : ℂ) + Complex.I) = G ((t : ℂ) + Complex.I)) :
    Set.EqOn F G kmsStrip := by
  refine eqOn_of_bdd_holomorphic_strip hF hG hFb hGb (fun z hz => ?_) (fun z hz => ?_)
  · have : z = ((z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hz]
    rw [this]; exact hreal z.re
  · have : z = ((z.re : ℝ) : ℂ) + Complex.I := by
      apply Complex.ext <;> simp [hz]
    rw [this]; exact htop z.re

/-- The Phragmén–Lindelöf growth bound holds trivially for a function bounded by `M` on the open strip. -/
private theorem isBigO_bdd {H : ℂ → ℂ} {M : ℝ} (hH : ∀ z ∈ kmsStripOpen, ‖H z‖ ≤ M) :
    ∃ c < Real.pi / (1 - 0), ∃ B,
      H =O[comap (_root_.abs ∘ Complex.re) atTop ⊓ 𝓟 (Complex.im ⁻¹' Set.Ioo (0 : ℝ) 1)]
        fun z => Real.exp (B * Real.exp (c * |z.re|)) := by
  refine ⟨0, by simpa using Real.pi_pos, 0, ?_⟩
  rw [isBigO_iff]
  exact ⟨M, by rw [eventually_inf_principal]; exact Filter.Eventually.of_forall (fun z hz => by
    simpa using hH z hz)⟩

/-- **★ Max-modulus on the strip: vanishing imaginary part propagates from the edges to the interior.**
    If `g` is bounded-holomorphic on the KMS strip (`DiffContOnCl` + a uniform bound) and its **imaginary
    part vanishes on both boundary edges** (`Im g = 0` on `Im z = 0` and `Im z = 1`), then `Im g = 0` on the
    whole closed strip.  Proof: `|exp(±i·g)| = exp(∓Im g) = 1` on the edges, so by `PhragmenLindelof`'s
    horizontal-strip max-modulus principle `|exp(i·g)| ≤ 1` and `|exp(−i·g)| ≤ 1` throughout, forcing
    `Im g = 0`.  This is the reflection-free substitute for RvD's "real on both edges ⇒ constant" step (the
    crux of the KMS-uniqueness Theorem 3.8). -/
theorem im_zero_on_strip {g : ℂ → ℂ} {M : ℝ}
    (hg : DiffContOnCl ℂ g kmsStripOpen) (hgb : ∀ z ∈ kmsStripOpen, ‖g z‖ ≤ M)
    (h0 : ∀ z : ℂ, z.im = 0 → (g z).im = 0) (h1 : ∀ z : ℂ, z.im = 1 → (g z).im = 0) :
    ∀ z ∈ kmsStrip, (g z).im = 0 := by
  have key : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 → ∀ z ∈ kmsStrip,
      Real.exp (-σ * (g z).im) ≤ 1 := by
    intro σ hσ z hz
    have hφd : DiffContOnCl ℂ (fun w => Complex.exp ((σ : ℂ) * Complex.I * g w))
        (Complex.im ⁻¹' Set.Ioo (0 : ℝ) 1) :=
      Complex.differentiable_exp.comp_diffContOnCl (hg.const_smul ((σ : ℂ) * Complex.I))
    have hnorm : ∀ w, ‖Complex.exp ((σ : ℂ) * Complex.I * g w)‖ = Real.exp (-σ * (g w).im) := by
      intro w
      rw [Complex.norm_exp]
      congr 1
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hbdd : ∀ w ∈ kmsStripOpen,
        ‖Complex.exp ((σ : ℂ) * Complex.I * g w)‖ ≤ Real.exp M := by
      intro w hw
      rw [hnorm]
      refine Real.exp_le_exp.mpr (le_trans (le_abs_self _) ?_)
      have hb1 : |(g w).im| ≤ M := le_trans (RCLike.abs_im_le_norm (g w)) (hgb w hw)
      rw [abs_mul, abs_neg]
      rcases hσ with h | h <;> rw [h] <;> simpa using hb1
    have hle : ‖Complex.exp ((σ : ℂ) * Complex.I * g z)‖ ≤ 1 := by
      refine PhragmenLindelof.horizontal_strip
        (f := fun w => Complex.exp ((σ : ℂ) * Complex.I * g w)) (C := 1) hφd (isBigO_bdd hbdd)
        (fun w hw => ?_) (fun w hw => ?_) hz.1 hz.2
      · rw [hnorm, h0 w hw]; simp
      · rw [hnorm, h1 w hw]; simp
    rw [hnorm] at hle
    exact hle
  intro z hz
  have hpos := key 1 (Or.inl rfl) z hz
  have hneg := key (-1) (Or.inr rfl) z hz
  simp only [one_mul, neg_neg, neg_one_mul] at hpos hneg
  have h1' : -(g z).im ≤ 0 := by
    have : Real.exp (-(g z).im) ≤ Real.exp 0 := by rw [Real.exp_zero]; exact hpos
    exact Real.exp_le_exp.mp this
  have h2' : (g z).im ≤ 0 := by
    have : Real.exp ((g z).im) ≤ Real.exp 0 := by rw [Real.exp_zero]; exact hneg
    exact Real.exp_le_exp.mp this
  linarith

/-- **★★ Bounded-holomorphic with imaginary part zero on both strip edges ⟹ constant.**  Combining the
    max-modulus propagation `im_zero_on_strip` (`Im g = 0` throughout) with the open-mapping corollary
    `AnalyticOnNhd.eq_const_of_re_eq_const` (a holomorphic function with constant real part is constant):
    since `Re(i·g) = −Im g = 0` on the (open, connected) strip, `i·g` is constant, hence `g` is constant.
    This is RvD Theorem 3.8's "real on both edges ⇒ constant" conclusion, obtained reflection-free. -/
theorem eqConst_of_im_zero_strip {g : ℂ → ℂ} {M : ℝ}
    (hg : DiffContOnCl ℂ g kmsStripOpen) (hgb : ∀ z ∈ kmsStripOpen, ‖g z‖ ≤ M)
    (h0 : ∀ z : ℂ, z.im = 0 → (g z).im = 0) (h1 : ∀ z : ℂ, z.im = 1 → (g z).im = 0) :
    ∃ c : ℂ, ∀ z ∈ kmsStripOpen, g z = c := by
  have himz : ∀ z ∈ kmsStrip, (g z).im = 0 := im_zero_on_strip hg hgb h0 h1
  have hopen : IsOpen kmsStripOpen :=
    Complex.continuous_im.isOpen_preimage _ isOpen_Ioo
  have hconv : Convex ℝ kmsStripOpen :=
    (convex_Ioo (0 : ℝ) 1).linear_preimage Complex.imCLM.toLinearMap
  have hne : kmsStripOpen.Nonempty :=
    ⟨Complex.I / 2, by simp [kmsStripOpen, Complex.div_im]; norm_num⟩
  have hsub : kmsStripOpen ⊆ kmsStrip := fun z hz => ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hana : AnalyticOnNhd ℂ (fun z => Complex.I * g z) kmsStripOpen :=
    (hg.differentiableOn.const_mul Complex.I).analyticOnNhd hopen
  have hre : ∀ z ∈ kmsStripOpen, (Complex.I * g z).re = 0 := by
    intro z hz
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, neg_eq_zero]
    exact himz z (hsub hz)
  obtain ⟨c, hc⟩ :=
    AnalyticOnNhd.eq_const_of_re_eq_const hana hre hopen ⟨hne, hconv.isPreconnected⟩
  refine ⟨-Complex.I * c, fun z hz => ?_⟩
  rw [← hc z hz, ← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

open Complex.HadamardThreeLines in
/-- **One-edge boundary uniqueness** (Hadamard three-lines — the Schwarz-reflection-free substitute).  A
    function bounded-holomorphic on the KMS strip and *vanishing on the bottom edge* `Im z = 0` vanishes on
    the whole closed strip.  Rotating the horizontal strip to the vertical strip `re⁻¹'[0,1]` (`w ↦ I·w`) and
    applying Hadamard's three-lines theorem with edge bounds `a = 0`, `b = M` gives `‖f‖ ≤ 0^{1−θ}·M^θ = 0` on
    the interior; continuity (`Set.EqOn.of_subset_closure`) propagates the zero to the closed strip.  This is
    the analytic-continuation step RvD Theorem 3.8 obtains via Schwarz reflection (absent in Mathlib) — here
    via three-lines instead.  It pins the orbit correlation against the KMS function in the step-5 matching. -/
theorem eqZero_of_im_zero_edge {f : ℂ → ℂ} {M : ℝ}
    (hf : DiffContOnCl ℂ f kmsStripOpen) (hfb : ∀ z ∈ kmsStrip, ‖f z‖ ≤ M)
    (h0 : ∀ z : ℂ, z.im = 0 → f z = 0) :
    ∀ z ∈ kmsStrip, f z = 0 := by
  have hφim : ∀ w : ℂ, (Complex.I * w).im = w.re := fun w => by
    rw [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  have hmaps_open : Set.MapsTo (fun w => Complex.I * w) (verticalStrip 0 1) kmsStripOpen := by
    intro w hw
    rw [verticalStrip, Set.mem_preimage] at hw
    rw [kmsStripOpen, Set.mem_preimage, hφim]; exact hw
  have hmaps_closed : Set.MapsTo (fun w => Complex.I * w) (verticalClosedStrip 0 1) kmsStrip := by
    intro w hw
    rw [verticalClosedStrip, Set.mem_preimage] at hw
    rw [kmsStrip, Set.mem_preimage, hφim]; exact hw
  have hclos_v : closure (verticalStrip 0 1) = verticalClosedStrip 0 1 := by
    rw [verticalStrip, verticalClosedStrip, Complex.closure_preimage_re,
      closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hclos_k : closure kmsStripOpen = kmsStrip := by
    rw [kmsStripOpen, kmsStrip, Complex.closure_preimage_im, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hgdiff : DiffContOnCl ℂ (fun w => f (Complex.I * w)) (verticalStrip 0 1) := by
    refine ⟨hf.1.comp ((differentiable_id.const_mul Complex.I).differentiableOn) hmaps_open, ?_⟩
    rw [hclos_v]
    refine hf.2.comp ((continuous_const.mul continuous_id).continuousOn) ?_
    rw [hclos_k]; exact hmaps_closed
  have hgbdd : BddAbove ((norm ∘ fun w => f (Complex.I * w)) '' verticalClosedStrip 0 1) :=
    ⟨M, by rintro _ ⟨w, hw, rfl⟩; exact hfb _ (hmaps_closed hw)⟩
  have hre' : ∀ z : ℂ, (-Complex.I * z).re = z.im := fun z => by
    rw [Complex.mul_re]; simp
  have ha : ∀ w ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖f (Complex.I * w)‖ ≤ 0 := by
    intro w hw
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
    rw [h0 _ (by rw [hφim]; exact hw)]; simp
  have hb : ∀ w ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖f (Complex.I * w)‖ ≤ M := by
    intro w hw
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
    exact hfb _ (by rw [kmsStrip, Set.mem_preimage, hφim, hw]; exact ⟨zero_le_one, le_rfl⟩)
  have hopen : ∀ z ∈ kmsStripOpen, f z = 0 := by
    intro z hz
    rw [kmsStripOpen, Set.mem_preimage, Set.mem_Ioo] at hz
    have hw : (-Complex.I * z) ∈ verticalClosedStrip 0 1 := by
      rw [verticalClosedStrip, Set.mem_preimage, hre', Set.mem_Icc]
      exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
    have hbound := norm_le_interp_of_mem_verticalClosedStrip' (f := fun w => f (Complex.I * w))
      (z := -Complex.I * z) zero_lt_one hw hgdiff hgbdd ha hb
    simp only [hre'] at hbound
    rw [show Complex.I * (-Complex.I * z) = z by
        rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]] at hbound
    rw [Real.zero_rpow (by simp only [sub_zero, div_one]; exact sub_ne_zero.mpr (ne_of_lt hz.2).symm),
      zero_mul] at hbound
    exact norm_le_zero_iff.mp hbound
  refine Set.EqOn.of_subset_closure hopen (hclos_k ▸ hf.2) continuousOn_const
    (Set.preimage_mono Set.Ioo_subset_Icc_self) (le_of_eq hclos_k.symm)

/-- **One-edge determination** (Hadamard form): two bounded-holomorphic functions on the KMS strip that
    agree on the *bottom edge* `Im z = 0` agree on the whole closed strip.  Apply `eqZero_of_im_zero_edge`
    to `F − G`.  This is the analytic-continuation matching of RvD Theorem 3.8 step 5: the orbit correlation
    `⟨h(z), b⟩` (entire) and the KMS function from `StripKMSrvd` (which exist on the strip with the same
    real-axis values) coincide on the strip, so the KMS function's *top-edge* reality transfers to the orbit
    correlation — the `Im = 1` edge input of `corrC_orbit_eq_of_edges_real`. -/
theorem eqOn_of_im_zero_edge {F G : ℂ → ℂ} {M : ℝ}
    (hF : DiffContOnCl ℂ F kmsStripOpen) (hG : DiffContOnCl ℂ G kmsStripOpen)
    (hFb : ∀ z ∈ kmsStrip, ‖F z‖ ≤ M) (hGb : ∀ z ∈ kmsStrip, ‖G z‖ ≤ M)
    (h0 : ∀ z : ℂ, z.im = 0 → F z = G z) : Set.EqOn F G kmsStrip := fun z hz =>
  sub_eq_zero.mp (eqZero_of_im_zero_edge (hF.sub hG)
    (fun w hw => (norm_sub_le _ _).trans (add_le_add (hFb w hw) (hGb w hw)))
    (fun w hw => by rw [Pi.sub_apply, h0 w hw, sub_self]) z hz)

end QIQTH.StripUniqueness
