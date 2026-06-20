import Mathlib.Analysis.Complex.PhragmenLindelof

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

end QIQTH.StripUniqueness
