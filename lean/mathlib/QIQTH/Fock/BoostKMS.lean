/-
  A4 (QIQT_GR_DISCHARGE_PLAN.md) — assembling `StripKMSrvd(boostUnitary, 𝒦_W)` from the wedge-mode
  analytic continuation (`WedgeAnalyticity`). This file bridges the concrete rapidity integrals to the
  abstract `Lp ℂ 2` inner product and the `boostUnitary` (rapidity-translation) action.

  First increment: the `L²` inner product of two wedge modes as a concrete `∫…dθ`, and its boosted form
  `⟪η, boostUnitary a ξ⟫ = ∫ conj(Krep g θ)·Krep f (θ−a) dθ` — the real-axis edge of the KMS function.
-/
import QIQTH.Fock.OneParticleBW
import QIQTH.Fock.WedgeAnalyticity

noncomputable section

open MeasureTheory Complex

namespace QIQTH.Fock.BoostKMS

open QIQTH.Fock.Localization QIQTH.Fock.OneParticle QIQTH.Fock.OneParticleBW QIQTH.Fock.WedgeAnalyticity

/-- **The `L²` inner product of two wedge modes as a concrete rapidity integral.**
    `⟪KrepL2 f, KrepL2 g⟫ = ∫ conj(Krep m f θ)·Krep m g θ dθ` (via `L2.inner_def` + `MemLp.coeFn_toLp`). -/
theorem inner_KrepL2 (m : ℝ) {f g : V → ℂ} (hf : MemLp (Krep m f) 2 volume)
    (hg : MemLp (Krep m g) 2 volume) :
    inner ℂ (hf.toLp (Krep m f)) (hg.toLp (Krep m g))
      = ∫ θ, (starRingEnd ℂ) (Krep m f θ) * Krep m g θ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with θ hfθ hgθ
  rw [hfθ, hgθ, RCLike.inner_apply]; ring

/-- **The real-axis edge.** `⟪KrepL2 g, boostUnitary a (KrepL2 f)⟫ = ∫ conj(Krep m g θ)·Krep m f (θ−a) dθ`.
    Combines `boostUnitary_KrepL2` (boost acts by `boostTest`), `inner_KrepL2`, and the amplitude boost-
    covariance `Krep m (boostTest (−a) f) θ = Krep m f (θ−a)`. This is the orbit correlation `f(t) =
    ⟪η, V_t ξ⟫` of `StripKMSrvd` (with `V_t = boostUnitary a`, `a` the rapidity). -/
theorem inner_boostUnitary_KrepL2 (m a : ℝ) {f g : V → ℂ}
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume)
    (hbf : MemLp (Krep m (boostTest (-a) f)) 2 volume) :
    inner ℂ (hg.toLp (Krep m g)) (boostUnitary a (hf.toLp (Krep m f)))
      = ∫ θ, (starRingEnd ℂ) (Krep m g θ) * Krep m f (θ - a) := by
  rw [boostUnitary_KrepL2 m a f hf hbf, inner_KrepL2 m hg hbf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [Krep_boost]
  rw [sub_eq_add_neg]

/-- **Symmetric ↔ shifted edge (change of variables `θ ↦ θ+πt`).** The KMS function's symmetric real-axis
    form equals the boost-orbit form:
    `∫ conj(Krep g (θ+πt))·Krep f (θ−πt) dθ = ∫ conj(Krep g θ)·Krep f (θ−2πt) dθ` (translation invariance). -/
theorem symm_edge_eq_shifted (m t : ℝ) (f g : V → ℂ) :
    (∫ θ, (starRingEnd ℂ) (Krep m g (θ + Real.pi * t)) * Krep m f (θ - Real.pi * t))
      = ∫ θ, (starRingEnd ℂ) (Krep m g θ) * Krep m f (θ - 2 * Real.pi * t) := by
  rw [← MeasureTheory.integral_add_right_eq_self
    (fun θ => (starRingEnd ℂ) (Krep m g θ) * Krep m f (θ - 2 * Real.pi * t)) (Real.pi * t)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only []
  rw [show θ - Real.pi * t = θ + Real.pi * t - 2 * Real.pi * t from by ring]

/-- **The KMS top edge `f(t) = ⟪η, V_t ξ⟫` in symmetric (KMS-function) form.** Combining `symm_edge_eq_shifted`
    and `inner_boostUnitary_KrepL2`: the symmetric integral `∫ conj(Krep g (θ+πt))·Krep f (θ−πt) dθ` — the
    `t`-real value of the KMS function `F(z)=∫ conj(KrepCont g (θ+πz̄))·KrepCont f (θ−πz)` — equals
    `⟪KrepL2 g, boostUnitary(2πt) (KrepL2 f)⟫`. (Boost sign `+2π` here; `StripKMSrvd`'s `V_t=boostUnitary(−2π·)`
    is matched by orienting `t`.) -/
theorem symm_edge_eq_inner (m t : ℝ) {f g : V → ℂ}
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume)
    (hbf : MemLp (Krep m (boostTest (-(2 * Real.pi * t)) f)) 2 volume) :
    (∫ θ, (starRingEnd ℂ) (Krep m g (θ + Real.pi * t)) * Krep m f (θ - Real.pi * t))
      = inner ℂ (hg.toLp (Krep m g)) (boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f))) := by
  rw [symm_edge_eq_shifted, inner_boostUnitary_KrepL2 m (2 * Real.pi * t) hf hg hbf]

/-- **The KMS function** `F(z) = ∫ conj(KrepCont g (conj(θ+πz)))·KrepCont f (θ−πz) dθ` — the candidate
    `StripKMSrvd` witness. `H^#(θ+πz) = conj(H(conj(θ+πz)))` with `H = KrepCont g`, `Ξ = KrepCont f`; for `z`
    in the strip `{−1<Im z<0}` both factors are evaluated with imaginary part in `(0,π)` (the good damping
    region). -/
def kmsFun (m : ℝ) (f g : V → ℂ) (z : ℂ) : ℂ :=
  ∫ θ : ℝ, (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
    * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)

/-- **The KMS function on the real axis** equals the symmetric integral (via `KrepCont_ofReal`): the real-axis
    arguments are real, so each `KrepCont` collapses to `Krep` and the inner conjugation is trivial. -/
theorem kmsFun_ofReal (m : ℝ) (f g : V → ℂ) (t : ℝ) :
    kmsFun m f g (t : ℂ)
      = ∫ θ, (starRingEnd ℂ) (Krep m g (θ + Real.pi * t)) * Krep m f (θ - Real.pi * t) := by
  rw [kmsFun]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  have e1 : (θ : ℂ) + (Real.pi : ℂ) * (t : ℂ) = ((θ + Real.pi * t : ℝ) : ℂ) := by push_cast; ring
  have e2 : (θ : ℂ) - (Real.pi : ℂ) * (t : ℂ) = ((θ - Real.pi * t : ℝ) : ℂ) := by push_cast; ring
  simp only [e1, e2, Complex.conj_ofReal, KrepCont_ofReal]

/-- **The KMS top edge for `kmsFun`**: `F(t) = ⟪KrepL2 g, boostUnitary(2πt) (KrepL2 f)⟫`
    (`kmsFun_ofReal` ∘ `symm_edge_eq_inner`). -/
theorem kmsFun_ofReal_eq_inner (m t : ℝ) {f g : V → ℂ}
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume)
    (hbf : MemLp (Krep m (boostTest (-(2 * Real.pi * t)) f)) 2 volume) :
    kmsFun m f g (t : ℂ)
      = inner ℂ (hg.toLp (Krep m g)) (boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f))) := by
  rw [kmsFun_ofReal, symm_edge_eq_inner m t hf hg hbf]

/-- **The KMS bottom edge `F(t−i) = conj(F(t))`** (for real `f,g`). At `z=t−i` the `iπ`-shift puts both
    `KrepCont` arguments at imaginary part `+π`, so `KrepCont_add_pi_I` (A3) collapses each to `conj(Krep …)`:
    `F(t−i) = ∫ Krep g(θ+πt)·conj(Krep f(θ−πt)) dθ = conj(F(t))`. With the top edge (`kmsFun_ofReal_eq_inner`)
    and `⟪V_t ξ,η⟫ = conj⟪η,V_t ξ⟫`, this is the bottom-edge requirement `f(t−i) = ⟪V_t ξ,η⟫` of `StripKMSrvd`. -/
theorem kmsFun_sub_I (m : ℝ) {f g : V → ℂ} (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x)
    (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x) (t : ℝ) :
    kmsFun m f g ((t : ℂ) - Complex.I) = (starRingEnd ℂ) (kmsFun m f g (t : ℂ)) := by
  have hL : kmsFun m f g ((t : ℂ) - Complex.I)
      = ∫ θ, Krep m g (θ + Real.pi * t) * (starRingEnd ℂ) (Krep m f (θ - Real.pi * t)) := by
    rw [kmsFun]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    dsimp only
    have ag : (starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * ((t : ℂ) - Complex.I))
        = ((θ + Real.pi * t : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by
      simp only [map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    have af : (θ : ℂ) - (Real.pi : ℂ) * ((t : ℂ) - Complex.I)
        = ((θ - Real.pi * t : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [ag, af, KrepCont_add_pi_I m hgr, KrepCont_add_pi_I m hfr, Complex.conj_conj]
  rw [hL, kmsFun_ofReal, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [map_mul, Complex.conj_conj, mul_comm]

/-- **The reflected amplitude `u ↦ conj(KrepCont g(conj u))` is entire** (Schwarz reflection: `conj∘F∘conj`
    is holomorphic when `F` is). Via `DifferentiableAt.star_conj` + `differentiable_KrepCont`. This is the `g`
    factor `H^#` of the KMS-function integrand — the holomorphy ingredient for `kmsFun`. -/
theorem differentiable_reflKrepCont (m : ℝ) {g : V → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Differentiable ℂ (fun u : ℂ => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u))) := by
  have hg' : Differentiable ℂ (KrepCont m g) := differentiable_KrepCont m hg hgc
  intro z
  have h := (hg' ((starRingEnd ℂ) z)).star_conj
  rw [Complex.conj_conj] at h
  exact h

/-- **Strip-decay of the reflected amplitude** `‖reflKrep(u)‖ = ‖KrepCont g(conj u)‖` for `−π ≤ Im u ≤ 0`
    (so `Im(conj u) ∈ [0,π]`): `≤ (1/√2)(∫‖g‖)·exp(−(m sin(−Im u)δ)·cosh(Re u))`. The `g`-factor bound for the
    `kmsFun` integrand (`reflKrep(θ+πz)`, where `Im(θ+πz)=π Im z ∈(−π,0)` for `z` in the strip). -/
theorem norm_reflKrepCont_le {m : ℝ} (hm : 0 ≤ m) {g : V → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {δ : ℝ}
    (hmargin : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {u : ℂ} (him0 : -Real.pi ≤ u.im) (himπ : u.im ≤ 0) :
    ‖(starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u))‖
      ≤ 1 / Real.sqrt 2 * (∫ x, ‖g x‖) * Real.exp (-(m * Real.sin (-u.im) * δ) * Real.cosh u.re) := by
  rw [Complex.norm_conj]
  have h := norm_KrepCont_le_exp_decay_gen hm hg hgc hmargin (w := (starRingEnd ℂ) u)
    (by rw [Complex.conj_im]; linarith) (by rw [Complex.conj_im]; linarith)
  rwa [Complex.conj_im, Complex.conj_re] at h

/-- The derivative of the reflected amplitude: `deriv(u ↦ conj(KrepCont g(conj u))) u
    = conj(deriv(KrepCont g)(conj u))` (Schwarz reflection, `HasDerivAt.conj_conj`). -/
theorem deriv_reflKrepCont_eq (m : ℝ) {g : V → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (u : ℂ) :
    deriv (fun u => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u))) u
      = (starRingEnd ℂ) (deriv (KrepCont m g) ((starRingEnd ℂ) u)) := by
  have hd : HasDerivAt (KrepCont m g) (deriv (KrepCont m g) ((starRingEnd ℂ) u)) ((starRingEnd ℂ) u) :=
    (differentiable_KrepCont m hg hgc ((starRingEnd ℂ) u)).hasDerivAt
  have h := hd.conj_conj
  rw [Complex.conj_conj] at h
  exact h.deriv

/-- **Strip-decay of the reflected amplitude's derivative**: `‖deriv reflKrep(u)‖ = ‖deriv KrepCont g(conj u)‖
    ≤ (1/√2)·|m|·cosh(Re u)·exp(−(m sin(−Im u)δ)·cosh(Re u))·∫(|x₀|+|x₁|)‖g‖` for `−π≤Im u≤0`. The
    `deriv reflKrep` factor bound for the `kmsFun` integrand's `z`-derivative. -/
theorem norm_deriv_reflKrepCont_le {m : ℝ} (hm : 0 ≤ m) {g : V → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) {δ : ℝ}
    (hmargin : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {u : ℂ} (him0 : -Real.pi ≤ u.im) (himπ : u.im ≤ 0) :
    ‖deriv (fun u => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u))) u‖
      ≤ 1 / Real.sqrt 2 * (|m| * Real.cosh u.re
        * Real.exp (-(m * Real.sin (-u.im) * δ) * Real.cosh u.re) * ∫ x, (|x 0| + |x 1|) * ‖g x‖) := by
  rw [deriv_reflKrepCont_eq m hg hgc, Complex.norm_conj]
  have h := norm_deriv_KrepCont_le_exp_decay hm hg hgc hmargin (ζ := (starRingEnd ℂ) u)
    (by rw [Complex.conj_im]; linarith) (by rw [Complex.conj_im]; linarith)
  rwa [Complex.conj_im, Complex.conj_re] at h

/-- **The `kmsFun` integrand is entire in `z`** (for `f,g` continuous with compact support). The `g`-factor
    `conj(KrepCont g(conj(θ+πz)))` = `differentiable_reflKrepCont ∘ (affine)`, the `f`-factor `KrepCont f(θ−πz)`
    = `differentiable_KrepCont ∘ (affine)`; the product is differentiable. This is the per-`θ` (`h_diff`)
    ingredient for the parametric-integral holomorphy of `F` (`DiffContOnCl`). -/
theorem differentiable_kmsIntegrand (m : ℝ) {f g : V → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (θ : ℝ) :
    Differentiable ℂ (fun z : ℂ =>
      (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)) :=
  ((differentiable_reflKrepCont m hg hgc).comp (by fun_prop)).mul
    ((differentiable_KrepCont m hf hfc).comp (by fun_prop))

/-- **The `kmsFun` integrand's `z`-derivative** (product/chain rule): for fixed `θ`, the integrand
    `conj(KrepCont g(conj(θ+πz)))·KrepCont f(θ−πz)` has derivative
    `[deriv reflKrep(θ+πz)·π]·KrepCont f(θ−πz) + reflKrep(θ+πz)·[deriv KrepCont f(θ−πz)·(−π)]`.
    The `h_diff` ingredient (with explicit value, for the domination bound) of the dominated-derivative
    theorem for `kmsFun`'s holomorphy. -/
theorem hasDerivAt_kmsIntegrand_z (m : ℝ) {f g : V → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (θ : ℝ) (z : ℂ) :
    HasDerivAt (fun z => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z))
      (deriv (fun u => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u))) ((θ : ℂ) + (Real.pi : ℂ) * z)
          * (Real.pi : ℂ) * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)
        + (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
          * (deriv (KrepCont m f) ((θ : ℂ) - (Real.pi : ℂ) * z) * (-(Real.pi : ℂ)))) z := by
  have hA : HasDerivAt (fun z : ℂ => (θ : ℂ) + (Real.pi : ℂ) * z) (Real.pi : ℂ) z := by
    simpa using ((hasDerivAt_id z).const_mul (Real.pi : ℂ)).const_add (θ : ℂ)
  have hB : HasDerivAt (fun z : ℂ => (θ : ℂ) - (Real.pi : ℂ) * z) (-(Real.pi : ℂ)) z := by
    simpa using ((hasDerivAt_id z).const_mul (Real.pi : ℂ)).const_sub (θ : ℂ)
  have hgfac := ((differentiable_reflKrepCont m hg hgc ((θ : ℂ) + (Real.pi : ℂ) * z)).hasDerivAt).comp z hA
  have hffac := ((differentiable_KrepCont m hf hfc ((θ : ℂ) - (Real.pi : ℂ) * z)).hasDerivAt).comp z hB
  exact hgfac.mul hffac

/-- Norm decomposition of the integrand `z`-derivative value (from `hasDerivAt_kmsIntegrand_z`) into its four
    factors: `‖A·π·C + B·(D·(−π))‖ ≤ π·‖A‖·‖C‖ + π·‖B‖·‖D‖`. -/
theorem norm_two_term_le (A B C D : ℂ) :
    ‖A * (Real.pi : ℂ) * C + B * (D * (-(Real.pi : ℂ)))‖
      ≤ Real.pi * (‖A‖ * ‖C‖) + Real.pi * (‖B‖ * ‖D‖) := by
  refine (norm_add_le _ _).trans (le_of_eq ?_)
  simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  ring

/-- **The `kmsFun` integrand is continuous in `θ`** (for fixed `z`) — the measurability (`hF_meas`) ingredient
    for the parametric-integral holomorphy of `F`. `KrepCont` is continuous (entire), composed with the
    continuous `θ`-maps `θ↦conj(θ+πz)`, `θ↦θ−πz`, and `conj`. -/
theorem continuous_kmsIntegrand_in_theta (m : ℝ) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    Continuous (fun θ : ℝ =>
      (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)) :=
  (Complex.continuous_conj.comp ((differentiable_KrepCont m hg hgc).continuous.comp
      (Complex.continuous_conj.comp (by fun_prop)))).mul
    ((differentiable_KrepCont m hf hfc).continuous.comp (by fun_prop))

/-- `deriv reflKrep` is continuous (`reflKrep` entire ⟹ deriv analytic ⟹ continuous). -/
theorem continuous_deriv_reflKrepCont (m : ℝ) {g : V → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Continuous (deriv (fun u => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u)))) :=
  Differentiable.continuous fun z =>
    ((differentiable_reflKrepCont m hg hgc).analyticAt z).deriv.differentiableAt

/-- **The `kmsFun` integrand's `z`-derivative value is continuous in `θ`** — the `hF'_meas` (derivative
    measurability) ingredient. Each of the four factors is continuous in `θ`. -/
theorem continuous_kmsIntegrand_deriv_in_theta (m : ℝ) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    Continuous (fun θ : ℝ =>
      deriv (fun u => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u))) ((θ : ℂ) + (Real.pi : ℂ) * z)
          * (Real.pi : ℂ) * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)
        + (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
          * (deriv (KrepCont m f) ((θ : ℂ) - (Real.pi : ℂ) * z) * (-(Real.pi : ℂ)))) := by
  refine (((((continuous_deriv_reflKrepCont m hg hgc).comp (by fun_prop)).mul continuous_const).mul
    ((differentiable_KrepCont m hf hfc).continuous.comp (by fun_prop))).add ?_)
  exact (Complex.continuous_conj.comp ((differentiable_KrepCont m hg hgc).continuous.comp
      (Complex.continuous_conj.comp (by fun_prop)))).mul
    (((continuous_deriv_KrepCont m hf hfc).comp (by fun_prop)).mul continuous_const)

/-- **`hF_int` — the `kmsFun` integrand is integrable in `θ`** at an interior strip point `z` (`−1<Im z<0`).
    `‖integrand‖ = ‖reflKrep(θ+πz)‖·‖KrepCont f(θ−πz)‖ ≤ C_g·(C_f·exp(−(mσδf)·cosh(θ−π Re z)))` (the `g`-factor
    bounded, the `f`-factor decaying, `σ=sin(−π Im z)>0`), dominated by an integrable translate of
    `exp(−c·cosh)`. -/
theorem integrable_kmsIntegrand {m : ℝ} (hmpos : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δf δg : ℝ}
    (hδf : 0 < δf) (hδg : 0 < δg) (hmf : ∀ x, f x ≠ 0 → δf ≤ x 1 - x 0 ∧ δf ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δg ≤ x 1 - x 0 ∧ δg ≤ x 1 + x 0)
    {z : ℂ} (hz0 : -1 < z.im) (hz1 : z.im < 0) :
    Integrable (fun θ : ℝ =>
      (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)) := by
  have hσ : 0 < Real.sin (-(Real.pi * z.im)) := sin_neg_pi_mul_pos hz0 hz1
  set Cf : ℝ := 1 / Real.sqrt 2 * ∫ x, ‖f x‖ with hCf
  set Cg : ℝ := 1 / Real.sqrt 2 * ∫ x, ‖g x‖ with hCg
  have hCgnn : 0 ≤ Cg := by rw [hCg]; positivity
  have hcf : 0 < m * Real.sin (-(Real.pi * z.im)) * δf := by positivity
  have hdom : Integrable (fun θ : ℝ =>
      Cg * (Cf * Real.exp (-(m * Real.sin (-(Real.pi * z.im)) * δf
        * Real.cosh (θ - Real.pi * z.re))))) :=
    (((integrable_exp_neg_const_mul_cosh hcf).comp_sub_right (Real.pi * z.re)).const_mul Cf).const_mul Cg
  refine hdom.mono' (continuous_kmsIntegrand_in_theta m hf hfc hg hgc z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ => ?_)
  have him_g : ((θ : ℂ) + (Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
  have him_f : ((θ : ℂ) - (Real.pi : ℂ) * z).im = -(Real.pi * z.im) := by simp
  have hre_f : ((θ : ℂ) - (Real.pi : ℂ) * z).re = θ - Real.pi * z.re := by simp
  rw [norm_mul]
  have hgb : ‖(starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))‖ ≤ Cg := by
    refine (norm_reflKrepCont_le hmpos.le hg hgc hmg (by rw [him_g]; nlinarith [Real.pi_pos])
      (by rw [him_g]; nlinarith [Real.pi_pos])).trans ?_
    rw [← hCg]
    refine mul_le_of_le_one_right hCgnn (Real.exp_le_one_iff.mpr ?_)
    rw [him_g]
    nlinarith [mul_pos (mul_pos (mul_pos hmpos hσ) hδg)
      (Real.cosh_pos ((θ : ℂ) + (Real.pi : ℂ) * z).re)]
  have hfb : ‖KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)‖
      ≤ Cf * Real.exp (-(m * Real.sin (-(Real.pi * z.im)) * δf
        * Real.cosh (θ - Real.pi * z.re))) := by
    have h := norm_KrepCont_le_exp_decay_gen hmpos.le hf hfc hmf
      (by rw [him_f]; nlinarith [Real.pi_pos]) (by rw [him_f]; nlinarith [Real.pi_pos])
    rw [← hCf, him_f, hre_f, neg_mul] at h
    exact h
  calc ‖(starRingEnd ℂ) (KrepCont m g _)‖ * ‖KrepCont m f _‖
      ≤ Cg * (Cf * Real.exp (-(m * Real.sin (-(Real.pi * z.im)) * δf
        * Real.cosh (θ - Real.pi * z.re)))) := mul_le_mul hgb hfb (norm_nonneg _) hCgnn

/-- **★★★★ `StripKMSrvd` for a wedge generator pair, reduced to the analytic regularity of `kmsFun`.**
    For real wedge modes `ξ=KrepL2 f`, `η=KrepL2 g`, GIVEN only that the explicit KMS function `kmsFun m f g`
    is `DiffContOnCl` on the strip `{−1<Im z<0}` and bounded (`hDCC`, `hbd`), the `StripKMSrvd` `∃F` witness
    holds for this pair with `V_t = boostUnitary(2πt)`: `F=kmsFun`, top edge `F(t)=⟪η,V_t ξ⟫`
    (`kmsFun_ofReal_eq_inner`), bottom edge `F(t−i)=⟪V_t ξ,η⟫` (`kmsFun_sub_I` + `inner_conj_symm`).

    This **precisely isolates the entire remaining frontier** of the free-field BW/Hardy discharge: everything
    — the construction of `F`, both KMS edges, the `Lp` bridge, the boost-orbit identification — is DONE and
    axiom-free; what remains is the analytic regularity (`DiffContOnCl` + boundedness) of the single explicit
    function `kmsFun m f g`, of which the holomorphy ingredients (`differentiable_kmsIntegrand`,
    `continuous_kmsIntegrand_in_theta`, `integrable_cosh_mul_exp_neg_const_mul_cosh`) are in hand. -/
theorem stripKMSrvd_pair_of_regularity (m : ℝ) {f g : V → ℂ}
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume)
    (hbf : ∀ t : ℝ, MemLp (Krep m (boostTest (-(2 * Real.pi * t)) f)) 2 volume)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hDCC : DiffContOnCl ℂ (kmsFun m f g) (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0))
    (hbd : ∃ M : ℝ, ∀ z : ℂ, ‖kmsFun m f g z‖ ≤ M) :
    ∃ F : ℂ → ℂ, DiffContOnCl ℂ F (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) ∧
      (∃ M : ℝ, ∀ z : ℂ, ‖F z‖ ≤ M) ∧
      (∀ t : ℝ, F t = inner ℂ (hg.toLp (Krep m g)) (boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f)))) ∧
      (∀ t : ℝ, F ((t : ℂ) - Complex.I)
        = inner ℂ (boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f))) (hg.toLp (Krep m g))) := by
  refine ⟨kmsFun m f g, hDCC, hbd, fun t => kmsFun_ofReal_eq_inner m t hf hg (hbf t), fun t => ?_⟩
  rw [kmsFun_sub_I m hfr hgr t, kmsFun_ofReal_eq_inner m t hf hg (hbf t)]
  exact inner_conj_symm _ _

/-- **Decay-rate lower bound over a strip-interior ball.** If `closedBall z₀ ε ⊆ {−1<Im<0}`, the decay rate
    `σ(z)=sin(−π·Im z)` has a positive lower bound `σmin` on the ball (continuous positive fn on a compact set
    attains a positive min). The `c₀` for `cosh_shift_exp_le` in the `h_bound` assembly. -/
theorem exists_sin_min {z₀ : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ z ∈ Metric.closedBall z₀ ε, -1 < z.im ∧ z.im < 0) :
    ∃ σmin : ℝ, 0 < σmin ∧ ∀ z ∈ Metric.closedBall z₀ ε, σmin ≤ Real.sin (-(Real.pi * z.im)) := by
  have hcont : ContinuousOn (fun z : ℂ => Real.sin (-(Real.pi * z.im)))
      (Metric.closedBall z₀ ε) := by fun_prop
  obtain ⟨z₁, hz₁mem, hz₁min⟩ :=
    (isCompact_closedBall z₀ ε).exists_isMinOn (Metric.nonempty_closedBall.mpr hε.le) hcont
  rw [isMinOn_iff] at hz₁min
  obtain ⟨him0, him1⟩ := hball z₁ hz₁mem
  exact ⟨Real.sin (-(Real.pi * z₁.im)), sin_neg_pi_mul_pos him0 him1, hz₁min⟩

/-- **`h_bound` term 1**: `‖deriv reflKrep(θ+πz)‖·‖KrepCont f(θ−πz)‖ ≤ Cdg·Cf·(e^{πR}·cosh θ·exp(−κ·cosh θ))`
    (`κ = m σmin δ e^{−πR}`), via `prod_norm_bound_cosh_shift` (the `deriv reflKrep` factor decays in
    `cosh(θ+π Re z)`, the `KrepCont f` factor is bounded by `Cf`). -/
theorem norm_term1_le {m : ℝ} (hmpos : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {z : ℂ} (hz0 : -1 < z.im) (hz1 : z.im < 0) {σmin R : ℝ} (hσmin : 0 < σmin)
    (hσ : σmin ≤ Real.sin (-(Real.pi * z.im))) (hR : |z.re| ≤ R) (θ : ℝ) :
    ‖deriv (fun u => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u))) ((θ : ℂ) + (Real.pi : ℂ) * z)‖
        * ‖KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)‖
      ≤ 1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖)
        * (Real.exp (Real.pi * R) * Real.cosh θ
          * Real.exp (-(m * σmin * δ * Real.exp (-(Real.pi * R)) * Real.cosh θ))) := by
  have him_g : ((θ : ℂ) + (Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
  have hre_g : ((θ : ℂ) + (Real.pi : ℂ) * z).re = θ + Real.pi * z.re := by simp
  have him_f : ((θ : ℂ) - (Real.pi : ℂ) * z).im = -(Real.pi * z.im) := by simp
  have hσz : 0 < Real.sin (-(Real.pi * z.im)) := sin_neg_pi_mul_pos hz0 hz1
  have hna : ‖deriv (fun u => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u))) ((θ : ℂ) + (Real.pi : ℂ) * z)‖
      ≤ 1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖g x‖)
        * (Real.cosh (θ + Real.pi * z.re)
          * Real.exp (-(m * Real.sin (-(Real.pi * z.im)) * δ * Real.cosh (θ + Real.pi * z.re)))) := by
    have h := norm_deriv_reflKrepCont_le hmpos.le hg hgc hmg
      (u := (θ : ℂ) + (Real.pi : ℂ) * z) (by rw [him_g]; nlinarith [Real.pi_pos])
      (by rw [him_g]; nlinarith [Real.pi_pos])
    rw [him_g, hre_g, neg_mul] at h
    exact h.trans_eq (by ring)
  have hnb : ‖KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)‖ ≤ 1 / Real.sqrt 2 * ∫ x, ‖f x‖ := by
    refine (norm_KrepCont_le_exp_decay_gen hmpos.le hf hfc hmf
      (by rw [him_f]; nlinarith [Real.pi_pos]) (by rw [him_f]; nlinarith [Real.pi_pos])).trans ?_
    refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
    rw [him_f]
    nlinarith [mul_pos (mul_pos (mul_pos hmpos hσz) hδ)
      (Real.cosh_pos ((θ : ℂ) - (Real.pi : ℂ) * z).re)]
  refine prod_norm_bound_cosh_shift (s := Real.pi * z.re) (S := Real.pi * R)
    (c := m * Real.sin (-(Real.pi * z.im)) * δ) (c₀ := m * σmin * δ) hna hnb (norm_nonneg _)
    (by positivity) (by positivity) ?_ (by positivity) ?_
  · rw [abs_mul, abs_of_nonneg Real.pi_pos.le]; nlinarith [hR, Real.pi_pos, abs_nonneg z.re]
  · nlinarith [mul_le_mul_of_nonneg_left hσ (mul_pos hmpos hδ).le, hδ, hmpos]

/-- **`h_bound` term 2**: `‖reflKrep(θ+πz)‖·‖deriv KrepCont f(θ−πz)‖ ≤ Cdf·Cg·(e^{πR}·cosh θ·exp(−κ·cosh θ))`
    (mirror of term 1, with the `deriv` on the `f`-factor: `deriv KrepCont f` decaying in `cosh(θ−π Re z)`,
    `reflKrep` bounded by `Cg`). -/
theorem norm_term2_le {m : ℝ} (hmpos : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {z : ℂ} (hz0 : -1 < z.im) (hz1 : z.im < 0) {σmin R : ℝ} (hσmin : 0 < σmin)
    (hσ : σmin ≤ Real.sin (-(Real.pi * z.im))) (hR : |z.re| ≤ R) (θ : ℝ) :
    ‖(starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))‖
        * ‖deriv (KrepCont m f) ((θ : ℂ) - (Real.pi : ℂ) * z)‖
      ≤ 1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖f x‖) * (1 / Real.sqrt 2 * ∫ x, ‖g x‖)
        * (Real.exp (Real.pi * R) * Real.cosh θ
          * Real.exp (-(m * σmin * δ * Real.exp (-(Real.pi * R)) * Real.cosh θ))) := by
  have him_g : ((θ : ℂ) + (Real.pi : ℂ) * z).im = Real.pi * z.im := by simp
  have him_f : ((θ : ℂ) - (Real.pi : ℂ) * z).im = -(Real.pi * z.im) := by simp
  have hre_f : ((θ : ℂ) - (Real.pi : ℂ) * z).re = θ - Real.pi * z.re := by simp
  have hσz : 0 < Real.sin (-(Real.pi * z.im)) := sin_neg_pi_mul_pos hz0 hz1
  have hna : ‖deriv (KrepCont m f) ((θ : ℂ) - (Real.pi : ℂ) * z)‖
      ≤ 1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖f x‖)
        * (Real.cosh (θ - Real.pi * z.re)
          * Real.exp (-(m * Real.sin (-(Real.pi * z.im)) * δ * Real.cosh (θ - Real.pi * z.re)))) := by
    have h := norm_deriv_KrepCont_le_exp_decay hmpos.le hf hfc hmf
      (ζ := (θ : ℂ) - (Real.pi : ℂ) * z) (by rw [him_f]; nlinarith [Real.pi_pos])
      (by rw [him_f]; nlinarith [Real.pi_pos])
    rw [him_f, hre_f, neg_mul] at h
    exact h.trans_eq (by ring)
  have hnb : ‖(starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))‖
      ≤ 1 / Real.sqrt 2 * ∫ x, ‖g x‖ := by
    refine (norm_reflKrepCont_le hmpos.le hg hgc hmg (by rw [him_g]; nlinarith [Real.pi_pos])
      (by rw [him_g]; nlinarith [Real.pi_pos])).trans ?_
    refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
    rw [him_g]
    nlinarith [mul_pos (mul_pos (mul_pos hmpos hσz) hδ)
      (Real.cosh_pos ((θ : ℂ) + (Real.pi : ℂ) * z).re)]
  rw [mul_comm]
  refine prod_norm_bound_cosh_shift (s := -(Real.pi * z.re)) (S := Real.pi * R)
    (c := m * Real.sin (-(Real.pi * z.im)) * δ) (c₀ := m * σmin * δ) hna hnb (norm_nonneg _)
    (by positivity) (by positivity) ?_ (by positivity) ?_
  · rw [abs_neg, abs_mul, abs_of_nonneg Real.pi_pos.le]; nlinarith [hR, Real.pi_pos, abs_nonneg z.re]
  · nlinarith [mul_le_mul_of_nonneg_left hσ (mul_pos hmpos hδ).le, hδ, hmpos]

/-- **The `h_bound` pointwise content**: `‖F'(z,θ)‖ ≤ π·(Cdg·Cf + Cdf·Cg)·(e^{πR}·cosh θ·exp(−κ·cosh θ))`,
    `κ = m σmin δ e^{−πR}` — a `z`-independent (for the ball) integrable-in-`θ` bound on the integrand
    `z`-derivative. Combines `norm_two_term_le` + `norm_term1_le` + `norm_term2_le`. -/
theorem kmsIntegrand_deriv_bound {m : ℝ} (hmpos : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {z : ℂ} (hz0 : -1 < z.im) (hz1 : z.im < 0) {σmin R : ℝ} (hσmin : 0 < σmin)
    (hσ : σmin ≤ Real.sin (-(Real.pi * z.im))) (hR : |z.re| ≤ R) (θ : ℝ) :
    ‖deriv (fun u => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u))) ((θ : ℂ) + (Real.pi : ℂ) * z)
          * (Real.pi : ℂ) * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)
        + (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
          * (deriv (KrepCont m f) ((θ : ℂ) - (Real.pi : ℂ) * z) * (-(Real.pi : ℂ)))‖
      ≤ Real.pi * ((1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖)
            + 1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖f x‖) * (1 / Real.sqrt 2 * ∫ x, ‖g x‖))
          * (Real.exp (Real.pi * R) * Real.cosh θ
            * Real.exp (-(m * σmin * δ * Real.exp (-(Real.pi * R)) * Real.cosh θ)))) := by
  refine (norm_two_term_le _ _ _ _).trans ?_
  have h1 := norm_term1_le hmpos hf hfc hg hgc hδ hmf hmg hz0 hz1 hσmin hσ hR θ
  have h2 := norm_term2_le hmpos hf hfc hg hgc hδ hmf hmg hz0 hz1 hσmin hσ hR θ
  nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h1),
    mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h2)]

/-- **★★★★★ `kmsFun m f g` is differentiable at every interior strip point** (`−1<Im z₀<0`), for `f,g`
    continuous with compact support strictly inside the wedge (uniform margin `δ>0`). The holomorphy half of
    `DiffContOnCl`. Assembles the six dominated-derivative hypotheses (`hF_meas`, `hF_int`, `hF'_meas`,
    `h_diff`, `h_bound`, `bound_integrable` — all proven) over a strip-interior ball (with `σ_min` from
    `exists_sin_min`, `R` from the ball). -/
theorem kmsFun_differentiableAt {m : ℝ} (hmpos : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {z₀ : ℂ} (hz₀0 : -1 < z₀.im) (hz₀1 : z₀.im < 0) :
    DifferentiableAt ℂ (kmsFun m f g) z₀ := by
  set ε : ℝ := min (z₀.im + 1) (-z₀.im) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; have := lt_min (by linarith : (0:ℝ) < z₀.im + 1) (by linarith : (0:ℝ) < -z₀.im); linarith
  have hdist : ∀ z ∈ Metric.closedBall z₀ ε, |z.im - z₀.im| ≤ ε ∧ |z.re - z₀.re| ≤ ε := by
    intro z hz
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    refine ⟨?_, ?_⟩
    · calc |z.im - z₀.im| = |(z - z₀).im| := by rw [Complex.sub_im]
        _ ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
        _ ≤ ε := hz
    · calc |z.re - z₀.re| = |(z - z₀).re| := by rw [Complex.sub_re]
        _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
        _ ≤ ε := hz
  have hball_im : ∀ z ∈ Metric.closedBall z₀ ε, -1 < z.im ∧ z.im < 0 := by
    intro z hz
    obtain ⟨him, _⟩ := hdist z hz
    rw [abs_le] at him
    constructor <;> [nlinarith [min_le_left (z₀.im + 1) (-z₀.im)]; nlinarith [min_le_right (z₀.im + 1) (-z₀.im)]]
  obtain ⟨σmin, hσmin, hσ⟩ := exists_sin_min hε hball_im
  set R : ℝ := |z₀.re| + ε with hRdef
  have hR : ∀ z ∈ Metric.closedBall z₀ ε, |z.re| ≤ R := by
    intro z hz
    obtain ⟨_, hre⟩ := hdist z hz
    rw [hRdef]; rw [abs_le] at hre; cases abs_cases z.re <;> cases abs_cases z₀.re <;> linarith
  have hballmem : ∀ z ∈ Metric.ball z₀ ε, z ∈ Metric.closedBall z₀ ε := fun z hz =>
    Metric.ball_subset_closedBall hz
  have hκ : 0 < m * σmin * δ * Real.exp (-(Real.pi * R)) := by positivity
  have hbi : Integrable (fun θ : ℝ => Real.pi
      * ((1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖)
          + 1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖f x‖) * (1 / Real.sqrt 2 * ∫ x, ‖g x‖))
        * (Real.exp (Real.pi * R) * Real.cosh θ
          * Real.exp (-(m * σmin * δ * Real.exp (-(Real.pi * R)) * Real.cosh θ))))) := by
    have heq : (fun θ : ℝ => Real.pi
        * ((1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖)
            + 1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖f x‖) * (1 / Real.sqrt 2 * ∫ x, ‖g x‖))
          * (Real.exp (Real.pi * R) * Real.cosh θ
            * Real.exp (-(m * σmin * δ * Real.exp (-(Real.pi * R)) * Real.cosh θ)))))
        = fun θ : ℝ => (Real.pi
            * (1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖)
              + 1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖f x‖) * (1 / Real.sqrt 2 * ∫ x, ‖g x‖))
            * Real.exp (Real.pi * R))
          * (Real.cosh θ
            * Real.exp (-(m * σmin * δ * Real.exp (-(Real.pi * R)) * Real.cosh θ))) := by funext θ; ring
    rw [heq]
    exact (integrable_cosh_mul_exp_neg_const_mul_cosh hκ).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℝ))
    (F := fun z θ => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z))
    (F' := fun z θ => deriv (fun u => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u)))
          ((θ : ℂ) + (Real.pi : ℂ) * z) * (Real.pi : ℂ) * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)
        + (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
          * (deriv (KrepCont m f) ((θ : ℂ) - (Real.pi : ℂ) * z) * (-(Real.pi : ℂ))))
    (bound := _) (s := Metric.ball z₀ ε) (x₀ := z₀) (Metric.ball_mem_nhds z₀ hε)
    (Filter.Eventually.of_forall fun z =>
      (continuous_kmsIntegrand_in_theta m hf hfc hg hgc z).aestronglyMeasurable)
    (integrable_kmsIntegrand hmpos hf hfc hg hgc hδ hδ hmf hmg hz₀0 hz₀1)
    (continuous_kmsIntegrand_deriv_in_theta m hf hfc hg hgc z₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ z hz =>
      kmsIntegrand_deriv_bound hmpos hf hfc hg hgc hδ hmf hmg (hball_im z (hballmem z hz)).1
        (hball_im z (hballmem z hz)).2 hσmin (hσ z (hballmem z hz)) (hR z (hballmem z hz)) θ)
    hbi
    (Filter.Eventually.of_forall fun θ z _ => hasDerivAt_kmsIntegrand_z m hf hfc hg hgc θ z)
  exact key.2.differentiableAt

/-- **`kmsFun m f g` is holomorphic on the whole open strip** `{−1<Im z<0}` — the `DifferentiableOn`
    half of `DiffContOnCl`, an immediate corollary of `kmsFun_differentiableAt` (the strip is open, so
    `DifferentiableAt` at each point gives `DifferentiableWithinAt`). -/
theorem kmsFun_differentiableOn {m : ℝ} (hmpos : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0) :
    DifferentiableOn ℂ (kmsFun m f g) (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) := by
  intro z hz
  rw [Set.mem_preimage, Set.mem_Ioo] at hz
  exact (kmsFun_differentiableAt hmpos hf hfc hg hgc hδ hmf hmg hz.1 hz.2).differentiableWithinAt

/-- **Cauchy–Schwarz for a conjugate-bilinear `L²` integral.** For `A, B ∈ L²(dθ)`,
    `‖∫ conj(A θ)·B θ‖ ≤ ‖A‖_{L²}·‖B‖_{L²}`. The abstract estimate behind the boundedness of `kmsFun`:
    `‖∫ F‖ ≤ ∫ ‖F‖` then Hölder (`integral_mul_le_Lp_mul_Lq_of_nonneg`, `p=q=2`). -/
theorem norm_integral_conj_mul_le_l2 {A B : ℝ → ℂ} (hA : MemLp A 2 volume) (hB : MemLp B 2 volume) :
    ‖∫ θ : ℝ, (starRingEnd ℂ) (A θ) * B θ‖
      ≤ Real.sqrt (∫ θ : ℝ, ‖A θ‖ ^ 2) * Real.sqrt (∫ θ : ℝ, ‖B θ‖ ^ 2) := by
  have hmA : MemLp (fun θ => ‖A θ‖) (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num [ENNReal.ofReal_ofNat]]; exact hA.norm
  have hmB : MemLp (fun θ => ‖B θ‖) (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num [ENNReal.ofReal_ofNat]]; exact hB.norm
  have hpow : ∀ h : ℝ → ℂ, (∫ θ : ℝ, ‖h θ‖ ^ (2 : ℝ)) = ∫ θ : ℝ, ‖h θ‖ ^ 2 := by
    intro h
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    show ‖h θ‖ ^ (2 : ℝ) = ‖h θ‖ ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  calc ‖∫ θ : ℝ, (starRingEnd ℂ) (A θ) * B θ‖
      ≤ ∫ θ : ℝ, ‖(starRingEnd ℂ) (A θ) * B θ‖ := norm_integral_le_integral_norm _
    _ = ∫ θ : ℝ, ‖A θ‖ * ‖B θ‖ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        show ‖(starRingEnd ℂ) (A θ) * B θ‖ = ‖A θ‖ * ‖B θ‖
        rw [norm_mul, RCLike.norm_conj]
    _ ≤ (∫ θ : ℝ, ‖A θ‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫ θ : ℝ, ‖B θ‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
          (Filter.Eventually.of_forall fun θ => norm_nonneg _)
          (Filter.Eventually.of_forall fun θ => norm_nonneg _) hmA hmB
    _ = Real.sqrt (∫ θ : ℝ, ‖A θ‖ ^ 2) * Real.sqrt (∫ θ : ℝ, ‖B θ‖ ^ 2) := by
        rw [hpow A, hpow B, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **Cauchy–Schwarz bound for `kmsFun`** (interior `z`): `‖kmsFun m f g z‖` is bounded by the product of
    the two strip-slice `L²` norms. Reduces the boundedness of `kmsFun` (the remaining frontier of the
    `StripKMSrvd` witness) to **uniform control of the slice `L²` norms** across the strip — the correct
    Hardy-space decomposition. Each slice is in `L²` via `memLp_KrepCont_affine` (`Im = −π·z.im ∈ (0,π)`). -/
theorem norm_kmsFun_le_l2_product {m : ℝ} (hmpos : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {z : ℂ} (hz0 : -1 < z.im) (hz1 : z.im < 0) :
    ‖kmsFun m f g z‖
      ≤ Real.sqrt (∫ θ : ℝ, ‖KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z))‖ ^ 2)
        * Real.sqrt (∫ θ : ℝ, ‖KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)‖ ^ 2) := by
  have h0 : 0 < Real.pi * (-z.im) := by
    have hz : 0 < -z.im := by linarith
    positivity
  have hπlt : Real.pi * (-z.im) < Real.pi := by
    have h1 : -z.im < 1 := by linarith
    nlinarith [Real.pi_pos]
  have hgim : ((Real.pi : ℂ) * (starRingEnd ℂ z)).im = Real.pi * (-z.im) := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im]; ring
  have hfim : (-((Real.pi : ℂ) * z)).im = Real.pi * (-z.im) := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hMemA : MemLp (fun θ : ℝ =>
      KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z))) 2 volume := by
    have hfun : (fun θ : ℝ => KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        = fun θ : ℝ => KrepCont m g ((θ : ℂ) + (Real.pi : ℂ) * (starRingEnd ℂ z)) := by
      funext θ; congr 1; rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [hfun]
    exact memLp_KrepCont_affine hmpos hg hgc hδ hmg (by rw [hgim]; exact h0) (by rw [hgim]; exact hπlt)
  have hMemB : MemLp (fun θ : ℝ => KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)) 2 volume := by
    have hfun : (fun θ : ℝ => KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z))
        = fun θ : ℝ => KrepCont m f ((θ : ℂ) + (-((Real.pi : ℂ) * z))) := by
      funext θ; rw [sub_eq_add_neg]
    rw [hfun]
    exact memLp_KrepCont_affine hmpos hf hfc hδ hmf (by rw [hfim]; exact h0) (by rw [hfim]; exact hπlt)
  rw [kmsFun]
  exact norm_integral_conj_mul_le_l2 hMemA hMemB

/-- **Top-edge uniform bound** (`Im z = 0`). `‖kmsFun m f g t‖ ≤ ‖KrepL2 g‖·‖KrepL2 f‖` for all real `t`:
    the top edge is the inner product `⟪KrepL2 g, boostUnitary(2πt) (KrepL2 f)⟫` (`kmsFun_ofReal_eq_inner`),
    Cauchy–Schwarz (`norm_inner_le_norm`) and the **boost isometry** (`LinearIsometryEquiv.norm_map`) give a
    bound **independent of `t`** — the edge constant `B` the three-lines/Phragmén–Lindelöf argument propagates
    into the strip interior. -/
theorem norm_kmsFun_ofReal_le (m t : ℝ) {f g : V → ℂ}
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume)
    (hbf : MemLp (Krep m (boostTest (-(2 * Real.pi * t)) f)) 2 volume) :
    ‖kmsFun m f g (t : ℂ)‖ ≤ ‖hg.toLp (Krep m g)‖ * ‖hf.toLp (Krep m f)‖ := by
  rw [kmsFun_ofReal_eq_inner m t hf hg hbf]
  calc ‖inner ℂ (hg.toLp (Krep m g)) (boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f)))‖
      ≤ ‖hg.toLp (Krep m g)‖ * ‖boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f))‖ :=
        norm_inner_le_norm _ _
    _ = ‖hg.toLp (Krep m g)‖ * ‖hf.toLp (Krep m f)‖ := by rw [LinearIsometryEquiv.norm_map]

/-- **Bottom-edge uniform bound** (`Im z = −1`). Same constant `B = ‖KrepL2 g‖·‖KrepL2 f‖`, via
    `kmsFun_sub_I` (`F(t−i) = conj F(t)`, so equal norm) and `norm_kmsFun_ofReal_le`. With the top edge this
    bounds `kmsFun` uniformly on **both** boundary lines of the strip `{−1<Im z<0}`. -/
theorem norm_kmsFun_sub_I_le (m t : ℝ) {f g : V → ℂ} (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x)
    (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume)
    (hbf : MemLp (Krep m (boostTest (-(2 * Real.pi * t)) f)) 2 volume) :
    ‖kmsFun m f g ((t : ℂ) - Complex.I)‖ ≤ ‖hg.toLp (Krep m g)‖ * ‖hf.toLp (Krep m f)‖ := by
  rw [kmsFun_sub_I m hfr hgr t, RCLike.norm_conj]
  exact norm_kmsFun_ofReal_le m t hf hg hbf

/-- **θ-truncated KMS function** (cutoff `R`): the same integrand as `kmsFun`, but integrated over the compact
    rapidity window `θ ∈ [−R,R]`. The truncation device (GPT-5.5): the compact θ-domain makes `kmsFunCut R`
    holomorphic on the open strip, continuous on the closed strip, and trivially BOUNDED there — with **no**
    logarithmic blow-up — so Hadamard three-lines bounds it by the edge constant `B` for every `R`, and
    `R→∞` (dominated convergence) transfers the bound to `kmsFun`. -/
def kmsFunCut (m : ℝ) (f g : V → ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  ∫ θ in Set.Icc (-R) R, (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
    * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)

/-- **Trivial closed-strip bound for `kmsFunCut`** (`Im z ∈ [−1,0]`, `R ≥ 0`): `‖kmsFunCut R z‖ ≤ C_g·C_f·2R`
    with `C_h = (1/√2)∫‖h‖`. Each `KrepCont` factor has argument imaginary part `−π·Im z ∈ [0,π]`, so the plain
    bound `norm_KrepCont_le_const` applies; integrate the constant `C_g·C_f` over `[−R,R]` (measure `2R`). This
    is the `BddAbove` Hadamard needs — finite for each `R`, the log-blowup absent. -/
theorem norm_kmsFunCut_le {m : ℝ} (hm : 0 ≤ m) {f g : V → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    ‖kmsFunCut m f g R z‖
      ≤ (1 / Real.sqrt 2 * ∫ x, ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖) * (2 * R) := by
  have him0 : (0 : ℝ) ≤ -(Real.pi * z.im) := by
    have : 0 ≤ -z.im := by linarith
    have := Real.pi_pos; nlinarith
  have himπ : -(Real.pi * z.im) ≤ Real.pi := by
    have h1 : -z.im ≤ 1 := by linarith
    nlinarith [Real.pi_pos]
  -- imaginary parts of the two KrepCont arguments both equal −(π·z.im)
  have hbound : ∀ θ : ℝ, ‖(starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)‖
      ≤ (1 / Real.sqrt 2 * ∫ x, ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖) := by
    intro θ
    rw [norm_mul, RCLike.norm_conj]
    have hgim : ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)).im = -(Real.pi * z.im) := by
      simp only [Complex.conj_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im]; ring
    have hfim : ((θ : ℂ) - (Real.pi : ℂ) * z).im = -(Real.pi * z.im) := by
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
    refine mul_le_mul ?_ ?_ (norm_nonneg _) ?_
    · exact norm_KrepCont_le_const hm hg hgc hδ hmg (by rw [hgim]; exact him0) (by rw [hgim]; exact himπ)
    · exact norm_KrepCont_le_const hm hf hfc hδ hmf (by rw [hfim]; exact him0) (by rw [hfim]; exact himπ)
    · have : 0 ≤ ∫ x, ‖g x‖ := integral_nonneg (fun x => norm_nonneg _)
      positivity
  rw [kmsFunCut]
  refine (norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top (fun x _ => hbound x)).trans_eq ?_
  rw [Real.volume_real_Icc_of_le (by linarith : (-R : ℝ) ≤ R)]
  ring

/-- **`kmsFunCut Rc` is differentiable at every interior strip point** (`−1<Im z₀<0`) — the open-strip
    (`DifferentiableOn`) half of `DiffContOnCl` for the truncated function. Same dominated-derivative assembly
    as `kmsFun_differentiableAt`, but over the restricted measure `volume.restrict [−Rc,Rc]`; the interior
    `σ`-damped bound (`kmsIntegrand_deriv_bound`) and integrability transfer to the restricted measure via
    `.integrableOn`. -/
theorem kmsFunCut_differentiableAt {m : ℝ} (hmpos : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (Rc : ℝ) {z₀ : ℂ} (hz₀0 : -1 < z₀.im) (hz₀1 : z₀.im < 0) :
    DifferentiableAt ℂ (kmsFunCut m f g Rc) z₀ := by
  set ε : ℝ := min (z₀.im + 1) (-z₀.im) / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    have := lt_min (by linarith : (0:ℝ) < z₀.im + 1) (by linarith : (0:ℝ) < -z₀.im); linarith
  have hdist : ∀ z ∈ Metric.closedBall z₀ ε, |z.im - z₀.im| ≤ ε ∧ |z.re - z₀.re| ≤ ε := by
    intro z hz
    rw [Metric.mem_closedBall, Complex.dist_eq] at hz
    refine ⟨?_, ?_⟩
    · calc |z.im - z₀.im| = |(z - z₀).im| := by rw [Complex.sub_im]
        _ ≤ ‖z - z₀‖ := Complex.abs_im_le_norm _
        _ ≤ ε := hz
    · calc |z.re - z₀.re| = |(z - z₀).re| := by rw [Complex.sub_re]
        _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
        _ ≤ ε := hz
  have hball_im : ∀ z ∈ Metric.closedBall z₀ ε, -1 < z.im ∧ z.im < 0 := by
    intro z hz
    obtain ⟨him, _⟩ := hdist z hz
    rw [abs_le] at him
    constructor <;> [nlinarith [min_le_left (z₀.im + 1) (-z₀.im)];
      nlinarith [min_le_right (z₀.im + 1) (-z₀.im)]]
  obtain ⟨σmin, hσmin, hσ⟩ := exists_sin_min hε hball_im
  set Rre : ℝ := |z₀.re| + ε with hRredef
  have hRre : ∀ z ∈ Metric.closedBall z₀ ε, |z.re| ≤ Rre := by
    intro z hz
    obtain ⟨_, hre⟩ := hdist z hz
    rw [hRredef]; rw [abs_le] at hre; cases abs_cases z.re <;> cases abs_cases z₀.re <;> linarith
  have hballmem : ∀ z ∈ Metric.ball z₀ ε, z ∈ Metric.closedBall z₀ ε := fun z hz =>
    Metric.ball_subset_closedBall hz
  have hκ : 0 < m * σmin * δ * Real.exp (-(Real.pi * Rre)) := by positivity
  have hbi : Integrable (fun θ : ℝ => Real.pi
      * ((1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖)
          + 1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖f x‖) * (1 / Real.sqrt 2 * ∫ x, ‖g x‖))
        * (Real.exp (Real.pi * Rre) * Real.cosh θ
          * Real.exp (-(m * σmin * δ * Real.exp (-(Real.pi * Rre)) * Real.cosh θ)))))
      (volume.restrict (Set.Icc (-Rc) Rc)) := by
    have heq : (fun θ : ℝ => Real.pi
        * ((1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖)
            + 1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖f x‖) * (1 / Real.sqrt 2 * ∫ x, ‖g x‖))
          * (Real.exp (Real.pi * Rre) * Real.cosh θ
            * Real.exp (-(m * σmin * δ * Real.exp (-(Real.pi * Rre)) * Real.cosh θ)))))
        = fun θ : ℝ => (Real.pi
            * (1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖)
              + 1 / Real.sqrt 2 * (|m| * ∫ x, (|x 0| + |x 1|) * ‖f x‖) * (1 / Real.sqrt 2 * ∫ x, ‖g x‖))
            * Real.exp (Real.pi * Rre))
          * (Real.cosh θ
            * Real.exp (-(m * σmin * δ * Real.exp (-(Real.pi * Rre)) * Real.cosh θ))) := by funext θ; ring
    rw [heq]
    exact ((integrable_cosh_mul_exp_neg_const_mul_cosh hκ).const_mul _).integrableOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Icc (-Rc) Rc))
    (F := fun z θ => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z))
    (F' := fun z θ => deriv (fun u => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u)))
          ((θ : ℂ) + (Real.pi : ℂ) * z) * (Real.pi : ℂ) * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)
        + (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
          * (deriv (KrepCont m f) ((θ : ℂ) - (Real.pi : ℂ) * z) * (-(Real.pi : ℂ))))
    (bound := _) (s := Metric.ball z₀ ε) (x₀ := z₀) (Metric.ball_mem_nhds z₀ hε)
    (Filter.Eventually.of_forall fun z =>
      (continuous_kmsIntegrand_in_theta m hf hfc hg hgc z).aestronglyMeasurable)
    (integrable_kmsIntegrand hmpos hf hfc hg hgc hδ hδ hmf hmg hz₀0 hz₀1).integrableOn
    (continuous_kmsIntegrand_deriv_in_theta m hf hfc hg hgc z₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ z hz =>
      kmsIntegrand_deriv_bound hmpos hf hfc hg hgc hδ hmf hmg (hball_im z (hballmem z hz)).1
        (hball_im z (hballmem z hz)).2 hσmin (hσ z (hballmem z hz)) (hRre z (hballmem z hz)) θ)
    hbi
    (Filter.Eventually.of_forall fun θ z _ => hasDerivAt_kmsIntegrand_z m hf hfc hg hgc θ z)
  exact key.2.differentiableAt

/-- **`kmsFunCut Rc` is holomorphic on the open strip** `{−1<Im z<0}` — the `DifferentiableOn` half of
    `DiffContOnCl` for the truncated function (immediate from `kmsFunCut_differentiableAt`). -/
theorem kmsFunCut_differentiableOn {m : ℝ} (hmpos : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0) (Rc : ℝ) :
    DifferentiableOn ℂ (kmsFunCut m f g Rc) (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) := by
  intro z hz
  rw [Set.mem_preimage, Set.mem_Ioo] at hz
  exact (kmsFunCut_differentiableAt hmpos hf hfc hg hgc hδ hmf hmg Rc hz.1 hz.2).differentiableWithinAt

end QIQTH.Fock.BoostKMS
