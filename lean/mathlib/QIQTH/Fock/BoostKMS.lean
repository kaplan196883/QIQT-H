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
    (hbd : ∃ M : ℝ, ∀ z ∈ Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0, ‖kmsFun m f g z‖ ≤ M) :
    ∃ F : ℂ → ℂ, DiffContOnCl ℂ F (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) ∧
      (∃ M : ℝ, ∀ z : ℂ, ‖F z‖ ≤ M) ∧
      (∀ t : ℝ, F t = inner ℂ (hg.toLp (Krep m g)) (boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f)))) ∧
      (∀ t : ℝ, F ((t : ℂ) - Complex.I)
        = inner ℂ (boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f))) (hg.toLp (Krep m g))) := by
  -- Witness: kmsFun clamped to 0 outside the closed strip — same DiffContOnCl + boundary values, but globally
  -- bounded (RvD Def 3.4's boundedness is on the strip; the clamp only supplies a value off-strip).
  set C : Set ℂ := Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0 with hCdef
  set F : ℂ → ℂ := C.indicator (kmsFun m f g) with hFdef
  have hEqC : Set.EqOn F (kmsFun m f g) C := fun z hz => by rw [hFdef, Set.indicator_of_mem hz]
  have htop : ∀ t : ℝ, (t : ℂ) ∈ C := by
    intro t
    rw [hCdef, Set.mem_preimage, Set.mem_Icc, Complex.ofReal_im]
    exact ⟨by norm_num, by norm_num⟩
  have hbot : ∀ t : ℝ, (t : ℂ) - Complex.I ∈ C := by
    intro t
    rw [hCdef, Set.mem_preimage, Set.mem_Icc, Complex.sub_im, Complex.ofReal_im, Complex.I_im]
    exact ⟨by norm_num, by norm_num⟩
  have hsubOpen : Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0 ⊆ C := by
    intro z hz
    rw [Set.mem_preimage, Set.mem_Ioo] at hz
    rw [hCdef, Set.mem_preimage, Set.mem_Icc]; exact ⟨hz.1.le, hz.2.le⟩
  have hsubClosure : closure (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) ⊆ C := by
    have h := Complex.continuous_im.closure_preimage_subset (Set.Ioo (-1 : ℝ) 0)
    rwa [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)] at h
  have hDCCF : DiffContOnCl ℂ F (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) :=
    ⟨hDCC.1.congr (fun z hz => hEqC (hsubOpen hz)),
      hDCC.2.congr (fun z hz => hEqC (hsubClosure hz))⟩
  obtain ⟨M, hM⟩ := hbd
  have h0C : (0 : ℂ) ∈ C := by
    rw [hCdef, Set.mem_preimage, Set.mem_Icc, Complex.zero_im]
    exact ⟨by norm_num, by norm_num⟩
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 h0C)
  refine ⟨F, hDCCF, ⟨M, fun z => ?_⟩, fun t => ?_, fun t => ?_⟩
  · by_cases hz : z ∈ C
    · rw [hEqC hz]; exact hM z hz
    · rw [hFdef, Set.indicator_of_notMem hz, norm_zero]; exact hMnn
  · rw [hEqC (htop t)]; exact kmsFun_ofReal_eq_inner m t hf hg (hbf t)
  · rw [hEqC (hbot t), kmsFun_sub_I m hfr hgr t, kmsFun_ofReal_eq_inner m t hf hg (hbf t)]
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
theorem norm_integral_conj_mul_le_l2 {μ : Measure ℝ} {A B : ℝ → ℂ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) :
    ‖∫ θ : ℝ, (starRingEnd ℂ) (A θ) * B θ ∂μ‖
      ≤ Real.sqrt (∫ θ : ℝ, ‖A θ‖ ^ 2 ∂μ) * Real.sqrt (∫ θ : ℝ, ‖B θ‖ ^ 2 ∂μ) := by
  have hmA : MemLp (fun θ => ‖A θ‖) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num [ENNReal.ofReal_ofNat]]; exact hA.norm
  have hmB : MemLp (fun θ => ‖B θ‖) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num [ENNReal.ofReal_ofNat]]; exact hB.norm
  have hpow : ∀ h : ℝ → ℂ, (∫ θ : ℝ, ‖h θ‖ ^ (2 : ℝ) ∂μ) = ∫ θ : ℝ, ‖h θ‖ ^ 2 ∂μ := by
    intro h
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    show ‖h θ‖ ^ (2 : ℝ) = ‖h θ‖ ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  calc ‖∫ θ : ℝ, (starRingEnd ℂ) (A θ) * B θ ∂μ‖
      ≤ ∫ θ : ℝ, ‖(starRingEnd ℂ) (A θ) * B θ‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ θ : ℝ, ‖A θ‖ * ‖B θ‖ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
        show ‖(starRingEnd ℂ) (A θ) * B θ‖ = ‖A θ‖ * ‖B θ‖
        rw [norm_mul, RCLike.norm_conj]
    _ ≤ (∫ θ : ℝ, ‖A θ‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫ θ : ℝ, ‖B θ‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
          (Filter.Eventually.of_forall fun θ => norm_nonneg _)
          (Filter.Eventually.of_forall fun θ => norm_nonneg _) hmA hmB
    _ = Real.sqrt (∫ θ : ℝ, ‖A θ‖ ^ 2 ∂μ) * Real.sqrt (∫ θ : ℝ, ‖B θ‖ ^ 2 ∂μ) := by
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

/-- **`kmsFunCut Rc` is continuous on the CLOSED strip** `{−1≤Im z≤0}` — the `ContinuousOn` half of
    `DiffContOnCl`. This is where the θ-truncation pays off: the integrand is dominated by the **constant**
    `C_g·C_f` uniformly on the closed strip (no degeneration, since `‖KrepCont‖ ≤ C` for `Im arg ∈ [0,π]`),
    which is integrable on the finite-measure window `[−Rc,Rc]`; `continuousOn_of_dominated` + the integrand's
    `z`-continuity (`differentiable_kmsIntegrand`) close it. -/
theorem kmsFunCut_continuousOn {m : ℝ} (hm : 0 ≤ m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0) (Rc : ℝ) :
    ContinuousOn (kmsFunCut m f g Rc) (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0) := by
  refine continuousOn_of_dominated
    (bound := fun _ : ℝ => (1 / Real.sqrt 2 * ∫ x, ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖))
    (fun z _ => (continuous_kmsIntegrand_in_theta m hf hfc hg hgc z).aestronglyMeasurable)
    (fun z hz => ?_) ?_ ?_
  · rw [Set.mem_preimage, Set.mem_Icc] at hz
    refine Filter.Eventually.of_forall fun θ => ?_
    have him0 : (0 : ℝ) ≤ -(Real.pi * z.im) := by
      have : 0 ≤ -z.im := by linarith [hz.2]
      have := Real.pi_pos; nlinarith
    have himπ : -(Real.pi * z.im) ≤ Real.pi := by
      have h1 : -z.im ≤ 1 := by linarith [hz.1]
      nlinarith [Real.pi_pos]
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
  · exact MeasureTheory.integrableOn_const measure_Icc_lt_top.ne
  · exact Filter.Eventually.of_forall fun θ =>
      (differentiable_kmsIntegrand m hf hfc hg hgc θ).continuous.continuousOn

/-- **`kmsFunCut Rc` is `DiffContOnCl` on the open strip** `{−1<Im z<0}` — holomorphic on the open strip
    (`kmsFunCut_differentiableOn`) and continuous on its closure `{−1≤Im z≤0}` (`kmsFunCut_continuousOn`, using
    `closure (im⁻¹' Ioo) ⊆ im⁻¹' Icc`). The full regularity hypothesis Hadamard three-lines consumes. -/
theorem kmsFunCut_diffContOnCl {m : ℝ} (hmpos : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0) (Rc : ℝ) :
    DiffContOnCl ℂ (kmsFunCut m f g Rc) (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) := by
  have hcl : closure (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) ⊆ Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0 := by
    have h := Complex.continuous_im.closure_preimage_subset (Set.Ioo (-1 : ℝ) 0)
    rwa [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)] at h
  exact ⟨kmsFunCut_differentiableOn hmpos hf hfc hg hgc hδ hmf hmg Rc,
    (kmsFunCut_continuousOn hmpos.le hf hfc hg hgc hδ.le hmf hmg Rc).mono hcl⟩

/-- **`kmsFunCut` on the real axis** — same `KrepCont→Krep` collapse as `kmsFun_ofReal`, over `[−R,R]`. -/
theorem kmsFunCut_ofReal (m : ℝ) (f g : V → ℂ) (R t : ℝ) :
    kmsFunCut m f g R (t : ℂ)
      = ∫ θ in Set.Icc (-R) R,
          (starRingEnd ℂ) (Krep m g (θ + Real.pi * t)) * Krep m f (θ - Real.pi * t) := by
  rw [kmsFunCut]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  have e1 : (θ : ℂ) + (Real.pi : ℂ) * (t : ℂ) = ((θ + Real.pi * t : ℝ) : ℂ) := by push_cast; ring
  have e2 : (θ : ℂ) - (Real.pi : ℂ) * (t : ℂ) = ((θ - Real.pi * t : ℝ) : ℂ) := by push_cast; ring
  simp only [e1, e2, Complex.conj_ofReal, KrepCont_ofReal]

/-- **Truncated top-edge bound** (`Im z = 0`): `‖kmsFunCut R t‖ ≤ √(∫‖Krep g‖²)·√(∫‖Krep f‖²) =: B`, the SAME
    constant for every `R, t`. Truncated Cauchy–Schwarz (`norm_integral_conj_mul_le_l2` over `volume.restrict
    [−R,R]`) bounds it by the truncated slice `L²`-norms, and truncation only DEcreases them
    (`setIntegral_le_integral`); translation-invariance (`integral_add_right_eq_self`) identifies each full
    slice norm with `∫‖Krep ·‖²`. This is the edge constant Hadamard propagates into the strip. -/
theorem norm_kmsFunCut_ofReal_le (m : ℝ) (R t : ℝ) {f g : V → ℂ}
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume) :
    ‖kmsFunCut m f g R (t : ℂ)‖
      ≤ Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2) := by
  rw [kmsFunCut_ofReal]
  have hAv : MemLp (fun θ : ℝ => Krep m g (θ + Real.pi * t)) 2 volume := by
    simpa [Function.comp_def] using
      hg.comp_measurePreserving (measurePreserving_add_right volume (Real.pi * t))
  have hBv : MemLp (fun θ : ℝ => Krep m f (θ - Real.pi * t)) 2 volume := by
    have h := hf.comp_measurePreserving (measurePreserving_add_right volume (-(Real.pi * t)))
    simpa [Function.comp_def, sub_eq_add_neg] using h
  have hAmem : MemLp (fun θ : ℝ => Krep m g (θ + Real.pi * t)) 2
      (volume.restrict (Set.Icc (-R) R)) := hAv.mono_measure Measure.restrict_le_self
  have hBmem : MemLp (fun θ : ℝ => Krep m f (θ - Real.pi * t)) 2
      (volume.restrict (Set.Icc (-R) R)) := hBv.mono_measure Measure.restrict_le_self
  refine (norm_integral_conj_mul_le_l2 hAmem hBmem).trans ?_
  have hslice : ∀ (h : V → ℂ) (a : ℝ), MemLp (fun θ : ℝ => Krep m h (θ + a)) 2 volume →
      Real.sqrt (∫ θ in Set.Icc (-R) R, ‖Krep m h (θ + a)‖ ^ 2)
        ≤ Real.sqrt (∫ θ, ‖Krep m h θ‖ ^ 2) := by
    intro h a hmem
    apply Real.sqrt_le_sqrt
    have hint : Integrable (fun θ : ℝ => ‖Krep m h (θ + a)‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq hmem.norm.aestronglyMeasurable).mp hmem.norm
    calc ∫ θ in Set.Icc (-R) R, ‖Krep m h (θ + a)‖ ^ 2
        ≤ ∫ θ, ‖Krep m h (θ + a)‖ ^ 2 :=
          setIntegral_le_integral hint (Filter.Eventually.of_forall fun θ => by positivity)
      _ = ∫ θ, ‖Krep m h θ‖ ^ 2 :=
          integral_add_right_eq_self (fun θ : ℝ => ‖Krep m h θ‖ ^ 2) a
  refine mul_le_mul (hslice g (Real.pi * t) hAv) ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hBv' : MemLp (fun θ : ℝ => Krep m f (θ + -(Real.pi * t))) 2 volume := by
    simpa [sub_eq_add_neg] using hBv
  calc Real.sqrt (∫ θ in Set.Icc (-R) R, ‖Krep m f (θ - Real.pi * t)‖ ^ 2)
      = Real.sqrt (∫ θ in Set.Icc (-R) R, ‖Krep m f (θ + -(Real.pi * t))‖ ^ 2) := by
        simp only [sub_eq_add_neg]
    _ ≤ Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2) := hslice f (-(Real.pi * t)) hBv'

/-- **`kmsFunCut` bottom edge** `F(t−i) = conj F(t)` (real `f,g`) — same `iπ`-shift collapse as `kmsFun_sub_I`,
    over `[−R,R]`. -/
theorem kmsFunCut_sub_I (m : ℝ) {f g : V → ℂ} (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x)
    (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x) (R t : ℝ) :
    kmsFunCut m f g R ((t : ℂ) - Complex.I) = (starRingEnd ℂ) (kmsFunCut m f g R (t : ℂ)) := by
  have hL : kmsFunCut m f g R ((t : ℂ) - Complex.I)
      = ∫ θ in Set.Icc (-R) R,
          Krep m g (θ + Real.pi * t) * (starRingEnd ℂ) (Krep m f (θ - Real.pi * t)) := by
    rw [kmsFunCut]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    dsimp only
    have ag : (starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * ((t : ℂ) - Complex.I))
        = ((θ + Real.pi * t : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by
      simp only [map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    have af : (θ : ℂ) - (Real.pi : ℂ) * ((t : ℂ) - Complex.I)
        = ((θ - Real.pi * t : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [ag, af, KrepCont_add_pi_I m hgr, KrepCont_add_pi_I m hfr, Complex.conj_conj]
  rw [hL, kmsFunCut_ofReal, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [map_mul, Complex.conj_conj, mul_comm]

/-- **Truncated bottom-edge bound** (`Im z = −1`): the SAME constant `B = √(∫‖Krep g‖²)·√(∫‖Krep f‖²)` as the
    top edge, via `kmsFunCut_sub_I` (equal norm) and `norm_kmsFunCut_ofReal_le`. Both boundary lines of the
    strip are now uniformly bounded by `B` for every `R` — the Hadamard edge data. -/
theorem norm_kmsFunCut_sub_I_le (m : ℝ) (R t : ℝ) {f g : V → ℂ}
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume) :
    ‖kmsFunCut m f g R ((t : ℂ) - Complex.I)‖
      ≤ Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2) := by
  rw [kmsFunCut_sub_I m hfr hgr R t, RCLike.norm_conj]
  exact norm_kmsFunCut_ofReal_le m R t hf hg

/-- **Abstract Hadamard-on-the-strip bound.** A function `Φ` holomorphic on the open strip `{−1<Im z<0}`,
    continuous and bounded on the closed strip, with both boundary lines `≤ b`, satisfies `‖Φ z‖ ≤ b`
    everywhere in the closed strip. Rotate `w↦−i·w` onto `verticalClosedStrip 0 1` and apply
    `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` (edge consts `b,b`,
    `b^(1−s)·b^s=b`). The reusable core of the truncation argument (used for `kmsFunCut` and for the annular
    differences `kmsFunCut S − kmsFunCut R`). -/
theorem norm_le_of_strip_edges {Φ : ℂ → ℂ} {b : ℝ}
    (hdiff : DifferentiableOn ℂ Φ (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0))
    (hcont : ContinuousOn Φ (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0))
    (hbdd : BddAbove ((norm ∘ Φ) '' (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0)))
    (htop : ∀ t : ℝ, ‖Φ (t : ℂ)‖ ≤ b) (hbot : ∀ t : ℝ, ‖Φ ((t : ℂ) - Complex.I)‖ ≤ b)
    {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    ‖Φ z‖ ≤ b := by
  have hbnn : 0 ≤ b := le_trans (norm_nonneg _) (htop 0)
  set φ : ℂ → ℂ := fun w => -Complex.I * w with hφdef
  set G : ℂ → ℂ := fun w => Φ (φ w) with hGdef
  have hφim : ∀ w' : ℂ, (φ w').im = -w'.re := fun w' => by simp [hφdef, Complex.mul_im, Complex.mul_re]
  have hφre : ∀ w' : ℂ, (φ w').re = w'.im := fun w' => by simp [hφdef, Complex.mul_re, Complex.mul_im]
  set w : ℂ := Complex.I * z with hwdef
  have hφw : φ w = z := by
    simp only [hφdef, hwdef]
    rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
  have hwre : w.re = -z.im := by rw [hwdef, Complex.mul_re, Complex.I_re, Complex.I_im]; ring
  have hφent : Differentiable ℂ φ := by rw [hφdef]; exact differentiable_id.const_mul _
  have hmaps_open : Set.MapsTo φ (Complex.HadamardThreeLines.verticalStrip 0 1)
      (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) := by
    intro w' hw'
    simp only [Complex.HadamardThreeLines.verticalStrip, Set.mem_preimage, Set.mem_Ioo] at hw'
    rw [Set.mem_preimage, Set.mem_Ioo, hφim]
    exact ⟨by linarith [hw'.2], by linarith [hw'.1]⟩
  have hmaps_closed : Set.MapsTo φ (Complex.HadamardThreeLines.verticalClosedStrip 0 1)
      (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0) := by
    intro w' hw'
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc] at hw'
    rw [Set.mem_preimage, Set.mem_Icc, hφim]
    exact ⟨by linarith [hw'.2], by linarith [hw'.1]⟩
  have hsub : closure (Complex.HadamardThreeLines.verticalStrip 0 1)
      ⊆ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    have h := Complex.continuous_re.closure_preimage_subset (Set.Ioo (0 : ℝ) 1)
    rwa [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] at h
  have hd : DiffContOnCl ℂ G (Complex.HadamardThreeLines.verticalStrip 0 1) :=
    ⟨hdiff.comp hφent.differentiableOn hmaps_open,
      (hcont.comp hφent.continuous.continuousOn hmaps_closed).mono hsub⟩
  have hbddG : BddAbove ((norm ∘ G) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine hbdd.mono ?_
    rintro y ⟨w', hw', rfl⟩
    exact ⟨φ w', hmaps_closed hw', rfl⟩
  have ha : ∀ w' ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖G w'‖ ≤ b := by
    intro w' hw'
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw'
    have hφeq : φ w' = (w'.im : ℂ) :=
      Complex.ext (by rw [hφre]; simp) (by rw [hφim, hw']; simp)
    show ‖Φ (φ w')‖ ≤ b
    rw [hφeq]; exact htop w'.im
  have hb : ∀ w' ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖G w'‖ ≤ b := by
    intro w' hw'
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hw'
    have hφeq : φ w' = (w'.im : ℂ) - Complex.I :=
      Complex.ext (by rw [hφre]; simp) (by rw [hφim, hw']; simp)
    show ‖Φ (φ w')‖ ≤ b
    rw [hφeq]; exact hbot w'.im
  have hmem : w ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage, Set.mem_Icc, hwre]
    exact ⟨by linarith, by linarith⟩
  have hhad := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (l := 0) (u := 1) (a := b) (b := b) (by norm_num) hmem hd hbddG ha hb
  have hGw : G w = Φ z := by simp only [hGdef]; rw [hφw]
  rw [hGw] at hhad
  have hwre0 : (0 : ℝ) ≤ w.re := by rw [hwre]; linarith
  have hwre1 : w.re ≤ 1 := by rw [hwre]; linarith
  simp only [sub_zero, div_one] at hhad
  rwa [← Real.rpow_add_of_nonneg hbnn (by linarith : (0:ℝ) ≤ 1 - w.re) hwre0,
    show 1 - w.re + w.re = 1 from by ring, Real.rpow_one] at hhad

/-- **Hadamard step: `‖kmsFunCut R z‖ ≤ B` on the whole closed strip**, for every `R`, with the
    `R,z`-independent constant `B = √(∫‖Krep g‖²)·√(∫‖Krep f‖²)`. Rotate `w ↦ −i·w` to put the strip
    `{−1≤Im z≤0}` onto Mathlib's `verticalClosedStrip 0 1`; the truncated function supplies the three Hadamard
    inputs — `DiffContOnCl` (`kmsFunCut_diffContOnCl`), `BddAbove` (`norm_kmsFunCut_le`), and both edges `≤ B`
    (`norm_kmsFunCut_ofReal_le`, `norm_kmsFunCut_sub_I_le`) — and `Complex.HadamardThreeLines.norm_le_interp_…'`
    with edge constants `B,B` interpolates to `B^(1−s)·B^s = B`. -/
theorem norm_kmsFunCut_le_B {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume)
    {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    ‖kmsFunCut m f g R z‖
      ≤ Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2) := by
  refine norm_le_of_strip_edges
    (kmsFunCut_differentiableOn hm hf hfc hg hgc hδ hmf hmg R)
    (kmsFunCut_continuousOn hm.le hf hfc hg hgc hδ.le hmf hmg R) ?_
    (fun t => norm_kmsFunCut_ofReal_le m R t hfL hgL)
    (fun t => norm_kmsFunCut_sub_I_le m R t hfr hgr hfL hgL) hz0 hz1
  refine ⟨(1 / Real.sqrt 2 * ∫ x, ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖) * (2 * R), ?_⟩
  rintro y ⟨z', hz', rfl⟩
  simp only [Set.mem_preimage, Set.mem_Icc] at hz'
  exact norm_kmsFunCut_le hm.le hf hfc hg hgc hδ.le hmf hmg hR hz'.1 hz'.2

/-- **Boundedness of `kmsFun` on the open strip** (the frontier, now closed): for interior `z`,
    `‖kmsFun m f g z‖ ≤ B = √(∫‖Krep g‖²)·√(∫‖Krep f‖²)`. The `R→∞` transfer of `norm_kmsFunCut_le_B`:
    `kmsFunCut n z → kmsFun z` by `tendsto_setIntegral_of_monotone` (`⋃ₙ [−n,n] = ℝ`), and `‖kmsFunCut n z‖ ≤ B`
    for all `n` passes to the limit. -/
theorem norm_kmsFun_le_B {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume)
    {z : ℂ} (hz0 : -1 < z.im) (hz1 : z.im < 0) :
    ‖kmsFun m f g z‖
      ≤ Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2) := by
  have hint := integrable_kmsIntegrand hm hf hfc hg hgc hδ hδ hmf hmg hz0 hz1
  have hmono : Monotone (fun n : ℕ => Set.Icc (-(n : ℝ)) (n : ℝ)) := by
    intro a b hab
    exact Set.Icc_subset_Icc (neg_le_neg (by exact_mod_cast hab)) (by exact_mod_cast hab)
  have hunion : ⋃ n : ℕ, Set.Icc (-(n : ℝ)) (n : ℝ) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro θ
    obtain ⟨n, hn⟩ := exists_nat_ge |θ|
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_Icc.mpr (abs_le.mp hn)⟩
  have hconv : Filter.Tendsto (fun n : ℕ => kmsFunCut m f g (n : ℝ) z)
      Filter.atTop (nhds (kmsFun m f g z)) := by
    have h := tendsto_setIntegral_of_monotone (μ := volume) (f := fun θ : ℝ =>
        (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
          * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z))
      (fun _ : ℕ => measurableSet_Icc) hmono (by rw [hunion]; exact hint.integrableOn)
    rw [hunion, MeasureTheory.setIntegral_univ] at h
    exact h
  have hbnd : ∀ n : ℕ, ‖kmsFunCut m f g (n : ℝ) z‖
      ≤ Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2) := fun n =>
    norm_kmsFunCut_le_B hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL (by positivity) hz0.le hz1.le
  exact le_of_tendsto hconv.norm (Filter.Eventually.of_forall hbnd)

/-- **`L²`-tail vanishes**: for `F` with `‖F‖² ∈ L¹`, the tail integral `∫_{|θ|>n}‖F‖² → 0` as `n→∞`. The
    sets `{|θ|>n}` are antitone with empty intersection, so `tendsto_setIntegral_of_antitone` applies. -/
theorem tendsto_tail_sq_zero {F : ℝ → ℂ} (hF : Integrable (fun θ : ℝ => ‖F θ‖ ^ 2) volume) :
    Filter.Tendsto (fun n : ℕ => ∫ θ in {θ : ℝ | (n : ℝ) < |θ|}, ‖F θ‖ ^ 2) Filter.atTop (nhds 0) := by
  have hanti : Antitone (fun n : ℕ => {θ : ℝ | (n : ℝ) < |θ|}) := by
    intro a b hab θ hθ
    simp only [Set.mem_setOf_eq] at hθ ⊢
    exact lt_of_le_of_lt (by exact_mod_cast hab) hθ
  have hcap : ⋂ n : ℕ, {θ : ℝ | (n : ℝ) < |θ|} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro θ hθ
    obtain ⟨n, hn⟩ := exists_nat_gt |θ|
    have hmem := Set.mem_iInter.mp hθ n
    simp only [Set.mem_setOf_eq] at hmem
    linarith
  have h := tendsto_setIntegral_of_antitone (μ := volume) (f := fun θ : ℝ => ‖F θ‖ ^ 2)
    (fun n => measurableSet_lt measurable_const _root_.continuous_abs.measurable) hanti
    ⟨0, hF.integrableOn⟩
  rwa [hcap, MeasureTheory.setIntegral_empty] at h

/-- **Tail seminorm vanishes**: `T_F(n) := √(∫_{|θ|>n}‖F‖²) → 0`. -/
theorem tendsto_tail_seminorm_zero {F : ℝ → ℂ} (hF : Integrable (fun θ : ℝ => ‖F θ‖ ^ 2) volume) :
    Filter.Tendsto (fun n : ℕ => Real.sqrt (∫ θ in {θ : ℝ | (n : ℝ) < |θ|}, ‖F θ‖ ^ 2))
      Filter.atTop (nhds 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp (tendsto_tail_sq_zero hF)
  rwa [Real.sqrt_zero] at h

/-- **Real Cauchy–Schwarz** for nonnegative `L²` functions: `∫ u·v ≤ √(∫u²)·√(∫v²)`. Hölder `p=q=2`. -/
theorem real_L2_inner_le {μ : Measure ℝ} {u v : ℝ → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (hunn : 0 ≤ᵐ[μ] u) (hvnn : 0 ≤ᵐ[μ] v) :
    ∫ θ, u θ * v θ ∂μ ≤ Real.sqrt (∫ θ, u θ ^ 2 ∂μ) * Real.sqrt (∫ θ, v θ ^ 2 ∂μ) := by
  have hmu : MemLp u (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num [ENNReal.ofReal_ofNat]]; exact hu
  have hmv : MemLp v (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = (2 : ENNReal) from by norm_num [ENNReal.ofReal_ofNat]]; exact hv
  have hpow : ∀ w : ℝ → ℝ, (∫ θ, w θ ^ (2 : ℝ) ∂μ) = ∫ θ, w θ ^ 2 ∂μ := by
    intro w
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    show w θ ^ (2 : ℝ) = w θ ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  refine (integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hunn hvnn hmu hmv).trans_eq ?_
  rw [hpow u, hpow v, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **One shifted-tail term**: with the cutoff indicator tied to the FIRST factor's shift `+c`,
    `∫ 1_{R<|θ+c|}·‖Krep h₁(θ+c)‖·‖Krep h₂(θ+d)‖ ≤ T_{h₁}(R)·‖Krep h₂‖₂`. Real Cauchy–Schwarz
    (`real_L2_inner_le`) on `1_{·}·‖Krep h₁(·+c)‖` and `‖Krep h₂(·+d)‖`, then translation-invariance
    (`integral_add_right_eq_self`) turns each shifted slice integral into the `t`-independent tail / full norm. -/
theorem tail_term_le (m : ℝ) {h₁ h₂ : V → ℂ} (hh₁ : MemLp (Krep m h₁) 2 volume)
    (hh₂ : MemLp (Krep m h₂) 2 volume) (R c d : ℝ) :
    ∫ θ, Set.indicator {θ : ℝ | R < |θ + c|} (1 : ℝ → ℝ) θ
        * (‖Krep m h₁ (θ + c)‖ * ‖Krep m h₂ (θ + d)‖)
      ≤ Real.sqrt (∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m h₁ θ‖ ^ 2)
        * Real.sqrt (∫ θ, ‖Krep m h₂ θ‖ ^ 2) := by
  have hmeasR : MeasurableSet {θ : ℝ | R < |θ|} :=
    measurableSet_lt measurable_const _root_.continuous_abs.measurable
  have hT₁ : MemLp (fun θ : ℝ => Krep m h₁ (θ + c)) 2 volume := by
    simpa [Function.comp_def] using hh₁.comp_measurePreserving (measurePreserving_add_right volume c)
  have hT₂ : MemLp (fun θ : ℝ => Krep m h₂ (θ + d)) 2 volume := by
    simpa [Function.comp_def] using hh₂.comp_measurePreserving (measurePreserving_add_right volume d)
  set S : Set ℝ := {θ : ℝ | R < |θ + c|} with hSdef
  have hSmeas : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
  set u : ℝ → ℝ := S.indicator (fun θ => ‖Krep m h₁ (θ + c)‖) with hudef
  set v : ℝ → ℝ := fun θ => ‖Krep m h₂ (θ + d)‖ with hvdef
  have hu : MemLp u 2 volume := hT₁.norm.indicator hSmeas
  have hv : MemLp v 2 volume := hT₂.norm
  have heq : (fun θ => Set.indicator S (1 : ℝ → ℝ) θ * (‖Krep m h₁ (θ + c)‖ * ‖Krep m h₂ (θ + d)‖))
      = fun θ => u θ * v θ := by
    funext θ
    rw [hudef, hvdef]
    by_cases hθ : θ ∈ S
    · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ, Pi.one_apply]; ring
    · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem hθ]; ring
  rw [heq]
  have hu2 : (∫ θ, u θ ^ 2) = ∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m h₁ θ‖ ^ 2 := by
    rw [show (∫ θ, u θ ^ 2)
        = ∫ θ, ({θ : ℝ | R < |θ|}.indicator (fun s => ‖Krep m h₁ s‖ ^ 2)) (θ + c) from ?_,
      integral_add_right_eq_self, integral_indicator hmeasR]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    show u θ ^ 2 = {θ : ℝ | R < |θ|}.indicator (fun s => ‖Krep m h₁ s‖ ^ 2) (θ + c)
    rw [hudef]
    by_cases hθ : R < |θ + c|
    · rw [Set.indicator_of_mem (show θ ∈ S from hθ),
        Set.indicator_of_mem (show (θ + c) ∈ {θ : ℝ | R < |θ|} from hθ)]
    · rw [Set.indicator_of_notMem (show θ ∉ S from hθ),
        Set.indicator_of_notMem (show (θ + c) ∉ {θ : ℝ | R < |θ|} from hθ)]; ring
  have hv2 : (∫ θ, v θ ^ 2) = ∫ θ, ‖Krep m h₂ θ‖ ^ 2 := by
    rw [hvdef]; exact integral_add_right_eq_self (fun θ => ‖Krep m h₂ θ‖ ^ 2) d
  have hcs := real_L2_inner_le hu hv
    (Filter.Eventually.of_forall fun θ => by rw [hudef]; exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) θ)
    (Filter.Eventually.of_forall fun θ => by rw [hvdef]; exact norm_nonneg _)
  rwa [hu2, hv2] at hcs

/-- **Shifted-tail geometry** (the crux of the annular bound): if `|θ| > R` then `|θ+a| > R` or `|θ−a| > R`.
    Since `2|θ| = |(θ+a)+(θ−a)| ≤ |θ+a|+|θ−a|`, both `≤ R` would force `|θ| ≤ R`. This is why the scalar KMS
    product has uniformly small edge tails even though the individual `L²` slices do not. -/
theorem tail_geom {R a θ : ℝ} (hθ : R < |θ|) : R < |θ + a| ∨ R < |θ - a| := by
  by_contra h
  push_neg at h
  have h2 : (2 : ℝ) * |θ| ≤ 2 * R :=
    calc (2 : ℝ) * |θ| = |θ + a + (θ - a)| := by
          rw [show θ + a + (θ - a) = 2 * θ from by ring, abs_mul, abs_two]
      _ ≤ |θ + a| + |θ - a| := abs_add_le _ _
      _ ≤ R + R := add_le_add h.1 h.2
      _ = 2 * R := by ring
  linarith

/-- **The full tail integral bound** `∫_{|θ|>R} ‖Krep g(θ+πt)‖·‖Krep f(θ−πt)‖ ≤ ε_R`, UNIFORM in `t`, with
    `ε_R = T_g(R)·‖Krep f‖₂ + T_f(R)·‖Krep g‖₂`. Split the `{|θ|>R}` indicator by `tail_geom` into the two
    shifted tails and apply `tail_term_le` to each. The scalar product's edge tail is `t`-uniform — the heart
    of the annular-difference route to closed-strip continuity. -/
theorem tail_integral_le (m t : ℝ) {f g : V → ℂ} (hf : MemLp (Krep m f) 2 volume)
    (hg : MemLp (Krep m g) 2 volume) (R : ℝ) :
    ∫ θ, Set.indicator {θ : ℝ | R < |θ|} (1 : ℝ → ℝ) θ
        * (‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ - Real.pi * t)‖)
      ≤ Real.sqrt (∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m g θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2)
        + Real.sqrt (∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m f θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2) := by
  have hTg : MemLp (fun θ : ℝ => Krep m g (θ + Real.pi * t)) 2 volume := by
    simpa [Function.comp_def] using
      hg.comp_measurePreserving (measurePreserving_add_right volume (Real.pi * t))
  have hTf : MemLp (fun θ : ℝ => Krep m f (θ - Real.pi * t)) 2 volume := by
    have h := hf.comp_measurePreserving (measurePreserving_add_right volume (-(Real.pi * t)))
    simpa [Function.comp_def, sub_eq_add_neg] using h
  have hga : Integrable (fun θ => ‖Krep m g (θ + Real.pi * t)‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq hTg.norm.aestronglyMeasurable).mp hTg.norm
  have hfb : Integrable (fun θ => ‖Krep m f (θ - Real.pi * t)‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq hTf.norm.aestronglyMeasurable).mp hTf.norm
  have hwaesm : AEStronglyMeasurable
      (fun θ => ‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ - Real.pi * t)‖) volume :=
    hTg.norm.aestronglyMeasurable.mul hTf.norm.aestronglyMeasurable
  have hw : Integrable
      (fun θ => ‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ - Real.pi * t)‖) volume := by
    refine Integrable.mono' (hga.add hfb) hwaesm (Filter.Eventually.of_forall fun θ => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (‖Krep m g (θ + Real.pi * t)‖ - ‖Krep m f (θ - Real.pi * t)‖),
      norm_nonneg (Krep m g (θ + Real.pi * t)), norm_nonneg (Krep m f (θ - Real.pi * t))]
  set w : ℝ → ℝ := fun θ => ‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ - Real.pi * t)‖ with hwdef
  -- the two shifted-tail term functions are integrable (bounded by w)
  have hmeas1 : MeasurableSet {θ : ℝ | R < |θ + Real.pi * t|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hmeas2 : MeasurableSet {θ : ℝ | R < |θ - Real.pi * t|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have hterm_int : ∀ s : Set ℝ, MeasurableSet s →
      Integrable (fun θ => Set.indicator s (1 : ℝ → ℝ) θ * w θ) volume := by
    intro s hs
    have heq : (fun θ => Set.indicator s (1 : ℝ → ℝ) θ * w θ) = s.indicator w := by
      funext θ
      by_cases hθ : θ ∈ s
      · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ, Pi.one_apply, one_mul]
      · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem hθ, zero_mul]
    rw [heq]; exact hw.indicator hs
  -- geometry: split the |θ|>R indicator into the two shifted tails
  have hgeom : ∀ θ : ℝ,
      Set.indicator {θ : ℝ | R < |θ|} (1 : ℝ → ℝ) θ * w θ
      ≤ Set.indicator {θ : ℝ | R < |θ + Real.pi * t|} (1 : ℝ → ℝ) θ * w θ
        + Set.indicator {θ : ℝ | R < |θ - Real.pi * t|} (1 : ℝ → ℝ) θ * w θ := by
    intro θ
    have hwnn : 0 ≤ w θ := by rw [hwdef]; positivity
    have hi1 : 0 ≤ Set.indicator {θ : ℝ | R < |θ + Real.pi * t|} (1 : ℝ → ℝ) θ * w θ :=
      mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) θ) hwnn
    have hi2 : 0 ≤ Set.indicator {θ : ℝ | R < |θ - Real.pi * t|} (1 : ℝ → ℝ) θ * w θ :=
      mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) θ) hwnn
    by_cases hθ : θ ∈ {θ : ℝ | R < |θ|}
    · rw [Set.indicator_of_mem hθ, Pi.one_apply, one_mul]
      rcases tail_geom (a := Real.pi * t) (show R < |θ| from hθ) with h1 | h2
      · rw [Set.indicator_of_mem (show θ ∈ {θ : ℝ | R < |θ + Real.pi * t|} from h1), Pi.one_apply, one_mul]
        linarith
      · rw [Set.indicator_of_mem (show θ ∈ {θ : ℝ | R < |θ - Real.pi * t|} from h2), Pi.one_apply, one_mul]
        linarith
    · rw [Set.indicator_of_notMem hθ, zero_mul]
      linarith
  -- integrate the geometry bound, then bound each term by tail_term_le
  have hsplit : (∫ θ, Set.indicator {θ : ℝ | R < |θ|} (1 : ℝ → ℝ) θ * w θ)
      ≤ (∫ θ, Set.indicator {θ : ℝ | R < |θ + Real.pi * t|} (1 : ℝ → ℝ) θ * w θ)
        + ∫ θ, Set.indicator {θ : ℝ | R < |θ - Real.pi * t|} (1 : ℝ → ℝ) θ * w θ := by
    rw [← integral_add (hterm_int _ hmeas1) (hterm_int _ hmeas2)]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => ?_)
      ((hterm_int _ hmeas1).add (hterm_int _ hmeas2)) (Filter.Eventually.of_forall hgeom)
    rw [hwdef]; exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) θ) (by positivity)
  refine hsplit.trans ?_
  gcongr ?_ + ?_
  · -- term 1 (indicator on g-shift +πt)
    have h := tail_term_le m hg hf R (Real.pi * t) (-(Real.pi * t))
    refine le_of_eq_of_le (integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)) h
    show Set.indicator {θ : ℝ | R < |θ + Real.pi * t|} (1 : ℝ → ℝ) θ * w θ
      = Set.indicator {θ : ℝ | R < |θ + Real.pi * t|} (1 : ℝ → ℝ) θ
        * (‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ + -(Real.pi * t))‖)
    simp only [hwdef]; rw [sub_eq_add_neg]
  · -- term 2 (indicator on f-shift −πt), product commuted
    have h := tail_term_le m hf hg R (-(Real.pi * t)) (Real.pi * t)
    refine le_of_eq_of_le (integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)) h
    show Set.indicator {θ : ℝ | R < |θ - Real.pi * t|} (1 : ℝ → ℝ) θ * w θ
      = Set.indicator {θ : ℝ | R < |θ + -(Real.pi * t)|} (1 : ℝ → ℝ) θ
        * (‖Krep m f (θ + -(Real.pi * t))‖ * ‖Krep m g (θ + Real.pi * t)‖)
    simp only [hwdef, sub_eq_add_neg]
    rw [mul_comm (‖Krep m g (θ + Real.pi * t)‖) (‖Krep m f (θ + -(Real.pi * t))‖)]

/-- **Annular top-edge bound** (`S ≥ R`): `‖kmsFunCut S t − kmsFunCut R t‖ ≤ ε_R` UNIFORMLY in `t`. The
    difference is `∫ (1_{Icc(−S,S)} − 1_{Icc(−R,R)})·I` whose integrand has norm `≤ 1_{|θ|>R}·w` pointwise
    (`I` is the real-axis integrand, `w=‖I‖`; on `|θ|≤R` it cancels, on `R<|θ|≤S` it is `I`, beyond `S` it is
    `0`); then `norm_integral_le_integral_norm` + `integral_mono` + `tail_integral_le`. -/
theorem norm_kmsFunCut_diff_ofReal_le (m t : ℝ) {f g : V → ℂ} (hf : MemLp (Krep m f) 2 volume)
    (hg : MemLp (Krep m g) 2 volume) {R S : ℝ} (hRS : R ≤ S) :
    ‖kmsFunCut m f g S (t : ℂ) - kmsFunCut m f g R (t : ℂ)‖
      ≤ Real.sqrt (∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m g θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2)
        + Real.sqrt (∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m f θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2) := by
  have hTg : MemLp (fun θ : ℝ => Krep m g (θ + Real.pi * t)) 2 volume := by
    simpa [Function.comp_def] using
      hg.comp_measurePreserving (measurePreserving_add_right volume (Real.pi * t))
  have hTf : MemLp (fun θ : ℝ => Krep m f (θ - Real.pi * t)) 2 volume := by
    have h := hf.comp_measurePreserving (measurePreserving_add_right volume (-(Real.pi * t)))
    simpa [Function.comp_def, sub_eq_add_neg] using h
  have hga : Integrable (fun θ => ‖Krep m g (θ + Real.pi * t)‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq hTg.norm.aestronglyMeasurable).mp hTg.norm
  have hfb : Integrable (fun θ => ‖Krep m f (θ - Real.pi * t)‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq hTf.norm.aestronglyMeasurable).mp hTf.norm
  have hprod : Integrable (fun θ => ‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ - Real.pi * t)‖) volume := by
    refine Integrable.mono' (hga.add hfb)
      (hTg.norm.aestronglyMeasurable.mul hTf.norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun θ => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (‖Krep m g (θ + Real.pi * t)‖ - ‖Krep m f (θ - Real.pi * t)‖),
      norm_nonneg (Krep m g (θ + Real.pi * t)), norm_nonneg (Krep m f (θ - Real.pi * t))]
  have hIaesm : AEStronglyMeasurable
      (fun θ => (starRingEnd ℂ) (Krep m g (θ + Real.pi * t)) * Krep m f (θ - Real.pi * t)) volume :=
    (Complex.continuous_conj.comp_aestronglyMeasurable hTg.aestronglyMeasurable).mul hTf.aestronglyMeasurable
  have hI : Integrable
      (fun θ => (starRingEnd ℂ) (Krep m g (θ + Real.pi * t)) * Krep m f (θ - Real.pi * t)) volume := by
    rw [← integrable_norm_iff hIaesm]
    refine hprod.congr (Filter.Eventually.of_forall fun θ => ?_)
    show ‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ - Real.pi * t)‖
      = ‖(starRingEnd ℂ) (Krep m g (θ + Real.pi * t)) * Krep m f (θ - Real.pi * t)‖
    rw [norm_mul, RCLike.norm_conj]
  rw [kmsFunCut_ofReal, kmsFunCut_ofReal, ← integral_indicator measurableSet_Icc,
    ← integral_indicator measurableSet_Icc,
    ← integral_sub (hI.indicator measurableSet_Icc) (hI.indicator measurableSet_Icc)]
  refine (norm_integral_le_integral_norm _).trans ?_
  set J : ℝ → ℂ := fun θ => (starRingEnd ℂ) (Krep m g (θ + Real.pi * t)) * Krep m f (θ - Real.pi * t)
    with hJdef
  have hnormJ : ∀ θ, ‖J θ‖ = ‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ - Real.pi * t)‖ := fun θ => by
    rw [hJdef, norm_mul, RCLike.norm_conj]
  have hRHSint : Integrable (fun θ => Set.indicator {θ : ℝ | R < |θ|} (1 : ℝ → ℝ) θ
      * (‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ - Real.pi * t)‖)) volume := by
    have heq : (fun θ => Set.indicator {θ : ℝ | R < |θ|} (1 : ℝ → ℝ) θ
          * (‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ - Real.pi * t)‖))
        = {θ : ℝ | R < |θ|}.indicator
          (fun θ => ‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ - Real.pi * t)‖) := by
      funext θ
      by_cases hθ : θ ∈ {θ : ℝ | R < |θ|}
      · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ, Pi.one_apply, one_mul]
      · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem hθ, zero_mul]
    rw [heq]
    exact hprod.indicator (measurableSet_lt measurable_const _root_.continuous_abs.measurable)
  refine (integral_mono ((hI.indicator measurableSet_Icc).sub (hI.indicator measurableSet_Icc)).norm
    hRHSint (fun θ => ?_)).trans (tail_integral_le m t hf hg R)
  -- pointwise: ‖1_S·J − 1_R·J‖ ≤ 1_{|θ|>R}·(‖Krep g(θ+πt)‖·‖Krep f(θ−πt)‖)
  show ‖Set.indicator (Set.Icc (-S) S) J θ - Set.indicator (Set.Icc (-R) R) J θ‖
    ≤ Set.indicator {θ : ℝ | R < |θ|} (1 : ℝ → ℝ) θ
      * (‖Krep m g (θ + Real.pi * t)‖ * ‖Krep m f (θ - Real.pi * t)‖)
  by_cases hR : |θ| ≤ R
  · have hθR : θ ∈ Set.Icc (-R) R := Set.mem_Icc.mpr (abs_le.mp hR)
    have hθS : θ ∈ Set.Icc (-S) S := Set.mem_Icc.mpr (abs_le.mp (hR.trans hRS))
    rw [Set.indicator_of_mem hθS, Set.indicator_of_mem hθR, sub_self, norm_zero]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) θ) (by positivity)
  · push_neg at hR
    rw [Set.indicator_of_mem (show θ ∈ {θ : ℝ | R < |θ|} from hR), Pi.one_apply, one_mul]
    by_cases hS : |θ| ≤ S
    · have hθS : θ ∈ Set.Icc (-S) S := Set.mem_Icc.mpr (abs_le.mp hS)
      have hθR : θ ∉ Set.Icc (-R) R := fun h => absurd (abs_le.mpr (Set.mem_Icc.mp h)) (not_le.mpr hR)
      rw [Set.indicator_of_mem hθS, Set.indicator_of_notMem hθR, sub_zero, hnormJ]
    · push_neg at hS
      have hθS : θ ∉ Set.Icc (-S) S := fun h => absurd (abs_le.mpr (Set.mem_Icc.mp h)) (not_le.mpr hS)
      have hθR : θ ∉ Set.Icc (-R) R :=
        fun h => absurd (abs_le.mpr (Set.mem_Icc.mp h)) (not_le.mpr hR)
      rw [Set.indicator_of_notMem hθS, Set.indicator_of_notMem hθR, sub_zero, norm_zero]
      positivity

/-- **Annular bottom-edge bound** (`S ≥ R`, real `f,g`): same `ε_R` as the top edge, via `kmsFunCut_sub_I`
    (`F(t−i)=conj F(t)`) ⟹ the difference is the conjugate of the top-edge difference, equal norm. -/
theorem norm_kmsFunCut_diff_sub_I_le (m t : ℝ) {f g : V → ℂ}
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume) {R S : ℝ} (hRS : R ≤ S) :
    ‖kmsFunCut m f g S ((t : ℂ) - Complex.I) - kmsFunCut m f g R ((t : ℂ) - Complex.I)‖
      ≤ Real.sqrt (∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m g θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2)
        + Real.sqrt (∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m f θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2) := by
  rw [kmsFunCut_sub_I m hfr hgr S t, kmsFunCut_sub_I m hfr hgr R t, ← map_sub, RCLike.norm_conj]
  exact norm_kmsFunCut_diff_ofReal_le m t hf hg hRS

/-- **The annular difference is `≤ ε_R` on the WHOLE closed strip** (`S ≥ R`). `kmsFunCut S − kmsFunCut R` is
    `DiffContOnCl` + bounded (difference of two such), and both boundary lines are `≤ ε_R`
    (`norm_kmsFunCut_diff_ofReal_le`/`_sub_I_le`); `norm_le_of_strip_edges` propagates the edge bound inward.
    Combined with `ε_R → 0` this is the uniform-Cauchy property of `{kmsFunCut n}` on the closed strip. -/
theorem norm_kmsFunCut_diff_le {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume)
    {R S : ℝ} (hR : 0 ≤ R) (hRS : R ≤ S) {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    ‖kmsFunCut m f g S z - kmsFunCut m f g R z‖
      ≤ Real.sqrt (∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m g θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2)
        + Real.sqrt (∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m f θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2) := by
  refine norm_le_of_strip_edges (Φ := fun z => kmsFunCut m f g S z - kmsFunCut m f g R z)
    ((kmsFunCut_differentiableOn hm hf hfc hg hgc hδ hmf hmg S).sub
      (kmsFunCut_differentiableOn hm hf hfc hg hgc hδ hmf hmg R))
    ((kmsFunCut_continuousOn hm.le hf hfc hg hgc hδ.le hmf hmg S).sub
      (kmsFunCut_continuousOn hm.le hf hfc hg hgc hδ.le hmf hmg R)) ?_
    (fun t => norm_kmsFunCut_diff_ofReal_le m t hfL hgL hRS)
    (fun t => norm_kmsFunCut_diff_sub_I_le m t hfr hgr hfL hgL hRS) hz0 hz1
  refine ⟨(1 / Real.sqrt 2 * ∫ x, ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖) * (2 * S)
      + (1 / Real.sqrt 2 * ∫ x, ‖g x‖) * (1 / Real.sqrt 2 * ∫ x, ‖f x‖) * (2 * R), ?_⟩
  rintro y ⟨z', hz', rfl⟩
  simp only [Set.mem_preimage, Set.mem_Icc] at hz'
  refine (norm_sub_le _ _).trans ?_
  gcongr
  · exact norm_kmsFunCut_le hm.le hf hfc hg hgc hδ.le hmf hmg (by linarith) hz'.1 hz'.2
  · exact norm_kmsFunCut_le hm.le hf hfc hg hgc hδ.le hmf hmg hR hz'.1 hz'.2

/-- **The `kmsFun` integrand is integrable at every CLOSED-strip `z`** (`−1≤Im z≤0`). Both slices are `L²`
    via `memLp_KrepCont_affine_closed` (arg `Im = −π·Im z ∈ [0,π]`, including the edges), so the product is
    integrable by AM-GM and the integrand by `integrable_norm_iff`. This is the per-`z` input that makes
    `kmsFunCut n z → kmsFun z` hold up to the boundary. -/
theorem integrable_kmsFun_integrand_closed {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume)
    {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    Integrable (fun θ : ℝ =>
      (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)) volume := by
  have him0 : (0 : ℝ) ≤ Real.pi * (-z.im) := by
    have : 0 ≤ -z.im := by linarith
    have := Real.pi_pos; positivity
  have himπ : Real.pi * (-z.im) ≤ Real.pi := by
    have h1 : -z.im ≤ 1 := by linarith
    nlinarith [Real.pi_pos]
  have hgim : ((Real.pi : ℂ) * (starRingEnd ℂ z)).im = Real.pi * (-z.im) := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im]; ring
  have hfim : (-((Real.pi : ℂ) * z)).im = Real.pi * (-z.im) := by
    simp only [Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hMemG : MemLp (fun θ : ℝ =>
      KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z))) 2 volume := by
    have hfun : (fun θ : ℝ => KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        = fun θ : ℝ => KrepCont m g ((θ : ℂ) + (Real.pi : ℂ) * (starRingEnd ℂ z)) := by
      funext θ; congr 1; rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [hfun]
    exact memLp_KrepCont_affine_closed hm hg hgc hδ hmg hgr hgL
      (by rw [hgim]; exact him0) (by rw [hgim]; exact himπ)
  have hMemF : MemLp (fun θ : ℝ => KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)) 2 volume := by
    have hfun : (fun θ : ℝ => KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z))
        = fun θ : ℝ => KrepCont m f ((θ : ℂ) + (-((Real.pi : ℂ) * z))) := by
      funext θ; rw [sub_eq_add_neg]
    rw [hfun]
    exact memLp_KrepCont_affine_closed hm hf hfc hδ hmf hfr hfL
      (by rw [hfim]; exact him0) (by rw [hfim]; exact himπ)
  have hAsq : Integrable (fun θ : ℝ =>
      ‖KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z))‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq hMemG.norm.aestronglyMeasurable).mp hMemG.norm
  have hBsq : Integrable (fun θ : ℝ => ‖KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq hMemF.norm.aestronglyMeasurable).mp hMemF.norm
  have haesm : AEStronglyMeasurable (fun θ : ℝ =>
      (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)) volume :=
    (Complex.continuous_conj.comp_aestronglyMeasurable hMemG.aestronglyMeasurable).mul
      hMemF.aestronglyMeasurable
  rw [← integrable_norm_iff haesm]
  refine Integrable.mono' (hAsq.add hBsq) haesm.norm (Filter.Eventually.of_forall fun θ => ?_)
  simp only [Pi.add_apply, norm_norm, norm_mul, RCLike.norm_conj]
  nlinarith [sq_nonneg (‖KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z))‖
      - ‖KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)‖),
    norm_nonneg (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z))),
    norm_nonneg (KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z))]

/-- **`kmsFunCut n z → kmsFun z` up to the boundary**: for closed-strip `z`, `tendsto_setIntegral_of_monotone`
    (`⋃ₙ[−n,n]=ℝ`) with the closed-strip integrability `integrable_kmsFun_integrand_closed`. -/
theorem kmsFunCut_tendsto_closed {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume)
    {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    Filter.Tendsto (fun n : ℕ => kmsFunCut m f g (n : ℝ) z) Filter.atTop (nhds (kmsFun m f g z)) := by
  have hint := integrable_kmsFun_integrand_closed hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL hz0 hz1
  have hmono : Monotone (fun n : ℕ => Set.Icc (-(n : ℝ)) (n : ℝ)) := fun a b hab =>
    Set.Icc_subset_Icc (neg_le_neg (by exact_mod_cast hab)) (by exact_mod_cast hab)
  have hunion : ⋃ n : ℕ, Set.Icc (-(n : ℝ)) (n : ℝ) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro θ
    obtain ⟨n, hn⟩ := exists_nat_ge |θ|
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_Icc.mpr (abs_le.mp hn)⟩
  have h := tendsto_setIntegral_of_monotone (μ := volume) (f := fun θ : ℝ =>
      (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z))
    (fun _ : ℕ => measurableSet_Icc) hmono (by rw [hunion]; exact hint.integrableOn)
  rw [hunion, MeasureTheory.setIntegral_univ] at h
  exact h

/-- **Uniform error `‖kmsFun z − kmsFunCut R z‖ ≤ ε_R`** on the closed strip (`R ≥ 0`). Pass `S→∞` to the limit
    in `norm_kmsFunCut_diff_le` via `kmsFunCut_tendsto_closed` + `le_of_tendsto`. -/
theorem norm_kmsFun_sub_kmsFunCut_le {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume)
    {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    ‖kmsFun m f g z - kmsFunCut m f g R z‖
      ≤ Real.sqrt (∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m g θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2)
        + Real.sqrt (∫ θ in {θ : ℝ | R < |θ|}, ‖Krep m f θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2) := by
  have hconv := (kmsFunCut_tendsto_closed hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL hz0 hz1).sub_const
    (kmsFunCut m f g R z)
  refine le_of_tendsto hconv.norm ?_
  rw [Filter.eventually_atTop]
  refine ⟨⌈R⌉₊, fun n hn => ?_⟩
  exact norm_kmsFunCut_diff_le hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL hR
    (le_trans (Nat.le_ceil R) (by exact_mod_cast hn)) hz0 hz1

/-- **★★★★★ `ContinuousOn kmsFun (closed strip)`** — the last analytic gap. `kmsFunCut n → kmsFun` UNIFORMLY
    on the closed strip (`norm_kmsFun_sub_kmsFunCut_le` + `ε_n → 0`), and each `kmsFunCut n` is continuous on
    the closed strip (`kmsFunCut_continuousOn`); the uniform limit of continuous functions is continuous
    (`TendstoUniformlyOn.continuousOn`). -/
theorem kmsFun_continuousOn_closed {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume) :
    ContinuousOn (kmsFun m f g) (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0) := by
  have hgsq : Integrable (fun θ : ℝ => ‖Krep m g θ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq hgL.norm.aestronglyMeasurable).mp hgL.norm
  have hfsq : Integrable (fun θ : ℝ => ‖Krep m f θ‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq hfL.norm.aestronglyMeasurable).mp hfL.norm
  have hεtend : Filter.Tendsto (fun n : ℕ =>
      Real.sqrt (∫ θ in {θ : ℝ | (n : ℝ) < |θ|}, ‖Krep m g θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2)
        + Real.sqrt (∫ θ in {θ : ℝ | (n : ℝ) < |θ|}, ‖Krep m f θ‖ ^ 2) * Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2))
      Filter.atTop (nhds 0) := by
    have h := ((tendsto_tail_seminorm_zero hgsq).mul_const (Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2))).add
      ((tendsto_tail_seminorm_zero hfsq).mul_const (Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2)))
    simpa using h
  have htu : TendstoUniformlyOn (fun n : ℕ => kmsFunCut m f g (n : ℝ)) (kmsFun m f g)
      Filter.atTop (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hεtend.eventually_lt_const hε] with n hn
    intro z hz
    rw [Set.mem_preimage, Set.mem_Icc] at hz
    rw [Complex.dist_eq]
    exact lt_of_le_of_lt
      (norm_kmsFun_sub_kmsFunCut_le hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL
        (Nat.cast_nonneg n) hz.1 hz.2) hn
  exact htu.continuousOn (Filter.Eventually.of_forall (fun n : ℕ =>
    kmsFunCut_continuousOn hm.le hf hfc hg hgc hδ.le hmf hmg (n : ℝ))).frequently

/-- **★★★★★ `kmsFun` is `DiffContOnCl` on the strip** — holomorphic on the open strip
    (`kmsFun_differentiableOn`) and continuous on its closure (`kmsFun_continuousOn_closed`). The full analytic
    regularity of the `StripKMSrvd` witness, axiom-free — the entire holomorphy + boundary-continuity of the
    free-field boost-KMS function, established via the θ-truncation + Hadamard + annular-difference route with
    NO Hardy/Paley–Wiener theory. -/
theorem kmsFun_diffContOnCl {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume) :
    DiffContOnCl ℂ (kmsFun m f g) (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) := by
  have hcl : closure (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) ⊆ Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0 := by
    have h := Complex.continuous_im.closure_preimage_subset (Set.Ioo (-1 : ℝ) 0)
    rwa [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)] at h
  exact ⟨kmsFun_differentiableOn hm hf hfc hg hgc hδ hmf hmg,
    (kmsFun_continuousOn_closed hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL).mono hcl⟩

/-- `kmsFunCut m f g 0 z = 0` — the cutoff window `[−0,0] = {0}` has measure zero. -/
theorem kmsFunCut_zero (m : ℝ) (f g : V → ℂ) (z : ℂ) : kmsFunCut m f g 0 z = 0 := by
  rw [kmsFunCut, neg_zero, Set.Icc_self, MeasureTheory.integral_singleton,
    show volume.real ({0} : Set ℝ) = 0 by
      rw [MeasureTheory.measureReal_def, Real.volume_singleton, ENNReal.toReal_zero], zero_smul]

/-- **`kmsFun` is bounded on the closed strip** by `M₀ := ε₀` (the `R=0` annular constant). `kmsFunCut 0 z = 0`
    and `norm_kmsFun_sub_kmsFunCut_le` at `R=0` give `‖kmsFun z‖ ≤ ε₀` for every `z` in the closed strip — the
    boundedness component of the `StripKMSrvd` witness (RvD Def 3.4 bounds `F` on the strip). -/
theorem norm_kmsFun_le_closed {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume) :
    ∃ M : ℝ, ∀ z ∈ Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0, ‖kmsFun m f g z‖ ≤ M := by
  refine ⟨Real.sqrt (∫ θ in {θ : ℝ | (0 : ℝ) < |θ|}, ‖Krep m g θ‖ ^ 2)
      * Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2)
      + Real.sqrt (∫ θ in {θ : ℝ | (0 : ℝ) < |θ|}, ‖Krep m f θ‖ ^ 2)
        * Real.sqrt (∫ θ, ‖Krep m g θ‖ ^ 2), fun z hz => ?_⟩
  rw [Set.mem_preimage, Set.mem_Icc] at hz
  have h := norm_kmsFun_sub_kmsFunCut_le hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL
    (le_refl (0 : ℝ)) hz.1 hz.2
  rwa [kmsFunCut_zero, sub_zero] at h

/-- **`kmsFun` is additive in the `f` slot** on the closed strip (continuous compact-support real wedge
    `f₁,f₂,g` with `MemLp` amplitudes). `KrepCont_add` distributes the `f`-factor; the outer integral splits by
    `integral_add` (each summand integrable via `integrable_kmsFun_integrand_closed`). -/
theorem kmsFun_add_left {m : ℝ} (hm : 0 < m) {f₁ f₂ g : V → ℂ}
    (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁) (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂)
    (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf₁ : ∀ x, f₁ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmf₂ : ∀ x, f₂ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hf₁r : ∀ x, (starRingEnd ℂ) (f₁ x) = f₁ x) (hf₂r : ∀ x, (starRingEnd ℂ) (f₂ x) = f₂ x)
    (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hf₁L : MemLp (Krep m f₁) 2 volume) (hf₂L : MemLp (Krep m f₂) 2 volume)
    (hgL : MemLp (Krep m g) 2 volume) {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    kmsFun m (f₁ + f₂) g z = kmsFun m f₁ g z + kmsFun m f₂ g z := by
  rw [kmsFun, kmsFun, kmsFun, ← integral_add
    (integrable_kmsFun_integrand_closed hm hf₁ hf₁c hg hgc hδ hmf₁ hmg hf₁r hgr hf₁L hgL hz0 hz1)
    (integrable_kmsFun_integrand_closed hm hf₂ hf₂c hg hgc hδ hmf₂ hmg hf₂r hgr hf₂L hgL hz0 hz1)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  show (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
      * KrepCont m (f₁ + f₂) ((θ : ℂ) - (Real.pi : ℂ) * z)
    = (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f₁ ((θ : ℂ) - (Real.pi : ℂ) * z)
      + (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f₂ ((θ : ℂ) - (Real.pi : ℂ) * z)
  rw [KrepCont_add m hf₁ hf₁c hf₂ hf₂c ((θ : ℂ) - (Real.pi : ℂ) * z)]
  ring

/-- **`kmsFun` is additive in the `g` slot** on the closed strip. Same as `kmsFun_add_left` but on the
    conjugated `g`-factor (`KrepCont_add` + `map_add` for `conj`). -/
theorem kmsFun_add_right {m : ℝ} (hm : 0 < m) {f g₁ g₂ : V → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hg₁ : Continuous g₁) (hg₁c : HasCompactSupport g₁)
    (hg₂ : Continuous g₂) (hg₂c : HasCompactSupport g₂) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg₁ : ∀ x, g₁ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg₂ : ∀ x, g₂ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hg₁r : ∀ x, (starRingEnd ℂ) (g₁ x) = g₁ x)
    (hg₂r : ∀ x, (starRingEnd ℂ) (g₂ x) = g₂ x)
    (hfL : MemLp (Krep m f) 2 volume) (hg₁L : MemLp (Krep m g₁) 2 volume)
    (hg₂L : MemLp (Krep m g₂) 2 volume) {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    kmsFun m f (g₁ + g₂) z = kmsFun m f g₁ z + kmsFun m f g₂ z := by
  rw [kmsFun, kmsFun, kmsFun, ← integral_add
    (integrable_kmsFun_integrand_closed hm hf hfc hg₁ hg₁c hδ hmf hmg₁ hfr hg₁r hfL hg₁L hz0 hz1)
    (integrable_kmsFun_integrand_closed hm hf hfc hg₂ hg₂c hδ hmf hmg₂ hfr hg₂r hfL hg₂L hz0 hz1)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  show (starRingEnd ℂ) (KrepCont m (g₁ + g₂) ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
      * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)
    = (starRingEnd ℂ) (KrepCont m g₁ ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)
      + (starRingEnd ℂ) (KrepCont m g₂ ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)
  rw [KrepCont_add m hg₁ hg₁c hg₂ hg₂c ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)), map_add]
  ring

/-- **`f`-slot subtraction identity**: `kmsFun m (f₁−f₂) g = kmsFun m f₁ g − kmsFun m f₂ g` on the closed strip
    (from `kmsFun_add_left`; `f₁−f₂` is again nice — `δ`-margin on the union of supports, real, `MemLp`). -/
theorem kmsFun_sub_left {m : ℝ} (hm : 0 < m) {f₁ f₂ g : V → ℂ}
    (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁) (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂)
    (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf₁ : ∀ x, f₁ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmf₂ : ∀ x, f₂ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hf₁r : ∀ x, (starRingEnd ℂ) (f₁ x) = f₁ x) (hf₂r : ∀ x, (starRingEnd ℂ) (f₂ x) = f₂ x)
    (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hf₁L : MemLp (Krep m f₁) 2 volume) (hf₂L : MemLp (Krep m f₂) 2 volume)
    (hgL : MemLp (Krep m g) 2 volume) {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    kmsFun m (f₁ - f₂) g z = kmsFun m f₁ g z - kmsFun m f₂ g z := by
  have hmf₁₂ : ∀ x, (f₁ - f₂) x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0 := by
    intro x hx
    by_cases h : f₁ x = 0
    · exact hmf₂ x fun hc => hx (by rw [Pi.sub_apply, h, hc, sub_zero])
    · exact hmf₁ x h
  have hf₁₂r : ∀ x, (starRingEnd ℂ) ((f₁ - f₂) x) = (f₁ - f₂) x := by
    intro x; rw [Pi.sub_apply, map_sub, hf₁r, hf₂r]
  have h : kmsFun m (f₁ - f₂ + f₂) g z = kmsFun m (f₁ - f₂) g z + kmsFun m f₂ g z :=
    kmsFun_add_left hm (hf₁.sub hf₂) (hf₁c.sub hf₂c) hf₂ hf₂c hg hgc hδ hmf₁₂ hmf₂ hmg hf₁₂r hf₂r hgr
      (memLp_Krep_sub hf₁ hf₁c hf₂ hf₂c hf₁L hf₂L) hf₂L hgL hz0 hz1
  have he : f₁ - f₂ + f₂ = f₁ := by ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [he] at h
  rw [h]; ring

/-- **`g`-slot subtraction identity**: `kmsFun m f (g₁−g₂) = kmsFun m f g₁ − kmsFun m f g₂` (from
    `kmsFun_add_right`; `g₁−g₂` is again nice). -/
theorem kmsFun_sub_right {m : ℝ} (hm : 0 < m) {f g₁ g₂ : V → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hg₁ : Continuous g₁) (hg₁c : HasCompactSupport g₁)
    (hg₂ : Continuous g₂) (hg₂c : HasCompactSupport g₂) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg₁ : ∀ x, g₁ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg₂ : ∀ x, g₂ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hg₁r : ∀ x, (starRingEnd ℂ) (g₁ x) = g₁ x)
    (hg₂r : ∀ x, (starRingEnd ℂ) (g₂ x) = g₂ x)
    (hfL : MemLp (Krep m f) 2 volume) (hg₁L : MemLp (Krep m g₁) 2 volume)
    (hg₂L : MemLp (Krep m g₂) 2 volume) {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    kmsFun m f (g₁ - g₂) z = kmsFun m f g₁ z - kmsFun m f g₂ z := by
  have hmg₁₂ : ∀ x, (g₁ - g₂) x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0 := by
    intro x hx
    by_cases h : g₁ x = 0
    · exact hmg₂ x fun hc => hx (by rw [Pi.sub_apply, h, hc, sub_zero])
    · exact hmg₁ x h
  have hg₁₂r : ∀ x, (starRingEnd ℂ) ((g₁ - g₂) x) = (g₁ - g₂) x := by
    intro x; rw [Pi.sub_apply, map_sub, hg₁r, hg₂r]
  have h : kmsFun m f (g₁ - g₂ + g₂) z = kmsFun m f (g₁ - g₂) z + kmsFun m f g₂ z :=
    kmsFun_add_right hm hf hfc (hg₁.sub hg₂) (hg₁c.sub hg₂c) hg₂ hg₂c hδ hmf hmg₁₂ hmg₂ hfr hg₁₂r hg₂r
      hfL (memLp_Krep_sub hg₁ hg₁c hg₂ hg₂c hg₁L hg₂L) hg₂L hz0 hz1
  have he : g₁ - g₂ + g₂ = g₁ := by ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [he] at h
  rw [h]; ring

/-- **`L²`-norm of a one-particle vector as an integral**: `‖KrepL2 f‖ = √(∫‖Krep m f‖²)`. Via `inner_KrepL2`
    (`⟪KrepL2 f, KrepL2 f⟫ = ∫ conj(Krep f)·Krep f = ↑∫‖Krep f‖²`) and `inner_self_eq_norm_sq`. The bridge from
    the analytic strip bound (in `∫‖Krep‖²`) to the Hilbert norms `‖ξ‖,‖η‖` for the closure/threading argument. -/
theorem norm_toLp_Krep_eq_sqrt {m : ℝ} {f : V → ℂ} (hf : MemLp (Krep m f) 2 volume) :
    ‖hf.toLp (Krep m f)‖ = Real.sqrt (∫ θ, ‖Krep m f θ‖ ^ 2) := by
  have hcongr : (∫ θ, (starRingEnd ℂ) (Krep m f θ) * Krep m f θ)
      = ∫ θ, ((‖Krep m f θ‖ ^ 2 : ℝ) : ℂ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    show (starRingEnd ℂ) (Krep m f θ) * Krep m f θ = ((‖Krep m f θ‖ ^ 2 : ℝ) : ℂ)
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm]
  have hinner : inner ℂ (hf.toLp (Krep m f)) (hf.toLp (Krep m f))
      = ((∫ θ, ‖Krep m f θ‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_KrepL2 m hf hf, hcongr, integral_complex_ofReal]
  have hsq : ‖hf.toLp (Krep m f)‖ ^ 2 = ∫ θ, ‖Krep m f θ‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (hf.toLp (Krep m f)), hinner]; simp
  rw [← hsq, Real.sqrt_sq (norm_nonneg _)]

/-- **`KrepL2` respects addition**: `KrepL2(f₁+f₂) = KrepL2 f₁ + KrepL2 f₂` in `L²`. `MemLp.toLp_add` +
    `MemLp.toLp_eq_toLp_iff` (`Krep(f₁+f₂) =ᵐ Krep f₁ + Krep f₂`, `Krep_add`). With `KrepL2_sub` and the real
    scalar law, this makes `{KrepL2 f : f nice}` an ℝ-subspace, so `span_ℝ` adds nothing: every span element is
    a single `KrepL2` of a nice function — collapsing the closure threading to single nice generator pairs. -/
theorem KrepL2_add {m : ℝ} {f₁ f₂ : V → ℂ} (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂)
    (hf₁L : MemLp (Krep m f₁) 2 volume) (hf₂L : MemLp (Krep m f₂) 2 volume) :
    (memLp_Krep_add hf₁ hf₁c hf₂ hf₂c hf₁L hf₂L).toLp (Krep m (f₁ + f₂))
      = hf₁L.toLp (Krep m f₁) + hf₂L.toLp (Krep m f₂) := by
  rw [← MemLp.toLp_add hf₁L hf₂L, MemLp.toLp_eq_toLp_iff]
  exact Filter.Eventually.of_forall fun θ =>
    (Krep_add m hf₁ hf₁c hf₂ hf₂c θ).trans (Pi.add_apply _ _ _).symm

/-- **`KrepL2` respects subtraction**: `KrepL2(f₁−f₂) = KrepL2 f₁ − KrepL2 f₂` in `L²`. `MemLp.toLp_sub` +
    `MemLp.toLp_eq_toLp_iff` (the `Lp` elements agree since `Krep(f₁−f₂) =ᵐ Krep f₁ − Krep f₂`, `Krep_sub`).
    Lets `‖KrepL2(Fₙ−Fₘ)‖ = ‖ξₙ − ξₘ‖ → 0` drive the closure Cauchy argument. -/
theorem KrepL2_sub {m : ℝ} {f₁ f₂ : V → ℂ} (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂)
    (hf₁L : MemLp (Krep m f₁) 2 volume) (hf₂L : MemLp (Krep m f₂) 2 volume) :
    (memLp_Krep_sub hf₁ hf₁c hf₂ hf₂c hf₁L hf₂L).toLp (Krep m (f₁ - f₂))
      = hf₁L.toLp (Krep m f₁) - hf₂L.toLp (Krep m f₂) := by
  rw [← MemLp.toLp_sub hf₁L hf₂L, MemLp.toLp_eq_toLp_iff]
  exact Filter.Eventually.of_forall fun θ =>
    (Krep_sub m hf₁ hf₁c hf₂ hf₂c θ).trans (Pi.sub_apply _ _ _).symm

/-- **Strip bound in Hilbert norms**: `‖kmsFun z‖ ≤ 2·‖KrepL2 g‖·‖KrepL2 f‖` on the closed strip. The `R=0`
    annular constant `ε₀` rewritten via `{0<|θ|} =ᵐ ℝ` and `norm_toLp_Krep_eq_sqrt`. The Cauchy–Schwarz-type
    bound `‖F z‖ ≤ C·‖η‖·‖ξ‖` controlling the span-closure threading. -/
theorem norm_kmsFun_le_norm_mul {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume)
    {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    ‖kmsFun m f g z‖ ≤ 2 * ‖hgL.toLp (Krep m g)‖ * ‖hfL.toLp (Krep m f)‖ := by
  have hset : ∀ h : V → ℂ,
      (∫ θ in {θ : ℝ | (0 : ℝ) < |θ|}, ‖Krep m h θ‖ ^ 2) = ∫ θ, ‖Krep m h θ‖ ^ 2 := by
    intro h
    have hae : {θ : ℝ | (0 : ℝ) < |θ|} =ᵐ[volume] (Set.univ : Set ℝ) := by
      rw [MeasureTheory.ae_eq_univ]
      have hcompl : {θ : ℝ | (0 : ℝ) < |θ|}ᶜ = {0} := by
        ext θ; simp [abs_pos, not_not]
      rw [hcompl]; exact Real.volume_singleton
    rw [MeasureTheory.setIntegral_congr_set hae, MeasureTheory.setIntegral_univ]
  have h := norm_kmsFun_sub_kmsFunCut_le hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL
    (le_refl (0 : ℝ)) hz0 hz1
  rw [kmsFunCut_zero, sub_zero, hset g, hset f, ← norm_toLp_Krep_eq_sqrt hgL,
    ← norm_toLp_Krep_eq_sqrt hfL] at h
  calc ‖kmsFun m f g z‖
      ≤ ‖hgL.toLp (Krep m g)‖ * ‖hfL.toLp (Krep m f)‖
        + ‖hfL.toLp (Krep m f)‖ * ‖hgL.toLp (Krep m g)‖ := h
    _ = 2 * ‖hgL.toLp (Krep m g)‖ * ‖hfL.toLp (Krep m f)‖ := by ring

/-- **Difference bound (closure Cauchy keystone)**: on the closed strip,
    `‖kmsFun f₁ g₁ z − kmsFun f₂ g₂ z‖ ≤ 2‖KrepL2 g₁‖·‖KrepL2 f₁ − KrepL2 f₂‖ + 2‖KrepL2 g₁ − KrepL2 g₂‖·‖KrepL2 f₂‖`.
    Difference identity (`kmsFun_sub_left/right`) ⟹ `kmsFun_{f₁−f₂,g₁}+kmsFun_{f₂,g₁−g₂}`, each bounded by
    `norm_kmsFun_le_norm_mul` and rewritten via `KrepL2_sub`. The controlling estimate for the BCF Cauchy net. -/
theorem norm_kmsFun_sub_le {m : ℝ} (hm : 0 < m) {f₁ f₂ g₁ g₂ : V → ℂ}
    (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁) (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂)
    (hg₁ : Continuous g₁) (hg₁c : HasCompactSupport g₁) (hg₂ : Continuous g₂) (hg₂c : HasCompactSupport g₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hmf₁ : ∀ x, f₁ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmf₂ : ∀ x, f₂ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg₁ : ∀ x, g₁ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg₂ : ∀ x, g₂ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hf₁r : ∀ x, (starRingEnd ℂ) (f₁ x) = f₁ x) (hf₂r : ∀ x, (starRingEnd ℂ) (f₂ x) = f₂ x)
    (hg₁r : ∀ x, (starRingEnd ℂ) (g₁ x) = g₁ x) (hg₂r : ∀ x, (starRingEnd ℂ) (g₂ x) = g₂ x)
    (hf₁L : MemLp (Krep m f₁) 2 volume) (hf₂L : MemLp (Krep m f₂) 2 volume)
    (hg₁L : MemLp (Krep m g₁) 2 volume) (hg₂L : MemLp (Krep m g₂) 2 volume)
    {z : ℂ} (hz0 : -1 ≤ z.im) (hz1 : z.im ≤ 0) :
    ‖kmsFun m f₁ g₁ z - kmsFun m f₂ g₂ z‖
      ≤ 2 * ‖hg₁L.toLp (Krep m g₁)‖ * ‖hf₁L.toLp (Krep m f₁) - hf₂L.toLp (Krep m f₂)‖
        + 2 * ‖hg₁L.toLp (Krep m g₁) - hg₂L.toLp (Krep m g₂)‖ * ‖hf₂L.toLp (Krep m f₂)‖ := by
  have hmf₁₂ : ∀ x, (f₁ - f₂) x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0 := by
    intro x hx
    by_cases h : f₁ x = 0
    · exact hmf₂ x fun hc => hx (by rw [Pi.sub_apply, h, hc, sub_zero])
    · exact hmf₁ x h
  have hf₁₂r : ∀ x, (starRingEnd ℂ) ((f₁ - f₂) x) = (f₁ - f₂) x := fun x => by
    rw [Pi.sub_apply, map_sub, hf₁r, hf₂r]
  have hmg₁₂ : ∀ x, (g₁ - g₂) x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0 := by
    intro x hx
    by_cases h : g₁ x = 0
    · exact hmg₂ x fun hc => hx (by rw [Pi.sub_apply, h, hc, sub_zero])
    · exact hmg₁ x h
  have hg₁₂r : ∀ x, (starRingEnd ℂ) ((g₁ - g₂) x) = (g₁ - g₂) x := fun x => by
    rw [Pi.sub_apply, map_sub, hg₁r, hg₂r]
  have hid : kmsFun m f₁ g₁ z - kmsFun m f₂ g₂ z
      = kmsFun m (f₁ - f₂) g₁ z + kmsFun m f₂ (g₁ - g₂) z := by
    rw [kmsFun_sub_left hm hf₁ hf₁c hf₂ hf₂c hg₁ hg₁c hδ hmf₁ hmf₂ hmg₁ hf₁r hf₂r hg₁r hf₁L hf₂L hg₁L hz0 hz1,
      kmsFun_sub_right hm hf₂ hf₂c hg₁ hg₁c hg₂ hg₂c hδ hmf₂ hmg₁ hmg₂ hf₂r hg₁r hg₂r hf₂L hg₁L hg₂L hz0 hz1]
    ring
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  gcongr ?_ + ?_
  · have hb := norm_kmsFun_le_norm_mul (f := f₁ - f₂) hm (hf₁.sub hf₂) (hf₁c.sub hf₂c) hg₁ hg₁c hδ hmf₁₂ hmg₁
      hf₁₂r hg₁r (memLp_Krep_sub hf₁ hf₁c hf₂ hf₂c hf₁L hf₂L) hg₁L hz0 hz1
    rwa [KrepL2_sub hf₁ hf₁c hf₂ hf₂c hf₁L hf₂L] at hb
  · have hb := norm_kmsFun_le_norm_mul (g := g₁ - g₂) hm hf₂ hf₂c (hg₁.sub hg₂) (hg₁c.sub hg₂c) hδ hmf₂ hmg₁₂
      hf₂r hg₁₂r hf₂L (memLp_Krep_sub hg₁ hg₁c hg₂ hg₂c hg₁L hg₂L) hz0 hz1
    rwa [KrepL2_sub hg₁ hg₁c hg₂ hg₂c hg₁L hg₂L] at hb

/-- **Boost-translate preserves `L²`**: `MemLp (Krep m (boostTest a f)) 2` from `MemLp (Krep m f) 2`, since
    `Krep m (boostTest a f) = Krep m f ∘ (·+a)` (`Krep_boost`) and translation is measure-preserving. -/
theorem memLp_Krep_boostTest {m : ℝ} {f : V → ℂ} (hf : MemLp (Krep m f) 2 volume) (a : ℝ) :
    MemLp (Krep m (boostTest a f)) 2 volume := by
  have heq : Krep m (boostTest a f) = (Krep m f) ∘ (fun θ => θ + a) := by
    funext θ; exact Krep_boost m a f θ
  rw [heq]
  exact hf.comp_measurePreserving (measurePreserving_add_right volume a)

/-- **★★★★★ `StripKMSrvd` (RvD Def 3.4) DISCHARGED for a wedge generator pair, axiom-free.** For real
    wedge-supported `f, g` (continuous, compact support inside the wedge with margin `δ>0`, `MemLp` one-particle
    amplitudes), the boost-orbit KMS witness exists with all of RvD Def 3.4: `DiffContOnCl` on the strip
    (`kmsFun_diffContOnCl`), bounded (`norm_kmsFun_le_closed`, via the global clamp), and the two boost-orbit
    edges. This is the complete discharge of the boost-KMS / Bisognano–Wichmann analytic input for the free
    field — no Hardy/Paley–Wiener theory, no Tomita–Takesaki, no axioms. -/
theorem stripKMSrvd_pair {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume) :
    ∃ F : ℂ → ℂ, DiffContOnCl ℂ F (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) ∧
      (∃ M : ℝ, ∀ z : ℂ, ‖F z‖ ≤ M) ∧
      (∀ t : ℝ, F t = inner ℂ (hgL.toLp (Krep m g)) (boostUnitary (2 * Real.pi * t) (hfL.toLp (Krep m f)))) ∧
      (∀ t : ℝ, F ((t : ℂ) - Complex.I)
        = inner ℂ (boostUnitary (2 * Real.pi * t) (hfL.toLp (Krep m f))) (hgL.toLp (Krep m g))) :=
  stripKMSrvd_pair_of_regularity m hfL hgL (fun t => memLp_Krep_boostTest hfL (-(2 * Real.pi * t))) hfr hgr
    (kmsFun_diffContOnCl hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL)
    (norm_kmsFun_le_closed hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL)

open scoped BoundedContinuousFunction in
/-- **(c1) The KMS witness as a bounded continuous function on the closed strip** (nice `f,g`). Continuous via
    `kmsFun_continuousOn_closed`, bounded by `2‖KrepL2 g‖·‖KrepL2 f‖` via `norm_kmsFun_le_norm_mul`. The vehicle
    for the uniform-Cauchy limit (`norm_kmsFun_sub_le`) in the span-closure threading to `StripKMSrvd 𝒦_W`. -/
noncomputable def kmsBCF {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume) :
    (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0) →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (Set.restrict (Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0) (kmsFun m f g))
    ((kmsFun_continuousOn_closed hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL).restrict)
    (2 * ‖hgL.toLp (Krep m g)‖ * ‖hfL.toLp (Krep m f)‖)
    (fun z => by
      have hz := z.2
      rw [Set.mem_preimage, Set.mem_Icc] at hz
      exact norm_kmsFun_le_norm_mul hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL hz.1 hz.2)

open scoped BoundedContinuousFunction in
@[simp] theorem kmsBCF_apply {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ : ℝ} (hδ : 0 < δ)
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume)
    (z : Complex.im ⁻¹' Set.Icc (-1 : ℝ) 0) :
    kmsBCF hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL z = kmsFun m f g (z : ℂ) := rfl

open scoped BoundedContinuousFunction in
/-- **(c2) BCF Cauchy-control step**: `dist (kmsBCF f₁ g₁) (kmsBCF f₂ g₂) ≤ ` the difference bound. Via
    `BoundedContinuousFunction.dist_le` + the pointwise `norm_kmsFun_sub_le`. (Common margin `δ`.) -/
theorem dist_kmsBCF_le {m : ℝ} (hm : 0 < m) {f₁ f₂ g₁ g₂ : V → ℂ}
    (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁) (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂)
    (hg₁ : Continuous g₁) (hg₁c : HasCompactSupport g₁) (hg₂ : Continuous g₂) (hg₂c : HasCompactSupport g₂)
    {δ : ℝ} (hδ : 0 < δ)
    (hmf₁ : ∀ x, f₁ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmf₂ : ∀ x, f₂ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg₁ : ∀ x, g₁ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg₂ : ∀ x, g₂ x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hf₁r : ∀ x, (starRingEnd ℂ) (f₁ x) = f₁ x) (hf₂r : ∀ x, (starRingEnd ℂ) (f₂ x) = f₂ x)
    (hg₁r : ∀ x, (starRingEnd ℂ) (g₁ x) = g₁ x) (hg₂r : ∀ x, (starRingEnd ℂ) (g₂ x) = g₂ x)
    (hf₁L : MemLp (Krep m f₁) 2 volume) (hf₂L : MemLp (Krep m f₂) 2 volume)
    (hg₁L : MemLp (Krep m g₁) 2 volume) (hg₂L : MemLp (Krep m g₂) 2 volume) :
    dist (kmsBCF hm hf₁ hf₁c hg₁ hg₁c hδ hmf₁ hmg₁ hf₁r hg₁r hf₁L hg₁L)
        (kmsBCF hm hf₂ hf₂c hg₂ hg₂c hδ hmf₂ hmg₂ hf₂r hg₂r hf₂L hg₂L)
      ≤ 2 * ‖hg₁L.toLp (Krep m g₁)‖ * ‖hf₁L.toLp (Krep m f₁) - hf₂L.toLp (Krep m f₂)‖
        + 2 * ‖hg₁L.toLp (Krep m g₁) - hg₂L.toLp (Krep m g₂)‖ * ‖hf₂L.toLp (Krep m f₂)‖ := by
  rw [BoundedContinuousFunction.dist_le (by positivity)]
  intro z
  have hz := z.2
  rw [Set.mem_preimage, Set.mem_Icc] at hz
  rw [kmsBCF_apply, kmsBCF_apply, Complex.dist_eq]
  exact norm_kmsFun_sub_le hm hf₁ hf₁c hf₂ hf₂c hg₁ hg₁c hg₂ hg₂c hδ hmf₁ hmf₂ hmg₁ hmg₂
    hf₁r hf₂r hg₁r hg₂r hf₁L hf₂L hg₁L hg₂L hz.1 hz.2

open scoped BoundedContinuousFunction in
/-- **`kmsBCF` is independent of the margin `δ`** (the BCF is determined by its coeFn `kmsFun m f g`, which has
    no `δ`). Lets the closure Cauchy sequence over approximants with shrinking margins `δₙ→0` be compared at a
    common (minimal) `δ` via `dist_kmsBCF_le`. -/
theorem kmsBCF_congr {m : ℝ} (hm : 0 < m) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) {δ δ' : ℝ} (hδ : 0 < δ)
    (hδ' : 0 < δ')
    (hmf : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmf' : ∀ x, f x ≠ 0 → δ' ≤ x 1 - x 0 ∧ δ' ≤ x 1 + x 0)
    (hmg : ∀ x, g x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0)
    (hmg' : ∀ x, g x ≠ 0 → δ' ≤ x 1 - x 0 ∧ δ' ≤ x 1 + x 0)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hfL : MemLp (Krep m f) 2 volume) (hgL : MemLp (Krep m g) 2 volume) :
    kmsBCF hm hf hfc hg hgc hδ hmf hmg hfr hgr hfL hgL
      = kmsBCF hm hf hfc hg hgc hδ' hmf' hmg' hfr hgr hfL hgL := by
  ext z; rw [kmsBCF_apply, kmsBCF_apply]

/-! ### The nice-core wedge generators as an ℝ-subspace (the standard BW wedge subspace) -/

/-- **A nice wedge test function**: the bundled data for a one-particle generator of the wedge standard
    subspace — continuous, compactly supported, real, with a `δ`-margin inside the wedge, and `L²` on-shell
    amplitude.  This is the standard AQFT wedge-localization core class (compactly-supported `δ`-margin
    functions), closed under `±`, so the generators `{NiceTest.vec}` already form an ℝ-subspace — and the
    BW/KMS extension over `closure(span(niceWedgeGenSet))` reduces to a closure limit over single nice
    generator PAIRS (no density theorem; the `kmsBCF` Cauchy limit closes the span). -/
structure NiceTest (m : ℝ) where
  /-- the underlying test function -/
  f : V → ℂ
  cont : Continuous f
  cpt : HasCompactSupport f
  /-- the wedge margin -/
  δ : ℝ
  hδ : 0 < δ
  margin : ∀ x, f x ≠ 0 → δ ≤ x 1 - x 0 ∧ δ ≤ x 1 + x 0
  real : ∀ x, (starRingEnd ℂ) (f x) = f x
  memLp : MemLp (Krep m f) 2 volume

/-- The one-particle vector `KrepL2 f ∈ L²` of a nice test function. -/
noncomputable def NiceTest.vec {m : ℝ} (N : NiceTest m) : Lp ℂ 2 (volume : Measure ℝ) :=
  N.memLp.toLp (Krep m N.f)

/-- **Nice tests are closed under addition** (margin → `min`, support → union): the sum is again nice.
    The structural engine behind `span_ℝ(niceWedgeGenSet) = niceWedgeGenSet`. -/
def NiceTest.add {m : ℝ} (N₁ N₂ : NiceTest m) : NiceTest m where
  f := N₁.f + N₂.f
  cont := N₁.cont.add N₂.cont
  cpt := N₁.cpt.add N₂.cpt
  δ := min N₁.δ N₂.δ
  hδ := lt_min N₁.hδ N₂.hδ
  margin := fun x hx => by
    rw [Pi.add_apply] at hx
    by_cases h : N₁.f x = 0
    · have h2 : N₂.f x ≠ 0 := by rw [h, zero_add] at hx; exact hx
      exact ⟨le_trans (min_le_right _ _) (N₂.margin x h2).1,
             le_trans (min_le_right _ _) (N₂.margin x h2).2⟩
    · exact ⟨le_trans (min_le_left _ _) (N₁.margin x h).1,
             le_trans (min_le_left _ _) (N₁.margin x h).2⟩
  real := fun x => by simp only [Pi.add_apply, map_add, N₁.real, N₂.real]
  memLp := memLp_Krep_add N₁.cont N₁.cpt N₂.cont N₂.cpt N₁.memLp N₂.memLp

/-- **`NiceTest.add` realizes Hilbert-space addition**: `(N₁.add N₂).vec = N₁.vec + N₂.vec` (via `KrepL2_add`). -/
theorem NiceTest.vec_add {m : ℝ} (N₁ N₂ : NiceTest m) :
    (N₁.add N₂).vec = N₁.vec + N₂.vec :=
  KrepL2_add N₁.cont N₁.cpt N₂.cont N₂.cpt N₁.memLp N₂.memLp

/-- **The nice-core wedge generating set**: the one-particle vectors `KrepL2 f` from *nice* wedge test
    functions.  The standard BW wedge-localization core; an ℝ-subspace as a set (closed under `±` via
    `NiceTest.add`/`vec_add`), so `span_ℝ` of it adds nothing. -/
noncomputable def niceWedgeGenSet (m : ℝ) : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  Set.range (fun N : NiceTest m => N.vec)

/-- Membership unfolding for `niceWedgeGenSet`: `ξ` is a nice generator iff it is some `NiceTest.vec`. -/
theorem mem_niceWedgeGenSet {m : ℝ} {ξ : Lp ℂ 2 (volume : Measure ℝ)} :
    ξ ∈ niceWedgeGenSet m ↔ ∃ N : NiceTest m, N.vec = ξ := Iff.rfl

/-- **`niceWedgeGenSet` is closed under addition** (witness: `NiceTest.add`), the set-level statement that
    it is already an ℝ-subspace (so `span_ℝ` collapses to it). -/
theorem niceWedgeGenSet_add_mem {m : ℝ} {ξ η : Lp ℂ 2 (volume : Measure ℝ)}
    (hξ : ξ ∈ niceWedgeGenSet m) (hη : η ∈ niceWedgeGenSet m) :
    ξ + η ∈ niceWedgeGenSet m := by
  obtain ⟨N₁, rfl⟩ := hξ
  obtain ⟨N₂, rfl⟩ := hη
  exact ⟨N₁.add N₂, N₁.vec_add N₂⟩

end QIQTH.Fock.BoostKMS
