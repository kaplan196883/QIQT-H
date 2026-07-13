/-
  # The abstract heat semigroup `e^{−tA}` via our own bounded Borel functional calculus

  This file builds the **ABSTRACT heat semigroup** `e^{−tA}` of a positive self-adjoint
  operator `A` — presented as `A = ∫ a dE` for a nonnegative symbol `a : Ω → ℝ` and a
  projection-valued measure `E` (`QIQTH.Spectral.ProjectionValuedMeasure`) — assembled
  entirely from our OWN bounded Borel functional calculus (`QIQTH.Spectral.boundedFC` and
  its laws in `PVM.lean`).  It delivers:

    • the **semigroup law** `e^{−sA} · e^{−tA} = e^{−(s+t)A}`  (`heatSemigroup_mul`),
    • the **`t=0` identity** `e^{0·A} = 1`                      (`heatSemigroup_zero`),
    • a **uniform operator bound** `‖e^{−tA}‖ ≤ 2`             (`heatSemigroup_norm_le`),
    • **positivity** `0 ≤ Re⟪x, e^{−tA} x⟫`                    (`heatSemigroup_inner_nonneg`).

  ### Phase B additions (this file, below)

    • the **SHARP contraction** `‖e^{−tA}‖ ≤ 1`                (`heatSemigroup_norm_le_one`),
      now PROVEN via the tower's norm-squared identity
      `‖boundedFC g x‖² = ∫ |g|² dμ_x` (`norm_boundedFC_sq`) — each `|e^{−t a}|² ≤ 1`
      and `∫ 1 dμ_x = ‖x‖²` (`scalarMeasure_univ`).  This SUPERSEDES the honest `2C = 2`
      note for this operator: the sharp `≤ 1` holds.
    • the **norm-squared bridge** `‖e^{−tA}x − x‖² = ∫ |e^{−t a} − 1|² dμ_x`
      (`heatSemigroup_sub_id_normSq`), and
    • **STRONG CONTINUITY in `L²`-spectral form**: the spectral integral
      `∫ |e^{−t a} − 1|² dμ_x → 0` as `t → 0⁺` (`heatSemigroup_L2_tendsto_zero`), by
      dominated convergence over the finite scalar spectral measure `μ_x`.  Together the
      bridge + the `L²`-limit MEAN `‖e^{−tA}x − x‖ → 0` (strong continuity of the
      semigroup at the origin); the `L²` form is the clean statement that avoids threading
      the dependent hypothesis `0 ≤ t` through a `fun t` (see note at the theorems).

  ⚠ The earlier `‖e^{−tA}‖ ≤ 2` (`heatSemigroup_norm_le`) is kept as the tower's raw `2C`
  bound; `heatSemigroup_norm_le_one` is the sharp replacement.

  ### Phase B1 additions (the GENERATOR — this file, below)

  The **generator** `−A = d/dt e^{−tA}|_{t=0⁺}` is now BUILT, as the REAL analogue of the tower's
  unitary Stone generator `hasDerivAt_boundedFC_expSymbol` (`d/dt e^{itK} x|₀ = i·K x`).  Two forms
  land, both axiom-free (std-3) and `sorry`-free:

    • the **`L²`-spectral form** `heatSymbol_diffQuotient_L2_tendsto`: as `t → 0⁺`,
      `∫ ‖(e^{−t a}−1)/t + a‖² dμ_x → 0` — i.e. the slope `(e^{−tA}x − x)/t → −A x` in `L²(μ_x)`
      (via Bochner filter dominated convergence, dominated by `a² ∈ L¹(μ_x)`), and
    • the **FULL packaged derivative** `hasDerivWithinAt_heatSemigroup`:
      `HasDerivWithinAt (fun t => e^{−tA}x) (−A x) (Set.Ici 0) 0` — the honest **one-sided**
      (semigroup-direction, `t ≥ 0`) derivative (the heat symbol is bounded by `1` only for `t ≥ 0`,
      so a two-sided `HasDerivAt` is unavailable; the function is written
      `fun t => if 0 ≤ t then heatSemigroup ... x else x`, a total `ℝ → H` equal to the genuine
      semigroup on `[0,∞)`).  Assembled from the `L²` heart + the heat **distance identity**
      `dist_boundedFC_add_fcOp_sq` (real/`−1` analogue of the tower's `dist_boundedFC_smul_fcOp_sq`,
      lintegral-based to dodge the Bochner-`whnf` wall) via its truncation lemma
      `boundedFC_add_fcTrunc_lintegral_tendsto`.

  With `A = ∫ a dE = fcOp a` self-adjoint (`fcOp_symmetric`), this makes `t ↦ e^{−tA}` a genuine
  `C₀`-contraction-semigroup with generator `−A` — the full abstract heat-semigroup package.

  ## Scope (Phase A of `HEAT_KERNEL_INFRASTRUCTURE_PLAN.md`)

  This is the **ABSTRACT operator semigroup ONLY**.  It does NOT build the manifold heat
  kernel.  That the Laplace–Beltrami `Δ` on `L²(M)` is such an operator (Phase C), that it
  has discrete spectrum (Phase D — Rellich compactness, absent from Mathlib), or that it
  has a smooth integral kernel `p_t(x,y)` (Phase E — elliptic regularity, absent) are the
  WALL.  This file is NOT the conjecture, NOT the strong holographic principle, NOT quantum
  gravity — just the semigroup algebra.  No axioms, no `sorry`.

  Assembled from existing `QIQTH.Spectral` FC laws; adds NO new infrastructure and NO
  project axioms.
-/

import QIQTH.Spectral.PVM
import QIQTH.Spectral.UnboundedFC

namespace QIQTH
namespace Spectral

open scoped BigOperators

variable {Ω : Type*} {H : Type*}
  [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **heat symbol** `e^{−t·a(ω)}` for a (nonnegative) generator symbol `a : Ω → ℝ`:
    the `ℝ → ℂ` coercion of the real exponent `−(t·a ω)` fed to `Complex.exp`.  For `t ≥ 0`
    and `a ≥ 0` it is a real number in `(0,1]`. -/
noncomputable def heatSymbol (a : Ω → ℝ) (t : ℝ) : Ω → ℂ :=
  fun ω => Complex.exp ((-(t * a ω) : ℝ) : ℂ)

/-- The heat symbol is measurable whenever the generator symbol is. -/
theorem heatSymbol_measurable {a : Ω → ℝ} (ha : Measurable a) (t : ℝ) :
    Measurable (heatSymbol a t) := by
  unfold heatSymbol
  fun_prop

omit [MeasurableSpace Ω] in
/-- For `t ≥ 0` and `a ≥ 0` the heat symbol is a contraction: `‖e^{−t a(ω)}‖ ≤ 1`.
    (`‖Complex.exp z‖ = Real.exp z.re` with `z.re = −(t·a ω) ≤ 0`.) -/
theorem heatSymbol_norm_le {a : Ω → ℝ} (ha0 : ∀ ω, 0 ≤ a ω) {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    ‖heatSymbol a t ω‖ ≤ 1 := by
  rw [heatSymbol, Complex.norm_exp, Complex.ofReal_re]
  calc Real.exp (-(t * a ω))
      ≤ Real.exp 0 := Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg ht (ha0 ω)))
    _ = 1 := Real.exp_zero

omit [MeasurableSpace Ω] in
/-- **`heatSymbol` in exponential-of-product form** `e^{−t·a(ω)} = exp(−(↑t·↑a(ω)))` — the shape the
    generic derivative/slope lemmas are stated in. -/
theorem heatSymbol_eq_exp_neg_mul (a : Ω → ℝ) (t : ℝ) (ω : Ω) :
    heatSymbol a t ω = Complex.exp (-((t : ℂ) * (a ω : ℂ))) := by
  rw [heatSymbol]
  congr 1
  push_cast
  ring

/-- **Pointwise generator derivative** `d/dt e^{−t c}|₀ = −c` — the REAL analogue of the tower's unitary
    `hasDerivAt_expSymbol` (`d/dt e^{itc}|₀ = i·c`).  The diff quotient `(e^{−tc}−1)/t → −c`. -/
theorem heatSymbol_hasDerivAt (c : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-((t : ℂ) * (c : ℂ)))) (-(c : ℂ)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => -((t : ℂ) * (c : ℂ))) (-(c : ℂ)) 0 := by
    have hb : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    simpa using (hb.mul_const (c : ℂ)).neg
  simpa using h1.cexp

/-- **The heat difference-quotient slope** `(e^{−t c}−1)/t → −c` as `t→0` (`t≠0`) — the pointwise input
    (in `𝓝[≠]0` slope form) to the generator relation, mirroring `expSymbol_slope_tendsto`. -/
theorem heatSymbol_slope_tendsto (c : ℝ) :
    Filter.Tendsto (fun t : ℝ => (Complex.exp (-((t : ℂ) * (c : ℂ))) - 1) / (t : ℂ))
      (nhdsWithin 0 {0}ᶜ) (nhds (-(c : ℂ))) := by
  have h := heatSymbol_hasDerivAt c
  rw [hasDerivAt_iff_tendsto_slope] at h
  refine h.congr fun t => ?_
  simp only [slope, vsub_eq_sub, sub_zero, Complex.ofReal_zero, zero_mul, neg_zero,
    Complex.exp_zero, Complex.real_smul, Complex.ofReal_inv]
  ring

omit [MeasurableSpace Ω] in
/-- **Heat difference-quotient `L²` domination**: for `t>0` and `a ≥ 0`,
    `‖(e^{−t a(ω)}−1)/t + a(ω)‖ ≤ a(ω)`.  Since `(e^{−t a}−1)/t ∈ [−a, 0]` (from `1−ta ≤ e^{−ta} ≤ 1`),
    the deviation `(e^{−ta}−1)/t + a ∈ [0, a]`; the uniform `L²(μ_x)`-domination (by `a ∈ L²`) for the
    dominated-convergence generator step.  Real analogue of `norm_expSymbol_sub_one_div_le`. -/
theorem heatSymbol_diffQuotient_norm_le {a : Ω → ℝ} (ha0 : ∀ ω, 0 ≤ a ω) {t : ℝ} (ht : 0 < t)
    (ω : Ω) :
    ‖(heatSymbol a t ω - 1) / (t : ℂ) + (a ω : ℂ)‖ ≤ a ω := by
  have hexp : heatSymbol a t ω = ((Real.exp (-(t * a ω)) : ℝ) : ℂ) := by
    rw [heatSymbol, Complex.ofReal_exp]
  have hcx : (heatSymbol a t ω - 1) / (t : ℂ) + (a ω : ℂ)
      = (((Real.exp (-(t * a ω)) - 1) / t + a ω : ℝ) : ℂ) := by
    rw [hexp]; push_cast; ring
  rw [hcx, Complex.norm_real, Real.norm_eq_abs]
  have he_ge : 1 - t * a ω ≤ Real.exp (-(t * a ω)) := by
    have h := Real.add_one_le_exp (-(t * a ω)); linarith
  have he_le : Real.exp (-(t * a ω)) ≤ 1 := by
    have h0 : -(t * a ω) ≤ 0 := by nlinarith [ha0 ω, ht.le]
    calc Real.exp (-(t * a ω)) ≤ Real.exp 0 := Real.exp_le_exp.mpr h0
      _ = 1 := Real.exp_zero
  have hlow : -(a ω) ≤ (Real.exp (-(t * a ω)) - 1) / t := by
    rw [le_div_iff₀ ht]; nlinarith [he_ge]
  have hupp : (Real.exp (-(t * a ω)) - 1) / t ≤ 0 := by
    rw [div_nonpos_iff]; right; exact ⟨by linarith, ht.le⟩
  rw [abs_le]
  exact ⟨by nlinarith [hlow, ha0 ω], by linarith [hupp]⟩

namespace ProjectionValuedMeasure

variable (P : ProjectionValuedMeasure Ω H)

/-- **★ The abstract heat semigroup `e^{−tA}`** of the positive self-adjoint operator
    `A = ∫ a dE` (`a ≥ 0`), defined through the bounded Borel functional calculus of its
    heat symbol.  A genuine operator on `H` for every `t ≥ 0`. -/
noncomputable def heatSemigroup {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {t : ℝ} (ht : 0 ≤ t) : H →L[ℂ] H :=
  P.boundedFC (heatSymbol_measurable ha t) zero_le_one (heatSymbol_norm_le ha0 ht)

/-- **★★ The semigroup law** `e^{−sA} · e^{−tA} = e^{−(s+t)A}`.
    From `boundedFC_mul` (multiplicativity of the FC) and the pointwise identity
    `e^{−s a} · e^{−t a} = e^{−(s+t) a}` (`Complex.exp_add`). -/
theorem heatSemigroup_mul {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    P.heatSemigroup ha ha0 hs * P.heatSemigroup ha ha0 ht
      = P.heatSemigroup ha ha0 (add_nonneg hs ht) := by
  have hpm : Measurable (fun ω => heatSymbol a s ω * heatSymbol a t ω) :=
    (heatSymbol_measurable ha s).mul (heatSymbol_measurable ha t)
  have hpb : ∀ ω, ‖heatSymbol a s ω * heatSymbol a t ω‖ ≤ 1 := fun ω => by
    rw [norm_mul]
    nlinarith [heatSymbol_norm_le ha0 hs ω, heatSymbol_norm_le ha0 ht ω,
      norm_nonneg (heatSymbol a s ω), norm_nonneg (heatSymbol a t ω)]
  have hsym : heatSymbol a (s + t) = fun ω => heatSymbol a s ω * heatSymbol a t ω := by
    funext ω
    have he : (-(( s + t) * a ω) : ℝ) = -(s * a ω) + -(t * a ω) := by ring
    simp only [heatSymbol, he, Complex.ofReal_add, Complex.exp_add]
  simp only [heatSemigroup]
  rw [← P.boundedFC_mul (heatSymbol_measurable ha s) zero_le_one (heatSymbol_norm_le ha0 hs)
      (heatSymbol_measurable ha t) zero_le_one (heatSymbol_norm_le ha0 ht) hpm zero_le_one hpb]
  exact (P.boundedFC_congr (heatSymbol_measurable ha (s + t)) zero_le_one
    (heatSymbol_norm_le ha0 (add_nonneg hs ht)) hpm zero_le_one hpb hsym).symm

/-- **★ The `t = 0` identity** `e^{0·A} = 1` (unitality of the semigroup at the origin).
    `heatSymbol a 0 = 1` pointwise, and `boundedFC (const 1) = 1`. -/
theorem heatSemigroup_zero {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω) :
    P.heatSemigroup ha ha0 (le_refl (0 : ℝ)) = 1 := by
  have h1 : heatSymbol a 0 = (fun _ => (1 : ℂ)) := by
    funext ω; simp [heatSymbol]
  simp only [heatSemigroup]
  rw [P.boundedFC_congr (heatSymbol_measurable ha 0) zero_le_one
      (heatSymbol_norm_le ha0 (le_refl 0)) measurable_const (norm_nonneg (1 : ℂ))
      (fun _ => le_rfl) h1, P.boundedFC_const (1 : ℂ), one_smul]

/-- **★ Uniform operator bound** `‖e^{−tA}‖ ≤ 2`.  This is the tower's `2C` estimate with
    `C = 1` (`boundedFC_norm_le`), NOT the sharp contraction `≤ 1`. -/
theorem heatSemigroup_norm_le {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {t : ℝ} (ht : 0 ≤ t) : ‖P.heatSemigroup ha ha0 ht‖ ≤ 2 := by
  simpa [heatSemigroup] using
    P.boundedFC_norm_le (heatSymbol_measurable ha t) zero_le_one (heatSymbol_norm_le ha0 ht)

/-- **★ Positivity** `0 ≤ Re⟪x, e^{−tA} x⟫`: `e^{−tA}` is a positive operator.
    `⟪x, e^{−tA} x⟫ = ∫ e^{−t a} dμ_x` (`inner_boundedFC_self`), a real integral of the
    nonnegative real symbol, so its real part is `≥ 0`. -/
theorem heatSemigroup_inner_nonneg {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {t : ℝ} (ht : 0 ≤ t) (x : H) :
    0 ≤ (inner ℂ x (P.heatSemigroup ha ha0 ht x)).re := by
  have hpt : ∀ ω, heatSymbol a t ω = ((Real.exp (-(t * a ω)) : ℝ) : ℂ) := fun ω => by
    rw [heatSymbol, Complex.ofReal_exp]
  simp only [heatSemigroup]
  rw [P.inner_boundedFC_self (heatSymbol_measurable ha t) zero_le_one (heatSymbol_norm_le ha0 ht) x]
  have hre : (∫ ω, heatSymbol a t ω ∂(P.scalarMeasure x))
      = ((∫ ω, Real.exp (-(t * a ω)) ∂(P.scalarMeasure x) : ℝ) : ℂ) := by
    simp only [hpt]; exact integral_ofReal
  rw [hre, Complex.ofReal_re]
  exact MeasureTheory.integral_nonneg (fun ω => (Real.exp_pos _).le)

/-- **★ SHARP CONTRACTION** `‖e^{−tA}‖ ≤ 1` — the heat semigroup is a genuine
    contraction (Phase B).  Proof via the tower's norm-squared identity
    `‖boundedFC g x‖² = ∫ |g|² dμ_x` (`norm_boundedFC_sq`): each `|e^{−t a(ω)}|² ≤ 1`
    (`heatSymbol_norm_le` squared), so
    `‖e^{−tA}x‖² = ∫ |e^{−t a}|² dμ_x ≤ ∫ 1 dμ_x = (μ_x univ).toReal = ‖x‖²`
    (`scalarMeasure_univ`), hence `‖e^{−tA}x‖ ≤ ‖x‖`.  Sharpens `heatSemigroup_norm_le`. -/
theorem heatSemigroup_norm_le_one {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {t : ℝ} (ht : 0 ≤ t) : ‖P.heatSemigroup ha ha0 ht‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  rw [one_mul]
  have hsq : ‖P.heatSemigroup ha ha0 ht x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [heatSemigroup, P.norm_boundedFC_sq]
    calc (∫ ω, ‖heatSymbol a t ω‖ ^ 2 ∂(P.scalarMeasure x))
        ≤ ∫ _ω, (1 : ℝ) ∂(P.scalarMeasure x) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
            (MeasureTheory.integrable_const (1 : ℝ))
            (Filter.Eventually.of_forall (fun ω => ?_))
          have := heatSymbol_norm_le ha0 ht ω
          nlinarith [norm_nonneg (heatSymbol a t ω)]
      _ = ‖x‖ ^ 2 := by
          rw [MeasureTheory.integral_const, MeasureTheory.measureReal_def,
            P.scalarMeasure_univ, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_one]
  have h1 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h1

/-- **★★ The norm-squared bridge for strong continuity**:
    `‖e^{−tA}x − x‖² = ∫ |e^{−t a(ω)} − 1|² dμ_x`.  Since `1 = boundedFC(const 1)`
    (`boundedFC_const`), the difference `e^{−tA} − 1 = boundedFC(e^{−t a} − 1)`, and the
    identity is the tower's difference-norm law `norm_boundedFC_sub_sq`. -/
theorem heatSemigroup_sub_id_normSq {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {t : ℝ} (ht : 0 ≤ t) (x : H) :
    ‖P.heatSemigroup ha ha0 ht x - x‖ ^ 2
      = ∫ ω, ‖heatSymbol a t ω - 1‖ ^ 2 ∂(P.scalarMeasure x) := by
  have hconst : P.boundedFC (f := fun _ => (1 : ℂ)) measurable_const
      (norm_nonneg (1 : ℂ)) (fun _ => le_rfl) x = x := by
    rw [P.boundedFC_const (1 : ℂ)]; simp
  have key := P.norm_boundedFC_sub_sq (heatSymbol_measurable ha t) zero_le_one
    (heatSymbol_norm_le ha0 ht) measurable_const (norm_nonneg (1 : ℂ)) (fun _ => le_rfl) x
  rw [hconst] at key
  rw [heatSemigroup]
  exact key

/-- **★★ STRONG CONTINUITY (`L²`-spectral form)**: the spectral integral
    `∫ |e^{−t a(ω)} − 1|² dμ_x → 0` as `t → 0⁺`.  By dominated convergence
    (`tendsto_integral_filter_of_dominated_convergence`) over the FINITE scalar spectral
    measure `μ_x`: the integrand is dominated by the constant `4` (since
    `‖e^{−t a} − 1‖ ≤ ‖e^{−t a}‖ + 1 ≤ 2` for `t ≥ 0`) — integrable because `μ_x` is finite
    — and converges pointwise to `0` (as `t → 0`, `e^{−t a(ω)} = exp(−t·a ω) → 1`).

    Combined with `heatSemigroup_sub_id_normSq` this MEANS `‖e^{−tA}x − x‖ → 0`: strong
    continuity of the semigroup at the origin.  (Stated in `L²`-form to avoid threading the
    dependent hypothesis `0 ≤ t` through the `fun t`; the pointwise heat-symbol convergence
    carries no such hypothesis.) -/
theorem heatSemigroup_L2_tendsto_zero {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    (x : H) :
    Filter.Tendsto (fun t : ℝ => ∫ ω, ‖heatSymbol a t ω - 1‖ ^ 2 ∂(P.scalarMeasure x))
      (nhdsWithin 0 (Set.Ici (0 : ℝ))) (nhds 0) := by
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := P.scalarMeasure x)
    (l := nhdsWithin 0 (Set.Ici (0 : ℝ)))
    (F := fun (t : ℝ) (ω : Ω) => ‖heatSymbol a t ω - 1‖ ^ 2)
    (f := fun _ : Ω => (0 : ℝ))
    (bound := fun _ : Ω => (4 : ℝ))
    (hF_meas := Filter.Eventually.of_forall (fun t =>
      (((heatSymbol_measurable ha t).sub measurable_const).norm.pow_const 2).aestronglyMeasurable))
    (h_bound := ?_) (bound_integrable := MeasureTheory.integrable_const (4 : ℝ))
    (h_lim := ?_)
  · simpa using h
  · -- domination: ‖‖e^{−t a} − 1‖²‖ ≤ 4 for t ≥ 0
    refine Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ?_)
    have ht0 : (0 : ℝ) ≤ t := ht
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have hb : ‖heatSymbol a t ω - 1‖ ≤ 2 := by
      calc ‖heatSymbol a t ω - 1‖ ≤ ‖heatSymbol a t ω‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by
            have := heatSymbol_norm_le ha0 ht0 ω; rw [norm_one]; linarith
        _ = 2 := by norm_num
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hb, norm_nonneg (heatSymbol a t ω - 1)]
  · -- pointwise convergence: e^{−t a(ω)} → 1, so ‖· − 1‖² → 0
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have hc : Continuous (fun t : ℝ => heatSymbol a t ω) := by unfold heatSymbol; fun_prop
    have h0 : heatSymbol a (0 : ℝ) ω = 1 := by simp [heatSymbol]
    have htend : Filter.Tendsto (fun t : ℝ => heatSymbol a t ω)
        (nhdsWithin 0 (Set.Ici (0 : ℝ))) (nhds 1) := by
      have hh : Filter.Tendsto (fun t : ℝ => heatSymbol a t ω)
          (nhdsWithin 0 (Set.Ici (0 : ℝ))) (nhds (heatSymbol a 0 ω)) :=
        (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      rwa [h0] at hh
    have h2 := ((htend.sub (tendsto_const_nhds (x := (1 : ℂ)))).norm).pow 2
    simpa using h2

/-- **★★ The generator relation in `L²`-spectral form (B1)** — the heat analogue of the tower's Stone
    generator relation `hasDerivAt_boundedFC_expSymbol`.  As `t → 0⁺` the slope of the heat symbol
    converges to `−a` in `L²(μ_x)`:
    `∫ ‖(e^{−t a(ω)}−1)/t + a(ω)‖² dμ_x → 0`.
    Since `‖(e^{−tA}x − x)/t − (−A x)‖² = ∫ ‖(e^{−t a}−1)/t − (−a)‖² dμ_x` (the norm-squared bridge
    `norm_boundedFC_sq` applied to the difference-quotient symbol), this MEANS
    `(e^{−tA}x − x)/t → −A x` in `H` — i.e. `d/dt e^{−tA}x|_{0⁺} = −A x`, with `A = ∫ a dE = fcOp a`.
    (Stated over `𝓝[>]0` — the honest one-sided/semigroup direction, `t ≥ 0`; this avoids threading the
    dependent bound `0 ≤ t` through a bare `fun t`.)  Bochner dominated convergence over the finite
    scalar spectral measure `μ_x`: pointwise `→ 0` from `heatSymbol_slope_tendsto`, dominated by
    `a² ∈ L¹(μ_x)` (finite exactly because `x ∈ fcDomain a`), via `heatSymbol_diffQuotient_norm_le`. -/
theorem heatSymbol_diffQuotient_L2_tendsto {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {x : H} (hx : x ∈ P.fcDomain a) :
    Filter.Tendsto
      (fun t : ℝ => ∫ ω, ‖(heatSymbol a t ω - 1) / (t : ℂ) + (a ω : ℂ)‖ ^ 2 ∂(P.scalarMeasure x))
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
  have hintsq : MeasureTheory.Integrable (fun ω => a ω ^ 2) (P.scalarMeasure x) :=
    (P.mem_fcDomain_iff_integrable_sq ha x).mp hx
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := P.scalarMeasure x)
    (l := nhdsWithin 0 (Set.Ioi (0 : ℝ)))
    (F := fun (t : ℝ) (ω : Ω) => ‖(heatSymbol a t ω - 1) / (t : ℂ) + (a ω : ℂ)‖ ^ 2)
    (f := fun _ : Ω => (0 : ℝ))
    (bound := fun ω => a ω ^ 2)
    (hF_meas := Filter.Eventually.of_forall (fun t =>
      (((((heatSymbol_measurable ha t).sub measurable_const).div_const _).add
        (Complex.measurable_ofReal.comp ha)).norm.pow_const 2).aestronglyMeasurable))
    (h_bound := ?_) (bound_integrable := hintsq) (h_lim := ?_)
  · simpa using h
  · -- domination on `t > 0`: `‖·‖² ≤ a²`
    refine Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ?_)
    have htpos : (0 : ℝ) < t := ht
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hle := heatSymbol_diffQuotient_norm_le ha0 htpos ω
    nlinarith [hle, norm_nonneg ((heatSymbol a t ω - 1) / (t : ℂ) + (a ω : ℂ)), ha0 ω]
  · -- pointwise `→ 0` from the slope tendsto
    refine Filter.Eventually.of_forall (fun ω => ?_)
    have hsub : Set.Ioi (0 : ℝ) ⊆ {(0 : ℝ)}ᶜ := fun s hs => ne_of_gt hs
    have hs := (heatSymbol_slope_tendsto (a ω)).mono_left (nhdsWithin_mono 0 hsub)
    have hs' : Filter.Tendsto (fun t : ℝ => (heatSymbol a t ω - 1) / (t : ℂ))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (-(a ω : ℂ))) :=
      hs.congr (fun t => by rw [heatSymbol_eq_exp_neg_mul])
    have hs0 : Filter.Tendsto (fun t : ℝ => (heatSymbol a t ω - 1) / (t : ℂ) + (a ω : ℂ))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
      have := hs'.add (tendsto_const_nhds (x := (a ω : ℂ)))
      simpa using this
    have hpow := (hs0.norm).pow 2
    simpa using hpow

/-- **Truncation `L²`-convergence for the `h + ↑a` symbol** (the real/`+` analogue of the tower's
    `complexSymbol_fcTrunc_lintegral_tendsto`): for a bounded symbol `h` and `x ∈ fcDomain a`,
    `∫⁻ ‖h + ↑fcTrunc_m‖² dμ_x → ∫⁻ ‖h + ↑a‖² dμ_x`.  Sequential `lintegral` dominated convergence:
    pointwise from `fcTrunc_tendsto`, dominated by `2C² + 2a²` (finite by `x ∈ fcDomain a` + finite
    measure).  Stated at the `lintegral` level to dodge the `Bochner`-over-`scalarMeasure` `whnf` wall. -/
theorem boundedFC_add_fcTrunc_lintegral_tendsto {a : Ω → ℝ} (ha : Measurable a) {x : H}
    (hx : x ∈ P.fcDomain a) {h : Ω → ℂ} (hh : Measurable h) {C : ℝ} (hC : ∀ ω, ‖h ω‖ ≤ C) :
    Filter.Tendsto
      (fun m => ∫⁻ ω, ENNReal.ofReal (‖h ω + (fcTrunc a m ω : ℂ)‖ ^ 2) ∂(P.scalarMeasure x))
      Filter.atTop
      (nhds (∫⁻ ω, ENNReal.ofReal (‖h ω + (a ω : ℂ)‖ ^ 2) ∂(P.scalarMeasure x))) := by
  have hmeas : ∀ m, Measurable (fun ω => ENNReal.ofReal (‖h ω + (fcTrunc a m ω : ℂ)‖ ^ 2)) := fun m =>
    ENNReal.measurable_ofReal.comp ((Measurable.norm (hh.add
      (Complex.measurable_ofReal.comp (fcTrunc_measurable ha m)))).pow_const 2)
  have hptbound : ∀ m ω, ‖h ω + (fcTrunc a m ω : ℂ)‖ ^ 2 ≤ 2 * C ^ 2 + 2 * (a ω) ^ 2 := by
    intro m ω
    have hfc : ‖((fcTrunc a m ω : ℝ) : ℂ)‖ = |fcTrunc a m ω| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖h ω + (fcTrunc a m ω : ℂ)‖ ≤ C + |a ω| := by
      calc ‖h ω + (fcTrunc a m ω : ℂ)‖
          ≤ ‖h ω‖ + ‖((fcTrunc a m ω : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ C + |a ω| := by rw [hfc]; exact add_le_add (hC ω) (fcTrunc_abs_le_abs a m ω)
    nlinarith [h1, norm_nonneg (h ω + (fcTrunc a m ω : ℂ)), abs_nonneg (a ω), sq_abs (a ω),
      sq_nonneg (C - |a ω|)]
  have hbound : ∀ m, (fun ω => ENNReal.ofReal (‖h ω + (fcTrunc a m ω : ℂ)‖ ^ 2))
      ≤ᵐ[P.scalarMeasure x]
      (fun ω => ENNReal.ofReal (2 * C ^ 2) + ENNReal.ofReal (2 * (a ω) ^ 2)) := fun m =>
    Filter.Eventually.of_forall fun ω =>
      (ENNReal.ofReal_le_ofReal (hptbound m ω)).trans ENNReal.ofReal_add_le
  have hfin : ∫⁻ ω, (ENNReal.ofReal (2 * C ^ 2) + ENNReal.ofReal (2 * (a ω) ^ 2))
      ∂(P.scalarMeasure x) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_add_left measurable_const]
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · rw [MeasureTheory.lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by rw [P.scalarMeasure_univ]; exact ENNReal.ofReal_ne_top)
    · have heq : ∫⁻ ω, ENNReal.ofReal (2 * (a ω) ^ 2) ∂(P.scalarMeasure x) = 2 * P.fcEnergy a x := by
        calc ∫⁻ ω, ENNReal.ofReal (2 * (a ω) ^ 2) ∂(P.scalarMeasure x)
            = ∫⁻ ω, 2 * ENNReal.ofReal ((a ω) ^ 2) ∂(P.scalarMeasure x) := by
              refine MeasureTheory.lintegral_congr fun ω => ?_
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
          _ = 2 * ∫⁻ ω, ENNReal.ofReal ((a ω) ^ 2) ∂(P.scalarMeasure x) :=
              MeasureTheory.lintegral_const_mul 2 (ENNReal.measurable_ofReal.comp (ha.pow_const 2))
          _ = 2 * P.fcEnergy a x := by rw [fcEnergy]
      rw [heq]; exact ENNReal.mul_ne_top (by norm_num) ((P.mem_fcDomain).mp hx)
  have hlim : ∀ᵐ ω ∂(P.scalarMeasure x), Filter.Tendsto
      (fun m => ENNReal.ofReal (‖h ω + (fcTrunc a m ω : ℂ)‖ ^ 2)) Filter.atTop
      (nhds (ENNReal.ofReal (‖h ω + (a ω : ℂ)‖ ^ 2))) := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have h0 : Filter.Tendsto (fun m => ((fcTrunc a m ω : ℝ) : ℂ)) Filter.atTop (nhds (a ω : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (a ω)).comp (fcTrunc_tendsto a ω)
    exact ENNReal.tendsto_ofReal (((tendsto_const_nhds.add h0).norm).pow 2)
  exact MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (fun ω => ENNReal.ofReal (2 * C ^ 2) + ENNReal.ofReal (2 * (a ω) ^ 2)) hmeas hbound hfin hlim

/-- **The heat distance identity** (the real analogue of the tower's `dist_boundedFC_smul_fcOp_sq`,
    with scalar `−1` in place of `i`):  for a bounded symbol `h` and `x ∈ fcDomain a`,
    `‖boundedFC(h) x + (∫a dE) x‖² = (∫⁻ ‖h + ↑a‖² dμ_x).toReal`.
    Collapses the generator's double limit to a single limit: the distance of `boundedFC(h)x` to
    `−A x = −(∫a dE)x` equals the `L²` distance of the symbol `h` to `−a`.  Limit-uniqueness of
    `boundedFC(h)x + fcSeq_m x → boundedFC(h)x + fcOp x` (Claim A), the per-`m` identity
    `‖boundedFC(h)x + fcSeq_m x‖² = (∫⁻‖h + ↑fcTrunc_m‖²).toReal` (Claim B, `boundedFC_add` +
    `norm_boundedFC_sq`), and the truncation `L²`-convergence (`boundedFC_add_fcTrunc_lintegral_tendsto`). -/
theorem dist_boundedFC_add_fcOp_sq {a : Ω → ℝ} (ha : Measurable a) {x : H} (hx : x ∈ P.fcDomain a)
    {h : Ω → ℂ} (hh : Measurable h) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω, ‖h ω‖ ≤ C) :
    ‖P.boundedFC hh hC0 hC x + P.fcOp ha x‖ ^ 2
      = (∫⁻ ω, ENNReal.ofReal (‖h ω + (a ω : ℂ)‖ ^ 2) ∂(P.scalarMeasure x)).toReal := by
  have hA : Filter.Tendsto (fun m => P.boundedFC hh hC0 hC x + P.fcSeq ha m x) Filter.atTop
      (nhds (P.boundedFC hh hC0 hC x + P.fcOp ha x)) :=
    tendsto_const_nhds.add (P.fcSeq_tendsto_fcOp ha hx)
  have hLHS : Filter.Tendsto (fun m => ‖P.boundedFC hh hC0 hC x + P.fcSeq ha m x‖ ^ 2) Filter.atTop
      (nhds (‖P.boundedFC hh hC0 hC x + P.fcOp ha x‖ ^ 2)) := (hA.norm).pow 2
  have hbnd : ∀ m ω, ‖((fcTrunc a m ω : ℝ) : ℂ)‖ ≤ (m : ℝ) := fun m ω => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact fcTrunc_abs_le a m ω
  have hB : ∀ m, ‖P.boundedFC hh hC0 hC x + P.fcSeq ha m x‖ ^ 2
      = (∫⁻ ω, ENNReal.ofReal (‖h ω + (fcTrunc a m ω : ℂ)‖ ^ 2) ∂(P.scalarMeasure x)).toReal := by
    intro m
    rw [fcSeq, ← ContinuousLinearMap.add_apply,
      ← P.boundedFC_add hh (Complex.continuous_ofReal.measurable.comp (fcTrunc_measurable ha m))
        hC0 m.cast_nonneg hC (hbnd m), P.norm_boundedFC_sq,
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        ((Measurable.norm (hh.add (Complex.measurable_ofReal.comp
          (fcTrunc_measurable ha m)))).pow_const 2).aestronglyMeasurable]
    simp only [Function.comp_apply]
  have hfin_lim : ∫⁻ ω, ENNReal.ofReal (‖h ω + (a ω : ℂ)‖ ^ 2) ∂(P.scalarMeasure x) ≠ ⊤ := by
    have hsum_fin : ∫⁻ ω, (ENNReal.ofReal (2 * C ^ 2) + ENNReal.ofReal (2 * (a ω) ^ 2))
        ∂(P.scalarMeasure x) ≠ ⊤ := by
      rw [MeasureTheory.lintegral_add_left measurable_const]
      refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
      · rw [MeasureTheory.lintegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (by rw [P.scalarMeasure_univ]; exact ENNReal.ofReal_ne_top)
      · have heq : ∫⁻ ω, ENNReal.ofReal (2 * (a ω) ^ 2) ∂(P.scalarMeasure x) = 2 * P.fcEnergy a x := by
          calc ∫⁻ ω, ENNReal.ofReal (2 * (a ω) ^ 2) ∂(P.scalarMeasure x)
              = ∫⁻ ω, 2 * ENNReal.ofReal ((a ω) ^ 2) ∂(P.scalarMeasure x) := by
                refine MeasureTheory.lintegral_congr fun ω => ?_
                rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
            _ = 2 * ∫⁻ ω, ENNReal.ofReal ((a ω) ^ 2) ∂(P.scalarMeasure x) :=
                MeasureTheory.lintegral_const_mul 2 (ENNReal.measurable_ofReal.comp (ha.pow_const 2))
            _ = 2 * P.fcEnergy a x := by rw [fcEnergy]
        rw [heq]; exact ENNReal.mul_ne_top (by norm_num) ((P.mem_fcDomain).mp hx)
    refine ne_top_of_le_ne_top hsum_fin (MeasureTheory.lintegral_mono fun ω => ?_)
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    have h1 : ‖h ω + (a ω : ℂ)‖ ≤ C + |a ω| := by
      have hIa : ‖((a ω : ℝ) : ℂ)‖ = |a ω| := by rw [Complex.norm_real, Real.norm_eq_abs]
      calc ‖h ω + (a ω : ℂ)‖ ≤ ‖h ω‖ + ‖((a ω : ℝ) : ℂ)‖ := norm_add_le _ _
        _ ≤ C + |a ω| := by rw [hIa]; exact add_le_add (hC ω) le_rfl
    nlinarith [h1, norm_nonneg (h ω + (a ω : ℂ)), abs_nonneg (a ω), sq_abs (a ω),
      sq_nonneg (C - |a ω|)]
  have hRHS : Filter.Tendsto
      (fun m => (∫⁻ ω, ENNReal.ofReal (‖h ω + (fcTrunc a m ω : ℂ)‖ ^ 2)
        ∂(P.scalarMeasure x)).toReal) Filter.atTop
      (nhds ((∫⁻ ω, ENNReal.ofReal (‖h ω + (a ω : ℂ)‖ ^ 2) ∂(P.scalarMeasure x)).toReal)) :=
    (ENNReal.continuousAt_toReal hfin_lim).tendsto.comp
      (P.boundedFC_add_fcTrunc_lintegral_tendsto ha hx hh hC)
  simp only [hB] at hLHS
  exact tendsto_nhds_unique hLHS hRHS

/-- **★★★ The abstract heat-semigroup generator (B1)** — `d/dt e^{−tA} x |_{0⁺} = −A x`, packaged as an
    honest one-sided (semigroup-direction, `t ≥ 0`) derivative.  With `A = ∫a dE = fcOp a` the positive
    self-adjoint operator, the strongly-continuous semigroup `t ↦ e^{−tA} x = heatSemigroup ... x` is
    differentiable within `[0,∞)` at the origin with right derivative `−A x` on the domain `fcDomain a`.
    This is the REAL analogue of the tower's Stone generator `hasDerivAt_boundedFC_expSymbol`
    (`d/dt e^{itK} x|₀ = i·K x`): `e^{−ta}` replaces `e^{itf}`, `−a` replaces `i·f`, `−fcOp a` replaces
    `i·fcOp f`, and the two-sided derivative becomes the one-sided `HasDerivWithinAt (Set.Ici 0)`
    (the heat symbol is bounded by `1` only for `t ≥ 0`).

    The function is written `fun t => if 0 ≤ t then heatSemigroup ... x else x` so it is a total `ℝ → H`
    that equals the genuine semigroup on `[0,∞)`; the `else`-branch is irrelevant to the
    within-`Ici 0` derivative.  Assembled from the `L²` analytic heart
    (`heatSymbol_diffQuotient_L2_tendsto`) + the distance identity (`dist_boundedFC_add_fcOp_sq`):
    `‖slope − (−A x)‖² = ∫‖(e^{−ta}−1)/t + a‖² → 0`, so the slope `→ −A x`. -/
theorem hasDerivWithinAt_heatSemigroup {a : Ω → ℝ} (ha : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω)
    {x : H} (hx : x ∈ P.fcDomain a) :
    HasDerivWithinAt (fun t : ℝ => if h : 0 ≤ t then P.heatSemigroup ha ha0 h x else x)
      (- P.fcOp ha x) (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext t
    simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h.1 (Ne.symm h.2), fun h => ⟨h.le, ne_of_gt h⟩⟩
  rw [hset]
  set F : ℝ → H := fun t => if h : 0 ≤ t then P.heatSemigroup ha ha0 h x else x with hFdef
  have hF0 : F 0 = x := by
    simp only [hFdef]
    rw [dif_pos (le_refl (0 : ℝ)), P.heatSemigroup_zero ha ha0, ContinuousLinearMap.one_apply]
  -- `‖slope − (−A x)‖² → 0`
  have hkey : Filter.Tendsto (fun t : ℝ => ‖slope F 0 t - (- P.fcOp ha x)‖ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hev : (fun t : ℝ => ‖slope F 0 t - (- P.fcOp ha x)‖ ^ 2)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun t : ℝ => ∫ ω, ‖(heatSymbol a t ω - 1) / (t : ℂ) + (a ω : ℂ)‖ ^ 2
          ∂(P.scalarMeasure x)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : (0 : ℝ) < t := ht
      have hFt : F t = P.boundedFC (heatSymbol_measurable ha t) zero_le_one
          (heatSymbol_norm_le ha0 htpos.le) x := by
        simp only [hFdef]; exact dif_pos htpos.le
      have hslope : slope F 0 t = (t : ℂ)⁻¹ • (P.boundedFC (heatSymbol_measurable ha t) zero_le_one
          (heatSymbol_norm_le ha0 htpos.le) x - x) := by
        simp only [slope, vsub_eq_sub, sub_zero]
        rw [hF0, hFt, ← Complex.coe_smul, Complex.ofReal_inv]
      have hsubx : P.boundedFC (heatSymbol_measurable ha t) zero_le_one
            (heatSymbol_norm_le ha0 htpos.le) x - x
          = P.boundedFC ((heatSymbol_measurable ha t).sub (measurable_const (a := (1 : ℂ))))
              (add_nonneg zero_le_one zero_le_one)
              (fun ω => (norm_sub_le _ _).trans
                (add_le_add (heatSymbol_norm_le ha0 htpos.le ω) norm_one.le)) x := by
        have h := P.boundedFC_sub (heatSymbol_measurable ha t) zero_le_one
          (heatSymbol_norm_le ha0 htpos.le) (measurable_const (a := (1 : ℂ))) zero_le_one
          (fun _ => norm_one.le)
        have hc1 : P.boundedFC (measurable_const (a := (1 : ℂ))) zero_le_one (fun _ => norm_one.le)
            = (1 : H →L[ℂ] H) := by
          have h2 := P.boundedFC_const (1 : ℂ); rw [one_smul] at h2; exact h2
        rw [hc1] at h
        have happ := congrArg (fun T : H →L[ℂ] H => T x) h
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at happ
        exact happ.symm
      rw [hslope, hsubx, ← ContinuousLinearMap.smul_apply,
        ← P.boundedFC_smul ((t : ℂ)⁻¹)
          ((heatSymbol_measurable ha t).sub (measurable_const (a := (1 : ℂ))))
          (add_nonneg zero_le_one zero_le_one)
          (fun ω => (norm_sub_le _ _).trans
            (add_le_add (heatSymbol_norm_le ha0 htpos.le ω) norm_one.le)),
        sub_neg_eq_add, P.dist_boundedFC_add_fcOp_sq ha hx,
        MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun ω => sq_nonneg _)
          (show MeasureTheory.AEStronglyMeasurable
              (fun ω => ‖(heatSymbol a t ω - 1) / (t : ℂ) + (a ω : ℂ)‖ ^ 2) (P.scalarMeasure x) from
            (((((heatSymbol_measurable ha t).sub measurable_const).div_const (t : ℂ)).add
              (Complex.measurable_ofReal.comp ha)).norm.pow_const 2).aestronglyMeasurable)]
      congr 1
      refine MeasureTheory.lintegral_congr fun ω => ?_
      have hβ : (t : ℂ)⁻¹ * (heatSymbol a t ω - 1) + (a ω : ℂ)
          = (heatSymbol a t ω - 1) / (t : ℂ) + (a ω : ℂ) := by rw [div_eq_mul_inv, mul_comm]
      simp only [hβ]
    rw [Filter.tendsto_congr' hev]
    exact P.heatSymbol_diffQuotient_L2_tendsto ha ha0 hx
  -- `‖·‖² → 0 ⟹ ‖·‖ → 0 ⟹ · → 0 ⟹ slope → −A x`
  have hnorm : Filter.Tendsto (fun t : ℝ => ‖slope F 0 t - (- P.fcOp ha x)‖)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hkey
    simp only [Real.sqrt_zero] at h
    refine h.congr fun t => ?_
    rw [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
  have hv := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have := hv.add (tendsto_const_nhds (x := - P.fcOp ha x))
  simpa using this

end ProjectionValuedMeasure

end Spectral
end QIQTH
