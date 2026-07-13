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
  bound; `heatSemigroup_norm_le_one` is the sharp replacement.  What remains genuinely
  UNBUILT is the **generator** `−A = d/dt e^{−tA}|_{t=0}` as a densely-defined operator
  (the harder piece: differentiability of the spectral integral, not just continuity).

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

end ProjectionValuedMeasure

end Spectral
end QIQTH
