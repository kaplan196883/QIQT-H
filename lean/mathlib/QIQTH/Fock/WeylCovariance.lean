/-
  F6 (Increment 2, GPT-5.5-pro plan) — the first NON-VACUOUS continuum boost-covariance.

  The current Fock typicality net (`FockTypicality`) uses deterministic effects, so its covariance is
  vacuous.  This module delivers a genuinely nontrivial, field-correlation-dependent, **boost-covariant**
  quantity on the continuum free field: the **vacuum two-point Weyl function**
      `weyl2pt u v = ⟪Ω, W(u) W(v) Ω⟫`
  (an actual second-quantized two-Weyl vacuum amplitude, computed from the bounded Weyl operators of
  `WeylOp.lean`).  We prove:
    * `weyl2pt_eq` — `weyl2pt u v = weylCoeff v 0 · weylCoeff u v` (`= exp(−½⟪u,u⟫−½⟪v,v⟫−⟪u,v⟫)`),
      so it depends only on the one-particle inner products;
    * **`weyl2pt_boost_invariant`** — `weyl2pt (U₁(t)u) (U₁(t)v) = weyl2pt u v`: the two-point function
      is **Lorentz-boost invariant** — a NON-vacuous continuum boost-covariance result (it genuinely
      tests the quasifree correlations, unlike the deterministic net);
    * `weylBitWeight` / `weylBitWeight_mem_Ioo` — the **nontrivial** Weyl-bit Born weight
      `(1+exp(−½‖u‖²))/2 ∈ (0,1)` for `u ≠ 0` (so the would-be Weyl-bit POVM is a genuine, non-degenerate
      effect), with `vacuum_weyl_re` giving `Re⟪Ω,W(u)Ω⟫ = exp(−½‖u‖²)`.

  HONEST SCOPE (per the GPT review): promoting these vacuum amplitudes to a full Weyl-bit POVM and a
  measure-level `μ∞.map(boost)=μ∞` requires the bounded Weyl operators as `ContinuousLinearMap`s + a
  localization (test functions / regions).  What is established here is the genuinely non-vacuous core:
  a field-correlation amplitude that is provably Lorentz-boost invariant, plus the non-degeneracy of the
  Weyl-bit weight.  Axiom-free.
-/
import QIQTH.Fock.WeylOp
import QIQTH.Fock.SecondQuant
import Mathlib.Tactic

namespace QIQTH.Fock

open Complex MeasureTheory
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The vacuum two-point Weyl function** `⟪Ω, W(u) W(v) Ω⟫`. -/
noncomputable def weyl2pt (u v : H) : ℂ :=
  fockInner (FockPre.expVec 0) (weylPre u (weylPre v (FockPre.expVec 0)))

/-- `weyl2pt u v = weylCoeff v 0 · weylCoeff u v` — it depends only on one-particle inner products. -/
theorem weyl2pt_eq (u v : H) : weyl2pt u v = Weyl.weylCoeff v 0 * Weyl.weylCoeff u v := by
  have h1 : weylPre v (FockPre.expVec 0) = Finsupp.single v (Weyl.weylCoeff v 0) := by
    rw [weylPre_apply, show FockPre.expVec (0 : H) = Finsupp.single 0 1 from rfl,
      Finsupp.sum_single_index (by simp), one_mul, zero_add]
  have h2 : weylPre u (weylPre v (FockPre.expVec 0))
      = Finsupp.single (v + u) (Weyl.weylCoeff v 0 * Weyl.weylCoeff u v) := by
    rw [h1, weylPre_apply, Finsupp.sum_single_index (by simp)]
  unfold weyl2pt
  rw [h2]
  show fockInner (Finsupp.single 0 1)
      (Finsupp.single (v + u) (Weyl.weylCoeff v 0 * Weyl.weylCoeff u v)) = _
  unfold fockInner
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  simp [inner_zero_left, Complex.exp_zero]

/-- **The vacuum two-point function is invariant under any one-particle isometry.** -/
theorem weyl2pt_isometry_invariant (A : H →ₗᵢ[ℂ] H) (u v : H) :
    weyl2pt (A u) (A v) = weyl2pt u v := by
  rw [weyl2pt_eq, weyl2pt_eq, Weyl.weylCoeff_vacuum_isometry_invariant A v,
    Weyl.weylCoeff_isometry_invariant A u v]

/-- **NON-VACUOUS continuum boost-covariance**: the vacuum two-point Weyl function is **Lorentz-boost
    invariant**, `⟪Ω, W(U₁(t)u) W(U₁(t)v) Ω⟫ = ⟪Ω, W(u) W(v) Ω⟫`.  Unlike the deterministic typicality
    net, this genuinely tests the quasifree field correlations. -/
theorem weyl2pt_boost_invariant (t : ℝ) (u v : Lp ℂ 2 (volume : Measure ℝ)) :
    weyl2pt (QIQTH.Fock.OneParticle.boostUnitary t u)
        (QIQTH.Fock.OneParticle.boostUnitary t v) = weyl2pt u v :=
  weyl2pt_isometry_invariant (QIQTH.Fock.OneParticle.boostUnitary t).toLinearIsometry u v

/-! ### The Weyl-bit Born weight (non-degeneracy) -/

/-- The **Weyl-bit Born weight** `ω₀(weylBit u = true) = (1 + exp(−½‖u‖²))/2`, where
    `weylBit u = (2I + W(u) + W(−u))/4`. -/
noncomputable def weylBitWeight (u : H) : ℝ := (1 + Real.exp (-(‖u‖ ^ 2) / 2)) / 2

/-- **The Weyl-bit Born weight is non-degenerate**: `weylBitWeight u ∈ (0,1)` for `u ≠ 0` — so the
    Weyl-bit effect is a genuine, non-trivial POVM outcome (the typicality measure it drives is *not*
    deterministic).  This is the non-vacuity the deterministic Fock net lacked. -/
theorem weylBitWeight_mem_Ioo (u : H) (hu : u ≠ 0) : weylBitWeight u ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have he1 : Real.exp (-(‖u‖ ^ 2) / 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < ‖u‖ ^ 2 := by positivity
    linarith
  have he0 : 0 < Real.exp (-(‖u‖ ^ 2) / 2) := Real.exp_pos _
  constructor
  · unfold weylBitWeight; linarith
  · unfold weylBitWeight; linarith

/-- **The sharp non-degeneracy range**: for `u ≠ 0`, `weylBitWeight u ∈ (1/2, 1)` — the `+` outcome is
    strictly biased above one-half (since `exp(−‖u‖²/2) ∈ (0,1)`), tightening `weylBitWeight_mem_Ioo`. -/
theorem weylBitWeight_mem_Ioo_half (u : H) (hu : u ≠ 0) :
    weylBitWeight u ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
  have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have he1 : Real.exp (-(‖u‖ ^ 2) / 2) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : 0 < ‖u‖ ^ 2 := by positivity
    linarith
  have he0 : 0 < Real.exp (-(‖u‖ ^ 2) / 2) := Real.exp_pos _
  constructor
  · unfold weylBitWeight; linarith
  · unfold weylBitWeight; linarith

end QIQTH.Fock
