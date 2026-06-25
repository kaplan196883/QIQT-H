/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The Wall, Phase 1.1 — measurability of the matter-representation fiber

Toward the matter representation `π(a)` of the crossed product `M ⋊_σ ℝ` on `L²(ℝ; H)` (see
`P4_WALL_CAMPAIGN_PLAN.md`), with `π(a)ξ(s) = σ_{-s}(a)(ξ s) = Δ^{-is} a Δ^{is}(ξ s)`.  First sub-step: the
**measurability of the fiber map** `s ↦ σ_{-s}(a)(ξ s)`.

The operator family `s ↦ Δ^{is} = modUnitary S s` is only *strongly* continuous (not norm-measurable), so we use
Mathlib's `stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable` — stated for an **opaque** CLM family
(so `modUnitary`'s heavy `borelFC` definition is never unfolded during unification).  `H` (the one-particle
space) is assumed separable (`[SecondCountableTopology H]`), which is physical.  Bounded operators only.
Axiom-free.
-/
import QIQTH.CrossedProduct
import Mathlib.MeasureTheory.Function.LpSpace.Basic

set_option maxHeartbeats 1000000

namespace QIQTH.StandardSubspaceModular

open MeasureTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- **Generic:** the uncurry of a strongly-continuous family of bounded operators is strongly measurable.
    Stated for an opaque family `U` so `modUnitary`'s `borelFC` definition is never unfolded. -/
theorem stronglyMeasurable_uncurry_clmFamily (U : ℝ → H →L[ℂ] H)
    (hU : ∀ x, Continuous (fun i => U i x)) :
    StronglyMeasurable (Function.uncurry (fun i x => U i x)) :=
  stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hU
    (fun i => (U i).continuous.stronglyMeasurable)

/-- **Applying the modular flow along a measurable time reparametrization preserves measurability.**  For an
    `AEStronglyMeasurable` field `g : ℝ → H` and a measurable time `τ : ℝ → ℝ`, `s ↦ Δ^{i τ(s)}(g s)` is
    `AEStronglyMeasurable`.  (Used with `τ = id` and `τ = (-·)` to build `σ_{-s}`.) -/
theorem aesm_modUnitary_comp (S : StandardSubspace H) {τ : ℝ → ℝ}
    (hτ : AEMeasurable τ (volume : Measure ℝ)) {g : ℝ → H}
    (hg : AEStronglyMeasurable g (volume : Measure ℝ)) :
    AEStronglyMeasurable (fun s => modUnitary S (τ s) (g s)) (volume : Measure ℝ) := by
  have key : AEStronglyMeasurable
      (Function.uncurry (fun i x => modUnitary S i x) ∘ fun s => (τ s, g s)) (volume : Measure ℝ) :=
    (stronglyMeasurable_uncurry_clmFamily (modUnitary S)
      (fun x => modUnitary_stronglyContinuous S x)).aestronglyMeasurable.comp_aemeasurable
      (hτ.prodMk hg.aemeasurable)
  exact key

/-- **★ Phase 1.1 — the matter-representation fiber is measurable.**  For a bounded operator `a` and an
    `AEStronglyMeasurable` field `ξ : ℝ → H`, the fiber `s ↦ σ_{-s}(a)(ξ s) = Δ^{-is} a Δ^{is}(ξ s)` is
    `AEStronglyMeasurable` — the first sub-step of `π(a)` as an operator on `L²(ℝ; H)`. -/
theorem aesm_matterFiber (S : StandardSubspace H) (a : H →L[ℂ] H) {ξ : ℝ → H}
    (hξ : AEStronglyMeasurable ξ (volume : Measure ℝ)) :
    AEStronglyMeasurable (fun s => modularAut S (-s) a (ξ s)) (volume : Measure ℝ) := by
  -- σ_{-s}(a)(ξ s) = Δ^{-is} (a (Δ^{is} (ξ s)))
  have h1 : AEStronglyMeasurable (fun s => modUnitary S s (ξ s)) (volume : Measure ℝ) :=
    aesm_modUnitary_comp S aemeasurable_id hξ
  have h2 : AEStronglyMeasurable (fun s => a (modUnitary S s (ξ s))) (volume : Measure ℝ) :=
    a.continuous.comp_aestronglyMeasurable h1
  have h3 : AEStronglyMeasurable
      (fun s => modUnitary S (-s) (a (modUnitary S s (ξ s)))) (volume : Measure ℝ) :=
    aesm_modUnitary_comp S aemeasurable_id.neg h2
  refine h3.congr (Filter.Eventually.of_forall (fun s => ?_))
  simp only [modularAut, neg_neg, ContinuousLinearMap.mul_apply]

/-- **The conjugation is norm-contractive:** `‖σ_t(a) v‖ ≤ ‖a‖·‖v‖` (the modular unitaries are isometries, so
    `‖σ_t(a)‖ ≤ ‖a‖`).  The pointwise bound powering the `L²` estimate for `π(a)`. -/
theorem norm_modularAut_apply_le (S : StandardSubspace H) (t : ℝ) (a : H →L[ℂ] H) (v : H) :
    ‖modularAut S t a v‖ ≤ ‖a‖ * ‖v‖ := by
  rw [modularAut]
  simp only [ContinuousLinearMap.mul_apply]
  rw [modUnitary_norm]
  calc ‖a (modUnitary S (-t) v)‖
      ≤ ‖a‖ * ‖modUnitary S (-t) v‖ := a.le_opNorm _
    _ = ‖a‖ * ‖v‖ := by rw [modUnitary_norm]

/-- **★ Phase 1.2 (Lᵖ membership) — `π(a)ξ ∈ L²(ℝ;H)`.**  For `ξ ∈ L²(ℝ;H)`, the fiber `s ↦ σ_{-s}(a)(ξ s)` is
    in `L²` (measurable by Phase 1.1, dominated by `‖a‖·‖ξ s‖` via the contraction bound). -/
theorem memLp_matterFiber (S : StandardSubspace H) (a : H →L[ℂ] H)
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    MemLp (fun s => modularAut S (-s) a (ξ s)) 2 (volume : Measure ℝ) :=
  MemLp.of_le_mul (Lp.memLp ξ) (aesm_matterFiber S a (Lp.aestronglyMeasurable ξ))
    (Filter.Eventually.of_forall (fun s => norm_modularAut_apply_le S (-s) a (ξ s)))

/-- `π(a)ξ` as an `L²(ℝ;H)` element. -/
noncomputable def matterRepFun (S : StandardSubspace H) (a : H →L[ℂ] H)
    (ξ : Lp H 2 (volume : Measure ℝ)) : Lp H 2 (volume : Measure ℝ) :=
  (memLp_matterFiber S a ξ).toLp

/-- Its fiber: `π(a)ξ (s) = σ_{-s}(a)(ξ s)` a.e. -/
theorem matterRepFun_coeFn (S : StandardSubspace H) (a : H →L[ℂ] H)
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    matterRepFun S a ξ =ᵐ[volume] fun s => modularAut S (-s) a (ξ s) :=
  MemLp.coeFn_toLp _

theorem matterRepFun_add (S : StandardSubspace H) (a : H →L[ℂ] H)
    (ξ η : Lp H 2 (volume : Measure ℝ)) :
    matterRepFun S a (ξ + η) = matterRepFun S a ξ + matterRepFun S a η := by
  rw [Lp.ext_iff]
  filter_upwards [matterRepFun_coeFn S a (ξ + η),
    Lp.coeFn_add (matterRepFun S a ξ) (matterRepFun S a η),
    matterRepFun_coeFn S a ξ, matterRepFun_coeFn S a η, Lp.coeFn_add ξ η] with s e1 e2 e3 e4 e5
  simp only [e1, e2, Pi.add_apply, e3, e4, e5, map_add]

theorem matterRepFun_smul (S : StandardSubspace H) (a : H →L[ℂ] H) (c : ℂ)
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    matterRepFun S a (c • ξ) = c • matterRepFun S a ξ := by
  rw [Lp.ext_iff]
  filter_upwards [matterRepFun_coeFn S a (c • ξ),
    Lp.coeFn_smul c (matterRepFun S a ξ), matterRepFun_coeFn S a ξ, Lp.coeFn_smul c ξ]
    with s e1 e2 e3 e4
  simp only [e1, e2, Pi.smul_apply, e3, e4, map_smul]

theorem matterRepFun_norm_le (S : StandardSubspace H) (a : H →L[ℂ] H)
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    ‖matterRepFun S a ξ‖ ≤ ‖a‖ * ‖ξ‖ := by
  have hg : ‖matterRepFun S a ξ‖ ≤ ‖(‖a‖ : ℝ) • ξ‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [matterRepFun_coeFn S a ξ, Lp.coeFn_smul (‖a‖ : ℝ) ξ] with s e1 e2
    rw [e1, e2, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)]
    exact norm_modularAut_apply_le S (-s) a (ξ s)
  rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg a)] at hg

/-- **★ Phase 1.2 — the matter representation `π(a)` as a bounded operator on `L²(ℝ;H)`.**
    `π(a)ξ = [s ↦ σ_{-s}(a)(ξ s)]`, ℂ-linear with `‖π(a)‖ ≤ ‖a‖` — the matter side of the crossed product. -/
noncomputable def matterRep (S : StandardSubspace H) (a : H →L[ℂ] H) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  LinearMap.mkContinuous
    { toFun := matterRepFun S a
      map_add' := matterRepFun_add S a
      map_smul' := matterRepFun_smul S a }
    ‖a‖ (matterRepFun_norm_le S a)

@[simp] theorem matterRep_apply (S : StandardSubspace H) (a : H →L[ℂ] H)
    (ξ : Lp H 2 (volume : Measure ℝ)) : matterRep S a ξ = matterRepFun S a ξ := rfl

theorem matterRepFun_one (S : StandardSubspace H) (ξ : Lp H 2 (volume : Measure ℝ)) :
    matterRepFun S (1 : H →L[ℂ] H) ξ = ξ := by
  rw [Lp.ext_iff]
  filter_upwards [matterRepFun_coeFn S 1 ξ] with s e1
  rw [e1, modularAut_one]; rfl

theorem matterRepFun_mul (S : StandardSubspace H) (a b : H →L[ℂ] H)
    (ξ : Lp H 2 (volume : Measure ℝ)) :
    matterRepFun S (a * b) ξ = matterRepFun S a (matterRepFun S b ξ) := by
  rw [Lp.ext_iff]
  filter_upwards [matterRepFun_coeFn S (a * b) ξ,
    matterRepFun_coeFn S a (matterRepFun S b ξ), matterRepFun_coeFn S b ξ] with s e1 e2 e3
  rw [e1, e2, e3, modularAut_mul]; rfl

/-- **★ Phase 1.3 (unital) — `π(1) = 1`.** -/
theorem matterRep_one (S : StandardSubspace H) : matterRep S (1 : H →L[ℂ] H) = 1 :=
  ContinuousLinearMap.ext (fun ξ => matterRepFun_one S ξ)

/-- **★ Phase 1.3 (multiplicative) — `π(a·b) = π(a)∘π(b)`.**  With `matterRep_one`, the unital algebra
    homomorphism `M → B(L²(ℝ;H))` underlying the crossed product (`σ_{-s}` is multiplicative). -/
theorem matterRep_mul (S : StandardSubspace H) (a b : H →L[ℂ] H) :
    matterRep S (a * b) = matterRep S a ∘L matterRep S b :=
  ContinuousLinearMap.ext (fun ξ => matterRepFun_mul S a b ξ)

end QIQTH.StandardSubspaceModular
