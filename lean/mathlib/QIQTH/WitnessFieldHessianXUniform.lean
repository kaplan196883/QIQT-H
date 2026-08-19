/-
  WitnessFieldHessianXUniform — J4-864: the `x`-UNIFORMISATION of the field-Hessian operator-norm
  envelope, discharging the `hFd` field of `MixedDirectionsFieldHessianEnvelope` (J4-843) DOWN TO an
  `x`-uniform per-index entrywise bound, plus the reusable `x`-free Gaussian-moment ATOM that the true
  entrywise `x`-uniformisation runs on.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.
  `a₁ = R/6` remains CONDITIONAL.  It performs the `x`-uniformisation reduction of the `hFd` field and
  banks the `x`-free Gaussian-moment atom, reusing the already-banked CLM operator-norm combinator
  (`MixedFieldHessianOpNormCombinator.witnessFieldHessian_opNorm_xuniform`, J4-863) and the banked
  Gaussian-peak / polynomial-absorption tools.  No `sorry`, no new axioms, no `:= True`, no vacuous /
  unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.  NOT `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT `hFd` NEEDS AND WHERE THE `x`-DEPENDENCE ACTUALLY LIVES (item 1/2 of the brief).

  `MixedDirectionsFieldHessianEnvelope.hFd` requires, for a.e. `s`, a.e. `z`, a bound
    `∀ x : Point n,  ‖fderiv ℝ (y ↦ witnessFieldDeriv … i (t−s) y z) x‖ ≤ BF s z`
  with a SINGLE constant `BF s z` independent of `x`.  The banked entrywise envelopes
  (`SecondDerivEnvelope.witnessFieldDeriv2_gate_abs_le`, diagonal, and
  `WitnessMixedHessianMagnitudeBound.witnessMixed_gate_abs_le`, off-diagonal) are stated AT a point `p`
  with abstract, symbolically `x`-FREE constants `Bs2, Bs1, Ba, Bd, Bdd` (resp. `Bs2, Bsj, Bsi, Ba,
  Bdi, Bdj, Bdd`).  The genuine `x`-dependence that blocks a single `BF` is NOT those constants — it is
  (a) the Gaussian prefactor `gaussDdim τ (uniformInverseChart z p)` sitting in the entrywise RHS, and
  (b) the fact that the carried scalar quantities (`⟨V,P⟩²/(4τ²)`, …, `V := uniformInverseChart z x`)
  GROW polynomially in `x`, so a naive "peak the Gaussian, sup the scalars separately" is unavailable:
  the product `gaussDdim τ (W z x)·(polynomial in x)` is bounded ONLY because the Gaussian decay beats
  the polynomial growth (a Gaussian-moment fact), not because either factor is `x`-uniform alone.

  `WitnessMixedPartialUniformBound` (Task E) addresses a DIFFERENT uniformity axis — uniformity over the
  BASE point `q` (the chart base slot), via a Grönwall boundedness argument — and is NOT applicable to
  the field-point `x` uniformity `hFd` needs.

  ## THE DELIVERABLE (ns `QIQTH.WitnessFieldHessianXUniform`).

    • `heatKernel1D_sq_moment_le_xfree` — ★ the reusable `x`-FREE Gaussian-quadratic-moment ATOM:
      `x²·G_t(x) ≤ 8t·G_t(0)`  (`0 < t`).  This is the mechanism (banked
      `GaussianPolyBound.gaussian_poly_absorb` `m=1` folds `x²·e^{−x²/4t}` into `8t·e^{−x²/8t}`, then the
      widened exponent's peak `e^{−x²/8t} ≤ 1` yields the `x`-FREE `8t·G_t(0)`) that converts a
      Gaussian×polynomial into a single `x`-free constant.

    • `gaussDdim_coord_sq_moment_le_xfree` — ★ the `d`-dimensional coordinate-square moment atom:
      `(vⱼ)²·gaussDdim τ v ≤ 8τ·gaussDdim τ 0`  (`0 < τ`).  The `1`-D atom on factor `j` combined with the
      banked pointwise peak `heatKernel1D_le_diagonal` on the remaining factors — the exact shape the
      entrywise leading term `gaussDdim τ (W z x)·⟨W z x,P⟩²/(4τ²)` reduces to under Cauchy–Schwarz and a
      uniform jet bound.

    • `witnessFieldHessian_hFd_of_xuniform_entrywise` — ★★★ THE `hFd` REDUCTION: the a.e.-lifted CLM
      operator-norm combinator.  From `x`-UNIFORM per-index second-partial bounds `∀ x j, |pd (∂ᵢH) j x|
      ≤ bb s z j` (a.e. `s`, a.e. `z`) and a.e. field-slot differentiability, it delivers EXACTLY the
      `hFd` field with `BF s z := Σⱼ bb s z j`.  So `hFd` is now reduced, verbatim, to an `x`-uniform
      per-index entrywise bound — the CLM assembly and the a.e. bookkeeping are fully discharged.

    • `witnessFieldHessian_hFd_nonvacuous` — ★ NON-VACUITY WITNESS: the combinator's antecedents are
      inhabited (the empty-gate `K = ∅` model makes `witnessFieldDeriv ≡ 0`, so `bb ≡ 0` and every
      hypothesis holds), exhibiting the reduction as a genuine implication with a satisfiable premise —
      no J4-548-style unsatisfiable antecedent.

  ## HONEST RESIDUAL (item 4 of the brief).  What remains for the FULL `hFd` instance is the production
  of the `x`-uniform per-index bound `bb s z j` from the banked entrywise envelopes: this is a joint
  Gaussian×polynomial `x`-supremum (assemble the coordinate-moment atom above against a uniform jet
  bound on `P, Q` and the amplitude sup-bounds).  That estimate is of the SAME difficulty class as the
  §C z-mass integrability wall (both are Gaussian-moment estimates), NOT a cheap restatement.  The atoms
  banked here are its reusable core; the assembly and the z-mass slot remain the two open pieces.

  No conclusion-in-disguise; no unsatisfiable / vacuous hypothesis; NO `sorry`; NO new axioms.  All mains
  std-3.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.MixedFieldHessianOpNormCombinator
import QIQTH.MixedDirectionsFieldHessianEnvelope
import QIQTH.GaussianPolyBound
import QIQTH.BoundaryAssembly

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.FlatHeatEquation
open QIQTH.GaussianConvolution QIQTH.HeatKernelA1
open scoped Topology Interval BigOperators

namespace QIQTH.WitnessFieldHessianXUniform

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### A — the `x`-free Gaussian-moment atoms (the `x`-uniformisation mechanism).
    ############################################################################### -/

/-- **★ A1 — `heatKernel1D_sq_moment_le_xfree`.**  The reusable `x`-FREE Gaussian-quadratic moment atom:
    for `0 < t`,
      `x² · heatKernel1D t x ≤ 8·t · heatKernel1D t 0`.
    Route: the banked `GaussianPolyBound.gaussian_poly_absorb` at `m = 1` gives
    `x²·e^{−x²/4t} ≤ 8t·e^{−x²/8t}`, and the widened exponent's peak `e^{−x²/8t} ≤ 1` collapses the
    residual Gaussian to the `x`-FREE value `heatKernel1D t 0 = (√(4πt))⁻¹`.  This is the atom that turns
    a Gaussian×quadratic into a single `x`-free constant — the core of the field-point uniformisation.
    NOT `a₁ = R/6`. -/
theorem heatKernel1D_sq_moment_le_xfree (t : ℝ) (ht : 0 < t) (x : ℝ) :
    x ^ 2 * heatKernel1D t x ≤ 8 * t * heatKernel1D t 0 := by
  have hpre : (0 : ℝ) ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ := by positivity
  have h0 : heatKernel1D t 0 = (Real.sqrt (4 * Real.pi * t))⁻¹ := by
    rw [heatKernel1D]
    have hz : -(0 : ℝ) ^ 2 / (4 * t) = 0 := by norm_num
    rw [hz, Real.exp_zero, mul_one]
  -- absorb the quadratic and peak the widened Gaussian ⟹ `x²·e^{−x²/4t} ≤ 8t`.
  have habs : x ^ 2 * Real.exp (-x ^ 2 / (4 * t)) ≤ 8 * t := by
    have h1 := QIQTH.GaussianPolyBound.gaussian_poly_absorb 1 ht x
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at h1
    have hexp1 : Real.exp (-x ^ 2 / (8 * t)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith [sq_nonneg x]
      · positivity
    calc x ^ 2 * Real.exp (-x ^ 2 / (4 * t))
        ≤ 8 * t * Real.exp (-x ^ 2 / (8 * t)) := h1
      _ ≤ 8 * t * 1 := by
          refine mul_le_mul_of_nonneg_left hexp1 ?_; positivity
      _ = 8 * t := by ring
  rw [heatKernel1D, h0]
  calc x ^ 2 * ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-x ^ 2 / (4 * t)))
      = (Real.sqrt (4 * Real.pi * t))⁻¹ * (x ^ 2 * Real.exp (-x ^ 2 / (4 * t))) := by ring
    _ ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ * (8 * t) := mul_le_mul_of_nonneg_left habs hpre
    _ = 8 * t * (Real.sqrt (4 * Real.pi * t))⁻¹ := by ring

/-- **★ A2 — `gaussDdim_coord_sq_moment_le_xfree`.**  The `d`-dimensional coordinate-square Gaussian
    moment atom: for `0 < τ` and any coordinate `j`,
      `(vⱼ)² · gaussDdim τ v ≤ 8·τ · gaussDdim τ 0`.
    The `1`-D atom (`heatKernel1D_sq_moment_le_xfree`) on the `j`-th tensor factor, combined with the
    banked pointwise peak (`heatKernel1D_le_diagonal`) on all remaining factors (both nonneg).  This is
    the exact `x`-free shape the entrywise leading term `gaussDdim τ (W z x)·⟨W z x, P⟩²/(4τ²)` reduces to
    once Cauchy–Schwarz and a uniform jet bound peel off `⟨W z x, P⟩²`.  NOT `a₁ = R/6`. -/
theorem gaussDdim_coord_sq_moment_le_xfree {τ : ℝ} (hτ : 0 < τ) (v : Point n) (j : Fin n) :
    (v j) ^ 2 * gaussDdim τ v ≤ 8 * τ * gaussDdim τ (0 : Point n) := by
  have hj : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
  have hprodv : gaussDdim τ v
      = heatKernel1D τ (v j) * ∏ k ∈ Finset.univ.erase j, heatKernel1D τ (v k) := by
    rw [gaussDdim]
    exact (Finset.mul_prod_erase Finset.univ (fun k => heatKernel1D τ (v k)) hj).symm
  have hprod0 : gaussDdim τ (0 : Point n)
      = heatKernel1D τ 0 * ∏ _k ∈ Finset.univ.erase j, heatKernel1D τ (0 : ℝ) := by
    simp only [gaussDdim, Pi.zero_apply]
    exact (Finset.mul_prod_erase Finset.univ (fun _ : Fin n => heatKernel1D τ (0 : ℝ)) hj).symm
  rw [hprodv, hprod0]
  have hatom : (v j) ^ 2 * heatKernel1D τ (v j) ≤ 8 * τ * heatKernel1D τ 0 :=
    heatKernel1D_sq_moment_le_xfree τ hτ (v j)
  have hrest : ∏ k ∈ Finset.univ.erase j, heatKernel1D τ (v k)
      ≤ ∏ _k ∈ Finset.univ.erase j, heatKernel1D τ (0 : ℝ) := by
    refine Finset.prod_le_prod (fun k _ => (heatKernel1D_pos τ (v k) hτ).le) (fun k _ => ?_)
    exact heatKernel1D_le_diagonal τ (v k) hτ
  have hrestnn : 0 ≤ ∏ k ∈ Finset.univ.erase j, heatKernel1D τ (v k) :=
    Finset.prod_nonneg (fun k _ => (heatKernel1D_pos τ (v k) hτ).le)
  have hatomnn : 0 ≤ 8 * τ * heatKernel1D τ 0 :=
    mul_nonneg (by positivity) (heatKernel1D_pos τ 0 hτ).le
  calc (v j) ^ 2 * (heatKernel1D τ (v j) * ∏ k ∈ Finset.univ.erase j, heatKernel1D τ (v k))
      = ((v j) ^ 2 * heatKernel1D τ (v j)) * ∏ k ∈ Finset.univ.erase j, heatKernel1D τ (v k) := by
        ring
    _ ≤ (8 * τ * heatKernel1D τ 0) * ∏ _k ∈ Finset.univ.erase j, heatKernel1D τ (0 : ℝ) :=
        mul_le_mul hatom hrest hrestnn hatomnn
    _ = 8 * τ * (heatKernel1D τ 0 * ∏ _k ∈ Finset.univ.erase j, heatKernel1D τ (0 : ℝ)) := by ring

/-! ###############################################################################
    ### B — the `hFd` reduction: the a.e.-lifted `x`-uniform CLM combinator.
    ############################################################################### -/

/-- **★★★ B — `witnessFieldHessian_hFd_of_xuniform_entrywise`.**  THE `hFd` REDUCTION.  From
      • a.e.-`s`, a.e.-`z` field-slot differentiability of `y ↦ witnessFieldDeriv … i (t−s) y z`, and
      • the `x`-UNIFORM per-index second-partial bounds `∀ x j, |pd (∂ᵢH) j x| ≤ bb s z j`
        (a.e.-`s`, a.e.-`z`, with `bb` NOT depending on `x`),
    the a.e.-lifted CLM operator-norm combinator (`MixedFieldHessianOpNormCombinator.
    witnessFieldHessian_opNorm_xuniform`, banked at J4-863) delivers EXACTLY the
    `MixedDirectionsFieldHessianEnvelope.hFd` field with `BF s z := Σⱼ bb s z j`:
      `∀ᵐ s, s ∈ uIoc 0 (t−εₘ) → ∀ᵐ z, ∀ x, ‖fderiv (y ↦ witnessFieldDeriv … i (t−s) y z) x‖ ≤ Σⱼ bb s z j`.
    So `hFd` is reduced verbatim to an `x`-uniform per-index entrywise bound; the CLM assembly and the
    two `∀ᵐ` layers are fully discharged.  NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_hFd_of_xuniform_entrywise (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (t : ℝ) (m : ℕ) (bb : ℝ → Point n → Fin n → ℝ)
    (hf : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∀ x : Point n,
          DifferentiableAt ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x)
    (hb : ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
        ∀ᵐ z ∂volume, ∀ (x : Point n) (j : Fin n),
          |pd (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) j x| ≤ bb s z j) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y => witnessFieldDeriv g gi hC hK S a b i (t - s) y z) x‖
          ≤ ∑ j, bb s z j := by
  filter_upwards [hf, hb] with s hfs hbs hs
  filter_upwards [hfs hs, hbs hs] with z hfz hbz
  exact QIQTH.MixedFieldHessianOpNormCombinator.witnessFieldHessian_opNorm_xuniform
    g gi hC hK S a b i (t - s) z (bb s z) hfz hbz

/-! ###############################################################################
    ### C — NON-VACUITY WITNESS (the combinator's antecedents are inhabited).
    ############################################################################### -/

/-- **★ C — `witnessFieldHessian_hFd_nonvacuous`.**  The antecedent set of the `hFd` reduction
    (`witnessFieldHessian_hFd_of_xuniform_entrywise`) is inhabited: at the empty-gate model `K = ∅`
    every base point is off-gate (`witnessFieldDeriv_offGate_eq_zero`), so `y ↦ witnessFieldDeriv … y z`
    is the zero function — differentiable, with all partials `0` — hence the `x`-uniform entrywise bounds
    hold with `bb ≡ 0` and the reduction yields `‖fderiv‖ ≤ Σⱼ 0`.  This exhibits the reduction as a
    genuine implication with a satisfiable premise (no J4-548-style unsatisfiable antecedent).
    NOT `a₁ = R/6`. -/
theorem witnessFieldHessian_hFd_nonvacuous (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (S : Point n → Set (Point n)) (a b : ℝ) (i : Fin n) (t : ℝ) (m : ℕ) :
    ∀ᵐ s ∂volume, s ∈ Set.uIoc 0 (t - epsSeq m) →
      ∀ᵐ z ∂volume, ∀ x : Point n,
        ‖fderiv ℝ (fun y =>
            witnessFieldDeriv g gi hC (isCompact_empty) S a b i (t - s) y z) x‖
          ≤ ∑ _j : Fin n, (0 : ℝ) := by
  refine witnessFieldHessian_hFd_of_xuniform_entrywise g gi hC isCompact_empty S a b i t m
    (fun _ _ _ => 0) ?_ ?_
  · filter_upwards with s _hs
    filter_upwards with z x
    have hzero : (fun y => witnessFieldDeriv g gi hC isCompact_empty S a b i (t - s) y z)
        = fun _ => (0 : ℝ) := by
      funext y
      exact witnessFieldDeriv_offGate_eq_zero g gi hC isCompact_empty S a b i (t - s) y z
        (Set.notMem_empty z)
    rw [hzero]
    exact differentiableAt_const 0
  · filter_upwards with s _hs
    filter_upwards with z x j
    have hzero : (fun y => witnessFieldDeriv g gi hC isCompact_empty S a b i (t - s) y z)
        = fun _ => (0 : ℝ) := by
      funext y
      exact witnessFieldDeriv_offGate_eq_zero g gi hC isCompact_empty S a b i (t - s) y z
        (Set.notMem_empty z)
    rw [hzero, pd_const, abs_zero]

end QIQTH.WitnessFieldHessianXUniform

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.WitnessFieldHessianXUniform
#print axioms heatKernel1D_sq_moment_le_xfree
#print axioms gaussDdim_coord_sq_moment_le_xfree
#print axioms witnessFieldHessian_hFd_of_xuniform_entrywise
#print axioms witnessFieldHessian_hFd_nonvacuous
end AxiomChecks
