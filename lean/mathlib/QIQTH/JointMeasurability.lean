/-
  JointMeasurability — J4-177: the LAST open G2 slot `hjoint` of
  `QIQTH.WitnessDerivMeasurability.g2_bundle_assembled` — the JOINT `(s,z)`-ae-measurability of the
  first-derivative kernel·source product `(s,z) ↦ witnessFieldDeriv … (t−s) x z · F s z` on the
  product measure `(volume.restrict (uIoc 0 t)).prod ν`, which feeds `hsmeas` via
  `AEStronglyMeasurable.integral_prod_right'`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS NOT `a₁ = R/6`, and proves NOTHING about `R/6`.  It discharges — for
  the concrete `dH := witnessFieldDeriv` — the single remaining `hjoint` slot of the seven-hypothesis
  G2 bundle, reducing it to strictly lighter, satisfiable, non-vacuous carries (a JOINT-witness
  measurability per field-shift, a JOINT a.e. field-differentiability, and the gate/measurability set
  data), never the conclusion.

  ── WHAT IS PROVED HERE (axiom-free, no `sorry`).

    LEVER (the product-measure difference-quotient lever).
      • `pd_aestronglyMeasurable_of_slice_prod` — ★ the ABSTRACT generalization of J4-163's
          `pd_aestronglyMeasurable_of_slice` to ANY measure space `μ` on ANY `Ω`: if every line-slice
          `w ↦ H w p` has a derivative `d p` at `a` for a.e. `p`, and each `H w` is
          `AEStronglyMeasurable`, then `d` is `AEStronglyMeasurable`.  (The J4-163 proof is generic in
          the base measure; this is the verbatim generalization, instantiated at the PRODUCT measure.)

    ae_ae → ae_prod CONVERTER (the honest Fubini-direction handling).
      • `ae_prod_of_ae_ae` — ★ from `∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x,y)` PLUS the genuine measurability
          side-condition `MeasurableSet {q | p q}`, concludes `∀ᵐ q ∂(μ.prod ν), p q`, via Mathlib's
          `MeasureTheory.Measure.ae_prod_iff_ae_ae`.  The reverse (`ae_prod → ae_ae`) is unconditional
          (`ae_ae_of_ae_prod`); THIS direction needs the measurable-set carry (Rudin's counterexample),
          carried honestly.

    THE GATED-WITNESS JOINT MEASURABILITY (indicator glue).
      • `witness_joint_aestronglyMeasurable` — ★ the JOINT `(s,z)`-ae-measurability of
          `(s,z) ↦ gatedKernel K S H (t−s) q₀ z · F s z` from: the INNER-kernel joint measurability
          `hinner` (`(s,z) ↦ H (t−s) q₀ z`), the gate-set measurabilities `MeasurableSet K` and
          `MeasurableSet {z | q₀ ∈ S z}`, and the source joint measurability `hF`.  Route: the gate is
          the indicator of the `s`-independent product set `univ ×ˢ (K ∩ {z | q₀ ∈ S z})`, a measurable
          set in the product σ-algebra; `AEStronglyMeasurable.indicator` then `.mul`.

    REDUCTION (`hjoint` from the witness).
      • `hjoint_from_witness` — ★ the EXACT `hjoint` shape of `g2_bundle_assembled`, reduced (via the
          product lever) to two strictly lighter carries: `hWmeasJ` — the JOINT-witness measurability
          per field-shift `w` (with the `F` factor) — and `hWdiffJ` — the JOINT a.e. field-slice
          differentiability of the witness to the derivative kernel (on the product measure).  The `F`
          factor is `w`-constant, so `HasDerivAt.mul_const` upgrades the witness derivative to the
          `dH·F` product derivative pointwise.

    CAPSTONE (`hjoint_concrete`).
      • `hjoint_concrete` — ★★ the EXACT `hjoint` slot for `dH := witnessFieldDeriv`, threading the
          witness joint measurability (per field-shift, via `witness_joint_aestronglyMeasurable`) into
          the reduction `hjoint_from_witness`, leaving the minimized carry list: the inner-kernel joint
          measurability family `hinnerJ`, the gate-set data `hKmeasSet`/`hSmeasSet`, the source joint
          measurability `hFjoint`, and the joint a.e. field-differentiability `hWdiffJ`.  NOT `a₁ = R/6`.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `hinnerJ` — joint `(s,z)`-ae-measurability of the ungated inner parametrix kernel
      `(s,z) ↦ globalCutoffParametrixWitnessN 1 … (t−s) q₀ z` (per field point `q₀`).  A genuine
      joint-measurability input (satisfiable from the joint continuity of the Gaussian parametrix in
      `(τ, z)` for `τ > 0`, `{s = t}` being a product-null slice) — NOT the fibrewise-integrated
      conclusion.
    • `hKmeasSet` / `hSmeasSet` — the base-gate measurable-set data (`K` and each field-fibre
      `{z | q₀ ∈ S z}`), the SAME gate structure the census already carries.
    • `hFjoint` — joint `(s,z)`-ae-measurability of the source `(s,z) ↦ F s z` (a property of `F`).
    • `hWdiffJ` — joint a.e. field-slice differentiability of the witness to `witnessFieldDeriv`
      (the `pd`-is-a-genuine-derivative content, on the product measure; convertible from the per-`z`
      `hWdiff` of J4-163 via `ae_prod_of_ae_ae` under the measurable-set side-condition).

  NO `sorry`.  NO new axioms.  NO `expRho`.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WitnessDerivMeasurability
import QIQTH.G2CarryDischarge

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.HeatParametrixAnsatz
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.WitnessDerivDomination
open scoped Interval Topology BigOperators

namespace QIQTH.JointMeasurability

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### LEVER — the product-measure difference-quotient measurability lever.
    ############################################################################### -/

/-- **★ `pd_aestronglyMeasurable_of_slice_prod` — THE PRODUCT-MEASURE MEASURABILITY LEVER.**  The
    ABSTRACT generalization of J4-163's `pd_aestronglyMeasurable_of_slice` to ANY measure `μ` on ANY
    `Ω`: for `H : ℝ → Ω → ℝ` whose every line-slice `w ↦ H w p` has a derivative `d p` at `a` for
    a.e. `p`, and each `H w` is `AEStronglyMeasurable`, the derivative `d` is `AEStronglyMeasurable`.
    `d p` is the `atTop` limit of the measurable difference quotients `slope (H · p) a (a+1/(k+1))`
    (each a `const_smul` of a difference of `AEStronglyMeasurable`s) via `hasDerivAt_iff_tendsto_slope`
    composed with `a + 1/(k+1) → a` inside `{≠ a}`, then `aestronglyMeasurable_of_tendsto_ae`.  Applied
    below at the PRODUCT measure `μ.prod ν`.  NOT `a₁ = R/6`. -/
theorem pd_aestronglyMeasurable_of_slice_prod {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : ℝ → Ω → ℝ) (d : Ω → ℝ) (a : ℝ)
    (hmeas : ∀ w : ℝ, AEStronglyMeasurable (fun p => H w p) μ)
    (hderiv : ∀ᵐ p ∂μ, HasDerivAt (fun w => H w p) (d p) a) :
    AEStronglyMeasurable d μ := by
  have ha : Tendsto (fun k : ℕ => a + 1 / ((k : ℝ) + 1)) atTop (𝓝 a) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add a
  have hne : ∀ᶠ (k : ℕ) in atTop, (a + 1 / ((k : ℝ) + 1)) ∈ ({a}ᶜ : Set ℝ) := by
    filter_upwards with k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h; linarith
  have hwk : Tendsto (fun k : ℕ => a + 1 / ((k : ℝ) + 1)) atTop (𝓝[≠] a) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ha hne
  have hf_meas : ∀ k : ℕ,
      AEStronglyMeasurable (fun p => slope (fun w => H w p) a (a + 1 / ((k : ℝ) + 1))) μ := by
    intro k
    have hrw : (fun p => slope (fun w => H w p) a (a + 1 / ((k : ℝ) + 1)))
        = (fun p => ((a + 1 / ((k : ℝ) + 1)) - a)⁻¹ • (H (a + 1 / ((k : ℝ) + 1)) p - H a p)) := by
      funext p; rw [slope_def_module]
    rw [hrw]
    exact ((hmeas (a + 1 / ((k : ℝ) + 1))).sub (hmeas a)).const_smul
      (((a + 1 / ((k : ℝ) + 1)) - a)⁻¹)
  have hlim : ∀ᵐ p ∂μ,
      Tendsto (fun k : ℕ => slope (fun w => H w p) a (a + 1 / ((k : ℝ) + 1))) atTop (𝓝 (d p)) := by
    filter_upwards [hderiv] with p hp
    exact (hp.tendsto_slope).comp hwk
  exact aestronglyMeasurable_of_tendsto_ae atTop hf_meas hlim

/-! ###############################################################################
    ### ae_ae → ae_prod CONVERTER (the honest Fubini-direction handling).
    ############################################################################### -/

/-- **★ `ae_prod_of_ae_ae`.**  THE ITERATED→PRODUCT a.e. converter.  From the iterated a.e. statement
    `∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x,y)` PLUS the genuine measurability side-condition `MeasurableSet {q | p q}`
    (needed — Rudin §8.9(c) is a counterexample without it), concludes `∀ᵐ q ∂(μ.prod ν), p q`.
    Thin wrapper over `MeasureTheory.Measure.ae_prod_iff_ae_ae`.  The REVERSE direction
    (`ae_prod → ae_ae`) is unconditional (`ae_ae_of_ae_prod`).  NOT `a₁ = R/6`. -/
theorem ae_prod_of_ae_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν] {p : α × β → Prop}
    (hp : MeasurableSet {q | p q})
    (h : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, p (x, y)) :
    ∀ᵐ q ∂(μ.prod ν), p q :=
  (MeasureTheory.Measure.ae_prod_iff_ae_ae hp).mpr h

/-! ###############################################################################
    ### THE GATED-WITNESS JOINT MEASURABILITY (indicator glue).
    ############################################################################### -/

/-- **★ `witness_joint_aestronglyMeasurable`.**  THE JOINT `(s,z)`-ae-measurability of the gated
    kernel·source product `(s,z) ↦ gatedKernel K S H (t−s) q₀ z · F s z` on `μ.prod ν`, from: the
    INNER-kernel joint measurability `hinner` (`(s,z) ↦ H (t−s) q₀ z`), the gate-set measurabilities
    `MeasurableSet K` and `MeasurableSet {z | q₀ ∈ S z}`, and the source joint measurability `hF`.
    The gate `gatedKernel K S H (t−s) q₀ z = if z∈K then (if q₀∈S z then H (t−s) q₀ z else 0) else 0`
    is exactly the indicator of the `s`-independent measurable product set
    `Prod.snd ⁻¹' (K ∩ {z | q₀ ∈ S z})`, so `AEStronglyMeasurable.indicator` then `.mul` closes it.
    Generic in the inner kernel `H` (the `gatedKernel` wrapper is inner-kernel-agnostic).
    NOT `a₁ = R/6`. -/
theorem witness_joint_aestronglyMeasurable {α : Type*} [MeasurableSpace α]
    {K : Set (Point n)} (S : Point n → Set (Point n))
    (H : ℝ → Point n → Point n → ℝ) (q₀ : Point n)
    (τ : α → ℝ) (F : α → Point n → ℝ) (μ : Measure α) (ν : Measure (Point n))
    (hKmeas : MeasurableSet K)
    (hSmeas : MeasurableSet {z : Point n | q₀ ∈ S z})
    (hinner : AEStronglyMeasurable (fun p : α × Point n => H (τ p.1) q₀ p.2) (μ.prod ν))
    (hF : AEStronglyMeasurable (fun p : α × Point n => F p.1 p.2) (μ.prod ν)) :
    AEStronglyMeasurable
      (fun p : α × Point n => gatedKernel K S H (τ p.1) q₀ p.2 * F p.1 p.2)
      (μ.prod ν) := by
  classical
  set G : Set (Point n) := K ∩ {z : Point n | q₀ ∈ S z} with hG
  have hGmeas : MeasurableSet G := hKmeas.inter hSmeas
  have hSetMeas : MeasurableSet (Prod.snd ⁻¹' G : Set (α × Point n)) :=
    measurable_snd hGmeas
  -- the gate = indicator of the `s`-independent product set of the inner kernel.
  have hgate : (fun p : α × Point n => gatedKernel K S H (τ p.1) q₀ p.2)
      = (Prod.snd ⁻¹' G).indicator (fun p : α × Point n => H (τ p.1) q₀ p.2) := by
    funext p
    rw [Set.indicator_apply]
    by_cases hz : p.2 ∈ G
    · have hzK : p.2 ∈ K := hz.1
      have hzS : q₀ ∈ S p.2 := hz.2
      rw [if_pos (by exact hz : p ∈ Prod.snd ⁻¹' G)]
      simp only [gatedKernel, if_pos hzK, if_pos hzS]
    · rw [if_neg (by exact hz : ¬ p ∈ Prod.snd ⁻¹' G)]
      have hnand : ¬ (p.2 ∈ K ∧ q₀ ∈ S p.2) := hz
      rcases not_and_or.mp hnand with hzK | hzS
      · simp only [gatedKernel, if_neg hzK]
      · by_cases hzK : p.2 ∈ K
        · simp only [gatedKernel, if_pos hzK, if_neg hzS]
        · simp only [gatedKernel, if_neg hzK]
  have hgateMeas : AEStronglyMeasurable
      (fun p : α × Point n => gatedKernel K S H (τ p.1) q₀ p.2) (μ.prod ν) := by
    rw [hgate]
    exact hinner.indicator hSetMeas
  exact hgateMeas.mul hF

/-! ###############################################################################
    ### REDUCTION — `hjoint` from the witness (product lever).
    ############################################################################### -/

/-- **★ `hjoint_from_witness`.**  THE EXACT `hjoint` SHAPE of `g2_bundle_assembled`, reduced (via the
    product lever `pd_aestronglyMeasurable_of_slice_prod`) to two strictly lighter carries: `hWmeasJ`
    — the JOINT-witness measurability per field-shift `w` (with the `F` factor) — and `hWdiffJ` — the
    JOINT a.e. field-slice differentiability of the witness to the derivative kernel.  Since `F p.1 p.2`
    is `w`-constant, `HasDerivAt.mul_const` upgrades the witness derivative to the `dH·F` product
    derivative pointwise, matching the lever's `d`.  NOT `a₁ = R/6`. -/
theorem hjoint_from_witness (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (F : ℝ → Point n → ℝ) (ν : Measure (Point n)) (u : Set (Point n))
    (hWmeasJ : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        AEStronglyMeasurable
          (fun p : ℝ × Point n =>
            vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2 * F p.1 p.2)
          ((volume.restrict (Set.uIoc 0 t)).prod ν))
    (hWdiffJ : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ p ∂((volume.restrict (Set.uIoc 0 t)).prod ν),
          HasDerivAt
            (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
            (witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) (x i)) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2 * F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 t)).prod ν) := by
  intro x₀ hx₀ i
  filter_upwards [hWmeasJ x₀ hx₀ i, hWdiffJ x₀ hx₀ i] with x hWm hWd
  refine pd_aestronglyMeasurable_of_slice_prod
    ((volume.restrict (Set.uIoc 0 t)).prod ν)
    (fun w p => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2
      * F p.1 p.2)
    (fun p => witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2 * F p.1 p.2)
    (x i) (fun w => hWm w) ?_
  filter_upwards [hWd] with p hp
  exact hp.mul_const (F p.1 p.2)

/-! ###############################################################################
    ### CAPSTONE — `hjoint_concrete`: the exact `hjoint` slot for `witnessFieldDeriv`.
    ############################################################################### -/

/-- **★★ `hjoint_concrete`.**  THE EXACT `hjoint` slot of `g2_bundle_assembled` for the concrete
    `dH := witnessFieldDeriv`.  Threads the per-field-shift gated-witness joint measurability
    (`witness_joint_aestronglyMeasurable`, from the inner-kernel joint measurability `hinnerJ` + gate
    data `hKmeasSet`/`hSmeasSet` + source `hFjoint`) into the reduction `hjoint_from_witness` (with the
    joint a.e. field-differentiability `hWdiffJ`).  The output is precisely the `hjoint` hypothesis
    `g2_bundle_assembled` consumes.  NONE of the carries is the conclusion.  NOT `a₁ = R/6`. -/
theorem hjoint_concrete (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (F : ℝ → Point n → ℝ) (ν : Measure (Point n)) (u : Set (Point n))
    (hKmeasSet : MeasurableSet K)
    (hSmeasSet : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        MeasurableSet {z : Point n | (Function.update x i w) ∈ S z})
    (hFjoint : AEStronglyMeasurable (fun p : ℝ × Point n => F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 t)).prod ν))
    (hinnerJ : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀, ∀ w : ℝ,
        AEStronglyMeasurable
          (fun p : ℝ × Point n =>
            globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK) (t - p.1) (Function.update x i w) p.2)
          ((volume.restrict (Set.uIoc 0 t)).prod ν))
    (hWdiffJ : ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
        ∀ᵐ p ∂((volume.restrict (Set.uIoc 0 t)).prod ν),
          HasDerivAt
            (fun w => vanVleckGatedWitness g gi hC hK S a b (t - p.1) (Function.update x i w) p.2)
            (witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2) (x i)) :
    ∀ x₀ ∈ u, ∀ i : Fin n, ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable
        (fun p : ℝ × Point n =>
          witnessFieldDeriv g gi hC hK S a b i (t - p.1) x p.2 * F p.1 p.2)
        ((volume.restrict (Set.uIoc 0 t)).prod ν) := by
  refine hjoint_from_witness g gi hC hK S a b t F ν u ?_ hWdiffJ
  intro x₀ hx₀ i
  filter_upwards [hSmeasSet x₀ hx₀ i, hinnerJ x₀ hx₀ i] with x hSm hin w
  have := witness_joint_aestronglyMeasurable (n := n) (α := ℝ) S
    (globalCutoffParametrixWitnessN 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hC hK))
    (Function.update x i w) (fun s => t - s) F
    (volume.restrict (Set.uIoc 0 t)) ν
    hKmeasSet (hSm w) (hin w) hFjoint
  exact this

end QIQTH.JointMeasurability

section AxiomChecks
open QIQTH.JointMeasurability
#print axioms pd_aestronglyMeasurable_of_slice_prod
#print axioms ae_prod_of_ae_ae
#print axioms witness_joint_aestronglyMeasurable
#print axioms hjoint_from_witness
#print axioms hjoint_concrete
end AxiomChecks
